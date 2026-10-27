module

public import CFSG.LargeExtraspecial.DW2AAlphaTrans
public import CFSG.LargeExtraspecial.DW2AOutInput
public import CFSG.LargeExtraspecial.DW2ModFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms

theorem s12NoNormalTwo_map_of_injective {G₁ G₂ : Type*} [Group G₁] [Group G₂] {H : Subgroup G₁}
    (hH : S12NoNormalTwo H) {φ : G₁ →* G₂} (hφ : Function.Injective φ) :
    S12NoNormalTwo (H.map φ) := by
  intro P hPH hP hHP
  have hP'p : IsPGroup 2 (P.comap φ ⊓ H : Subgroup G₁) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := hP ⟨φ g, (Subgroup.mem_inf.mp hg).1⟩
    refine ⟨k, Subtype.ext (hφ ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hP'H : H ≤ normalizer ((P.comap φ ⊓ H : Subgroup G₁) : Set G₁) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro g
    have hN := mem_normalizer_iff.mp (hHP ⟨h, hh, rfl⟩) (φ g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_comap, mem_comap, map_mul, map_mul, map_inv]
    constructor
    · rintro ⟨hg, hgH⟩
      exact ⟨hN.mp hg, H.mul_mem (H.mul_mem hh hgH) (H.inv_mem hh)⟩
    · rintro ⟨hg, hgH⟩
      refine ⟨hN.mpr hg, ?_⟩
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hgH) hh
      simpa [mul_assoc] using this
  have hbot := hH _ inf_le_right hP'p hP'H
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hPH hx
  have : g ∈ P.comap φ ⊓ H := Subgroup.mem_inf.mpr ⟨hx, hg⟩
  rw [hbot, mem_bot] at this
  rw [this, map_one, mem_bot]

namespace Alpha

variable {G : Type} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

theorem isSpTypeA_of_isTypeA {t : S.Qt ≃ₗ[ZMod 2] S.Qt} (ht : IsTypeA S.q t 2) :
    IsSpTypeA S.q.polarBilin t 2 := by
  obtain ⟨hiso, hne, hinv, hdim, hsing⟩ := ht
  refine ⟨fun u v => ?_, hne, hinv, hdim, fun v => ?_⟩
  · rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add, hiso, hiso,
      hiso]
  · rw [polarBilin_apply_apply]
    have hc := hsing (t v - v) (sub_mem_commSpace t v)
    have e : t v = v + (t v - v) := by abel
    have h1 := hiso v
    rw [e, QuadraticMap.map_add S.q, hc, add_zero, add_eq_left] at h1
    rw [e, polar_add_right, polar_self, h1, add_zero, two_nsmul, add_self_zmod2]

variable (S W) in
@[expose] noncomputable def XbarL : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := (Xbar S W).map S.O.subtype

variable (S W) in
@[expose] noncomputable def TsetL : Set (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.O.subtype '' Tset S W

theorem XbarL_eq_closure (hA : Hyp S W) : XbarL S W = closure (TsetL S W) := by
  rw [XbarL, TsetL, ← MonoidHom.map_closure, le_antisymm (Xbar_le_closure_Tset hA)
    closure_Tset_le_Xbar]

theorem XbarL_le_Ybar : XbarL S W ≤ Ybar S := map_mono Xbar_le_Mbar

theorem Ybar_le_normalizer_XbarL (hA : Hyp S W) :
    Ybar S ≤ normalizer (XbarL S W : Set (S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [mem_normalizer_iff]
  intro t
  have hN := mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar hA hm)
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨m * u * m⁻¹, (hN u).mp hu, by simp⟩
  · rintro ⟨u, hu, hue⟩
    refine ⟨m⁻¹ * u * m, ?_, ?_⟩
    · have := (hN (m⁻¹ * u * m)).mpr (by simpa [mul_assoc] using hu)
      exact this
    · have : (S.O.subtype m) * t * (S.O.subtype m)⁻¹ = S.O.subtype u := hue.symm
      have e : t = (S.O.subtype m)⁻¹ * S.O.subtype u * S.O.subtype m := by
        rw [← this]; group
      rw [e]
      simp

theorem noNormalTwo_XbarL (hA : Hyp S W) : S12NoNormalTwo (XbarL S W) :=
  s12NoNormalTwo_map_of_injective (noNormalTwo_Xbar hA) S.O.subtype_injective

section Class

variable (hA : Hyp S W) [IsSimpleGroup G] (hn : 2 ≤ S.width) {h₀ : G} (hx₀ : IsDx S W h₀)
  {t₀ : S.O} (ht₀ : t₀ ∈ Abar S (S.clPre W) h₀) (ht₀1 : t₀ ≠ 1)
include hA hn hx₀ ht₀ ht₀1

theorem isA2Class : IsA2Class S.q.polarBilin (XbarL S W) (TsetL S W) := by
  refine ⟨XbarL_eq_closure hA, ⟨t₀, ⟨t₀, mem_Tset_of_mem_Abar hA hx₀ ht₀ ht₀1, rfl⟩, ?_⟩, ?_⟩
  · intro d
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Tset_conj hA hn hx₀ ht₀ ht₀1 hτ
      exact ⟨x, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x * t₀ * x⁻¹, (transpositionData hA hn hx₀ ht₀ ht₀1).conj x hx t₀
        (mem_Tset_of_mem_Abar hA hx₀ ht₀ ht₀1), by simp⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    exact isSpTypeA_of_isTypeA hτ.2

omit ht₀ ht₀1 in

theorem hasFourGroup : HasFourGroup (TsetL S W) := by
  obtain ⟨t₁, ht₁, t₂, ht₂, h1, h2, h12⟩ := exists_two_mem_Abar hA (by omega) hx₀
  have h121 : t₁ * t₂ ≠ 1 := by
    intro e
    apply h12
    calc t₁ = t₁ * (t₂ * t₂) := by
          rw [Tset_mul_self (mem_Tset_of_mem_Abar hA hx₀ ht₂ h2), mul_one]
      _ = (t₁ * t₂) * t₂ := by group
      _ = t₂ := by rw [e, one_mul]
  refine ⟨t₁, ⟨t₁, mem_Tset_of_mem_Abar hA hx₀ ht₁ h1, rfl⟩, t₂,
    ⟨t₂, mem_Tset_of_mem_Abar hA hx₀ ht₂ h2, rfl⟩, fun e => h12 (Subtype.ext e), ?_,
    ⟨t₁ * t₂, mem_Tset_of_mem_Abar hA hx₀ (mul_mem ht₁ ht₂) h121, rfl⟩⟩
  have := congrArg Subtype.val (Abar_comm hA hx₀ ht₁ ht₂)
  simpa using this

theorem isTransClass34 :
    IsTransClass34 {x : Xbar S W | (x : S.O) ∈ Tset S W} := by
  have hD := transpositionData hA hn hx₀ ht₀ ht₀1
  have ht₀T := mem_Tset_of_mem_Abar hA hx₀ ht₀ ht₀1
  refine ⟨?_, ⟨⟨t₀, ht₀T.1⟩, ht₀T, fun d => ?_⟩, fun d hd => ⟨fun h => Tset_ne_one hd
    (congrArg Subtype.val h), Subtype.ext (Tset_mul_self hd)⟩, fun d hd e he => ?_,
    fun d hd e he h4 => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx := Xbar_le_closure_Tset hA x.2
    have key : ∀ y ∈ closure (Tset S W), ∀ hy : y ∈ Xbar S W,
        (⟨y, hy⟩ : Xbar S W) ∈ closure {x : Xbar S W | (x : S.O) ∈ Tset S W} := by
      intro y hy
      induction hy using closure_induction with
      | mem z hz => exact fun hy => subset_closure hz
      | one => exact fun _ => one_mem _
      | mul a b ha hb iha ihb =>
        exact fun hab => by
          have := mul_mem (iha (closure_Tset_le_Xbar ha)) (ihb (closure_Tset_le_Xbar hb))
          exact this
      | inv a ha iha =>
        exact fun hai => by
          have := inv_mem (iha (closure_Tset_le_Xbar ha))
          exact this
    exact key x hx x.2
  · constructor
    · intro hdT
      obtain ⟨x, hx, hxd⟩ := Tset_conj hA hn hx₀ ht₀ ht₀1 hdT
      exact isConj_iff.mpr ⟨⟨x, hx⟩, Subtype.ext (by simp [hxd])⟩
    · intro h
      obtain ⟨g, rfl⟩ := isConj_iff.mp h
      have := hD.conj g g.2 t₀ ht₀T
      exact this
  · rw [s12_orderOf_mul_coe]
    exact hD.ord d hd e he
  · rw [s12_orderOf_mul_coe] at h4
    have := hD.sq d hd e he h4
    simpa using this

end Class

end Alpha

end CFSG.LargeExtraspecial.DW
