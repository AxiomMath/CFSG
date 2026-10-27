module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS01KSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

@[expose] def KDL227PumpK : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (S : Subgroup Y), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup ↥S → CFSG.Open.IsKGroup ↥S →
    Subgroup.centralizer (S : Set Y) = ⊥ →
    ∀ (I : Subgroup Y) (b x : Y), b ^ 3 = 1 → x ^ 3 = 1 → b * x = x * b →
      GLAPComponent 3 (S ⊓ Subgroup.centralizer ({b} : Set Y)) I →
      catalogIs (PSimple 3 I) (onLie (isL2 27)) → x ∈ Subgroup.normalizer (I : Set Y) →
      ¬ InducesInnerMod 3 I x → b = 1

section Cert

set_option linter.unusedSectionVars false


theorem s_levelK (hSpor : KDL227SporK) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (hK : CFSG.Open.IsKGroup S)
    (β ξ : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hξ : ξ ^ 3 = 1) (hξβ : ξ * β = β * ξ)
    (I : Subgroup S) (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hL : catalogIs (PSimple 3 I) (onLie (isL2 27))) (hN : I.map ξ.toMonoidHom = I) :
    ∃ i ∈ I, ∀ y ∈ I, ξ y * (i * y * i⁻¹)⁻¹ ∈ GLAPPrimeCoreOf 3 I := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact (KDL227Aux.alt_case hn e β hβ hβ1 I hI hL).elim
  | sporadic s => exact (hSpor S s ⟨e⟩ hK β hβ hβ1 I hI hL).elim
  | lie d =>
    by_cases hd3 : d.1.characteristic = 3
    · by_cases hinn : β ∈ innerAut S
      · exact (KDL227Aux.lie_three_inner_case hs hna d e hd3 β hβ hβ1 hinn I hI).elim
      · exact KDL227Aux.lie_three_outer_case hs hna d e hd3 β ξ hβ hβ1 hinn hξ hξβ I hI hL hN
    · exact (KDL227Aux.lie_ne_three_case hs hna d e hd3 β hβ I hI hL).elim

open CFSG.HardMathSupport.Dickson.DefCharOuter.Export (FixedData3)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (map_glaPPrimeCoreOf_of_injective)

theorem kdL227PumpK_of_sporK (hSpor : KDL227SporK) : KDL227PumpK := by
  intro Y _ _ S hSn hSs hSna hSc hSK hSC I b x hb3 hx3 hbx hI hL hxN hind
  by_contra hb1
  haveI := hSn
  set β : MulAut ↥S := MulAut.conjNormal (H := S) b with hβdef
  set ξ : MulAut ↥S := MulAut.conjNormal (H := S) x⁻¹ with hξdef
  have hβ3 : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hb3, map_one]
  have hξ3 : ξ ^ 3 = 1 := by rw [hξdef, ← map_pow, inv_pow, hx3, inv_one, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hb1
    have hmem : b ∈ Subgroup.centralizer (S : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := congrArg Subtype.val (DFunLike.congr_fun h ⟨g, hg⟩)
      simp only [hβdef, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc g * b = b * g * b⁻¹ * b := by rw [this]
        _ = b * g := by group
    rw [hSC] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hξβ : ξ * β = β * ξ := by
    rw [hξdef, hβdef, ← map_mul, ← map_mul]
    congr 1
    calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * b) * x⁻¹ := by rw [hbx]
      _ = b * x⁻¹ := by group
  rw [← KDL227Aux.map_fixSubgroup_conjNormal S b] at hI
  obtain ⟨I', hI', rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three S.subtype
    (FixedData3.coprime_inf_ker S.subtype S.subtype_injective _) hI
  have hL' : catalogIs (PSimple 3 I') (onLie (isL2 27)) :=
    (catalogIs_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3
      (I'.equivMapOfInjective S.subtype S.subtype_injective))).2 hL
  have hN : I'.map ξ.toMonoidHom = I' := by
    have key : ∀ g : Y, g ∈ Subgroup.normalizer ((I'.map S.subtype : Subgroup Y) : Set Y) →
        ∀ s ∈ I', ∃ t ∈ I', (t : Y) = g * (s : Y) * g⁻¹ := by
      intro g hg s hs
      have h1 : g * (s : Y) * g⁻¹ ∈ I'.map S.subtype :=
        (Subgroup.mem_normalizer_iff.1 hg (s : Y)).1 ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hts⟩ := h1
      exact ⟨t, ht, hts⟩
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hts⟩ := key x⁻¹ (Subgroup.inv_mem _ hxN) s hs
      have : ξ s = t := Subtype.ext (by
        simp only [hξdef, MulAut.conjNormal_apply]
        exact hts.symm)
      rw [MulEquiv.coe_toMonoidHom, this]
      exact ht
    · intro t ht
      obtain ⟨s, hs, hts⟩ := key x hxN t ht
      refine ⟨s, hs, ?_⟩
      apply Subtype.ext
      simp only [MulEquiv.coe_toMonoidHom, hξdef, MulAut.conjNormal_apply, inv_inv]
      calc x⁻¹ * (s : Y) * x = x⁻¹ * (x * (t : Y) * x⁻¹) * x := by rw [← hts]
        _ = t := by group
  obtain ⟨i, hi, hall⟩ :=
    s_levelK hSpor hSs hSna hSc hSK β ξ hβ3 hβ1 hξ3 hξβ I' hI' hL' hN
  apply hind
  refine ⟨((i⁻¹ : ↥S) : Y), ⟨i⁻¹, I'.inv_mem hi, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_glaPPrimeCoreOf_of_injective 3 S.subtype S.subtype_injective I']
  have hw : ((i * y * i⁻¹)⁻¹ : ↥S) ∈ I' :=
    I'.inv_mem (I'.mul_mem (I'.mul_mem hi hy) (I'.inv_mem hi))
  have h1 := hall y hy
  have hnorm := le_normalizer_glaPPrimeCoreOf 3 I' hw
  have h2 : (i * y * i⁻¹)⁻¹ * ξ y ∈ GLAPPrimeCoreOf 3 I' := by
    have := (Subgroup.mem_normalizer_iff.1 hnorm _).1 h1
    simpa [mul_assoc] using this
  refine ⟨_, h2, ?_⟩
  simp only [Subgroup.coe_subtype, hξdef, MulAut.conjNormal_apply, inv_inv, Subgroup.coe_mul,
    Subgroup.coe_inv]

end Cert

end CFSG.LocalAnalysis.GLTheoremA
