module

public import CFSG.LargeExtraspecial.S6ThreeF
public import CFSG.LargeExtraspecial.S8FusB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S8

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_orbit_of_ne_zero {t : S.O} (ht : t ∈ S.Lbar g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v) {v : S.Qt}
    (hv : v ∈ Vt S g t) (hv0 : v ≠ 0) : v ∈ orbit S g t := by
  obtain ⟨e, he, hev⟩ := htr ⟨v, hv⟩ fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨r, hr, hre⟩ := he
  refine ⟨r, hr, ?_⟩
  have h1 := hre (aV ht)
  rw [hev] at h1
  exact h1

theorem exists_point_of_mem_commSpace (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    {x : S.O} (hxM : x ∈ S.Mbar) {v : S.Qt}
    (hv : v ∈ commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (hv0 : v ≠ 0) :
    ∃ k : S.M, x * t * x⁻¹ ∈ S.Lbar ((k : G) * g) ∧
      v = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hv0 (map_zero _)
  obtain ⟨r, hr, hrw⟩ := mem_orbit_of_ne_zero ht htr hw hw0
  obtain ⟨k₀, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp hxM
  refine ⟨j * k₀, ?_, ?_⟩
  · have h1 := conj_mem_Lbar_mul S (j * k₀) ht
    have hc := commute_of_mem_Rbar H.conj_mem hr
    rw [map_mul] at h1
    have e : S.ρ j * S.ρ k₀ * t * (S.ρ j * S.ρ k₀)⁻¹ = S.ρ j * t * (S.ρ j)⁻¹ := by
      calc S.ρ j * S.ρ k₀ * t * (S.ρ j * S.ρ k₀)⁻¹ =
          S.ρ j * (S.ρ k₀ * t) * (S.ρ k₀)⁻¹ * (S.ρ j)⁻¹ := by group
        _ = S.ρ j * (t * S.ρ k₀) * (S.ρ k₀)⁻¹ * (S.ρ j)⁻¹ := by rw [hc]
        _ = S.ρ j * t * (S.ρ j)⁻¹ := by group
    rwa [e] at h1
  · rw [hrw]
    change ((S.ρ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((S.ρ k₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹))) = _
    rw [ρ_cl_conj_z S k₀ H.conj_mem, ρ_cl_conj_z S j (conj_mem_QG' S k₀.2 H.conj_mem)]
    simp [mul_assoc]

theorem mem_Lbar_of_mem_commSpace (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v)
    {x : S.O} (hxM : x ∈ S.Mbar) {k : S.M}
    (hk : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈
      commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    x * t * x⁻¹ ∈ S.Lbar ((k : G) * g) := by
  obtain ⟨k', hk'L, hk'v⟩ := exists_point_of_mem_commSpace H C ht ht1 hVQ htr hxM hk
    (cl_conj_z_ne_zero S (conj_mem_QG' S k.2 H.conj_mem) (conj_ne_z' S k.2 H.conj_ne))
  rwa [Lbar_eq_of_cl_eq S (conj_mem_QG' S k'.2 H.conj_mem) (conj_ne_z' S k'.2 H.conj_ne)
    (conj_mem_QG' S k.2 H.conj_mem) hk'v]

theorem eq_zero_of_forall_mem_clSub (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {w : S.Qt}
    (hw : ∀ k : S.M, S.ρ k ∈ Rbar S g t → w ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g))) :
    w = 0 := by
  set D : Submodule (ZMod 2) S.Qt :=
    ⨅ (k : S.M) (_ : S.ρ k ∈ Rbar S g t), S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) with hD
  have hmemD : ∀ {v : S.Qt}, v ∈ D ↔
      ∀ k : S.M, S.ρ k ∈ Rbar S g t → v ∈ S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) := by
    intro v
    simp only [hD, Submodule.mem_iInf]
  have hinv : ∀ l ∈ S.Lbar g, ∀ v ∈ D, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ D := by
    intro l hl v hv
    rw [hmemD] at hv ⊢
    intro k hk
    obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hl)
    have hjR : S.ρ j ∈ Rbar S g t := Lbar_le_Rbar ht hl
    have hjk : S.ρ (j⁻¹ * k) ∈ Rbar S g t := by
      rw [map_mul, map_inv]
      exact mul_mem (inv_mem hjR) hk
    have h1 := hv _ hjk
    have h2 := apply_mem_clSub_Qa_mul j h1
    have e : ((j : G) * (((j⁻¹ * k : S.M) : G) * g)) = (k : G) * g := by
      simp [mul_assoc]
    rwa [e] at h2
  by_contra hw0
  have hDne : D ≠ ⊥ := by
    intro h
    have : w ∈ D := hmemD.mpr hw
    rw [h, Submodule.mem_bot] at this
    exact hw0 this
  have haD := cl_mem_of_Lbar_invariant H hinv hDne
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  exact cl_a_not_mem H hb (hmemD.mp haD h hh)

theorem mem_zpowers_of_fix_clSub_inf_Wt (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x : S.O} (hx : x ∈ S.Lbar g)
    (hfix : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    x ∈ zpowers t := by
  set K : Subgroup S.O := S.Lbar g ⊓
    (S2.fixGroup (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t)).comap S.O.subtype with hK
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have htK : zpowers t ≤ K := by
    rw [zpowers_le]
    refine ⟨ht, S2.mem_fixGroup.mpr fun w hw => ?_⟩
    have hW := (commSpace_t_eq H C ht ht1 hVQ).2
    have hw2 := hw.2
    rw [← hW] at hw2
    exact mem_fixSpace.mp hw2
  have hxK : x ∈ K := ⟨hx, S2.mem_fixGroup.mpr hfix⟩
  have h1 := card_mul_two_pow_finrank_fix H C (K := K) inf_le_left
  have h2 := finrank_clSub_inf_Wt H C ht ht1 hVQ
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K := by
    refine le_inf inf_le_left fun v hv => (mem_fixSub S).mpr fun y hy => ?_
    exact S2.mem_fixGroup.mp hy.2 v hv
  have h3 := Submodule.finrank_mono hle
  have hcard : Nat.card K ≤ Nat.card (zpowers t) := by
    rw [Nat.card_zpowers, hto]
    have hp : 2 ^ (S.width - 1) ≤
        2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hw : 2 ^ S.width = 2 * 2 ^ (S.width - 1) := by
      rw [← pow_succ']
      congr 1
      have := H.two_lt_width
      omega
    by_contra hlt
    push Not at hlt
    have hpos : 0 < 2 ^ (S.width - 1) := by positivity
    have := Nat.mul_le_mul hlt hp
    rw [h1, hw] at this
    omega
  have heq := Subgroup.eq_of_le_of_card_ge htK hcard
  rw [heq]
  exact hxK

theorem mem_Lbar_of_commute (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    {x : S.O} (hxM : x ∈ S.Mbar) (hc : ∀ l ∈ S.Lbar g, x * t * x⁻¹ * l = l * (x * t * x⁻¹)) :
    x * t * x⁻¹ ∈ S.Lbar g := by
  obtain ⟨n, -, hnN, hn⟩ := S5.exists_mem_normalizer_conj H C hxM
    (fun l hl => Lbar_comm S H.conj_mem ht hl) hc
  rw [hn]
  exact (mem_normalizer_iff.mp hnN t).mp ht

theorem map_Vone_of_commute (H : Hyp4 S g) {t : S.O} {k : S.M} (hk : S.ρ k * t = t * S.ρ k)
    (g₁ g₂ : G) :
    (Vone S g t g₁ g₂).map ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap =
      Vone S g t ((k : G) * g₁) ((k : G) * g₂) := by
  set e := ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  have hP : ∀ g' : G, (S.clSub (S.QG ⊓ S.Qa g')).map e.toLinearMap =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g')) := by
    intro g'
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact apply_mem_clSub_Qa_mul k hw
    · intro hv
      refine ⟨(((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v, (mem_clSub_Qa_mul_iff k).mp hv, ?_⟩
      exact apply_inv_apply_O _ v
  have hV : (Vt S g t).map e.toLinearMap = Vt S g t := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq e _)
    rintro _ ⟨v, hv, rfl⟩
    exact apply_mem_Vt H.conj_mem hk hv
  unfold Vone
  rw [Submodule.map_inf _ e.injective, Submodule.map_sup, Submodule.map_sup, hP, hP, hV]

theorem Vone_eq_of_cl_eq {t : S.O} {g₁ g₂ g₁' g₂' : G} (h1Q : g₁ * S.z * g₁⁻¹ ∈ S.QG)
    (h1z : g₁ * S.z * g₁⁻¹ ≠ S.z) (h1Q' : g₁' * S.z * g₁'⁻¹ ∈ S.QG)
    (h1 : S.cl (g₁ * S.z * g₁⁻¹) = S.cl (g₁' * S.z * g₁'⁻¹)) (h2Q : g₂ * S.z * g₂⁻¹ ∈ S.QG)
    (h2z : g₂ * S.z * g₂⁻¹ ≠ S.z) (h2Q' : g₂' * S.z * g₂'⁻¹ ∈ S.QG)
    (h2 : S.cl (g₂ * S.z * g₂⁻¹) = S.cl (g₂' * S.z * g₂'⁻¹)) :
    Vone S g t g₁ g₂ = Vone S g t g₁' g₂' := by
  unfold Vone
  rw [clSub_eq_of_cl_eq h1Q h1z h1Q' h1, clSub_eq_of_cl_eq h2Q h2z h2Q' h2]

section Inv

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem apply_mem_Vone_of_commute {x : S.O} (hxM : x ∈ S.Mbar) (hxt : x * t = t * x) {v : S.Qt}
    (hv : v ∈ Vone S g t g ((h : G) * g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vone S g t g ((h : G) * g) := by
  obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp hxM
  have haQ := H.conj_mem
  have hm : ((S.ρ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
      (Vone S g t g ((h : G) * g)).map ((S.ρ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap :=
    Submodule.mem_map_of_mem hv
  rw [map_Vone_of_commute H hxt] at hm
  have hbQ := conj_mem_QG' S h.2 haQ
  have hjQ := conj_mem_QG' S j.2 haQ
  have hjhQ := conj_mem_QG' S (j * h).2 haQ
  have hjz := conj_ne_z' S j.2 H.conj_ne
  have hjhz := conj_ne_z' S (j * h).2 H.conj_ne
  have hhtr := hSp.transitive
  have hja : S.cl ((j : G) * g * S.z * ((j : G) * g)⁻¹) ∈ Vt S g t := by
    rw [← ρ_cl_conj_z S j haQ]
    exact apply_mem_Vt haQ hxt (cl_a_mem_Vt ht)
  have hjb : S.cl (((j * h : S.M) : G) * g * S.z * (((j * h : S.M) : G) * g)⁻¹) ∈ Vt S g t := by
    rw [← ρ_cl_conj_z S (j * h) haQ, map_mul, coe_mul_apply, ρ_cl_conj_z S h haQ]
    exact apply_mem_Vt haQ hxt (cl_mem_Vt (mem_Lbar_of_pair H ht hh))
  obtain ⟨k₁, hk₁, hk₁e⟩ := exists_of_mem_orbit (mem_orbit_of_ne_zero ht hhtr hja
    (cl_conj_z_ne_zero S hjQ hjz)) haQ
  obtain ⟨k₂, hk₂, hk₂e⟩ := exists_of_mem_orbit (mem_orbit_of_ne_zero ht hhtr hjb
    (cl_conj_z_ne_zero S hjhQ hjhz)) haQ
  have hk₁Q := conj_mem_QG' S k₁.2 haQ
  have hk₂Q := conj_mem_QG' S k₂.2 haQ
  have e1 : (j : G) * ((h : G) * g) = ((j * h : S.M) : G) * g := by simp [mul_assoc]
  rw [e1, Vone_eq_of_cl_eq hjQ hjz hk₁Q hk₁e hjhQ hjhz hk₂Q hk₂e] at hm
  have hk₁₂ : (k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹ ∉ S.Qa ((k₁ : G) * g) := by
    intro hmem
    have h1 := S.cl_mem_clSub (Subgroup.mem_inf.mpr ⟨hk₂Q, hmem⟩) hk₂Q
    rw [← hk₂e, ← clSub_eq_of_cl_eq hjQ hjz hk₁Q hk₁e, mem_clSub_Qa_mul_iff,
      ← ρ_cl_conj_z S (j * h) haQ, map_mul, coe_mul_apply, inv_apply_apply_O,
      ρ_cl_conj_z S h haQ] at h1
    exact cl_b_not_mem H hb h1
  rwa [Vone_pair_eq hCE H hNo C ht ht1 hVQ hSp hh hb hk₁ hk₂ hk₁₂] at hm

theorem apply_mem_Wone_of_commute {x : S.O} (hxM : x ∈ S.Mbar) (hxt : x * t = t * x) {w : S.Qt}
    (hw : w ∈ Wone S g t g ((h : G) * g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wone S g t g ((h : G) * g) := by
  rw [mem_Wone] at hw ⊢
  intro u hu
  have hxt' : x⁻¹ * t = t * x⁻¹ := by
    calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt]
      _ = t * x⁻¹ := by group
  have hu' := apply_mem_Vone_of_commute hCE H hNo C ht ht1 hVQ hSp hh hb (inv_mem hxM) hxt' hu
  have := hw _ hu'
  rwa [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2, apply_inv_apply_O] at this

end Inv

end CFSG.LargeExtraspecial.S9
