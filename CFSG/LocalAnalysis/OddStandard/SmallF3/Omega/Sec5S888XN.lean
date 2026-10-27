module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888X75
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E7b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private lemma xn_mem_conjugate_iff {Y : Type*} [Group Y] {A : Subgroup Y} {g x : Y} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [h] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem strongly_closed_in_normalizer [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W)
    (hC : ∀ y ∈ normalizer (V : Set X), y * y = 1 → y ∈ centralizer (V : Set X) → y ∈ V)
    (h518 : ∀ (E : Subgroup X) (n : ℕ), ActsElemAb V E →
      (centralizer (V : Set X)).relIndex E = 2 ^ n → n ≤ 3)
    (h73 : ∀ v : V, SuppTwo hS v → centralizer ({(v : X)} : Set X) ≤ normalizer (V : Set X)) :
    ∀ u ∈ normalizer (V : Set X), (∃ k : X, u ∈ CFSG.conjugate V k) → u ∈ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro u hu ⟨k, hk⟩
  have hu2 : u * u = 1 := by
    have hkm : k * u * k⁻¹ ∈ V := xn_mem_conjugate_iff.mp hk
    have h := hS.sq _ hkm
    have e : (k * u * k⁻¹) * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
    rw [e] at h
    have e2 : u * u = k⁻¹ * (k * (u * u) * k⁻¹) * k := by group
    rw [e2, h]
    group
  let N : Subgroup X := normalizer (V : Set X)
  let u' : N := ⟨u, hu⟩
  have hu'2 : u' * u' = 1 := Subtype.ext hu2
  have hP0 : IsPGroup 2 (Subgroup.zpowers u') := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu'2)
  obtain ⟨P, hP⟩ := hP0.exists_le_sylow
  have hVN : V ≤ N := Subgroup.le_normalizer
  haveI hVnormal : (V.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hVN]
    intro h k hh hk
    exact (Subgroup.mem_set_normalizer_iff.mp hk h).mp hh
  have hV0 : IsPGroup 2 V := IsPGroup.of_card hS.card_D
  have hVp : IsPGroup 2 (V.subgroupOf N) := hV0.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
  have hVP : V.subgroupOf N ≤ (P : Subgroup N) := hVp.le_sylow_of_normal P
  let T : Subgroup X := (P : Subgroup N).map N.subtype
  have huT : u ∈ T := Subgroup.mem_map.mpr ⟨u', hP (Subgroup.mem_zpowers u'), rfl⟩
  have hVT : V ≤ T := by
    intro v hv
    exact Subgroup.mem_map.mpr ⟨⟨v, hVN hv⟩, hVP (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  have hTp : IsPGroup 2 T := P.isPGroup'.map N.subtype
  have hrel : T.relIndex N = (P : Subgroup N).index := by
    unfold Subgroup.relIndex
    rw [show T.subgroupOf N = (P : Subgroup N) from
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _]
  have hT : IsSylow2Of T N := ⟨hTN, hTp, by rw [hrel]; exact P.not_dvd_index⟩
  have hTop : IsSylow2Of T (⊤ : Subgroup X) := isSylow2Of_top hS hpar hC hVT hT
  exact strongly_closed_of_hyp hS hpar hC h518 h73 hTop hVT hTN u huT ⟨k, hk⟩

end CFSG.OddStandard.SmallF3.Omega
