module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalMove

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem conj_mem_factorZStar (i : Fin r) {x z : G}
    (hx : x ∈ aschbacherThm5Preimage D (Abar i)) (hz : z ∈ factorZStar D Abar i) :
    x * z * x⁻¹ ∈ factorZStar D Abar i := by
  set A := aschbacherThm5Preimage D (Abar i)
  obtain ⟨hzA, hzC⟩ := hz
  have hxD : x ∈ D := preimage_le D (Abar i) hx
  obtain ⟨hzD, hzc⟩ := (mem_centralizing_iff (Abar i) z).mp hzC
  refine ⟨A.mul_mem (A.mul_mem hx hzA) (A.inv_mem hx), (mem_centralizing_iff (Abar i) _).mpr
    ⟨D.mul_mem (D.mul_mem hxD hzD) (D.inv_mem hxD), fun a ha => ?_⟩⟩
  have ha' : x⁻¹ * a * x ∈ A := A.mul_mem (A.mul_mem (A.inv_mem hx) ha) hx
  have h1 := hzc _ ha'
  have heq : (x * z * x⁻¹)⁻¹ * a⁻¹ * (x * z * x⁻¹) * a =
      x * (z⁻¹ * (x⁻¹ * a * x)⁻¹ * z * (x⁻¹ * a * x)) * x⁻¹ := by group
  rw [heq]
  have hxH : x ∈ Subgroup.normalizer (aschbacherThm5Core D : Set G) :=
    normalizer_le_normalizer_core D (Subgroup.le_normalizer hxD)
  exact (Subgroup.mem_normalizer_iff.mp hxH _).mp h1

omit [Finite G] in
theorem factor_le_normalizer_factorZStar (i : Fin r) :
    aschbacherThm5Preimage D (Abar i) ≤
      Subgroup.normalizer (factorZStar D Abar i : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact conj_mem_factorZStar i hx
  · intro hz
    have h1 := conj_mem_factorZStar i
      ((aschbacherThm5Preimage D (Abar i)).inv_mem hx) hz
    simpa [mul_assoc] using h1


theorem sylow_normalizer_abelian (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (a : Fin r) {W : Subgroup G}
    (hW : IsSylowOf 2 W (aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G)))
    (hLH : ¬ rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (D : Set G) ≤
        Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
    (hWZ : ¬ W ≤ factorZStar D Abar a) : IsMulCommutative W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  have hΔ' := inv_mem_deltaConjugates hloc hC hΔ
  obtain ⟨d, hdg, -⟩ := exists_sylow_datum hC hΔ' a
  have hA' : ¬ A ⊓ rightConjugate H d.g ≤ Subgroup.normalizer (rightConjugate A d.g : Set G) := by
    rw [hdg]
    intro hle
    apply hLH
    intro y hy
    have h1 : g * y * g⁻¹ ∈ A ⊓ rightConjugate H g⁻¹ := by
      refine Subgroup.mem_inf.mpr ⟨(mem_rightConjugate_iff A g y).mp hy.1, ?_⟩
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hy.2
    have h2 := hle h1
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff] at h2
    simpa [mul_assoc] using h2
  have hT' : ¬ d.T ≤ rightConjugate (factorZStar D Abar a) d.g := by
    rw [hdg]
    intro hle
    have hsyl : IsSylowOf 2 (rightConjugate d.T g) (A ⊓
        Subgroup.normalizer (rightConjugate A g : Set G)) := by
      have h1 := AschbacherTheorem3.isSylowOf_rightConjugate d.sylowT g
      rwa [hdg, AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel,
        rightConjugate_one, AschbacherTheorem3.rightConjugate_normalizer] at h1
    obtain ⟨c, hc, hcW⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hW hsyl
    apply hWZ
    rw [← hcW]
    have h1 : rightConjugate d.T g ≤ factorZStar D Abar a := by
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hle g
      rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this
    have h2 := AschbacherTheorem3.rightConjugate_le_rightConjugate h1 c
    rwa [(rightConjugate_eq_self_iff _ c).mpr (factor_le_normalizer_factorZStar a hc.1)] at h2
  obtain ⟨y, -, -, -, -, -, hab⟩ := hloc.lemma_6_10 hC d hA' hT'
  have hTab : IsMulCommutative d.T := AschbacherTheorem3.isMulCommutative_of_le le_sup_left hab
  have hsyl : IsSylowOf 2 (rightConjugate d.T g) (A ⊓
      Subgroup.normalizer (rightConjugate A g : Set G)) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate d.sylowT g
    rwa [hdg, AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, inv_mul_cancel,
      rightConjugate_one, AschbacherTheorem3.rightConjugate_normalizer] at h1
  obtain ⟨c, -, hcW⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hW hsyl
  rw [← hcW]
  exact AschbacherTheorem3.isMulCommutative_rightConjugate
    (AschbacherTheorem3.isMulCommutative_rightConjugate hTab g) c


theorem rightConjugate_eq_other (hC : Counterexample G D r Abar) (hr : r = 2) {y : G}
    (hyH : y ∈ Subgroup.normalizer (D : Set G)) {i j : Fin r} (hji : j ≠ i)
    (hyN : y ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    rightConjugate (aschbacherThm5Preimage D (Abar i)) y = aschbacherThm5Preimage D (Abar j) := by
  have hyH' := (Subgroup.normalizer (D : Set G)).inv_mem hyH
  obtain ⟨k, hk⟩ := exists_conj_eq hC hyH' i
  have hki : k ≠ i := by
    intro hki
    apply hyN
    rw [hki] at hk
    have := (Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)).inv_mem
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hk)
    simpa using this
  rw [eq_of_ne_of_ne hr hji hki]
  exact hk

theorem mem_factorZStar_of_mem_other (hC : Counterexample G D r Abar) {i j : Fin r}
    (hji : j ≠ i) {s : G} (hsi : s ∈ aschbacherThm5Preimage D (Abar i))
    (hsj : s ∈ aschbacherThm5Preimage D (Abar j)) : s ∈ factorZStar D Abar i :=
  ⟨hsi, (mem_centralizing_iff (Abar i) s).mpr ⟨preimage_le D _ hsi,
    cross_factor_centralizes D Abar hC.hyp.hcomm i j (Ne.symm hji) s hsj⟩⟩

theorem exists_involution_factorZStar (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (a : Fin r) {T W : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G)))
    (hW : IsSylowOf 2 W (aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G)))
    (hTW : Nat.card T ≤ Nat.card W) :
    ∃ s ∈ W ⊓ factorZStar D Abar a, s ≠ 1 ∧ s ^ 2 = 1 := by
  obtain ⟨y, hy, hyN, W', hW', s, hsW', hsy, hs1, hs2⟩ :=
    exists_swap_core hloc hC hΔ a hT hW hTW
  obtain ⟨b, hba⟩ := exists_other hC a
  rw [rightConjugate_eq_other hC hr (Subgroup.mem_inf.mp hy).2 hba hyN] at hsy
  have hsZ : s ∈ factorZStar D Abar a :=
    mem_factorZStar_of_mem_other hC hba ((hW'.le hsW').1) hsy
  obtain ⟨c, hc, hcW⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hW hW'
  refine ⟨c⁻¹ * s * c, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← hcW]
    exact AschbacherTheorem3.conj_mem_rightConjugate hsW' c
  · have h1 := conj_mem_factorZStar a ((aschbacherThm5Preimage D (Abar a)).inv_mem hc.1) hsZ
    simpa using h1
  · intro h1
    apply hs1
    calc s = c * (c⁻¹ * s * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · rw [show c⁻¹ * s * c = c⁻¹ * s * c⁻¹⁻¹ by simp, conj_pow, hs2]
    group

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
