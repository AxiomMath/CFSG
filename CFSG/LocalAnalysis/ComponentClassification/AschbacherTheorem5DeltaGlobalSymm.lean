module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBarTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SixLocalResults

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
theorem isElemAbelian_rightConjugate {E : Subgroup G} (hE : IsElemAbelian 2 E) (g : G) :
    IsElemAbelian 2 (rightConjugate E g) := by
  refine ⟨AschbacherTheorem3.isMulCommutative_rightConjugate hE.1 g, fun x hx => ?_⟩
  rw [mem_rightConjugate_iff] at hx
  have h := hE.2 _ hx
  have heq : x ^ 2 = g⁻¹ * (g * x * g⁻¹) ^ 2 * g := by
    simp only [pow_two]
    group
  rw [heq, h]
  group

omit [Finite G] in
theorem rightConjugate_rightConjugate_inv (K : Subgroup G) (g : G) :
    rightConjugate (rightConjugate K g) g⁻¹ = K := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

omit [Finite G] in
theorem rightConjugate_inv_eq_iff (K : Subgroup G) (g : G) :
    rightConjugate K g⁻¹ = K ↔ rightConjugate K g = K := by
  rw [rightConjugate_eq_self_iff, rightConjugate_eq_self_iff]
  exact ⟨fun h => by simpa using (Subgroup.normalizer (K : Set G)).inv_mem h,
    fun h => (Subgroup.normalizer (K : Set G)).inv_mem h⟩

theorem mem_fourGroupsInto_of_le_conj (hC : Counterexample G D r Abar) {i : Fin r} {g : G}
    {E : Subgroup G} (hEL : E ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g)
    (hEH : E ≤ Subgroup.normalizer (D : Set G)) (hE : IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) :
    E ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g) := by
  refine ⟨hEH, hE, hE4, fun u hu hu1 => ?_⟩
  exact centralizer_le_conj hC i g ⟨1, by rw [pow_one, hE.2 u hu]⟩ hu1 (hEL hu)

theorem fourGroup_le_normalizer (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {i : Fin r} {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {E : Subgroup G} (hEL : E ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g)
    (hEH : E ≤ Subgroup.normalizer (D : Set G)) (hE : IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) (j : Fin r) :
    E ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar j) : Set G) :=
  hloc.lemma_6_5_one hC hg (mem_fourGroupsInto_of_le_conj hC hEL hEH hE hE4) j

theorem fourGroup_le_normalizer_conj (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {i : Fin r} {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    {E : Subgroup G} (hEA : E ≤ aschbacherThm5Preimage D (Abar i))
    (hEH : E ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g) (hE : IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) (j : Fin r) :
    E ≤ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar j)) g : Set G) := by
  have hg' : rightConjugate (Subgroup.normalizer (D : Set G)) g⁻¹ ≠
      Subgroup.normalizer (D : Set G) :=
    fun h => hg ((rightConjugate_inv_eq_iff _ g).mp h)
  have h1 := fourGroup_le_normalizer hloc hC hg'
    (E := rightConjugate E g⁻¹) (AschbacherTheorem3.rightConjugate_le_rightConjugate hEA g⁻¹)
    (by
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hEH g⁻¹
      rwa [rightConjugate_rightConjugate_inv] at this)
    (isElemAbelian_rightConjugate hE g⁻¹) (by rw [rightConjugate_card, hE4]) j
  have h2 := AschbacherTheorem3.rightConjugate_le_rightConjugate h1 g
  rwa [AschbacherTheorem3.rightConjugate_normalizer, rightConjugate_mul, inv_mul_cancel,
    rightConjugate_one] at h2

theorem inv_mem_deltaConjugates (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {g : G} (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) :
    rightConjugate (Subgroup.normalizer (D : Set G)) g⁻¹ ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) := by
  obtain ⟨-, -, hne, -⟩ := id hΔ
  have i : Fin r := ⟨0, by have := two_le hC; omega⟩
  obtain ⟨-, h2, -⟩ := hloc.lemma_6_7 hC hΔ i
  obtain ⟨E, hEle, hE4, hE⟩ := AschbacherTheorem3.exists_four_le
    (T := aschbacherThm5Preimage D (Abar i) ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (by omega)
  refine ⟨g⁻¹, rfl, fun h => hne ((rightConjugate_inv_eq_iff _ g).mp h), rightConjugate E g⁻¹,
    ?_⟩
  refine mem_fourGroupsInto_of_le_conj hC
    (AschbacherTheorem3.rightConjugate_le_rightConjugate (hEle.trans inf_le_left) g⁻¹) ?_
    (isElemAbelian_rightConjugate hE g⁻¹) (by rw [rightConjugate_card, hE4])
  have := AschbacherTheorem3.rightConjugate_le_rightConjugate (hEle.trans inf_le_right) g⁻¹
  rwa [rightConjugate_rightConjugate_inv] at this


theorem even_card_of_two_le {P : Subgroup G} (hP : IsPGroup 2 P) (h2 : 2 ≤ Nat.card P) :
    Even (Nat.card P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at h2 ⊢
  rcases n with _ | n
  · simp at h2
  · exact (Nat.even_pow' (Nat.succ_ne_zero n)).mpr even_two

theorem involution_mem_normalizer (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) {i j : Fin r} {x : G}
    (hxL : x ∈ rightConjugate (aschbacherThm5Preimage D (Abar i)) g)
    (hxH : x ∈ Subgroup.normalizer (D : Set G)) (hx2 : x ^ 2 = 1) :
    x ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar j) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G)
  set N := Subgroup.normalizer (aschbacherThm5Preimage D (Abar j) : Set G)
  set K := rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊓ H
  obtain ⟨-, -, hne, -⟩ := id hΔ
  by_contra hxN
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ N.one_mem)
  have hxK : x ∈ K := ⟨hxL, hxH⟩
  have hZ2 : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hx2 hx1, pow_one])
  obtain ⟨P, hP, hxP⟩ := AschbacherTheorem3.exists_isSylowOf_le hZ2
    (Subgroup.zpowers_le.mpr hxK)
  have hxP' : x ∈ P := hxP (Subgroup.mem_zpowers x)
  obtain ⟨h2, -, -⟩ := hloc.lemma_6_7 hC hΔ i
  have h2' : 2 ≤ CFSG.Open.pRank 2 K := h2
  obtain ⟨F, hFK, hF4, -⟩ := AschbacherTheorem3.exists_four_le (T := K) (by omega)
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF4]; norm_num)
  have hP4 : 4 ≤ Nat.card P := hF4 ▸ AschbacherTheorem3.card_le_of_isSylowOf hP hF2 hFK
  have hPH : P ≤ H := hP.le.trans inf_le_right
  have hPN : ¬ P ≤ N := fun h => hxN (h hxP')
  have hcard := card_eq_two_mul hC hr j hPH hPN
  set Y := P ⊓ N
  have hYeven : Even (Nat.card Y) :=
    even_card_of_two_le (hP.isPGroup.to_le inf_le_left) (by omega)
  have hxY : Subgroup.zpowers x ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.zpowers_le]
    have hYeq : Y = P ⊓ (H ⊓ N) := by
      rw [← inf_assoc, inf_eq_left.mpr hPH]
    rw [hYeq]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hxP', le_normalizer_inf_normalizer hC hr j hxH⟩
  obtain ⟨z, hzY, hz2, hzx⟩ := BarTools.exists_involution_centralized hZ2 hxY hYeven
  have hzx' : x * z = z * x := hzx x (Subgroup.mem_zpowers x)
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  have hzne : x ≠ z := fun h => hxN (h ▸ hzY.2)
  obtain ⟨hcard4, hel⟩ := AschbacherTheorem3.exists_four_of_involutions hx2
    (by rw [← hz2]; exact pow_orderOf_eq_one z) hx1 hz1 hzne hzx'
  have hEK : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hxK)
      (Subgroup.zpowers_le.mpr (hP.le (hzY.1)))
  have hEN := fourGroup_le_normalizer hloc hC hne (hEK.trans inf_le_left) (hEK.trans inf_le_right)
    hel hcard4 j
  exact hxN (hEN (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))

theorem involution_mem_normalizer_conj (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) (hr : r = 2) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) {i j : Fin r} {x : G}
    (hxA : x ∈ aschbacherThm5Preimage D (Abar i))
    (hxH : x ∈ rightConjugate (Subgroup.normalizer (D : Set G)) g) (hx2 : x ^ 2 = 1) :
    x ∈ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar j)) g : Set G) := by
  have hΔ' := inv_mem_deltaConjugates hloc hC hΔ
  have hyL : g * x * g⁻¹ ∈ rightConjugate (aschbacherThm5Preimage D (Abar i)) g⁻¹ := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hxA
  have hyH : g * x * g⁻¹ ∈ Subgroup.normalizer (D : Set G) := (mem_rightConjugate_iff _ _ _).mp hxH
  have hy2 : (g * x * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hx2]
    group
  have h := involution_mem_normalizer hloc hC hr hΔ' (j := j) hyL hyH hy2
  rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
  exact h

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
