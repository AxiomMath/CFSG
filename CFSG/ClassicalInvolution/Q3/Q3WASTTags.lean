module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
public import CFSG.ClassicalInvolution.Uniform.U8Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic


section Pair

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem exists_pair3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x))
    {K₀ Kβ : Subgroup G} (h0 : K₀ ∈ centralizingMembers Ω {x})
    (hβ : Kβ ∈ centralizingMembers Ω {x}) (hnc : ¬ Commutes K₀ Kβ) :
    ∃ i, K₀ ∈ compMembers3 Ω x D i ∧ Kβ ∈ compMembers3 Ω x D i ∧
      ∀ N ∈ centralizingMembers Ω {x}, ¬ Commutes N Kβ → N ∈ compMembers3 Ω x D i := by
  obtain ⟨i, hi, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D h0
  obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hβ
  have hij : i = j := by
    by_contra hne
    exact hnc (commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne hi hj)
  subst hij
  refine ⟨i, hi, hj, fun N hN hnN => ?_⟩
  obtain ⟨k, hk, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hN
  by_cases hki : k = i
  · exact hki ▸ hk
  · exact absurd (commutes_of_ne_comp3 hΩ hex hP1 hO3 D hki hk hj) hnN

theorem twinPair_of_members3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {j : ι}
    (hsc : ∀ R ∈ (D.kind j).fund, ∀ R' ∈ (D.kind j).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind j)) {K M : Subgroup G} (hK : K ∈ compMembers3 Ω x D j)
    (hM : M ∈ compMembers3 Ω x D j) (hne : K ≠ M) (hKM : Commutes K M)
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, (N = K ∨ Commutes N K) ↔ (N = M ∨ Commutes N M)) :
    ∃ F : Fin 2 → Subgroup (D.kind j).G, (∀ k, F k ∈ (D.kind j).fund) ∧ Function.Injective F ∧
      (∀ k l, k ≠ l → Commutes (F k) (F l)) ∧
      ∀ k l, ∀ S ∈ (D.kind j).fund,
        (S = F k ∨ Commutes S (F k)) ↔ (S = F l ∨ Commutes S (F l)) := by
  let T : Fin 2 → Subgroup G := ![K, M]
  have hTx : ∀ k, T k ∈ compMembers3 Ω x D j := by
    intro k
    fin_cases k
    exacts [hK, hM]
  have hinj : Function.Injective T := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact absurd hkl hne
    · exact absurd hkl.symm hne
    · rfl
  have hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact hKM
    · exact hKM.symm
    · exact absurd rfl hkl
  have htw : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l)) := by
    intro N hN k l
    fin_cases k <;> fin_cases l
    · exact Iff.rfl
    · exact htwin N hN
    · exact (htwin N hN).symm
    · exact Iff.rfl
  choose R hR using fun k => exists_corr_left3 hΩ hex hP1 hO3 D (hTx k)
  refine ⟨R, fun k => (hR k).2.1, ?_, ?_, ?_⟩
  · intro k l hkl
    exact hinj (corr_unique_right3 hΩ hex hP1 hO3 (hR k) (hkl ▸ hR l))
  · intro k l hkl
    exact (corr_commutes3 hΩ hex hP1 hO3 hk (hR k) (hR l)).mp (hcomm k l hkl)
  · intro k l S hS
    obtain ⟨N, hN⟩ := exists_corr_right3 hΩ D hsc hS
    have key : ∀ m, (S = R m ∨ Commutes S (R m)) ↔ (N = T m ∨ Commutes N (T m)) := by
      intro m
      constructor
      · rintro (h | h)
        · left
          exact corr_unique_right3 hΩ hex hP1 hO3 (h ▸ hN) (hR m)
        · right
          exact (corr_commutes3 hΩ hex hP1 hO3 hk hN (hR m)).mpr h
      · rintro (h | h)
        · left
          exact corr_unique_left3 hk (h ▸ hN) (hR m)
        · right
          exact (corr_commutes3 hΩ hex hP1 hO3 hk hN (hR m)).mp h
    rw [key k, key l]
    exact htw N hN.1 k l

end Pair

section Kind

theorem modelTwinClass_of_comp3 {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (F : Fin 2 → Subgroup c.G) (hF : ∀ k, F k ∈ c.fund)
    (hinj : Function.Injective F) (hcomm : ∀ k l, k ≠ l → Commutes (F k) (F l))
    (htwin : ∀ k l, ∀ S ∈ c.fund, (S = F k ∨ Commutes S (F k)) ↔ (S = F l ∨ Commutes S (F l))) :
    ModelTwinClass 3 t n 1 2 := by
  subst hc
  exact ⟨F, hF, hinj, hcomm, htwin⟩

theorem singleClass_of_kind3 {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g, R' = conjSub g R := by
  subst hc
  exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three hfund
    hadm hG2 hD4

theorem powCop3_of_kind3 {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) : PowCop3 c := by
  subst hc
  exact powCop3_model hfund hadm hG2 hD4

theorem model_false_of_central3 {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (ht : t = .G2 ∨ t = .trialityD4) {X : Type} [Group X]
    (φ : c.G →* X) (hker : φ.ker ≤ Subgroup.center c.G) {a : X} (ha : a ∈ φ.range)
    (hcen : ∀ y : X, a * y = y * a) (h1 : a ≠ 1) : False := by
  subst hc
  exact model_false_of_central (p := 3) le_rfl hfund hadm ht φ hker ha hcen h1

theorem classical_of_not_exc3 {t : StatedLieTag} (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    (hfe : ¬ (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)) :
    t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
  revert hfund hG2 hD4 hfe
  cases t <;> simp [Generic.IsFundTag]

end Kind

section Tag

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem tag_of_twins3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι}
    {K M : Subgroup G} (hK : K ∈ compMembers3 Ω x D i) (hM : M ∈ compMembers3 Ω x D i)
    (hKM : Commutes K M) (hne : K ≠ M) {z w : G} (hz : IsClassicalMember3 K z)
    (hw : IsClassicalMember3 M w) (hxzw : z * w = x) (hzw : z ≠ w)
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, (N = K ∨ Commutes N K) ↔ (N = M ∨ Commutes N M)) :
    ∃ (t : StatedLieTag) (n : ℕ), D.kind i = CompData.model t n ∧ Generic.IsFundTag t ∧
      StatedLieAdmissible t n 3 1 ∧
      (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) := by
  classical
  rcases D.valid i with ⟨t, n, hfund, hadm, hk⟩ | hk | hk
  · have hfund' : Generic.IsFundTag t := hfund
    by_cases hex2 : t = .G2 ∨ t = .trialityD4
    · exfalso
      have hzY : z ∈ locLayer Ω x := le_centralizingLayer hK.1 hz.mem
      have hwY : w ∈ locLayer Ω x := le_centralizingLayer hM.1 hw.mem
      have ha₁ : Gaps.locMk Ω x ⟨z, hzY⟩ ∈ (D.hom i).range :=
        hK.2 ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
      have ha₃ : Gaps.locMk Ω x ⟨w, hwY⟩ ∈ (D.hom i).range :=
        hM.2 ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
      have hcomm : z * w = w * z := hKM z hz.mem w hw.mem
      have hx2 : orderOf x = 2 := by
        rw [← hxzw]
        exact orderOf_mul_of_commute_involutions hz.orderOf_eq_two hw.orderOf_eq_two hcomm hzw
      have hxY : x ∈ locLayer Ω x := hxzw ▸ (locLayer Ω x).mul_mem hzY hwY
      have hmul : Gaps.locMk Ω x ⟨z, hzY⟩ * Gaps.locMk Ω x ⟨w, hwY⟩ = locElt Ω x x hxY := by
        have := locElt_mul hzY hwY
        simp only [locElt] at this ⊢
        rw [this]
        congr 1
        exact Subtype.ext hxzw
      have hne1 : Gaps.locMk Ω x ⟨z, hzY⟩ * Gaps.locMk Ω x ⟨w, hwY⟩ ≠ 1 := by
        rw [hmul]
        intro h1
        have := orderOf_locElt hxY hx2
        rw [h1, orderOf_one] at this
        omega
      exact model_false_of_central3 hk hfund' hadm hex2 (D.hom i) (D.ker_le_center i)
        (mul_mem ha₁ ha₃) (locMk_mul_central hzY hwY hxzw) hne1
    have hG2 : t ≠ .G2 := fun h => hex2 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hex2 (Or.inr h)
    by_cases hfe : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6
    · exfalso
      have hsc := singleClass_of_kind3 hk hfund' hadm hG2 hD4
      have hpc := powCop3_of_kind3 hk hfund' hadm hG2 hD4
      obtain ⟨F, hFmem, hFinj, hFcomm, hFtwin⟩ :=
        twinPair_of_members3 hΩ hex hP1 hO3 D hsc hpc hK hM hne hKM htwin
      exact Uniform.noTwinClass3_of_layer3 hfund' hadm hG2 hD4 (Uniform.excLayer3 t n hfe hadm)
        (le_refl 2) (modelTwinClass_of_comp3 hk F hFmem hFinj hFcomm hFtwin)
    exact ⟨t, n, hk, hfund', hadm, classical_of_not_exc3 hfund' hG2 hD4 hfe⟩
  · exact absurd (eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hk hK hM) hne
  · exact absurd hKM (not_commutes_of_m11_comp3 hΩ hex hP1 hO3 hk hK hM)

end Tag

end CFSG.ClassicalInvolution.Q3.Q3W
