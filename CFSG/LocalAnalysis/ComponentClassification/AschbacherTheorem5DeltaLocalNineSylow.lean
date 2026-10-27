module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineOrbit

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem mem_normalizer_orbitProduct (hyp : Hyp61 G D r Abar) {y : G}
    (hyH : y ∈ Subgroup.normalizer (D : Set G)) {I : Set (Fin r)}
    (hI : ∀ k ∈ I, ∀ l, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj y).toMonoidHom =
      aschbacherThm5Preimage D (Abar l) → l ∈ I) :
    y ∈ Subgroup.normalizer (orbitProduct D Abar I : Set G) := by
  apply AschbacherToolkit.mem_normalizer_of_conj_le
  have hle : orbitProduct D Abar I ≤
      (orbitProduct D Abar I).comap (MulAut.conj y).toMonoidHom := by
    refine iSup₂_le fun k hk => ?_
    obtain ⟨l, hl⟩ := hyp.hperm y hyH k
    rw [← Subgroup.map_le_iff_le_comap, hl]
    exact factor_le_orbitProduct (hI k hk l hl)
  exact fun x hx => hle hx

theorem index_eq_of_mem_normalizer (hyp : Hyp61 G D r Abar) {y : G} {k l : Fin r}
    (hyk : y ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G))
    (hl : (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj y).toMonoidHom =
      aschbacherThm5Preimage D (Abar l)) : l = k := by
  apply SixTools.index_eq_of_preimage_eq hyp
  rw [← hl]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyk

theorem sylow_normalizes (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) (i : Fin r) :
    ∃ T : Subgroup G, IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊓
      Subgroup.normalizer (D : Set G)) ∧
      ∀ k, T ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set L := rightConjugate (aschbacherThm5Preimage D (Abar i)) g with hLdef
  have hNH := Eight.normalizer_factor_le hC i
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (L ⊓ Subgroup.normalizer
    (aschbacherThm5Preimage D (Abar i) : Set G))
  have hT2 := hT.isPGroup
  have hTL : T ≤ L := hT.le.trans inf_le_left
  have hTi : T ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) :=
    hT.le.trans inf_le_right
  have hTH : T ≤ H := hTi.trans hNH
  have hTk : ∀ k, T ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G) := by
    intro k
    by_cases hki : k = i
    · rw [hki]
      exact hTi
    have hB := le_normalizer_orbitProduct hC.hyp hTH (I := {l | l ≠ i}) (by
      intro p hp l hl l' hl'
      show l' ≠ i
      intro hl'i
      apply hl
      subst hl'i
      have h2 : (aschbacherThm5Preimage D (Abar l')).map (MulAut.conj p).toMonoidHom =
          aschbacherThm5Preimage D (Abar l') :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTi hp)
      exact SixTools.index_eq_of_preimage_eq hC.hyp (Subgroup.map_injective
        (f := (MulAut.conj p).toMonoidHom) (MulAut.conj p).injective (hl'.trans h2.symm)))
    exact (orbit_normalizes h3 hin hC hΔ hr hTL hTH hT2 (orbitProduct_le_D _)
      (factor_le_orbitProduct (I := {l | l ≠ i}) hki)
      (orbitProduct_le_centralizing hC.hyp.hcomm (j := i) (by simp)) hB).1
  refine ⟨T, ?_, hTk⟩
  obtain ⟨T', hT', hTT'⟩ := AschbacherTheorem3.exists_isSylowOf_le hT2
    (le_inf hTL hTH : T ≤ L ⊓ H)
  rcases eq_or_lt_of_le hTT' with heq | hlt
  · rw [heq]
    exact hT'
  exfalso
  obtain ⟨y, hyT', hyN, hyT, hyy⟩ := exists_sq_mem_of_lt hT'.isPGroup hlt
  have hyL : y ∈ L := (hT'.le hyT').1
  have hyH : y ∈ H := (hT'.le hyT').2
  obtain ⟨i', hi'⟩ := hC.hyp.hperm y hyH i
  obtain ⟨k, hki, hki'⟩ := Six.exists_third hr i i'
  have hyyi : y * y ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) :=
    hTi hyy
  have hPN : T ⊔ Subgroup.zpowers y ≤
      Subgroup.normalizer (orbitProduct D Abar {i, i'} : Set G) := by
    refine sup_le (le_normalizer_orbitProduct hC.hyp hTH (fun p hp l hl l' hl' => ?_))
      (Subgroup.zpowers_le.mpr (mem_normalizer_orbitProduct hC.hyp hyH (fun l hl l' hl' => ?_)))
    · rw [index_eq_of_mem_normalizer hC.hyp (hTk l hp) hl']
      exact hl
    · rcases hl with h | h
      · rw [h, hi'] at hl'
        rw [SixTools.index_eq_of_preimage_eq hC.hyp hl'.symm]
        exact Or.inr rfl
      · have h1 : (aschbacherThm5Preimage D (Abar i')).map (MulAut.conj y).toMonoidHom =
            aschbacherThm5Preimage D (Abar i) := by
          have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y).toMonoidHom =
              (MulAut.conj (y * y)).toMonoidHom := by
            ext x
            simp [MulAut.conj_apply, mul_assoc]
          rw [← hi', Subgroup.map_map, hcomp]
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyyi
        rw [h] at hl'
        rw [hl'] at h1
        rw [SixTools.index_eq_of_preimage_eq hC.hyp h1]
        exact Or.inl rfl
  have hP2 : IsPGroup 2 (T ⊔ Subgroup.zpowers y : Subgroup G) :=
    hT'.isPGroup.to_le (sup_le hTT' (Subgroup.zpowers_le.mpr hyT'))
  have hPL : T ⊔ Subgroup.zpowers y ≤ L := sup_le hTL (Subgroup.zpowers_le.mpr hyL)
  have hPH : T ⊔ Subgroup.zpowers y ≤ H := sup_le hTH (Subgroup.zpowers_le.mpr hyH)
  have hPi := (orbit_normalizes h3 hin hC hΔ hr hPL hPH hP2 (orbitProduct_le_D _)
    (factor_le_orbitProduct (I := {i, i'}) (k := i) (by simp))
    (orbitProduct_le_centralizing hC.hyp.hcomm (j := k) (by simp [hki, hki'])) hPN).1
  have hle : T ⊔ Subgroup.zpowers y ≤ L ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := le_inf hPL hPi
  have heq := hT.eq_of_le le_sup_left hle hP2
  apply hyT
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem normalizes_of_le (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) {i : Fin r}
    {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPL : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) (k : Fin r) :
    P ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTk⟩ := sylow_normalizes h3 hin hC hΔ hr i
  obtain ⟨c, hc, hcle⟩ :=
    AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hT hP2 (le_inf hPL hPH)
  obtain ⟨l, hl⟩ := hC.hyp.hperm c⁻¹ (Subgroup.inv_mem _ hc.2) k
  intro p hp
  have hp' : c⁻¹ * p * c ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar l) : Set G) :=
    hTk l (hcle (AschbacherTheorem3.conj_mem_rightConjugate hp c))
  have hNl : Subgroup.normalizer (aschbacherThm5Preimage D (Abar l) : Set G) =
      rightConjugate (Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G)) c := by
    rw [AschbacherTheorem3.rightConjugate_normalizer, ← hl]
    rfl
  rw [hNl, mem_rightConjugate_iff] at hp'
  simpa [mul_assoc] using hp'

theorem delta_conj (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) :
    rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹ ∈
      deltaConjugates (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi : 0 < r := by have := two_le hC; omega
  obtain ⟨-, h2, -⟩ := lemma_6_7 h3 hin hC hΔ ⟨0, hi⟩
  obtain ⟨V, hVA, hVel, hV4⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) h2
  have hV := Seven.mem_fourGroupsInto_conj hC ⟨0, hi⟩ hVA hVel (by rw [hV4]; norm_num)
  obtain ⟨-, -, hne, -⟩ := hΔ
  refine ⟨g⁻¹, rfl, ?_, V, hV⟩
  rw [Six.conj_normalizer_inv, normalizer_rightConjugate]
  exact Ne.symm hne

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
