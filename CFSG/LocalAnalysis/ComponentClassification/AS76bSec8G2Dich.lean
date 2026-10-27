module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Torus

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ComponentClassification.AS76b.Lemma36 (ConjData PairData)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Dich

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem inf_centralizer_sec3 (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (hZA : Odd (Nat.card (center A))) :
    (R ⊔ T) ⊓ centralizer (A : Set G) = R := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hVe := isElemAbelian_sup_sec3 hc h32
  refine le_antisymm (fun v hv => ?_) (le_inf le_sup_left hc.sylowR.le)
  obtain ⟨hvV, hvK⟩ := mem_inf.1 hv
  have hN : (R ⊔ T) ⊓ A ≤ normalizer (R : Set G) := by
    intro x hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun r hr => ?_)
    exact (mem_centralizer_iff.1 (hc.sylowR.le hr) x (mem_inf.1 hx).2).symm
  have hvV' : v ∈ ((R ⊔ ((R ⊔ T) ⊓ A) : Subgroup G) : Set G) := by
    rw [sup_inf_sec3 hc h32 h4 h34]
    exact hvV
  rw [coe_mul_of_right_le_normalizer_left R _ hN, Set.mem_mul] at hvV'
  obtain ⟨r, hr, z, hz, rfl⟩ := hvV'
  have hzK : z ∈ centralizer (A : Set G) := by
    have h1 := mul_mem (inv_mem (hc.sylowR.le hr)) hvK
    rwa [inv_mul_cancel_left] at h1
  have hz1 : z = 1 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨(mem_inf.1 hz).2, hzK⟩)) (k := 1)
    (by rw [pow_one]; exact hVe.2 z (mem_inf.1 hz).1)
  rw [hz1, mul_one]
  exact hr

theorem sec3_of_conj (hc : Sec3 A R T g) (h32 : Lemma32) {x x' : G}
    (hx : rightConjugate R x ≤ R ⊔ T) (hx' : rightConjugate R x' ≤ R ⊔ T)
    (hn : x' * x⁻¹ ∉ normalizer (A : Set G)) :
    Sec3 A R (rightConjugate R (x' * x⁻¹)) (x' * x⁻¹) := by
  refine ⟨hc.hyp, hc.sylowR, hn, AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR _, ?_⟩
  have hVC : R ⊔ T ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) :=
    le_centralizer_self_of_isElemAbelian (isElemAbelian_sup_sec3 hc h32)
  have h1 : rightConjugate R x' ≤ centralizer (rightConjugate R x : Set G) :=
    hx'.trans (hVC.trans (centralizer_le fun v hv => hx hv))
  have h2 := map_mono (f := (MulAut.conj x⁻¹⁻¹).toMonoidHom) h1
  change rightConjugate (rightConjugate R x') x⁻¹ ≤
    rightConjugate (centralizer (rightConjugate R x : Set G)) x⁻¹ at h2
  rwa [← centralizer_rightConjugate, RankTwoClassical.rightConjugate_rightConjugate_inv,
    rightConjugate_mul] at h2

theorem exists_conjData_g2
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) {x : G} (hx : rightConjugate R x ≤ R ⊔ T) :
    ∃ y, ConjData (R ⊔ T) (rightConjugate R x) (rightConjugate A x) y ∧
      TorusData (rightConjugate A x) (R ⊔ T) y := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨xT, hxT, hAxT⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hVK := inf_centralizer_sec3 hc h32 h4 h34 hZA
  have hRK : ∀ y : G, y ∈ normalizer (A : Set G) → rightConjugate R y ≤ R ⊔ T →
      rightConjugate R y = R := by
    intro y hy hyV
    have hKy : rightConjugate (centralizer (A : Set G)) y = centralizer (A : Set G) := by
      rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A y).2 hy]
    have h1 : rightConjugate R y ≤ (R ⊔ T) ⊓ centralizer (A : Set G) :=
      le_inf hyV (hKy ▸ map_mono hc.sylowR.le)
    rw [hVK] at h1
    exact eq_of_le_of_card_ge h1 (by rw [rightConjugate_card])
  obtain ⟨x', hx', hn⟩ : ∃ x' : G, rightConjugate R x' ≤ R ⊔ T ∧
      x' * x⁻¹ ∉ normalizer (A : Set G) := by
    by_cases hQ : rightConjugate R x = R
    · refine ⟨xT, hxT ▸ le_sup_right, fun h => ?_⟩
      have hxN : x ∈ normalizer (A : Set G) := by
        have h1 := Lemma36.normalizer_le hc.hyp hc.sylowR 1 (by
          rw [rightConjugate_one]
          exact (rightConjugate_eq_self_iff R x).1 hQ)
        rwa [rightConjugate_one] at h1
      have hxTN : xT ∈ normalizer (A : Set G) := by
        have h1 := mul_mem h hxN
        rwa [inv_mul_cancel_right] at h1
      have h1 := hRK xT hxTN (hxT ▸ le_sup_right)
      rw [← hxT] at h1
      apply hc.R_ne_bot
      rw [← inf_idem R]
      nth_rewrite 2 [← h1]
      exact hc.inf_eq_bot
    · refine ⟨1, by rw [rightConjugate_one]; exact le_sup_left, fun h => hQ (hRK x ?_ hx)⟩
      rw [one_mul] at h
      have h1 := inv_mem h
      rwa [inv_inv] at h1
  have hcx := sec3_of_conj hc h32 hx hx' hn
  obtain ⟨y', hy'⟩ := torusData hf hK h4 h32 h184 h184s hcx hOut hZA hψ hRq
  have hd := hy'.rightConjugate x
  have hconj : rightConjugate (R ⊔ rightConjugate R (x' * x⁻¹)) x =
      rightConjugate R x ⊔ rightConjugate R x' := by
    rw [RankTwoClassical.rightConjugate_sup, rightConjugate_mul, inv_mul_cancel_right]
  have hV : rightConjugate R x ⊔ rightConjugate R x' = R ⊔ T := by
    refine eq_of_le_of_card_ge (sup_le hx hx') ?_
    rw [← hconj, rightConjugate_card, card_sup_sec3 hcx, card_sup_sec3 hc]
  rw [hconj, hV] at hd
  refine ⟨x⁻¹ * y' * x, ?_, hd⟩
  have hsup := sup_inf_sec3 hcx h32 h4 h34
  have hsup' := congrArg (fun H => rightConjugate H x) hsup
  simp only [RankTwoClassical.rightConjugate_sup, RankTwoClassical.rightConjugate_inf] at hsup'
  rw [← RankTwoClassical.rightConjugate_sup, hconj, hV] at hsup'
  have hR4 : 4 ≤ Nat.card (rightConjugate R x) := by
    rw [rightConjugate_card]
    exact hc.four_le
  exact
    { elem := isElemAbelian_sup_sec3 hc h32
      le := hx
      sup_eq := hsup'
      le_centralizer := by
        rw [centralizer_rightConjugate]
        exact map_mono hc.sylowR.le
      mem := hd.mem
      mem_normalizer := hd.mem_normalizer
      odd := hd.odd
      trans := hd.trans
      four_le := hR4
      card_lt := by
        rw [rightConjugate_card, card_sup_sec3 hc]
        have h1 : 4 * Nat.card R ≤ Nat.card R * Nat.card R := Nat.mul_le_mul_right _ hc.four_le
        have h2 := hc.four_le
        omega }

theorem g2_dichotomy
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) (h184s : G2Centr184s)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) :
    (T = (R ⊔ T) ⊓ A ∧ ∀ x : G, rightConjugate R x ≤ R ⊔ T →
        rightConjugate R x = R ∨ rightConjugate R x = T) ∨
      ((R ⊔ T) ⊓ A = (R ⊔ T) ⊓ rightConjugate A g ∧
        (∀ v ∈ R ⊔ T, v ∉ A ↔
          ∃ x : G, rightConjugate R x ≤ R ⊔ T ∧ v ∈ rightConjugate R x ∧ v ≠ 1) ∧
        ∀ x₁ x₂ x₁' x₂' : G, rightConjugate R x₁ ≤ R ⊔ T → rightConjugate R x₂ ≤ R ⊔ T →
          rightConjugate R x₁' ≤ R ⊔ T → rightConjugate R x₂' ≤ R ⊔ T →
          rightConjugate R x₁ ≠ rightConjugate R x₂ →
          rightConjugate R x₁' ≠ rightConjugate R x₂' →
          ∃ n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G),
            rightConjugate (rightConjugate R x₁) n = rightConjugate R x₁' ∧
              rightConjugate (rightConjugate R x₂) n = rightConjugate R x₂') := by
  classical
  obtain ⟨xT, hxT, hAxT⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hex := fun x (hx : rightConjugate R x ≤ R ⊔ T) =>
    exists_conjData_g2 hf hK h4 h32 h184 h184s hc hOut hZA hψ hRq hx
  let y : G → G := fun x => if hx : rightConjugate R x ≤ R ⊔ T then (hex x hx).choose else 1
  have hy : ∀ x (hx : rightConjugate R x ≤ R ⊔ T),
      ConjData (R ⊔ T) (rightConjugate R x) (rightConjugate A x) (y x) ∧
        TorusData (rightConjugate A x) (R ⊔ T) (y x) := by
    intro x hx
    have h1 := (hex x hx).choose_spec
    simp only [y, hx, ↓reduceDIte]
    exact h1
  have hRneT : R ≠ T := by
    intro h
    apply hc.R_ne_bot
    have h1 := hc.inf_eq_bot
    rwa [← h, inf_idem] at h1
  have hmain := Lemma36.main_of_data (y := y) hxT hAxT le_sup_left le_sup_right hRneT
    (fun x hx => (hy x hx).1)
    (fun x₁ x₂ hx₁ hx₂ hne => Lemma36.pairData hc.hyp hc.sylowR (hy x₁ hx₁).1 (hy x₂ hx₂).1
      (hy x₁ hx₁).2.norm (hy x₂ hx₂).2.norm hne)
  have hR1 : rightConjugate R 1 ≤ R ⊔ T := by
    rw [rightConjugate_one]
    exact le_sup_left
  have dR := (hy 1 hR1).1
  rw [rightConjugate_one, rightConjugate_one] at dR
  have hT1 : rightConjugate R xT ≤ R ⊔ T := by
    rw [← hxT]
    exact le_sup_right
  have dT := (hy xT hT1).1
  rw [← hxT, hAxT] at dT
  rw [dR.commutator_eq, dT.commutator_eq] at hmain
  rcases hmain with ⟨h1, -, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1.symm, h3⟩
  · refine Or.inr ⟨h1, fun v hv => ?_, h3⟩
    rw [← h2 v hv]
    exact ⟨fun h hv' => h (mem_inf.1 hv').2, fun h hvA => h (mem_inf.2 ⟨hv, hvA⟩)⟩

end Dich

end CFSG.ComponentClassification.RankTwoExceptional
