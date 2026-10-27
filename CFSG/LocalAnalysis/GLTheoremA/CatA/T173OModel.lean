module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172InnerConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I162
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I61
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.S172X CFSG.StandardType

private theorem glaInduces_pow_conj {Ω : Type} [Group Ω] {S : Subgroup Ω} {R : Type} [Group R]
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* R) {b : Ω} (hN : b ∈ Subgroup.normalizer (S : Set Ω))
    {φ : MulAut R} (hφ : GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) :
    ∀ k : ℕ, GLAInduces θ (fun l l' => (l' : Ω) = (b ^ k)⁻¹ * l * b ^ k) (φ ^ k) := by
  intro k
  induction k with
  | zero =>
    intro l l' h
    rw [show l' = l from Subtype.ext (by simpa using h)]
    rfl
  | succ k ih =>
    intro l l' h
    have hmem : (b ^ k)⁻¹ * (l : Ω) * b ^ k ∈ S := by
      have hbk : b ^ k ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.pow_mem _ hN k
      have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbk)) (l : Ω)
      simpa using h'.mp l.2
    let m : ↥S := ⟨(b ^ k)⁻¹ * (l : Ω) * b ^ k, hmem⟩
    have h1 : (φ ^ k) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk m) := ih l m rfl
    have h2 : φ (θ (QuotientGroup.mk m)) = θ (QuotientGroup.mk l') := by
      refine hφ m l' ?_
      change (l' : Ω) = b⁻¹ * (m : Ω) * b
      rw [h]
      show (b ^ (k + 1))⁻¹ * (l : Ω) * b ^ (k + 1)
        = b⁻¹ * ((b ^ k)⁻¹ * (l : Ω) * b ^ k) * b
      rw [pow_succ, mul_inv_rev]
      group
    calc (φ ^ (k + 1)) (θ (QuotientGroup.mk l))
        = φ ((φ ^ k) (θ (QuotientGroup.mk l))) := by
          rw [pow_succ', MulAut.mul_apply]
      _ = φ (θ (QuotientGroup.mk m)) := by rw [h1]
      _ = θ (QuotientGroup.mk l') := h2

section


private theorem exists_adjointGroup_of_exceptional_lieModel
    {R : Type} [Group R] {t : StatedLieTag} {τ : Tag} {n : ℕ}
    (hLM : CFSG.Blueprint.LieModel R t 0 2 n)
    (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    (hτ : (t = .F4 ∧ τ = .F4) ∨ (t = .E6 ∧ τ = .E6) ∨
      (t = .E7 ∧ τ = .E7) ∨ (t = .E8 ∧ τ = .E8)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (R ≃* ↥(adjointGroup τ F)) := by
  rcases hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hLM.chevalleyExceptionalModel ht
    letI : Field F := hF
    letI : Finite F := hFin
    let χ : AdjointQuotient .F4 F ≃* ↥(adjointGroup .F4 F) :=
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := F))).trans
        QuotientGroup.quotientBot
    exact ⟨F, hF, hFin, hcard, ⟨e.trans χ⟩⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hLM.chevalleyExceptionalModel ht
    letI : Field F := hF
    letI : Finite F := hFin
    let χ : AdjointQuotient .E6 F ≃* ↥(adjointGroup .E6 F) :=
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := F))).trans
        QuotientGroup.quotientBot
    exact ⟨F, hF, hFin, hcard, ⟨e.trans χ⟩⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hLM.chevalleyExceptionalModel ht
    letI : Field F := hF
    letI : Finite F := hFin
    let χ : AdjointQuotient .E7 F ≃* ↥(adjointGroup .E7 F) :=
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := F))).trans
        QuotientGroup.quotientBot
    exact ⟨F, hF, hFin, hcard, ⟨e.trans χ⟩⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hLM.chevalleyExceptionalModel ht
    letI : Field F := hF
    letI : Finite F := hFin
    let χ : AdjointQuotient .E8 F ≃* ↥(adjointGroup .E8 F) :=
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := F))).trans
        QuotientGroup.quotientBot
    exact ⟨F, hF, hFin, hcard, ⟨e.trans χ⟩⟩

private theorem exists_mulEquiv_adjointGroup_of_markedModel_exceptional
    {R : Type} [Group R] [Finite R] {lab : GLALabel} (hM : MarkedModel lab R)
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    ∃ (τ : Tag) (F : Type) (_ : Field F) (_ : Finite F),
      (lab.tag = .F4 ∧ τ = .F4 ∨ lab.tag = .E6 ∧ τ = .E6 ∨
        lab.tag = .E7 ∧ τ = .E7 ∨ lab.tag = .E8 ∧ τ = .E8) ∧
      Nat.card F = 2 ^ lab.n ∧ Nonempty (R ≃* ↥(adjointGroup τ F)) := by
  obtain ⟨t, r, n⟩ := lab
  rcases htag with ht | ht | ht | ht
  · subst ht
    have hLM : CFSG.Blueprint.LieModel R .F4 0 2 n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
      exists_adjointGroup_of_exceptional_lieModel hLM (t := .F4) (τ := .F4)
        (by decide) (Or.inl ⟨rfl, rfl⟩)
    exact ⟨.F4, F, hF, hFin, Or.inl ⟨rfl, rfl⟩, hcard, ⟨e⟩⟩
  · subst ht
    have hLM : CFSG.Blueprint.LieModel R .E6 0 2 n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
      exists_adjointGroup_of_exceptional_lieModel hLM (t := .E6) (τ := .E6)
        (by decide) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact ⟨.E6, F, hF, hFin, Or.inr (Or.inl ⟨rfl, rfl⟩), hcard, ⟨e⟩⟩
  · subst ht
    have hLM : CFSG.Blueprint.LieModel R .E7 0 2 n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
      exists_adjointGroup_of_exceptional_lieModel hLM (t := .E7) (τ := .E7)
        (by decide) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    exact ⟨.E7, F, hF, hFin, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), hcard, ⟨e⟩⟩
  · subst ht
    have hLM : CFSG.Blueprint.LieModel R .E8 0 2 n := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
      exists_adjointGroup_of_exceptional_lieModel hLM (t := .E8) (τ := .E8)
        (by decide) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    exact ⟨.E8, F, hF, hFin, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), hcard, ⟨e⟩⟩

theorem exists_mulEquiv_adjointGroup_of_markedModel_exc
    {R : Type} [Group R] [Finite R] {lab : GLALabel} (hM : MarkedModel lab R)
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    ∃ (τ : Tag) (F : Type) (_ : Field F) (_ : Finite F),
      (lab.tag = .F4 ∧ τ = .F4 ∨ lab.tag = .E6 ∧ τ = .E6 ∨
        lab.tag = .E7 ∧ τ = .E7 ∨ lab.tag = .E8 ∧ τ = .E8) ∧
      Nat.card F = 2 ^ lab.n ∧ Nonempty (R ≃* ↥(adjointGroup τ F)) :=
  exists_mulEquiv_adjointGroup_of_markedModel_exceptional hM htag

theorem exists_mulEquiv_statedSp_of_markedModel
    {R : Type} [Group R] [Finite R] {r n : ℕ}
    (hM : MarkedModel (⟨.B, r, n⟩ : GLALabel) R) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (R ≃* ↥(StatedSp r F)) := by
  have hM' : CFSG.Blueprint.LieModel R .PSp r 2 n := hM
  have hSC : StatedClassicalModel R .PSp r 2 n :=
    hM'.statedClassicalModel (by decide : StatedLieTag.PSp ∈ classicalTags)
  obtain ⟨hadm, F, hF, hFin, hcard, ⟨e⟩⟩ := hSC
  letI : Field F := hF
  letI : Finite F := hFin
  have hn : 1 ≤ n := hadm.2.1
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn hcard
  letI : CharP F 2 := hchar
  have hbot : (StatedScalars (Fin r ⊕ Fin r) F).subgroupOf (StatedSp r F) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let eS : StatedProj (StatedSp r F) ≃* ↥(StatedSp r F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact ⟨F, hF, hFin, hcard, ⟨e.trans eS⟩⟩

end

section


private theorem not_dvd_card_center_of_dvd_two {K : Type} [Group K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : Nat.card (Subgroup.center K) ∣ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpZ
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hpZ.trans hdvd))

private theorem not_dvd_card_center_of_dvd_one {K : Type} [Group K] {p : ℕ}
    (hp : p.Prime) (hdvd : Nat.card (Subgroup.center K) ∣ 1) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpZ
  exact hp.not_dvd_one (hpZ.trans hdvd)

private theorem not_dvd_card_center_of_dvd_gcd_two {K : Type} [Group K] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : Nat.card (Subgroup.center K) ∣ Nat.gcd 2 (2 ^ n - 1)) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpZ
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    ((hpZ.trans hdvd).trans (Nat.gcd_dvd_left 2 (2 ^ n - 1))))

private theorem not_dvd_card_center_of_dvd_gcd_three {K : Type} [Group K] {p n : ℕ}
    (hp : p.Prime) (hE6 : p ≠ 3 ∨ n = 1)
    (hdvd : Nat.card (Subgroup.center K) ∣ Nat.gcd 3 (2 ^ n - 1)) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpZ
  have h3 : p ∣ Nat.gcd 3 (2 ^ n - 1) := hpZ.trans hdvd
  rcases hE6 with hp3 | hn1
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (h3.trans (Nat.gcd_dvd_left 3 (2 ^ n - 1))))
  · subst hn1
    have h1 : p ∣ 1 := by simpa using h3
    exact hp.not_dvd_one h1

private theorem not_dvd_card_center_f4 {K : Type} [Group K] [Finite K] {n p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .F4 0 2 n)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .F4 0 2 n = (1, 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .F4 0 2 n = (2, 1) ∨
      CFSG.Blueprint.Multiplier.exceptionalOrders .F4 0 2 n = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rcases hexc with h | h
  · exact not_dvd_card_center_of_dvd_two hp hp2 (by
      have := i61_card_center_dvd_native (Q := K) hQ (t := .F4) (n := 0) (p := 2) (f := n)
        (a := 1) (b := 1) (c := 2) (d := 1) hM' hgen h
      simpa using this)
  · exact not_dvd_card_center_of_dvd_one hp (by
      have := i61_card_center_dvd_native (Q := K) hQ (t := .F4) (n := 0) (p := 2) (f := n)
        (a := 1) (b := 1) (c := 1) (d := 1) hM' hgen h
      simpa using this)

private theorem not_dvd_card_center_e6 {K : Type} [Group K] [Finite K] {n p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 n)
    (hp : p.Prime) (hE6 : p ≠ 3 ∨ n = 1) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hdvd := i61_card_center_dvd_native (Q := K) hQ (t := .E6) (n := 0) (p := 2) (f := n)
    (a := Nat.gcd 3 (2 ^ n - 1)) (b := 1) (c := 1) (d := 1) hM' rfl rfl
  exact not_dvd_card_center_of_dvd_gcd_three hp hE6 (by simpa using hdvd)

private theorem not_dvd_card_center_e7 {K : Type} [Group K] [Finite K] {n p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 n)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hdvd := i61_card_center_dvd_native (Q := K) hQ (t := .E7) (n := 0) (p := 2) (f := n)
    (a := Nat.gcd 2 (2 ^ n - 1)) (b := 1) (c := 1) (d := 1) hM' rfl rfl
  exact not_dvd_card_center_of_dvd_gcd_two hp hp2 (by simpa using hdvd)

private theorem not_dvd_card_center_e8 {K : Type} [Group K] [Finite K] {n p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 n)
    (hp : p.Prime) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hdvd := i61_card_center_dvd_native (Q := K) hQ (t := .E8) (n := 0) (p := 2) (f := n)
    (a := 1) (b := 1) (c := 1) (d := 1) hM' rfl rfl
  exact not_dvd_card_center_of_dvd_one hp (by simpa using hdvd)

private theorem not_dvd_card_center_of_markedModel_exceptional
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE6 : lab.tag = .E6 → p ≠ 3 ∨ lab.n = 1) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  obtain ⟨t, r, n⟩ := lab
  rcases htag with ht | ht | ht | ht
  · subst ht
    exact not_dvd_card_center_f4 hQ
      (by simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM) hp hp2
  · subst ht
    exact not_dvd_card_center_e6 hQ
      (by simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM) hp (hE6 rfl)
  · subst ht
    exact not_dvd_card_center_e7 hQ
      (by simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM) hp hp2
  · subst ht
    exact not_dvd_card_center_e8 hQ
      (by simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM) hp

theorem not_dvd_card_center_of_markedModel_exc
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hp : p.Prime) (hp2 : p ≠ 2) (hE6 : lab.tag = .E6 → p ≠ 3 ∨ lab.n = 1) :
    ¬ p ∣ Nat.card (Subgroup.center K) :=
  not_dvd_card_center_of_markedModel_exceptional hQ hM htag hp hp2 hE6

private theorem not_dvd_card_center_psp {K : Type} [Group K] [Finite K] {r n p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp r 2 n)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSp r 2 n =
      (Nat.gcd 2 (2 ^ n - 1), 1) := rfl
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp r 2 n = (2, 1) ∨
      CFSG.Blueprint.Multiplier.exceptionalOrders .PSp r 2 n = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  intro hpZ
  rcases hexc with h | h
  · have hdvd := i61_card_center_dvd_native (Q := K) hQ (t := .PSp) (n := r) (p := 2) (f := n)
      (a := Nat.gcd 2 (2 ^ n - 1)) (b := 1) (c := 2) (d := 1) hM' hgen h
    have h1 : p ∣ Nat.gcd 2 (2 ^ n - 1) * 2 := by simpa using hpZ.trans hdvd
    have hp2' : p ∣ 2 := by
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h' | h'
      · exact h'.trans (Nat.gcd_dvd_left 2 (2 ^ n - 1))
      · exact h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
  · have hdvd := i61_card_center_dvd_native (Q := K) hQ (t := .PSp) (n := r) (p := 2) (f := n)
      (a := Nat.gcd 2 (2 ^ n - 1)) (b := 1) (c := 1) (d := 1) hM' hgen h
    have h1 : p ∣ Nat.gcd 2 (2 ^ n - 1) := by simpa using hpZ.trans hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (h1.trans (Nat.gcd_dvd_left 2 (2 ^ n - 1))))

private theorem not_dvd_card_center_of_markedModel_symplectic
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  obtain ⟨t, r, n⟩ := lab
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp r 2 n := by
    rcases htag with ht | ht
    · change t = .B at ht
      subst ht
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    · change t = .C at ht
      subst ht
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
  exact not_dvd_card_center_psp hQ hM' hp hp2

theorem not_dvd_card_center_of_markedModel_sp
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hQ : CFSG.Open.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .B ∨ lab.tag = .C) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) :=
  not_dvd_card_center_of_markedModel_symplectic hQ hM htag hp hp2

end

section


private theorem mem_sup_centralizer_of_innerDiag_marking
    {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B)
    {lab : GLALabel} (hlab : GLAInLambda2 lab) (hpd : ¬ p ∣ rk2DiagIndex lab)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  classical
  obtain ⟨hperf, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _hs₀, _hna₀, θ₀, hP₀⟩ := rk2_rawDatum_exists hraw
  obtain ⟨hlabEq, _⟩ := hP₀
  subst hlabEq
  have hraw' := rk2_pSubgroup_le_inn' hlab hp hp2 hpd _ hraw
  obtain ⟨R, _, I, F, hQ, hInn⟩ := rk2_rawDatum_exists hraw'
  obtain ⟨_hs, _hna, θ, hP⟩ := hQ
  obtain ⟨_, hN, hind⟩ := hP
  haveI : Finite R := Finite.of_equiv _ θ.toEquiv
  intro b hb
  obtain ⟨φ, hφI, hφ⟩ := hind b hb
  have hφp : φ ^ p = 1 := by
    have hbp : b ^ p = 1 := by simpa using hB.2 b hb
    have hind_p := glaInduces_pow_conj θ (hN hb) hφ p
    refine rk2_induces_unique θ (b := (1 : Ω)) (by simp) ?_ ?_
    · intro l l' hll'
      exact hind_p l l' (by simpa [hbp] using hll')
    · intro l l' hll'
      rw [show l' = l from Subtype.ext (by simpa using hll')]
      rfl
  have hEp : IsPGroup p (Subgroup.zpowers φ) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      simpa using orderOf_dvd_of_pow_eq_one hφp)
  have hle : Subgroup.zpowers φ ≤
      Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inl hφI))
  obtain ⟨r, hr⟩ := hInn (Subgroup.zpowers φ) hle hEp (Subgroup.mem_zpowers φ)
  exact mem_sup_centralizer_of_largeEvenInduces_conj θ hperf (hN hb) (by rwa [hr])

theorem mem_sup_centralizer_of_innerDiag_of_not_dvd_diagIndex
    {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B)
    {lab : GLALabel} (hlab : GLAInLambda2 lab) (hpd : ¬ p ∣ rk2DiagIndex lab)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) :=
  mem_sup_centralizer_of_innerDiag_marking hp hp2 hB hlab hpd hmark

private theorem not_dvd_rk2DiagIndex_of_exceptional_tag
    {p : ℕ} (hp : p.Prime) {t : CFSG.Assembly.LargeEvenLieTag} {r n : ℕ}
    (htag : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hE6 : t = .E6 → p ≠ 3 ∨ n = 1) :
    ¬ p ∣ rk2DiagIndex (⟨t, r, n⟩ : GLALabel) := by
  rcases htag with ht | ht | ht | ht
  · subst ht
    intro h
    exact hp.not_dvd_one (by simpa [rk2DiagIndex] using h)
  · subst ht
    intro h
    have h3 : p ∣ Nat.gcd 3 (2 ^ n - 1) := by simpa [rk2DiagIndex] using h
    rcases hE6 rfl with hp3 | hn1
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
        (h3.trans (Nat.gcd_dvd_left 3 (2 ^ n - 1))))
    · subst hn1
      have h1 : p ∣ 1 := by simpa using h3
      exact hp.not_dvd_one h1
  · subst ht
    intro h
    exact hp.not_dvd_one (by simpa [rk2DiagIndex] using h)
  · subst ht
    intro h
    exact hp.not_dvd_one (by simpa [rk2DiagIndex] using h)

private theorem not_dvd_rk2DiagIndex_of_symplectic_tag
    {p : ℕ} (hp : p.Prime) {t : CFSG.Assembly.LargeEvenLieTag} {r n : ℕ}
    (htag : t = .B ∨ t = .C) :
    ¬ p ∣ rk2DiagIndex (⟨t, r, n⟩ : GLALabel) := by
  rcases htag with ht | ht <;> subst ht <;>
    (intro h; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using h))

private theorem markedModel_and_mem_sup_of_marking
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (hpd : ¬ p ∣ rk2DiagIndex lab)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 p lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    MarkedModel lab (↥S ⧸ Subgroup.center ↥S) ∧
      ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  have hmark' : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) :=
    rk2_marking_mono (fun lab' R _ I F θ h => ⟨h.1, h.2.2⟩) hmark
  have hBin := mem_sup_centralizer_of_innerDiag_marking hcfg.prime hcfg.odd hcfg.elem
    hlab hpd hmark'
  have hRk : Rk2IsLabel S lab := rk2_marking_mono (fun lab' R _ I F θ h => h.1) hmark
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hRk
  exact ⟨hM, hBin⟩

private theorem exists_model_exc_of_markedModel
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel}
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hE6 : lab.tag = .E6 → p ≠ 3 ∨ lab.n = 1)
    (hM : MarkedModel lab (↥S ⧸ Subgroup.center ↥S))
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∃ (τ : CFSG.Blueprint.Chevalley.Tag) (F : Type) (_ : Field F) (_ : Finite F)
      (_ : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup τ F)),
      (lab.tag = .F4 ∧ τ = .F4 ∨ lab.tag = .E6 ∧ τ = .E6 ∨
        lab.tag = .E7 ∧ τ = .E7 ∨ lab.tag = .E8 ∧ τ = .E8) ∧
      Nat.card F = 2 ^ lab.n ∧ ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
      Nonempty (S172X.S172Model S B ↥(CFSG.Blueprint.Chevalley.adjointGroup τ F)) := by
  have hcenter := not_dvd_card_center_of_markedModel_exceptional hcfg.qs hM htag
    hcfg.prime hcfg.odd hE6
  obtain ⟨τ, F, hF, hFin, hτ, hcard, ⟨e⟩⟩ :=
    exists_mulEquiv_adjointGroup_of_markedModel_exceptional hM htag
  letI : Field F := hF
  letI : Finite F := hFin
  obtain ⟨M⟩ := S172Model.nonempty_of_mem_sup hcfg.normal hBin e
  exact ⟨τ, F, hF, hFin, CFSG.LieType.Chevalley.generated_group_finite τ F, hτ, hcard,
    hcenter, ⟨M⟩⟩

theorem exists_model_exc
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hE6 : lab.tag = .E6 → p ≠ 3 ∨ lab.n = 1)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 p lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∃ (τ : CFSG.Blueprint.Chevalley.Tag) (F : Type) (_ : Field F) (_ : Finite F)
      (_ : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup τ F)),
      (lab.tag = .F4 ∧ τ = .F4 ∨ lab.tag = .E6 ∧ τ = .E6 ∨ lab.tag = .E7 ∧ τ = .E7 ∨
        lab.tag = .E8 ∧ τ = .E8) ∧
      Nat.card F = 2 ^ lab.n ∧ ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
      Nonempty (S172X.S172Model S B ↥(CFSG.Blueprint.Chevalley.adjointGroup τ F)) := by
  obtain ⟨t, r, n⟩ := lab
  have hpd := not_dvd_rk2DiagIndex_of_exceptional_tag (r := r) (n := n) hcfg.prime htag hE6
  obtain ⟨hM, hBin⟩ := markedModel_and_mem_sup_of_marking hcfg hlab hpd hmark
  exact exists_model_exc_of_markedModel hcfg htag hE6 hM hBin

private theorem exists_model_sp_of_markedModel
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hrank : 3 ≤ lab.rank)
    (hM : MarkedModel lab (↥S ⧸ Subgroup.center ↥S))
    (hBin : ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ lab.n ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
      Nonempty (S172X.S172Model S B ↥(CFSG.Open.StatedSp lab.rank F)) := by
  have hcenter := not_dvd_card_center_of_markedModel_symplectic hcfg.qs hM htag
    hcfg.prime hcfg.odd
  obtain ⟨t, r, n⟩ := lab
  have hMB : MarkedModel (⟨.B, r, n⟩ : GLALabel) (↥S ⧸ Subgroup.center ↥S) := by
    rcases htag with ht | ht
    · subst ht
      exact hM
    · subst ht
      exact hM
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_markedModel hMB
  letI : Field F := hF
  letI : Finite F := hFin
  obtain ⟨M⟩ := S172Model.nonempty_of_mem_sup hcfg.normal hBin e
  exact ⟨F, hF, hFin, hcard, hcenter, ⟨M⟩⟩

theorem exists_model_sp
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hrank : 3 ≤ lab.rank)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 p lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ lab.n ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥S) ∧
      Nonempty (S172X.S172Model S B ↥(CFSG.Open.StatedSp lab.rank F)) := by
  obtain ⟨t, r, n⟩ := lab
  have hpd := not_dvd_rk2DiagIndex_of_symplectic_tag (r := r) (n := n) hcfg.prime htag
  obtain ⟨hM, hBin⟩ := markedModel_and_mem_sup_of_marking hcfg hlab hpd hmark
  exact exists_model_sp_of_markedModel hcfg htag hrank hM hBin

end

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
