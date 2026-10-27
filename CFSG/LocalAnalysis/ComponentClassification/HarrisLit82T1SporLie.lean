module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatFittingTransfer

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup Assembly.LowTwoRank CatLeaf
open scoped MatrixGroups

theorem indLieOrder_of_lieModel
    {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Blueprint.LieModel X τ n p f) (hs : IndShape τ n p f) : IndLieOrder (Nat.card X) := by
  have ha := SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h
  obtain ⟨-, h1, h2⟩ := CatLeafProof.lieOrderFormulasInput X τ n p f ha h
  exact ⟨τ, n, p, f, hp, hp2, ha, hs, h1, h2⟩

theorem oddLieOrder_of_lieModel
    {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Blueprint.LieModel X τ n p f) : OddLieOrder (Nat.card X) := by
  have ha := SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel h
  obtain ⟨-, h1, h2⟩ := CatLeafProof.lieOrderFormulasInput X τ n p f ha h
  exact ⟨τ, n, p, f, hp, hp2, ha, h1, h2⟩

theorem indLieOrder_psl_two {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : Even f) (hf1 : 1 ≤ f) (hF : Nat.card F = p ^ f) :
    IndLieOrder (Nat.card (PSL(2, F))) := by
  have hcard := SectionRank.OddCover.card_psl_two hp hp2 hF
  have hfac := SectionRank.OddCover.factorization_card_psl_two hp hp2 hF
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
  have hq3 : 3 ≤ p ^ f := by
    have := hp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hq9 : p ^ f ≠ 3 := by
    intro h3
    obtain ⟨j, rfl⟩ := hf
    have : p ^ (j + j) = (p ^ j) ^ 2 := by ring
    rw [this] at h3
    have hj : p ^ j ≤ 1 := by nlinarith
    have : p ^ j = 1 := by
      have := pow_pos hp.pos j
      omega
    rw [this] at h3
    norm_num at h3
  refine ⟨.PSL, 2, p, f, hp, hp2, ⟨hp, hf1, le_rfl, fun h => ?_, fun h => hq9 ?_⟩,
    .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, hf⟩)))), ?_, ?_⟩
  · simp only [Prod.mk.injEq] at h
    omega
  · simp only [Prod.mk.injEq] at h
    exact h.2
  · have hdiv : lieOrderDivisor .PSL 2 (p ^ f) = 2 := by
      simp only [lieOrderDivisor]
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    have hnum : lieOrderNumerator .PSL 2 (p ^ f) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      simp only [lieOrderNumerator]
      norm_num
    rw [hdiv, hnum, hcard, mul_assoc]
    congr 1
    have h2 : 2 ∣ (p ^ f) ^ 2 - 1 := by
      rw [hk]
      exact ⟨2 * k * k + 2 * k, by ring_nf; omega⟩
    exact Nat.div_mul_cancel h2
  · rw [hfac]
    simp only [lieSylowExponent]
    norm_num

theorem indLieOrder_of_field
    {L : Type} [Group L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∃ f : ℕ, 1 ≤ f ∧
      (IsCoverOf .POmegaOdd 3 p f 2 (L ⧸ pPrimeCore 2 L) ∨
        IsCoverOf .PSL 4 p f (Nat.gcd 4 (p ^ f - 1)) (L ⧸ pPrimeCore 2 L) ∨
        IsCoverOf .PSU 4 p f (Nat.gcd 4 (p ^ f + 1)) (L ⧸ pPrimeCore 2 L) ∨
        IsCoverOf .PSp 2 p f 2 (L ⧸ pPrimeCore 2 L) ∨
        (Even f ∧ IsSLTwoOver (p ^ f) (L ⧸ pPrimeCore 2 L)))) :
    IndLieOrder (Nat.card (L ⧸ Open.fusionZStar L)) := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv L
  rw [Nat.card_congr eZ.toEquiv]
  rcases h with ⟨f, hf1, ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩ |
      ⟨hfe, F, _, _, hF, ⟨eF⟩⟩⟩
  · exact indLieOrder_of_lieModel hp hp2 hm (.inl ⟨rfl, rfl⟩)
  · exact indLieOrder_of_lieModel hp hp2 hm (.inr (.inl ⟨rfl, rfl⟩))
  · exact indLieOrder_of_lieModel hp hp2 hm (.inr (.inr (.inl ⟨rfl, rfl⟩)))
  · exact indLieOrder_of_lieModel hp hp2 hm (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  · let e' : (L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L) ≃* PSL(2, F) :=
      QuotientGroup.congr _ _ eF (Subgroup.map_center_eq eF)
    rw [Nat.card_congr e'.toEquiv]
    exact indLieOrder_psl_two hp hp2 hfe hf1 (by rw [Nat.card_eq_fintype_card, hF])

theorem card_quotient_fusionZStar_of_bot {X : Type*} [Group X] (hO : pPrimeCore 2 X = ⊥) :
    Nat.card (X ⧸ Open.fusionZStar X) = Nat.card (X ⧸ center X) := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv X
  rw [Nat.card_congr eZ.toEquiv]
  let e0 : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  exact Nat.card_congr (QuotientGroup.congr _ _ e0 (Subgroup.map_center_eq e0)).toEquiv

@[expose] def selfCent {S : Type*} [Group S] (t : S) : ↥(centralizer ({t} : Set S)) :=
  ⟨t, mem_centralizer_singleton_iff.2 rfl⟩

structure SporT1Data (s : TauCeti.SporadicName) : Prop where
  oddCore : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    (S ≃* Blueprint.NativeSporadic.Carrier s) → ∀ t : S, orderOf t = 2 →
      pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥
  comps : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    (S ≃* Blueprint.NativeSporadic.Carrier s) → ∀ t : S, orderOf t = 2 →
    ∀ B : Subgroup ↥(centralizer ({t} : Set S)), IsComponent B → selfCent t ∈ B →
      ¬ IndLieOrder (Nat.card (↥B ⧸ center ↥B))

theorem oddCore_of_free {s : TauCeti.SporadicName} (hs : CatalogueU.SporadicOddCoreFree s)
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* Blueprint.NativeSporadic.Carrier s) (t : S) (ht : orderOf t = 2) :
    pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥ := by
  rw [← BMCase.gmat_oddCore_eq_pPrimeCore_two]
  have hF : CFSG.generalizedFitting S = ⊤ :=
    (CFSG.generalizedFitting_eq_componentClassification S).trans
      CatLeaf.generalizedFitting_subgroup_eq_top_of_simple
  let eF : CFSG.generalizedFitting S ≃* S := (MulEquiv.subgroupCongr hF).trans topEquiv
  have : IsSimpleGroup (CFSG.generalizedFitting S) := eF.isSimpleGroup
  refine hs S inferInstance ?_ ⟨eF.trans e⟩ t ht
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem false_of_perfect
    {S : Type} [Group S] [Finite S] {t : S}
    (hO : pPrimeCore 2 ↥(centralizer ({t} : Set S)) = ⊥) {J : Subgroup S}
    (hJC : J ≤ centralizer {t}) (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal)
    (htJ : t ∈ J) (hJq : IsTwoQuasisimple ↥J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type}
    [Group L] (hLI : ∃ f : ℕ, 1 ≤ f ∧
      (IsCoverOf .POmegaOdd 3 p f 2 (L ⧸ pPrimeCore 2 L) ∨
        IsCoverOf .PSL 4 p f (Nat.gcd 4 (p ^ f - 1)) (L ⧸ pPrimeCore 2 L) ∨
        IsCoverOf .PSU 4 p f (Nat.gcd 4 (p ^ f + 1)) (L ⧸ pPrimeCore 2 L) ∨
        IsCoverOf .PSp 2 p f 2 (L ⧸ pPrimeCore 2 L) ∨
        (Even f ∧ IsSLTwoOver (p ^ f) (L ⧸ pPrimeCore 2 L))))
    (eL : L ⧸ Open.fusionZStar L ≃* ↥J ⧸ Open.fusionZStar ↥J)
    (hcomp : ∀ B : Subgroup ↥(centralizer ({t} : Set S)), IsComponent B → selfCent t ∈ B →
      ¬ IndLieOrder (Nat.card (↥B ⧸ center ↥B))) : False := by
  set C := centralizer ({t} : Set S)
  set B := J.subgroupOf C
  let eB : ↥B ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  have hOB : pPrimeCore 2 ↥B = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hJs
  have hOJ : pPrimeCore 2 ↥J = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eB, hOB, Subgroup.map_bot]
  have hBq : IsTwoQuasisimple ↥B := isTwoQuasisimple_of_mulEquiv eB.symm hJq
  have hBq' : IsQuasisimple ↥B := LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hOB).trans QuotientGroup.quotientBot) hBq.2
  have hB : IsComponent B := ⟨hBq', hJs⟩
  have htB : selfCent t ∈ B := mem_subgroupOf.2 htJ
  have hcJ : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥B ⧸ center ↥B) := by
    rw [card_quotient_fusionZStar_of_bot hOJ]
    exact (Nat.card_congr (QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB)).toEquiv).symm
  have hL : Nat.card (L ⧸ Open.fusionZStar L) = Nat.card (↥B ⧸ center ↥B) := by
    rw [Nat.card_congr eL.toEquiv, hcJ]
  have hind := indLieOrder_of_field hp hp2 hLI
  rw [hL] at hind
  exact hcomp B hB htB hind

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
