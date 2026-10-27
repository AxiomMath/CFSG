module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Plane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Field
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3ResidualQ
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.PartOne
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical.SteinbergBY CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open scoped Pointwise

section Dichotomy

theorem mem_of_pow_mem_of_relIndex_two_pow {M : Type*} [Group M] {I L : Subgroup M}
    [I.Normal] {k : ℕ} (hk : I.relIndex L = 2 ^ k) {δ : M} (hδ : δ ∈ L) {j : ℕ}
    (hj : δ ^ (3 ^ j) ∈ I) : δ ∈ I := by
  set x : L ⧸ I.subgroupOf L := QuotientGroup.mk (⟨δ, hδ⟩ : L) with hx
  have hxk : x ^ (3 ^ j) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hj
  have hcard : Nat.card (L ⧸ I.subgroupOf L) = I.relIndex L := (Subgroup.index_eq_card _).symm
  have hdvd1 : orderOf x ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hxk
  have hdvd2 : orderOf x ∣ 2 ^ k := by
    rw [← hk, ← hcard]
    exact orderOf_dvd_natCard x
  have hcop : Nat.Coprime (3 ^ j) (2 ^ k) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : L)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

theorem d4_plane_or_field (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3) :
    (∃ E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      E ≤ D ∧ E ≤ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∧
        IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2) ∨
    ∃ a ∈ D, a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range ∧ orderOf a = 3 := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 ℓ f h K hK e
  obtain ⟨-, -, ⟨hInnL, k, hrel⟩, horb, -, hEA, -⟩ := hgates
  have : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := inferInstance
  have : Finite (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := inferInstance
  have hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3 := by
    have hst : (projectivePointFamilyAut (coordinateQuadPlus 4 K)).index =
        (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
          (projectivePointFamily (coordinateQuadPlus 4 K))).ncard :=
      MulAction.index_stabilizer _ _
    rw [← hEA, hst]
    exact horb
  have hge := card_inf_ge_of_index_le hp hcard hidx
  by_cases hex : ∃ a ∈ D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K),
      a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range
  · right
    obtain ⟨a, ⟨haD, haE⟩, hanot⟩ := hex
    have ha1 : a ≠ 1 := fun h1 => hanot (h1 ▸ Subgroup.one_mem _)
    exact ⟨a, haD, haE, hanot, orderOf_eq_prime (hD.2 a haD) ha1⟩
  · left
    push Not at hex
    have hinn : D ⊓ matrixProjectiveImage (coordinateQuadPlus 4 K) ≤
        D ⊓ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
      intro a ha
      refine ⟨ha.1, ?_⟩
      have hL := hex a ha
      refine mem_of_pow_mem_of_relIndex_two_pow hrel hL (j := 1) ?_
      rw [pow_one, hD.2 a ha.1]
      exact Subgroup.one_mem _
    exact exists_plane_of_card_inf_ge hp hD hcard ((hge.trans (Subgroup.card_le_of_le hinn)))

end Dichotomy

section Main

theorem d4_isLocallyBalancedAbs_three (G : Type) [Group G] {ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (hℓ3 : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) (hK4 : 4 ≤ Nat.card K)
    (hrig : ∀ A : Subgroup (ProjOrthDerived (coordinateQuadPlus 4 K)), IsElemAbelian 3 A →
      Nat.card A = 3 ^ 2 → ∀ g : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)),
        (∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer
          ({a} : Set (ProjOrthDerived (coordinateQuadPlus 4 K))),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived (coordinateQuadPlus 4 K)))⁆,
          g n = n) → g = 1) :
    IsLocallyBalancedAbs 3 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hpl : 3 ≠ ringChar K := by
    rw [hchar]
    exact hℓ3
  have hd : 0 < 2 * 4 := by norm_num
  have hplanes : InnerPlanesBalanced 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    InnerPlanesBalanced.of_mulEquiv (KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 K) hd)
      (innerPlanesBalanced_projOrth3 hnd hT Nat.prime_three (by norm_num) hK4 hpl hrig)
  refine isLocallyBalancedAbs_of_planes_or_element hplanes fun D hD hcard => ?_
  rcases d4_plane_or_field G h K hK e D hD hcard with hplane | ⟨a, haD, haE, haL, hao⟩
  · exact Or.inl hplane
  · exact Or.inr fun H hH => d4_localDeltaIn_eq_bot_of_field G h hℓ3 K hK e a haE haL hao haD hH

@[expose] def regimeD4Three (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .D 4 q ∧ p = 3 ∧ q.card ≠ 2

theorem crossCharFamAt_D_four_three : CrossCharFamAt .D regimeD4Three := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, rfl, hq2⟩
  change d = _ at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card F = q.p ^ q.exponent :=
    card_fixedField_validIndex_orth ⟨.D 4 q, hv⟩ 4 q (Or.inr (Or.inl rfl))
  have hring : ringChar F = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK4 : 4 ≤ Nat.card F := by
    rw [hcard, ← hqc]
    have h2 : 2 ≤ q.card := by
      rw [hqc]
      exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
    by_contra hlt
    have h3 : q.card = 3 := by omega
    apply hpq
    have : q.p ∣ 3 := h3 ▸ (hqc ▸ dvd_pow_self q.p q.exponent_pos.ne')
    exact ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp this).symm
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  have hmodel : StatedClassicalModel (Cat ⟨.D 4 q, hv⟩) .POmegaPlus 4 q.p q.exponent :=
    statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)
  have hcard' : Nat.card F = q.p ^ q.exponent := hcard
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus hmodel F hcard' e₁
  have hpl : 3 ≠ ringChar F := by rw [hring]; exact hpq
  have hrig : ∀ A : Subgroup (ProjOrthDerived (coordinateQuadPlus 4 F)), IsElemAbelian 3 A →
      Nat.card A = 3 ^ 2 → ∀ g : MulAut (ProjOrthDerived (coordinateQuadPlus 4 F)),
        (∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer
          ({a} : Set (ProjOrthDerived (coordinateQuadPlus 4 F))),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived (coordinateQuadPlus 4 F)))⁆,
          g n = n) → g = 1 := by
    intro A hA hAc g hg
    rcases three_dvd_card_sub_or_add_one (q := q) (fun h => hpq h.symm) with h1 | h1
    · exact orth3_split_derived_rigid hnd hT Nat.prime_three (by norm_num)
        (by rw [hcard, ← hqc]; exact h1) A ⟨hA.1, hA.2⟩ hAc g hg
    · exact d4_qplus_derived_rigid (Cat ⟨.D 4 q, hv⟩) hmodel F hcard' e₁ Nat.prime_three
        (by norm_num) hK4 hpl (by rw [hcard, ← hqc]; exact h1) A ⟨hA.1, hA.2⟩ hAc g hg
  exact IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv F e₁)
    (d4_isLocallyBalancedAbs_three (Cat ⟨.D 4 q, hv⟩) hmodel hpq F hcard' e₁ hK4 hrig)

end Main

section Residual

@[expose] def regimeDAll5 (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  regimeDAll4 idx p ∨ regimeD4Three idx p

theorem crossCharFamAt_D_all5 : CrossCharFamAt .D regimeDAll5 := by
  intro idx hk p hp hp2 hc hR
  rcases hR with hR | hR
  · exact crossCharFamAt_D_all4 idx hk p hp hp2 hc hR
  · exact crossCharFamAt_D_four_three idx hk p hp hp2 hc hR

theorem not_regimeDAll5_iff {idx : TauCeti.ValidLieTypeIndex} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : LieFamily.D.Matches idx.1) (hc : idx.1.characteristic ≠ p) :
    ¬ regimeDAll5 idx p ↔ p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧
      q.card = 2 := by
  unfold regimeDAll5
  rw [not_or, not_regimeDAll4_iff hp hp2 hk hc]
  constructor
  · rintro ⟨⟨h3, r, q, hrq, hcond⟩, hn⟩
    refine ⟨h3, r, q, hrq, ?_⟩
    rcases hcond with hr4 | hq2
    · by_contra hq2
      subst hr4
      exact hn ⟨q, hrq, h3, hq2⟩
    · exact hq2
  · rintro ⟨h3, r, q, hrq, hq2⟩
    refine ⟨⟨h3, r, q, hrq, Or.inr hq2⟩, ?_⟩
    rintro ⟨q', hrq', -, hq2'⟩
    rw [hrq] at hrq'
    obtain ⟨-, hq⟩ : (r = 4) ∧ q = q' := by
      injection hrq' with h1 h2
      exact ⟨h1, h2⟩
    subst hq
    exact hq2' hq2

theorem crossCharFamAt_not_regimeDAll5_iff :
    CrossCharFamAt .D (fun idx p => ¬ regimeDAll5 idx p) ↔
      CrossCharFamAt .D (fun idx p => p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower),
        idx.1 = .D r q ∧ q.card = 2) := by
  constructor
  · intro h idx hk p hp hp2 hc hR
    exact h idx hk p hp hp2 hc ((not_regimeDAll5_iff hp hp2 hk hc).2 hR)
  · intro h idx hk p hp hp2 hc hR
    exact h idx hk p hp hp2 hc ((not_regimeDAll5_iff hp hp2 hk hc).1 hR)

end Residual

end CFSG.HardMathSupport.Timmesfeld.CrossChar
