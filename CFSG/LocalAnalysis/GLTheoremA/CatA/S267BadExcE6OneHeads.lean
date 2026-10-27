module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6OneAct
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSignalizer
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.CGT.PushingUpLit.Transport
import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.NoOffE6Three CFSG.StandardType.TableBExc.E6Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

section Transport

variable {Ω : Type} [Group Ω] {S : Subgroup Ω} {X : Type} [Group X]

theorem ker_conj_comp (Γ : Ω →* MulAut X) (ψ : MulAut X) :
    ((MulAut.conj ψ).toMonoidHom.comp Γ).ker = Γ.ker := by
  ext b
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro h
    have h' : Γ b = ψ⁻¹ * 1 * ψ := by rw [← h]; group
    rw [h']
    group
  · intro h
    rw [h]
    group

theorem concA_of_concA_of_card_le {p : ℕ} [Finite Ω] {B B' : Subgroup Ω} (h : S267ConcA p S B')
    (hcard : Nat.card B ≤ Nat.card B') {T : Subgroup Ω} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hB'T : B' ≤ Subgroup.normalizer (T : Set Ω)) : S267ConcA p S B := by
  obtain ⟨B'', D, J, hB'', hD, hor, hBC, t, ht1, ht2, htD, htJ⟩ := h
  refine ⟨B'', D, J, hB'', hD, Or.inr ?_, hBC, t, ht1, ht2, htD, htJ⟩
  rcases hor with rfl | ⟨hle, T', hT', hT'2, hN⟩
  · exact ⟨hcard, T, hT, hT2, hB'T⟩
  · exact ⟨hcard.trans hle, T', hT', hT'2, hN⟩

end Transport

section Diag

variable {K : Type} [Field K]

theorem map_entrywiseHom_diagHom {σ : K ≃+* K} {ζ : Kˣ} (hζ : ζ ^ 3 = 1) (hσζ : σ (ζ : K) = ζ)
    (z : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    Units.map (entrywiseHom σ.toRingHom) (diagHom ζ hζ z) = diagHom ζ hζ z := by
  apply Units.ext
  change entrywise σ.toRingHom (rootDiag (zetaHom ζ hζ z)) = rootDiag (zetaHom ζ hζ z)
  rw [entrywise_rootDiag]
  congr 1
  funext i
  change Units.map σ.toRingHom.toMonoidHom (ζ ^ (Multiplicative.toAdd z i).val) =
    ζ ^ (Multiplicative.toAdd z i).val
  rw [map_pow]
  congr 1
  exact Units.ext hσζ

theorem entrywiseAdjointAut_mul_diag3 {σ : K ≃+* K} {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hσζ : σ (ζ : K) = ζ) (z : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    entrywiseAdjointAut .E6 σ * diag3 ζ hζ z = diag3 ζ hζ z * entrywiseAdjointAut .E6 σ := by
  have hd := map_entrywiseHom_diagHom hζ hσζ z
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_entrywiseAdjointAut, coe_diag3_apply,
    coe_diag3_apply, coe_entrywiseAdjointAut, map_mul, map_mul, map_inv, hd]

theorem exists_eq_of_mem_closure_diag3 {σ : K ≃+* K} {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hσζ : σ (ζ : K) = ζ) (hσ3 : σ ^ 3 = 1) {f : MulAut (adjointGroup .E6 K)}
    (hf : f ∈ Subgroup.closure (Set.range (diag3 ζ hζ) ∪ {entrywiseAdjointAut .E6 σ})) :
    ∃ z, ∃ k : ℕ, f = diag3 ζ hζ z * entrywiseAdjointAut .E6 σ ^ k := by
  set s := entrywiseAdjointAut .E6 σ with hs
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← entrywiseAdjointAut_pow, hσ3]
    exact map_one (entrywiseAdjointAutHom (τ := .E6) (K := K))
  have hcomm : ∀ z (k : ℕ), s ^ k * diag3 ζ hζ z = diag3 ζ hζ z * s ^ k := by
    intro z k
    induction k with
    | zero => rw [pow_zero, one_mul, mul_one]
    | succ k ih =>
      rw [pow_succ, mul_assoc, hs, entrywiseAdjointAut_mul_diag3 hζ hσζ, ← hs, ← mul_assoc, ih,
        mul_assoc]
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
    rcases hf with ⟨z, rfl⟩ | hf
    · exact ⟨z, 0, by rw [pow_zero, mul_one]⟩
    · rw [Set.mem_singleton_iff] at hf
      exact ⟨1, 1, by rw [hf, map_one, one_mul, pow_one]⟩
  | one => exact ⟨1, 0, by rw [map_one, pow_zero, one_mul]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨z, k, rfl⟩ := hf
    obtain ⟨z', k', rfl⟩ := hg
    refine ⟨z * z', k + k', ?_⟩
    rw [map_mul, pow_add, mul_assoc, ← mul_assoc (s ^ k), hcomm z' k, mul_assoc, mul_assoc]
  | inv f _ hf =>
    obtain ⟨z, k, rfl⟩ := hf
    refine ⟨z⁻¹, 2 * k, ?_⟩
    have hinv : (s ^ k)⁻¹ = s ^ (2 * k) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, hs3, one_pow]
    rw [mul_inv_rev, hinv, ← map_inv, hcomm]

end Diag

section Field

theorem exists_hom_ringAut_E6_three (K : Type) [Field K] [Finite K] :
    ∃ Θ : MulAut (adjointGroup .E6 K) →* RingAut K, ∀ x ∈ Θ.ker, x ^ 3 = 1 →
      x ∈ (hatAut .E6 K).range := by
  obtain ⟨Φ, -, hker, -⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  refine ⟨(MonoidHom.fst _ _).comp (Φ.comp (QuotientGroup.mk' (inner (adjointGroup .E6 K)))), ?_⟩
  intro x hx hx3
  set y := QuotientGroup.mk' (inner (adjointGroup .E6 K)) x with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, hx3, map_one]
  have h1 : (Φ y).1 = 1 := hx
  have h2 : (Φ y).2 = 1 := by
    have hE : exactE Tag.E6 = 2 := rfl
    have hcard : Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 2 := by
      rw [hE, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have hz2 : (Φ y).2 ^ 2 = 1 := by
      have h0 : (Φ y).2 ^ Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 1 :=
        pow_card_eq_one'
      rwa [hcard] at h0
    have hz3 : (Φ y).2 ^ 3 = 1 := by
      have := congrArg Prod.snd (show Φ y ^ 3 = 1 by rw [← map_pow, hy3, map_one])
      simpa using this
    have hcop : Nat.Coprime 2 3 := by norm_num
    exact (pow_eq_one_iff_of_coprime hcop).1 ⟨hz2, hz3⟩
  have hyk : y ∈ Φ.ker := Prod.ext h1 h2
  rw [hker] at hyk
  obtain ⟨a, ha⟩ := hyk
  have hq : QuotientGroup.mk' (inner (adjointGroup .E6 K)) (rootDiagAutHom .E6 K a) =
      QuotientGroup.mk' (inner (adjointGroup .E6 K)) x := ha
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
  rw [hatAut_range_eq_sup]
  have hx : x = rootDiagAutHom .E6 K a * ((rootDiagAutHom .E6 K a)⁻¹ * x) := by group
  rw [hx]
  exact mul_mem (Subgroup.mem_sup_right ⟨a, rfl⟩) (Subgroup.mem_sup_left hq)

theorem card_le_three_mul_card_inf_hatAut {K : Type} [Field K] [Finite K]
    {A : Subgroup (MulAut (adjointGroup .E6 K))} (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (hatAut .E6 K).range) := by
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E6_three K
  have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Θ A
  have h1 : Nat.card (A.map Θ) ≤ 3 := by
    haveI : Finite ↥(A.map Θ) := Finite.of_surjective
      (fun x : ↥A => (⟨Θ x, Subgroup.mem_map_of_mem Θ x.2⟩ : ↥(A.map Θ)))
      (fun y => by
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
    refine CFSG.LocalAnalysis.RankFourTheoremC.card_le_of_isCyclic_of_pow_eq_one (by norm_num)
      fun y => ?_
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxy, ← map_pow, hA.2 x hx, map_one]
  have h2 : Nat.card ↥(A ⊓ Θ.ker) ≤ Nat.card ↥(A ⊓ (hatAut .E6 K).range) :=
    Subgroup.card_le_of_le fun x hx => ⟨hx.1, hΘ x hx.2 (hA.2 x hx.1)⟩
  rw [← h]
  exact Nat.mul_le_mul h1 h2

theorem hatAut_range_normal (K : Type) [Field K] [Finite K] :
    ((hatAut .E6 K).range).Normal := by
  obtain ⟨Φ, -, hker, -⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  have e : (hatAut .E6 K).range = (Φ.comp (QuotientGroup.mk' (inner (adjointGroup .E6 K)))).ker := by
    refine le_antisymm ?_ fun x hx => ?_
    · rw [hatAut_range_eq_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨g, rfl⟩
        have hg : MulAut.conj g ∈ inner (adjointGroup .E6 K) := ⟨g, rfl⟩
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff _).2 hg, map_one]
      · rintro _ ⟨a, rfl⟩
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        have : QuotientGroup.mk' (inner (adjointGroup .E6 K)) (rootDiagAutHom .E6 K a) ∈ Φ.ker := by
          rw [hker]
          exact ⟨a, rfl⟩
        exact this
    · have hyk : QuotientGroup.mk' (inner (adjointGroup .E6 K)) x ∈ Φ.ker := hx
      rw [hker] at hyk
      obtain ⟨a, ha⟩ := hyk
      have hq : QuotientGroup.mk' (inner (adjointGroup .E6 K)) (rootDiagAutHom .E6 K a) =
          QuotientGroup.mk' (inner (adjointGroup .E6 K)) x := ha
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
      rw [hatAut_range_eq_sup]
      have hx : x = rootDiagAutHom .E6 K a * ((rootDiagAutHom .E6 K a)⁻¹ * x) := by group
      rw [hx]
      exact mul_mem (Subgroup.mem_sup_right ⟨a, rfl⟩) (Subgroup.mem_sup_left hq)
  rw [e]
  exact MonoidHom.normal_ker _

end Field

section Hyp

variable {K : Type} [Field K]

theorem diagHom_hypIncl_mem (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Multiplicative CFSG.StandardType.NoOffRest.hypE6) :
    diagHom ζ hζ (hypIncl x) ∈ adjointGroup .E6 K := by
  obtain ⟨y, hy⟩ := zetaVec_eq_cartanChar_of_mem_hyp ζ hζ (Multiplicative.toAdd x).2
  change rootDiagUnit .E6 (zetaVec ζ hζ (Multiplicative.toAdd x).1) ∈ adjointGroup .E6 K
  rw [hy]
  exact CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
    (rootDiagUnit_cartanChar_mem_torusGroup _)

@[expose] noncomputable def hypTorusHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative CFSG.StandardType.NoOffRest.hypE6 →* ↥(adjointGroup .E6 K) :=
  ((diagHom ζ hζ).comp hypIncl).codRestrict (adjointGroup .E6 K) (diagHom_hypIncl_mem ζ hζ)

theorem conj_hypTorusHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Multiplicative CFSG.StandardType.NoOffRest.hypE6) :
    MulAut.conj (hypTorusHom ζ hζ x) = diag3 ζ hζ (hypIncl x) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem hypTorusHom_injective {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (hypTorusHom (K := K) ζ hζ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : diag3 ζ hζ (hypIncl x) = diag3 ζ hζ (hypIncl 1) := by
    rw [← conj_hypTorusHom, hx, map_one, map_one, map_one]
  exact hypIncl_injective (diag3_injective hζo hζ h1)

theorem card_range_hypTorusHom {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Nat.card (hypTorusHom (K := K) ζ hζ).range = 3 ^ 5 := by
  rw [card_range_of_injective' (hypTorusHom_injective hζo hζ),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative CFSG.StandardType.NoOffRest.hypE6 ≃ _)]
  exact CFSG.StandardType.NoOffRest.card_hypE6

theorem isElemAbelian_range_hypTorusHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    IsElemAbelian 3 (hypTorusHom (K := K) ζ hζ).range := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨u, hu⟩ := x.2
    obtain ⟨v, hv⟩ := y.2
    change (x : ↥(adjointGroup .E6 K)) * y = y * x
    rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, pow_three_eq_one_hyp, map_one]

theorem entrywiseAdjointAut_hypTorusHom {σ : K ≃+* K} {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (hσζ : σ (ζ : K) = ζ) (x : Multiplicative CFSG.StandardType.NoOffRest.hypE6) :
    entrywiseAdjointAut .E6 σ (hypTorusHom ζ hζ x) = hypTorusHom ζ hζ x := by
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut]
  exact map_entrywiseHom_diagHom hζ hσζ _

theorem rootDiagUnit_neg_one_mem :
    rootDiagUnit .E6 (Pi.mulSingle (highNode .E6) (-1 : Kˣ)) ∈ adjointGroup .E6 K :=
  CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
    (rootDiagUnit_mulSingle_mem_torusGroup (sum_highRoot_mul_cartan (Or.inl rfl)) _)

@[expose] noncomputable def thetaInv (K : Type) [Field K] : ↥(adjointGroup .E6 K) :=
  ⟨_, rootDiagUnit_neg_one_mem⟩

theorem thetaInv_ne_one (hK2 : ringChar K ≠ 2) : thetaInv K ≠ 1 := by
  intro h1
  have h := congrArg (fun g : ↥(adjointGroup .E6 K) => (g : ModGL .E6 K)) h1
  change rootDiagUnit .E6 (Pi.mulSingle (highNode .E6) (-1 : Kˣ)) = 1 at h
  rw [← rootDiagUnit_one (τ := .E6) (K := K)] at h
  have h' := congrFun (rootDiagUnit_injective h) (highNode .E6)
  rw [Pi.mulSingle_eq_same, Pi.one_apply] at h'
  exact hK2 ((neg_one_eq_one_iff (R := K)).1 (by simpa using congrArg Units.val h'))

theorem thetaInv_sq : thetaInv K ^ 2 = 1 := by
  apply Subtype.ext
  change rootDiagUnit .E6 (Pi.mulSingle (highNode .E6) (-1 : Kˣ)) ^ 2 = 1
  rw [rootDiagUnit_pow_hr, ← rootDiagUnit_one (τ := .E6) (K := K)]
  congr 1
  rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]

theorem hypTorusHom_mul_thetaInv (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Multiplicative CFSG.StandardType.NoOffRest.hypE6) :
    hypTorusHom ζ hζ x * thetaInv K = thetaInv K * hypTorusHom ζ hζ x := by
  apply Subtype.ext
  change rootDiagUnit .E6 (zetaHom ζ hζ (hypIncl x)) *
      rootDiagUnit .E6 (Pi.mulSingle (highNode .E6) (-1 : Kˣ)) =
    rootDiagUnit .E6 (Pi.mulSingle (highNode .E6) (-1 : Kˣ)) *
      rootDiagUnit .E6 (zetaHom ζ hζ (hypIncl x))
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem entrywiseAdjointAut_thetaInv (σ : K ≃+* K) :
    entrywiseAdjointAut .E6 σ (thetaInv K) = thetaInv K := by
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut]
  apply Units.ext
  change entrywise σ.toRingHom (rootDiag (Pi.mulSingle (highNode .E6) (-1 : Kˣ))) =
    rootDiag (Pi.mulSingle (highNode .E6) (-1 : Kˣ))
  rw [entrywise_rootDiag]
  congr 1
  funext i
  by_cases hi : i = highNode .E6
  · subst hi
    rw [Pi.mulSingle_eq_same]
    exact Units.ext (by simp)
  · rw [Pi.mulSingle_eq_of_ne hi, map_one]

end Hyp

section Count

variable {K : Type} [Field K]

theorem three_dvd_of_pow_mem {G : Type*} [Group G] {I : Subgroup G} {s : G} (hs3 : s ^ 3 = 1)
    (hsI : s ∉ I) {k : ℕ} (hk : s ^ k ∈ I) : 3 ∣ k := by
  rw [pow_eq_pow_mod k hs3] at hk
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exact Nat.dvd_of_mod_eq_zero h
  · rw [h, pow_one] at hk
    exact absurd hk hsI
  · rw [h] at hk
    exfalso
    apply hsI
    have e : s = (s ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hs3, one_mul]
    rw [e]
    exact pow_mem hk 2

theorem card_le_pow_five_of_not_le {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 3 A) (h : ¬ 3 ^ 6 ≤ Nat.card A) : Nat.card A ≤ 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.Open.IsElemAbelian.isPGroup hA)
  rw [hk] at h ⊢
  apply Nat.pow_le_pow_right (by norm_num)
  by_contra hk5
  exact h (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem card_eq_card_map_mul_three {Ω : Type} [Group Ω] {S B : Subgroup Ω} {X : Type} [Group X]
    {Γ : Ω →* MulAut X} (hΓker : Γ.ker = centModSubgroup 3 S)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) : Nat.card B = Nat.card (B.map Γ) * 3 := by
  have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ B
  rw [hΓker, hBC] at h
  exact h.symm

end Count

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

end
