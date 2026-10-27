module

public import CFSG.LocalAnalysis.GLTheoremA.LayerCentralizerTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2LinResB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResDefs
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsFix
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Transport
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLinearDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.S151YC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38K0
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal
public import Certificates.Certificate14953
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescTD4

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.StandardType
open CFSG.PGLModel (projImage)

set_option linter.unusedSectionVars false


section Count

variable {C₀ : Type} [Group C₀] [Finite C₀] {T : Type} [Group T] [IsCyclic T]

private theorem card_le_three_mul_card_inf_conj (Θ : MulAut C₀ →* T)
    (hΘ : Θ.ker = (MulAut.conj : C₀ →* MulAut C₀).range)
    {B : Subgroup (MulAut C₀)} (hB : ∀ b ∈ B, b ^ 3 = 1) :
    Nat.card B ≤ 3 * Nat.card ↥(B ⊓ (MulAut.conj : C₀ →* MulAut C₀).range) := by
  let ρ : B →* T := Θ.comp B.subtype
  have hker : ρ.ker = (B ⊓ (MulAut.conj : C₀ →* MulAut C₀).range).subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Θ ↑x = 1 ↔ (↑x : MulAut C₀) ∈ B ⊓ (MulAut.conj : C₀ →* MulAut C₀).range
    rw [Subgroup.mem_inf, ← hΘ, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcardker : Nat.card ρ.ker =
      Nat.card ↥(B ⊓ (MulAut.conj : C₀ →* MulAut C₀).range) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hle : Nat.card B ≤ 3 * Nat.card ρ.ker :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.card_le_mul_card_ker Nat.prime_three
      (fun b => Subtype.ext (by simpa using hB b b.2)) ρ
  rwa [hcardker] at hle

end Count

section Model

private abbrev TriD4C (K : Type) [Field K] (σ : K ≃+* K) : Type :=
  ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

private theorem card_inf_conj_range_le_nine {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {A : Subgroup (MulAut (TriD4C K σ))} (hA : IsElemAbelian 3 A) :
    Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range) ≤ 9 := by
  classical
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, -, -, -, hcenter, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := n) (by omega) K hK σ hσ
  have hconj : Function.Injective (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  set E : Subgroup (TriD4C K σ) :=
    (A ⊓ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range).comap
      (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)) with hEdef
  have hEea : IsElemAbelian 3 E := (hA.mono inf_le_left).comap hconj
  have hEcard : Nat.card ↥E =
      Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range) := by
    rw [hEdef, ← Subgroup.card_map_of_injective hconj,
      Subgroup.map_comap_eq_self inf_le_right]
  have hElt : Nat.card ↥E < 3 ^ 3 :=
    CFSG.StandardType.TableBExcSmallRanks.card_lt_of_isElemAbelian_triD4 (by omega) K hK σ hσ
      hEea
  rw [← hEcard]
  obtain ⟨m, hm⟩ := hEea.isPGroup.exists_card_eq
  have hm2 : m ≤ 2 := by
    rw [hm] at hElt
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 9 := by norm_num

private theorem card_eq_twenty_seven {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {A : Subgroup (MulAut (TriD4C K σ))} (hA : IsElemAbelian 3 A)
    (hA27 : 3 ^ 3 ≤ Nat.card A) :
    Nat.card A = 27 ∧
      Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range) = 9 := by
  classical
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := n) (by omega) K hK σ hσ
  haveI : IsCyclic (K ≃+* K) := hcyc
  have hcount := card_le_three_mul_card_inf_conj Θ hΘker (B := A) (fun b hb => hA.2 b hb)
  have hle9 := card_inf_conj_range_le_nine hn hK σ hσ hA
  have h27 : 27 ≤ Nat.card A := by simpa using hA27
  have hAcard : Nat.card A = 27 := by
    have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →*
        MulAut (TriD4C K σ)).range) := hcount
    have h3 : 3 * Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →*
        MulAut (TriD4C K σ)).range) ≤ 3 * 9 := Nat.mul_le_mul_left 3 hle9
    exact le_antisymm (h1.trans (h3.trans (by norm_num))) h27
  have hdcard : Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →*
      MulAut (TriD4C K σ)).range) = 9 := by
    refine le_antisymm hle9 ?_
    have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (MulAut.conj : TriD4C K σ →*
        MulAut (TriD4C K σ)).range) := hcount
    rw [hAcard] at h1
    omega
  exact ⟨hAcard, hdcard⟩

end Model


private theorem layer_fixed_shape (hP : PGLThreeInvGood)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {H : Subgroup (TriD4C K σ)} (σ' : MulAut (TriD4C K σ))
    (hσ'3 : σ' ^ 3 = 1)
    (hσ'out : σ' ∉ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range)
    (hH : H = fixSubgroup σ') {x t : TriD4C K σ} (hxH : x ∈ H) (htH : t ∈ H)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (ht2 : orderOf t = 2) (hxt : x * t = t * x) :
    GLAPLayer 3 (H ⊓ Subgroup.centralizer ({x} : Set (TriD4C K σ))) ≠ ⊥ := by
  classical
  let x' : ↥H := ⟨x, hxH⟩
  let t' : ↥H := ⟨t, htH⟩
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have ht'2 : orderOf t' = 2 := by
    have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have htn : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      omega
    exact orderOf_eq_prime (Subtype.ext (by simpa using ht2'))
      (fun h => htn (congrArg Subtype.val h))
  have hx't' : x' * t' = t' * x' := Subtype.ext (by simpa using hxt)
  have hshape : GGTriD4FixedShape n ↥H := by
    rw [hH]
    exact ggTriD4_fixedShape_Y (n := n) (K₃ := K) (by omega) hK σ hσ σ' hσ'3 hσ'out
  rcases hshape with ⟨k, hkF, hkFin, hkcard, ⟨e⟩⟩
    | ⟨hneven, F, hFF, hFFin, hFcard, ⟨e⟩⟩
    | ⟨hnodd, F, hFF, hFFin, hFcard, ⟨e⟩⟩
  · letI := hkF
    letI := hkFin
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP k 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hkcard
    have hkchar : ringChar k = 2 := ringChar.eq k 2
    have hk3 : ringChar k ≠ 3 := by rw [hkchar]; norm_num
    have hk4 : 4 ≤ Nat.card k := by
      rw [hkcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hx'e3 : (e x') ^ 3 = 1 := by rw [← map_pow, hx'3, map_one]
    have hx'e1 : e x' ≠ 1 := fun h => hx'1 (e.injective (by rw [h, map_one]))
    have hm : GLAPLayer 3
        (Subgroup.centralizer ({e x'} : Set ↥(adjointGroup .G2 k))) ≠ ⊥ :=
      glaPLayer_centralizer_ne_bot_g2 hk3 hk4 hx'e3 hx'e1
    have h1 : GLAPLayer 3 (Subgroup.centralizer ({x'} : Set ↥H)) ≠ ⊥ :=
      (glaPLayer_centralizer_ne_bot_iff_of_mulEquiv (p := 3) Nat.prime_three e x').mp hm
    exact (glaPLayer_centralizer_subtype_ne_bot_iff (p := 3) Nat.prime_three x').mp h1
  · letI := hFF
    letI := hFFin
    have hx'e3 : (e x') ^ 3 = 1 := by rw [← map_pow, hx'3, map_one]
    have hx'e1 : e x' ≠ 1 := fun h => hx'1 (e.injective (by rw [h, map_one]))
    have ht'e2 : orderOf (e t') = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact ht'2
    have hcomm' : e x' * e t' = e t' * e x' := by rw [← map_mul, hx't', map_mul]
    have h1 : GLAPLayer 3 (Subgroup.centralizer ({x'} : Set ↥H)) ≠ ⊥ :=
      (glaPLayer_centralizer_ne_bot_iff_of_mulEquiv (p := 3) Nat.prime_three e x').mp
        (hP.1 n hn hneven F hFcard (e x') (e t') hx'e3 hx'e1 ht'e2 hcomm')
    exact (glaPLayer_centralizer_subtype_ne_bot_iff (p := 3) Nat.prime_three x').mp h1
  · letI := hFF
    letI := hFFin
    have hx'e3 : (e x') ^ 3 = 1 := by rw [← map_pow, hx'3, map_one]
    have hx'e1 : e x' ≠ 1 := fun h => hx'1 (e.injective (by rw [h, map_one]))
    have ht'e2 : orderOf (e t') = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact ht'2
    have hcomm' : e x' * e t' = e t' * e x' := by rw [← map_mul, hx't', map_mul]
    have h1 : GLAPLayer 3 (Subgroup.centralizer ({x'} : Set ↥H)) ≠ ⊥ :=
      (glaPLayer_centralizer_ne_bot_iff_of_mulEquiv (p := 3) Nat.prime_three e x').mp
        (hP.2 n hn hnodd F hFcard (e x') (e t') hx'e3 hx'e1 ht'e2 hcomm')
    exact (glaPLayer_centralizer_subtype_ne_bot_iff (p := 3) Nat.prime_three x').mp h1

private theorem isGood_of_outer (hP : PGLThreeInvGood)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {B : Subgroup (MulAut (TriD4C K σ))} {t : TriD4C K σ}
    (hB9 : Nat.card B = 9) (hB : IsElemAbelian 3 B)
    (htB : ∀ b ∈ B, b t = t) (ht2 : orderOf t = 2)
    (hBout : ∃ σ' ∈ B, σ' ∉ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range) :
    IsGood 3 B := by
  classical
  obtain ⟨σ', hσ'B, hσ'out⟩ := hBout
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, hcenter, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := n) (by omega) K hK σ hσ
  haveI : IsCyclic (K ≃+* K) := hcyc
  have hconj : Function.Injective (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  have hBinn3 : 3 ≤ Nat.card ↥(B ⊓ (MulAut.conj : TriD4C K σ →*
      MulAut (TriD4C K σ)).range) := by
    have hcount := card_le_three_mul_card_inf_conj Θ hΘker (B := B) hB.2
    have h9 : (9 : ℕ) ≤ 3 * Nat.card ↥(B ⊓ (MulAut.conj : TriD4C K σ →*
        MulAut (TriD4C K σ)).range) := by
      calc (9 : ℕ) = Nat.card B := hB9.symm
        _ ≤ 3 * Nat.card ↥(B ⊓ (MulAut.conj : TriD4C K σ →*
            MulAut (TriD4C K σ)).range) := hcount
    omega
  have hBinnne : B ⊓ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hBinn3
    omega
  obtain ⟨⟨c, hcBinn⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBinnne
  have hcB : c ∈ B := (Subgroup.mem_inf.1 hcBinn).1
  have hcInn : c ∈ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range :=
    (Subgroup.mem_inf.1 hcBinn).2
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hσ'3 : σ' ^ 3 = 1 := hB.2 σ' hσ'B
  have hcl : Subgroup.closure {σ', c} = B :=
    HDescLinRes.closure_eq_of_card_nine_not_mem hB9 hσ'B hcB hσ'3 hσ'out hcInn hc1'
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hcInn
  have hx3 : x ^ 3 = 1 := by
    apply hconj
    rw [map_pow, hB.2 (MulAut.conj x) hcB, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    exact hc1' (by rw [h, map_one])
  have hcomm : σ' * MulAut.conj x * σ'⁻¹ = MulAut.conj x := by
    have h : σ' * MulAut.conj x = MulAut.conj x * σ' :=
      congrArg Subtype.val (hB.1.is_comm.comm ⟨σ', hσ'B⟩ ⟨MulAut.conj x, hcB⟩)
    calc σ' * MulAut.conj x * σ'⁻¹ = (MulAut.conj x * σ') * σ'⁻¹ := by rw [h]
      _ = MulAut.conj x := by group
  have hσ'x : σ' x = x := by
    apply hconj
    calc MulAut.conj (σ' x) = σ' * MulAut.conj x * σ'⁻¹ := by
          ext y
          simp [MulAut.conj_apply, MulAut.mul_apply, map_mul]
      _ = MulAut.conj x := hcomm
  have htσ' : σ' t = t := htB σ' hσ'B
  have htx : x * t = t * x := by
    have h := htB (MulAut.conj x) hcB
    rw [MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hxH : x ∈ fixSubgroup σ' := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    exact hσ'x
  have htH : t ∈ fixSubgroup σ' := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    exact htσ'
  have hlayer : GLAPLayer 3 (fixSubgroup σ' ⊓ Subgroup.centralizer ({x} : Set (TriD4C K σ))) ≠ ⊥ :=
    layer_fixed_shape hP hn hK σ hσ σ' hσ'3 hσ'out rfl hxH htH hx3 hx1 ht2 htx
  have hlayer' : GLAPLayer 3 (fixSubgroup σ' ⊓ fixSubgroup (MulAut.conj x)) ≠ ⊥ := by
    rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fixSubgroup_conj]
    exact hlayer
  rw [← hcl]
  exact HDescLinRes.isGood_closure_pair σ' (MulAut.conj x) hlayer'

theorem goodSubThree_triD4 (hI : TriD4InvCentRankOne) (hP : PGLThreeInvGood) {n : ℕ}
    (hn : 2 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    HDescLinRes.GoodSubThree ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  change HDescLinRes.GoodSubThree (TriD4C K σ)
  classical
  intro A hA hA27 T hT2 hT hAT
  obtain ⟨hAcard, -⟩ := card_eq_twenty_seven hn hK σ hσ hA hA27
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  obtain ⟨B, hBA, hBmul, t, -, ht2, htB⟩ :=
    HDescLinRes.exists_hyperplane_fix_involution Nat.prime_three (by norm_num) hA hA1 hT2 hT hAT
  have hB9 : Nat.card B = 9 := by
    rw [hAcard] at hBmul
    omega
  have hBea : IsElemAbelian 3 B := hA.mono hBA
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, hcenter, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := n) (by omega) K hK σ hσ
  have hconj : Function.Injective (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  by_cases hBinn : B ≤ (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range
  · set B₀ : Subgroup (TriD4C K σ) :=
      B.comap (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)) with hB0def
    have hB0ea : IsElemAbelian 3 B₀ := hBea.comap hconj
    have hB0card : Nat.card B₀ = 9 := by
      rw [hB0def, ← Subgroup.card_map_of_injective hconj,
        Subgroup.map_comap_eq_self hBinn, hB9]
    have hB0cent : ∀ e ∈ B₀, e * t = t * e := by
      intro e he
      have heB : MulAut.conj e ∈ B := by
        rw [hB0def, Subgroup.mem_comap] at he
        exact he
      have hfix := htB (MulAut.conj e) heB
      rw [MulAut.conj_apply] at hfix
      exact mul_inv_eq_iff_eq_mul.1 hfix
    have hle : Nat.card B₀ ≤ 3 := hI n (by omega) K hK σ hσ t ht2 B₀ hB0ea hB0cent
    rw [hB0card] at hle
    omega
  · have hBout : ∃ σ' ∈ B, σ' ∉
        (MulAut.conj : TriD4C K σ →* MulAut (TriD4C K σ)).range := by
      by_contra h
      push Not at h
      exact hBinn h
    refine ⟨B, hBA, by simpa using hB9, ?_⟩
    exact isGood_of_outer hP hn hK σ hσ hB9 hBea htB ht2 hBout

theorem goodSubAt_triD4 (hI : TriD4InvCentRankOne) (hP : PGLThreeInvGood)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (hq : q.p = 2) (hq2 : 2 < q.card) :
    HDesc.GoodSubAt 3 ⟨.trialityD4 q, hv⟩ 2 := by
  classical
  intro hfin h3dvd A hA hcard T hT2 hT hAT
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hn : 2 ≤ q.exponent := by
    have hqcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
    rw [hqcard, hq] at hq2
    by_contra h
    have h1 : q.exponent ≤ 1 := by omega
    have h2 : 2 ^ q.exponent ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hK2 : Nat.card K = (2 ^ q.exponent) ^ 3 := by
    simpa [hq] using hK
  have hσ2 : ∀ c, σ c = c ^ 2 ^ q.exponent := by
    simpa [hq] using hσ
  have hgood := goodSubThree_triD4 hI hP hn K hK2 σ hσ2
  have hgood' : HDescLinRes.GoodSubThree (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group :=
    HDescLinRes.GoodSubThree.of_mulEquiv eC.symm hgood
  exact hgood' A hA hcard T hT2 hT hAT

end CFSG.LocalAnalysis.GLTheoremA.HDescTD4

end
