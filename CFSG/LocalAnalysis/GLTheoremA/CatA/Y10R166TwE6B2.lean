module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverLifts
public import CFSG.LieType.Chevalley.HeightSeries
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open scoped commutatorElement

section Certs


def twE6C4 (α : Fin TwistTag.E6.tag.rank → ℤ) : ℤ := α ⟨3, by decide⟩

def twE6Eleven : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {α | IsRoot TwistTag.E6.tag α ∧ 2 ≤ twE6C4 α}

theorem twE6Eleven_ncard : twE6Eleven.ncard = 11 := by
  rw [show twE6Eleven = ↑((rootFinset TwistTag.E6.tag).filter (fun α => 2 ≤ twE6C4 α)) from by
    ext α; rw [Finset.mem_coe, Finset.mem_filter, mem_rootFinset]; rfl]
  rw [Set.ncard_coe_finset]
  decide +kernel

theorem twE6Eleven_perm_mem {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ twE6Eleven) :
    permLattice TwistTag.E6.perm α ∈ twE6Eleven := by
  obtain ⟨hroot, hc⟩ := hα
  refine ⟨hroot.permLattice TwistTag.E6.cartan_perm, ?_⟩
  have hfix : TwistTag.E6.perm.symm ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide +kernel
  show 2 ≤ twE6C4 (permLattice TwistTag.E6.perm α)
  rw [show twE6C4 (permLattice TwistTag.E6.perm α) = twE6C4 α from by
    simp only [twE6C4, permLattice, Function.comp_apply, hfix]]
  exact hc

theorem twE6Eleven_height_pos {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ twE6Eleven) :
    0 < height α := by
  obtain ⟨hroot, hc⟩ := hα
  rw [IsRoot.height_pos_iff hroot]
  rcases hroot.nonneg_or_nonpos with h | h
  · exact h
  · have := h ⟨3, by decide⟩
    simp only [twE6C4] at hc
    omega

theorem twE6Eleven_closed {α β : Fin TwistTag.E6.tag.rank → ℤ} (hα : α ∈ twE6Eleven)
    (hβ : β ∈ twE6Eleven) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot TwistTag.E6.tag (a • α + b • β)) : a • α + b • β ∈ twE6Eleven := by
  refine ⟨hr, ?_⟩
  have h1 : twE6C4 (a • α + b • β) = (a : ℤ) * twE6C4 α + (b : ℤ) * twE6C4 β := by
    simp [twE6C4, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  have h2 := hα.2
  have h3 := hβ.2
  rw [h1]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem twE6C4_le_three {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    twE6C4 γ ≤ 3 := by
  have hall : ∀ δ ∈ rootFinset TwistTag.E6.tag, twE6C4 δ ≤ 3 := by
    decide +kernel
  exact hall γ (mem_rootFinset.2 hγ)

theorem twE6Eleven_add_not_isRoot {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ twE6Eleven) (hβ : β ∈ twE6Eleven) : ¬ IsRoot TwistTag.E6.tag (α + β) := by
  intro hr
  have h1 : twE6C4 (α + β) = twE6C4 α + twE6C4 β := by
    simp [twE6C4, Pi.add_apply]
  have := twE6C4_le_three hr
  have h2 := hα.2
  have h3 := hβ.2
  rw [h1] at this
  omega

theorem rootSpan_commute_of_pairwise {τ : Tag} {K : Type} [Field K]
    {S : Set (Fin τ.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ β ∈ S, α ≠ β → ∀ c d : K,
      Commute (pinnedX τ K α c) (pinnedX τ K β d)) :
    ∀ x ∈ rootSpan τ K S, ∀ y ∈ rootSpan τ K S, Commute x y := by
  have hgen : ∀ α ∈ S, ∀ c : K,
      rootSpan τ K S ≤ Subgroup.centralizer ({pinnedX τ K α c} : Set (ModGL τ K)) := by
    intro α hα c
    refine iSup₂_le fun β hβ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases eq_or_ne β α with rfl | hne
    · rw [← pinnedX_add, add_comm, pinnedX_add]
    · exact (h α hα β hβ hne.symm c d).symm
  intro x hx y hy
  rw [rootSpan_eq_closure K S] at hy
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨α, hα, c, rfl⟩ := hg
      exact Subgroup.mem_centralizer_singleton_iff.1 (hgen α hα c hx)
  | one => exact Commute.one_right x
  | mul a b ha hb iha ihb => exact iha.mul_right ihb
  | inv a ha iha => exact iha.inv_right

theorem twE6Eleven_rootSpan_sq {K : Type} [Field K] [CharP K 2]
    (hcomm : ∀ x ∈ rootSpan TwistTag.E6.tag K twE6Eleven,
      ∀ y ∈ rootSpan TwistTag.E6.tag K twE6Eleven, x * y = y * x) :
    ∀ x ∈ rootSpan TwistTag.E6.tag K twE6Eleven, x ^ 2 = 1 := by
  intro x hx
  rw [rootSpan_eq_closure K twE6Eleven] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨α, hα, c, rfl⟩ := hg
      exact CFSG.LieType.Chevalley.ExceptionalCover.pinnedX_sq α c
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        hcomm a (by rw [rootSpan_eq_closure K twE6Eleven]; exact ha)
          b (by rw [rootSpan_eq_closure K twE6Eleven]; exact hb)
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [← pow_two, iha, ← pow_two, ihb, one_mul]
  | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by rw [mul_inv_rev]
        _ = 1 := by rw [← pow_two, iha, inv_one]

theorem exists_elemAbelian_card_graphFixedRootGroup_twE6 {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    ∃ E : Subgroup (ModGL TwistTag.E6.tag K),
      E ≤ graphFixedRootGroup TwistTag.E6 K σ ∧ IsElemAbelian 2 E ∧
        Nat.card E = (2 ^ n) ^ 11 := by
  classical
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK'
  have hKord : Nat.card K = (2 ^ n) ^ TwistTag.E6.order := by
    rw [hK]; rfl
  have hq : ∀ a : Fin TwistTag.E6.foldedTag.rank,
      Nat.card (orbitField TwistTag.E6 K σ a) = (2 ^ n) ^ (TwistTag.E6.orbit a).card :=
    fun a => CFSG.Timmesfeld.ExceptionalOrders.card_orbitField Nat.prime_two hn hKord hσ a
  have hsurj : Function.Surjective σ := by
    obtain ⟨σ', hσ', -, -, -, -⟩ :=
      finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hn K hKord
    have hEq : σ = σ'.toRingHom := RingHom.ext fun c => by
      rw [hσ c]
      exact (hσ' c).symm
    rw [hEq]
    exact σ'.surjective
  have hpair : ∀ α ∈ twE6Eleven, ∀ β ∈ twE6Eleven, α ≠ β → ∀ c d : K,
      Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) := by
    intro α hα β hβ hne c d
    have hne' : α ≠ -β := by
      intro h
      have h1 := twE6Eleven_height_pos hα
      have h2 := twE6Eleven_height_pos hβ
      rw [h, height_neg] at h1
      omega
    exact (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl))
      hα.1 hβ.1 hne hne').2 (twE6Eleven_add_not_isRoot hα hβ) K
      (pinnedX TwistTag.E6.tag K α c) (mem_rootSubgroup.2 ⟨c, rfl⟩)
      (pinnedX TwistTag.E6.tag K β d) (mem_rootSubgroup.2 ⟨d, rfl⟩)
  have hcomm : ∀ x ∈ rootSpan TwistTag.E6.tag K twE6Eleven,
      ∀ y ∈ rootSpan TwistTag.E6.tag K twE6Eleven, x * y = y * x :=
    fun x hx y hy => (rootSpan_commute_of_pairwise hpair x hx y hy).eq
  have hcard : Nat.card ↥(rootSpan TwistTag.E6.tag K twE6Eleven ⊓
      twistedFixedGroup TwistTag.E6 K σ) = (2 ^ n) ^ 11 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup hsurj hq
      (fun α hα => ⟨hα.1, twE6Eleven_height_pos hα⟩)
      (fun α hα => twE6Eleven_perm_mem hα)
      (fun α hα β hβ a b ha hb hr => twE6Eleven_closed hα hβ ha hb hr),
      twE6Eleven_ncard]
  refine ⟨rootSpan TwistTag.E6.tag K twE6Eleven ⊓ twistedFixedGroup TwistTag.E6 K σ,
    ?_, ?_, hcard⟩
  ·
    have hrootpos : rootSpan TwistTag.E6.tag K twE6Eleven ≤
        posUnipotent TwistTag.E6.tag K := by
      rw [posUnipotent, rootSpan]
      exact iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, twE6Eleven_height_pos hα⟩ le_rfl
    exact (le_inf (inf_le_left.trans hrootpos) inf_le_right).trans
      (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ)
  ·
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2.1 b.1 b.2.1)⟩⟩, fun x hx => ?_⟩
    have hx2 : (x ^ 2 : ModGL TwistTag.E6.tag K) = 1 :=
      twE6Eleven_rootSpan_sq hcomm x hx.1
    simpa using hx2

theorem eleven_mul_le_twoRank_graphFixedRootGroup_twE6 {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    11 * n ≤ twoRank ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEG, hEel, hEcard⟩ :=
    exists_elemAbelian_card_graphFixedRootGroup_twE6 hn hK hσ
  have hEsub : IsElemAbelian 2 (E.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :=
    IsElemAbelian.subgroupOf hEel (graphFixedRootGroup TwistTag.E6 K σ)
  have hcard' : Nat.card ↥(E.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) = 2 ^ (11 * n) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv, hEcard, ← pow_mul, mul_comm]
  exact CFSG.SectionRank.le_pRank (p := 2) (H := ⊤) (E := E.subgroupOf _) (by norm_num)
    le_top hEsub hcard'




end Certs

theorem twoRank_le_of_central_quotient {K C : Type} [Group K] [Finite K] [Group C] [Finite C]
    (π : K →* C) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card π.ker)) : twoRank C ≤ twoRank K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.SectionRank.pRank_le (p := 2) (H := ⊤) (k := twoRank K) (by norm_num)
    fun A _ hA => ?_
  have hAp : IsPGroup 2 ↥A := hA.isPGroup
  obtain ⟨S, -, -, hmapS, -, -, -, ⟨eS⟩⟩ := lift_twoGroup π hπ hker hodd hAp
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  haveI hAcomm : IsMulCommutative ↥A := hA.1
  have hSel : IsElemAbelian 2 S := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · exact eS.injective (by rw [map_mul, map_mul]; exact mul_comm' (eS a) (eS b))
    · have hx2 : (⟨x, hx⟩ : ↥S) ^ 2 = 1 :=
        eS.injective (by
          rw [map_pow, map_one]
          exact Subtype.ext (hA.2 (eS ⟨x, hx⟩) (eS ⟨x, hx⟩).2))
      simpa using hx2
  have hScard : Nat.card ↥S = 2 ^ k := by
    rw [Nat.card_congr eS.toEquiv, hk]
  have hle : k ≤ twoRank K :=
    CFSG.SectionRank.le_pRank (p := 2) (H := ⊤) (E := S) (by norm_num) le_top hSel hScard
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hle

end CFSG.LocalAnalysis.GLTheoremA.Y10F
