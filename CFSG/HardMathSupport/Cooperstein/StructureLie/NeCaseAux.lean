module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseOdd
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseSylow
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineSplit
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.S1567Z7
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BlockSolvableTransfer
import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseRadical

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (barM)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement Pointwise

section Bar

variable {G : Type} [Group G]

theorem barM_mono {X A B : Subgroup G} (h : A ≤ B) : barM X A ≤ barM X B := fun γ hγ => by
  obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
  exact barHom_mem_barM (h hx)

theorem isSubnormal_barM {X A K : Subgroup G} (h : IsSubnormal A K) (hK : K ≤ X) :
    IsSubnormal (barM X A) (barM X K) := by
  induction h with
  | refl => exact IsSubnormal.refl _
  | @step H M K hle hN hMK ih =>
    have hMX : M ≤ X := (A3.subnormal_le hMK).trans hK
    refine IsSubnormal.step (barM_mono hle) ?_ (ih hK)
    have hM : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (barM_mono hle)]
    intro γ hγ
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
    exact barHom_mem_normalizer_of_mem (hM hx)

end Bar

section Equiv

theorem nonempty_mulEquiv_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* B)
    (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) : Nonempty (B ≃* C) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))⟩

theorem open_isQuasisimple_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : CFSG.Open.IsQuasisimple H) : CFSG.Open.IsQuasisimple K := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 : (commutator H).map e.toMonoidHom = commutator K := by
      simp only [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    rw [← h1, hc, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center H) (Subgroup.center K) e
        (Subgroup.map_center_eq e))).mp hs

theorem open_isQuasisimple_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

end Equiv

section PerfectCore

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_perfectCore_of_surjective {H : Subgroup G} {K : Type*} [Group K]
    (ψ : ↥H →* K) (hψ : Function.Surjective ψ) (hK : commutator K = ⊤) (k : K) :
    ∃ l : ↥H, (l : G) ∈ perfectCore H ∧ ψ l = k := by
  obtain ⟨n, hn⟩ := exists_perfectCore_eq H
  have htop : ∀ m : ℕ, derivedSeries K m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih]; exact hK
  have hk : k ∈ (derivedSeries ↥H n).map ψ := by
    rw [map_derivedSeries_eq hψ n, htop n]; exact Subgroup.mem_top k
  obtain ⟨d, hd, rfl⟩ := hk
  refine ⟨d, ?_, rfl⟩
  rw [hn n le_rfl, derivedSeriesOf_eq_map_derivedSeries]
  exact ⟨d, hd, rfl⟩

theorem perfectCore_subgroupOf_eq (H : Subgroup G) :
    ∃ n, (perfectCore H).subgroupOf H = derivedSeries ↥H n := by
  obtain ⟨n, hn⟩ := exists_perfectCore_eq H
  refine ⟨n, ?_⟩
  rw [hn n le_rfl, derivedSeriesOf_eq_map_derivedSeries]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem normal_perfectCore_subgroupOf (H : Subgroup G) : ((perfectCore H).subgroupOf H).Normal := by
  obtain ⟨n, hn⟩ := perfectCore_subgroupOf_eq H
  rw [hn]
  infer_instance

end PerfectCore

section Decomp

local notation "centerIn" => CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.centerIn

variable {Γ : Type} [Group Γ]

theorem mem_centerIn {L : Subgroup Γ} {z : Γ} (hz : z ∈ centerIn L) :
    z ∈ L ∧ ∀ k ∈ L, z * k = k * z := by
  obtain ⟨c, hc, rfl⟩ := hz
  exact ⟨c.2, fun k hk => by
    have := Subgroup.mem_center_iff.mp hc ⟨k, hk⟩
    exact congrArg Subtype.val this.symm⟩

theorem comm_mul_central_right (r z w : Γ) (h : z * w = w * z) : ⁅r * z, w⁆ = ⁅r, w⁆ := by
  have h1 : z * w * z⁻¹ = w := by rw [h]; group
  calc ⁅r * z, w⁆ = r * (z * w * z⁻¹) * r⁻¹ * w⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅r, w⁆ := by rw [h1]; simp only [commutatorElement_def]

theorem comm_mul_central_left (a b z : Γ) (h : z * a = a * z) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h1 : z * a⁻¹ * z⁻¹ = a⁻¹ := ((show Commute z a from h).inv_right).mul_inv_cancel
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h1]; simp only [commutatorElement_def]

theorem perfect_eq_bot_of_decomp [Finite Γ] {L R K : Subgroup Γ} (hR : IsPGroup 2 R) (hRL : R ≤ L)
    (hK : ⁅K, K⁆ = K) (hdec : ∀ k ∈ K, k ∈ R ⊔ centerIn L) : K = ⊥ := by
  have hKR : K ≤ R := by
    conv_lhs => rw [← hK]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨r, hr, z, hz, rfl⟩ := exists_mul_of_mem_sup_centerIn hRL (hdec a ha)
    obtain ⟨r', hr', z', hz', rfl⟩ := exists_mul_of_mem_sup_centerIn hRL (hdec b hb)
    have hr'z' : r' * z' ∈ L := L.mul_mem (hRL hr') (mem_centerIn hz').1
    have e1 : ⁅r * z, r' * z'⁆ = ⁅r, r' * z'⁆ :=
      comm_mul_central_right r z _ ((mem_centerIn hz).2 _ hr'z')
    have e2 : ⁅r, r' * z'⁆ = ⁅r, r'⁆ :=
      comm_mul_central_left r r' z' ((mem_centerIn hz').2 r (hRL hr))
    have hc : ⁅r, r'⁆ ∈ R := by
      simpa [commutatorElement_def] using
        R.mul_mem (R.mul_mem (R.mul_mem hr hr') (R.inv_mem hr)) (R.inv_mem hr')
    rw [e1, e2]
    exact hc
  have hKp : IsPGroup 2 K := hR.to_le hKR
  have : Group.IsNilpotent K := hKp.isNilpotent
  have : Group.IsSolvable K := inferInstance
  by_contra hne
  have : Nontrivial K := (Subgroup.bot_or_nontrivial K).resolve_left hne
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  exact Group.IsPerfect.not_isSolvable K inferInstance

end Decomp

end CFSG.HardMathSupport.Cooperstein.StructureLie
