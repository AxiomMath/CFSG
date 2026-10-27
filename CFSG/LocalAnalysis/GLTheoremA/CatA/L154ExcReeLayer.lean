module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116b
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCent
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification
open CFSG.LieType.Ree
open scoped commutatorElement

theorem l154_isSubnormal_inf_normal {G : Type*} [Group G] {A B N : Subgroup G}
    (h : IsSubnormal A B) (hNB : N ≤ B) (hN : (N.subgroupOf B).Normal) :
    IsSubnormal (A ⊓ N) N := by
  induction h with
  | refl A =>
    rw [inf_eq_right.mpr hNB]
    exact IsSubnormal.refl _
  | step hAM hn _ ih =>
    refine IsSubnormal.step (inf_le_inf_right N hAM) ?_ (ih hNB hN)
    rw [Subgroup.normal_subgroupOf_iff hAM] at hn
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right N hAM)]
    intro x g hx hg
    exact ⟨hn x g hx.1 hg.1, N.mul_mem (N.mul_mem hg.2 hx.2) (N.inv_mem hg.2)⟩

theorem l154_normal_subgroupOf_of_commutator_le {G : Type*} [Group G] {C N : Subgroup G}
    (hNC : N ≤ C) (h : ⁅C, C⁆ ≤ N) : (N.subgroupOf C).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hNC]
  intro n g hn hg
  have h1 : ⁅g, n⁆ ∈ N := h (Subgroup.commutator_mem_commutator hg (hNC hn))
  have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact N.mul_mem h1 hn

theorem l154_lieModel_psl_two {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type} [Group X]
    (e : Matrix.SpecialLinearGroup (Fin 2) K ≃* X) :
    CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 2 2 (2 * a + 1) := by
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [CFSG.Blueprint.LieModel.classical_iff (by decide)]
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  · intro h
    have := (Prod.mk.inj h).2
    omega
  · intro h
    have := (Prod.mk.inj h).2
    omega
  · exact (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)

theorem l154_lieModel_twistedB2 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (e : CFSG.Blueprint.suzukiGroup a K ≃* X) :
    CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .twistedB2 0 2 (2 * a + 1) := by
  refine CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, rfl, a, ha, K, inferInstance, inferInstance,
    rfl, hK, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e.symm

section Layer


theorem l154_ree_layer {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {s : ReeTag.F4.reeGamma K a} (hs : orderOf s = p)
    {T : Subgroup (ReeTag.F4.reeGamma K a)}
    (hT : GLAPComponent p
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)) T) :
    CFSG.Open.IsQuasisimple ↥T ∧ Subgroup.center ↥T = ⊥ ∧ 2 ^ (2 * a + 1) - 1 ∣ Nat.card ↥T ∧
      (Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥T) ∨
        Nonempty (CFSG.Blueprint.suzukiGroup a K ≃* ↥T)) := by
  classical
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj] at hT
  have hperf : ⁅T, T⁆ = T := glaPComponent_perfect hT
  have hne : T ≠ ⊥ := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hT
  have hTC : T ≤ Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a)) := hT.1
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116b.largeRee_layer_typed ha hK hp hp3 s
    hs with hsolv | ⟨N, hNC, hCN, -, hty⟩
  · exfalso
    haveI : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.2 hperf
    haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hne
    haveI := hsolv
    haveI : Group.IsSolvable ↥T :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hTC)
        (Subgroup.inclusion_injective hTC)
    exact Group.IsPerfect.not_isSolvable ↥T inferInstance
  · have hty' : Nonempty (↥N ≃* CFSG.Blueprint.suzukiGroup a K) ∨
        Nonempty (↥N ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
      hty.symm.imp (fun ⟨e⟩ => ⟨e.symm⟩) (fun ⟨e⟩ => ⟨e.symm⟩)
    obtain ⟨hNq, -, -⟩ :=
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.layerType_props ha hK hty'
    have hTN : T ≤ N := by
      calc T = ⁅T, T⁆ := hperf.symm
        _ ≤ ⁅Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a)),
            Subgroup.centralizer ({s} : Set (ReeTag.F4.reeGamma K a))⁆ :=
          Subgroup.commutator_mono hTC hTC
        _ ≤ N := hCN
    have hsub : IsSubnormal T N := by
      have := l154_isSubnormal_inf_normal hT.2.1 hNC
        (l154_normal_subgroupOf_of_commutator_le hNC hCN)
      rwa [inf_eq_left.2 hTN] at this
    have hNq' : CFSG.Open.IsQuasisimple ↥N :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hNq
    have hTeq : T = N := l154_eq_of_subnormal_quasisimple hsub hNq' hperf hne
    subst hTeq
    obtain ⟨hq, hZ, hdvd⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.layerType_props ha hK
      hty'
    exact ⟨hNq', hZ, hdvd, hty⟩

end Layer

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
