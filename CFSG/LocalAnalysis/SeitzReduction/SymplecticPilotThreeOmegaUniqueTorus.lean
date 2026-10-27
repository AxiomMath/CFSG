module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOmegaUniqueRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegel
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotUnitaryEven
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6Assembly
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus
  commutator_coordinateQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG modelToG_mono)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.OmegaPilot (diagOmega diagOmega_coe)
open CFSG.Quasithin (perfectCore perfectCore_le)

section ParamPlus


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_kOmegaParam_global {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hr : 2 ≤ r) (hr3 : 3 ≤ r) (e : L ≃* StatedSp r K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobal e t f .omegaPlus) :
    ∃ (Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* spGlobal e) (σ : K ≃+* K),
      (∀ g, t * ((Φ g : spGlobal e) : G) * t⁻¹ = ((Φ (kOmegaBetaC K r g) : spGlobal e) : G)) ∧
      ∀ x : StatedSp r K, ((Φ (kOmegaIota hr hr3 hKc hf x) : spGlobal e) : G) =
        ((e.symm (fieldSp r K σ x) : L) : G) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hN : t ∈ normalizer (spGlobal e : Set G) := mem_normalizer_spGlobal e htC
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact hN
  have hty' : LieModel (spGlobal e) .POmegaPlus (r + 1) 2 f := hty
  obtain ⟨ε₀⟩ := OmegaPilot.nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (plusIndexEquiv (r + 1)) (quadPlus (r + 1) K)
    (coe_quadPlus (r + 1) K) (kOmega_matrixDerivedScalars_eq_bot K r) with hπ
  have hreg := regular_coordinateQuadPlus (K := K) (n := r + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K) (n := r + 1) (by omega)
  have hθθ : (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ *
      (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix (by omega : 1 ≤ f) hKc
    (by omega : 4 ≤ r + 1) hreg.1 hreg.2 hE (kOmega_hconj K (by omega) (by omega) hKc)
    (kOmega_reindexQuadraticForm_vec K r) (ε₀.trans π)
  set Φ₀ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* spGlobal e := π.trans ψ with hΦ₀
  have hΦ₀θ : ∀ g, (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ (Φ₀ g) = Φ₀ (kOmegaBetaC K r g) :=
    fun g => (hψ (π g)).trans
      (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
  have hΦ₀t : ∀ g, t * ((Φ₀ g : spGlobal e) : G) * t⁻¹ =
      ((Φ₀ (kOmegaBetaC K r g) : spGlobal e) : G) := by
    intro g
    rw [← hΦ₀θ g, Subgroup.normalizerMonoidHom_apply_apply_coe]
  set ι := kOmegaIota (k := K) hr hr3 hKc hf with hιdef
  set κ : StatedSp r K →* G := (spGlobal e).subtype.comp (Φ₀.toMonoidHom.comp ι) with hκdef
  have hκinj : Function.Injective κ := (spGlobal e).subtype_injective.comp
    (Φ₀.injective.comp (kOmegaIota_injective hr hr3 hKc hf))
  have hκt : ∀ x, κ x * t = t * κ x := by
    intro x
    have hιx : kOmegaBetaC K r (ι x) = ι x := by
      have hmem : ι x ∈ fixedSubgroup (kOmegaBetaC K r) := by
        rw [hιdef, ← range_kOmegaIota hr hr3 hKc hf]
        exact ⟨x, rfl⟩
      exact hmem
    have h1 := hΦ₀t (ι x)
    rw [hιx] at h1
    change ((Φ₀ (ι x) : spGlobal e) : G) * t = t * ((Φ₀ (ι x) : spGlobal e) : G)
    calc ((Φ₀ (ι x) : spGlobal e) : G) * t =
        (t * ((Φ₀ (ι x) : spGlobal e) : G) * t⁻¹) * t := by rw [h1]
      _ = t * ((Φ₀ (ι x) : spGlobal e) : G) := by group
  have hfixκ : ∀ y : spGlobal e, (y : G) * t = t * y → ∃ x, κ x = y := by
    intro y hy
    have hθy : (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ y = y := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← hy, mul_inv_cancel_right]
    have hβ : kOmegaBetaC K r (Φ₀.symm y) = Φ₀.symm y := by
      apply Φ₀.injective
      rw [← hΦ₀θ, MulEquiv.apply_symm_apply, hθy]
    have hmem : Φ₀.symm y ∈ (kOmegaIota hr hr3 hKc hf).range := by
      rw [range_kOmegaIota]
      exact hβ
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, ?_⟩
    change ((Φ₀ (ι x) : spGlobal e) : G) = y
    rw [hιdef, hx, MulEquiv.apply_symm_apply]
  have hκr : κ.range = L := by
    have hle : L ≤ κ.range := by
      intro l hl
      obtain ⟨x, hx⟩ := hfixκ ⟨l, hLS hl⟩ (mem_centralizer_iff.1 htC l hl)
      exact ⟨x, by rw [hx]⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hκinj, Subgroup.card_top,
      Nat.card_congr e.toEquiv]
  set lam : StatedSp r K →* G := L.subtype.comp e.symm.toMonoidHom with hlamdef
  have hlaminj : Function.Injective lam := L.subtype_injective.comp e.symm.injective
  have hlamr : lam.range = L := by
    rw [hlamdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  set δ : MulAut (StatedSp r K) := ((MonoidHom.ofInjective hlaminj).trans
    (MulEquiv.subgroupCongr (hlamr.trans hκr.symm))).trans (MonoidHom.ofInjective hκinj).symm
    with hδdef
  have hκδ : ∀ g, κ (δ g) = lam g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκinj).apply_symm_apply
      (MulEquiv.subgroupCongr (hlamr.trans hκr.symm) (MonoidHom.ofInjective hlaminj g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, σ₀, hsσ⟩ := exists_eq_conj_mul_fieldSp hr3 δ
  have hιs : kOmegaBetaC K r (ι s) = ι s := by
    have hmem : ι s ∈ fixedSubgroup (kOmegaBetaC K r) := by
      rw [hιdef, ← range_kOmegaIota hr hr3 hKc hf]
      exact ⟨s, rfl⟩
    exact hmem
  refine ⟨(MulAut.conj (ι s)).trans Φ₀, σ₀⁻¹, fun g => ?_, fun x => ?_⟩
  · change t * ((Φ₀ (ι s * g * (ι s)⁻¹) : spGlobal e) : G) * t⁻¹ =
      ((Φ₀ (ι s * kOmegaBetaC K r g * (ι s)⁻¹) : spGlobal e) : G)
    have h2 : kOmegaBetaC K r (ι s * g * (ι s)⁻¹) = ι s * kOmegaBetaC K r g * (ι s)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hιs]
    rw [hΦ₀t, h2]
  · have h1 := hκδ (fieldSp r K σ₀⁻¹ x)
    rw [hsσ, MulAut.mul_apply, MulAut.conj_apply, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply] at h1
    change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : spGlobal e) : G) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1

theorem pieceCore_zero_le_centralizer_omegaPlus {r f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hr3 : 3 ≤ r) (e : L ≃* StatedSp r K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobal e t f .omegaPlus) :
    pieceCore e ({⟨0, by omega⟩} : Finset (Fin r)) ≤ centralizer ({t} : Set G) := by
  have hr : 2 ≤ r := by omega
  obtain ⟨Φ, σ, hN3, hN1⟩ := exists_kOmegaParam_global hKc hf hr hr3 e htC ht hglob
  set j₀ : Fin r := ⟨0, by omega⟩ with hj₀
  set T₀ := modelToG e (leviTorusSp K ({j₀} : Finset (Fin r))) with hT₀
  set H := pieceCore e ({j₀} : Finset (Fin r)) with hHdef
  have hHE : H ≤ spGlobal e := le_iSup (fun j : Fin r => pieceCore e ({j} : Finset (Fin r))) j₀
  have hHperf : ⁅H, H⁆ = H := CFSG.Quasithin.perfectCore_perfect _
  have hHC : H ≤ centralizer (T₀ : Set G) := perfectCore_le _
  set H' : Subgroup (StatedOmega (StatedQuadPlus (r + 1) K)) :=
    (H.subgroupOf (spGlobal e)).map Φ.symm.toMonoidHom with hH'
  set P : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :=
    H'.map (StatedOmega (StatedQuadPlus (r + 1) K)).subtype with hP
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hH', ← Subgroup.map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self hHE hHperf]
  set W : Set (Fin (r + 1) ⊕ Fin (r + 1) → K) :=
    {w | ∃ s ∈ leviTorusParam K ({j₀} : Finset (Fin r)), w = diagSpEntry (kOmegaSnoc K s)}
    with hW
  have hW1 : ∀ w ∈ W, w (kOmegaA r) = 1 ∧ w (kOmegaB r) = 1 := by
    rintro _ ⟨s, -, rfl⟩
    simp [kOmegaA, kOmegaB, diagSpEntry_inl, diagSpEntry_inr]
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK4
  have hconst : (fun _ : Fin r => κ) ∈ leviTorusParam K ({j₀} : Finset (Fin r)) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨fun _ => rfl, fun h => by simp [hj₀] at h; omega⟩
  have hWsep : ∀ c, c ≠ kOmegaA r → c ≠ kOmegaB r → ∃ w ∈ W, w c ≠ 1 := by
    intro c hca hcb
    refine ⟨_, ⟨_, hconst, rfl⟩, ?_⟩
    rcases c with i | i
    · have hi : i ≠ Fin.last r := fun h' => hca (by rw [h'])
      obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      rw [diagSpEntry_inl, kOmegaSnoc_castSucc]
      exact fun h' => hκ (Units.val_eq_one.1 h')
    · have hi : i ≠ Fin.last r := fun h' => hcb (by rw [h'])
      obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      rw [diagSpEntry_inr, kOmegaSnoc_castSucc]
      exact fun h' => hκ (inv_eq_one.1 (Units.val_eq_one.1 h'))
  have hΦT : ∀ s ∈ leviTorusParam K ({j₀} : Finset (Fin r)),
      ((Φ (kOmegaIota hr hr3 hKc hf (diagSp K r s)) : spGlobal e) : G) ∈ T₀ := by
    intro s hs
    rw [hN1]
    refine (mem_modelToG e).2 ⟨_, fieldSp_mem_leviTorusSp σ (diagSp_mem_leviTorusSp hs), rfl⟩
  have hPC : P ≤ kOmegaTorusCent r W := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(Φ.symm z).2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hzT := mem_centralizer_iff.1 (hHC hz) _ (hΦT s hs)
    set d := kOmegaIota hr hr3 hKc hf (diagSp K r s) with hd
    have hcomm : Φ.symm z * d = d * Φ.symm z := by
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hzT.symm
    have hdM : (((d : StatedOmega (StatedQuadPlus (r + 1) K)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) =
        Matrix.diagonal (diagSpEntry (kOmegaSnoc K s)) := by
      rw [hd, coe_kOmegaIota_diagSp, diagOmega_coe]
    have e1 := congrArg (fun y : StatedOmega (StatedQuadPlus (r + 1) K) =>
      (((y : GL (Fin (r + 1) ⊕ Fin (r + 1)) K)) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K)) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul] at e1
    rw [hdM] at e1
    exact e1
  intro x hx
  have hxE := hHE hx
  set g : StatedOmega (StatedQuadPlus (r + 1) K) := Φ.symm ⟨x, hxE⟩ with hg
  have hgP : (g : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) ∈ P :=
    ⟨g, ⟨⟨x, hxE⟩, show x ∈ H from hx, rfl⟩, rfl⟩
  have hgv := kOmega_mulVec_vec_of_perfect hW1 hWsep hPC hPperf hgP
  have hgfix : g ∈ fixedSubgroup (kOmegaBetaC K r) :=
    (mem_fixedSubgroup_kOmegaBetaC_iff K hr g).2 hgv
  have hβ : kOmegaBetaC K r g = g := hgfix
  have h3 := hN3 g
  rw [hβ, hg, MulEquiv.apply_symm_apply] at h3
  rw [mem_centralizer_singleton_iff]
  calc x * t = t * x * t⁻¹ * t := by rw [h3]
    _ = t * x := by group

end ParamPlus

section Weyl

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem oddCoordInv_mem_spATorusParam_one {r : ℕ} (hr : 2 ≤ r) {s : Fin r → Kˣ}
    (hs : s ∈ leviTorusParam K ({⟨0, by omega⟩} : Finset (Fin r))) :
    oddCoordInv s ∈ spATorusParam K r 1 := by
  have h01 : s ⟨0, by omega⟩ = s ⟨1, by omega⟩ := (hs ⟨0, by omega⟩ (Finset.mem_singleton_self _)).1
    (by simp; omega)
  intro a b h1 h2 h3 h4
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  have hb : b.val = 0 ∨ b.val = 1 := by omega
  have hab : a.val ≠ b.val := fun h => h2 (Fin.ext h)
  simp only [oddCoordInv]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · omega
  · have ha' : (⟨0, by omega⟩ : Fin r) = a := Fin.ext ha.symm
    have hb' : (⟨1, by omega⟩ : Fin r) = b := Fin.ext hb.symm
    rw [← ha', ← hb']
    simp [h01]
  · have ha' : (⟨1, by omega⟩ : Fin r) = a := Fin.ext ha.symm
    have hb' : (⟨0, by omega⟩ : Fin r) = b := Fin.ext hb.symm
    rw [← ha', ← hb']
    simp [h01]
  · omega

theorem centralizerPerfectCore_spATorus_one_le {r : ℕ} (hr : 2 ≤ r) (e : L ≃* StatedSp r K)
    {t : G} (htC : t ∈ centralizer (L : Set G))
    (hM : pieceCore e ({⟨0, by omega⟩} : Finset (Fin r)) ≤ centralizer ({t} : Set G)) :
    centralizerPerfectCore (modelToG e (spATorus K r 1)) ≤ centralizer ({t} : Set G) := by
  set c : G := ((e.symm (oddSwapSp K r) : L) : G) with hc
  have hcL : c ∈ L := (e.symm (oddSwapSp K r)).2
  set H := centralizerPerfectCore (modelToG e (spATorus K r 1)) with hH
  have hHperf : ⁅H, H⁆ = H := CFSG.Quasithin.perfectCore_perfect _
  have hHC : H ≤ centralizer (modelToG e (spATorus K r 1) : Set G) := perfectCore_le _
  set H' := H.map (MulAut.conj c⁻¹).toMonoidHom with hH'
  have hH'perf : ⁅H', H'⁆ = H' := by rw [hH', ← Subgroup.map_commutator, hHperf]
  have hH'C : H' ≤ centralizer (modelToG e (leviTorusSp K ({⟨0, by omega⟩} : Finset (Fin r))) :
      Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro τ hτ
    obtain ⟨d, ⟨s, hs, rfl⟩, rfl⟩ := (mem_modelToG e).1 hτ
    have h1 : oddSwapSp K r * diagSp K r s * (oddSwapSp K r)⁻¹ =
        diagSp K r (oddCoordInv s) := by
      rw [oddSwapSp_mul_diagSp, mul_inv_cancel_right]
    have hmem : c * ((e.symm (diagSp K r s) : L) : G) * c⁻¹ ∈ modelToG e (spATorus K r 1) := by
      refine (mem_modelToG e).2 ⟨diagSp K r (oddCoordInv s),
        ⟨_, oddCoordInv_mem_spATorusParam_one hr hs, rfl⟩, ?_⟩
      rw [hc, ← h1, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h2 := mem_centralizer_iff.1 (hHC hy) _ hmem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc ((e.symm (diagSp K r s) : L) : G) * (c⁻¹ * y * c) =
        c⁻¹ * ((c * ((e.symm (diagSp K r s) : L) : G) * c⁻¹) * y) * c := by group
      _ = c⁻¹ * (y * (c * ((e.symm (diagSp K r s) : L) : G) * c⁻¹)) * c := by rw [h2]
      _ = c⁻¹ * y * c * ((e.symm (diagSp K r s) : L) : G) := by group
  have hle := (F4Pilot.le_centralizerPerfectCore hH'perf hH'C).trans hM
  intro y hy
  have h1 : c⁻¹ * y * c ∈ centralizer ({t} : Set G) := by
    refine hle ⟨y, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hct : c * t = t * c := mem_centralizer_iff.1 htC c hcL
  have h2 : (c⁻¹ * y * c) * t = t * (c⁻¹ * y * c) := mem_centralizer_singleton_iff.1 h1
  rw [mem_centralizer_singleton_iff]
  have hct' : c⁻¹ * t = t * c⁻¹ := by
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
      _ = t * c⁻¹ := by group
  calc y * t = c * ((c⁻¹ * y * c) * t) * c⁻¹ := by
        rw [show c * ((c⁻¹ * y * c) * t) * c⁻¹ = y * (c * t * c⁻¹) by group, hct]
        group
    _ = c * (t * (c⁻¹ * y * c)) * c⁻¹ := by rw [h2]
    _ = t * y := by
        rw [show c * (t * (c⁻¹ * y * c)) * c⁻¹ = (c * t * c⁻¹) * y by group, hct]
        group

end Weyl

theorem spThreeOmegaTorusInput_omegaPlus :
    SpThreeOmegaTorusInput .omegaPlus := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hglob
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact centralizerPerfectCore_spATorus_one_le (by norm_num) e htC
    (pieceCore_zero_le_centralizer_omegaPlus hKc hf (by norm_num) e htC ht hglob)

theorem spThreeOmegaRowUniqueInput_omegaPlus_of_nonembedding
    (hU18 : OmegaMinusEightSpSixNonembeddingInput) : SpThreeOmegaRowUniqueInput .omegaPlus :=
  spThreeOmegaRowUniqueInput_omegaPlus_of_torus spThreeOmegaTorusInput_omegaPlus hU18

end CFSG.SeitzReduction.SymplecticPilot
