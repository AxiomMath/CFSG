module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOmegaUniqueTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordTorusMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus
  commutator_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG modelToG_mono)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)

section ParamMinus


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_kOmMParam_global {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp r K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobal e t f .omegaMinus) :
    ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (Φ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* spGlobal e) (σ : K ≃+* K),
      (∀ g, t * ((Φ g : spGlobal e) : G) * t⁻¹ =
        ((Φ (kOmMBetaC K r b c g) : spGlobal e) : G)) ∧
      ∀ x : StatedSp r K, ((Φ (kOmMIota hr3 hirr hKc hf x) : spGlobal e) : G) =
        ((e.symm (fieldSp r K σ x) : L) : G) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hN : t ∈ normalizer (spGlobal e : Set G) := mem_normalizer_spGlobal e htC
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact hN
  have hty' : LieModel (spGlobal e) .POmegaMinus (r + 1) 2 f := hty
  obtain ⟨b, c, hirr, ⟨ε₀⟩⟩ := kOmM_nonempty_mulEquiv_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (minusIndexEquiv (r + 1) (by omega)) (quadMinus (r + 1) K b c)
    (coe_quadMinus (r + 1) K b c) (kOmM_matrixDerivedScalars_eq_bot K r b c) with hπ
  have hreg := regular_coordinateQuadMinus (r + 1) K b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus (r + 1) K b c (by omega) hirr
  have hθθ : (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ *
      (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix (by omega : 1 ≤ f) hKc
    (by omega : 4 ≤ r + 1) hreg.1 hreg.2 hE (kOmM_hconj K (by omega) (by omega) hKc hirr)
    (kOmM_reindexQuadraticForm_vec K r) (ε₀.trans π)
  set Φ₀ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* spGlobal e := π.trans ψ with hΦ₀
  have hΦ₀θ : ∀ g, (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ (Φ₀ g) =
      Φ₀ (kOmMBetaC K r b c g) :=
    fun g => (hψ (π g)).trans
      (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
  have hΦ₀t : ∀ g, t * ((Φ₀ g : spGlobal e) : G) * t⁻¹ =
      ((Φ₀ (kOmMBetaC K r b c g) : spGlobal e) : G) := by
    intro g
    rw [← hΦ₀θ g, Subgroup.normalizerMonoidHom_apply_apply_coe]
  set ι := kOmMIota (k := K) hr3 hirr hKc hf with hιdef
  set κ : StatedSp r K →* G := (spGlobal e).subtype.comp (Φ₀.toMonoidHom.comp ι) with hκdef
  have hκinj : Function.Injective κ := (spGlobal e).subtype_injective.comp
    (Φ₀.injective.comp (kOmMIota_injective hr3 hirr hKc hf))
  have hfixκ : ∀ y : spGlobal e, (y : G) * t = t * y → ∃ x, κ x = y := by
    intro y hy
    have hθy : (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ y = y := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← hy, mul_inv_cancel_right]
    have hβ : kOmMBetaC K r b c (Φ₀.symm y) = Φ₀.symm y := by
      apply Φ₀.injective
      rw [← hΦ₀θ, MulEquiv.apply_symm_apply, hθy]
    have hmem : Φ₀.symm y ∈ (kOmMIota hr3 hirr hKc hf).range := by
      rw [range_kOmMIota]
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
  have hιs : kOmMBetaC K r b c (ι s) = ι s := by
    have hmem : ι s ∈ fixedSubgroup (kOmMBetaC K r b c) := by
      rw [hιdef, ← range_kOmMIota hr3 hirr hKc hf]
      exact ⟨s, rfl⟩
    exact hmem
  refine ⟨b, c, hirr, (MulAut.conj (ι s)).trans Φ₀, σ₀⁻¹, fun g => ?_, fun x => ?_⟩
  · change t * ((Φ₀ (ι s * g * (ι s)⁻¹) : spGlobal e) : G) * t⁻¹ =
      ((Φ₀ (ι s * kOmMBetaC K r b c g * (ι s)⁻¹) : spGlobal e) : G)
    have h2 : kOmMBetaC K r b c (ι s * g * (ι s)⁻¹) =
        ι s * kOmMBetaC K r b c g * (ι s)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hιs]
    rw [hΦ₀t, h2]
  · have h1 := hκδ (fieldSp r K σ₀⁻¹ x)
    rw [hsσ, MulAut.mul_apply, MulAut.conj_apply, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply] at h1
    change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : spGlobal e) : G) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1

theorem pieceCore_zero_le_centralizer_omegaMinus {r f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hr3 : 3 ≤ r) (e : L ≃* StatedSp r K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobal e t f .omegaMinus) :
    pieceCore e ({⟨0, by omega⟩} : Finset (Fin r)) ≤ centralizer ({t} : Set G) := by
  obtain ⟨b, c, hirr, Φ, σ, hN3, hN1⟩ := exists_kOmMParam_global hKc hf hr3 e htC ht hglob
  set j₀ : Fin r := ⟨0, by omega⟩ with hj₀
  set T₀ := modelToG e (leviTorusSp K ({j₀} : Finset (Fin r))) with hT₀
  set H := pieceCore e ({j₀} : Finset (Fin r)) with hHdef
  have hHE : H ≤ spGlobal e := le_iSup (fun j : Fin r => pieceCore e ({j} : Finset (Fin r))) j₀
  have hHperf : ⁅H, H⁆ = H := CFSG.Quasithin.perfectCore_perfect _
  have hHC : H ≤ centralizer (T₀ : Set G) := perfectCore_le _
  set H' : Subgroup (StatedOmega (StatedQuadMinus (r + 1) K b c)) :=
    (H.subgroupOf (spGlobal e)).map Φ.symm.toMonoidHom with hH'
  set P : Subgroup (GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) :=
    H'.map (StatedOmega (StatedQuadMinus (r + 1) K b c)).subtype with hP
  have hPperf : ⁅P, P⁆ = P := by
    rw [hP, ← Subgroup.map_commutator, hH', ← Subgroup.map_commutator,
      CFSG.SeitzReduction.commutator_subgroupOf_eq_self hHE hHperf]
  have hΦT : ∀ s ∈ leviTorusParam K ({j₀} : Finset (Fin r)),
      ((Φ (kOmMIota hr3 hirr hKc hf (diagSp K r s)) : spGlobal e) : G) ∈ T₀ := by
    intro s hs
    rw [hN1]
    exact (mem_modelToG e).2 ⟨_, fieldSp_mem_leviTorusSp σ (diagSp_mem_leviTorusSp hs), rfl⟩
  have hPB : P ≤ StatedOmega (StatedQuadMinus (r + 1) K b c) ⊓
      centralizer (kOmMDiag K r ''
        (leviTorusParam K ({j₀} : Finset (Fin r)) : Set (Fin r → Kˣ))) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(Φ.symm z).2, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hzT := mem_centralizer_iff.1 (hHC hz) _ (hΦT s hs)
    set d := kOmMIota hr3 hirr hKc hf (diagSp K r s) with hd
    have hcomm : Φ.symm z * d = d * Φ.symm z := by
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hzT.symm
    rw [← coe_kOmMIota_diagSp hr3 hirr hKc hf s, ← hd]
    exact (congrArg Subtype.val hcomm).symm
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK4
  have hconst : (fun _ : Fin r => κ) ∈ leviTorusParam K ({j₀} : Finset (Fin r)) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨fun _ => rfl, fun h => by simp [hj₀] at h; omega⟩
  have hsep : ∀ a : Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2,
      a ∉ Set.range (kOmMPlaneEmb r) → kOmMWeight K r (fun _ => κ) a ≠ 1 := by
    intro a ha
    rcases a with i | i | i
    · rw [kOmMWeight_inl]
      exact fun h' => hκ (Units.val_eq_one.1 h')
    · change ((κ⁻¹ : Kˣ) : K) ≠ 1
      exact fun h' => hκ (inv_eq_one.1 (Units.val_eq_one.1 h'))
    · exact absurd ⟨i, rfl⟩ ha
  have hPsupp : P ≤ suppGL K (Set.range (kOmMEmb r)) :=
    (le_perfectCore_of_perfect hPB hPperf).trans
      (kOmM_perfectCore_le_suppGL_hyp_of_sep hirr hconst hsep)
  intro x hx
  have hxE := hHE hx
  set g : StatedOmega (StatedQuadMinus (r + 1) K b c) := Φ.symm ⟨x, hxE⟩ with hg
  have hgP : (g : GL (Fin (r + 1 - 1) ⊕ Fin (r + 1 - 1) ⊕ Fin 2) K) ∈ P :=
    ⟨g, ⟨⟨x, hxE⟩, show x ∈ H from hx, rfl⟩, rfl⟩
  have hgv := kOmM_mulVec_vec_of_mem_suppGL (hPsupp hgP)
  have hgfix : g ∈ fixedSubgroup (kOmMBetaC K r b c) :=
    (mem_fixedSubgroup_kOmMBetaC_iff K hr3 hirr g).2 hgv
  have hβ : kOmMBetaC K r b c g = g := hgfix
  have h3 := hN3 g
  rw [hβ, hg, MulEquiv.apply_symm_apply] at h3
  rw [mem_centralizer_singleton_iff]
  calc x * t = t * x * t⁻¹ * t := by rw [h3]
    _ = t * x := by group

theorem spThreeOmegaTorusInput_omegaMinus : SpThreeOmegaTorusInput .omegaMinus := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hglob
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact centralizerPerfectCore_spATorus_one_le (by norm_num) e htC
    (pieceCore_zero_le_centralizer_omegaMinus hKc hf (by norm_num) e htC ht hglob)

theorem spThreeOmegaRowUniqueInput_omegaMinus : SpThreeOmegaRowUniqueInput .omegaMinus :=
  spThreeOmegaRowUniqueInput_omegaMinus_of_torus spThreeOmegaTorusInput_omegaMinus

end ParamMinus

section GraphRows


theorem spThreeGraphRowsInput_of_recognition (hLE : SpThreeLinearEvenRecognitionInput)
    (hUE : SpThreeUnitaryEvenRecognitionInput) (hLO : SpThreeKindCoverInput .linearOdd)
    (hUO : SpThreeKindCoverInput .unitaryOdd) (hU18 : OmegaMinusEightSpSixNonembeddingInput) :
    SpThreeGraphRowsInput :=
  spThreeGraphRowsInput_of_inputs hLE hUE hLO hUO
    (spThreeOmegaRowUniqueInput_omegaPlus_of_nonembedding hU18)
    spThreeOmegaRowUniqueInput_omegaMinus

end GraphRows

end CFSG.SeitzReduction.SymplecticPilot
