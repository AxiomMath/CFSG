module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinBetaC
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusFinal

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)

local instance f4PilotGraphSpinLeviNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Field

variable {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem plusSwapMat_map (ρ : k ≃+* k) :
    (plusSwapMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k).map ρ = plusSwapMat := by
  ext i j
  simp only [plusSwapMat, Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem omegaPlusBetaC_omegaPlusFieldAut (ρ : k ≃+* k) (A : StatedOmega (StatedQuadPlus 4 k)) :
    omegaPlusBetaC k (omegaPlusFieldAut k ρ A) = omegaPlusFieldAut k ρ (omegaPlusBetaC k A) := by
  apply Subtype.ext
  apply Units.ext
  have hP : ((plusSwapGL⁻¹ : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) =
      plusSwapMat := rfl
  have hP' : ((plusSwapGL : GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) =
      plusSwapMat := rfl
  change (((omegaPlusBetaC k (omegaPlusFieldAut k ρ A) : StatedOmega (StatedQuadPlus 4 k)) :
      GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k) =
    (((omegaPlusFieldAut k ρ (omegaPlusBetaC k A) : StatedOmega (StatedQuadPlus 4 k)) :
      GL (Fin 4 ⊕ Fin 4) k) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k)
  rw [coe_omegaPlusFieldAut, coe_omegaPlusBetaC, coe_omegaPlusBetaC, Units.val_mul,
    Units.val_mul, Units.val_mul, Units.val_mul, hP, hP', coe_omegaPlusFieldAut]
  have hmul : ∀ M N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) k,
      (M * N).map ρ = M.map ρ * N.map ρ := fun M N => Matrix.map_mul (f := (ρ : k →+* k))
  rw [hmul, hmul, plusSwapMat_map]

end Field

section Iota

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

@[expose] noncomputable def spinIota : StatedSp 3 K →* spinGroup (quadPlus 4 K) :=
  (spinOmegaEquiv (K := K)).symm.toMonoidHom.comp
    (omegaPlusIota hK hf (diagOmega_mem_omegaPlus8 K))

theorem spinIota_apply (s : StatedSp 3 K) :
    spinIota hK hf s =
      (spinOmegaEquiv (K := K)).symm (omegaPlusIota hK hf (diagOmega_mem_omegaPlus8 K) s) :=
  rfl

theorem spinIota_injective : Function.Injective (spinIota hK hf) :=
  (spinOmegaEquiv (K := K)).symm.injective.comp (omegaPlusIota_injective hK hf _)

omit [Finite K] in
theorem spinOmegaEquiv_symm_omegaPlusBetaC
    [Finite K] (A : StatedOmega (StatedQuadPlus 4 K)) :
    (spinOmegaEquiv (K := K)).symm (omegaPlusBetaC K A) =
      spinD4Graph K ((spinOmegaEquiv (K := K)).symm A) := by
  rw [MulEquiv.symm_apply_eq, spinOmegaEquiv_spinD4Graph_eq_omegaPlusBetaC,
    MulEquiv.apply_symm_apply]

theorem mem_range_spinIota_iff
    (x : spinGroup (quadPlus 4 K)) :
    x ∈ (spinIota hK hf).range ↔ spinD4Graph K x = x := by
  constructor
  · rintro ⟨s, rfl⟩
    have hs : omegaPlusIota hK hf (diagOmega_mem_omegaPlus8 K) s ∈
        fixedSubgroup (omegaPlusBetaC K) := (range_omegaPlusIota hK hf _) ▸ ⟨s, rfl⟩
    have hs' : omegaPlusBetaC K (omegaPlusIota hK hf (diagOmega_mem_omegaPlus8 K) s) =
        omegaPlusIota hK hf (diagOmega_mem_omegaPlus8 K) s := hs
    rw [spinIota_apply, ← spinOmegaEquiv_symm_omegaPlusBetaC, hs']
  · intro hx
    have hfix : spinOmegaEquiv x ∈ fixedSubgroup (omegaPlusBetaC K) := by
      change omegaPlusBetaC K (spinOmegaEquiv x) = spinOmegaEquiv x
      rw [← spinOmegaEquiv_spinD4Graph_eq_omegaPlusBetaC, hx]
    rw [← range_omegaPlusIota hK hf (diagOmega_mem_omegaPlus8 K)] at hfix
    obtain ⟨s, hs⟩ := hfix
    exact ⟨s, by rw [spinIota_apply, hs, MulEquiv.symm_apply_apply]⟩

end Iota

section Normalized

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_comm_spinD4Graph_normalized_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K) {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e .X) (hiY : Function.Injective ΦY)
    (hc : ∀ g, t * ΦY g * t⁻¹ = ΦY (spinD4Graph K g)) :
    ∃ δ : MulAut (spinGroup (quadPlus 4 K)), (∀ g, δ (spinD4Graph K g) = spinD4Graph K (δ g)) ∧
      ∀ s, ΦY (δ (spinIota hw.card_eq hf s)) = levi6Hom e ε s := by
  have hdiag := diagOmega_mem_omegaPlus8 K
  set ι := omegaPlusIota hw.card_eq hf hdiag with hιdef
  set ψ := spinOmegaEquiv (K := K) with hψ
  set Φ₂ : StatedOmega (StatedQuadPlus 4 K) →* G := ΦY.comp ψ.symm.toMonoidHom with hΦ₂
  have hΦ₂i : Function.Injective Φ₂ := hiY.comp ψ.symm.injective
  have hΦ₂r : Φ₂.range = neighbourCore e .X := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ.symm.surjective,
      ← MonoidHom.range_eq_map, hrY]
  have hker₂ : Φ₂.ker ≤ center (StatedOmega (StatedQuadPlus 4 K)) := by
    rw [(MonoidHom.ker_eq_bot_iff Φ₂).2 hΦ₂i]
    exact bot_le
  have hβ₂ : ∀ A, Φ₂ (omegaPlusBetaC K A) = t * Φ₂ A * t⁻¹ := by
    intro A
    change ΦY (ψ.symm (omegaPlusBetaC K A)) = t * ΦY (ψ.symm A) * t⁻¹
    rw [spinOmegaEquiv_symm_omegaPlusBetaC, hc]
  have hιperf : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hfixr : fixedSubgroup (omegaPlusBetaC K) = ι.range :=
    (range_omegaPlusIota hw.card_eq hf hdiag).symm
  have hcore : perfectCore (fixedSubgroup (omegaPlusBetaC K)) = ι.range := by
    rw [hfixr]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hmap := map_perfectCore_fixedSubgroup_eq Φ₂ hker₂ hβ₂
  rw [hcore, hΦ₂r, perfectCore_neighbourCore_inf_centralizer_X hw hf e,
    ← neighbourLeviG_eq_modelToG] at hmap
  set κ : StatedSp 3 K →* G := Φ₂.comp ι with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := hΦ₂i.comp (omegaPlusIota_injective hw.card_eq hf hdiag)
  have hlam := levi6Hom_injective e ε
  have hrange : (levi6Hom e ε).range = κ.range := by
    rw [range_levi6Hom, hκr]
  set δ : MulAut (StatedSp 3 K) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ g) = levi6Hom e ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ
  set δh : MulAut (StatedOmega (StatedQuadPlus 4 K)) :=
    MulAut.conj (ι s) * omegaPlusFieldAut K ρ with hδh
  have hιs : omegaPlusBetaC K (ι s) = ι s := by
    have hs : ι s ∈ fixedSubgroup (omegaPlusBetaC K) := hfixr ▸ ⟨s, rfl⟩
    exact hs
  have hδβ : ∀ A, δh (omegaPlusBetaC K A) = omegaPlusBetaC K (δh A) := by
    intro A
    rw [hδh, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
      map_mul, map_inv, hιs, omegaPlusBetaC_omegaPlusFieldAut]
  refine ⟨(ψ.trans δh).trans ψ.symm, fun g => ?_, fun g => ?_⟩
  · simp only [MulEquiv.trans_apply]
    rw [spinOmegaEquiv_spinD4Graph_eq_omegaPlusBetaC, hδβ, spinOmegaEquiv_symm_omegaPlusBetaC]
  · change ΦY (ψ.symm (δh (ψ (ψ.symm (ι g))))) = _
    rw [MulEquiv.apply_symm_apply, ← hκδ, hsρ]
    change Φ₂ (δh (ι g)) = Φ₂ (ι (s * statedSpMap (ρ : K →+* K) 3 g * s⁻¹))
    rw [hδh, MulAut.mul_apply, MulAut.conj_apply,
      omegaPlusFieldAut_iota K hw.card_eq hf hdiag ρ g]
    simp only [map_mul, map_inv]
    rfl

theorem exists_comm_spinD4Graph_normalized {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} {e₂ : L ≃* adjointGroup .F4 K}
    (he₂ : IsNeighbourFrame e e₂ N) (ε : K ≃+* K) {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e N) (hiY : Function.Injective ΦY)
    (hc : ∀ g, t * ΦY g * t⁻¹ = ΦY (spinD4Graph K g)) :
    ∃ δ : MulAut (spinGroup (quadPlus 4 K)), (∀ g, δ (spinD4Graph K g) = spinD4Graph K (δ g)) ∧
      ∀ s, ΦY (δ (spinIota hw.card_eq hf s)) = levi6Hom e₂ ε s := by
  cases N with
  | X =>
    have h' : e₂ = e := he₂
    subst h'
    exact exists_comm_spinD4Graph_normalized_X hw hf e₂ ε hrY hiY hc
  | Y =>
    obtain ⟨hc', rfl⟩ := he₂
    exact exists_comm_spinD4Graph_normalized_X hw hf _ ε (hrY.trans (neighbourCore_Y_eq_X e))
      hiY hc
  | X' => exact he₂.elim

end Normalized

end CFSG.SeitzReduction.F4Pilot
