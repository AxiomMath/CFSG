module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelImages
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedCoverBeta
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup)

local instance f4PilotGraphTwistedPiModelTorusNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Vectors

variable {k : Type} [Field k]

theorem toLinEquiv_diag_single_of_weight {t : Fin 3 → kˣ} {p : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2}
    {δ : k} (hp : minusWeight k t p = δ) :
    toLinEquiv _ k (diagOmegaMinus k t) (Pi.single p 1) = δ • Pi.single p 1 := by
  rw [toLinEquiv_diagOmegaMinus_single, hp]

theorem toLinEquiv_diag_smul_single_of_weight {t : Fin 3 → kˣ}
    {p : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2} {δ : k} (hp : minusWeight k t p = δ) (a : k) :
    toLinEquiv _ k (diagOmegaMinus k t) (a • Pi.single p 1) = δ • (a • Pi.single p 1) := by
  rw [map_smul, toLinEquiv_diagOmegaMinus_single, hp, smul_comm]

theorem toLinEquiv_diag_tail (t : Fin 3 → kˣ) (a : Fin 2 → k) :
    toLinEquiv _ k (diagOmegaMinus k t) (tailModelEquiv (4 - 1) k (Fin 2) (0, a)) =
      tailModelEquiv (4 - 1) k (Fin 2) (0, a) :=
  toLinEquiv_diagOmegaMinus_of_V₆_zero t fun i => by rcases i with i | i <;> rfl

end Vectors

section Commute

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

theorem toLinEquiv_twCoverPi (x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes) :
    toLinEquiv _ (descentField σ) ((twCoverPi σ hσσ hω x : StatedOmega
      (StatedQuadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :
        GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (descentField σ)) = (twCoverPhi σ hσσ hω x).val := by
  change toLinEquiv _ (descentField σ) ((toLinEquiv _ (descentField σ)).symm
    (twCoverPhi σ hσσ hω x).val) = _
  rw [MulEquiv.apply_symm_apply]

theorem commute_twCoverPi_diag_of_eichler {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {u w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ}
    (hx : (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w)
    {t : Fin 3 → (descentField σ)ˣ} {δ : descentField σ} (hδ : δ ≠ 0)
    (hu : toLinEquiv _ (descentField σ) (diagOmegaMinus (descentField σ) t) u = δ • u)
    (hw : toLinEquiv _ (descentField σ) (diagOmegaMinus (descentField σ) t) w = δ⁻¹ • w) :
    Commute (twCoverPi σ hσσ hω x)
      ⟨diagOmegaMinus (descentField σ) t, diagOmegaMinus_mem _ _ t⟩ := by
  apply commute_of_toLinEquiv
  rw [toLinEquiv_twCoverPi, hx]
  exact (commute_eichler_of_apply_eq_smul (toLinEquiv_diagOmegaMinus_mem _ _ t) hδ hu hw).symm

theorem commute_twCoverPi_of_mem_twLevi {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ AmalgamNeighbour.Y.nodes)
    {d : StatedOmega (StatedQuadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))}
    (hgen : ∀ j ∈ J, ∀ g : fixedGroup F (σ : F →+* F),
      (g ∈ twistedRootGroup F (σ : F →+* F) (Pi.single j 1) ∨
        g ∈ twistedRootGroup F (σ : F →+* F) (-Pi.single j 1)) →
      ∀ hg : g ∈ twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes,
        Commute (twCoverPi σ hσσ hω ⟨g, hg⟩) d)
    (x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes)
    (hx : (x : fixedGroup F (σ : F →+* F)) ∈ twLevi F (σ : F →+* F) J) :
    Commute (twCoverPi σ hσσ hω x) d := by
  set S : Subgroup (fixedGroup F (σ : F →+* F)) :=
    ((Subgroup.centralizer {d}).comap (twCoverPi σ hσσ hω)).map
      (twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes).subtype with hS
  have hmem : ∀ j ∈ J, ∀ g : fixedGroup F (σ : F →+* F),
      (g ∈ twistedRootGroup F (σ : F →+* F) (Pi.single j 1) ∨
        g ∈ twistedRootGroup F (σ : F →+* F) (-Pi.single j 1)) → g ∈ S := by
    intro j hj g hg
    have hgY := mem_twLevi_Y_of_mem (hJ hj) hg
    refine ⟨⟨g, hgY⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hgen j hj g hg hgY).eq.symm
  have hle : twLevi F (σ : F →+* F) J ≤ S :=
    iSup₂_le fun j hj => sup_le (fun g hg => hmem j hj g (Or.inl hg))
      (fun g hg => hmem j hj g (Or.inr hg))
  obtain ⟨y, hy, hyx⟩ := hle hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hy
  exact (hy d rfl).symm

theorem commute_twCoverPi_one_two (x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes)
    (hx : (x : fixedGroup F (σ : F →+* F)) ∈ twLevi F (σ : F →+* F) {1, 2})
    {t : Fin 3 → (descentField σ)ˣ} (ht1 : t 1 = 1) (ht2 : t 2 = 1) :
    Commute (twCoverPi σ hσσ hω x)
      ⟨diagOmegaMinus (descentField σ) t, diagOmegaMinus_mem _ _ t⟩ := by
  have w1 : minusWeight (descentField σ) t (Sum.inl 1) = 1 := by
    show ((t 1 : (descentField σ)ˣ) : descentField σ) = 1
    rw [ht1, Units.val_one]
  have w2 : minusWeight (descentField σ) t (Sum.inl 2) = 1 := by
    show ((t 2 : (descentField σ)ˣ) : descentField σ) = 1
    rw [ht2, Units.val_one]
  have w1' : minusWeight (descentField σ) t (Sum.inr (Sum.inl 1)) = 1⁻¹ := by
    show (((t 1)⁻¹ : (descentField σ)ˣ) : descentField σ) = 1⁻¹
    rw [ht1, inv_one, Units.val_one, inv_one]
  have w2' : minusWeight (descentField σ) t (Sum.inr (Sum.inl 2)) = 1 := by
    show (((t 2)⁻¹ : (descentField σ)ˣ) : descentField σ) = 1
    rw [ht2, inv_one, Units.val_one]
  have w2'' : minusWeight (descentField σ) t (Sum.inr (Sum.inl 2)) = 1⁻¹ := by
    rw [w2', inv_one]
  have htail : ∀ a : Fin 2 → descentField σ,
      toLinEquiv _ (descentField σ) (diagOmegaMinus (descentField σ) t)
        (tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a)) =
          (1 : descentField σ)⁻¹ • tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a) := by
    intro a
    rw [toLinEquiv_diag_tail, inv_one, one_smul]
  refine commute_twCoverPi_of_mem_twLevi hσσ hω one_two_subset_Y (fun j hj g hg hgY => ?_) x hx
  have hj' : j = 1 ∨ j = 2 := by simpa using hj
  rcases hj' with rfl | rfl <;> rcases hg with hg | hg
  · obtain ⟨s, hs⟩ := exists_xm_of_mem_twistedRootGroup_one hg
    exact commute_twCoverPi_diag_of_eichler hσσ hω (twCoverPhi_long_one hσσ hω (x := ⟨g, hgY⟩) hs)
      one_ne_zero (toLinEquiv_diag_single_of_weight w1)
      (toLinEquiv_diag_smul_single_of_weight w2'' _)
  · obtain ⟨s, hs⟩ := exists_xm_of_mem_twistedRootGroup_neg_one hg
    exact commute_twCoverPi_diag_of_eichler hσσ hω
      (twCoverPhi_long_one_neg hσσ hω (x := ⟨g, hgY⟩) hs)
      one_ne_zero (toLinEquiv_diag_single_of_weight w2)
      (toLinEquiv_diag_smul_single_of_weight w1' _)
  · obtain ⟨a, c, hc, hgc⟩ := exists_xm_of_mem_twistedRootGroup_two hσσ hω hg
    exact commute_twCoverPi_diag_of_eichler hσσ hω
      (twCoverPhi_short hσσ hω (x := ⟨g, hgY⟩) a hc hgc)
      one_ne_zero (toLinEquiv_diag_single_of_weight w2) (htail a)
  · obtain ⟨a, c, hc, hgc⟩ := exists_xm_of_mem_twistedRootGroup_neg_two hσσ hω hg
    exact commute_twCoverPi_diag_of_eichler hσσ hω
      (twCoverPhi_short_neg hσσ hω (x := ⟨g, hgY⟩) a hc hgc)
      one_ne_zero (toLinEquiv_diag_single_of_weight w2') (htail a)

theorem commute_twCoverPi_zero (x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes)
    (hx : (x : fixedGroup F (σ : F →+* F)) ∈ twLevi F (σ : F →+* F) {0})
    {t : Fin 3 → (descentField σ)ˣ} (ht : t 0 = t 1) :
    Commute (twCoverPi σ hσσ hω x)
      ⟨diagOmegaMinus (descentField σ) t, diagOmegaMinus_mem _ _ t⟩ := by
  have w0 : minusWeight (descentField σ) t (Sum.inl 0) = ((t 0 : (descentField σ)ˣ) :
      descentField σ) := rfl
  have w1 : minusWeight (descentField σ) t (Sum.inl 1) = ((t 0 : (descentField σ)ˣ) :
      descentField σ) := by
    show ((t 1 : (descentField σ)ˣ) : descentField σ) = _
    rw [ht]
  have w0' : minusWeight (descentField σ) t (Sum.inr (Sum.inl 0)) =
      ((t 0 : (descentField σ)ˣ) : descentField σ)⁻¹ := by
    show (((t 0)⁻¹ : (descentField σ)ˣ) : descentField σ) = _
    rw [Units.val_inv_eq_inv_val]
  have w1' : minusWeight (descentField σ) t (Sum.inr (Sum.inl 1)) =
      ((t 0 : (descentField σ)ˣ) : descentField σ)⁻¹ := by
    show (((t 1)⁻¹ : (descentField σ)ˣ) : descentField σ) = _
    rw [← ht, Units.val_inv_eq_inv_val]
  refine commute_twCoverPi_of_mem_twLevi hσσ hω zero_subset_Y (fun j hj g hg hgY => ?_) x hx
  have hj' : j = 0 := by simpa using hj
  subst hj'
  rcases hg with hg | hg
  · obtain ⟨s, hs⟩ := exists_xm_of_mem_twistedRootGroup_zero hg
    exact commute_twCoverPi_diag_of_eichler hσσ hω
      (twCoverPhi_long_zero hσσ hω (x := ⟨g, hgY⟩) hs)
      (t 0).ne_zero (toLinEquiv_diag_single_of_weight w0)
      (toLinEquiv_diag_smul_single_of_weight w1' _)
  · obtain ⟨s, hs⟩ := exists_xm_of_mem_twistedRootGroup_neg_zero hg
    exact commute_twCoverPi_diag_of_eichler hσσ hω
      (twCoverPhi_long_zero_neg hσσ hω (x := ⟨g, hgY⟩) hs)
      (t 0).ne_zero (toLinEquiv_diag_single_of_weight w1)
      (toLinEquiv_diag_smul_single_of_weight w0' _)

end Commute

section Transport

variable {k₁ k₂ : Type} [Field k₁] [Field k₂] [Finite k₁] [Finite k₂] [CharP k₁ 2] [CharP k₂ 2]
  (ε₀ : k₁ ≃+* k₂) {b : k₁} (c : k₁) (hb : ε₀ b ≠ 0)

theorem commute_twTransport_diag {g : StatedOmega (StatedQuadMinus 4 k₁ b c)} {t : Fin 3 → k₂ˣ}
    (h : Commute g ⟨diagOmegaMinus k₁ (fun i => Units.map (ε₀.symm : k₂ →* k₁) (t i)),
      diagOmegaMinus_mem _ _ _⟩) :
    Commute (twTransport ε₀ c hb g) ⟨diagOmegaMinus k₂ t, diagOmegaMinus_mem _ _ t⟩ := by
  have e : twTransport ε₀ c hb ⟨diagOmegaMinus k₁ (fun i => Units.map (ε₀.symm : k₂ →* k₁) (t i)),
      diagOmegaMinus_mem _ _ _⟩ = ⟨diagOmegaMinus k₂ t, diagOmegaMinus_mem _ _ t⟩ := by
    rw [twTransport_diag]
    apply Subtype.ext
    show diagOmegaMinus k₂ _ = diagOmegaMinus k₂ t
    congr 1
    funext i
    apply Units.ext
    simp
  have h' := h.map (twTransport ε₀ c hb).toMonoidHom
  rwa [MulEquiv.coe_toMonoidHom, e] at h'

end Transport

end CFSG.SeitzReduction.F4Pilot
