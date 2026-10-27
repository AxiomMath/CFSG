module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviModelRigid

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

section Entries

variable {k : Type} [Field k]

theorem eichler_apply_coord {ι : Type*} {Q : QuadraticForm k (ι → k)} {u w : ι → k}
    (hu : Q u = 0) (hw : polar Q u w = 0) (x : ι → k) (p : ι) :
    eichler Q u w x p = x p + polar Q x u * w p - (polar Q x w + Q w * polar Q x u) * u p := by
  rw [eichler_apply hu hw]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

variable (b c : k)

set_option linter.unusedSimpArgs false in
theorem eichler_entry_long_one (t : k) (i j : Fin 3 ⊕ Fin 3) :
    eichler (quadMinus 4 k b c) (Pi.single (Sum.inl 1) 1)
        ((-t) • Pi.single (Sum.inr (Sum.inl 2)) 1) (Pi.single (minusEmb j) 1) (minusEmb i) =
      mat 3 k (CFSG.LieType.Steinberg.Sp.x 3 k (Pi.single 1 1) t) i j := by
  have hw : polar (quadMinus 4 k b c) (Pi.single (Sum.inl 1) 1)
      ((-t) • Pi.single (Sum.inr (Sum.inl 2)) 1) = 0 := by
    rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  rw [eichler_apply_coord (quadMinus_single_inl _) hw,
    polar_comm _ (Pi.single (minusEmb j) 1) (Pi.single (Sum.inl 1) 1), polar_single_inl_quadMinus,
    polar_smul_right, polar_comm _ (Pi.single (minusEmb j) 1) (Pi.single (Sum.inr (Sum.inl 2)) 1),
    polar_single_inr_quadMinus, QuadraticMap.map_smul, quadMinus_single_inr, mat_sp_x_single_one]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minusEmb, Pi.single_apply, Matrix.one_apply, Matrix.single_apply]

set_option linter.unusedSimpArgs false in
theorem eichler_entry_long_one_neg (t : k) (i j : Fin 3 ⊕ Fin 3) :
    eichler (quadMinus 4 k b c) (Pi.single (Sum.inl 2) 1)
        ((-t) • Pi.single (Sum.inr (Sum.inl 1)) 1) (Pi.single (minusEmb j) 1) (minusEmb i) =
      mat 3 k (CFSG.LieType.Steinberg.Sp.x 3 k (-Pi.single 1 1) t) i j := by
  have hw : polar (quadMinus 4 k b c) (Pi.single (Sum.inl 2) 1)
      ((-t) • Pi.single (Sum.inr (Sum.inl 1)) 1) = 0 := by
    rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  rw [eichler_apply_coord (quadMinus_single_inl _) hw,
    polar_comm _ (Pi.single (minusEmb j) 1) (Pi.single (Sum.inl 2) 1), polar_single_inl_quadMinus,
    polar_smul_right, polar_comm _ (Pi.single (minusEmb j) 1) (Pi.single (Sum.inr (Sum.inl 1)) 1),
    polar_single_inr_quadMinus, QuadraticMap.map_smul, quadMinus_single_inr,
    mat_sp_x_neg_single_one]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minusEmb, Pi.single_apply, Matrix.one_apply, Matrix.single_apply]

theorem polar_single_minusEmb_tail (j : Fin 3 ⊕ Fin 3) (a : Fin 2 → k) :
    polar (quadMinus 4 k b c) (Pi.single (minusEmb j) 1)
      (tailModelEquiv (4 - 1) k (Fin 2) (0, a)) = 0 := by
  rcases j with j | j
  · exact (polar_single_inl_quadMinus (n := 4) j _).trans rfl
  · exact (polar_single_inr_quadMinus (n := 4) j _).trans rfl

theorem quadMinus_tail_fst (s : k) :
    quadMinus 4 k b c (tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0])) = s ^ 2 := by
  rw [quadMinus_apply]
  simp [tailModelEquiv_inl, tailModelEquiv_inr_inl, tailModelEquiv_inr_inr]

set_option linter.unusedSimpArgs false in
theorem eichler_entry_short (s : k) (i j : Fin 3 ⊕ Fin 3) :
    eichler (quadMinus 4 k b c) (Pi.single (Sum.inl 2) 1)
        (tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0])) (Pi.single (minusEmb j) 1) (minusEmb i) =
      mat 3 k (CFSG.LieType.Steinberg.Sp.x 3 k (Pi.single 2 1) (-(s ^ 2))) i j := by
  have hw : polar (quadMinus 4 k b c) (Pi.single (Sum.inl 2) 1)
      (tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0])) = 0 :=
    polar_single_minusEmb_tail b c (Sum.inl 2) _
  have h0 : ∀ i : Fin 3 ⊕ Fin 3,
      tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0]) (minusEmb i) = 0 := fun i => by
    rcases i with i | i <;> rfl
  rw [eichler_apply_coord (quadMinus_single_inl _) hw, polar_single_minusEmb_tail, h0,
    quadMinus_tail_fst, polar_comm _ (Pi.single (minusEmb j) 1) (Pi.single (Sum.inl 2) 1),
    polar_single_inl_quadMinus, mat_sp_x_single_two]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minusEmb, Pi.single_apply, Matrix.one_apply, Matrix.single_apply]

set_option linter.unusedSimpArgs false in
theorem eichler_entry_short_neg (s : k) (i j : Fin 3 ⊕ Fin 3) :
    eichler (quadMinus 4 k b c) (Pi.single (Sum.inr (Sum.inl 2)) 1)
        (tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0])) (Pi.single (minusEmb j) 1) (minusEmb i) =
      mat 3 k (CFSG.LieType.Steinberg.Sp.x 3 k (-Pi.single 2 1) (-(s ^ 2))) i j := by
  have hw : polar (quadMinus 4 k b c) (Pi.single (Sum.inr (Sum.inl 2)) 1)
      (tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0])) = 0 :=
    polar_single_minusEmb_tail b c (Sum.inr 2) _
  have h0 : ∀ i : Fin 3 ⊕ Fin 3,
      tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0]) (minusEmb i) = 0 := fun i => by
    rcases i with i | i <;> rfl
  rw [eichler_apply_coord (quadMinus_single_inr _) hw, polar_single_minusEmb_tail, h0,
    quadMinus_tail_fst,
    polar_comm _ (Pi.single (minusEmb j) 1) (Pi.single (Sum.inr (Sum.inl 2)) 1),
    polar_single_inr_quadMinus, mat_sp_x_neg_single_two]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minusEmb, Pi.single_apply, Matrix.one_apply, Matrix.single_apply]

theorem polar_minusVec_single_minusEmb (j : Fin 3 ⊕ Fin 3) :
    polar (quadMinus 4 k b c) (minusVec k) (Pi.single (minusEmb j) 1) = 0 := by
  rw [polar_comm]
  rcases j with j | j
  · exact (polar_single_inl_quadMinus (n := 4) j _).trans (minusVec_minusEmb k (Sum.inr j))
  · exact (polar_single_inr_quadMinus (n := 4) j _).trans (minusVec_minusEmb k (Sum.inl j))

theorem polar_minusVec_smul_single_minusEmb (j : Fin 3 ⊕ Fin 3) (a : k) :
    polar (quadMinus 4 k b c) (minusVec k) (a • Pi.single (minusEmb j) 1) = 0 := by
  rw [polar_smul_right, polar_minusVec_single_minusEmb, smul_zero]

theorem polar_minusVec_tail [CharP k 2] (s : k) :
    polar (quadMinus 4 k b c) (minusVec k) (tailModelEquiv (4 - 1) k (Fin 2) (0, ![s, 0])) = 0 := by
  rw [polar_quadMinus]
  simp [minusVec, tailModelEquiv_inl, tailModelEquiv_inr_inl, tailModelEquiv_inr_inr,
    CharTwo.two_eq_zero]

end Entries

section Res

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

theorem twCoverPi_apply_apply (y : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes)
    (p q : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) :
    (((twCoverPi σ hσσ hω y : StatedOmega
      (StatedQuadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :
        GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (descentField σ)) :
          Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
            (descentField σ)) p q = (twCoverPhi σ hσσ hω y).val (Pi.single q 1) p :=
  toLinEquiv_symm_apply_apply _ p q

variable {K : Type} [Field K] [Finite K] [CharP K 2] (ε₀ : descentField σ ≃+* K)
  (hb : ε₀ (d4MinusB hσσ ω) ≠ 0)

theorem omegaMinusIota_eq_twTransport_of_eichler {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hc : ∀ s : K, s ^ 2 + 1 * s + ε₀ (d4MinusC hσσ ω) / ε₀ (d4MinusB hσσ ω) ^ 2 ≠ 0)
    {y : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {u w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ}
    (hy : (twCoverPhi σ hσσ hω y).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w)
    (hu : polar (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (minusVec (descentField σ)) u = 0)
    (hw : polar (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (minusVec (descentField σ)) w = 0)
    {g : StatedSp 3 (descentField σ)}
    (hg : ∀ i j, eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w
      (Pi.single (minusEmb j) 1) (minusEmb i) = mat 3 (descentField σ) g i j) :
    omegaMinusIota hK hf hc (statedSpCongr ε₀ 3 g) =
      twTransport ε₀ (d4MinusC hσσ ω) hb (twCoverPi σ hσσ hω y) := by
  have hfix0 : twCoverPi σ hσσ hω y ∈
      fixedSubgroup (omegaMinusBetaC (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) := by
    rw [mem_fixedSubgroup_omegaMinusBetaC_iff (descentField σ) (d4Minus_irr hσσ hω)]
    have h1 := toLinEquiv_apply ((twCoverPi σ hσσ hω y : StatedOmega
      (StatedQuadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :
        GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (descentField σ)) (minusVec (descentField σ))
    rw [toLinEquiv_twCoverPi, hy] at h1
    rw [← h1]
    exact eichler_apply_of_polar_eq_zero hu hw
  have hfix := twTransport_mem_fixedSubgroup ε₀ (d4MinusC hσσ ω) hb hfix0
  refine omegaMinusIota_eq_of_res hK hf hc (y := ⟨_, hfix⟩) ?_
  apply mat_injective
  rw [mat_apply, coe_omegaMinusRes, mat_apply, coe_statedSpCongr, coe_statedSpMap]
  ext i j
  rw [Matrix.submatrix_apply, twTransport_apply_minusEmb, twCoverPi_apply_apply, hy, hg]
  rfl

end Res

section Field

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem descentField_barEquiv : descentField h.barEquiv = h.fixedField :=
  Subfield.ext fun _ => Iff.rfl

variable {K : Type} [Field K] (ε : h.fixedField ≃+* K)

@[expose] noncomputable def twFieldEquiv : descentField h.barEquiv ≃+* K :=
  (RingEquiv.subfieldCongr (descentField_barEquiv h)).trans ε

@[expose] def toDescentField (c : h.fixedField) : descentField h.barEquiv :=
  ⟨(c : F), mem_descentField.2 ((h.mem_fixedField).1 c.2)⟩

omit ε in
theorem twBar_bar : ∀ c, h.barEquiv (h.barEquiv c) = c :=
  h.bar_bar

end Field

section Gens

variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem coe_twParamEquiv_uEmbed6_x_single_two (c : h.fixedField) :
    (((twParamEquiv h (uEmbed6 h (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 2 1) c)) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 1) 1) (c : F) := by
  rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_single_two, map_transvection,
    graphParamHom_transvection, a5Root_graphSwapPerm_check.1]
  rfl

theorem coe_twParamEquiv_uEmbed6_x_neg_single_two (c : h.fixedField) :
    (((twParamEquiv h (uEmbed6 h
      (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 2 1) c)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 1) 1) (c : F) := by
  rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_neg_single_two, map_transvection,
    graphParamHom_transvection, a5Root_graphSwapPerm_check.2.1]
  rfl

theorem coe_twParamEquiv_uEmbed6_x_single_one (c : h.fixedField) :
    (((twParamEquiv h (uEmbed6 h (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 1 1) c)) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 2) 1) (c : F) *
        e6Data_valid.xm F (Pi.single (jD 3) 1) (h.barEquiv (c : F)) := by
  rw [show h.barEquiv (c : F) = c from (h.mem_fixedField).1 c.2, coe_twParamEquiv_uEmbed6,
    sp6ToSL6_x_single_one_eq, rgUSL, map_mul, map_transvection, map_transvection]
  exact graphParamHom_rgUSL (c : F) (c : F)

theorem coe_twParamEquiv_uEmbed6_x_neg_single_one (c : h.fixedField) :
    (((twParamEquiv h (uEmbed6 h
      (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 1 1) c)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 2) 1) (c : F) *
        e6Data_valid.xm F (-Pi.single (jD 3) 1) (h.barEquiv (c : F)) := by
  rw [show h.barEquiv (c : F) = c from (h.mem_fixedField).1 c.2, coe_twParamEquiv_uEmbed6,
    sp6ToSL6_x_neg_single_one_eq, rgUmSL, map_mul, map_transvection, map_transvection]
  exact graphParamHom_rgUmSL (c : F) (c : F)

theorem twParamEquiv_uEmbed6_mem_Y {s : StatedSp 3 h.fixedField} (hs : s ∈ sp4Gens h.fixedField) :
    ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) ∈
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes := by
  have hA3 : s ∈ rigA3Good h := by
    obtain ⟨c, rfl | rfl | rfl | rfl⟩ := hs
    · exact spx_one_mem_rigA3Good h c (Or.inl rfl)
    · exact spx_one_mem_rigA3Good h c (Or.inr rfl)
    · exact spx_two_mem_rigA3Good h c (Or.inl rfl)
    · exact spx_two_mem_rigA3Good h c (Or.inr rfl)
  exact CFSG.LieType.CurtisTits.levi_mono _ one_two_subset_Y ((mem_rigA3Good h).1 hA3).2

end Gens

section Partners

variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
  {K : Type} [Field K] [Finite K] [CharP K 2] (ε : h.fixedField ≃+* K)
  {ω : F} (hω : h.barEquiv ω ≠ ω) (hb : twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ≠ 0)
  (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
  (hc : ∀ s : K, s ^ 2 + 1 * s + twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
    twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2 ≠ 0)

theorem omegaMinusIota_partner_x_single_two (c : h.fixedField)
    (hmem : ((twParamEquiv h (uEmbed6 h
      (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 2 1) c)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) ∈
        twLevi F (h.barEquiv : F →+* F) AmalgamNeighbour.Y.nodes) :
    omegaMinusIota hK hf hc (CFSG.LieType.Steinberg.Sp.x 3 K (Pi.single 1 1) (ε c)) =
      twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω) hb
        (twCoverPi h.barEquiv (twBar_bar h) hω ⟨_, hmem⟩) := by
  have e : CFSG.LieType.Steinberg.Sp.x 3 K (Pi.single 1 1) (ε c) =
      statedSpCongr (twFieldEquiv h ε) 3 (CFSG.LieType.Steinberg.Sp.x 3 (descentField h.barEquiv)
        (Pi.single 1 1) (toDescentField h c)) := by
    rw [statedSpCongr_x]
    rfl
  rw [e]
  exact omegaMinusIota_eq_twTransport_of_eichler (twBar_bar h) hω (twFieldEquiv h ε) hb hK hf hc
    (twCoverPhi_long_one (twBar_bar h) hω (t := toDescentField h c)
      (coe_twParamEquiv_uEmbed6_x_single_two h c))
    (polar_minusVec_single_minusEmb _ _ (Sum.inl 1))
    (polar_minusVec_smul_single_minusEmb _ _ (Sum.inr 2) _) (eichler_entry_long_one _ _ _)

theorem omegaMinusIota_partner_x_neg_single_two (c : h.fixedField)
    (hmem : ((twParamEquiv h (uEmbed6 h
      (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 2 1) c)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) ∈
        twLevi F (h.barEquiv : F →+* F) AmalgamNeighbour.Y.nodes) :
    omegaMinusIota hK hf hc (CFSG.LieType.Steinberg.Sp.x 3 K (-Pi.single 1 1) (ε c)) =
      twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω) hb
        (twCoverPi h.barEquiv (twBar_bar h) hω ⟨_, hmem⟩) := by
  have e : CFSG.LieType.Steinberg.Sp.x 3 K (-Pi.single 1 1) (ε c) =
      statedSpCongr (twFieldEquiv h ε) 3 (CFSG.LieType.Steinberg.Sp.x 3 (descentField h.barEquiv)
        (-Pi.single 1 1) (toDescentField h c)) := by
    rw [statedSpCongr_x]
    rfl
  rw [e]
  exact omegaMinusIota_eq_twTransport_of_eichler (twBar_bar h) hω (twFieldEquiv h ε) hb hK hf hc
    (twCoverPhi_long_one_neg (twBar_bar h) hω (t := toDescentField h c)
      (coe_twParamEquiv_uEmbed6_x_neg_single_two h c))
    (polar_minusVec_single_minusEmb _ _ (Sum.inl 2))
    (polar_minusVec_smul_single_minusEmb _ _ (Sum.inr 1) _) (eichler_entry_long_one_neg _ _ _)

theorem omegaMinusIota_partner_x_single_one (c : h.fixedField)
    (hmem : ((twParamEquiv h (uEmbed6 h
      (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (Pi.single 1 1) c)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) ∈
        twLevi F (h.barEquiv : F →+* F) AmalgamNeighbour.Y.nodes) :
    omegaMinusIota hK hf hc (CFSG.LieType.Steinberg.Sp.x 3 K (Pi.single 2 1) (ε c ^ 2)) =
      twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω) hb
        (twCoverPi h.barEquiv (twBar_bar h) hω ⟨_, hmem⟩) := by
  have e : CFSG.LieType.Steinberg.Sp.x 3 K (Pi.single 2 1) (ε c ^ 2) =
      statedSpCongr (twFieldEquiv h ε) 3 (CFSG.LieType.Steinberg.Sp.x 3 (descentField h.barEquiv)
        (Pi.single 2 1) (-(toDescentField h c ^ 2))) := by
    rw [statedSpCongr_x, map_neg, map_pow, CharTwo.neg_eq]
    rfl
  have hc' : (c : F) = -(((![toDescentField h c, 0] 0 : descentField h.barEquiv) : F) +
      ((![toDescentField h c, 0] 1 : descentField h.barEquiv) : F) * h.barEquiv ω) := by
    show (c : F) = -((c : F) + 0 * h.barEquiv ω)
    rw [zero_mul, add_zero, CharTwo.neg_eq]
  rw [e]
  exact omegaMinusIota_eq_twTransport_of_eichler (twBar_bar h) hω (twFieldEquiv h ε) hb hK hf hc
    (twCoverPhi_short (twBar_bar h) hω _ hc' (coe_twParamEquiv_uEmbed6_x_single_one h c))
    (polar_minusVec_single_minusEmb _ _ (Sum.inl 2)) (polar_minusVec_tail _ _ _)
    (eichler_entry_short _ _ _)

theorem omegaMinusIota_partner_x_neg_single_one (c : h.fixedField)
    (hmem : ((twParamEquiv h (uEmbed6 h
      (CFSG.LieType.Steinberg.Sp.x 3 h.fixedField (-Pi.single 1 1) c)) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) ∈
        twLevi F (h.barEquiv : F →+* F) AmalgamNeighbour.Y.nodes) :
    omegaMinusIota hK hf hc (CFSG.LieType.Steinberg.Sp.x 3 K (-Pi.single 2 1) (ε c ^ 2)) =
      twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω) hb
        (twCoverPi h.barEquiv (twBar_bar h) hω ⟨_, hmem⟩) := by
  have e : CFSG.LieType.Steinberg.Sp.x 3 K (-Pi.single 2 1) (ε c ^ 2) =
      statedSpCongr (twFieldEquiv h ε) 3 (CFSG.LieType.Steinberg.Sp.x 3 (descentField h.barEquiv)
        (-Pi.single 2 1) (-(toDescentField h c ^ 2))) := by
    rw [statedSpCongr_x, map_neg, map_pow,
      CharTwo.neg_eq (twFieldEquiv h ε (toDescentField h c) ^ 2)]
    rfl
  have hc' : (c : F) = ((![toDescentField h c, 0] 0 : descentField h.barEquiv) : F) +
      ((![toDescentField h c, 0] 1 : descentField h.barEquiv) : F) * ω := by
    show (c : F) = (c : F) + 0 * ω
    rw [zero_mul, add_zero]
  rw [e]
  exact omegaMinusIota_eq_twTransport_of_eichler (twBar_bar h) hω (twFieldEquiv h ε) hb hK hf hc
    (twCoverPhi_short_neg (twBar_bar h) hω _ hc' (coe_twParamEquiv_uEmbed6_x_neg_single_one h c))
    (polar_minusVec_single_minusEmb _ _ (Sum.inr 2)) (polar_minusVec_tail _ _ _)
    (eichler_entry_short_neg _ _ _)

end Partners

end CFSG.SeitzReduction.F4Pilot
