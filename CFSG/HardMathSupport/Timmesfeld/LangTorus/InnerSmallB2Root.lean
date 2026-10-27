module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallB2Rel
public import CFSG.RankThree.PartOne.S11c.EvenRootInverters
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.Chevalley.SteinbergCFOddE6E7RootInverters
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.Walter.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Elements

@[expose] noncomputable def xr (K : Type) [Field K] (γ : Fin Tag.F4.rank → ℤ) : ModGL Tag.F4 K :=
  pinnedX .F4 K γ 1

variable {K : Type} [Field K] [CharP K 2]

theorem xr_sq (K : Type) [Field K] [CharP K 2] (γ : Fin Tag.F4.rank → ℤ) :
    xr K γ * xr K γ = 1 := by
  unfold xr
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem xr_inv (γ : Fin Tag.F4.rank → ℤ) : (xr K γ)⁻¹ = xr K γ :=
  inv_eq_of_mul_eq_one_right (xr_sq K γ)

theorem uSL_braid : (uSL 1 * vSL 1 * uSL 1 : SL2 K) = vSL 1 * uSL 1 * vSL 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, uSL_val, vSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem xr_braid {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    xr K α * xr K (-α) * xr K α = xr K (-α) * xr K α * xr K (-α) := by
  have hu := rootSL2_uSL_of_charTwo (K := K) hα 1
  have hv := rootSL2_vSL_of_charTwo (K := K) hα 1
  unfold xr
  rw [← hu, ← hv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, uSL_braid]

theorem xr_braid_of {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (h : -α = β) :
    xr K α * xr K β * xr K α = xr K β * xr K α * xr K β := by
  subst h
  exact xr_braid hα

theorem xr_ne_xr_neg {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) : xr K α ≠ xr K (-α) := by
  intro h
  have hinj := (even_Chevalley_pinned_root_SL2_maps (τ := .F4) (K := K) hα).1
  have hu := rootSL2_uSL_of_charTwo (K := K) hα 1
  have hv := rootSL2_vSL_of_charTwo (K := K) hα 1
  have hUV : (uSL 1 : SL2 K) = vSL 1 := hinj (by rw [hu, hv]; exact h)
  have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hUV
  simp [uSL_val, vSL_val] at this

theorem comm_of_sq4 {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y * x * y = 1) : x * y = y * x := by
  have h' : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using h)
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right hx] at h'

theorem not_isRoot_F4 {γ : Fin Tag.F4.rank → ℤ} (h2 : iform γ γ ≠ 2) (h4 : iform γ γ ≠ 4) :
    ¬ IsRoot .F4 γ := fun h => by
  rcases iform_self_cases noG2_F4 h with h | h
  exacts [h2 h, h4 h]

theorem xr_comm_of_nil {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hnil : commPairs .F4 α β = []) :
    xr K α * xr K β = xr K β * xr K α := by
  obtain ⟨C, -, hF⟩ := exists_pinnedX_commFormula_F4_exact hα hβ hne hne'
  have e := hF K 1 1
  rw [hnil, List.map_nil, List.prod_nil, CharTwo.neg_eq (1 : K)] at e
  exact comm_of_sq4 (xr_sq K α) (xr_sq K β) e

theorem xr_comm_of_one {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hl : commPairs .F4 α β = [(1, 1)])
    (hd : IsRoot .F4 (β - α)) : xr K α * xr K β = xr K β * xr K α := by
  classical
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hα hβ hne hne'
  have e := hF K 1 1
  have h11 : ((1, 1) : ℕ × ℕ) ∈ commPairs .F4 α β := by rw [hl]; simp
  have hC11 := hC (1, 1) h11
  simp only [hd, and_self, ite_true] at hC11
  have hC0 : ((C (1, 1) : ℤ) : K) = 0 := by
    rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).1 hC11 with h | h <;> rw [h] <;>
      simp [CharTwo.two_eq_zero]
  rw [hl, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hC0,
    CharTwo.neg_eq (1 : K)] at e
  simp only [zero_mul, pinnedX_zero] at e
  exact comm_of_sq4 (xr_sq K α) (xr_sq K β) e

theorem xr_comm_nonroot {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β)
    (h0 : 0 ≤ iform α β) (hs : ¬ IsRoot .F4 (α + β)) :
    xr K α * xr K β = xr K β * xr K α := by
  by_cases hab : α = β
  · rw [hab]
  have hββ := iform_self_cases noG2_F4 hβ
  have hne' : α ≠ -β := by
    intro e
    have := congrArg (fun x => iform x β) e
    simp only [iform_neg_left_eq] at this
    omega
  refine xr_comm_of_nil hα hβ hab hne' ?_
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  rw [mem_commPairs] at hp
  obtain ⟨hp, hr⟩ := hp
  obtain ⟨⟨h1, -⟩, h2, -⟩ := mem_commCandidates.1 hp
  rcases exponent_pair_cases noG2_F4 hα hβ hab hne' h1 h2 hr with h | h | h
  · obtain ⟨h1', h2'⟩ := h
    apply hs
    have e : p.1 • α + p.2 • β = α + β := by rw [h1', h2', one_smul, one_smul]
    rwa [e] at hr
  · omega
  · omega

theorem xr_comm_short_orth {α β γ δ : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (hβ : IsRoot .F4 β) (h0 : iform α β = 0) (hαα : iform α α = 2) (e1 : α + β = γ)
    (hγ : IsRoot .F4 γ) (e2 : β - α = δ) (hδ : IsRoot .F4 δ) :
    xr K α * xr K β = xr K β * xr K α := by
  subst e1 e2
  have hab : α ≠ β := by
    intro e
    rw [e] at h0 hαα
    omega
  have hne' : α ≠ -β := by
    intro e
    have := congrArg (fun x => iform x β) e
    simp only [iform_neg_left_eq] at this
    have := iform_self_cases noG2_F4 hβ
    omega
  refine xr_comm_of_one hα hβ hab hne' ?_ hδ
  refine commPairs_eq_of_mem_iff α β (by simp) fun p => ?_
  rw [mem_commPairs, List.mem_singleton]
  constructor
  · rintro ⟨hp, hr⟩
    obtain ⟨⟨h1, -⟩, h2, -⟩ := mem_commCandidates.1 hp
    rcases exponent_pair_cases noG2_F4 hα hβ hab hne' h1 h2 hr with h | h | h
    · exact Prod.ext h.1 h.2
    · omega
    · omega
  · rintro rfl
    exact ⟨by decide, by simpa using hγ⟩

theorem xr_mixed_eq {sg lg ρ π : Fin Tag.F4.rank → ℤ} (hs : IsRoot .F4 sg) (hl : IsRoot .F4 lg)
    (hss : iform sg sg = 2) (hll : iform lg lg = 4) (hsl : iform sg lg = -2) (e1 : sg + lg = ρ)
    (e2 : 2 • sg + lg = π) :
    xr K sg * xr K lg * xr K sg * xr K lg = xr K ρ * xr K π := by
  subst e1 e2
  obtain ⟨-, -, C₁, C₂, hC₁, hC₂, hform⟩ := f4_commutator_mixed hs hl hss hll hsl
  have e := hform K 1 1
  have hc : ∀ C : ℤ, (C = 1 ∨ C = -1) → ((C : ℤ) : K) = 1 := fun C h => by
    rcases h with rfl | rfl
    · simp
    · simpa using CharTwo.neg_eq (1 : K)
  have hi1 : (pinnedX .F4 K sg 1)⁻¹ = pinnedX .F4 K sg 1 := xr_inv sg
  have hi2 : (pinnedX .F4 K lg 1)⁻¹ = pinnedX .F4 K lg 1 := xr_inv lg
  rw [commutatorElement_def, hi1, hi2, hc C₁ hC₁, hc C₂ hC₂] at e
  simp only [mul_one, one_pow] at e
  exact e

end Elements

open scoped Pointwise

set_option hygiene false in
local macro "iform_eval" : tactic =>
  `(tactic| (simp only [two_nsmul, iform_add_left, iform_add_right, iform_neg_left_eq,
      iform_neg_right_eq, hss, hll, hsl, hls]; try norm_num))

theorem b2Rel_F4 {K : Type} [Field K] [CharP K 2] {s l : Fin Tag.F4.rank → ℤ}
    (hs : IsRoot .F4 s) (hl : IsRoot .F4 l) (hss : iform s s = 2) (hll : iform l l = 4)
    (hsl : iform s l = -2) :
    B2Rel (xr K s) (xr K (-s)) (xr K l) (xr K (-l)) (xr K (s + l)) (xr K (-(s + l)))
      (xr K (2 • s + l)) (xr K (-(2 • s + l))) := by
  have hls : iform l s = -2 := by rw [iform_comm]; exact hsl
  obtain ⟨ha, hb, -⟩ := f4_commutator_mixed hs hl hss hll hsl
  have hms := IsRoot.neg hs
  have hml := IsRoot.neg hl
  have hma := IsRoot.neg ha
  have hmb := IsRoot.neg hb
  exact {
    r0 := xr_sq _ _,
    r1 := xr_sq _ _,
    r2 := xr_sq _ _,
    r3 := xr_sq _ _,
    r4 := xr_sq _ _,
    r5 := xr_sq _ _,
    r6 := xr_sq _ _,
    r7 := xr_sq _ _,
    r8 := xr_braid_of hms (by simp),
    r9 := xr_comm_nonroot hms hl (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r10 := xr_comm_short_orth hms ha (by iform_eval) (by iform_eval) (by abel) hl (by abel) hb,
    r11 := xr_mixed_eq hms hb (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r12 := xr_mixed_eq hs hl (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r13 := xr_comm_nonroot hml hs (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r14 := xr_mixed_eq hms hml (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r15 := xr_braid_of hml (by simp),
    r16 := xr_mixed_eq ha hml (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r17 := xr_comm_nonroot hml hb (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r18 := xr_comm_short_orth ha hs (by iform_eval) (by iform_eval) (by abel) hb (by abel) hml,
    r19 := xr_comm_nonroot ha hl (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r20 := xr_comm_nonroot ha hb (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r21 := xr_comm_short_orth hma hs (by iform_eval) (by iform_eval) (by abel) hml (by abel) hb,
    r22 := xr_comm_short_orth hma hms (by iform_eval) (by iform_eval) (by abel) hmb (by abel) hl,
    r23 := xr_mixed_eq hma hl (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r24 := xr_comm_nonroot hma hml (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r25 := xr_braid_of hma (by simp),
    r26 := xr_mixed_eq hma hb (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r27 := xr_comm_nonroot hma hmb (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r28 := xr_comm_nonroot hb hs (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r29 := xr_comm_nonroot hb hl (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r30 := xr_mixed_eq hs hmb (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r31 := xr_comm_nonroot hmb hms (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r32 := xr_comm_nonroot hmb hl (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r33 := xr_comm_nonroot hmb hml (by iform_eval) (not_isRoot_F4 (by iform_eval) (by iform_eval)),
    r34 := xr_mixed_eq ha hmb (by iform_eval) (by iform_eval) (by iform_eval) (by abel) (by abel),
    r35 := xr_braid_of hmb (by simp),
  }

end CFSG.HardMathSupport.Timmesfeld.LangTorus
