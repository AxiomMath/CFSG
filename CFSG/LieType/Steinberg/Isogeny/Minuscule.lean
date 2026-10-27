module

public import CFSG.LieType.Steinberg.Isogeny.Lift
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.ChevExtras
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

variable {τ : Tag}

@[expose] def minWeylSign (D : MinData τ) (a : ℕ) (i : Fin τ.rank) : ℤ :=
  if D.signs.getD a 0 / 2 ^ (i : ℕ) % 2 = 1 then -1 else 1

@[expose] def minPairSign (D : MinData τ) (l : ℕ) (j : Fin τ.rank) : ℤ :=
  if dig (D.pairTable.getD l 0) j % 2 = 1 then -1 else 1

@[expose] def checkSigns (D : MinData τ) (D' : AdjData τ) : Bool :=
  ((List.range τ.rootCertificate.roots.length).all fun a => (List.finRange τ.rank).all fun i =>
    D'.weylSign a i == minWeylSign D a i) &&
  ((List.range τ.rootCertificate.roots.length).all fun l => (List.finRange τ.rank).all fun j =>
    decide (l = D'.neg j) || D'.pairDig l j == 0 ||
      (((D'.pairDig l j % 8 : ℕ) : ℤ) - 4 == minPairSign D l j)) &&
  ((List.finRange τ.rank).all fun j => D'.weylSign j j == -1)

section Checks

variable {D : MinData τ} {D' : AdjData τ} (h : checkSigns D D' = true)
include h

theorem checkSigns_weyl {a : ℕ} (ha : a < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    D'.weylSign a i = minWeylSign D a i := by
  simp only [checkSigns, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies, beq_iff_eq] at h
  exact h.1.1 a ha i

theorem checkSigns_pair {l : ℕ} (hl : l < τ.rootCertificate.roots.length) (j : Fin τ.rank)
    (hlj : l ≠ D'.neg j) (hd : D'.pairDig l j ≠ 0) :
    ((D'.pairDig l j % 8 : ℕ) : ℤ) - 4 = minPairSign D l j := by
  simp only [checkSigns, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (h.1.2 l hl j).resolve_left (by simp [hlj, hd])

theorem checkSigns_self (j : Fin τ.rank) : D'.weylSign j j = -1 := by
  simp only [checkSigns, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq] at h
  exact h.2 j

end Checks

section Minuscule

variable {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]
include hV

theorem nOp_rootOp_nInv {a : ℕ} (ha : a < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    D.nOp k i * D.rootOp k (τ.rootCertificate.root a) * D.nInv k i =
      (minWeylSign D a i : k) • D.rootOp k (reflect τ i (τ.rootCertificate.root a)) := by
  rw [MinData.rootOp_root ha, ← MinData.root_image ha i,
    MinData.rootOp_root (MinData.image_lt ha i), MinData.nOp, MinData.E, MinData.nInv,
    ← (hV.isSPerm_weylOp i).toEnd_conj hV.d_le (hV.wf_op a), hV.conj_op ha i, minWeylSign]
  split_ifs
  · rw [toEnd_neg, Int.cast_neg, Int.cast_one, neg_one_smul]
    rfl
  · rw [Int.cast_one, one_smul]
    rfl

theorem nm_conj_xm_root {a : ℕ} (ha : a < τ.rootCertificate.roots.length) (i : Fin τ.rank)
    (c : k) :
    hV.nm k i * hV.xm k (τ.rootCertificate.root a) c * (hV.nm k i)⁻¹ =
      hV.xm k (reflect τ i (τ.rootCertificate.root a)) ((minWeylSign D a i : k) * c) := by
  refine hV.endo_injective k ?_
  rw [MinData.Valid.endo_mul, MinData.Valid.endo_mul, hV.endo_nm, hV.endo_nm_inv,
    MinData.Valid.endo_xm, MinData.Valid.endo_xm, mul_add, add_mul, mul_one, hV.nOp_mul_nInv,
    mul_smul_comm, smul_mul_assoc, nOp_rootOp_nInv hV k ha i, smul_smul, mul_comm c]

theorem rootOp_bracket_single {l : ℕ} (hl : l < τ.rootCertificate.roots.length)
    (j : Fin τ.rank) (hne : τ.rootCertificate.root l ≠ -Pi.single j 1)
    (hr : IsRoot τ (Pi.single j 1 + τ.rootCertificate.root l)) :
    D.rootOp k (Pi.single j 1) * D.rootOp k (τ.rootCertificate.root l) -
        D.rootOp k (τ.rootCertificate.root l) * D.rootOp k (Pi.single j 1) =
      (minPairSign D l j : k) • D.rootOp k (Pi.single j 1 + τ.rootCertificate.root l) := by
  have hP : D.checkPairs = true := by
    have := hV.check
    simp only [MinData.check, Bool.and_eq_true] at this
    tauto
  simp only [MinData.checkPairs, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies] at hP
  have h := hP l hl j
  have hj : (j : ℕ) < τ.rootCertificate.roots.length :=
    lt_of_lt_of_le j.2 MinData.rank_le_length
  have hEj : D.rootOp k (Pi.single j 1) = D.E k j := by
    rw [← MinData.root_basis j, MinData.rootOp_root hj]
  have hA : toEnd k D.d (comp D.d (D.op j) (D.op l)) = D.E k j * D.E k l :=
    toEnd_comp (hV.wf_op l)
  have hB : toEnd k D.d (comp D.d (D.op l) (D.op j)) = D.E k l * D.E k j :=
    toEnd_comp (hV.wf_op j)
  rw [hEj, MinData.rootOp_root hl, ← hA, ← hB, minPairSign]
  split_ifs at h with hc hs
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    rcases h with h | ⟨h1, -⟩
    · exact absurd (List.ofFn_injective h) hne
    · rw [(StringData.memDec_iff τ.rootCertificate_check τ.stringData_check).2 hr] at h1
      exact absurd h1 (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hm, hroot⟩, hdisj⟩, hunion⟩, -⟩, -⟩ := h
    rw [ite_eq_left hs, ← toEnd_union_neg hdisj, hunion, toEnd_neg, ← List.ofFn_injective hroot,
      MinData.rootOp_root hm, Int.cast_neg, Int.cast_one, neg_one_smul]
    rfl
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hm, hroot⟩, hdisj⟩, hunion⟩, -⟩, -⟩ := h
    rw [ite_eq_right hs, ← toEnd_union_neg hdisj, hunion, ← List.ofFn_injective hroot,
      MinData.rootOp_root hm, Int.cast_one, one_smul]
    rfl

theorem commutator_xm_single {l : ℕ} (hl : l < τ.rootCertificate.roots.length)
    (j : Fin τ.rank) (hne : Pi.single j 1 + τ.rootCertificate.root l ≠ 0)
    (hr : IsRoot τ (Pi.single j 1 + τ.rootCertificate.root l)) (c d : k) :
    ⁅hV.xm k (Pi.single j 1) c, hV.xm k (τ.rootCertificate.root l) d⁆ =
      hV.xm k (Pi.single j 1 + τ.rootCertificate.root l) ((minPairSign D l j : k) * c * d) := by
  have hγ : IsRoot τ (Pi.single j 1) := isRoot_single τ j
  have hδ : IsRoot τ (τ.rootCertificate.root l) := RootCertificate.isRoot_root
    τ.rootCertificate_check l hl
  have hne' : τ.rootCertificate.root l ≠ -Pi.single j 1 := fun h0 => hne (by
    rw [h0, add_neg_cancel])
  obtain ⟨hroot, -⟩ := hV.pairRel (R := k) hγ hδ hne
  obtain ⟨-, h1, h2⟩ := hroot hr
  have hX : (c • D.rootOp k (Pi.single j 1)) * (c • D.rootOp k (Pi.single j 1)) = 0 := by
    rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero]
  have hY : (d • D.rootOp k (τ.rootCertificate.root l)) *
      (d • D.rootOp k (τ.rootCertificate.root l)) = 0 := by
    rw [smul_mul_smul_comm, hV.rootOp_mul_self, smul_zero]
  refine hV.endo_injective k ?_
  rw [hV.endo_commutator, commutator_one_add hX hY, MinData.Valid.endo_xm, smul_mul_smul_comm,
    smul_mul_smul_comm, mul_comm d c, ← smul_sub, rootOp_bracket_single hV k hl j hne' hr,
    smul_smul, mul_comm (c * d), mul_assoc]
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, h1, smul_zero]
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, h2, smul_zero]

end Minuscule

section Adjoint

variable (F : RootOperatorFamily τ) {D' : AdjData τ} (hD : D'.Valid)

open _root_.Classical in
@[expose] def relSignOr (γ : Fin τ.rank → ℤ) : ℤ :=
  if h : IsRoot τ γ then RootOperatorFamily'.relSign F hD ⟨γ, h⟩ else 1

@[expose] def yPar {k : Type} [Field k] (γ : Fin τ.rank → ℤ) (c : k) : ↥(adjointGroup τ k) :=
  xPar F γ ((relSignOr F hD γ : k) * c)

variable {F hD} {k : Type} [Field k]

theorem relSignOr_of_isRoot {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    relSignOr F hD γ = RootOperatorFamily'.relSign F hD ⟨γ, h⟩ := by
  classical
  exact dite_eq_left h

theorem relSignOr_mul_self (γ : Fin τ.rank → ℤ) :
    (relSignOr F hD γ : k) * (relSignOr F hD γ : k) = 1 := by
  by_cases h : IsRoot τ γ
  · rw [relSignOr_of_isRoot h]
    exact sign_cast_eq (RootOperatorFamily'.relSign_eq F hD _)
  · classical
    rw [relSignOr, dite_eq_right h, Int.cast_one, one_mul]

theorem yPar_add (γ : Fin τ.rank → ℤ) (c d : k) :
    yPar F hD γ (c + d) = yPar F hD γ c * yPar F hD γ d := by
  rw [yPar, yPar, yPar, mul_add, xPar_add]

theorem rootOp_ne_zero (F₀ : RootOperatorFamily τ) (hD₀ : D'.Valid) (α : Root τ) :
    D'.rootOp k α ≠ 0 := by
  intro h0
  obtain ⟨a, b, hab⟩ := RootOperatorFamily'.exists_D_one_apply_ne_zero F₀ (R := k) α
  rw [RootOperatorFamily'.D_one_eq F₀ hD₀ α k, h0, smul_zero] at hab
  exact hab rfl

theorem sign_mul_relSign (α : Root τ) (i : Fin τ.rank) :
    ((F.sign i α * RootOperatorFamily'.relSign F hD α * D'.rootSign α i : ℤ) : k) =
      (RootOperatorFamily'.relSign F hD (sRoot i α) : k) := by
  have h1 : F.D k (simple τ i • α) 1 = ((F.sign i α * RootOperatorFamily'.relSign F hD α *
      D'.rootSign α i : ℤ) : k) • D'.rootOp k (sRoot i α) := by
    rw [F.D_simple_smul, pow_one, RootOperatorFamily'.D_one_eq F hD α k, mul_smul_comm,
      smul_mul_assoc, ← weylElt_inv, AdjData.rootOp_weyl hD, smul_smul, smul_smul]
    push_cast
    ring_nf
  have h2 := RootOperatorFamily'.D_one_eq F hD (simple τ i • α) k
  rw [simple_smul_eq_sRoot] at h1 h2
  exact smul_left_injective k (rootOp_ne_zero F hD _) (h1.symm.trans h2)

theorem relSign_simple (j : Fin τ.rank) :
    (RootOperatorFamily'.relSign F hD (simpleRoot τ j) : k) = 1 := by
  have h1 := RootOperatorFamily'.D_one_eq F hD (simpleRoot τ j) k
  have h2 : D'.rootOp k (simpleRoot τ j) = infE τ k j := AdjData.rootOp_simple hD j
  rw [F.D_simple, xCoeff_one, h2] at h1
  have hne : infE τ k j ≠ 0 := by
    rw [← h2]
    exact rootOp_ne_zero F hD _
  exact smul_left_injective k hne ((one_smul k (infE τ k j)).trans h1).symm

theorem sign_simple_self (i : Fin τ.rank) : (F.sign i (simpleRoot τ i) : k) = -1 := by
  have hs : simple τ i • simpleRoot τ i = -simpleRoot τ i :=
    Subtype.ext (by rw [coe_smul_root, simple_smul, simpleRoot, reflect_single_self]; rfl)
  have h1 := F.weylElement_mul_eltElement_mul_inv i (simpleRoot τ i) (1 : k)
  rw [hs] at h1
  have h2 : CFSG.LieType.Chevalley.weylElement τ k i * F.eltElement (simpleRoot τ i) 1 *
      (CFSG.LieType.Chevalley.weylElement τ k i)⁻¹ = F.eltElement (-simpleRoot τ i) (-1) := by
    refine Subtype.ext (Units.ext ?_)
    change (weylElt τ k i 1 : Module.End k (RootModule τ k)) * F.elt k (simpleRoot τ i) 1 *
      (((weylElt τ k i 1)⁻¹ : (Module.End k (RootModule τ k))ˣ) :
        Module.End k (RootModule τ k)) = F.elt k (-simpleRoot τ i) (-1)
    rw [F.elt_simple, F.elt_neg_simple, weylElt_mul_xOp_mul_inv]
    simp
  have h3 := h1.symm.trans h2
  rw [← xPar_neg_simple, ← xPar_neg_simple] at h3
  have h4 := xPar_injective (isRoot_neg_single τ i) h3
  rwa [mul_one] at h4

theorem relSign_neg_simple (hself : ∀ j : Fin τ.rank, D'.weylSign j j = -1) (j : Fin τ.rank) :
    (RootOperatorFamily'.relSign F hD (-simpleRoot τ j) : k) = 1 := by
  have h := sign_mul_relSign (F := F) (hD := hD) (k := k) (simpleRoot τ j) j
  have hs : sRoot j (simpleRoot τ j) = -simpleRoot τ j :=
    Subtype.ext (by simp only [sRoot, simpleRoot, reflect_single_self]; rfl)
  have hσ : D'.rootSign (simpleRoot τ j) j = -1 := by
    rw [AdjData.rootSign, (AdjData.pos_eq_simple_iff j).2 rfl]
    exact hself j
  rw [hs] at h
  rw [← h, Int.cast_mul, Int.cast_mul, sign_simple_self, relSign_simple, hσ]
  norm_num

theorem adj_rootOp_bracket_single (hD₀ : D'.Valid) (j : Fin τ.rank) (γ : Root τ)
    (hγ : γ.1 ≠ -Pi.single j 1)
    (h : IsRoot τ (Pi.single j 1 + γ.1)) :
    D'.rootOp k ⟨Pi.single j 1, isRoot_single τ j⟩ * D'.rootOp k γ -
        D'.rootOp k γ * D'.rootOp k ⟨Pi.single j 1, isRoot_single τ j⟩ =
      ((((D'.pairDig (pos γ) j % 8 : ℕ) : ℤ) - 4 : ℤ) : k) •
        D'.rootOp k ⟨Pi.single j 1 + γ.1, h⟩ ∧ D'.pairDig (pos γ) j ≠ 0 := by
  have hT := hD₀.tables
  have hl : pos γ < τ.rootCertificate.roots.length := pos_lt γ
  have hrl : τ.rootCertificate.root (pos γ) = γ.1 := root_pos γ
  have hlj : pos γ ≠ D'.neg j := fun h' => hγ ((AdjData.pos_eq_neg_simple_iff hT j).1 h')
  have hsj : pos (⟨Pi.single j 1, isRoot_single τ j⟩ : Root τ) = j :=
    (AdjData.pos_eq_simple_iff j).2 rfl
  have hlj' : pos γ ≠ j := fun h' => by
    have hγj : γ.1 = Pi.single j 1 := (AdjData.pos_eq_simple_iff j).1 h'
    rw [hγj] at h
    exact not_isRoot_single_add_single j h
  have hu : D'.upI (pos γ) j ≠ 0 := fun hu =>
    AdjData.not_isRoot_of_upI hT hl hu (by rw [hrl, add_comm]; exact h)
  have hP := (AdjData.checkPairs_at hD₀.pairs hl j hlj).1
  have hd : D'.pairDig (pos γ) j ≠ 0 := by
    intro h0
    rw [ite_eq_left h0] at hP
    exact hP.elim hlj' hu
  rw [ite_eq_right hd] at hP
  obtain ⟨hm, hmr⟩ := AdjData.upI_spec hT hl hu
  refine ⟨?_, hd⟩
  rw [AdjData.rootOp, AdjData.rootOp, hsj,
    AdjData.recOp_bracket_simple hT hD₀.simple hD₀.weyl hD₀.pairs hl j hlj, ite_eq_right hd,
    AdjData.rootOp, hP]
  congr 2
  rw [eq_comm, pos_eq_iff hm, hmr, hrl, add_comm]

theorem bracketCoeff_single (j : Fin τ.rank) (γ : Root τ) (hγ : γ.1 ≠ -Pi.single j 1)
    (h : IsRoot τ (Pi.single j 1 + γ.1)) :
    (RootOperatorFamily'.bracketCoeff F hD ⟨Pi.single j 1, isRoot_single τ j⟩ γ : k) =
      ((RootOperatorFamily'.relSign F hD ⟨Pi.single j 1, isRoot_single τ j⟩ *
        RootOperatorFamily'.relSign F hD γ * RootOperatorFamily'.relSign F hD ⟨_, h⟩ *
          (((D'.pairDig (pos γ) j % 8 : ℕ) : ℤ) - 4) : ℤ) : k) := by
  have hb := RootOperatorFamily'.bracket_eq F hD (β := ⟨Pi.single j 1, isRoot_single τ j⟩)
    (γ := γ) hγ h k
  rw [RootOperatorFamily'.D_one_eq F hD _ k, RootOperatorFamily'.D_one_eq F hD γ k,
    RootOperatorFamily'.D_one_eq F hD ⟨_, h⟩ k, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm (RootOperatorFamily'.relSign F hD γ : k), ← smul_sub,
    (adj_rootOp_bracket_single hD j γ hγ h).1, smul_smul, smul_smul] at hb
  have he := smul_left_injective k (rootOp_ne_zero F hD _) hb
  have hs := sign_cast_eq (R := k) (RootOperatorFamily'.relSign_eq F hD ⟨_, h⟩)
  push_cast at he ⊢
  linear_combination (-(RootOperatorFamily'.relSign F hD ⟨_, h⟩ : k)) * he -
    (RootOperatorFamily'.bracketCoeff F hD ⟨Pi.single j 1, isRoot_single τ j⟩ γ : k) * hs

theorem commutator_yPar_single (hτ : NoG2 τ) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (j : Fin τ.rank) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hne : Pi.single j 1 + δ ≠ 0)
    (hr : IsRoot τ (Pi.single j 1 + δ)) (c d : k) :
    ⁅yPar F hD (Pi.single j 1) c, yPar F hD δ d⁆ = yPar F hD (Pi.single j 1 + δ)
      (((((D'.pairDig (pos ⟨δ, hδ⟩) j % 8 : ℕ) : ℤ) - 4 : ℤ) : k) * c * d) := by
  have hj := isRoot_single τ j
  have hne1 : Pi.single j 1 ≠ δ := fun h => by
    rw [← h] at hr
    exact not_isRoot_single_add_single j hr
  have hne2 : Pi.single j 1 ≠ -δ := fun h => hne (by rw [h, neg_add_cancel])
  have hne' : δ ≠ -Pi.single j 1 := fun h0 => hne (by rw [h0, add_neg_cancel])
  have h12 : ¬IsRoot τ (Pi.single j 1 + 2 • δ) := fun h12 => by
    have := eq_one_of_isRoot_nsmul_add_nsmul hpd hj hδ hne (i := 1) (j := 2) one_pos two_pos
      (by rwa [one_smul])
    omega
  have h21 : ¬IsRoot τ (2 • Pi.single j 1 + δ) := fun h21 => by
    have := eq_one_of_isRoot_nsmul_add_nsmul hpd hj hδ hne (i := 2) (j := 1) two_pos one_pos
      (by rwa [one_smul])
    omega
  rw [yPar, yPar, commutator_xPar hD hτ hj hδ hne1 hne2, xPar_of_not_isRoot h12,
    xPar_of_not_isRoot h21, mul_one, mul_one, yPar]
  congr 1
  rw [RootOperatorFamily'.coeff11, bracketCoeff_single j ⟨δ, hδ⟩ hne' hr, relSignOr_of_isRoot hj,
    relSignOr_of_isRoot hδ, relSignOr_of_isRoot hr]
  have e1 := sign_cast_eq (R := k) (RootOperatorFamily'.relSign_eq F hD ⟨Pi.single j 1, hj⟩)
  have e2 := sign_cast_eq (R := k) (RootOperatorFamily'.relSign_eq F hD ⟨δ, hδ⟩)
  push_cast
  linear_combination ((RootOperatorFamily'.relSign F hD ⟨_, hr⟩ : k) *
      (((D'.pairDig (pos ⟨δ, hδ⟩) j : ℤ) % 8 : ℤ) - 4 : k) * c * d *
      (RootOperatorFamily'.relSign F hD ⟨δ, hδ⟩ : k) *
      (RootOperatorFamily'.relSign F hD ⟨δ, hδ⟩ : k)) * e1 +
    ((RootOperatorFamily'.relSign F hD ⟨_, hr⟩ : k) *
      (((D'.pairDig (pos ⟨δ, hδ⟩) j : ℤ) % 8 : ℤ) - 4 : k) * c * d) * e2

end Adjoint

open _root_.Classical in
@[expose] def weylSignOr (D : MinData τ) (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) : ℤ :=
  if h : IsRoot τ γ then minWeylSign D (pos ⟨γ, h⟩) i else 1

theorem weylSignOr_of_isRoot {D : MinData τ} (i : Fin τ.rank) {γ : Fin τ.rank → ℤ}
    (h : IsRoot τ γ) : weylSignOr D i γ = minWeylSign D (pos ⟨γ, h⟩) i := by
  classical
  exact dite_eq_left h

theorem weylSignOr_mul_self {k : Type*} [Field k] (D : MinData τ) (i : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) : (weylSignOr D i γ : k) * (weylSignOr D i γ : k) = 1 := by
  classical
  unfold weylSignOr minWeylSign
  split_ifs <;> norm_num

section Comparison

variable {D : MinData τ} (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
  (F : RootOperatorFamily τ) {D' : AdjData τ} (hD : D'.Valid) (hτ : NoG2 τ)
  (hS : checkSigns D D' = true) (k : Type) [Field k]

include hV in
theorem nm_conj_xm_eq (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k) :
    hV.nm k i * hV.xm k γ c * (hV.nm k i)⁻¹ =
      hV.xm k (reflect τ i γ) ((weylSignOr D i γ : k) * c) := by
  have h := nm_conj_xm_root hV k (pos_lt ⟨γ, hγ⟩) i c
  rw [root_pos] at h
  rw [weylSignOr_of_isRoot i hγ]
  exact h

include hS in
theorem weylElement_conj_yPar (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k) :
    CFSG.LieType.Chevalley.weylElement τ k i * yPar F hD γ c *
        (CFSG.LieType.Chevalley.weylElement τ k i)⁻¹ =
      yPar F hD (reflect τ i γ) ((weylSignOr D i γ : k) * c) := by
  rw [yPar, xPar_of_isRoot hγ, F.weylElement_mul_eltElement_mul_inv, simple_smul_eq_sRoot, yPar,
    xPar_of_isRoot (hγ.reflect i), relSignOr_of_isRoot hγ, relSignOr_of_isRoot (hγ.reflect i),
    weylSignOr_of_isRoot i hγ, ← checkSigns_weyl hS (pos_lt _) i]
  congr 1
  have h : (RootOperatorFamily'.relSign F hD ⟨reflect τ i γ, hγ.reflect i⟩ : k) =
      ((F.sign i ⟨γ, hγ⟩ * RootOperatorFamily'.relSign F hD ⟨γ, hγ⟩ *
        D'.weylSign (pos ⟨γ, hγ⟩) i : ℤ) : k) :=
    (sign_mul_relSign (F := F) (hD := hD) ⟨γ, hγ⟩ i).symm
  have hσ := sign_cast_eq (R := k) (D'.weylSign_eq (pos ⟨γ, hγ⟩) i)
  rw [h]
  push_cast
  linear_combination (-((F.sign i ⟨γ, hγ⟩ : k) *
    (RootOperatorFamily'.relSign F hD ⟨γ, hγ⟩ : k) * c)) * hσ

include hV hpd hD hτ hS in
theorem sameCommutators_simple (j : Fin τ.rank) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hne : Pi.single j 1 + δ ≠ 0) :
    SameCommutators (hV.xm k) (yPar F hD (k := k)) (Pi.single j 1) δ := by
  have hj := isRoot_single τ j
  have hl := pos_lt ⟨δ, hδ⟩
  have hrl : τ.rootCertificate.root (pos ⟨δ, hδ⟩) = δ := root_pos _
  refine ⟨fun hr => ?_, fun hnr => ?_⟩
  · have hne' : δ ≠ -Pi.single j 1 := fun h0 => hne (by rw [h0, add_neg_cancel])
    obtain ⟨-, hd⟩ := adj_rootOp_bracket_single (k := k) hD j ⟨δ, hδ⟩ hne' hr
    have hlj : pos ⟨δ, hδ⟩ ≠ D'.neg j := fun h' =>
      hne' ((AdjData.pos_eq_neg_simple_iff hD.tables j).1 h')
    have hN := checkSigns_pair hS hl j hlj hd
    refine ⟨(minPairSign D (pos ⟨δ, hδ⟩) j : k), fun c d => ?_, fun c d => ?_⟩
    · have h := commutator_xm_single hV k hl j (by rwa [hrl]) (by rwa [hrl]) c d
      rwa [hrl] at h
    · rw [commutator_yPar_single hτ hpd j hδ hne hr, hN]
  · refine ⟨fun c d => ((hV.commutator_xm k hj hδ hne).2 hnr) c d, fun c d => ?_⟩
    rw [yPar, yPar, commutatorElement_eq_one_iff_commute]
    exact commute_xPar hD hτ hj hδ hne hnr _ _

include hV hpd hD hτ hS in
theorem sameCommutators_xm_yPar {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α + β ≠ 0) : SameCommutators (hV.xm k) (yPar F hD (k := k)) α β :=
  sameCommutators_of_simple (n := hV.nm k) (m := CFSG.LieType.Chevalley.weylElement τ k)
    (s := fun i γ => (weylSignOr D i γ : k)) (fun i γ _ => weylSignOr_mul_self D i γ)
    (fun i _ hγ c => nm_conj_xm_eq hV k i hγ c)
    (fun i _ hγ c => weylElement_conj_yPar F hD hS k i hγ c)
    (fun j _ hδ hne => sameCommutators_simple hV hpd F hD hτ hS k j hδ hne) hα hβ hne

include hV hpd hD hτ hS in
theorem commutatorFormula_yPar {Φ : Steinberg.RootSystem (Fin τ.rank)}
    (hΦ : Φ.roots = {γ | IsRoot τ γ}) {O : CommOrder Φ}
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (hV.xm k) O C) : CommutatorFormula (yPar F hD (k := k)) O C :=
  commutatorFormula_of_sameCommutators hΦ
    (fun _ hα _ hβ hne hr => list_eq_singleton_of_isRoot hpd hΦ O hα hβ hne hr)
    (fun _ hα _ hβ hne hr => list_eq_nil_of_not_isRoot hpd hΦ O hα hβ hne hr)
    (fun _ hγ => hV.xm_injective k hγ)
    (fun _ _ hα hβ hne => sameCommutators_xm_yPar hV hpd F hD hτ hS k hα hβ hne) hC

@[expose] def isogeny {Φ : Steinberg.RootSystem (Fin τ.rank)} (hΦ : Φ.roots = {γ | IsRoot τ γ})
    (hpres : PresentationB (Φ := Φ) (hV.xm k)) : ↥(hV.minGroup k) →* ↥(adjointGroup τ k) :=
  liftOfPresentationB hpres (commOrder hpd Φ hΦ) (hV.commutatorFormula_commC k hpd Φ hΦ _)
    (fun γ _ c d => yPar_add γ c d)
    (commutatorFormula_yPar hV hpd F hD hτ hS k hΦ (hV.commutatorFormula_commC k hpd Φ hΦ _))

variable {Φ : Steinberg.RootSystem (Fin τ.rank)} (hΦ : Φ.roots = {γ | IsRoot τ γ})
  (hpres : PresentationB (Φ := Φ) (hV.xm k))

theorem isogeny_xm {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k) :
    isogeny hV hpd F hD hτ hS k hΦ hpres (hV.xm k γ c) = yPar F hD γ c :=
  liftOfPresentationB_apply _ _ _ _ _ (by rw [hΦ]; exact hγ) c

theorem isogeny_xm_single (j : Fin τ.rank) (c : k) :
    isogeny hV hpd F hD hτ hS k hΦ hpres (hV.xm k (Pi.single j 1) c) =
      F.eltElement (simpleRoot τ j) c := by
  rw [isogeny_xm hV hpd F hD hτ hS k hΦ hpres (isRoot_single τ j), yPar,
    relSignOr_of_isRoot (isRoot_single τ j),
    show (RootOperatorFamily'.relSign F hD ⟨Pi.single j 1, isRoot_single τ j⟩ : k) = 1 from
      relSign_simple j, one_mul, xPar_simple]

theorem isogeny_xm_neg_single (j : Fin τ.rank) (c : k) :
    isogeny hV hpd F hD hτ hS k hΦ hpres (hV.xm k (-Pi.single j 1) c) =
      F.eltElement (-simpleRoot τ j) c := by
  rw [isogeny_xm hV hpd F hD hτ hS k hΦ hpres (isRoot_neg_single τ j), yPar,
    relSignOr_of_isRoot (isRoot_neg_single τ j),
    show (RootOperatorFamily'.relSign F hD ⟨-Pi.single j 1, isRoot_neg_single τ j⟩ : k) = 1 from
      relSign_neg_simple (fun j => checkSigns_self hS j) j, one_mul, xPar_neg_simple]

omit hV hpd hτ hS in
include hΦ in
theorem closure_yPar_eq_top :
    Subgroup.closure {g | ∃ γ ∈ Φ.roots, ∃ c : k, yPar F hD γ c = g} = ⊤ := by
  rw [eq_top_iff, ← iSup_rootGroup_eq_top F k]
  refine iSup₂_le fun γ hγ => ?_
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
  refine Subgroup.subset_closure ⟨γ, by rw [hΦ]; exact hγ, (relSignOr F hD γ : k) * c, ?_⟩
  rw [yPar, ← mul_assoc, relSignOr_mul_self, one_mul]

theorem isogeny_surjective : Function.Surjective (isogeny hV hpd F hD hτ hS k hΦ hpres) :=
  liftOfPresentationB_surjective _ _ _ _ _ (closure_yPar_eq_top F hD k hΦ)

theorem isogeny_xm_single_one_ne_one (j : Fin τ.rank) :
    isogeny hV hpd F hD hτ hS k hΦ hpres (hV.xm k (Pi.single j 1) 1) ≠ 1 := by
  rw [isogeny_xm_single, ← xPar_simple, ← xPar_zero (F := F) (Pi.single j 1)]
  exact fun h => one_ne_zero (xPar_injective (isRoot_single τ j) h)

theorem isogeny_ne_one : ∃ g, isogeny hV hpd F hD hτ hS k hΦ hpres g ≠ 1 := by
  have h : 0 < τ.rank := by cases τ <;> decide
  exact ⟨_, isogeny_xm_single_one_ne_one hV hpd F hD hτ hS k hΦ hpres ⟨0, h⟩⟩

end Comparison

end CFSG.LieType.Steinberg.Isogeny
