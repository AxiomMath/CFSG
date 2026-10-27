module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests
public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Two
public import Certificates.Certificate15066
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIXiO2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6Wit
import CFSG.Monster.B.Classical.E6AdjointGroup
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
import CFSG.LargeExtraspecial.S14C12E6Coord
import CFSG.LieType.Chevalley.C2E6StandardLevi
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.Walter.JRFacts
import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.B.Classical.E6Adjoint

theorem twistedE6TwoFactor_check : factorCheck = true :=
  Certificates.certificate15066.1

theorem twistedE6TwoConj_check : conjCheck = true :=
  Certificates.certificate15066.2

@[expose] def rhoCheck : Bool :=
  (List.range 72).all fun k => decide (rhoIdx.getD k 0 < 72) &&
    List.ofFn (e6Certificate.root (rhoIdx.getD k 0)) ==
      List.ofFn (permLattice TwistTag.E6.perm (e6Certificate.root k))

theorem rhoCheck_eq_true : rhoCheck = true := by decide

theorem rhoIdx_lt {k : ℕ} (hk : k < 72) : rhoIdx.getD k 0 < 72 := by
  have h := rhoCheck_eq_true
  simp only [rhoCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h k hk).1

theorem root_rhoIdx {k : ℕ} (hk : k < 72) :
    e6Certificate.root (rhoIdx.getD k 0) = permLattice TwistTag.E6.perm (e6Certificate.root k) := by
  have h := rhoCheck_eq_true
  simp only [rhoCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact RootCertificate.eq_of_ofFn_beq (h k hk).2

theorem root_seventy : e6Certificate.root 70 = e6HighestRoot :=
  RootCertificate.eq_of_ofFn_beq (by decide)

@[expose] noncomputable def glMatT
    : ModGL TwistTag.E6.tag C2E6Overlap.K →* Matrix (Fin 78) (Fin 78) C2E6Overlap.K :=
  glMat

theorem glMatT_injective
    : Function.Injective glMatT :=
  glMat_injective

theorem eq_of_glMatT
    {g : ModGL TwistTag.E6.tag C2E6Overlap.K} {P : Native.Mat} (hg : glMatT g = toMat P)
    (h : Native.eqM P Native.one = true) : g = 1 :=
  glMatT_injective (by rw [hg, toMat_eq_of_eqM h, toMat_one, map_one])

theorem glMatT_getD
    {arr : Array (ModGL TwistTag.E6.tag C2E6Overlap.K)} {arr' : Array Native.Mat}
    (h : arr.map glMatT = arr'.map toMat) (i : ℕ) :
    glMatT (arr.getD i 1) = toMat (arr'.getD i Native.one) := by
  have e1 := getD_map glMatT arr i 1
  have e2 := getD_map toMat arr' i Native.one
  rw [← e1, map_one, h, ← toMat_one, e2]

@[expose] noncomputable def genY
    (k : ℕ) : ModGL TwistTag.E6.tag C2E6Overlap.K :=
  if rhoIdx.getD k 0 = k then pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root k) 1
  else pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root k) 1 *
    pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root (rhoIdx.getD k 0)) 1

@[expose, irreducible] noncomputable def gensY
    : Array (ModGL TwistTag.E6.tag C2E6Overlap.K) :=
  (List.range 72).toArray.map genY

theorem glMat_pinnedX_root
    {k : ℕ} (hk : k < 72) (c0 c1 : Bool) :
    glMat (pinnedX Tag.E6 C2E6Overlap.K (e6Certificate.root k) (ofBits c0 c1)) =
      toMat (Native.rootMat bracketCodes formBits (k + 6) c0 c1) := by
  have hr := isRoot_certRoot hk
  have hl : lab ⟨k + 6, by omega⟩ = Sum.inr ⟨e6Certificate.root k, hr⟩ := by
    rw [lab_of_ge (by simp)]
    simp
  rw [glMat_apply, pinnedX_eq hr, CFSG.Monster.B.Classical.E6Adjoint.rootVec_eq_single hr, ← hl]
  exact matOf_rootOp ⟨k + 6, by omega⟩ c0 c1

theorem glMatT_pinnedX_root
    {k : ℕ} (hk : k < 72) (c0 c1 : Bool) :
    glMatT (pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root k) (ofBits c0 c1)) =
      toMat (Native.rootMat bracketCodes formBits (k + 6) c0 c1) :=
  glMat_pinnedX_root hk c0 c1

theorem glMatT_genY
    {k : ℕ} (hk : k < 72) : glMatT (genY k) = toMat (nGen k) := by
  have h1 : (1 : C2E6Overlap.K) = ofBits true false := ofBits_true_false.symm
  unfold genY nGen
  split_ifs with h
  · rw [h1]
    exact glMatT_pinnedX_root hk true false
  · rw [map_mul, h1, toMat_mul]
    exact congrArg₂ (· * ·) (glMatT_pinnedX_root hk true false)
      (glMatT_pinnedX_root (rhoIdx_lt hk) true false)

theorem gensY_map_glMatT
    : gensY.map glMatT = nGens.map toMat := by
  unfold gensY
  simp only [nGens, List.map_toArray, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => glMatT_genY (List.mem_range.1 hk)

theorem diagramMap_comm_orbit
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hr : IsRoot TwistTag.E6.tag α) :
    diagramMap TwistTag.E6 C2E6Overlap.K * (pinnedX TwistTag.E6.tag C2E6Overlap.K α 1 *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (permLattice TwistTag.E6.perm α) 1) =
      pinnedX TwistTag.E6.tag C2E6Overlap.K α 1 *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (permLattice TwistTag.E6.perm α) 1 *
          diagramMap TwistTag.E6 C2E6Overlap.K := by
  have h2 : (2 : C2E6Overlap.K) = 0 := CharP.cast_eq_zero C2E6Overlap.K 2
  have hPX := mul_inv_eq_iff_eq_mul.1
    (E6GraphRadical.diagramMap_conj_pinnedX_of_two h2 hr (1 : C2E6Overlap.K))
  have hPY := mul_inv_eq_iff_eq_mul.1 (E6GraphRadical.diagramMap_conj_pinnedX_of_two h2
    (hr.permLattice TwistTag.E6.cartan_perm) (1 : C2E6Overlap.K))
  rw [SeitzReduction.permLattice_twistedE6_perm_perm] at hPY
  have hc := SeitzReduction.commute_pinnedX_permLattice_twistedE6 hr (1 : C2E6Overlap.K) 1
  rw [← mul_assoc, hPX, mul_assoc, hPY, ← mul_assoc, ← hc.eq]

theorem diagramMap_comm_fixed
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hr : IsRoot TwistTag.E6.tag α)
    (hρ : permLattice TwistTag.E6.perm α = α) :
    diagramMap TwistTag.E6 C2E6Overlap.K * pinnedX TwistTag.E6.tag C2E6Overlap.K α 1 =
      pinnedX TwistTag.E6.tag C2E6Overlap.K α 1 * diagramMap TwistTag.E6 C2E6Overlap.K := by
  have e := E6GraphRadical.diagramMap_conj_pinnedX_of_two (CharP.cast_eq_zero C2E6Overlap.K 2)
    hr (1 : C2E6Overlap.K)
  rw [hρ] at e
  exact mul_inv_eq_iff_eq_mul.1 e

theorem genY_mem
    {k : ℕ} (hk : k < 72) :
    genY k ∈ graphFixedRootGroup TwistTag.E6 C2E6Overlap.K barHom ⊓
      Subgroup.centralizer {diagramMap TwistTag.E6 C2E6Overlap.K} := by
  have hr : IsRoot TwistTag.E6.tag (e6Certificate.root k) := isRoot_certRoot hk
  have hρ := root_rhoIdx hk
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · unfold genY
    split_ifs with h
    · rw [h] at hρ
      exact SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed barHom hr hρ.symm (map_one _)
    · have := SeitzReduction.twistedE6PairX_mem_graphFixedRootGroup (σ := barHom)
        (fun x => bar_bar x) hr 1
      simp only [SeitzReduction.twistedE6PairX, map_one, ← hρ] at this
      exact this
  · unfold genY
    split_ifs with h
    · rw [h] at hρ
      exact (diagramMap_comm_fixed hr hρ.symm).symm
    · have := diagramMap_comm_orbit hr
      rw [← hρ] at this
      exact this.symm

@[expose, irreducible] noncomputable def valsY
    : Array (ModGL TwistTag.E6.tag C2E6Overlap.K) :=
  slpRunG gensY progY

theorem valsY_map_glMatT
    : valsY.map glMatT = nVals.map toMat := by
  unfold valsY
  rw [nVals, map_slpRunG, gensY_map_glMatT, toMat_slpRun]

theorem glMatT_valsY
    (i : ℕ) : glMatT (valsY.getD i 1) = toMat (nVals.getD i Native.one) :=
  glMatT_getD valsY_map_glMatT i

theorem valsY_mem
    (i : ℕ) : valsY.getD i 1 ∈ graphFixedRootGroup TwistTag.E6 C2E6Overlap.K barHom ⊓
      Subgroup.centralizer {diagramMap TwistTag.E6 C2E6Overlap.K} := by
  unfold valsY
  refine getD_mem _ (slpRunG_mem _ (fun x hx => ?_) progY) i
  unfold gensY at hx
  obtain ⟨k, hk, rfl⟩ := Array.mem_map.1 hx
  exact genY_mem (List.mem_range.1 (List.mem_toArray.1 hk))

theorem glMatT_theta
    : glMatT (pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1) = toMat nT := by
  have h70 : rhoIdx.getD 70 0 = 70 := by decide
  rw [nT, ← glMatT_genY (by norm_num : 70 < 72)]
  simp only [genY, h70, ↓reduceIte, root_seventy]

theorem valsY_of_oddOK
    {i m : ℕ} (h : oddOK i m = true) :
    Odd m ∧ valsY.getD i 1 ^ m = 1 ∧
      valsY.getD i 1 * pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1 =
        pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1 * valsY.getD i 1 := by
  simp only [oddOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hm, hp⟩, hc⟩ := h
  refine ⟨Nat.odd_iff.2 hm, eq_of_glMatT (by rw [map_pow, glMatT_valsY, toMat_pow]) hp,
    glMatT_injective ?_⟩
  rw [map_mul, map_mul, glMatT_valsY, glMatT_theta, ← toMat_mul, ← toMat_mul,
    toMat_eq_of_eqM hc]

theorem glMatT_lineProdG_valsY
    (line : List ℕ) : glMatT (lineProdG valsY line) = toMat (Native.lineProd nVals line) := by
  rw [map_lineProdG, valsY_map_glMatT, toMat_lineProd]

theorem glMatT_lineProdG_gensY
    (line : List ℕ) : glMatT (lineProdG gensY line) = toMat (Native.lineProd nGens line) := by
  rw [map_lineProdG, gensY_map_glMatT, toMat_lineProd]

theorem toMat_foldl_mul {ι : Type*} (f : ι → Native.Mat) (l : List ι) (acc : Native.Mat) :
    toMat (l.foldl (fun acc q => Native.mul acc (f q)) acc) =
      toMat acc * (l.map (toMat ∘ f)).prod := by
  induction l generalizing acc with
  | nil => simp
  | cons q l ih =>
    rw [List.foldl_cons, ih, toMat_mul, List.map_cons, List.prod_cons, mul_assoc]
    rfl

theorem lineProdG_mem_of {G : Type*} [Group G] (H : Subgroup G) {vals : Array G}
    {line : List ℕ} (h : ∀ i ∈ line, vals.getD i 1 ∈ H) : lineProdG vals line ∈ H := by
  have key : ∀ acc ∈ H, line.foldl (fun acc i => acc * vals.getD i 1) acc ∈ H := by
    induction line with
    | nil => exact fun acc hacc => hacc
    | cons i line ih =>
      intro acc hacc
      rw [List.foldl_cons]
      exact (ih fun j hj => h j (List.mem_cons_of_mem _ hj)) _
        (H.mul_mem hacc (h i List.mem_cons_self))
  exact key 1 H.one_mem

theorem factorData_lt : ∀ p ∈ factorData, p.1 < 72 := by decide

theorem genY_eq_of_mem_factorData
    {k : ℕ} {l : List (ℕ × ℕ)} (hp : (k, l) ∈ factorData) :
    (∀ q ∈ l, oddOK q.1 q.2 = true) ∧ genY k = lineProdG valsY (l.map Prod.fst) := by
  have h := twistedE6TwoFactor_check
  simp only [factorCheck, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h _ hp
  refine ⟨h1, glMatT_injective ?_⟩
  rw [glMatT_genY (factorData_lt _ hp), glMatT_lineProdG_valsY, toMat_eq_of_eqM h2]

theorem theta_eq_of_mem_conjData
    {a : List ℕ} {l : List (ℕ × ℕ)} (hp : (a, l) ∈ conjData) :
    (∀ q ∈ l, oddOK q.1 q.2 = true) ∧
      pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1 =
        (l.map fun q => valsY.getD q.1 1 * lineProdG gensY a * (valsY.getD q.1 1)⁻¹).prod := by
  have h := twistedE6TwoConj_check
  simp only [conjCheck, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h _ hp
  refine ⟨h1, glMatT_injective ?_⟩
  rw [glMatT_theta, toMat_eq_of_eqM h2, conjProd, toMat_foldl_mul, toMat_one, one_mul,
    map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hm, hpow, -⟩ := valsY_of_oddOK (h1 q hq)
  have hinv : (valsY.getD q.1 1)⁻¹ = valsY.getD q.1 1 ^ (q.2 - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hm.pos]
    exact hpow
  simp only [Function.comp_apply, map_mul, hinv, map_pow, glMatT_valsY, glMatT_lineProdG_gensY,
    toMat_mul, toMat_pow]

theorem fixCheck_eq_true : ((List.range 72).all fun k => (rhoIdx.getD k 0 == k) ==
    (List.ofFn (permLattice TwistTag.E6.perm (e6Certificate.root k)) ==
      List.ofFn (e6Certificate.root k))) = true := by decide

theorem rhoIdx_eq_iff {k : ℕ} (hk : k < 72) :
    rhoIdx.getD k 0 = k ↔
      permLattice TwistTag.E6.perm (e6Certificate.root k) = e6Certificate.root k := by
  have h := fixCheck_eq_true
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h k hk
  constructor
  · intro e
    rw [e, beq_self_eq_true, Bool.true_beq] at h'
    exact RootCertificate.eq_of_ofFn_beq h'
  · intro e
    have hb : (List.ofFn (permLattice TwistTag.E6.perm (e6Certificate.root k)) ==
        List.ofFn (e6Certificate.root k)) = true := by
      rw [e]
      exact beq_self_eq_true _
    rw [hb] at h'
    simpa using h'

end CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

namespace CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel

theorem eq_zero_or_eq_one_of_card {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    c = 0 ∨ c = 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  rcases eq_or_ne c 0 with h | h
  · exact Or.inl h
  · right
    have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
    have : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.1 hu).1
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 c h) 1)

theorem eq_one_or_eq_orbitElt
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α)
    {u : ModGL TwistTag.E6.tag F}
    (hu : u ∈ rootSpan TwistTag.E6.tag F (TwistTag.E6.diagramOrbit α : Set _) ⊓
      twistedFixedGroup TwistTag.E6 F (RingHom.id F)) :
    u = 1 ∨ (permLattice TwistTag.E6.perm α = α ∧ u = pinnedX TwistTag.E6.tag F α 1) ∨
      (permLattice TwistTag.E6.perm α ≠ α ∧ u = pinnedX TwistTag.E6.tag F α 1 *
        pinnedX TwistTag.E6.tag F (permLattice TwistTag.E6.perm α) 1) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨huS, huΓ⟩ := Subgroup.mem_inf.1 hu
  have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 F (RingHom.id F)).1 huΓ).2
  by_cases hρ : permLattice TwistTag.E6.perm α = α
  · rw [diagramOrbit_eq_singleton_of_fixed hρ, Finset.coe_singleton, rootSpan_singleton] at huS
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 huS
    rcases eq_zero_or_eq_one_of_card hF c with rfl | rfl
    · exact Or.inl (pinnedX_zero _ _ _)
    · exact Or.inr (Or.inl ⟨hρ, rfl⟩)
  · have hβ : IsRoot TwistTag.E6.tag (permLattice TwistTag.E6.perm α) :=
      hα.permLattice TwistTag.E6.cartan_perm
    have hβh : height (permLattice TwistTag.E6.perm α) = height α := height_permLattice _ _
    have hmemO : ∀ γ, γ ∈ [α, permLattice TwistTag.E6.perm α] ↔
        γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) := by
      intro γ
      simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_coe]
      constructor
      · rintro (rfl | rfl)
        · exact TwistTag.E6.self_mem_diagramOrbit _
        · exact TwistTag.E6.permLattice_mem_diagramOrbit (TwistTag.E6.self_mem_diagramOrbit _)
      · intro hγ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
        rw [Finset.mem_range, show TwistTag.E6.order = 2 from rfl] at hj
        interval_cases j
        · exact Or.inl rfl
        · exact Or.inr (by rw [pow_one])
    have hS : ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        IsRoot TwistTag.E6.tag γ ∧ 0 < height γ := fun γ hγ =>
      ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit hα hγ,
        by rw [TwistTag.E6.height_of_mem_diagramOrbit hγ]; exact hαp⟩
    have hcl : ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
        ∀ δ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)), ∀ a b : ℕ,
          1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • γ + b • δ) →
            a • γ + b • δ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) :=
      fun γ hγ δ hδ a b ha hb hr =>
        absurd hr (TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα hγ hδ ha hb)
    have hnd : [α, permLattice TwistTag.E6.perm α].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        and_true]
      exact ⟨Ne.symm hρ, not_false⟩
    obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F hS hcl hnd hmemO huS
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
    subst hc
    rw [map_mul, E6GraphRadical.twistHom_pinnedX_of_two h2 _ hα,
      E6GraphRadical.twistHom_pinnedX_of_two h2 _ hβ, RingHom.id_apply, RingHom.id_apply,
      SeitzReduction.permLattice_twistedE6_perm_perm,
      ← (SeitzReduction.commute_pinnedX_permLattice_twistedE6 hα _ _).eq] at hfix
    have hX : ∀ d : F, pinnedX TwistTag.E6.tag F α d ∈ heightSeries TwistTag.E6.tag F (height α) :=
      fun d => pinnedX_mem_heightSeries_height ⟨hα, hαp⟩ d
    have hY : ∀ d : F, pinnedX TwistTag.E6.tag F (permLattice TwistTag.E6.perm α) d ∈
        heightSeries TwistTag.E6.tag F (height α) := fun d =>
      pinnedX_mem_rootSpan (S := {γ | IsRoot TwistTag.E6.tag γ ∧ 0 < height γ ∧
        height α ≤ height γ}) ⟨hβ, by rw [hβh]; exact hαp, hβh.ge⟩ d
    have hc' := congrArg (rootCoord ⟨hα, hαp⟩) hfix
    rw [rootCoord_mul _ (hX _) (hY _), rootCoord_mul _ (hX _) (hY _), rootCoord_self,
      rootCoord_self, rootCoord_pinnedX_of_ne _ ⟨hβ, by rw [hβh]; exact hαp⟩ hβh.ge hρ,
      rootCoord_pinnedX_of_ne _ ⟨hβ, by rw [hβh]; exact hαp⟩ hβh.ge hρ, add_zero,
      add_zero] at hc'
    rcases eq_zero_or_eq_one_of_card hF (c α) with h0 | h1
    · left
      rw [hc', h0, pinnedX_zero, pinnedX_zero, mul_one]
    · right
      right
      exact ⟨hρ, by rw [hc', h1]⟩

theorem baseChange_mem_of_genY_mem
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra k C2E6Overlap.K] (hk : Nat.card k = 2)
    {M : Submonoid (ModGL TwistTag.E6.tag C2E6Overlap.K)}
    (hM : ∀ j < 72, 0 < height (e6Certificate.root j) →
      (genY j : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈ M)
    {s : ModGL TwistTag.E6.tag k}
    (hs : s ∈ graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)) :
    baseChangeGL (algebraMap k C2E6Overlap.K) s ∈ M := by
  obtain ⟨hposS, hposρ, hposcl⟩ := SeitzReduction.posRoots_twistedE6_facts
  obtain ⟨n, O, hO, hrange⟩ := exists_ordering_posOrbits TwistTag.E6
  have hbij := bijOn_prod_graphFixed (K := k) (σ := RingHom.id k) Function.surjective_id hposS
    hposρ hposcl O hO hrange
  obtain ⟨w, -, hw⟩ := hbij.surjOn hs
  rw [← hw, map_list_prod]
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
  have hOj : O j ∈ TwistTag.E6.diagramRootOrbits ∧ (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆
      {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := by
    have h : O j ∈ Set.range O := Set.mem_range_self j
    rw [hrange] at h
    exact h
  obtain ⟨α, hα, hαO⟩ := hOj.1
  have hαp : 0 < height α :=
    (hOj.2 (by rw [← hαO]; exact TwistTag.E6.self_mem_diagramOrbit α)).2
  have hwj : (w j : ModGL TwistTag.E6.tag k) ∈ rootSpan TwistTag.E6.tag k
      (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.E6 k (RingHom.id k) := by
    rw [hαO]
    exact (w j).2
  obtain ⟨kα, hkα, hrk⟩ := RootCertificate.exists_root_eq e6Certificate_check hα
  rw [CFSG.Monster.B.Classical.E6Adjoint.e6Certificate_length] at hkα
  have hg := hM kα hkα (by rw [hrk]; exact hαp)
  rcases eq_one_or_eq_orbitElt hk hα hαp hwj with h1 | ⟨hρ, h1⟩ | ⟨hρ, h1⟩
  · rw [h1, map_one]
    exact M.one_mem
  · have hfix : rhoIdx.getD kα 0 = kα := (rhoIdx_eq_iff hkα).2 (by rw [hrk]; exact hρ)
    have e : genY kα = pinnedX TwistTag.E6.tag C2E6Overlap.K α 1 := by
      simp only [genY, hfix, ↓reduceIte, hrk]
    rw [h1, baseChangeGL_pinnedX, map_one, ← e]
    exact hg
  · have hne : rhoIdx.getD kα 0 ≠ kα := fun h => hρ (by rw [← hrk]; exact (rhoIdx_eq_iff hkα).1 h)
    have e : genY kα = pinnedX TwistTag.E6.tag C2E6Overlap.K α 1 *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (permLattice TwistTag.E6.perm α) 1 := by
      simp only [genY, hne, ↓reduceIte, root_rhoIdx hkα, hrk]
    rw [h1, map_mul, baseChangeGL_pinnedX, baseChangeGL_pinnedX, map_one, ← e]
    exact hg

theorem exists_baseChange_mem_of_tests
    {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra k C2E6Overlap.K]
    {C : Subgroup (ModGL TwistTag.E6.tag C2E6Overlap.K)}
    (hCa : C ≤ adjointGroup TwistTag.E6.tag C2E6Overlap.K)
    (hι : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
      (baseChangeGL (algebraMap k C2E6Overlap.K)) ≤ C)
    (hJ : ∀ g ∈ C, diagramMap TwistTag.E6 C2E6Overlap.K * g *
        (diagramMap TwistTag.E6 C2E6Overlap.K)⁻¹ = g →
      g ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k C2E6Overlap.K)))
    {ξ : MulAut C}
    (hξ : ∀ g : C, (ξ g : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1 *
        (diagramMap TwistTag.E6 C2E6Overlap.K * g * (diagramMap TwistTag.E6 C2E6Overlap.K)⁻¹) *
          (pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1)⁻¹)
    {E₁ : Subgroup C} (hne : E₁ ≠ ⊥) (h2 : ∀ a ∈ E₁, a ^ 2 = 1) (hfix : ∀ a ∈ E₁, ξ a = a)
    (hn : ∀ s ∈ graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k), ∀ c : C,
      (c : ModGL TwistTag.E6.tag C2E6Overlap.K) = baseChangeGL (algebraMap k C2E6Overlap.K) s →
        ∀ a ∈ E₁, c * a * c⁻¹ ∈ E₁) :
    ∃ a₀ ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k), a₀ ≠ 1 ∧
      a₀ ∈ heightSeries TwistTag.E6.tag k 8 ∧
        ∃ a ∈ E₁, (a : ModGL TwistTag.E6.tag C2E6Overlap.K) =
          baseChangeGL (algebraMap k C2E6Overlap.K) a₀ := by
  have hK2 : ringChar C2E6Overlap.K = 2 := ringChar.eq C2E6Overlap.K 2
  have hinj := baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap k C2E6Overlap.K)
  have hE₁ι : ∀ a ∈ E₁, ∃ g ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      baseChangeGL (algebraMap k C2E6Overlap.K) g = a := by
    intro a ha
    have h := hξ a
    rw [hfix a ha] at h
    exact Subgroup.mem_map.1
      (hJ _ a.2 (E6SecondGraphFixed.diagramMap_conj_eq_of_conj hK2 (hCa a.2) h.symm))
  obtain ⟨a₀, ha₀, ha₀1, ha₀U, hT⟩ := exists_commute_tests_of_le
    (E₂ := (E₁.map C.subtype).comap (baseChangeGL (algebraMap k C2E6Overlap.K)))
    (fun g hg => by
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hg)
      obtain ⟨g', hg', hg'a⟩ := hE₁ι a ha
      rwa [hinj (hg'a.trans hag)] at hg')
    (fun hbot => hne (by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨g, -, hga⟩ := hE₁ι a ha
      have hg : g ∈ (E₁.map C.subtype).comap (baseChangeGL (algebraMap k C2E6Overlap.K)) :=
        Subgroup.mem_comap.2 (hga ▸ Subgroup.mem_map_of_mem _ ha)
      rw [hbot, Subgroup.mem_bot] at hg
      rw [hg, map_one] at hga
      exact Subgroup.mem_bot.2 (Subtype.ext hga.symm)))
    (fun g hg => by
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hg)
      apply hinj
      rw [map_pow, map_one, ← hag, ← map_pow, h2 a ha, map_one])
    (fun s hs g hg => by
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hg)
      have hsC : baseChangeGL (algebraMap k C2E6Overlap.K) s ∈ C :=
        hι (Subgroup.mem_map_of_mem _ hs.2)
      refine Subgroup.mem_comap.2 (Subgroup.mem_map.2
        ⟨_, hn s hs ⟨_, hsC⟩ rfl a ha, ?_⟩)
      rw [map_mul, map_mul, map_inv, hag, map_mul, map_mul, map_inv]
      rfl)
  obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 ha₀)
  have hU8 := mem_heightSeries_eight_of_commute ha₀U hT
  have hΓ : a₀ ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) := by
    obtain ⟨g', hg', hg'a⟩ := hE₁ι a ha
    rwa [hinj (hg'a.trans hag)] at hg'
  exact ⟨a₀, hΓ, ha₀1, hU8, a, ha, hag⟩

abbrev rt (j : ℕ) : Fin TwistTag.E6.tag.rank → ℤ := e6Certificate.root j

theorem high_roots : ∀ j < 72, height (e6Certificate.root j) < 8 ∨ j = 61 ∨ j = 62 ∨ j = 66 ∨
    j = 68 ∨ j = 70 := by decide

theorem height_root_61 : height (rt 61) = 8 := by decide
theorem height_root_62 : height (rt 62) = 8 := by decide
theorem height_root_66 : height (rt 66) = 9 := by decide
theorem height_root_68 : height (rt 68) = 10 := by decide
theorem height_root_70 : height (rt 70) = 11 := by decide

theorem root_61_ne_62 : rt 62 ≠ rt 61 := fun h => by
  have e := congrArg List.ofFn h
  revert e
  decide

theorem eq_root_of_eight_le_height
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (h8 : 8 ≤ height γ) :
    γ = rt 61 ∨ γ = rt 62 ∨ γ = rt 66 ∨ γ = rt 68 ∨ γ = rt 70 := by
  obtain ⟨j, hj, rfl⟩ := RootCertificate.exists_root_eq e6Certificate_check hγ
  rw [CFSG.Monster.B.Classical.E6Adjoint.e6Certificate_length] at hj
  rcases high_roots j hj with h | rfl | rfl | rfl | rfl | rfl
  · exact absurd h8 (not_le.2 h)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

section Peel

variable {F : Type} [Field F]

theorem strip_one
    [Finite F] {h h' : ℤ} (hh : h + 1 = h') {z : ModGL TwistTag.E6.tag F}
    (hz : z ∈ heightSeries TwistTag.E6.tag F h)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ ∧ 0 < height γ)
    (hγh : height γ = h)
    (honly : ∀ β, IsRoot TwistTag.E6.tag β ∧ 0 < height β → height β = h → β = γ) :
    pinnedX TwistTag.E6.tag F γ (-rootCoord hγ z) * z ∈ heightSeries TwistTag.E6.tag F h' := by
  subst hγh hh
  refine CFSG.LargeExtraspecial.S14.TwoE6.mem_heightSeries_succ
    (mul_mem (pinnedX_mem_heightSeries_height hγ _) hz) fun β hβ hβh => ?_
  obtain rfl := honly β hβ hβh
  rw [rootCoord_mul hβ (pinnedX_mem_heightSeries_height hγ _) hz, rootCoord_self, neg_add_cancel]

theorem strip_two
    [Finite F] {h h' : ℤ} (hh : h + 1 = h') {z : ModGL TwistTag.E6.tag F}
    (hz : z ∈ heightSeries TwistTag.E6.tag F h)
    {γ₁ γ₂ : Fin TwistTag.E6.tag.rank → ℤ} (hγ₁ : IsRoot TwistTag.E6.tag γ₁ ∧ 0 < height γ₁)
    (hγ₂ : IsRoot TwistTag.E6.tag γ₂ ∧ 0 < height γ₂) (h₁ : height γ₁ = h) (h₂ : height γ₂ = h)
    (hne : γ₂ ≠ γ₁)
    (honly : ∀ β, IsRoot TwistTag.E6.tag β ∧ 0 < height β → height β = h → β = γ₁ ∨ β = γ₂) :
    pinnedX TwistTag.E6.tag F γ₂ (-rootCoord hγ₂ z) *
        (pinnedX TwistTag.E6.tag F γ₁ (-rootCoord hγ₁ z) * z) ∈
      heightSeries TwistTag.E6.tag F h' := by
  subst h₁ hh
  have hX₁ := pinnedX_mem_heightSeries_height (K := F) hγ₁ (-rootCoord hγ₁ z)
  have hX₂ : pinnedX TwistTag.E6.tag F γ₂ (-rootCoord hγ₂ z) ∈
      heightSeries TwistTag.E6.tag F (height γ₁) := by
    rw [← h₂]
    exact pinnedX_mem_heightSeries_height hγ₂ _
  refine CFSG.LargeExtraspecial.S14.TwoE6.mem_heightSeries_succ (mul_mem hX₂ (mul_mem hX₁ hz))
    fun β hβ hβh => ?_
  rcases honly β hβ hβh with rfl | rfl
  · rw [rootCoord_mul hβ hX₂ (mul_mem hX₁ hz), rootCoord_mul hβ hX₁ hz,
      rootCoord_pinnedX_of_ne hβ hγ₂ h₂.ge hne, rootCoord_self, zero_add, neg_add_cancel]
  · have hz' : z ∈ heightSeries TwistTag.E6.tag F (height β) := by rw [h₂]; exact hz
    have hX₁' : pinnedX TwistTag.E6.tag F γ₁ (-rootCoord hγ₁ z) ∈
        heightSeries TwistTag.E6.tag F (height β) := by rw [h₂]; exact hX₁
    have hX₂' : pinnedX TwistTag.E6.tag F β (-rootCoord hγ₂ z) ∈
        heightSeries TwistTag.E6.tag F (height β) := pinnedX_mem_heightSeries_height hβ _
    rw [rootCoord_mul hβ hX₂' (mul_mem hX₁' hz'), rootCoord_mul hβ hX₁' hz',
      rootCoord_pinnedX_of_ne hβ hγ₁ h₂.le (Ne.symm hne), rootCoord_self, zero_add,
      neg_add_cancel]

theorem heightSeries_twelve'
    : heightSeries TwistTag.E6.tag F 12 = ⊥ :=
  iSup₂_eq_bot.2 fun _ hα => absurd (height_le_eleven hα.1) (by linarith [hα.2.2])

theorem eq_pinnedX_mul_of_eq
    {γ : Fin TwistTag.E6.tag.rank → ℤ} {c : F} {a b : ModGL TwistTag.E6.tag F}
    (h : a = pinnedX TwistTag.E6.tag F γ (-c) * b) : b = pinnedX TwistTag.E6.tag F γ c * a := by
  rw [h, ← mul_assoc, ← pinnedX_add, add_neg_cancel, pinnedX_zero, one_mul]

theorem eq_prod_of_mem_heightSeries_eight
    [Finite F] {z : ModGL TwistTag.E6.tag F} (hz : z ∈ heightSeries TwistTag.E6.tag F 8) :
    ∃ c₁ c₂ c₃ c₄ c₅ : F, z = pinnedX TwistTag.E6.tag F (rt 61) c₁ *
      pinnedX TwistTag.E6.tag F (rt 62) c₂ *
      pinnedX TwistTag.E6.tag F (rt 66) c₃ *
      pinnedX TwistTag.E6.tag F (rt 68) c₄ *
      pinnedX TwistTag.E6.tag F (rt 70) c₅ := by
  have hr : ∀ j < 72, IsRoot TwistTag.E6.tag (rt j) := fun j hj =>
    CFSG.Monster.B.Classical.E6Adjoint.isRoot_certRoot hj
  have h61 : IsRoot TwistTag.E6.tag (rt 61) ∧ 0 < height (rt 61) :=
    ⟨hr 61 (by norm_num), by rw [height_root_61]; norm_num⟩
  have h62 : IsRoot TwistTag.E6.tag (rt 62) ∧ 0 < height (rt 62) :=
    ⟨hr 62 (by norm_num), by rw [height_root_62]; norm_num⟩
  have h66 : IsRoot TwistTag.E6.tag (rt 66) ∧ 0 < height (rt 66) :=
    ⟨hr 66 (by norm_num), by rw [height_root_66]; norm_num⟩
  have h68 : IsRoot TwistTag.E6.tag (rt 68) ∧ 0 < height (rt 68) :=
    ⟨hr 68 (by norm_num), by rw [height_root_68]; norm_num⟩
  have h70 : IsRoot TwistTag.E6.tag (rt 70) ∧ 0 < height (rt 70) :=
    ⟨hr 70 (by norm_num), by rw [height_root_70]; norm_num⟩
  have key : ∀ β, IsRoot TwistTag.E6.tag β → ∀ h : ℤ, 8 ≤ h → height β = h →
      β = rt 61 ∨ β = rt 62 ∨ β = rt 66 ∨
        β = rt 68 ∨ β = rt 70 := fun β hβ h h8 hh =>
    eq_root_of_eight_le_height hβ (hh ▸ h8)
  have hz₁ := strip_two (h' := 9) (by norm_num) hz h61 h62 height_root_61 height_root_62
    root_61_ne_62 fun β hβ hβh => by
      rcases key β hβ.1 8 le_rfl hβh with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rw [height_root_66] at hβh; norm_num at hβh
      · rw [height_root_68] at hβh; norm_num at hβh
      · rw [height_root_70] at hβh; norm_num at hβh
  generalize hz₁def : pinnedX TwistTag.E6.tag F (rt 62) (-rootCoord h62 z) *
    (pinnedX TwistTag.E6.tag F (rt 61) (-rootCoord h61 z) * z) = z₁ at hz₁
  have hz₂ := strip_one (h' := 10) (by norm_num) hz₁ h66 height_root_66 fun β hβ hβh => by
    rcases key β hβ.1 9 (by norm_num) hβh with rfl | rfl | rfl | rfl | rfl
    · rw [height_root_61] at hβh; norm_num at hβh
    · rw [height_root_62] at hβh; norm_num at hβh
    · rfl
    · rw [height_root_68] at hβh; norm_num at hβh
    · rw [height_root_70] at hβh; norm_num at hβh
  generalize hz₂def : pinnedX TwistTag.E6.tag F (rt 66) (-rootCoord h66 z₁) * z₁ = z₂ at hz₂
  have hz₃ := strip_one (h' := 11) (by norm_num) hz₂ h68 height_root_68 fun β hβ hβh => by
    rcases key β hβ.1 10 (by norm_num) hβh with rfl | rfl | rfl | rfl | rfl
    · rw [height_root_61] at hβh; norm_num at hβh
    · rw [height_root_62] at hβh; norm_num at hβh
    · rw [height_root_66] at hβh; norm_num at hβh
    · rfl
    · rw [height_root_70] at hβh; norm_num at hβh
  generalize hz₃def : pinnedX TwistTag.E6.tag F (rt 68) (-rootCoord h68 z₂) * z₂ = z₃ at hz₃
  have hz₄ := strip_one (h' := 12) (by norm_num) hz₃ h70 height_root_70 fun β hβ hβh => by
    rcases key β hβ.1 11 (by norm_num) hβh with rfl | rfl | rfl | rfl | rfl
    · rw [height_root_61] at hβh; norm_num at hβh
    · rw [height_root_62] at hβh; norm_num at hβh
    · rw [height_root_66] at hβh; norm_num at hβh
    · rw [height_root_68] at hβh; norm_num at hβh
    · rfl
  rw [heightSeries_twelve', Subgroup.mem_bot] at hz₄
  have e₃ : z₃ = pinnedX TwistTag.E6.tag F (rt 70) (rootCoord h70 z₃) := by
    have e := eq_inv_of_mul_eq_one_right hz₄
    rwa [pinnedX_neg, neg_neg] at e
  have e₂ := eq_pinnedX_mul_of_eq hz₃def.symm
  have e₁ := eq_pinnedX_mul_of_eq hz₂def.symm
  have e₀ := eq_pinnedX_mul_of_eq (eq_pinnedX_mul_of_eq hz₁def.symm).symm
  refine ⟨rootCoord h61 z, rootCoord h62 z, rootCoord h66 z₁, rootCoord h68 z₂,
    rootCoord h70 z₃, ?_⟩
  conv_lhs => rw [e₀, e₁, e₂, e₃]
  simp only [mul_assoc]

theorem rootCoord_sixtyOne
    [Finite F] (h61 : IsRoot TwistTag.E6.tag (rt 61) ∧ 0 < height (rt 61))
    {β₁ β₂ : Fin TwistTag.E6.tag.rank → ℤ} (hβ : (β₁ = rt 61 ∧ β₂ = rt 62) ∨
      (β₁ = rt 62 ∧ β₂ = rt 61)) (d₁ d₂ d₃ d₄ d₅ : F) :
    rootCoord h61 (pinnedX TwistTag.E6.tag F β₁ d₁ * pinnedX TwistTag.E6.tag F β₂ d₂ *
      pinnedX TwistTag.E6.tag F (rt 66) d₃ * pinnedX TwistTag.E6.tag F (rt 68) d₄ *
      pinnedX TwistTag.E6.tag F (rt 70) d₅) = if β₁ = rt 61 then d₁ else d₂ := by
  have hr : ∀ j < 72, IsRoot TwistTag.E6.tag (rt j) := fun j hj =>
    CFSG.Monster.B.Classical.E6Adjoint.isRoot_certRoot hj
  have hU : ∀ j < 72, 8 ≤ height (rt j) → ∀ d : F,
      pinnedX TwistTag.E6.tag F (rt j) d ∈ heightSeries TwistTag.E6.tag F (height (rt 61)) :=
    fun j hj h8 d => by
      rw [height_root_61]
      exact pinnedX_mem_rootSpan (S := {γ | IsRoot TwistTag.E6.tag γ ∧ 0 < height γ ∧
        8 ≤ height γ}) ⟨hr j hj, by omega, h8⟩ d
  have hz : ∀ j < 72, 8 < height (rt j) → ∀ d : F,
      rootCoord h61 (pinnedX TwistTag.E6.tag F (rt j) d) = 0 := fun j hj h8 d =>
    rootCoord_pinnedX_of_ne h61 ⟨hr j hj, by omega⟩ (by rw [height_root_61]; omega)
      (fun e => by rw [e, height_root_61] at h8; omega) d
  have h62 : rootCoord h61 (pinnedX TwistTag.E6.tag F (rt 62) d₁) = 0 ∧
      rootCoord h61 (pinnedX TwistTag.E6.tag F (rt 62) d₂) = 0 :=
    ⟨rootCoord_pinnedX_of_ne h61 ⟨hr 62 (by norm_num), by rw [height_root_62]; norm_num⟩
      (by rw [height_root_61, height_root_62]) root_61_ne_62 d₁,
     rootCoord_pinnedX_of_ne h61 ⟨hr 62 (by norm_num), by rw [height_root_62]; norm_num⟩
      (by rw [height_root_61, height_root_62]) root_61_ne_62 d₂⟩
  have hβ₁ : 8 ≤ height β₁ := by
    rcases hβ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [height_root_61]
    · rw [height_root_62]
  have hβ₂ : 8 ≤ height β₂ := by
    rcases hβ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [height_root_62]
    · rw [height_root_61]
  have hB : ∀ β, (β = rt 61 ∨ β = rt 62) → ∀ d : F,
      pinnedX TwistTag.E6.tag F β d ∈ heightSeries TwistTag.E6.tag F (height (rt 61)) := by
    rintro β (rfl | rfl) d
    · exact hU 61 (by norm_num) (by rw [height_root_61]) d
    · exact hU 62 (by norm_num) (by rw [height_root_62]) d
  have hb₁ : β₁ = rt 61 ∨ β₁ = rt 62 := by
    rcases hβ with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hb₂ : β₂ = rt 61 ∨ β₂ = rt 62 := by
    rcases hβ with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have m66 := hU 66 (by norm_num) (by rw [height_root_66]; norm_num) d₃
  have m68 := hU 68 (by norm_num) (by rw [height_root_68]; norm_num) d₄
  have m70 := hU 70 (by norm_num) (by rw [height_root_70]; norm_num) d₅
  rw [rootCoord_mul h61 (mul_mem (mul_mem (mul_mem (hB _ hb₁ _) (hB _ hb₂ _)) m66) m68) m70,
    rootCoord_mul h61 (mul_mem (mul_mem (hB _ hb₁ _) (hB _ hb₂ _)) m66) m68,
    rootCoord_mul h61 (mul_mem (hB _ hb₁ _) (hB _ hb₂ _)) m66,
    rootCoord_mul h61 (hB _ hb₁ _) (hB _ hb₂ _),
    hz 66 (by norm_num) (by rw [height_root_66]; norm_num),
    hz 68 (by norm_num) (by rw [height_root_68]; norm_num),
    hz 70 (by norm_num) (by rw [height_root_70]; norm_num)]
  rcases hβ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [rootCoord_self, h62.2, ↓reduceIte]
    ring
  · simp only [rootCoord_self, h62.1, root_61_ne_62, ↓reduceIte]
    ring

end Peel

@[expose] def bitF (F : Type) [Field F] (b : Bool) : F := if b then 1 else 0

theorem eq_bitF_of_card {F : Type} [Field F] (hF : Nat.card F = 2) (c : F) :
    ∃ b : Bool, c = bitF F b := by
  rcases eq_zero_or_eq_one_of_card hF c with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

theorem map_bitF {F L : Type} [Field F] [Field L] (f : F →+* L) (b : Bool) :
    f (bitF F b) = bitF L b := by
  cases b
  · exact map_zero f
  · exact map_one f

theorem exists_bits_of_mem
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    {z : ModGL TwistTag.E6.tag F}
    (hz : z ∈ heightSeries TwistTag.E6.tag F 8)
    (hfix : twistHom TwistTag.E6 F (RingHom.id F) z = z) :
    ∃ b8 b9 b10 b11 : Bool, z = pinnedX TwistTag.E6.tag F (rt 61) (bitF F b8) *
      pinnedX TwistTag.E6.tag F (rt 62) (bitF F b8) *
      pinnedX TwistTag.E6.tag F (rt 66) (bitF F b9) *
      pinnedX TwistTag.E6.tag F (rt 68) (bitF F b10) *
      pinnedX TwistTag.E6.tag F (rt 70) (bitF F b11) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr : ∀ j < 72, IsRoot TwistTag.E6.tag (rt j) := fun j hj =>
    CFSG.Monster.B.Classical.E6Adjoint.isRoot_certRoot hj
  have h61 : IsRoot TwistTag.E6.tag (rt 61) ∧ 0 < height (rt 61) :=
    ⟨hr 61 (by norm_num), by rw [height_root_61]; norm_num⟩
  have hρ : ∀ j < 72, ∀ j', rhoIdx.getD j 0 = j' →
      permLattice TwistTag.E6.perm (rt j) = rt j' := fun j hj j' e => by
    rw [← e]
    exact (root_rhoIdx hj).symm
  obtain ⟨c₁, c₂, c₃, c₄, c₅, rfl⟩ := eq_prod_of_mem_heightSeries_eight hz
  have e := hfix
  simp only [map_mul, E6GraphRadical.twistHom_pinnedX_of_two h2 _ (hr 61 (by norm_num)),
    E6GraphRadical.twistHom_pinnedX_of_two h2 _ (hr 62 (by norm_num)),
    E6GraphRadical.twistHom_pinnedX_of_two h2 _ (hr 66 (by norm_num)),
    E6GraphRadical.twistHom_pinnedX_of_two h2 _ (hr 68 (by norm_num)),
    E6GraphRadical.twistHom_pinnedX_of_two h2 _ (hr 70 (by norm_num)), RingHom.id_apply,
    hρ 61 (by norm_num) 62 (by decide), hρ 62 (by norm_num) 61 (by decide),
    hρ 66 (by norm_num) 66 (by decide), hρ 68 (by norm_num) 68 (by decide),
    hρ 70 (by norm_num) 70 (by decide)] at e
  have hc := congrArg (rootCoord h61) e
  rw [rootCoord_sixtyOne h61 (Or.inr ⟨rfl, rfl⟩), rootCoord_sixtyOne h61 (Or.inl ⟨rfl, rfl⟩)]
    at hc
  simp only [root_61_ne_62, ↓reduceIte] at hc
  obtain ⟨b8, rfl⟩ := eq_bitF_of_card hF c₁
  obtain ⟨b9, rfl⟩ := eq_bitF_of_card hF c₃
  obtain ⟨b10, rfl⟩ := eq_bitF_of_card hF c₄
  obtain ⟨b11, rfl⟩ := eq_bitF_of_card hF c₅
  exact ⟨b8, b9, b10, b11, by rw [hc]⟩

@[expose] def aLineOf (b8 b9 b10 b11 : Bool) : List ℕ :=
  (if b8 then [61] else []) ++ (if b9 then [66] else []) ++ (if b10 then [68] else []) ++
    (if b11 then [70] else [])

theorem aLineOf_mem : ∀ b8 b9 b10 b11 : Bool, (b8 || b9 || b10) = true →
    aLineOf b8 b9 b10 b11 ∈ conjData.map Prod.fst := by decide

theorem gensY_getD
    {k : ℕ} (hk : k < 72) : gensY.getD k 1 = genY k := by
  rw [gensY, Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range hk]
  rfl

theorem prod_bitF_eq_lineProdG
    (b8 b9 b10 b11 : Bool) :
    pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 61) (bitF _ b8) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 62) (bitF _ b8) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 66) (bitF _ b9) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 68) (bitF _ b10) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 70) (bitF _ b11) =
      lineProdG gensY (aLineOf b8 b9 b10 b11) := by
  have g61 : gensY.getD 61 1 = pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 61) 1 *
      pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 62) 1 := by
    rw [gensY_getD (by norm_num)]
    have h : rhoIdx.getD 61 0 = 62 := by decide
    simp only [genY, h]
    rfl
  have g66 : gensY.getD 66 1 = pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 66) 1 := by
    rw [gensY_getD (by norm_num)]
    have h : rhoIdx.getD 66 0 = 66 := by decide
    simp only [genY, h, ↓reduceIte]
  have g68 : gensY.getD 68 1 = pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 68) 1 := by
    rw [gensY_getD (by norm_num)]
    have h : rhoIdx.getD 68 0 = 68 := by decide
    simp only [genY, h, ↓reduceIte]
  have g70 : gensY.getD 70 1 = pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 70) 1 := by
    rw [gensY_getD (by norm_num)]
    have h : rhoIdx.getD 70 0 = 70 := by decide
    simp only [genY, h, ↓reduceIte]
  cases b8 <;> cases b9 <;> cases b10 <;> cases b11 <;>
    simp only [aLineOf, bitF, lineProdG, Bool.false_eq_true, ↓reduceIte, List.nil_append,
      List.cons_append, List.foldl_cons, List.foldl_nil, pinnedX_zero, one_mul, mul_one, g61,
      g66, g68, g70, mul_assoc]

end CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoHypIIY

section PullbackO2

variable {C : Type*} [Group C]

theorem exists_pullback_of_witnessO2 (hZ : center C = ⊥) {ξ : MulAut C}
    {E₀ : Subgroup (MulAut C)} (hab : IsElemAbelian 2 E₀) (hne : E₀ ≠ ⊥)
    (hX : E₀ ≤ OuterAutomorphisms.inner C) (hξ : E₀ ≤ centralizer {ξ})
    (hN : oUpperTwo (OuterAutomorphisms.inner C ⊓ centralizer {ξ}) ≤
      normalizer (E₀ : Set (MulAut C)))
    (hcl : ∀ x ∈ E₀, x ≠ 1 → ∀ w ∈ oUpperTwo (OuterAutomorphisms.inner C ⊓ centralizer {x}),
      w * ξ * w⁻¹ * ξ⁻¹ ∈ E₀) :
    ∃ E₁ : Subgroup C, E₁ ≠ ⊥ ∧ (∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) ∧
      (∀ a ∈ E₁, a ^ 2 = 1) ∧ (∀ a ∈ E₁, ξ a = a) ∧
      (∀ c ∈ closure {c : C | ξ c = c ∧ Odd (orderOf c)}, ∀ a ∈ E₁, c * a * c⁻¹ ∈ E₁) ∧
      ∀ x ∈ E₁, x ≠ 1 → ∀ w ∈ closure {c : C | c * x = x * c ∧ Odd (orderOf c)},
        w * (ξ w)⁻¹ ∈ E₁ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  have hcξ : ∀ g : C, MulAut.conj g ∈ centralizer {ξ} ↔ ξ g = g := by
    intro g
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply hinj
      rw [conj_apply_eq_mul_conj_mul_inv, ← h, mul_inv_cancel_right]
    · intro h
      have e := conj_apply_eq_mul_conj_mul_inv ξ g
      rw [h] at e
      have := congrArg (· * ξ) e
      simpa [mul_assoc] using this
  have hodd : ∀ g : C, Odd (orderOf g) → Odd (orderOf (MulAut.conj g)) := fun g hg =>
    hg.of_dvd_nat (orderOf_map_dvd _ g)
  have hO2ξ : ∀ c ∈ closure {c : C | ξ c = c ∧ Odd (orderOf c)},
      MulAut.conj c ∈ oUpperTwo (OuterAutomorphisms.inner C ⊓ centralizer {ξ}) := by
    intro c hc
    refine (closure_le ((oUpperTwo (OuterAutomorphisms.inner C ⊓ centralizer {ξ})).comap
      (MulAut.conj : C →* MulAut C))).2 ?_ hc
    rintro g ⟨hgξ, hgo⟩
    exact subset_closure ⟨⟨⟨g, rfl⟩, (hcξ g).2 hgξ⟩, hodd g hgo⟩
  have hO2x : ∀ x : C, ∀ w ∈ closure {c : C | c * x = x * c ∧ Odd (orderOf c)},
      MulAut.conj w ∈
        oUpperTwo (OuterAutomorphisms.inner C ⊓ centralizer {MulAut.conj x}) := by
    intro x w hw
    refine (closure_le ((oUpperTwo (OuterAutomorphisms.inner C ⊓
      centralizer {MulAut.conj x})).comap (MulAut.conj : C →* MulAut C))).2 ?_ hw
    rintro g ⟨hgx, hgo⟩
    exact subset_closure ⟨⟨⟨g, rfl⟩, mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, hgx])⟩, hodd g hgo⟩
  refine ⟨E₀.comap (MulAut.conj : C →* MulAut C), fun hbot => hne ?_, fun a ha b hb => hinj ?_,
    fun a ha => hinj ?_, fun a ha => (hcξ a).1 (hξ ha), fun c hc a ha => ?_,
    fun x hx hx1 w hw => ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, rfl⟩ := hX hy
    have : g ∈ E₀.comap (MulAut.conj : C →* MulAut C) := hy
    rw [hbot, mem_bot] at this
    rw [this, map_one]
    exact one_mem _
  · rw [map_mul, map_mul]
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  · rw [map_pow, hab.2 _ ha, map_one]
  · have hcN := hN (hO2ξ c hc)
    change MulAut.conj (c * a * c⁻¹) ∈ E₀
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hcN _).mp ha
  · have hx1' : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (h.trans (map_one _).symm))
    have h := hcl _ hx hx1' _ (hO2x x w hw)
    change MulAut.conj (w * (ξ w)⁻¹) ∈ E₀
    have e : MulAut.conj (w * (ξ w)⁻¹) =
        MulAut.conj w * ξ * (MulAut.conj w)⁻¹ * ξ⁻¹ := by
      rw [map_mul, map_inv, conj_apply_eq_mul_conj_mul_inv]
      group
    rw [e]
    exact h

@[expose] def normalizingMonoid {G : Type*} [Group G] (C : Subgroup G) (E : Subgroup C) :
    Submonoid G where
  carrier := {g | ∃ hg : g ∈ C, ∀ a ∈ E, (⟨g, hg⟩ : C) * a * (⟨g, hg⟩ : C)⁻¹ ∈ E}
  mul_mem' := by
    rintro g h ⟨hg, hgE⟩ ⟨hh, hhE⟩
    refine ⟨C.mul_mem hg hh, fun a ha => ?_⟩
    have e : (⟨g * h, C.mul_mem hg hh⟩ : C) * a * (⟨g * h, C.mul_mem hg hh⟩ : C)⁻¹ =
        (⟨g, hg⟩ : C) * ((⟨h, hh⟩ : C) * a * (⟨h, hh⟩ : C)⁻¹) * (⟨g, hg⟩ : C)⁻¹ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hgE _ (hhE a ha)
  one_mem' := ⟨C.one_mem, fun a ha => by
    have e : (⟨1, C.one_mem⟩ : C) * a * (⟨1, C.one_mem⟩ : C)⁻¹ = a := by
      refine Subtype.ext ?_
      simp
    rw [e]
    exact ha⟩

theorem mem_normalizingMonoid {G : Type*} [Group G] {C : Subgroup G} {E : Subgroup C} {g : G} :
    g ∈ normalizingMonoid C E ↔
      ∃ hg : g ∈ C, ∀ a ∈ E, (⟨g, hg⟩ : C) * a * (⟨g, hg⟩ : C)⁻¹ ∈ E :=
  Iff.rfl

theorem mem_normalizingMonoid_of_mem_map {G : Type*} [Group G] {C : Subgroup G}
    {E : Subgroup C} {S : Set C} (hS : ∀ c ∈ closure S, ∀ a ∈ E, c * a * c⁻¹ ∈ E) {g : G}
    (hg : g ∈ (closure S).map C.subtype) : g ∈ normalizingMonoid C E := by
  obtain ⟨c, hc, rfl⟩ := hg
  exact ⟨c.2, fun a ha => hS c hc a ha⟩

end PullbackO2

section TwistedE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

local notation "C₀" => graphFixedRootGroup TwistTag.E6 C2E6Overlap.K C2E6Overlap.barHom

local notation "tθ" => pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1

local notation "Pd" => diagramMap TwistTag.E6 C2E6Overlap.K

theorem genY_seventy
    : (genY 70 : ModGL TwistTag.E6.tag C2E6Overlap.K) = tθ := by
  have h : rhoIdx.getD 70 0 = 70 := by decide
  simp only [genY, h, ↓reduceIte, root_seventy]

theorem rt_six : rt 6 = -e6Alpha false := RootCertificate.eq_of_ofFn_beq (by decide)

theorem rt_sixteen : rt 16 = -e6Alpha true := RootCertificate.eq_of_ofFn_beq (by decide)

theorem genY_six
    : (genY 6 : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      pinnedX TwistTag.E6.tag C2E6Overlap.K (-e6Alpha false) 1 *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (-e6Alpha true) 1 := by
  have h : rhoIdx.getD 6 0 = 16 := by decide
  simp only [genY, h]
  rw [← rt_six, ← rt_sixteen]
  rfl

theorem factor_keys : ∀ j < 72, 0 < height (rt j) → j ≠ 70 → j ∈ factorData.map Prod.fst := by
  decide

theorem six_mem_factor_keys : 6 ∈ factorData.map Prod.fst := by decide

theorem valsY_mem_oddFixed
    {ξ : MulAut C₀}
    (hξ : ∀ g : C₀, (ξ g : ModGL TwistTag.E6.tag C2E6Overlap.K) = tθ * (Pd * g * Pd⁻¹) * tθ⁻¹)
    {i m : ℕ} (h : oddOK i m = true) :
    ∃ hv : valsY.getD i 1 ∈ C₀, ξ ⟨_, hv⟩ = ⟨_, hv⟩ ∧ Odd (orderOf (⟨_, hv⟩ : C₀)) := by
  obtain ⟨hm, hpow, hcomm⟩ := valsY_of_oddOK h
  have hmem := valsY_mem i
  have hP : Pd * valsY.getD i 1 = valsY.getD i 1 * Pd :=
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hmem).2).symm
  have hT : tθ * valsY.getD i 1 = valsY.getD i 1 * tθ := hcomm.symm
  have hpow' : valsY.getD i 1 ^ m = 1 := hpow
  have hv : valsY.getD i 1 ∈ C₀ := (Subgroup.mem_inf.1 hmem).1
  refine ⟨hv, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [hξ]
    change tθ * (Pd * valsY.getD i 1 * Pd⁻¹) * tθ⁻¹ = valsY.getD i 1
    rw [mul_inv_eq_of_eq_mul hP, mul_inv_eq_of_eq_mul hT]
  · refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one (Subtype.ext ?_))
    rw [SubmonoidClass.coe_pow]
    exact hpow'

theorem lineProdG_valsY_mem
    {ξ : MulAut C₀}
    (hξ : ∀ g : C₀, (ξ g : ModGL TwistTag.E6.tag C2E6Overlap.K) = tθ * (Pd * g * Pd⁻¹) * tθ⁻¹)
    {l : List (ℕ × ℕ)} (hl : ∀ q ∈ l, oddOK q.1 q.2 = true) :
    lineProdG valsY (l.map Prod.fst) ∈
      (Subgroup.closure {c : C₀ | ξ c = c ∧ Odd (orderOf c)}).map (Subgroup.subtype C₀) := by
  refine lineProdG_mem_of _ fun i hi => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hv, hfix, hodd⟩ := valsY_mem_oddFixed hξ (hl q hq)
  exact ⟨⟨_, hv⟩, Subgroup.subset_closure ⟨hfix, hodd⟩, rfl⟩

theorem theta_mem_of_bits
    (ht : tθ ∈ C₀) {ξ : MulAut C₀}
    (hξ : ∀ g : C₀, (ξ g : ModGL TwistTag.E6.tag C2E6Overlap.K) = tθ * (Pd * g * Pd⁻¹) * tθ⁻¹)
    {E₁ : Subgroup C₀}
    (hn : ∀ c ∈ Subgroup.closure {c : C₀ | ξ c = c ∧ Odd (orderOf c)}, ∀ a ∈ E₁,
      c * a * c⁻¹ ∈ E₁)
    {a : C₀} (ha : a ∈ E₁) (ha1 : a ≠ 1) (b8 b9 b10 b11 : Bool)
    (hab : (a : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 61) (bitF _ b8) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 62) (bitF _ b8) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 66) (bitF _ b9) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 68) (bitF _ b10) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 70) (bitF _ b11)) :
    (⟨tθ, ht⟩ : C₀) ∈ E₁ := by
  rw [prod_bitF_eq_lineProdG] at hab
  cases h : (b8 || b9 || b10)
  · simp only [Bool.or_eq_false_iff] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    cases b11
    · exact absurd (Subtype.ext (by rw [hab]; rfl)) ha1
    · have e : a = ⟨tθ, ht⟩ := by
        refine Subtype.ext ?_
        rw [hab]
        simp only [aLineOf, Bool.false_eq_true, ↓reduceIte, List.nil_append, lineProdG,
          List.foldl_cons, List.foldl_nil, one_mul, gensY_getD (by norm_num : 70 < 72),
          genY_seventy]
      rw [← e]
      exact ha
  · obtain ⟨⟨a', l⟩, hp, hp1⟩ := List.mem_map.1 (aLineOf_mem b8 b9 b10 b11 h)
    simp only at hp1
    subst hp1
    obtain ⟨hl, hT⟩ := theta_eq_of_mem_conjData hp
    rw [← hab] at hT
    have hprod : (l.map fun q => valsY.getD q.1 1 * (a : ModGL TwistTag.E6.tag C2E6Overlap.K) *
        (valsY.getD q.1 1)⁻¹).prod ∈ E₁.map (Subgroup.subtype C₀) := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hv, hfix, hodd⟩ := valsY_mem_oddFixed hξ (hl q hq)
      exact ⟨_, hn ⟨_, hv⟩ (Subgroup.subset_closure ⟨hfix, hodd⟩) a ha, rfl⟩
    rw [← hT] at hprod
    obtain ⟨c, hc, hcT⟩ := hprod
    have e : c = ⟨tθ, ht⟩ := Subtype.ext hcT
    rw [← e]
    exact hc

theorem secondGraphWitnessO2_twistedE6Two
    (ht : tθ ∈ C₀) (η : MulAut C₀)
    (hη : ∀ h, (η h : ModGL TwistTag.E6.tag C2E6Overlap.K) = Pd * h * Pd⁻¹) :
    SecondGraphWitnessO2 (MulAut.conj (⟨_, ht⟩ : C₀) * η) := by
  intro E₀ hab hne hX hξ₀ hN hcl
  have h2 : (2 : C2E6Overlap.K) = 0 := CharP.cast_eq_zero C2E6Overlap.K 2
  have hK : Nat.card C2E6Overlap.K = (2 ^ 1) ^ 2 := by
    rw [Nat.card_eq_fintype_card, C2E6Overlap.card_K]
    norm_num
  have hσ : ∀ c, C2E6Overlap.barHom c = c ^ 2 ^ 1 := fun c => rfl
  have hZ : Subgroup.center C₀ = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv
  obtain ⟨E₁, hE₁ne, hE₁c, hE₁2, hE₁ξ, hE₁n, hE₁w⟩ :=
    exists_pullback_of_witnessO2 hZ hab hne hX hξ₀ hN hcl
  set ξ := MulAut.conj (⟨_, ht⟩ : C₀) * η with hξdef
  have hξ : ∀ g : C₀, (ξ g : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      tθ * (Pd * g * Pd⁻¹) * tθ⁻¹ := fun g => by
    rw [hξdef, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη]
  have hCa : C₀ ≤ adjointGroup TwistTag.E6.tag C2E6Overlap.K := fun g hg =>
    (graphFixedRootGroup_le _ _ _ hg).1
  have hK2 : ringChar C2E6Overlap.K = 2 := ringChar.eq C2E6Overlap.K 2
  have hE₁t : ∀ a ∈ E₁, (⟨tθ, ht⟩ : C₀) * a * (⟨tθ, ht⟩ : C₀)⁻¹ = a := by
    intro a ha
    have h := hξ a
    rw [hE₁ξ a ha] at h
    have hP := E6SecondGraphFixed.diagramMap_conj_eq_of_conj hK2 (hCa a.2) h.symm
    rw [hP] at h
    exact Subtype.ext h.symm
  have hM : ∀ j < 72, 0 < height (rt j) → genY j ∈ normalizingMonoid C₀ E₁ := by
    intro j hj hpos
    by_cases h70 : j = 70
    · subst h70
      rw [genY_seventy]
      exact ⟨ht, fun a ha => by rw [hE₁t a ha]; exact ha⟩
    · obtain ⟨⟨j', l⟩, hp, hp1⟩ := List.mem_map.1 (factor_keys j hj hpos h70)
      simp only at hp1
      subst hp1
      obtain ⟨hl, hg⟩ := genY_eq_of_mem_factorData hp
      rw [hg]
      exact mem_normalizingMonoid_of_mem_map hE₁n (lineProdG_valsY_mem hξ hl)
  have hk := CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two le_rfl hK hσ
  have : CharP (RingHom.eqLocusField C2E6Overlap.barHom (RingHom.id C2E6Overlap.K)) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hk
  have hk2 : Nat.card (RingHom.eqLocusField C2E6Overlap.barHom (RingHom.id C2E6Overlap.K)) = 2 :=
    by rw [hk]; norm_num
  obtain ⟨-, ⟨η₀, hη₀, -, hJC, hfixJ, -⟩, -⟩ := even_E6_twisted_E6_canonical_graph_fixed_subgroup
    1 le_rfl (RingHom.eqLocusField C2E6Overlap.barHom (RingHom.id C2E6Overlap.K))
    C2E6Overlap.K hk hK C2E6Overlap.barHom hσ
  have hJ : ∀ g ∈ C₀, Pd * g * Pd⁻¹ = g →
      g ∈ (twistedFixedGroup TwistTag.E6
        (RingHom.eqLocusField C2E6Overlap.barHom (RingHom.id C2E6Overlap.K))
        (RingHom.id _)).map (baseChangeGL (algebraMap _ C2E6Overlap.K)) := fun g hg hP =>
    (hfixJ ⟨g, hg⟩).1 (Subtype.ext (by rw [hη₀]; exact hP))
  obtain ⟨a₀, ha₀Γ, ha₀1, ha₀8, a, haE, hag⟩ :=
    exists_baseChange_mem_of_tests hCa hJC hJ hξ hE₁ne hE₁2 hE₁ξ fun s hs c hc b hb => by
      obtain ⟨hg, hgN⟩ := baseChange_mem_of_genY_mem hk2 hM hs
      have e : c = ⟨_, hg⟩ := Subtype.ext hc
      rw [e]
      exact hgN b hb
  obtain ⟨b8, b9, b10, b11, hb⟩ := exists_bits_of_mem hk2 ha₀8
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 ha₀Γ).2
  have ha1 : a ≠ 1 := fun h1 => ha₀1 (baseChangeGL_injective (τ := TwistTag.E6.tag)
    (algebraMap _ C2E6Overlap.K) (by rw [← hag, h1, map_one]; rfl))
  have hab : (a : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 61) (bitF _ b8) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 62) (bitF _ b8) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 66) (bitF _ b9) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 68) (bitF _ b10) *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (rt 70) (bitF _ b11) := by
    rw [hag, hb]
    simp only [map_mul, baseChangeGL_pinnedX, map_bitF]
  have htE := theta_mem_of_bits ht hξ hE₁n haE ha1 b8 b9 b10 b11 hab
  have ht1 : (⟨tθ, ht⟩ : C₀) ≠ 1 := fun h1 => one_ne_zero (pinnedX_injective _ _ _
    ((congrArg Subtype.val h1).trans (pinnedX_zero _ _ _).symm))
  obtain ⟨d, hd⟩ := exists_ne_fixed le_rfl hK hσ
  have hd' : d + C2E6Overlap.barHom d ≠ 0 := fun h =>
    hd ((eq_neg_of_add_eq_zero_right h).trans (CharTwo.neg_eq d))
  have hδ : IsRoot TwistTag.E6.tag (e6Alpha false) := isRoot_e6Alpha false
  have hρδ : permLattice TwistTag.E6.perm (e6Alpha false) ≠ e6Alpha false := by
    rw [permLattice_e6Alpha.1]
    decide
  have hδr : ¬IsRoot TwistTag.E6.tag (e6Alpha false + e6HighestRoot) := by
    rw [add_comm]
    exact not_isRoot_add_e6Alpha isRoot_e6HighestRoot (by rw [height_e6HighestRoot]; norm_num)
      false
  obtain ⟨b, hbC, hbr, hbδ, -, hbρ⟩ := SeitzReduction.exists_twistedE6TorusTwo
    (σ := C2E6Std.barEquiv) (by rw [hK]; norm_num) (fun c => rfl) hδ hρδ
  have hσσ : ∀ x, C2E6Std.barEquiv.toRingHom (C2E6Std.barEquiv.toRingHom x) = x := fun x =>
    C2E6Overlap.bar_bar x
  have hw := SeitzReduction.twistedE6PairX_mem_closure_odd (f := 1) le_rfl hK hσσ
    (t := ⟨tθ, ht⟩) rfl hδ hρδ hδr hbC hbr hbδ hbρ d
  have hwC : SeitzReduction.twistedE6PairX C2E6Overlap.barHom (e6Alpha false) d ∈ C₀ :=
    SeitzReduction.twistedE6PairX_mem_graphFixedRootGroup (σ := C2E6Overlap.barHom)
      (fun x => C2E6Overlap.bar_bar x) hδ d
  have hw₀ : (⟨_, hwC⟩ : C₀) ∈ Subgroup.closure {c : C₀ | c * ⟨tθ, ht⟩ = ⟨tθ, ht⟩ * c ∧
      Odd (orderOf c)} := hw
  have hz := hE₁w _ htE ht1 _ hw₀
  obtain ⟨⟨j', l⟩, hp, hp1⟩ := List.mem_map.1 six_mem_factor_keys
  simp only at hp1
  subst hp1
  obtain ⟨hl, hg⟩ := genY_eq_of_mem_factorData hp
  obtain ⟨y, hy, hy'⟩ := lineProdG_valsY_mem hξ hl
  rw [← hg, genY_six] at hy'
  have hyz := hE₁n y hy _ hz
  have hcomm := congrArg Subtype.val (hE₁c _ hz _ hyz)
  have hw' : SeitzReduction.twistedE6PairX C2E6Overlap.barHom (e6Alpha false) d =
      pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Alpha false) d *
        pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Alpha true) (C2E6Overlap.barHom d) := by
    simp only [SeitzReduction.twistedE6PairX, permLattice_e6Alpha.1]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcomm
  rw [hξ] at hcomm
  simp only [hw'] at hcomm
  rw [conj_theta_diagramMap_pair h2, e6Alpha_pair_mul_inv] at hcomm
  simp only [Subgroup.coe_subtype] at hy'
  rw [hy'] at hcomm
  exact e6Alpha_pair_not_commute hd' hcomm

end TwistedE6Two

end CFSG.ComponentClassification.RankTwoExcHypII
