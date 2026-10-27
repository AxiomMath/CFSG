module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoWit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairE6Tests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairReduce
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Classes
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesCheck
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Chevalley.C2E6StandardLevi
public import Certificates.Certificate3951
public import Certificates.Certificate15074
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Rigidity
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Two
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassList
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
import CFSG.LargeExtraspecial.S14C12E6Center
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.LieType.Chevalley.TwistedE6FieldTwoCyclicKernel
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
import CFSG.LieType.Chevalley.ProductInjectivity
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityRadical
public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LieType.Chevalley.C2E6A5ExteriorCubeModel
import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.Sporadic.M23.M23Group
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.PairE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
  CFSG.SeitzReduction CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

local notation "C₀" => graphFixedRootGroup TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv.toRingHom

theorem twistedE6TwoPairU_check : pairCheckU = true :=
  Certificates.certificate15074.1

theorem twistedE6TwoPairV_check : pairCheckV = true :=
  Certificates.certificate15074.2

theorem bar_omega : barEquiv.toRingHom (ofBits false true) = ofBits true true := by
  rw [barEquiv_toRingHom, barHom_apply, bar, ← ofBits_sq]
  rfl

@[expose] noncomputable def genW
    (k : ℕ) : ModGL TwistTag.E6.tag C2E6Overlap.K :=
  if rhoIdx.getD k 0 = k then pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root k) 1
  else pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root k) (ofBits false true) *
    pinnedX TwistTag.E6.tag C2E6Overlap.K (e6Certificate.root (rhoIdx.getD k 0)) (ofBits true true)

theorem glMatT_genW
    {k : ℕ} (hk : k < 72) : glMatT (genW k) = toMat (nGenW k) := by
  have h1 : (1 : C2E6Overlap.K) = ofBits true false := ofBits_true_false.symm
  unfold genW nGenW
  split_ifs with h
  · rw [h1]
    exact glMatT_pinnedX_root hk true false
  · rw [map_mul, toMat_mul]
    exact congrArg₂ (· * ·) (glMatT_pinnedX_root hk false true)
      (glMatT_pinnedX_root (rhoIdx_lt hk) true true)

theorem genW_mem
    {k : ℕ} (hk : k < 72) : genW k ∈ C₀ := by
  have hr : IsRoot TwistTag.E6.tag (e6Certificate.root k) := isRoot_certRoot hk
  have hρ := root_rhoIdx hk
  unfold genW
  split_ifs with h
  · rw [h] at hρ
    exact SeitzReduction.pinnedX_mem_graphFixedRootGroup_of_fixed _ hr hρ.symm (map_one _)
  · have := SeitzReduction.twistedE6PairX_mem_graphFixedRootGroup (σ := barEquiv.toRingHom)
      (fun x => bar_bar x) hr (ofBits false true)
    simp only [SeitzReduction.twistedE6PairX, bar_omega, ← hρ] at this
    exact this

@[expose, irreducible] noncomputable def gensP
    : Array (ModGL TwistTag.E6.tag C2E6Overlap.K) :=
  gensY ++ (List.range 72).toArray.map genW

theorem gensP_map_glMatT
    : gensP.map glMatT = nGensP.map toMat := by
  unfold gensP
  rw [Array.map_append, gensY_map_glMatT, nGensP, Array.map_append]
  congr 1
  simp only [List.map_toArray, List.map_map]
  congr 1
  exact List.map_congr_left fun k hk => glMatT_genW (List.mem_range.1 hk)

theorem gensP_mem
    : ∀ x ∈ gensP, x ∈ C₀ := by
  intro x hx
  unfold gensP at hx
  rcases Array.mem_append.1 hx with hx | hx
  · unfold gensY at hx
    obtain ⟨k, hk, rfl⟩ := Array.mem_map.1 hx
    exact (Subgroup.mem_inf.1 (genY_mem (List.mem_range.1 (List.mem_toArray.1 hk)))).1
  · obtain ⟨k, hk, rfl⟩ := Array.mem_map.1 hx
    exact genW_mem (List.mem_range.1 (List.mem_toArray.1 hk))

@[expose, irreducible] noncomputable def valsP
    : Array (ModGL TwistTag.E6.tag C2E6Overlap.K) :=
  slpRunG gensP progP

theorem glMatT_valsP
    (i : ℕ) : glMatT (valsP.getD i 1) = toMat (nValsP.getD i Native.one) := by
  refine glMatT_getD ?_ i
  unfold valsP
  rw [nValsP, map_slpRunG, gensP_map_glMatT, toMat_slpRun]

theorem valsP_mem
    (i : ℕ) : valsP.getD i 1 ∈ C₀ := by
  unfold valsP
  exact getD_mem _ (slpRunG_mem _ gensP_mem progP) i

theorem valsP_of_witOK
    {S : Native.Mat} {s : ModGL TwistTag.E6.tag C2E6Overlap.K}
    (hs : glMatT s = toMat S) {i m : ℕ} (h : witOK S i m = true) :
    Odd m ∧ valsP.getD i 1 ^ m = 1 ∧ valsP.getD i 1 * s = s * valsP.getD i 1 := by
  simp only [witOK, commB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hm, hp⟩, hc⟩ := h
  refine ⟨Nat.odd_iff.2 hm, eq_of_glMatT (by rw [map_pow, glMatT_valsP, toMat_pow]) hp,
    glMatT_injective ?_⟩
  rw [map_mul, map_mul, glMatT_valsP, hs, ← toMat_mul, ← toMat_mul, toMat_eq_of_eqM hc]

theorem eq_one_or_eq_of_pairOK
    {S P : Native.Mat} {w : List (ℕ × ℕ)} {s y : C₀}
    (hs : glMatT (s : ModGL TwistTag.E6.tag C2E6Overlap.K) = toMat S)
    (hy : glMatT (y : ModGL TwistTag.E6.tag C2E6Overlap.K) = toMat P)
    (hw : ∀ q ∈ w, witOK S q.1 q.2 = true) (hok : pairOK S w P = true)
    (hD : Step83Pair.OddCommute s y) : y = 1 ∨ y = s := by
  have hall : (w.all fun q => commB (nValsP.getD q.1 Native.one) P) = true := by
    refine List.all_eq_true.2 fun q hq => ?_
    obtain ⟨hm, hp, hc⟩ := valsP_of_witOK hs (hw q hq)
    set c : C₀ := ⟨valsP.getD q.1 1, valsP_mem q.1⟩
    have hcs : c * s = s * c := Subtype.ext hc
    have hcm : c ^ q.2 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hp)
    have hodd : Odd (orderOf c) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hcm)
    have hcy := congrArg Subtype.val (hD c hcs hodd)
    simp only [Subgroup.coe_mul] at hcy
    refine eqM_of_toMat_eq ?_
    rw [toMat_mul, toMat_mul, ← glMatT_valsP, ← hy, ← map_mul, ← map_mul]
    exact congrArg glMatT hcy
  simp only [pairOK, hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at hok
  rcases hok with h | h
  · exact Or.inl (Subtype.ext (eq_of_glMatT hy h))
  · exact Or.inr (Subtype.ext (glMatT_injective (by rw [hy, hs, toMat_eq_of_eqM h])))

theorem root62 : e6Certificate.root 62 = twistedE6ClassRootU :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root61 : e6Certificate.root 61 = twistedE6ClassRootU' :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root48 : e6Certificate.root 48 = twistedE6ClassRootA :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root52 : e6Certificate.root 52 = twistedE6ClassRootA' :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root66 : e6Certificate.root 66 = twistedE6ClassRootB :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root68 : e6Certificate.root 68 = ![1, 1, 2, 3, 2, 1] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem genY_62
    : genY 62 = twistedE6ClassU C2E6Overlap.K := by
  have h : rhoIdx.getD 62 0 = 61 := by decide
  simp only [genY, h, Nat.reduceEqDiff, ↓reduceIte, root62, root61, twistedE6ClassU]

theorem genY_48_66
    : genY 48 * genY 66 = twistedE6ClassV C2E6Overlap.K := by
  have h : rhoIdx.getD 48 0 = 52 := by decide
  have h' : rhoIdx.getD 66 0 = 66 := by decide
  simp only [genY, h, h', Nat.reduceEqDiff, ↓reduceIte, root48, root52, root66, twistedE6ClassV]

theorem glMatT_classU
    : glMatT (twistedE6ClassU C2E6Overlap.K) = toMat nU := by
  rw [← genY_62, glMatT_genY (by norm_num), nU]

theorem glMatT_classV
    : glMatT (twistedE6ClassV C2E6Overlap.K) = toMat nV := by
  rw [← genY_48_66, map_mul, glMatT_genY (by norm_num), glMatT_genY (by norm_num), nV, toMat_mul]

theorem exists_coeff_of_mem
    {L : List (Fin TwistTag.E6.tag.rank → ℤ)} (hnd : L.Nodup)
    (hL : ∀ α ∈ L, IsRoot TwistTag.E6.tag α ∧ 6 ≤ height α)
    (hρ : ∀ α ∈ L, permLattice TwistTag.E6.perm α ∈ L)
    (hLL : ∀ α ∈ L, ∀ β ∈ L, ¬IsRoot TwistTag.E6.tag (α + β))
    {z : ModGL TwistTag.E6.tag C2E6Overlap.K}
    (hz : z ∈ rootSpan TwistTag.E6.tag C2E6Overlap.K {γ | γ ∈ L})
    (hzΓ : z ∈ twistedFixedGroup TwistTag.E6 C2E6Overlap.K barEquiv.toRingHom) :
    ∃ c : (Fin TwistTag.E6.tag.rank → ℤ) → C2E6Overlap.K,
      (L.map fun α => pinnedX TwistTag.E6.tag C2E6Overlap.K α (c α)).prod = z ∧
        ∀ α ∈ L, c (permLattice TwistTag.E6.perm α) = barEquiv.toRingHom (c α) := by
  have h2 : (2 : C2E6Overlap.K) = 0 := CharP.cast_eq_zero _ 2
  have hpos : ∀ α ∈ L, IsRoot TwistTag.E6.tag α ∧ 0 < height α :=
    fun α hα => ⟨(hL α hα).1, by linarith [(hL α hα).2]⟩
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq C2E6Overlap.K (S := {γ | γ ∈ L}) hpos
    (fun α hα β hβ a b ha hb hr => absurd (height_le_eleven hr) (by
      rw [height_nsmul_add_nsmul]
      have h1 := (hL α hα).2
      have h2 := (hL β hβ).2
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith)) hnd (fun α => Iff.rfl) hz
  refine ⟨c, hc, ?_⟩
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hzΓ).2
  have hFz : twistHom TwistTag.E6 C2E6Overlap.K barEquiv.toRingHom z =
      (L.map fun α => pinnedX TwistTag.E6.tag C2E6Overlap.K (permLattice TwistTag.E6.perm α)
        (barEquiv.toRingHom (c α))).prod := by
    rw [← hc, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun α hα => ?_
    exact twistHom_pinnedX_eq_of_charTwo h2 barEquiv.toRingHom (hL α hα).1 (c α)
  set g : (Fin TwistTag.E6.tag.rank → ℤ) → ModGL TwistTag.E6.tag C2E6Overlap.K :=
    fun β => pinnedX TwistTag.E6.tag C2E6Overlap.K β
      (barEquiv.toRingHom (c (permLattice TwistTag.E6.perm β))) with hg
  have hmap : (L.map fun α => pinnedX TwistTag.E6.tag C2E6Overlap.K
      (permLattice TwistTag.E6.perm α) (barEquiv.toRingHom (c α))) =
      (L.map (permLattice TwistTag.E6.perm)).map g := by
    rw [List.map_map]
    refine List.map_congr_left fun α _ => ?_
    simp only [hg, Function.comp_apply, permLattice_twistedE6_perm_perm]
  have hinj : Function.Injective (permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm) :=
    Function.LeftInverse.injective (g := permLattice TwistTag.E6.perm)
      fun α => permLattice_twistedE6_perm_perm α
  have hperm : (L.map (permLattice TwistTag.E6.perm)).Perm L := by
    refine (List.perm_ext_iff_of_nodup (hnd.map hinj) hnd).2 fun β => ⟨fun hβ => ?_, fun hβ => ?_⟩
    · obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hβ
      exact hρ α hα
    · exact List.mem_map.2 ⟨_, hρ β hβ, permLattice_twistedE6_perm_perm β⟩
  have hcomm : ((L.map (permLattice TwistTag.E6.perm)).map g).Pairwise Commute := by
    refine List.pairwise_of_forall_mem_list fun a ha b hb => ?_
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 ha
    obtain ⟨β', hβ', rfl⟩ := List.mem_map.1 hb
    have hβL := hperm.subset hβ
    have hβ'L := hperm.subset hβ'
    refine commute_pinnedX_of_not_isRoot_of_ne_zero_E6 (hL β hβL).1 (hL β' hβ'L).1
      (hLL β hβL β' hβ'L) (fun h0 => ?_) _ _
    have := congrArg height h0
    rw [height_add, show height (0 : Fin TwistTag.E6.tag.rank → ℤ) = 0 by simp [height]] at this
    linarith [(hL β hβL).2, (hL β' hβ'L).2]
  have heq : (L.map fun α => pinnedX TwistTag.E6.tag C2E6Overlap.K α (c α)).prod =
      (L.map fun β => pinnedX TwistTag.E6.tag C2E6Overlap.K β
        (barEquiv.toRingHom (c (permLattice TwistTag.E6.perm β)))).prod := by
    rw [hc, ← hF, hFz, hmap, (hperm.map g).prod_eq' hcomm]
  have key := pinnedX_list_prod_injective L hnd hpos c _ heq
  intro α hα
  rw [key _ (hρ α hα), permLattice_twistedE6_perm_perm]

theorem omega_add_bar : ofBits false true + barEquiv.toRingHom (ofBits false true) = 1 := by
  rw [bar_omega, ← ofBits_add]
  exact ofBits_true_false

theorem bar_omega_ne : barEquiv.toRingHom (ofBits false true) ≠ ofBits false true := by
  rw [bar_omega]
  intro h
  exact absurd (ofBits_injective h).1 Bool.noConfusion

theorem card_K_eq : Nat.card C2E6Overlap.K = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, C2E6Overlap.card_K]
  norm_num

theorem barEquiv_eq_pow (c : C2E6Overlap.K) : C2E6Std.barEquiv c = c ^ 2 ^ 1 := rfl

theorem commute_of_mem_closure
    {s y : C₀} (hD : Step83Pair.OddCommute s y) {x : C₀}
    (hx : x ∈ Subgroup.closure {c : C₀ | c * s = s * c ∧ Odd (orderOf c)}) : x * y = y * x := by
  have h : Commute x y := by
    induction hx using Subgroup.closure_induction with
    | mem c hc => exact hD c hc.1 hc.2
    | one => exact Commute.one_left y
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  exact h.eq

theorem mem_posUnipotent_of_commute
    {h : ℤ} (h1 : 1 ≤ h) (h7 : h ≤ 7) {y : C₀}
    (hy : ∀ x : C₀, (x : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈
      heightSeries TwistTag.E6.tag C2E6Overlap.K h → x * y = y * x) :
    (y : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈
      graphFixedPosUnipotent TwistTag.E6 C2E6Overlap.K barEquiv.toRingHom := by
  obtain ⟨u, huU, hu, he, -⟩ := exists_eq_conj_of_fix_fixedHeightSeries_twistedE6 (f := 1) le_rfl
    card_K_eq (σ := C2E6Std.barEquiv) barEquiv_eq_pow h1 h7 (MulAut.conj y)
    (fun x hx => by rw [MulAut.conj_apply, ← hy x hx, mul_inv_cancel_right])
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 C2E6Overlap.K C2E6Std.barEquiv
  have hyu : y = ⟨u, hu⟩ := UnbalancedCatalog.conj_injective hZ he
  rw [hyu]
  exact huU

theorem mem_rootSpan_of_classCheck
    {R : List (Fin TwistTag.E6.tag.rank → ℤ)} {h : ℤ}
    {T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))} {L : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hchk : twistedE6ClassCheck R h T L = true) {s : C₀}
    (hs : (s : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      (R.map fun ε => pinnedX TwistTag.E6.tag C2E6Overlap.K ε 1).prod)
    {z : C₀} (hz : (z : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈
      graphFixedPosUnipotent TwistTag.E6 C2E6Overlap.K barEquiv.toRingHom)
    (hD : Step83Pair.OddCommute s z) :
    (z : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈
      rootSpan TwistTag.E6.tag C2E6Overlap.K {γ | γ ∈ L} := by
  have hσσ : ∀ x, barEquiv.toRingHom (barEquiv.toRingHom x) = x := fun x => bar_bar x
  obtain ⟨-, -, hTp, hDc, -, hdet, hL, -⟩ := twistedE6ClassCheck_sound hchk
  have hA := twistedE6OrbitClosure_le_closure_odd hσσ omega_add_bar hchk hs
  have hcomm : ∀ γ ∈ twistedE6ClassTargets T, ∀ c : C₀,
      (c : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈
        rootSpan TwistTag.E6.tag C2E6Overlap.K (TwistTag.E6.diagramOrbit γ : Set _) ⊓
          twistedFixedGroup TwistTag.E6 C2E6Overlap.K barEquiv.toRingHom →
        (z : ModGL TwistTag.E6.tag C2E6Overlap.K) * c = c * z := fun γ hγ c hc =>
    (congrArg Subtype.val
      (commute_of_mem_closure hD (hA (Subgroup.subset_closure ⟨γ, hγ, hc⟩)))).symm
  exact mem_rootSpan_of_commute_twistedE6 bar_omega_ne
    (S := {δ | δ ∈ twistedE6ClassTargets T}) (A := {γ | γ ∈ L}) (fun δ hδ => hTp δ hδ)
    (fun δ hδ => (hDc δ hδ).2.2) (fun γ hγ δ hδ => (hL γ hγ).2.2 δ hδ) hdet
    (Subgroup.mem_inf.1 hz).1
    (fun δ hδ hρ => hcomm δ hδ
      ⟨_, pinnedX_mem_graphFixedRootGroup_of_fixed _ (hTp δ hδ).1 hρ (map_one _)⟩
      (pinnedX_mem_orbitGroup_of_fixed _ (hTp δ hδ).1 hρ (map_one _)))
    (fun δ hδ _ d => hcomm δ hδ
      ⟨_, twistedE6PairX_mem_graphFixedRootGroup hσσ (hTp δ hδ).1 d⟩
      (twistedE6PairX_mem_orbitGroup hσσ (hTp δ hδ).1 d))

theorem eq_of_oddCommute_theta
    {s y : C₀} (hs : (s : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      pinnedX TwistTag.E6.tag C2E6Overlap.K e6HighestRoot 1)
    (hD : Step83Pair.OddCommute s y) : y = 1 ∨ y = s := by
  have hU : ∀ x : C₀, (x : ModGL TwistTag.E6.tag C2E6Overlap.K) ∈
      graphFixedPosUnipotent TwistTag.E6 C2E6Overlap.K barEquiv.toRingHom → x * y = y * x :=
    fun x hx => commute_of_mem_closure hD
      (graphFixedPosUnipotent_le_closure_odd_two (σ := C2E6Std.barEquiv)
        (by rw [Nat.card_eq_fintype_card, C2E6Overlap.card_K]) (fun c => rfl) hs hx)
  have hy := mem_posUnipotent_of_commute (h := 1) le_rfl (by norm_num) fun x hx =>
    hU x (Subgroup.mem_inf.2 ⟨by rwa [heightSeries_one] at hx,
      graphFixedRootGroup_le _ _ _ x.2⟩)
  rcases LargeExtraspecial.S14.TwoE6.eq_one_or_eq_pinnedX_theta_of_commute hy fun u hu =>
      (congrArg Subtype.val (hU ⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hu⟩
        hu)).symm with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext (h.trans hs.symm))

theorem exists_ofBits (x : C2E6Overlap.K) : ∃ a0 a1 : Bool, ofBits a0 a1 = x := by
  have hinj : Function.Injective fun p : Bool × Bool => ofBits p.1 p.2 := fun p q h => by
    obtain ⟨h1, h2⟩ := ofBits_injective h
    exact Prod.ext h1 h2
  obtain ⟨p, hp⟩ := ((Fintype.bijective_iff_injective_and_card _).2
    ⟨hinj, by rw [C2E6Overlap.card_K]; rfl⟩).2 x
  exact ⟨p.1, p.2, hp⟩

theorem bar_ofBits (a0 a1 : Bool) :
    barEquiv.toRingHom (ofBits a0 a1) = ofBits (a0 ^^ a1) a1 := by
  rw [barEquiv_toRingHom, barHom_apply, bar, ofBits_sq]

theorem exists_ofBits_of_fixed {x : C2E6Overlap.K} (hx : barEquiv.toRingHom x = x) :
    ∃ c0 : Bool, ofBits c0 false = x := by
  obtain ⟨c0, c1, rfl⟩ := exists_ofBits x
  rw [bar_ofBits] at hx
  have h1 : c1 = false := by
    have := (ofBits_injective hx).1
    cases c0 <;> cases c1 <;> simp_all
  exact ⟨c0, by rw [h1]⟩

theorem mem_bools (b : Bool) : b ∈ bools := by
  cases b <;> decide

theorem root62' : e6Certificate.root 62 = ![1, 1, 1, 2, 2, 1] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root61' : e6Certificate.root 61 = ![1, 1, 2, 2, 1, 1] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root70' : e6Certificate.root 70 = ![1, 2, 2, 3, 2, 1] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root52' : e6Certificate.root 52 = ![0, 1, 1, 2, 1, 1] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root48' : e6Certificate.root 48 = ![1, 1, 1, 2, 1, 0] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem root66' : e6Certificate.root 66 = ![1, 1, 2, 2, 2, 1] :=
  RootCertificate.eq_of_ofFn_beq (by decide)

theorem annU_eq : twistedE6ClassUAnn = [rt 62, rt 61, rt 70] := by
  unfold rt
  rw [root62', root61', root70']
  rfl

theorem annV_eq : twistedE6ClassVAnn = [rt 52, rt 48, rt 66, rt 68, rt 70] := by
  unfold rt
  rw [root52', root48', root66', root68, root70']
  rfl

theorem annU_facts : twistedE6ClassUAnn.Nodup ∧ (∀ α ∈ twistedE6ClassUAnn, 6 ≤ height α) ∧
    ∀ α ∈ twistedE6ClassUAnn, permLattice TwistTag.E6.perm α ∈ twistedE6ClassUAnn := by
  decide

theorem annV_facts : twistedE6ClassVAnn.Nodup ∧ (∀ α ∈ twistedE6ClassVAnn, 6 ≤ height α) ∧
    ∀ α ∈ twistedE6ClassVAnn, permLattice TwistTag.E6.perm α ∈ twistedE6ClassVAnn := by
  decide

theorem rho_root {k j : ℕ} (hk : k < 72) (h : rhoIdx.getD k 0 = j) :
    permLattice TwistTag.E6.perm (rt k) = rt j := by
  rw [← root_rhoIdx hk, h]

theorem eq_of_oddCommute_classU
    {s y : C₀} (hs : (s : ModGL TwistTag.E6.tag C2E6Overlap.K) = twistedE6ClassU C2E6Overlap.K)
    (hD : Step83Pair.OddCommute s y) : y = 1 ∨ y = s := by
  have hσσ : ∀ x, barEquiv.toRingHom (barEquiv.toRingHom x) = x := fun x => bar_bar x
  have hR : (s : ModGL TwistTag.E6.tag C2E6Overlap.K) = (twistedE6ClassURoots.map fun ε =>
      pinnedX TwistTag.E6.tag C2E6Overlap.K ε 1).prod := by
    rw [hs]
    simp [twistedE6ClassU, twistedE6ClassURoots]
  have hyU := mem_posUnipotent_of_commute (h := 4) (by norm_num) (by norm_num) fun x hx =>
    commute_of_mem_closure hD (fixedHeightSeries_le_closure_odd_of_classCheck
      barEquiv.surjective hσσ omega_add_bar twistedE6ClassCheck_U hR x hx)
  have hyL := mem_rootSpan_of_classCheck twistedE6ClassCheck_U hR hyU hD
  obtain ⟨-, -, -, -, -, -, hL, hLL⟩ := twistedE6ClassCheck_sound twistedE6ClassCheck_U
  obtain ⟨hnd, hht, hρ⟩ := annU_facts
  obtain ⟨c, hc, hcρ⟩ := exists_coeff_of_mem hnd (fun α hα => ⟨(hL α hα).1, hht α hα⟩) hρ hLL
    hyL (graphFixedRootGroup_le _ _ _ y.2)
  rw [annU_eq] at hc hcρ
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
  have h1 := hcρ (rt 62) (by simp)
  have h3 := hcρ (rt 70) (by simp)
  rw [rho_root (by norm_num) (by decide : rhoIdx.getD 62 0 = 61)] at h1
  rw [rho_root (by norm_num) (by decide : rhoIdx.getD 70 0 = 70)] at h3
  obtain ⟨a0, a1, ha⟩ := exists_ofBits (c (rt 62))
  obtain ⟨c0, hc0⟩ := exists_ofBits_of_fixed h3.symm
  rw [h1, ← hc0, ← ha, bar_ofBits] at hc
  have hy : glMatT (y : ModGL TwistTag.E6.tag C2E6Overlap.K) = toMat (candU a0 a1 c0) := by
    rw [← hc, map_mul, map_mul, glMatT_pinnedX_root (by norm_num),
      glMatT_pinnedX_root (by norm_num), glMatT_pinnedX_root (by norm_num), candU, toMat_mul,
      toMat_mul, mul_assoc]
  have hchk := twistedE6TwoPairU_check
  simp only [pairCheckU, Bool.and_eq_true, List.all_eq_true] at hchk
  exact eq_one_or_eq_of_pairOK (by rw [hs, glMatT_classU]) hy hchk.1
    (hchk.2 a0 (mem_bools a0) a1 (mem_bools a1) c0 (mem_bools c0)) hD

theorem eq_of_oddCommute_classV
    {s y : C₀} (hs : (s : ModGL TwistTag.E6.tag C2E6Overlap.K) = twistedE6ClassV C2E6Overlap.K)
    (hD : Step83Pair.OddCommute s y) : y = 1 ∨ y = s := by
  have hσσ : ∀ x, barEquiv.toRingHom (barEquiv.toRingHom x) = x := fun x => bar_bar x
  have hR : (s : ModGL TwistTag.E6.tag C2E6Overlap.K) = (twistedE6ClassVRoots.map fun ε =>
      pinnedX TwistTag.E6.tag C2E6Overlap.K ε 1).prod := by
    rw [hs]
    simp [twistedE6ClassV, twistedE6ClassVRoots, mul_assoc]
  have hyU := mem_posUnipotent_of_commute (h := 6) (by norm_num) (by norm_num) fun x hx =>
    commute_of_mem_closure hD (fixedHeightSeries_le_closure_odd_of_classCheck
      barEquiv.surjective hσσ omega_add_bar twistedE6ClassCheck_V hR x hx)
  have hyL := mem_rootSpan_of_classCheck twistedE6ClassCheck_V hR hyU hD
  obtain ⟨-, -, -, -, -, -, hL, hLL⟩ := twistedE6ClassCheck_sound twistedE6ClassCheck_V
  obtain ⟨hnd, hht, hρ⟩ := annV_facts
  obtain ⟨c, hc, hcρ⟩ := exists_coeff_of_mem hnd (fun α hα => ⟨(hL α hα).1, hht α hα⟩) hρ hLL
    hyL (graphFixedRootGroup_le _ _ _ y.2)
  rw [annV_eq] at hc hcρ
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hc
  have h1 := hcρ (rt 52) (by simp)
  have h3 := hcρ (rt 66) (by simp)
  have h4 := hcρ (rt 68) (by simp)
  have h5 := hcρ (rt 70) (by simp)
  rw [rho_root (by norm_num) (by decide : rhoIdx.getD 52 0 = 48)] at h1
  rw [rho_root (by norm_num) (by decide : rhoIdx.getD 66 0 = 66)] at h3
  rw [rho_root (by norm_num) (by decide : rhoIdx.getD 68 0 = 68)] at h4
  rw [rho_root (by norm_num) (by decide : rhoIdx.getD 70 0 = 70)] at h5
  obtain ⟨a0, a1, ha⟩ := exists_ofBits (c (rt 52))
  obtain ⟨c1, hc1⟩ := exists_ofBits_of_fixed h3.symm
  obtain ⟨c2, hc2⟩ := exists_ofBits_of_fixed h4.symm
  obtain ⟨c3, hc3⟩ := exists_ofBits_of_fixed h5.symm
  rw [h1, ← hc1, ← hc2, ← hc3, ← ha, bar_ofBits] at hc
  have hy : glMatT (y : ModGL TwistTag.E6.tag C2E6Overlap.K) =
      toMat (candV a0 a1 c1 c2 c3) := by
    rw [← hc]
    simp only [map_mul, candV, toMat_mul, mul_assoc]
    rw [glMatT_pinnedX_root (by norm_num), glMatT_pinnedX_root (by norm_num),
      glMatT_pinnedX_root (by norm_num), glMatT_pinnedX_root (by norm_num),
      glMatT_pinnedX_root (by norm_num)]
  have hchk := twistedE6TwoPairV_check
  simp only [pairCheckV, Bool.and_eq_true, List.all_eq_true] at hchk
  exact eq_one_or_eq_of_pairOK (by rw [hs, glMatT_classV]) hy hchk.1
    (hchk.2 a0 (mem_bools a0) a1 (mem_bools a1) c1 (mem_bools c1) c2 (mem_bools c2) c3
      (mem_bools c3)) hD

theorem eq_of_oddCommute_rep
    {s y : C₀} (hs : s ∈ twistedE6ClassReps C2E6Overlap.K barEquiv.toRingHom)
    (hD : Step83Pair.OddCommute s y) : y = 1 ∨ y = s := by
  rcases hs with hs | hs | hs
  · exact eq_of_oddCommute_theta hs hD
  · exact eq_of_oddCommute_classU hs hD
  · exact eq_of_oddCommute_classV hs hD

theorem eq_of_oddCommute
    {x y : C₀} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) (hD : Step83Pair.OddCommute x y) :
    y = 1 ∨ y = x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction (f := 1) le_rfl
    card_K_eq (σ := barEquiv) barEquiv_eq_pow
    (twistedE6FrameReduction le_rfl card_K_eq barEquiv_eq_pow) hx hx1
  rcases eq_of_oddCommute_rep hg (Step83Pair.oddCommute_conj g hD) with h | h
  · exact Or.inl (conj_eq_one_iff.1 h)
  · exact Or.inr (mul_left_cancel (mul_right_cancel h))

theorem eq_of_oddCommute_model
    {S : Type} [Group S] (h : ChevalleyExceptionalModel S .twistedE6 2 1) {x y : S}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hD : Step83Pair.OddCommute x y) : y = x := by
  have hmod : TwistedChevalleyModel S .E6 (2 ^ 1) := h.2
  obtain ⟨L, _, _, σL, hL, hσL, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two le_rfl hmod
  obtain ⟨e₂⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four
    (L := L) (by rw [hL]; rfl) σL.toRingHom fun c => by simpa using hσL c
  have e : S ≃* C₀ := e₁.trans e₂
  have hx2 : e x ^ 2 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hx1 : e x ≠ 1 := fun h1 => by
    rw [(map_eq_one_iff e e.injective).1 h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  rcases eq_of_oddCommute hx2 hx1 (Step83Pair.oddCommute_map e hD) with h1 | h1
  · rw [(map_eq_one_iff e e.injective).1 h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · exact e.injective h1

theorem not_pairCent_twistedE6
    {S : Type} [Group S] (h : ChevalleyExceptionalModel S .twistedE6 2 1) {x y : S}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hne : x ≠ y) :
    ¬AS76b.oUpperTwo (Subgroup.centralizer ({x} : Set S)) ≤ Subgroup.centralizer ({y} : Set S) :=
  fun h1 => hne (eq_of_oddCommute_model h hx hy (Step83Pair.oddCommute_of_oUpperTwo_le h1)).symm

end CFSG.ComponentClassification.RankTwoExceptional.PairE6
