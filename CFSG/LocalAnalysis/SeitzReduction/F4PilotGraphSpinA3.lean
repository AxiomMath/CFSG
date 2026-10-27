module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowParam
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinLevi

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus toStdD spinMatrix
  plusFrame)
open CFSG.LieType.RootSystem (roots)
open CFSG.SeitzReduction.OmegaPilot (diagOmega diagOmega_coe)
open CFSG.SeitzReduction.SymplecticPilot (diagSpEntry diagSpEntry_inl diagSpEntry_inr)

local instance f4PilotGraphSpinA3NeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Matrix

variable {K : Type} [Field K]

theorem snocOne_sp6ParamA_of_ne_zero (a : Kˣ) {m : Fin 4} (hm : m ≠ 0) :
    snocOne K (sp6ParamA K a) m = 1 := by
  rw [c3Torus_sp6ParamA_apply]
  fin_cases m
  · exact absurd rfl hm
  · rfl
  · rfl
  · rfl

theorem diagSpEntry_snocOne_sp6ParamA (a : Kˣ) {m : Fin 4} (hm : m ≠ 0) (r : Bool) :
    diagSpEntry (snocOne K (sp6ParamA K a)) (SpinPlus.plusIdx m r) = 1 := by
  cases r
  · change (((snocOne K (sp6ParamA K a) m)⁻¹ : Kˣ) : K) = 1
    rw [snocOne_sp6ParamA_of_ne_zero a hm, inv_one, Units.val_one]
  · change ((snocOne K (sp6ParamA K a) m : Kˣ) : K) = 1
    rw [snocOne_sp6ParamA_of_ne_zero a hm, Units.val_one]

@[expose] def spinPlusCoord : Fin 4 ⊕ Fin 4 → Fin 4 := Sum.elim id id

theorem spinPlusCoord_plusIdx (m : Fin 4) (r : Bool) :
    spinPlusCoord (SpinPlus.plusIdx m r) = m := by
  cases r <;> rfl

theorem eq_plusIdx_spinPlusCoord (p : Fin 4 ⊕ Fin 4) :
    ∃ r, p = SpinPlus.plusIdx (spinPlusCoord p) r := by
  rcases p with m | m
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

theorem longMat_apply_eq_zero {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) (s t : Bool)
    {p q : Fin 4 ⊕ Fin 4} (hpq : spinPlusCoord p = 0 ∨ spinPlusCoord q = 0) :
    longMat K SpinPlus.plusIdx i j s t p q = 0 := by
  have key : ∀ (m : Fin 4) (r : Bool), m ≠ 0 → spinPlusCoord (SpinPlus.plusIdx m r) ≠ 0 :=
    fun m r hm => by rwa [spinPlusCoord_plusIdx]
  have h1 : ¬ (SpinPlus.plusIdx i s = p ∧ SpinPlus.plusIdx j (!t) = q) := by
    rintro ⟨rfl, rfl⟩
    rcases hpq with h | h
    exacts [key i s hi h, key j (!t) hj h]
  have h2 : ¬ (SpinPlus.plusIdx j t = p ∧ SpinPlus.plusIdx i (!s) = q) := by
    rintro ⟨rfl, rfl⟩
    rcases hpq with h | h
    exacts [key j t hj h, key i (!s) hi h]
  simp only [longMat, Matrix.sub_apply, Matrix.single_apply, h1, h2, ↓reduceIte, sub_zero]

theorem commute_diagonal_longMat (a : Kˣ) {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) (s t : Bool) :
    Commute (diagonal (diagSpEntry (snocOne K (sp6ParamA K a))))
      (longMat K SpinPlus.plusIdx i j s t) := by
  refine ((mul_diagonal_eq_diagonal_mul_iff _ _).2 fun p q hpq => ?_).symm
  apply longMat_apply_eq_zero hi hj s t
  by_contra! h
  obtain ⟨hp, hq⟩ := h
  obtain ⟨r, hr⟩ := eq_plusIdx_spinPlusCoord p
  obtain ⟨r', hr'⟩ := eq_plusIdx_spinPlusCoord q
  apply hpq
  rw [hr, hr', diagSpEntry_snocOne_sp6ParamA a hp, diagSpEntry_snocOne_sp6ParamA a hq]

theorem toStdD_four_apply_zero (v : Fin 4 → ℤ) : toStdD 4 v 0 = v 0 := by
  simp [toStdD]

end Matrix

section Commute

variable
  {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

omit
  [Finite K] [CharP K 2] in
theorem commute_spinMatrix_x_diagonal {γ : Fin 4 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (h0 : γ 0 = 0) (c : K) (a : Kˣ) :
    Commute ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 γ c) :
        GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)
      (diagonal (diagSpEntry (snocOne K (sp6ParamA K a)))) := by
  have hF := SpinPlus.isCoordFrame_plusFrame (K := K) three_le_rank_D4
  change Commute ((spinMatrix (quadPlus 4 K) (rootElt (plusFrame 4 K three_le_rank_D4)
    (toStdD 4 γ) c) : GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) _
  rw [coe_spinMatrix_rootElt hF]
  obtain ⟨i, j, hij, s, t, he⟩ := (SpinPlus.isLong_toStdD_iff (by norm_num)).2 hγ
  have he0 : toStdD 4 γ 0 = 0 := by rw [toStdD_four_apply_zero, h0]
  have hi : i ≠ 0 := by
    rintro rfl
    rw [he] at he0
    have hj0 : (0 : Fin 4) ≠ j := hij
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_apply, hj0, ite_false,
      add_zero] at he0
    cases s <;> simp [CFSG.LieType.Universal.Spin.boolSign] at he0
  have hj : j ≠ 0 := by
    rintro rfl
    rw [he] at he0
    have hi0 : (0 : Fin 4) ≠ i := hij.symm
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_apply, hi0, ite_false,
      zero_add] at he0
    cases t <;> simp [CFSG.LieType.Universal.Spin.boolSign] at he0
  rw [rootMat_eq hF hij he]
  have hL := commute_diagonal_longMat (K := K) a hi hj s t
  exact (Commute.one_left _).add_left ((hL.symm.smul_left _).smul_left _)

theorem commute_spinX_spinIota_sp6Diag {γ : Fin 4 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (h0 : γ 0 = 0) (c : K) (a : Kˣ) :
    Commute (SpinPlus.x 4 K three_le_rank_D4 γ c)
      (spinIota hK hf (sp6Diag K (sp6ParamA K a))) := by
  apply (spinOmegaEquiv (K := K)).injective
  rw [map_mul, map_mul, spinIota_apply, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_spinOmegaEquiv, coe_omegaPlusIota_sp6Diag, diagOmega_coe]
  exact commute_spinMatrix_x_diagonal hγ h0 c a

theorem e6ScLevi_A3_le_map_centralizer :
    e6ScLevi K e6A3Nodes ≤ (centralizer ((((sp6TorusA (⊤ : Subgroup Kˣ)).map (spinIota hK hf)) :
      Subgroup (spinGroup (quadPlus 4 K))) : Set (spinGroup (quadPlus 4 K)))).map
        (spinToE6Sc K) := by
  have hsingle : ∀ k : Fin 4, (Pi.single k 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    fun k => (SpinPlus.Φ 4 K three_le_rank_D4).single_mem k
  have hneg : ∀ k : Fin 4, (-Pi.single k 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    fun k => by
      have := (CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅).smul_mem
        ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k)
        _ (hsingle k)
      rwa [(CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅).simple_single]
        at this
  have hmem : ∀ γ ∈ roots (isFiniteType_cartanD 4) ∅, γ 0 = 0 → ∀ c : K,
      SpinPlus.x 4 K three_le_rank_D4 γ c ∈ centralizer ((((sp6TorusA (⊤ : Subgroup Kˣ)).map
        (spinIota hK hf)) : Subgroup (spinGroup (quadPlus 4 K))) :
          Set (spinGroup (quadPlus 4 K))) := by
    intro γ hγ h0 c
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
    exact (commute_spinX_spinIota_sp6Diag hK hf hγ h0 c a).symm.eq
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi]
  refine iSup₂_le fun j hj => ?_
  obtain ⟨k, hk, rfl⟩ : ∃ k : Fin 4, k ≠ 0 ∧ d4Node k = j := by
    revert j
    decide
  rw [CFSG.LieType.CurtisTits.rankOne]
  refine sup_le ?_ ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
    refine ⟨SpinPlus.x 4 K three_le_rank_D4 (Pi.single k 1) c,
      hmem _ (hsingle k) (Pi.single_eq_of_ne hk.symm 1) c, ?_⟩
    rw [spinToE6Sc_x (hsingle k), d4Embed_single]
  · intro g hg
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
    refine ⟨SpinPlus.x 4 K three_le_rank_D4 (-Pi.single k 1) c,
      hmem _ (hneg k) (by rw [Pi.neg_apply, Pi.single_eq_of_ne hk.symm 1, neg_zero]) c, ?_⟩
    rw [spinToE6Sc_x (hneg k), d4Embed_neg_single]

theorem commute_spinEquivD4_symm_A3 {y : e6Data_valid.minGroup K}
    (hy : y ∈ e6ScLevi K e6A3Nodes) {s : StatedSp 3 K} (hs : s ∈ sp6TorusA (⊤ : Subgroup Kˣ)) :
    Commute ((spinEquivD4 K).symm
      ⟨y, CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6D4Nodes hy⟩)
      (spinIota hK hf s) := by
  obtain ⟨w, hw, hwy⟩ := e6ScLevi_A3_le_map_centralizer hK hf hy
  have hw' : (spinEquivD4 K).symm
      ⟨y, CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6D4Nodes hy⟩ = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_spinEquivD4]
    exact hwy.symm
  rw [hw']
  exact ((mem_centralizer_iff.1 hw) _ ⟨s, hs, rfl⟩).symm

end Commute

section Perfect


variable {K : Type} [Field K]

theorem hm_mem_e6ScLevi_singleton (j : Fin (Tag.rank .E6)) (t : Kˣ) :
    e6Data_valid.hm K j t ∈ e6ScLevi K {j} := by
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mul_mem (e6Data_valid.nt_mem_rankOne K j t) (inv_mem (e6Data_valid.nt_mem_rankOne K j 1))

theorem commutator_e6ScLevi_singleton (j : Fin (Tag.rank .E6)) {t : Kˣ} (ht : t ^ 2 ≠ 1) :
    ⁅e6ScLevi K {j}, e6ScLevi K {j}⁆ = e6ScLevi K {j} := by
  refine le_antisymm (commutator_le_self _) ?_
  have hmem := hm_mem_e6ScLevi_singleton (K := K) j t
  have hw2 : ∀ i : Fin (Tag.rank .E6), MinData.toWeight (τ := Tag.E6) (Pi.single i 1) i = 2 := by
    decide
  have hw2' : ∀ i : Fin (Tag.rank .E6),
      MinData.toWeight (τ := Tag.E6) (-Pi.single i 1) i = -2 := by
    decide
  have key : ∀ (γ : Fin (Tag.rank .E6) → ℤ), (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
      ∀ c : K, e6Data_valid.xm K γ c ∈ ⁅e6ScLevi K {j}, e6ScLevi K {j}⁆ := by
    intro γ hγ c
    have hroot : IsRoot .E6 γ := by
      rcases hγ with rfl | rfl
      exacts [isRoot_single _ j, isRoot_neg_single _ j]
    have hw : ((t ^ MinData.toWeight (τ := Tag.E6) γ j : Kˣ) : K) ≠ 1 := by
      rcases hγ with rfl | rfl
      · rw [hw2]
        intro h
        apply ht
        exact Units.ext (by simpa using h)
      · rw [hw2']
        intro h
        apply ht
        have h' : ((t ^ (2 : ℤ))⁻¹ : Kˣ) = 1 := by
          rw [← _root_.zpow_neg]
          exact Units.ext (by simpa using h)
        rw [inv_eq_one] at h'
        simpa using h'
    set w : K := ((t ^ MinData.toWeight (τ := Tag.E6) γ j : Kˣ) : K)
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hw
    set d : K := c / (w - 1)
    have hxmem : e6Data_valid.xm K γ d ∈ e6ScLevi K {j} := by
      rcases hγ with rfl | rfl
      · exact xm_single_mem_scLevi j d
      · exact xm_neg_single_mem_scLevi j d
    have hc : ⁅e6Data_valid.hm K j t, e6Data_valid.xm K γ d⁆ = e6Data_valid.xm K γ c := by
      rw [commutatorElement_def, e6Data_valid.hm_conj_xm K hroot, e6Data_valid.xm_neg,
        ← e6Data_valid.xm_add]
      congr 1
      change w * d + -d = c
      rw [show w * d + -d = (w - 1) * d by ring, mul_div_cancel₀ c hw1]
    rw [← hc]
    exact commutator_mem_commutator hmem hxmem
  dsimp only [e6ScLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
  refine sup_le ?_ ?_
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    have := key _ (Or.inl rfl) c
    dsimp only [e6ScLevi] at this
    rwa [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne] at this
  · intro z hz
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
    have := key _ (Or.inr rfl) c
    dsimp only [e6ScLevi] at this
    rwa [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne] at this

theorem commutator_e6ScLevi_A3 {t : Kˣ} (ht : t ^ 2 ≠ 1) :
    ⁅e6ScLevi K e6A3Nodes, e6ScLevi K e6A3Nodes⁆ = e6ScLevi K e6A3Nodes := by
  refine le_antisymm (commutator_le_self _) ?_
  have h : e6ScLevi K e6A3Nodes = ⨆ j ∈ e6A3Nodes, e6ScLevi K {j} := by
    dsimp only [e6ScLevi]
    rw [CFSG.LieType.CurtisTits.levi]
    exact iSup_congr fun j => iSup_congr fun _ => (CFSG.LieType.CurtisTits.levi_singleton _ j).symm
  conv_lhs => rw [h]
  refine iSup₂_le fun j hj => ?_
  rw [← commutator_e6ScLevi_singleton j ht]
  have hle : e6ScLevi K {j} ≤ e6ScLevi K e6A3Nodes :=
    CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 hj)
  exact commutator_mono hle hle

end Perfect

section Piece


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem scLeviRestrict_A3_mem_centralizer {e₂ : L ≃* adjointGroup .F4 K} {ε : K ≃+* K}
    {ΦY : spinGroup (quadPlus 4 K) →* G} (hrY : ΦY.range = neighbourCore e₂ .X)
    (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) (x : e6ScLevi K e6A3Nodes) :
    scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes x ∈
      centralizer (leviTorusG e₂ {1, 2} : Set G) := by
  set g := scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom)
    e6A3Nodes_subset_e6D4Nodes x with hg
  have hgE : g ∈ neighbourCore e₂ .X := by
    rw [← hrY]
    exact ⟨_, rfl⟩
  have hT : leviTorusG e₂ {1, 2} ⊓ neighbourLeviG e₂ .X ≤ centralizer ({g} : Set G) := by
    rw [← map_levi6Hom_sp6TorusA e₂ ε]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hn]
    have hc := congrArg ΦY (commute_spinEquivD4_symm_A3 hK hf x.2 hs).eq
    rw [map_mul, map_mul] at hc
    exact hc.symm
  have hC : centralizer (neighbourCore e₂ .X : Set G) ≤ centralizer ({g} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hz g hgE).symm
  have hle : leviTorusG e₂ {1, 2} ≤ centralizer ({g} : Set G) := by
    refine (le_sup_left (b := centralizer (neighbourCore e₂ .X : Set G))).trans ?_
    rw [leviTorusG_sup_centralizer_eq e₂ one_two_subset_X]
    exact sup_le hT hC
  rw [mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.1 (hle hz)

theorem range_scLeviRestrict_A3_le_pieceCore (hq : 4 ≤ Nat.card K) {e₂ : L ≃* adjointGroup .F4 K}
    {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G} (hrY : ΦY.range = neighbourCore e₂ .X)
    (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) :
    (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes).range ≤
      pieceCore e₂ {1, 2} := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one_of_four_le (K := K) hq
  have hperf : Group.IsPerfect (e6ScLevi K e6A3Nodes) :=
    Subgroup.isPerfect_iff.2 (commutator_e6ScLevi_A3 ht)
  have hperf' := Subgroup.isPerfect_iff.1 (Group.IsPerfect.range
    (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes))
  refine le_centralizerPerfectCore hperf' ?_
  rintro _ ⟨x, rfl⟩
  exact scLeviRestrict_A3_mem_centralizer hK hf hrY hn x

end Piece

section Frames


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

omit
  [CharP K 2] in
theorem pieceCore_one_two_of_frame {e e₂ : L ≃* adjointGroup .F4 K} {N : AmalgamNeighbour}
    (he₂ : IsNeighbourFrame e e₂ N) : pieceCore e₂ {1, 2} = pieceCore e {1, 2} := by
  cases N with
  | X =>
    have h : e₂ = e := he₂
    rw [h]
  | Y =>
    obtain ⟨hc, rfl⟩ := he₂
    rw [pieceCore_trans_graphAutF4_symm, nodePermPow_one_one_two]
  | X' => exact he₂.elim

theorem range_scLeviRestrict_A3_le_pieceCore_of_frame {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e e₂ : L ≃* adjointGroup .F4 K} {N : AmalgamNeighbour}
    (he₂ : IsNeighbourFrame e e₂ N) {ε : K ≃+* K} {ΦY : spinGroup (quadPlus 4 K) →* G}
    (hrY : ΦY.range = neighbourCore e N) (hn : ∀ s, ΦY (spinIota hK hf s) = levi6Hom e₂ ε s) :
    (scLeviRestrict (ΦY.comp (spinEquivD4 K).symm.toMonoidHom) e6A3Nodes_subset_e6D4Nodes).range ≤
      pieceCore e {1, 2} := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [← pieceCore_one_two_of_frame he₂]
  exact range_scLeviRestrict_A3_le_pieceCore hK hf hq (hrY.trans (neighbourFrame_eq he₂).1) hn

theorem range_scLeviRestrict_A3_le_pieceCore_A (hq : 4 ≤ Nat.card K)
    {e e₁ : L ≃* adjointGroup .F4 K} {N : AmalgamNeighbour} (he₁ : IsNeighbourFrame e e₁ N)
    {ΦA : e6ScLevi K e6A5Nodes →* G} (hrA : ΦA.range = neighbourCore e N)
    (hnA : IsLeviNormalizedA e₁ ΦA) :
    (scLeviRestrict ΦA e6A3Nodes_subset_e6A5Nodes).range ≤ pieceCore e {1, 2} := by
  have hB := (neighbourCore_X_le_pieceSpan_of_isLeviNormalizedA hq e₁
    (hrA.trans (neighbourFrame_eq he₁).1) hnA).2
  rw [← pieceCore_one_two_of_frame he₁]
  rintro _ ⟨x, rfl⟩
  obtain ⟨b, hb, hbx⟩ := e6ScLevi_A3_le_map_sl6BlockA x.2
  have hx : (⟨(x : e6Data_valid.minGroup K),
      CFSG.LieType.CurtisTits.levi_mono _ e6A3Nodes_subset_e6A5Nodes x.2⟩ :
        e6ScLevi K e6A5Nodes) = graphParamEquiv K (RingEquiv.refl K) b :=
    Subtype.ext hbx.symm
  rw [scLeviRestrict_apply, hx]
  exact hB ⟨b, hb, rfl⟩

end Frames

end CFSG.SeitzReduction.F4Pilot
