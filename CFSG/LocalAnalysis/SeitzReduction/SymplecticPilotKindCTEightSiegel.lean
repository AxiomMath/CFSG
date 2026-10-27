module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTEightGraph
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTFourOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotFourOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore ordSL)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [CharP K 2] {N ε : ℕ}

theorem ctGraph_mem_blockSpecialLinear_image {I : Finset (Fin (2 * N + ε))}
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ blockSpecialLinear I) :
    ctGraph ε x ∈ blockSpecialLinear (I.image (q2Par N ε)) := by
  have hx' : x⁻¹ ∈ blockSpecialLinear I := inv_mem hx
  rw [mem_blockSpecialLinear] at hx' ⊢
  intro a b hab
  have hab' : q2Par N ε b ∉ I ∨ q2Par N ε a ∉ I := by
    rcases hab with h | h
    · exact Or.inr fun hm => h (Finset.mem_image.2 ⟨_, hm, q2Par_q2Par a⟩)
    · exact Or.inl fun hm => h (Finset.mem_image.2 ⟨_, hm, q2Par_q2Par b⟩)
  rw [coe_ctGraph, q2GramMat_mul_mul_apply, transpose_apply, hx' _ _ hab', Matrix.one_apply,
    Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (by rw [← q2Par_q2Par a, ← h', q2Par_q2Par])), ite_eq_right h]

theorem q2Par_ctE (p : Fin N) : q2Par N ε (ctE N ε p) = ctF N ε p := by
  rw [q2Par_q2Coord]
  rfl

theorem image_q2Par_pair_ctE (p r : Fin N) :
    ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))).image (q2Par N ε) =
      {ctF N ε p, ctF N ε r} := by
  rw [Finset.image_insert, Finset.image_singleton, q2Par_ctE, q2Par_ctE]

theorem disjoint_pair_ctE_ctF (p r p' r' : Fin N) :
    Disjoint ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))) {ctF N ε p', ctF N ε r'} := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h <;> exact ctE_ne_ctF _ _ h

omit [CharP K 2] in
theorem eq_one_of_mem_blockSpecialLinear_of_disjoint {n : ℕ} {I I' : Finset (Fin n)}
    (h : Disjoint I I') {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ blockSpecialLinear I)
    (hx' : x ∈ blockSpecialLinear I') : x = 1 := by
  apply Subtype.ext
  ext a b
  by_cases ha : a ∈ I
  · rw [hx' a b (Or.inl (Finset.disjoint_left.1 h ha))]
    rfl
  · rw [hx a b (Or.inl ha)]
    rfl

omit [CharP K 2] in
theorem ctTorAut_eq_self_of_mem_blockSpecialLinear {W : Finset (Fin (2 * N + 1))}
    (hW : ctV N ∉ W) (a : Kˣ) {x : SpecialLinearGroup (Fin (2 * N + 1)) K}
    (hx : x ∈ blockSpecialLinear W) : ctTorAut a x = x := by
  apply Subtype.ext
  ext i j
  rw [ctTorAut_apply_apply]
  by_cases hi : i = ctV N
  · subst hi
    rw [hx _ j (Or.inl hW), ctTorEntry_ctV]
    by_cases hj : ctV N = j
    · subst hj
      rw [Matrix.one_apply_eq, mul_one, ctTorEntry_ctV, Units.mul_inv]
    · rw [Matrix.one_apply_ne hj, mul_zero, zero_mul]
  · by_cases hj : j = ctV N
    · subst hj
      rw [hx i _ (Or.inr hW), Matrix.one_apply_ne hi, mul_zero, zero_mul]
    · rw [ctTorEntry_of_ne hi, ctTorEntry_of_ne hj, one_mul, mul_one]

end Model

section Blocks

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]
  {N ε : ℕ} {e : L ≃* StatedSp N K}

omit [CharP K 2] [Finite K] in
theorem pair_ctE_subset_compl {k p r : Fin N} (hpk : p ≠ k) (hrk : r ≠ k) :
    ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))) ⊆ (planeCoordsQ2 ε {k})ᶜ := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rw [Finset.mem_compl]
  rcases ha with rfl | rfl
  · exact q2Coord_inl_notMem hpk _ rfl
  · exact q2Coord_inl_notMem hrk _ rfl

omit [CharP K 2] [Finite K] in
theorem pair_ctF_subset_compl {k p r : Fin N} (hpk : p ≠ k) (hrk : r ≠ k) :
    ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))) ⊆ (planeCoordsQ2 ε {k})ᶜ := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rw [Finset.mem_compl]
  rcases ha with rfl | rfl
  · exact q2Coord_inl_notMem hpk _ rfl
  · exact q2Coord_inl_notMem hrk _ rfl

omit [CharP K 2] [Finite K] in
theorem pair_ctE_subset_compl_of_notMem {R : Finset (Fin N)} {p r : Fin N} (hp : p ∉ R)
    (hr : r ∉ R) : ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))) ⊆ (planeCoordsQ2 ε R)ᶜ := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rw [Finset.mem_compl]
  rcases ha with rfl | rfl
  · rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl, planeOf_inl]
    exact hp
  · rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl, planeOf_inl]
    exact hr

omit [CharP K 2] [Finite K] in
theorem pair_ctF_subset_compl_of_notMem {R : Finset (Fin N)} {p r : Fin N} (hp : p ∉ R)
    (hr : r ∉ R) : ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))) ⊆ (planeCoordsQ2 ε R)ᶜ := by
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rw [Finset.mem_compl]
  rcases ha with rfl | rfl
  · rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl, planeOf_inr]
    exact hp
  · rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl, planeOf_inr]
    exact hr

theorem CtLinParam.mem_stringCore_ctE (hK : 4 ≤ Nat.card K) {k : Fin N} (P : CtLinParam ε e k)
    {p r : Fin N} (hpk : p ≠ k) (hrk : r ≠ k) (hpr : p ≠ r)
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hx : x ∈ blockSpecialLinear ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))))
    (hx' : x ∈ q2Block ε K {k}) : P.Φ ⟨x, hx'⟩ ∈ stringCore e {p, r} := by
  have hI2 : 2 ≤ ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))).card := by
    rw [Finset.card_pair fun h => hpr (ctE_injective h)]
  rw [stringCore_def]
  refine P.mem_torusCore hK hI2 (pair_ctE_subset_compl hpk hrk)
    (T := stringTorusSp K {p, r}) ?_ hx
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t, rfl, ?_⟩
  have htpr : t p = t r := (mem_stringTorusParam.1 ht) p (by simp) r (by simp)
  have hval : ∀ a ∈ ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))),
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a = ((t p : Kˣ) : K) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [ctEmbed_diagSp_apply_self]
      simp [Function.update_of_ne hpk]
    · rw [ctEmbed_diagSp_apply_self]
      simp [Function.update_of_ne hrk, htpr]
  intro a ha b hb
  rw [hval a ha, hval b hb]

theorem CtLinParam.mem_stringCore_ctF (hK : 4 ≤ Nat.card K) {k : Fin N} (P : CtLinParam ε e k)
    {p r : Fin N} (hpk : p ≠ k) (hrk : r ≠ k) (hpr : p ≠ r)
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hx : x ∈ blockSpecialLinear ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))))
    (hx' : x ∈ q2Block ε K {k}) : P.Φ ⟨x, hx'⟩ ∈ stringCore e {p, r} := by
  have hI2 : 2 ≤ ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))).card := by
    rw [Finset.card_pair fun h => hpr (ctF_injective h)]
  rw [stringCore_def]
  refine P.mem_torusCore hK hI2 (pair_ctF_subset_compl hpk hrk)
    (T := stringTorusSp K {p, r}) ?_ hx
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨t, rfl, ?_⟩
  have htpr : t p = t r := (mem_stringTorusParam.1 ht) p (by simp) r (by simp)
  have hval : ∀ a ∈ ({ctF N ε p, ctF N ε r} : Finset (Fin (2 * N + ε))),
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a = (((t p)⁻¹ : Kˣ) : K) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [ctEmbed_diagSp_apply_self]
      simp [Function.update_of_ne hpk]
    · rw [ctEmbed_diagSp_apply_self]
      simp [Function.update_of_ne hrk, htpr]
  intro a ha b hb
  rw [hval a ha, hval b hb]

omit [CharP K 2] [Finite K] in
theorem blockSpecialLinear_le_q2Block_pair {k l : Fin N} {I : Finset (Fin (2 * N + ε))}
    (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ) :
    blockSpecialLinear (K := K) I ≤ q2Block ε K {k, l} :=
  LinearPilot.blockSpecialLinear_mono hI

@[expose] noncomputable def CtLinParam.blockHom {k : Fin N} (P : CtLinParam ε e k) (l : Fin N)
    {I : Finset (Fin (2 * N + ε))} (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ) :
    blockSpecialLinear (K := K) I →* G :=
  P.Φ.comp (Subgroup.inclusion ((blockSpecialLinear_le_q2Block_pair hI).trans
    (q2Block_pair_le_left' k l)))

omit [Finite K] in
theorem CtLinParam.blockHom_apply {k : Fin N} (P : CtLinParam ε e k) (l : Fin N)
    {I : Finset (Fin (2 * N + ε))} (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ)
    (x : blockSpecialLinear (K := K) I) :
    P.blockHom l hI x = P.Φ ⟨x, (blockSpecialLinear_le_q2Block_pair hI).trans
      (q2Block_pair_le_left' k l) x.2⟩ :=
  rfl

omit [Finite K] in
theorem CtLinParam.blockHom_injective {k : Fin N} (P : CtLinParam ε e k) {l : Fin N}
    (hkl : k ≠ l) {I : Finset (Fin (2 * N + ε))} (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ) :
    Function.Injective (P.blockHom l hI) := by
  intro x y hxy
  have h := P.injective_overlap hkl (a₁ := ⟨x, blockSpecialLinear_le_q2Block_pair hI x.2⟩)
    (a₂ := ⟨y, blockSpecialLinear_le_q2Block_pair hI y.2⟩) hxy
  exact Subtype.ext (congrArg (fun z : q2Block ε K {k, l} =>
    (z : SpecialLinearGroup (Fin (2 * N + ε)) K)) h)

omit [Finite K] in
theorem CtLinParam.natCard_sup_eq [Finite G] {k : Fin N} (P : CtLinParam ε e k) {l : Fin N}
    (hkl : k ≠ l) {I I' : Finset (Fin (2 * N + ε))} (hI : I ⊆ (planeCoordsQ2 ε {k, l})ᶜ)
    (hI' : I' ⊆ (planeCoordsQ2 ε {k, l})ᶜ) (hII' : Disjoint I I') :
    Nat.card ((P.blockHom l hI).range ⊔ (P.blockHom l hI').range : Subgroup G) =
      Nat.card (blockSpecialLinear (K := K) I) * Nat.card (blockSpecialLinear (K := K) I') := by
  have hcomm : ∀ (x : blockSpecialLinear (K := K) I) (y : blockSpecialLinear (K := K) I'),
      Commute (P.blockHom l hI x) (P.blockHom l hI' y) := by
    intro x y
    rw [P.blockHom_apply, P.blockHom_apply]
    have h := LinearPilot.commute_blockSpecialLinear_of_disjoint hII' x.2 y.2
    change P.Φ _ * P.Φ _ = P.Φ _ * P.Φ _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h.eq
  have hinj : Function.Injective ((P.blockHom l hI).noncommCoprod (P.blockHom l hI') hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨P.blockHom_injective hkl hI, P.blockHom_injective hkl hI', ?_⟩
    rw [disjoint_iff_inf_le]
    rintro _ ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    rw [mem_bot]
    rw [P.blockHom_apply, P.blockHom_apply] at hy
    have h := P.injective_overlap hkl
      (a₁ := ⟨y, blockSpecialLinear_le_q2Block_pair hI' y.2⟩)
      (a₂ := ⟨x, blockSpecialLinear_le_q2Block_pair hI x.2⟩) hy
    have hxy : (y : SpecialLinearGroup (Fin (2 * N + ε)) K) = x := congrArg
      (fun z : q2Block ε K {k, l} => (z : SpecialLinearGroup (Fin (2 * N + ε)) K)) h
    have hx1 : (x : SpecialLinearGroup (Fin (2 * N + ε)) K) = 1 :=
      eq_one_of_mem_blockSpecialLinear_of_disjoint hII' x.2 (hxy ▸ y.2)
    have hx1' : x = 1 := Subtype.ext hx1
    rw [hx1', map_one]
  rw [← MonoidHom.noncommCoprod_range _ _ hcomm, ← Nat.card_prod,
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

omit [Finite K] in
theorem CtLinParam.orderOf_ctGraph_mul_inv {k : Fin N} (P : CtLinParam ε e k) {l : Fin N}
    (hkl : k ≠ l) {p r : Fin N} (hp : p ∉ ({k, l} : Finset (Fin N)))
    (hr : r ∉ ({k, l} : Finset (Fin N))) {x : SpecialLinearGroup (Fin (2 * N + ε)) K}
    (hxI : x ∈ blockSpecialLinear ({ctE N ε p, ctE N ε r} : Finset (Fin (2 * N + ε))))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx : x ∈ q2Block ε K {k}) :
    orderOf (P.Φ ⟨ctGraph ε x, ctGraph_mem_q2Block hx⟩ * (P.Φ ⟨x, hx⟩)⁻¹) = 2 := by
  have hγI : ctGraph ε x ∈ blockSpecialLinear ({ctF N ε p, ctF N ε r} :
      Finset (Fin (2 * N + ε))) := by
    have := ctGraph_mem_blockSpecialLinear_image hxI
    rwa [image_q2Par_pair_ctE] at this
  have hdisj := disjoint_pair_ctE_ctF (ε := ε) p r p r
  have hcomm : Commute (ctGraph ε x) x :=
    LinearPilot.commute_blockSpecialLinear_of_disjoint hdisj.symm hγI hxI
  have hxkl : x ∈ q2Block ε K {k, l} :=
    blockSpecialLinear_le_q2Block_pair (pair_ctE_subset_compl_of_notMem hp hr) hxI
  have hγkl : ctGraph ε x ∈ q2Block ε K {k, l} :=
    blockSpecialLinear_le_q2Block_pair (pair_ctF_subset_compl_of_notMem hp hr) hγI
  have hγγ : ctGraph ε x * ctGraph ε x = 1 := by rw [← map_mul, hx2, map_one]
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_inv, ← map_mul, ← map_mul, ← map_one P.Φ]
    congr 1
    apply Subtype.ext
    change ctGraph ε x * x⁻¹ * (ctGraph ε x * x⁻¹) = 1
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxinv, mul_assoc, ← mul_assoc x, ← hcomm.eq, mul_assoc, hx2, mul_one, hγγ]
  · intro h1
    have h2 : P.Φ ⟨ctGraph ε x, ctGraph_mem_q2Block hx⟩ = P.Φ ⟨x, hx⟩ := mul_inv_eq_one.1 h1
    have h3 := P.injective_overlap hkl (a₁ := ⟨ctGraph ε x, hγkl⟩) (a₂ := ⟨x, hxkl⟩) h2
    have h4 : ctGraph ε x = x := congrArg
      (fun z : q2Block ε K {k, l} => (z : SpecialLinearGroup (Fin (2 * N + ε)) K)) h3
    exact hx1 (eq_one_of_mem_blockSpecialLinear_of_disjoint hdisj hxI (h4 ▸ hγI))

end Blocks

theorem not_ordSL_two_mul_self_dvd {q : ℕ} (hq : 2 ≤ q) :
    ¬ ordSL 2 q * ordSL 2 q ∣ ordSL 2 (q ^ 2) := by
  rw [F4Pilot.ordSL_two, F4Pilot.ordSL_two]
  intro h
  have hq4 : 4 ≤ q ^ 2 := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 1 := ⟨q ^ 2 - 1, by omega⟩
  have h1 : q ^ 2 - 1 = a := by omega
  have h2 : (q ^ 2) ^ 2 - 1 = a * (a + 2) := by
    rw [ha, show (a + 1) ^ 2 = a * (a + 2) + 1 by ring, Nat.add_sub_cancel]
  rw [h1, h2] at h
  have h3 : (q ^ 2 * a) * a ∣ (q ^ 2 * a) * (a + 2) := by
    have e1 : q * a * (q * a) = (q ^ 2 * a) * a := by ring
    have e2 : q ^ 2 * (a * (a + 2)) = (q ^ 2 * a) * (a + 2) := by ring
    rwa [e1, e2] at h
  have hpos : 0 < q ^ 2 * a := Nat.mul_pos (by positivity) (by omega)
  have h4 : a ∣ a + 2 := Nat.dvd_of_mul_dvd_mul_left hpos h3
  have h5 : a ∣ 2 := (Nat.dvd_add_right (dvd_refl a)).1 h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

section Siegel

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem pieceCore_zero_eq_stringCore_four (e : L ≃* StatedSp 4 K) :
    pieceCore e ({0} : Finset (Fin 4)) = stringCore e ({0, 1} : Finset (Fin 4)) :=
  pieceCore_singleton_eq_stringCore e (j := 0) (by decide)

theorem ctE_zero_ne_ctE_one (ε : ℕ) : ctE 4 ε 0 ≠ ctE 4 ε 1 := fun h =>
  absurd (ctE_injective h) (by decide)

omit [Finite K] [CharP K 2] in
theorem transvection_ctE_ne_one (ε : ℕ) :
    SpecialLinearGroup.transvection (ctE_zero_ne_ctE_one ε) (1 : K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * 4 + ε)) K =>
    (z : Matrix (Fin (2 * 4 + ε)) (Fin (2 * 4 + ε)) K) (ctE 4 ε 0) (ctE 4 ε 1)) h
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply_same,
    Matrix.one_apply_ne (ctE_zero_ne_ctE_one ε), zero_add] at h1
  exact one_ne_zero h1

theorem false_of_siegel_normal_of_ctLinParam (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {ε : ℕ} (P : CtLinParam ε e 3)
    (hP : ∀ (x : SpecialLinearGroup (Fin (2 * 4 + ε)) K) (hx : x ∈ q2Block ε K {3}),
      x ∈ blockSpecialLinear ({ctE 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) →
        t * P.Φ ⟨x, hx⟩ * t⁻¹ = P.Φ ⟨ctGraph ε x, ctGraph_mem_q2Block hx⟩)
    (htX : t ∈ centralizer (modelToG e (siegelTorus K 4) : Set G))
    (hnorm : (((modelToG e (siegelLevi K 4)).subgroupOf
      (centralizer (modelToG e (siegelTorus K 4) : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (siegelTorus K 4) : Set G))))).Normal) : False := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hcen := mk_mem_center_of_siegel_normal hset hKc hf (by norm_num) e htC ht htX hnorm
  set x₀ := SpecialLinearGroup.transvection (ctE_zero_ne_ctE_one ε) (1 : K) with hx₀
  have hx₀I : x₀ ∈ blockSpecialLinear ({ctE 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) :=
    LinearPilot.transvection_mem_blockSpecialLinear _ (by simp) (by simp) 1
  have hx₀k : x₀ ∈ q2Block ε K {3} :=
    LinearPilot.blockSpecialLinear_mono (pair_ctE_subset_compl (by decide) (by decide)) hx₀I
  have hord := P.orderOf_ctGraph_mul_inv (l := 2) (by decide) (p := 0) (r := 1) (by decide)
    (by decide) hx₀I (ct_transvection_one_mul_self _) (transvection_ctE_ne_one ε) hx₀k
  rw [← hP x₀ hx₀k hx₀I] at hord
  have hyH : P.Φ ⟨x₀, hx₀k⟩ ∈ centralizer (modelToG e (siegelTorus K 4) : Set G) := by
    have h1 := P.mem_stringCore_ctE hq (p := 0) (r := 1) (by decide) (by decide) (by decide)
      hx₀I hx₀k
    rw [← pieceCore_zero_eq_stringCore_four] at h1
    exact pieceCore_singleton_le_centralizer_siegelTorus e (j := 0) (by decide) h1
  exact false_of_mk_mem_center_of_orderOf_commutator htX hyH hord hcen

theorem false_of_siegelFieldParam_of_ctLinParam (hq : 4 ≤ Nat.card K) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = Nat.card K ^ 2) {e : L ≃* StatedSp 4 K} {t : G}
    {ι : K →+* F} {σ : F ≃+* F} (S : SiegelFieldParam e t ι σ) {ε : ℕ} (P : CtLinParam ε e 3) :
    False := by
  have hI := pair_ctE_subset_compl_of_notMem (ε := ε) (R := ({3, 2} : Finset (Fin 4)))
    (p := 0) (r := 1) (by decide) (by decide)
  have hI' := pair_ctF_subset_compl_of_notMem (ε := ε) (R := ({3, 2} : Finset (Fin 4)))
    (p := 0) (r := 1) (by decide) (by decide)
  have hcard := P.natCard_sup_eq (l := 2) (by decide) hI hI' (disjoint_pair_ctE_ctF 0 1 0 1)
  have hle : (P.blockHom 2 hI).range ⊔ (P.blockHom 2 hI').range ≤
      pieceCore e ({0} : Finset (Fin 4)) := by
    rw [pieceCore_zero_eq_stringCore_four]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [P.blockHom_apply]
      exact P.mem_stringCore_ctE hq (by decide) (by decide) (by decide) x.2 _
    · rintro _ ⟨x, rfl⟩
      rw [P.blockHom_apply]
      exact P.mem_stringCore_ctF hq (by decide) (by decide) (by decide) x.2 _
  have hdvd := Subgroup.card_dvd_of_le hle
  have hcE : ({ctE 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))).card = 2 :=
    Finset.card_pair (ctE_zero_ne_ctE_one ε)
  have hcF : ({ctF 4 ε 0, ctF 4 ε 1} : Finset (Fin (2 * 4 + ε))).card = 2 :=
    Finset.card_pair fun h => absurd (ctF_injective h) (by decide)
  rw [hcard, S.natCard_pieceCore_singleton hq (by norm_num) (j := 0) (by decide), hF,
    F4Pilot.natCard_blockSpecialLinear (by omega), F4Pilot.natCard_blockSpecialLinear (by omega),
    hcE, hcF] at hdvd
  exact not_ordSL_two_mul_self_dvd (by omega) hdvd

theorem nonempty_siegelSwapParam_of_ctLinParam (hcat : LinearPilot.SLmCatalogueClausesAt 4)
    (hdet : LinearPilot.SLmEvenTypeDetAt 4) (hsplit : OddCentralSplit (siegelLevi K 4))
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 4 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {ε : ℕ} (P : CtLinParam ε e 3)
    (hP : ∀ (x : SpecialLinearGroup (Fin (2 * 4 + ε)) K) (hx : x ∈ q2Block ε K {3}),
      x ∈ blockSpecialLinear ({ctE 4 ε 0, ctE 4 ε 1} : Finset (Fin (2 * 4 + ε))) →
        t * P.Φ ⟨x, hx⟩ * t⁻¹ = P.Φ ⟨ctGraph ε x, ctGraph_mem_q2Block hx⟩) :
    Nonempty (SiegelSwapParam e t) := by
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
  obtain ⟨hσ1, hσσ⟩ := ne_one_and_mul_self_of_orderOf_eq_two hσ
  have hF : Nat.card F = Nat.card K ^ 2 := by
    rw [LinearPilot.natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix, hKc, ← pow_mul,
      mul_comm]
  rcases siegel_normal_or_fieldParam_or_swapParam hcat hdet hset hKc hf (by norm_num) e htC ht
    hsplit ι hσ1 hσσ hfix with ⟨htX, hnorm⟩ | hS' | hS
  · exact (false_of_siegel_normal_of_ctLinParam hset hKc hf e htC ht P hP htX hnorm).elim
  · obtain ⟨S⟩ := hS'
    exact (false_of_siegelFieldParam_of_ctLinParam hq hF S P).elim
  · exact hS

theorem nonempty_siegelSwapParam_linearEven
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4)
    (hsplit : OddCentralSplit (siegelLevi K 4)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hk : RootKindSp e t f 3 .linearEven) : Nonempty (SiegelSwapParam e t) := by
  obtain ⟨P, hP⟩ := exists_ctLinParam_conj_ctGraph (m := 3) hset hKc hf le_rfl e htC ht 3 hk
  exact nonempty_siegelSwapParam_of_ctLinParam hcat hdet hsplit hset hKc hf e htC ht P
    fun x hx _ => hP ⟨x, hx⟩

theorem nonempty_siegelSwapParam_linearOdd
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4)
    (hsplit : OddCentralSplit (siegelLevi K 4)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 4 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hk : RootKindSp e t f 3 .linearOdd) : Nonempty (SiegelSwapParam e t) := by
  obtain ⟨P, a, hP⟩ :=
    exists_ctLinParam_conj_ctTor_ctGraph (m := 3) hset hKc hf le_rfl e htC ht 3 hk
  refine nonempty_siegelSwapParam_of_ctLinParam hcat hdet hsplit hset hKc hf e htC ht P
    fun x hx hxI => ?_
  have hγI : ctGraph 1 x ∈
      blockSpecialLinear ({ctF 4 1 0, ctF 4 1 1} : Finset (Fin (2 * 4 + 1))) := by
    have := ctGraph_mem_blockSpecialLinear_image hxI
    rwa [image_q2Par_pair_ctE] at this
  have hv : ctV 4 ∉ ({ctF 4 1 0, ctF 4 1 1} : Finset (Fin (2 * 4 + 1))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(q2Coord_inl_ne_ctV _).symm, (q2Coord_inl_ne_ctV _).symm⟩
  exact (hP ⟨x, hx⟩).trans (congrArg P.Φ (Subtype.ext
    (ctTorAut_eq_self_of_mem_blockSpecialLinear hv a hγI)))

end Siegel

theorem spLinearFourOrthInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4)
    {κ : Sp2mKind} (hκ : κ = .linearEven ∨ κ = .linearOdd) : SpLinearFourOrthInput κ := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hsplit : OddCentralSplit (siegelLevi K 4) := oddCentralSplit_siegelLevi (by norm_num)
  have hS : Nonempty (SiegelSwapParam e t) := by
    rcases hκ with rfl | rfl
    · exact nonempty_siegelSwapParam_linearEven hcat hdet hsplit hset hKc hf e htC ht (hroot 3)
    · exact nonempty_siegelSwapParam_linearOdd hcat hdet hsplit hset hKc hf e htC ht (hroot 3)
  obtain ⟨S⟩ := hS
  intro a ha b hb
  exact (mem_centralizer_iff.1 (S.pieceCore_zero_le_centralizer_pieceCore_two hq le_rfl ha) b
    hb).symm

theorem spKindCoverInput_linearOdd_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) :
    SpKindCoverInput .linearOdd :=
  spKindCoverInput_linearOdd_of_orth (spLinearFourOrthInput_of_clauses hcat hdet (Or.inr rfl))

end CFSG.SeitzReduction.SymplecticPilot
