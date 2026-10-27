module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinear

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {N ε : ℕ}

theorem commute_of_mem_blockSpecialLinear_of_diag {n : ℕ} {I : Finset (Fin n)}
    {x d : SpecialLinearGroup (Fin n) K} (hx : x ∈ blockSpecialLinear I)
    (hd : ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) K) i j = 0)
    (hconst : ∀ i ∈ I, ∀ j ∈ I, (d : Matrix (Fin n) (Fin n) K) i i =
      (d : Matrix (Fin n) (Fin n) K) j j) : x * d = d * x := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  have h1 : ((x : Matrix (Fin n) (Fin n) K) * (d : Matrix (Fin n) (Fin n) K)) i j =
      (x : Matrix (Fin n) (Fin n) K) i j * (d : Matrix (Fin n) (Fin n) K) j j := by
    rw [mul_apply, Finset.sum_eq_single j (fun k _ hkj => by rw [hd k j hkj, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]
  have h2 : ((d : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)) i j =
      (d : Matrix (Fin n) (Fin n) K) i i * (x : Matrix (Fin n) (Fin n) K) i j := by
    rw [mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hd i k (Ne.symm hki), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
  rw [h1, h2]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [hconst i hij.1 j hij.2, mul_comm]
  · rw [(mem_blockSpecialLinear.mp hx) i j (by tauto)]
    by_cases h : i = j
    · subst h
      rw [one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne h, mul_zero, zero_mul]

theorem ctEmbed_diagSp_apply_ne [CharP K 2] (t : Fin N → Kˣ) {a b : Fin (2 * N + ε)}
    (hab : a ≠ b) :
    ((ctEmbed ε (diagSp K N t) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a b = 0 := by
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  have hww : w ≠ w' := fun h => hab (h ▸ rfl)
  rw [ctEmbed_apply_q2Coord]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, mat_diagSp_apply, ite_eq_right (fun h => hww (congrArg Sum.inl h))]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [fromBlocks_apply₂₂, Matrix.one_apply_ne (fun h => hww (congrArg Sum.inr h))]

theorem ctEmbed_diagSp_apply_self [CharP K 2] (t : Fin N → Kˣ) (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    ((ctEmbed ε (diagSp K N t) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (q2Coord N ε w) (q2Coord N ε w) =
        Sum.elim (diagSpEntry t) (fun _ => 1) w := by
  rw [ctEmbed_apply_q2Coord]
  rcases w with u | i
  · rw [fromBlocks_apply₁₁, mat_diagSp_apply, ite_eq_left rfl]
    rfl
  · rw [fromBlocks_apply₂₂, Matrix.one_apply_eq]
    rfl

theorem diagSp_eq_rootTorusHom_mul (t : Fin N → Kˣ) (k : Fin N) :
    diagSp K N t = rootTorusHom K N k (t k) * diagSp K N (Function.update t k 1) := by
  rw [rootTorusHom_apply, ← map_mul]
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

theorem diagSp_update_mem_spBlock_compl (t : Fin N → Kˣ) (k : Fin N) :
    diagSp K N (Function.update t k 1) ∈ spBlock K ({k} : Finset (Fin N))ᶜ := by
  rw [mem_spBlock]
  intro a b hab
  rw [mat_diagSp_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    have ha : planeOf a = k := by
      by_contra hc
      apply hab
      simp only [mem_planeCoords, Finset.mem_compl, Finset.mem_singleton]
      exact ⟨hc, hc⟩
    rw [ite_eq_left rfl, ite_eq_left rfl]
    rcases a with i | i <;> simp only [planeOf_inl, planeOf_inr] at ha <;> subst ha <;> simp
  · rw [ite_eq_right h, ite_eq_right h]

theorem eq_one_of_mem_center_of_apply_self {n : ℕ} {z : SpecialLinearGroup (Fin n) K}
    (hz : z ∈ center (SpecialLinearGroup (Fin n) K)) {j : Fin n}
    (hj : (z : Matrix (Fin n) (Fin n) K) j j = 1) : z = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr1 : r = 1 := by
    rw [← hr] at hj
    simpa using hj
  apply Subtype.ext
  rw [← hr, hr1]
  simp

theorem injOn_blockSpecialLinear_of_ker_le_center {n : ℕ} {G : Type*} [Group G]
    {ψ : SpecialLinearGroup (Fin n) K →* G}
    (hker : ψ.ker ≤ center (SpecialLinearGroup (Fin n) K)) {I : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ I) {x y : SpecialLinearGroup (Fin n) K} (hx : x ∈ blockSpecialLinear I)
    (hy : y ∈ blockSpecialLinear I) (hxy : ψ x = ψ y) : x = y := by
  have hm : x * y⁻¹ ∈ blockSpecialLinear I := mul_mem hx (inv_mem hy)
  have hk : x * y⁻¹ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  have h1 := eq_one_of_mem_center_of_apply_self (hker hk) (j := j) (by
    rw [(mem_blockSpecialLinear.mp hm) j j (by tauto), one_apply_eq])
  exact mul_inv_eq_one.1 h1

section Pieces

variable {G : Type*} [Group G] {L : Subgroup G} [CharP K 2] {e : L ≃* StatedSp N K}

theorem CtLinParam.mem_pieceCore [Finite K] (hK : 4 ≤ Nat.card K) {k : Fin N}
    (P : CtLinParam ε e k) {I : Finset (Fin (2 * N + ε))} (hI2 : 2 ≤ I.card)
    (hIk : I ⊆ (planeCoordsQ2 ε {k})ᶜ) {J : Finset (Fin N)}
    (hconst : ∀ t ∈ leviTorusParam K J, ∀ a ∈ I, ∀ b ∈ I,
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a =
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) b b)
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ blockSpecialLinear I) :
    P.Φ ⟨x, LinearPilot.blockSpecialLinear_mono hIk hx⟩ ∈ pieceCore e J := by
  set H : Subgroup (q2Block ε K {k}) := (blockSpecialLinear I).subgroupOf (q2Block ε K {k})
    with hH
  have hHmap : H.map (q2Block ε K {k}).subtype = blockSpecialLinear I := by
    rw [hH, subgroupOf_map_subtype, inf_eq_left.mpr
      (show blockSpecialLinear I ≤ q2Block ε K {k} from LinearPilot.blockSpecialLinear_mono hIk)]
  have hHperf : ⁅H, H⁆ = H := by
    apply Subgroup.map_injective (q2Block ε K {k}).subtype_injective
    rw [map_commutator, hHmap, LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hI2 hK]
  have hmem : (⟨x, LinearPilot.blockSpecialLinear_mono hIk hx⟩ : q2Block ε K {k}) ∈ H := hx
  have hcent : H.map P.Φ ≤ centralizer (modelToG e (leviTorusSp K J) : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨d, ⟨t, ht, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    rw [diagSp_eq_rootTorusHom_mul t k, map_mul, Subgroup.coe_mul]
    have h1 : P.Φ z ∈ centralizer (modelToG e (rootTorusSp K k) : Set G) := by
      have : P.Φ z ∈ neighbourCore e k := P.range_eq ▸ ⟨z, rfl⟩
      exact F4Pilot.centralizerPerfectCore_le_centralizer _ this
    have h2 := mem_centralizer_iff.1 h1 _
      (UnitaryPilot.symm_mem_modelToG e ⟨t k, rfl⟩)
    have hd := diagSp_update_mem_spBlock_compl (K := K) t k
    have h3 : ((e.symm (diagSp K N (Function.update t k 1)) : L) : G) =
        P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), ctEmbed_mem_q2Block_iff.2 hd⟩ :=
      (P.N1 _ hd).symm
    have hzc : (z : SpecialLinearGroup (Fin (2 * N + ε)) K) *
        ctEmbed ε (diagSp K N (Function.update t k 1)) =
        ctEmbed ε (diagSp K N (Function.update t k 1)) * z :=
      commute_of_mem_blockSpecialLinear_of_diag (I := I) hz
        (fun a b hab => ctEmbed_diagSp_apply_ne _ hab) (hconst t ht)
    have h4 : P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), ctEmbed_mem_q2Block_iff.2 hd⟩ *
        P.Φ z = P.Φ z * P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)),
          ctEmbed_mem_q2Block_iff.2 hd⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzc.symm
    rw [h3]
    calc ((e.symm (rootTorusHom K N k (t k)) : L) : G) *
          P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), _⟩ * P.Φ z
        = ((e.symm (rootTorusHom K N k (t k)) : L) : G) * (P.Φ z *
          P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), _⟩) := by rw [mul_assoc, h4]
      _ = P.Φ z * (((e.symm (rootTorusHom K N k (t k)) : L) : G) *
          P.Φ ⟨ctEmbed ε (diagSp K N (Function.update t k 1)), _⟩) := by
          rw [← mul_assoc, h2, mul_assoc]
  have hle : H.map P.Φ ≤ pieceCore e J :=
    CFSG.Quasithin.le_perfectCore_of_perfect hcent (by rw [← map_commutator, hHperf])
  exact hle ⟨_, hmem, rfl⟩

omit [CharP K 2] in
theorem transvection_mem_q2Block {k : Fin N} {a b : Fin (2 * N + ε)} (hab : a ≠ b)
    (ha : a ∉ planeCoordsQ2 ε {k}) (hb : b ∉ planeCoordsQ2 ε {k}) (c : K) :
    SpecialLinearGroup.transvection hab c ∈ q2Block ε K {k} :=
  LinearPilot.transvection_mem_blockSpecialLinear hab (Finset.mem_compl.2 ha)
    (Finset.mem_compl.2 hb) c

theorem q2Coord_inl_notMem {k p : Fin N} (hpk : p ≠ k) (u : Fin N ⊕ Fin N) (hu : planeOf u = p) :
    q2Coord N ε (Sum.inl u) ∉ planeCoordsQ2 ε {k} := by
  rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl, Finset.mem_singleton, hu]
  exact hpk

theorem q2Coord_inr_notMem {k : Fin N} (i : Fin ε) :
    q2Coord N ε (Sum.inr i) ∉ planeCoordsQ2 ε {k} := by
  rw [q2Coord_mem_planeCoordsQ2]
  exact not_inPlanes_inr _ _

theorem CtLinParam.transvection_plane_mem_spGlobal [Finite K] (hK : 4 ≤ Nat.card K) (hN : 1 ≤ N)
    {k : Fin N} (P : CtLinParam ε e k) {p : Fin N} (hpk : p ≠ k) (c : K) (hx₁ hx₂) :
    P.Φ ⟨SpecialLinearGroup.transvection (ctPlaneNe (ε := ε) p) c, hx₁⟩ ∈ spGlobal e ∧
      P.Φ ⟨SpecialLinearGroup.transvection (ctPlaneNe (ε := ε) p).symm c, hx₂⟩ ∈ spGlobal e := by
  have hp : p ∈ ({k} : Finset (Fin N))ᶜ := by simpa using hpk
  have hLG := le_spGlobal hK hN e
  constructor
  · have h1 : SpecialLinearGroup.transvection (ctPlaneNe (ε := ε) p) c =
        ctEmbed ε (longBlock K N p (CFSG.LieType.Steinberg.sl2Upper c)) := by
      rw [ctEmbed_longBlock, pairEmbed_sl2Upper]
    have hy := longBlock_mem_spBlock hp (CFSG.LieType.Steinberg.sl2Upper c)
    have h2 := P.N1 _ hy
    have h3 : (⟨SpecialLinearGroup.transvection (ctPlaneNe (ε := ε) p) c, hx₁⟩ :
        q2Block ε K {k}) = ⟨_, ctEmbed_mem_q2Block_iff.2 hy⟩ := Subtype.ext h1
    rw [h3, h2]
    exact hLG (e.symm _).2
  · have h1 : SpecialLinearGroup.transvection (ctPlaneNe (ε := ε) p).symm c =
        ctEmbed ε (longBlock K N p (CFSG.LieType.Steinberg.sl2Lower c)) := by
      rw [ctEmbed_longBlock, pairEmbed_sl2Lower]
    have hy := longBlock_mem_spBlock hp (CFSG.LieType.Steinberg.sl2Lower c)
    have h2 := P.N1 _ hy
    have h3 : (⟨SpecialLinearGroup.transvection (ctPlaneNe (ε := ε) p).symm c, hx₂⟩ :
        q2Block ε K {k}) = ⟨_, ctEmbed_mem_q2Block_iff.2 hy⟩ := Subtype.ext h1
    rw [h3, h2]
    exact hLG (e.symm _).2

theorem CtLinParam.transvection_short_mem_spGlobal [Finite K] (hK : 4 ≤ Nat.card K)
    {k : Fin N} (P : CtLinParam ε e k) {p p' : Fin N} (hp' : p'.val = p.val + 1)
    (hpk : p ≠ k) (hp'k : p' ≠ k) (c : K)
    (hab : q2Coord N ε (Sum.inl (Sum.inl p)) ≠ q2Coord N ε (Sum.inl (Sum.inl p'))) (hx₁ hx₂) :
    P.Φ ⟨SpecialLinearGroup.transvection hab c, hx₁⟩ ∈ spGlobal e ∧
      P.Φ ⟨SpecialLinearGroup.transvection hab.symm c, hx₂⟩ ∈ spGlobal e := by
  set I : Finset (Fin (2 * N + ε)) :=
    {q2Coord N ε (Sum.inl (Sum.inl p)), q2Coord N ε (Sum.inl (Sum.inl p'))} with hI
  have hI2 : 2 ≤ I.card := by rw [hI, Finset.card_pair hab]
  have hIk : I ⊆ (planeCoordsQ2 ε {k})ᶜ := by
    intro a ha
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact q2Coord_inl_notMem hpk _ rfl
    · rw [Finset.mem_singleton.1 ha]
      exact q2Coord_inl_notMem hp'k _ rfl
  have hconst : ∀ t ∈ leviTorusParam K ({p} : Finset (Fin N)), ∀ a ∈ I, ∀ b ∈ I,
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a =
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) b b := by
    intro t ht
    have htp : t p = t p' := by
      have h1 := ((mem_leviTorusParam.1 ht) p (Finset.mem_singleton_self p)).1 (by omega)
      rw [h1]
      congr 1
      exact Fin.ext hp'.symm
    have hval : ∀ a ∈ I,
        ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a = ((t p : Kˣ) : K) := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [ctEmbed_diagSp_apply_self]
        simp [Function.update_of_ne hpk]
      · rw [Finset.mem_singleton.1 ha, ctEmbed_diagSp_apply_self]
        simp [Function.update_of_ne hp'k, htp]
    intro a ha b hb
    rw [hval a ha, hval b hb]
  have hmem : ∀ x ∈ blockSpecialLinear I, ∀ hx : x ∈ q2Block ε K {k},
      P.Φ ⟨x, hx⟩ ∈ spGlobal e := by
    intro x hx hx'
    have h := P.mem_pieceCore hK hI2 hIk hconst hx
    exact le_iSup (fun j : Fin N => pieceCore e ({j} : Finset (Fin N))) p h
  refine ⟨hmem _ (LinearPilot.transvection_mem_blockSpecialLinear hab (by simp [hI])
    (by simp [hI]) c) _, hmem _ (LinearPilot.transvection_mem_blockSpecialLinear hab.symm
    (by simp [hI]) (by simp [hI]) c) _⟩

theorem CtLinParam.transvection_rad_mem_spGlobal [Finite K] (hK : 4 ≤ Nat.card K)
    {k : Fin N} (P : CtLinParam ε e k) {p : Fin N} (hp : p.val + 1 = N) (hpk : p ≠ k)
    (i : Fin ε) (c : K)
    (hab : q2Coord N ε (Sum.inl (Sum.inr p)) ≠ q2Coord N ε (Sum.inr i)) (hx₁ hx₂) :
    P.Φ ⟨SpecialLinearGroup.transvection hab c, hx₁⟩ ∈ spGlobal e ∧
      P.Φ ⟨SpecialLinearGroup.transvection hab.symm c, hx₂⟩ ∈ spGlobal e := by
  set I : Finset (Fin (2 * N + ε)) :=
    {q2Coord N ε (Sum.inl (Sum.inr p)), q2Coord N ε (Sum.inr i)} with hI
  have hI2 : 2 ≤ I.card := by rw [hI, Finset.card_pair hab]
  have hIk : I ⊆ (planeCoordsQ2 ε {k})ᶜ := by
    intro a ha
    rw [Finset.mem_compl]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact q2Coord_inl_notMem hpk _ rfl
    · rw [Finset.mem_singleton.1 ha]
      exact q2Coord_inr_notMem i
  have hconst : ∀ t ∈ leviTorusParam K ({p} : Finset (Fin N)), ∀ a ∈ I, ∀ b ∈ I,
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a =
      ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) b b := by
    intro t ht
    have htp : t p = 1 := ((mem_leviTorusParam.1 ht) p (Finset.mem_singleton_self p)).2 hp
    have hval : ∀ a ∈ I,
        ((ctEmbed ε (diagSp K N (Function.update t k 1)) : SpecialLinearGroup (Fin (2 * N + ε)) K) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a a = 1 := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [ctEmbed_diagSp_apply_self]
        simp [Function.update_of_ne hpk, htp]
      · rw [Finset.mem_singleton.1 ha, ctEmbed_diagSp_apply_self]
        rfl
    intro a ha b hb
    rw [hval a ha, hval b hb]
  have hmem : ∀ x ∈ blockSpecialLinear I, ∀ hx : x ∈ q2Block ε K {k},
      P.Φ ⟨x, hx⟩ ∈ spGlobal e := by
    intro x hx hx'
    have h := P.mem_pieceCore hK hI2 hIk hconst hx
    exact le_iSup (fun j : Fin N => pieceCore e ({j} : Finset (Fin N))) p h
  refine ⟨hmem _ (LinearPilot.transvection_mem_blockSpecialLinear hab (by simp [hI])
    (by simp [hI]) c) _, hmem _ (LinearPilot.transvection_mem_blockSpecialLinear hab.symm
    (by simp [hI]) (by simp [hI]) c) _⟩

theorem CtLinParam.commutator_mem_spGlobal {k : Fin N} (P : CtLinParam ε e k)
    {x y : q2Block ε K {k}} (hx : P.Φ x ∈ spGlobal e) (hy : P.Φ y ∈ spGlobal e) :
    P.Φ ⁅x, y⁆ ∈ spGlobal e := by
  rw [map_commutatorElement, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem CtLinParam.transvection_mixed_mem_spGlobal [Finite K] (hK : 4 ≤ Nat.card K)
    (hN : 1 ≤ N) {k : Fin N} (P : CtLinParam ε e k) {p p' : Fin N} (hp' : p'.val = p.val + 1)
    (hpk : p ≠ k) (hp'k : p' ≠ k) (c : K)
    (hab : q2Coord N ε (Sum.inl (Sum.inr p)) ≠ q2Coord N ε (Sum.inl (Sum.inl p'))) (hx₁ hx₂) :
    P.Φ ⟨SpecialLinearGroup.transvection hab c, hx₁⟩ ∈ spGlobal e ∧
      P.Φ ⟨SpecialLinearGroup.transvection hab.symm c, hx₂⟩ ∈ spGlobal e := by
  have hpp : p ≠ p' := fun h => by
    have := congrArg Fin.val h
    omega
  have hee : q2Coord N ε (Sum.inl (Sum.inl p)) ≠ q2Coord N ε (Sum.inl (Sum.inl p')) :=
    fun h => hpp (Sum.inl.inj (Sum.inl.inj ((q2Coord N ε).injective h)))
  have hk1 := fun (u : Fin N ⊕ Fin N) (q : Fin N) (hq : q ≠ k) (hu : planeOf u = q) =>
    q2Coord_inl_notMem (ε := ε) hq u hu
  have hfe := (ctPlaneNe (ε := ε) p).symm
  have hef := ctPlaneNe (ε := ε) p
  have mfe := (P.transvection_plane_mem_spGlobal hK hN hpk c
    (transvection_mem_q2Block hef (hk1 _ p hpk rfl) (hk1 _ p hpk rfl) c)
    (transvection_mem_q2Block hfe (hk1 _ p hpk rfl) (hk1 _ p hpk rfl) c)).2
  have mef := (P.transvection_plane_mem_spGlobal hK hN hpk 1
    (transvection_mem_q2Block hef (hk1 _ p hpk rfl) (hk1 _ p hpk rfl) 1)
    (transvection_mem_q2Block hfe (hk1 _ p hpk rfl) (hk1 _ p hpk rfl) 1)).1
  have mee := (P.transvection_short_mem_spGlobal hK hp' hpk hp'k 1 hee
    (transvection_mem_q2Block hee (hk1 _ p hpk rfl) (hk1 _ p' hp'k rfl) 1)
    (transvection_mem_q2Block hee.symm (hk1 _ p' hp'k rfl) (hk1 _ p hpk rfl) 1)).1
  have mee' := (P.transvection_short_mem_spGlobal hK hp' hpk hp'k c hee
    (transvection_mem_q2Block hee (hk1 _ p hpk rfl) (hk1 _ p' hp'k rfl) c)
    (transvection_mem_q2Block hee.symm (hk1 _ p' hp'k rfl) (hk1 _ p hpk rfl) c)).2
  constructor
  · have h := P.commutator_mem_spGlobal mfe mee
    convert h using 2
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← commutatorElement_def, SpecialLinearGroup.commutatorElement_transvection hfe hee hab,
      mul_one]
  · have h := P.commutator_mem_spGlobal mee' mef
    convert h using 2
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← commutatorElement_def,
      SpecialLinearGroup.commutatorElement_transvection hee.symm hef hab.symm, mul_one]

theorem CtLinParam.transvection_adjacent_mem_spGlobal [Finite K] (hK : 4 ≤ Nat.card K)
    (hε : ε ≤ 1) (hN : 1 ≤ N) {k : Fin N} (P : CtLinParam ε e k) {a b : Fin (2 * N + ε)}
    (hab : a ≠ b) (hba : b.val = a.val + 1) (ha : a ∉ planeCoordsQ2 ε {k})
    (hb : b ∉ planeCoordsQ2 ε {k}) (c : K) (hx₁ hx₂) :
    P.Φ ⟨SpecialLinearGroup.transvection hab c, hx₁⟩ ∈ spGlobal e ∧
      P.Φ ⟨SpecialLinearGroup.transvection hab.symm c, hx₂⟩ ∈ spGlobal e := by
  have hplane : ∀ (u : Fin N ⊕ Fin N), q2Coord N ε (Sum.inl u) ∉ planeCoordsQ2 ε {k} →
      planeOf u ≠ k := by
    intro u hu h
    apply hu
    rw [q2Coord_mem_planeCoordsQ2, inPlanes_inl, Finset.mem_singleton]
    exact h
  have hbN := b.2
  rcases Nat.even_or_odd a.val with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hpN : p < N := by omega
    obtain rfl : a = q2Coord N ε (Sum.inl (Sum.inl ⟨p, hpN⟩)) := Fin.ext (by simp; omega)
    obtain rfl : b = q2Coord N ε (Sum.inl (Sum.inr ⟨p, hpN⟩)) := Fin.ext (by simp; omega)
    exact P.transvection_plane_mem_spGlobal hK hN (hplane _ ha) c hx₁ hx₂
  · have hpN : p < N := by omega
    obtain rfl : a = q2Coord N ε (Sum.inl (Sum.inr ⟨p, hpN⟩)) := Fin.ext (by simp; omega)
    by_cases hlast : 2 * p + 2 < 2 * N
    · have hp1 : p + 1 < N := by omega
      obtain rfl : b = q2Coord N ε (Sum.inl (Sum.inl ⟨p + 1, hp1⟩)) :=
        Fin.ext (by simp only [q2Coord_inl_inl]; simp at hba; omega)
      exact P.transvection_mixed_mem_spGlobal hK hN rfl (hplane _ ha) (hplane _ hb) c hab hx₁ hx₂
    · have hε1 : ε = 1 := by simp at hba; omega
      subst hε1
      obtain rfl : b = q2Coord N 1 (Sum.inr 0) := Fin.ext (by simp at hba ⊢; omega)
      exact P.transvection_rad_mem_spGlobal hK (show p + 1 = N by omega) (hplane _ ha) 0 c hab
        hx₁ hx₂

end Pieces

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [CharP K 2] {e : L ≃* StatedSp N K}

theorem exists_ct_linRow_of_agree [Finite K] {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hε : ε ≤ 1) (hN : 5 ≤ N) (P : ∀ k : Fin N, CtLinParam ε e k)
    (hagree : CtLinParamAgree P) :
    ∃ ψ : SpecialLinearGroup (Fin (2 * N + ε)) K →* G, ψ.range = spGlobal e ∧
      ψ.ker ≤ center (SpecialLinearGroup (Fin (2 * N + ε)) K) ∧
      CFSG.IsQuasisimple (spGlobal e) ∧ Odd (Nat.card (center (spGlobal e))) ∧
      LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL (2 * N + ε) 2 f := by
  classical
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * N + ε := ⟨2 * N + ε - 1, by omega⟩
  choose kJ hkJ using fun J : {J : Finset (Fin m) // J.card ≤ 2} =>
    exists_plane_notMem_of_card_le_two hm hN J.1 J.2
  have hKle : ∀ (J : {J : Finset (Fin m) // J.card ≤ 2})
      (x : (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ q2Block ε K {kJ J} := by
    intro J x
    have hx : (x : SpecialLinearGroup (Fin (m + 1)) K) ∈
        CFSG.LieType.Universal.SpecialLinear.levi m K J.1 := by
      rw [← CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
      exact x.2
    exact map_levi_le_q2Block hm (hkJ J) ⟨x, hx, rfl⟩
  set φ : ∀ J, (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G :=
    fun J => (P (kJ J)).Φ.comp
      (((q2CastSL hm).toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ (hKle J)) with hφ
  have hφapp : ∀ J x, φ J x = (P (kJ J)).Φ ⟨q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K),
      hKle J x⟩ := fun _ _ => rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ := by
    intro I J _ x y hxy
    rw [hφapp, hφapp]
    have hy' : q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ q2Block ε K {kJ J} := by
      rw [hxy]; exact hKle J y
    rw [hagree (kJ I) (kJ J) _ (hKle I x) hy']
    congr 2
    rw [hxy]
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J →* G₀ :=
    fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hm0 : 0 < m := by omega
    set j₀ : Fin m := ⟨0, hm0⟩ with hj₀
    set J₀ : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j₀}, by simp⟩ with hJ₀
    have hx₀ : SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K) ∈
        (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J₀ := by
      have h1 : SpecialLinearGroup.transvection
          (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K) ∈
          CFSG.LieType.CurtisTits.levi (CFSG.LieType.Universal.SpecialLinear.rootGroup m K)
            ({j₀} : Finset (Fin m)) := by
        rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
        have hlevi : CFSG.LieType.Universal.SpecialLinear.fundamentalRootSubgroup m K j₀ true ≤
            CFSG.LieType.Universal.SpecialLinear.levi m K {j₀} :=
          le_iSup_of_le j₀ (le_iSup_of_le (Finset.mem_singleton_self j₀)
            (le_iSup (fun s => CFSG.LieType.Universal.SpecialLinear.fundamentalRootSubgroup m K j₀
              s) true))
        exact hlevi (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup _ 1)
      exact h1
    refine ⟨J₀, ⟨_, hx₀⟩, fun h => ?_⟩
    have h1 : (P (kJ J₀)).Φ ⟨q2CastSL hm (SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K)),
        hKle J₀ ⟨_, hx₀⟩⟩ = 1 := congrArg Subtype.val h
    set p₀ : Fin N := ⟨0, by omega⟩ with hp₀
    have hpk : p₀ ≠ kJ J₀ := by
      intro hpk
      have h2 := (hkJ J₀ j₀ (Finset.mem_singleton_self j₀)).1
      rw [← hpk] at h2
      apply h2
      rw [mem_planeCoordsQ2_iff]
      exact ⟨by simp [hj₀]; omega, by simp [hp₀, hj₀]⟩
    have hy := longBlock_mem_spBlock (K := K) (show p₀ ∈ ({kJ J₀} : Finset (Fin N))ᶜ by
      simpa using hpk) (CFSG.LieType.Steinberg.sl2Upper 1)
    have hcast : q2CastSL hm (SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K)) =
        ctEmbed ε (longBlock K N p₀ (CFSG.LieType.Steinberg.sl2Upper 1)) := by
      rw [q2CastSL_transvection, ctEmbed_longBlock, pairEmbed_sl2Upper]
      congr 1
    have h3 : (⟨q2CastSL hm (SpecialLinearGroup.transvection
        (show j₀.castSucc < j₀.succ from Fin.castSucc_lt_succ).ne (1 : K)), hKle J₀ ⟨_, hx₀⟩⟩ :
        q2Block ε K {kJ J₀}) = ⟨_, ctEmbed_mem_q2Block_iff.2 hy⟩ := Subtype.ext hcast
    rw [h3, (P (kJ J₀)).N1 _ hy] at h1
    have h4 : e.symm (longBlock K N p₀ (CFSG.LieType.Steinberg.sl2Upper 1)) = 1 :=
      Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h4
    have h5 : CFSG.LieType.Steinberg.sl2Upper (1 : K) = 1 :=
      longBlock_injective p₀ (h4.trans (map_one _).symm)
    have h6 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h5
    simp [CFSG.LieType.Steinberg.sl2Upper] at h6
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f :=
    ⟨Nat.prime_two, by omega, by omega, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_specialLinear.{0} (F := K) hadm hKc
      (by omega : 3 ≤ m)
  obtain ⟨ψ₀, hψ₀, hsurj, hker, hqs, -, -, hLM⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SpecialLinearGroup (Fin (2 * N + ε)) K →* G :=
    (G₀.subtype.comp ψ₀).comp (q2CastSL hm).symm.toMonoidHom with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hψφ : ∀ J (x : (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J),
      ψ (q2CastSL hm x) = φ J x := by
    intro J x
    change ((ψ₀ ((q2CastSL hm).symm (q2CastSL hm x)) : G₀) : G) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SpecialLinearGroup (Fin (2 * N + ε)) K) := by
    intro z hz
    have hz₀ : (q2CastSL hm).symm z ∈ ψ₀.ker := by
      rw [MonoidHom.mem_ker]
      apply G₀.subtype_injective
      rw [map_one]
      exact hz
    have hc := hker hz₀
    rw [mem_center_iff] at hc ⊢
    intro g
    have := hc ((q2CastSL hm).symm g)
    apply (q2CastSL hm).symm.injective
    rw [map_mul, map_mul]
    exact this
  have hG₀le : G₀ ≤ spGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    rw [hφapp]
    set k := kJ J with hk
    set A : Subgroup (SpecialLinearGroup (Fin (2 * N + ε)) K) :=
      ((spGlobal e).comap (P k).Φ).map (q2Block ε K {k}).subtype with hA
    have hAle : (CFSG.LieType.Universal.SpecialLinear.levi m K J.1).map
        (q2CastSL hm).toMonoidHom ≤ A := by
      unfold CFSG.LieType.Universal.SpecialLinear.levi
      rw [Subgroup.map_iSup]
      refine iSup_le fun j => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hj => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun s => ?_
      rintro _ ⟨y, hy, rfl⟩
      have hab : finCongr hm j.castSucc ≠ finCongr hm j.succ := fun h =>
        (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne ((finCongr hm).injective h)
      have hba : (finCongr hm j.succ).val = (finCongr hm j.castSucc).val + 1 := by simp
      have key := (P k).transvection_adjacent_mem_spGlobal hK4 hε (by omega) hab hba
        (hkJ J j hj).1 (hkJ J j hj).2
      cases s
      · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ y).1 hy
        rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
        have hmem := transvection_mem_q2Block hab.symm (hkJ J j hj).2 (hkJ J j hj).1 c
        exact ⟨⟨_, hmem⟩, (key c (transvection_mem_q2Block hab (hkJ J j hj).1 (hkJ J j hj).2 c)
          hmem).2, rfl⟩
      · obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ y).1 hy
        rw [MulEquiv.coe_toMonoidHom, q2CastSL_transvection]
        have hmem := transvection_mem_q2Block hab (hkJ J j hj).1 (hkJ J j hj).2 c
        exact ⟨⟨_, hmem⟩, (key c hmem
          (transvection_mem_q2Block hab.symm (hkJ J j hj).2 (hkJ J j hj).1 c)).1, rfl⟩
    have hx : (x : SpecialLinearGroup (Fin (m + 1)) K) ∈
        CFSG.LieType.Universal.SpecialLinear.levi m K J.1 :=
      (CFSG.LieType.Universal.SpecialLinear.levi_rootGroup (m := m) (F := K) J.1) ▸ x.2
    obtain ⟨y, hy, hyx⟩ := hAle ⟨_, hx, rfl⟩
    have hy' : (⟨q2CastSL hm (x : SpecialLinearGroup (Fin (m + 1)) K), hKle J x⟩ :
        q2Block ε K {k}) = y := Subtype.ext hyx.symm
    rw [hy']
    exact hy
  have hEk : ∀ k : Fin N, neighbourCore e k ≤ G₀ := by
    intro k
    obtain ⟨j, hj⟩ : ∃ j : Fin m, j.val = 2 * k.val := ⟨⟨2 * k.val, by have := k.2; omega⟩, rfl⟩
    set J : {J : Finset (Fin m) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hkk : kJ J ≠ k := by
      intro hkk
      have h1 := (hkJ J j (Finset.mem_singleton_self j)).1
      rw [hkk] at h1
      apply h1
      rw [mem_planeCoordsQ2_iff]
      refine ⟨by have := k.2; simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega,
        ?_⟩
      rw [Finset.mem_singleton]
      exact Fin.ext (by simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]; omega)
    have hψx : ∀ x ∈ spBlock K ({k} : Finset (Fin N)),
        ψ (ctEmbed ε x) = ((e.symm x : L) : G) := by
      intro x hx
      have hc : ctEmbed ε x ∈ (CFSG.LieType.Universal.SpecialLinear.levi m K {j}).map
          (q2CastSL hm).toMonoidHom := by
        refine blockSpecialLinear_plane_le_map_levi hm k j hj ?_
        have := ctEmbed_mem_blockSpecialLinear_planeCoordsQ2 (ε := ε) hx
        rwa [planeCoordsQ2_singleton] at this
      obtain ⟨x₀, hx₀, hx₀c⟩ := hc
      have hx₀' : x₀ ∈ (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).leviAmalgam J := by
        have h1 : x₀ ∈ CFSG.LieType.CurtisTits.levi
            (CFSG.LieType.Universal.SpecialLinear.rootGroup m K) ({j} : Finset (Fin m)) := by
          rw [CFSG.LieType.Universal.SpecialLinear.levi_rootGroup]
          exact hx₀
        exact h1
      have hxk : x ∈ spBlock K ({kJ J} : Finset (Fin N))ᶜ :=
        spBlock_mono (by simpa using hkk) hx
      rw [MulEquiv.coe_toMonoidHom] at hx₀c
      have h1 := hψφ J ⟨x₀, hx₀'⟩
      change ψ (q2CastSL hm x₀) = _ at h1
      rw [← hx₀c, h1, show φ J ⟨x₀, hx₀'⟩ = (P (kJ J)).Φ ⟨q2CastSL hm x₀, hKle J ⟨x₀, hx₀'⟩⟩
        from rfl]
      have h2 : (⟨q2CastSL hm (x₀ : SpecialLinearGroup (Fin (m + 1)) K), hKle J ⟨x₀, hx₀'⟩⟩ :
          q2Block ε K {kJ J}) = ⟨ctEmbed ε x, ctEmbed_mem_q2Block_iff.2 hxk⟩ :=
        Subtype.ext hx₀c
      rw [h2]
      exact (P (kJ J)).N1 x hxk
    have hblock : (q2Block ε K {k}).map ψ ≤ neighbourCore e k := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
        have hx' : x ∈ spBlock K ({k} : Finset (Fin N)) := by
          rw [spBlock_singleton]
          exact rootTorusSp_le_longRootSp2 k hx
        rw [← hψx x hx', ← map_mul, ← map_mul]
        congr 1
        exact (LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right
          (ctEmbed_mem_blockSpecialLinear_planeCoordsQ2 (ε := ε) hx') hz).eq
      · have hcard : 3 ≤ ((planeCoordsQ2 ε ({k} : Finset (Fin N)))ᶜ).card := by
          rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
          omega
        rw [← map_commutator, commutator_q2Block_eq hcard]
    have hcardE : Nat.card (neighbourCore e k) ≤ Nat.card ((q2Block ε K {k}).map ψ) := by
      have hinj : Function.Injective (ψ.comp (q2Block ε K {k}).subtype) := by
        intro x y hxy
        apply Subtype.ext
        refine injOn_blockSpecialLinear_of_ker_le_center hψker
          (j := q2Coord N ε (Sum.inl (Sum.inl k))) ?_ x.2 y.2 hxy
        rw [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2, inPlanes_inl]
        simp
      have h1 : Nat.card ((q2Block ε K {k}).map ψ) = Nat.card (q2Block ε K {k}) := by
        have h2 : (q2Block ε K {k}).map ψ = (ψ.comp (q2Block ε K {k}).subtype).range := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [h2]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rw [h1, ← (P k).range_eq]
      exact Nat.card_le_card_of_surjective _ (P k).Φ.rangeRestrict_surjective
    have heq := Subgroup.eq_of_le_of_card_ge hblock hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have hG₀eq : G₀ = spGlobal e := le_antisymm hG₀le
    ((spGlobal_le_iSup_neighbourCore (by omega) e).trans (iSup_le hEk))
  clear_value G₀
  subst hG₀eq
  refine ⟨ψ, hψrange, hψker, hqs,
    odd_card_center_of_surjective_specialLinear hKc (by omega) (by omega) hsurj hker, ?_⟩
  rw [← hm]
  exact hLM

theorem spGlobalCoverType_of_ctLinParamAgree [Finite K] {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hN : 5 ≤ N) {κ : Sp2mKind}
    (hκ : (κ = .linearEven ∧ ε = 0) ∨ (κ = .linearOdd ∧ ε = 1))
    (P : ∀ k : Fin N, CtLinParam ε e k) (hagree : CtLinParamAgree P) :
    SpGlobalCoverType e f κ := by
  have hε : ε ≤ 1 := by rcases hκ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  obtain ⟨-, -, -, hqs, hodd, hLM⟩ := exists_ct_linRow_of_agree hKc hf hε hN P hagree
  refine ⟨hqs, hodd, ?_⟩
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hLM
  · exact hLM

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
