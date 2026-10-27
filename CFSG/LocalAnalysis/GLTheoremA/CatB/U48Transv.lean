module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open Matrix CFSG.LocalAnalysis.GLTheoremA
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

def CenIn (r : ℕ) {H : Type} [Group H] (x : H) : Prop :=
  ∃ P : Subgroup H, IsPGroup r P ∧ x ∈ P ∧ P ≤ Subgroup.centralizer ({x} : Set H) ∧
    ∀ Q : Subgroup H, P ≤ Q → IsPGroup r Q → Q = P

theorem CenIn.congr {r : ℕ} {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {x : H}
    (hx : CenIn r x) : CenIn r (e x) := by
  obtain ⟨P, hP, hxP, hPC, hmax⟩ := hx
  refine ⟨P.map e.toMonoidHom, hP.map e.toMonoidHom, Subgroup.mem_map_of_mem _ hxP, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hc : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp (hPC hu)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e u * e x = e x * e u
    rw [← map_mul, ← map_mul, hc]
  · intro Q' hQ' hQ'p
    have hQ : P ≤ Q'.comap e.toMonoidHom := fun u hu =>
      hQ' (Subgroup.mem_map_of_mem _ hu)
    have hQp : IsPGroup r (Q'.comap e.toMonoidHom) := hQ'p.comap_of_injective _ e.injective
    have hEq := hmax _ hQ hQp
    have hs : Function.Surjective e.toMonoidHom := e.surjective
    rw [← Subgroup.map_comap_eq_self_of_surjective hs Q', hEq]

theorem isCentralIn_iff_cenIn {G : Type} [Group G] (r : ℕ) (K : Subgroup G) {z : G} (hz : z ∈ K) :
    IsCentralIn r z K ↔ CenIn r (⟨z, hz⟩ : K) := by
  constructor
  · rintro ⟨-, P, hPK, hP, hzP, hPC, hmax⟩
    refine ⟨P.comap K.subtype, hP.comap_subtype, hzP, ?_, ?_⟩
    · intro y hy
      have hc : (y : G) * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hPC hy)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hc
    · intro Q' hQ' hQ'p
      have hQ : P ≤ Q'.map K.subtype := fun g hg =>
        Subgroup.mem_map.mpr ⟨⟨g, hPK hg⟩, hQ' (show (⟨g, hPK hg⟩ : K) ∈ P.comap K.subtype from hg),
          rfl⟩
      have hQK : Q'.map K.subtype ≤ K := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have hEq := hmax _ hQ hQK (hQ'p.map K.subtype)
      rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q', hEq]
  · rintro ⟨P', hP', hzP', hPC', hmax⟩
    refine ⟨hz, P'.map K.subtype, ?_, hP'.map K.subtype, Subgroup.mem_map_of_mem _ hzP', ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      have h2 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hPC' hy))
      have hc : (y : G) * z = z * (y : G) := by simpa using h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc
    · intro Q hQ hQK hQp
      have hQ' : P' ≤ Q.comap K.subtype := fun y hy => hQ (Subgroup.mem_map_of_mem _ hy)
      have hEq := hmax _ hQ' hQp.comap_subtype
      have hrange : Q ≤ K.subtype.range := by rwa [Subgroup.range_subtype]
      rw [← Subgroup.map_comap_eq_self hrange, hEq]


section Transvection

variable {f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def wMat (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => w i * h.bar (w j)

@[expose] noncomputable def vnorm (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) : K :=
  ∑ i, w i * h.bar (w i)

@[expose] noncomputable def tvMat (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K) :
    Matrix (Fin 4) (Fin 4) K :=
  1 + c • wMat h w

@[expose] def IsIsoVec (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) : Prop := w ≠ 0 ∧ vnorm h w = 0

theorem wMat_mul_wMat (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) :
    wMat h w * wMat h w = vnorm h w • wMat h w := by
  ext i k
  simp only [wMat, Matrix.mul_apply, Matrix.of_apply, vnorm, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tvMat_mul_tvMat (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K)
    (hw : vnorm h w = 0) : tvMat h w c * tvMat h w (-c) = 1 := by
  have hWW : wMat h w * wMat h w = 0 := by rw [wMat_mul_wMat, hw, zero_smul]
  unfold tvMat
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hWW, smul_zero, add_zero, zero_add]
  rw [neg_smul, add_comm]
  simp [neg_add_cancel]

theorem det_tvMat (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K) :
    (tvMat h w c).det = 1 + c * vnorm h w := by
  have hm : tvMat h w c = 1 + Matrix.replicateCol (Fin 1) (fun i => c * w i) *
      Matrix.replicateRow (Fin 1) (fun j => h.bar (w j)) := by
    ext i j
    simp [tvMat, wMat, Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, mul_assoc]
  rw [hm]
  refine (Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (fun i => c * w i) (fun j => h.bar (w j))).trans ?_
  simp only [dotProduct, vnorm]
  rw [Finset.mul_sum]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun j _ => ?_)
  ring


@[expose] noncomputable def tvGL (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K) (hw : vnorm h w = 0) :
    GL (Fin 4) K :=
  Units.mk (tvMat h w c) (tvMat h w (-c)) (tvMat_mul_tvMat h w c hw)
    (by
      have := tvMat_mul_tvMat h w (-c) hw
      rwa [neg_neg] at this)

theorem coe_tvGL (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K) (hw : vnorm h w = 0) :
    ((tvGL h w c hw : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = tvMat h w c :=
  rfl

theorem transpose_bar_tvMat (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K) :
    ((tvMat h w c).map h.bar)ᵀ = 1 + h.bar c • wMat h w := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [tvMat, wMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.one_apply_eq, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_add, map_mul,
      map_one, h.bar_bar]
    ring
  · simp only [tvMat, wMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.one_apply_ne hij, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_add, map_mul,
      map_zero, h.bar_bar, Ne.symm hij, Matrix.one_apply_ne (Ne.symm hij), map_zero]
    ring

theorem conjT_tvMat_mul (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) (c : K) :
    ((tvMat h w c).map h.bar)ᵀ * tvMat h w c =
      1 + (c + h.bar c + h.bar c * c * vnorm h w) • wMat h w := by
  rw [transpose_bar_tvMat]
  unfold tvMat
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    wMat_mul_wMat, smul_add, add_smul]
  module

theorem tvGL_mem (h : UnitaryFieldData 2 f K) {w : Fin 4 → K} {c : K} (hw : vnorm h w = 0)
    (hc : h.bar c = c) : tvGL h w c hw ∈ gramSU h (1 : Matrix (Fin 4) (Fin 4) K) := by
  have : CharP K 2 := h.charP
  have hc2 : c + h.bar c = 0 := by
    rw [hc, ← two_mul, CharTwo.two_eq_zero, zero_mul]
  rw [mem_gramSU, coe_tvGL]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_one, conjT_tvMat_mul, hw, mul_zero, add_zero, hc2, zero_smul, add_zero]
  · rw [det_tvMat, hw, mul_zero, add_zero]

theorem key_sum (h : UnitaryFieldData 2 f K) (g : Matrix (Fin 4) (Fin 4) K)
    (hg : (g.map h.bar)ᵀ * g = 1) (w : Fin 4 → K) (k : Fin 4) :
    ∑ j, h.bar ((g *ᵥ w) j) * g j k = h.bar (w k) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hw : h.bar (w k) = ∑ l, h.bar (w l) * (1 : Matrix (Fin 4) (Fin 4) K) l k := by
    simp [Matrix.one_apply]
  rw [hw]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl : ∑ j, h.bar (g j l) * g j k = (1 : Matrix (Fin 4) (Fin 4) K) l k := by
    have := congrFun (congrFun hg l) k
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using this
  calc ∑ j, h.bar (g j l) * h.bar (w l) * g j k
      = h.bar (w l) * ∑ j, h.bar (g j l) * g j k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = h.bar (w l) * (1 : Matrix (Fin 4) (Fin 4) K) l k := by rw [hl]

theorem mul_wMat_eq (h : UnitaryFieldData 2 f K) (g : Matrix (Fin 4) (Fin 4) K)
    (hg : (g.map h.bar)ᵀ * g = 1) (w : Fin 4 → K) :
    g * wMat h w = wMat h (g *ᵥ w) * g := by
  ext i k
  have hk := key_sum h g hg w k
  simp only [Matrix.mul_apply, wMat, Matrix.of_apply]
  calc ∑ j, g i j * (w j * h.bar (w k)) = (g *ᵥ w) i * h.bar (w k) := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = (g *ᵥ w) i * ∑ j, h.bar ((g *ᵥ w) j) * g j k := by rw [hk]
    _ = ∑ j, (g *ᵥ w) i * h.bar ((g *ᵥ w) j) * g j k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

theorem mul_tvMat_eq (h : UnitaryFieldData 2 f K) (g : Matrix (Fin 4) (Fin 4) K)
    (hg : (g.map h.bar)ᵀ * g = 1) (w : Fin 4 → K) (c : K) :
    g * tvMat h w c = tvMat h (g *ᵥ w) c * g := by
  unfold tvMat
  rw [mul_add, mul_one, Matrix.mul_smul, mul_wMat_eq h g hg, add_mul, one_mul, smul_mul_assoc]

end Transvection


section Hyperbolic

variable {f : ℕ} {K : Type} [Field K]

abbrev hp1 : HypIndex 2 0 := Sum.inl 0
abbrev hp2 : HypIndex 2 0 := Sum.inl 1
abbrev hp3 : HypIndex 2 0 := Sum.inr (Sum.inr 1)
abbrev hp4 : HypIndex 2 0 := Sum.inr (Sum.inr 0)

theorem hAll_index (a : HypIndex 2 0) : a = hp1 ∨ a = hp2 ∨ a = hp3 ∨ a = hp4 := by
  rcases a with p | q | p
  · fin_cases p <;> simp [hp1, hp2]
  · exact q.elim0
  · fin_cases p <;> simp [hp3, hp4]

noncomputable def rx1 (h : UnitaryFieldData 2 f K) (t : K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  1 + Matrix.single hp1 hp2 t - Matrix.single hp3 hp4 (h.bar t)

noncomputable def rx2 (h : UnitaryFieldData 2 f K) (t : K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  1 + Matrix.single hp1 hp3 t - Matrix.single hp2 hp4 (h.bar t)

theorem uRootMat_rx1 (h : UnitaryFieldData 2 f K) (t : K) :
    uRootMat 0 h (Sum.inl 0) (Sum.inl 1) t = rx1 h t := by
  simp [uRootMat, uRootNil, rx1, lineCoord, hp1, hp2, hp3, hp4]
  abel

theorem uRootMat_rx2 (h : UnitaryFieldData 2 f K) (t : K) :
    uRootMat 0 h (Sum.inl 0) (Sum.inr 1) t = rx2 h t := by
  simp [uRootMat, uRootNil, rx2, lineCoord, hp1, hp2, hp3, hp4]
  abel

theorem mul_rx1_apply (h : UnitaryFieldData 2 f K) (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (t : K) (i j : HypIndex 2 0) :
    (M * rx1 h t) i j = M i j + M i hp1 * t * (if j = hp2 then 1 else 0) -
      M i hp3 * h.bar t * (if j = hp4 then 1 else 0) := by
  simp only [rx1, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_single_apply_same]
  simp [Matrix.mul_apply, Matrix.single_apply, eq_comm]

theorem rx1_mul_apply (h : UnitaryFieldData 2 f K) (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (t : K) (i j : HypIndex 2 0) :
    (rx1 h t * M) i j = M i j + t * (if i = hp1 then M hp2 j else 0) -
      h.bar t * (if i = hp3 then M hp4 j else 0) := by
  simp only [rx1, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, Matrix.single_apply, eq_comm]

theorem mul_rx2_apply (h : UnitaryFieldData 2 f K) (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (t : K) (i j : HypIndex 2 0) :
    (M * rx2 h t) i j = M i j + M i hp1 * t * (if j = hp3 then 1 else 0) -
      M i hp2 * h.bar t * (if j = hp4 then 1 else 0) := by
  simp only [rx2, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_single_apply_same]
  simp [Matrix.mul_apply, Matrix.single_apply, eq_comm]

theorem rx2_mul_apply (h : UnitaryFieldData 2 f K) (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (t : K) (i j : HypIndex 2 0) :
    (rx2 h t * M) i j = M i j + t * (if i = hp1 then M hp3 j else 0) -
      h.bar t * (if i = hp2 then M hp4 j else 0) := by
  simp only [rx2, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, Matrix.single_apply, eq_comm]

theorem rx1_block (h : UnitaryFieldData 2 f K) (t : K) : (rx1 h t).BlockTriangular fullPos := by
  intro i j hij
  rcases hAll_index i with rfl | rfl | rfl | rfl <;> rcases hAll_index j with rfl | rfl | rfl | rfl <;>
    simp_all [rx1, Matrix.one_apply, Matrix.single_apply, fullPos, hp1, hp2, hp3, hp4]

theorem rx2_block (h : UnitaryFieldData 2 f K) (t : K) : (rx2 h t).BlockTriangular fullPos := by
  intro i j hij
  rcases hAll_index i with rfl | rfl | rfl | rfl <;> rcases hAll_index j with rfl | rfl | rfl | rfl <;>
    simp_all [rx2, Matrix.one_apply, Matrix.single_apply, fullPos, hp1, hp2, hp3, hp4]

theorem center_matrix (h : UnitaryFieldData 2 f K) (y : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (hbt : y.BlockTriangular fullPos) (hd : ∀ a, y a a = 1)
    (h1 : ∀ t : K, y * rx1 h t = rx1 h t * y) (h2 : ∀ t : K, y * rx2 h t = rx2 h t * y) :
    y = 1 + Matrix.single hp1 hp4 (y hp1 hp4) := by
  obtain ⟨t₀, ht₀⟩ := h.exists_bar_ne
  have ht₀' : t₀ - h.bar t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm ht₀)
  have E1 : ∀ t : K, -(y hp1 hp3 * h.bar t) = t * y hp2 hp4 := by
    intro t
    have := congrFun (congrFun (h1 t) hp1) hp4
    rw [mul_rx1_apply, rx1_mul_apply] at this
    simp at this
    linear_combination this
  have E2 : ∀ t : K, -(y hp1 hp2 * h.bar t) = t * y hp3 hp4 := by
    intro t
    have := congrFun (congrFun (h2 t) hp1) hp4
    rw [mul_rx2_apply, rx2_mul_apply] at this
    simp at this
    linear_combination this
  have E3 : y hp2 hp3 = 0 := by
    have := congrFun (congrFun (h1 1) hp1) hp3
    rw [mul_rx1_apply, rx1_mul_apply] at this
    simp at this
    linear_combination this
  have Z1 : y hp1 hp3 = 0 := by
    have a := E1 1
    have b := E1 t₀
    rw [map_one] at a
    have : (y hp1 hp3) * (t₀ - h.bar t₀) = 0 := by linear_combination b - t₀ * a
    exact (mul_eq_zero.mp this).resolve_right ht₀'
  have Z4 : y hp2 hp4 = 0 := by
    have a := E1 1
    rw [map_one, Z1] at a
    linear_combination -a
  have Z2 : y hp1 hp2 = 0 := by
    have a := E2 1
    have b := E2 t₀
    rw [map_one] at a
    have : (y hp1 hp2) * (t₀ - h.bar t₀) = 0 := by linear_combination b - t₀ * a
    exact (mul_eq_zero.mp this).resolve_right ht₀'
  have Z5 : y hp3 hp4 = 0 := by
    have a := E2 1
    rw [map_one, Z2] at a
    linear_combination -a
  have L21 : y hp2 hp1 = 0 := hbt (i := hp2) (j := hp1) (by decide)
  have L31 : y hp3 hp1 = 0 := hbt (i := hp3) (j := hp1) (by decide)
  have L32 : y hp3 hp2 = 0 := hbt (i := hp3) (j := hp2) (by decide)
  have L41 : y hp4 hp1 = 0 := hbt (i := hp4) (j := hp1) (by decide)
  have L42 : y hp4 hp2 = 0 := hbt (i := hp4) (j := hp2) (by decide)
  have L43 : y hp4 hp3 = 0 := hbt (i := hp4) (j := hp3) (by decide)
  ext i j
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rcases hAll_index i with rfl | rfl | rfl | rfl <;> rcases hAll_index j with rfl | rfl | rfl | rfl <;>
    simp [hd, Z1, Z2, E3, Z4, Z5, L21, L31, L32, L41, L42, L43, hp1, hp2, hp3, hp4]

theorem bar_of_unitary (h : UnitaryFieldData 2 f K) (n : K)
    (hg : ((1 + Matrix.single hp1 hp4 n : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ *
      hypGram 2 0 K * (1 + Matrix.single hp1 hp4 n) = hypGram 2 0 K) :
    n + h.bar n = 0 := by
  have := congrFun (congrFun hg hp4) hp4
  simp [Matrix.mul_apply, Matrix.single_apply, hypGram_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.transpose_apply, Matrix.map_apply, hp1, hp2, hp3, hp4, Matrix.mul_add, Matrix.add_mul]
    at this
  linear_combination this

end Hyperbolic

section MaxPAndNorms

variable {f : ℕ} {K : Type} [Field K]

def MaxP (r : ℕ) {G : Type} [Group G] (P : Subgroup G) : Prop :=
  IsPGroup r P ∧ ∀ Q : Subgroup G, P ≤ Q → IsPGroup r Q → Q = P

theorem MaxP.map {r : ℕ} {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {P : Subgroup G}
    (hP : MaxP r P) : MaxP r (P.map e.toMonoidHom) := by
  refine ⟨hP.1.map e.toMonoidHom, fun Q' hQ' hQ'p => ?_⟩
  have hQ : P ≤ Q'.comap e.toMonoidHom := fun u hu => hQ' (Subgroup.mem_map_of_mem _ hu)
  have hEq := hP.2 _ hQ (hQ'p.comap_of_injective _ e.injective)
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  rw [← Subgroup.map_comap_eq_self_of_surjective hs Q', hEq]

theorem MaxP.exists_sylow {r : ℕ} {G : Type} [Group G] {P : Subgroup G} (hP : MaxP r P) :
    ∃ S : Sylow r G, (S : Subgroup G) = P :=
  ⟨⟨P, hP.1, fun hQ hPQ => hP.2 _ hPQ hQ⟩, rfl⟩

theorem MaxP.of_sylow {r : ℕ} {G : Type} [Group G] (S : Sylow r G) :
    MaxP r (S : Subgroup G) :=
  ⟨S.isPGroup', fun Q hPQ hQp => S.is_maximal' hQp hPQ⟩

theorem cenIn_iff_maxP {r : ℕ} {H : Type} [Group H] (x : H) :
    CenIn r x ↔ ∃ P : Subgroup H, MaxP r P ∧ x ∈ P ∧ P ≤ Subgroup.centralizer ({x} : Set H) :=
  ⟨fun ⟨P, h1, h2, h3, h4⟩ => ⟨P, ⟨h1, h4⟩, h2, h3⟩,
    fun ⟨P, ⟨h1, h4⟩, h2, h3⟩ => ⟨P, h1, h2, h3, h4⟩⟩

theorem unitri_commute (v : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (hv : v.BlockTriangular fullPos) (hd : ∀ a, v a a = 1) (n : K) :
    v * (1 + Matrix.single hp1 hp4 n) = (1 + Matrix.single hp1 hp4 n) * v := by
  have L21 : v hp2 hp1 = 0 := hv (i := hp2) (j := hp1) (by decide)
  have L31 : v hp3 hp1 = 0 := hv (i := hp3) (j := hp1) (by decide)
  have L41 : v hp4 hp1 = 0 := hv (i := hp4) (j := hp1) (by decide)
  have L42 : v hp4 hp2 = 0 := hv (i := hp4) (j := hp2) (by decide)
  have L43 : v hp4 hp3 = 0 := hv (i := hp4) (j := hp3) (by decide)
  have hcol : ∀ i, v i hp1 = if i = hp1 then 1 else 0 := by
    intro i
    rcases hAll_index i with rfl | rfl | rfl | rfl <;> simp [hd, L21, L31, L41, hp1, hp2, hp3, hp4]
  have hrow : ∀ j, v hp4 j = if j = hp4 then 1 else 0 := by
    intro j
    rcases hAll_index j with rfl | rfl | rfl | rfl <;> simp [hd, L41, L42, L43, hp1, hp2, hp3, hp4]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  congr 1
  ext i j
  by_cases hi : i = hp1 <;> by_cases hj : j = hp4 <;>
    simp [Matrix.mul_apply, Matrix.single_apply, hcol, hrow, hi, hj, eq_comm]

theorem single_block (n : K) :
    (1 + Matrix.single hp1 hp4 n : Matrix (HypIndex 2 0) (HypIndex 2 0) K).BlockTriangular fullPos := by
  intro i j hij
  rcases hAll_index i with rfl | rfl | rfl | rfl <;> rcases hAll_index j with rfl | rfl | rfl | rfl <;>
    simp_all [Matrix.one_apply, Matrix.single_apply, fullPos, hp1, hp2, hp3, hp4]

theorem wMat_smul (h : UnitaryFieldData 2 f K) (μ : K) (w : Fin 4 → K) :
    wMat h (μ • w) = (μ * h.bar μ) • wMat h w := by
  ext i j
  simp only [wMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply]
  ring

theorem tvMat_smul_vec (h : UnitaryFieldData 2 f K) (μ : K) (w : Fin 4 → K) (n : K) :
    tvMat h (μ • w) n = tvMat h w (n * (μ * h.bar μ)) := by
  unfold tvMat
  rw [wMat_smul, smul_smul]

theorem vnorm_smul (h : UnitaryFieldData 2 f K) (μ : K) (w : Fin 4 → K) :
    vnorm h (μ • w) = (μ * h.bar μ) * vnorm h w := by
  simp only [vnorm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem vnorm_mulVec (h : UnitaryFieldData 2 f K) (M : Matrix (Fin 4) (Fin 4) K)
    (hM : (M.map h.bar)ᵀ * M = 1) (w : Fin 4 → K) :
    vnorm h (M *ᵥ w) = vnorm h w := by
  have hk : ∀ k, ∑ j, h.bar ((M *ᵥ w) j) * M j k = h.bar (w k) := fun k => key_sum h M hM w k
  unfold vnorm
  calc ∑ j, (M *ᵥ w) j * h.bar ((M *ᵥ w) j)
      = ∑ j, h.bar ((M *ᵥ w) j) * (M *ᵥ w) j := Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = ∑ j, ∑ k, h.bar ((M *ᵥ w) j) * M j k * w k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, (∑ j, h.bar ((M *ᵥ w) j) * M j k) * w k := by
        simp only [Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ k, h.bar (w k) * w k := Finset.sum_congr rfl fun k _ => by rw [hk k]
    _ = ∑ k, w k * h.bar (w k) := Finset.sum_congr rfl fun k _ => mul_comm _ _


section Witt

variable {f : ℕ} {K : Type} [Field K]

theorem transportInv_row_hp4 (h : UnitaryFieldData 2 f K)
    {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K} (j : Fin (2 * 2 + 0)) :
    transportInv h R hp4 j = h.bar (R j hp1) := by
  simp [transportInv, Matrix.mul_apply, hypGram_apply, hp4, hp1, hypPartner, Matrix.transpose_apply,
    Matrix.map_apply]

theorem transport_one_add (h : UnitaryFieldData 2 f K)
    {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K} (hR : IsHypTransport h R) (n : K) :
    R * (1 + Matrix.single hp1 hp4 n) * transportInv h R = tvMat h (fun i : Fin 4 => R i hp1) n := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, mul_transportInv hR]
  unfold tvMat wMat
  congr 1
  ext (i j : Fin 4)
  simp [Matrix.mul_apply, Matrix.single_apply, transportInv_row_hp4, hp4, hp1]
  ring

theorem vnorm_col_hp1 (h : UnitaryFieldData 2 f K) {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K}
    (hR : IsHypTransport h R) : vnorm h (fun i : Fin 4 => R i hp1) = 0 := by
  have := congrFun (congrFun hR hp1) hp1
  simp [Matrix.mul_apply, hypGram_apply, hp1, hypPartner, Matrix.transpose_apply,
    Matrix.map_apply] at this
  unfold vnorm
  simpa [mul_comm] using this

theorem stdHermForm_self (h : UnitaryFieldData 2 f K) (w : Fin 4 → K) :
    CFSG.LinearGroups.stdHermForm h 4 w w = vnorm h w := by
  simp [CFSG.LinearGroups.stdHermForm, vnorm, mul_comm]

theorem exists_witt (h : UnitaryFieldData 2 f K) {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K}
    (hR : IsHypTransport h R) {w : Fin 4 → K} (hw : IsIsoVec h w) :
    ∃ g : hypSU h 2 0, ∃ μ : K, μ ≠ 0 ∧
      (R * ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        transportInv h R) *ᵥ (fun i : Fin 4 => R i hp1) = μ • w := by
  have hRT : R * transportInv h R = 1 := mul_transportInv hR
  have hTR : transportInv h R * R = 1 := transportInv_mul hR
  set x : HypIndex 2 0 → K := transportInv h R *ᵥ w with hxdef
  have hRx : R *ᵥ x = w := by
    rw [hxdef, Matrix.mulVec_mulVec, hRT, Matrix.one_mulVec]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hw.1
    rw [← hRx, h0, Matrix.mulVec_zero]
  have hxx : hypForm h 2 0 x x = 0 := by
    rw [hxdef, hypForm_transportInv hR]
    rw [stdHermForm_self]
    exact hw.2
  have hW0 : (K ∙ x) ≠ ⊥ := fun h0 => hx0 (Submodule.span_singleton_eq_bot.mp h0)
  have hWiso : ∀ a ∈ K ∙ x, ∀ b ∈ K ∙ x, hypForm h 2 0 a b = 0 := by
    intro a ha b hb
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hb
    simp [map_smulₛₗ, map_smul, hxx]
  obtain ⟨-, -, g, hg⟩ := exists_smul_hypFlag_eq (r := 2) (ε := 0) h (by norm_num) hW0 hWiso
  rw [finrank_span_singleton hx0] at hg
  have he : (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) ∈ hypFlag h 2 0 1 := by
    rw [hypFlag, if_pos (by norm_num)]
    exact Submodule.subset_span ⟨0, by simp, by simp [hp1]⟩
  have hge : g • (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) ∈ K ∙ x := by
    rw [← hg]
    exact Submodule.smul_mem_pointwise_smul _ _ _ he
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hge
  have hvec : ∀ v : HypIndex 2 0 → K, ∀ g' : hypSU h 2 0,
      g' • v = ((g' : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v :=
    fun v g' => rfl
  refine ⟨g, μ, ?_, ?_⟩
  · rintro rfl
    have hz : g • (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) = 0 := by
      rw [← hμ, zero_smul]
    have h2 := congrArg (fun v => g⁻¹ • v) hz
    simp only [smul_smul, inv_mul_cancel, one_smul, smul_zero] at h2
    have h3 := congrFun h2 hp1
    simp at h3
  · have e0 : (fun i : Fin 4 => R i hp1) = (R *ᵥ (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) : Fin 4 → K) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hT : transportInv h R *ᵥ (R *ᵥ (Pi.single hp1 (1 : K) : HypIndex 2 0 → K)) =
        Pi.single hp1 (1 : K) := by
      rw [Matrix.mulVec_mulVec, hTR, Matrix.one_mulVec]
    have hg' : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) = μ • x := by
      rw [← hvec, hμ]
    rw [e0, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT, hg', Matrix.mulVec_smul, hRx]

end Witt

section Group

variable {f : ℕ} {K : Type} [Field K]

theorem rx1_diag (h : UnitaryFieldData 2 f K) (t : K) (a : HypIndex 2 0) : rx1 h t a a = 1 := by
  rcases hAll_index a with rfl | rfl | rfl | rfl <;>
    simp [rx1, Matrix.one_apply, Matrix.single_apply, hp1, hp2, hp3, hp4]

theorem rx2_diag (h : UnitaryFieldData 2 f K) (t : K) (a : HypIndex 2 0) : rx2 h t a a = 1 := by
  rcases hAll_index a with rfl | rfl | rfl | rfl <;>
    simp [rx2, Matrix.one_apply, Matrix.single_apply, hp1, hp2, hp3, hp4]

theorem single_diag (n : K) (a : HypIndex 2 0) :
    (1 + Matrix.single hp1 hp4 n : Matrix (HypIndex 2 0) (HypIndex 2 0) K) a a = 1 := by
  rcases hAll_index a with rfl | rfl | rfl | rfl <;>
    simp [Matrix.one_apply, Matrix.single_apply, hp1, hp2, hp3, hp4]

theorem uRootMat_swap (h : UnitaryFieldData 2 f K) (t : K) :
    uRootMat 0 h (Sum.inl 0) (Sum.inr 0) t = 1 + Matrix.single hp1 hp4 t := by
  simp [uRootMat, uRootNil, lineCoord, hp1, hp4]

noncomputable def xe1 (h : UnitaryFieldData 2 f K) (t : K) : hypSU h 2 0 :=
  uRootElt (ε := 0) h (show (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inl 1 by decide)
    ⟨t, by rw [uRootDom_of_ne _ (by decide)]; trivial⟩

noncomputable def xe2 (h : UnitaryFieldData 2 f K) (t : K) : hypSU h 2 0 :=
  uRootElt (ε := 0) h (show (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 1 by decide)
    ⟨t, by rw [uRootDom_of_ne _ (by decide)]; trivial⟩

noncomputable def xeT (h : UnitaryFieldData 2 f K) (t : K) (ht : t ∈ h.traceZero) : hypSU h 2 0 :=
  uRootElt (ε := 0) h (show (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0 by decide)
    ⟨t, by
      have := uRootDom_swap h (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
      simp only [Sum.swap_inl] at this
      rw [this]
      exact ht⟩

theorem coe_xe1 (h : UnitaryFieldData 2 f K) (t : K) :
    ((xe1 h t : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = rx1 h t := by
  rw [xe1, coe_uRootElt, uRootMat_rx1]

theorem coe_xe2 (h : UnitaryFieldData 2 f K) (t : K) :
    ((xe2 h t : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = rx2 h t := by
  rw [xe2, coe_uRootElt, uRootMat_rx2]

theorem coe_xeT (h : UnitaryFieldData 2 f K) (t : K) (ht : t ∈ h.traceZero) :
    ((xeT h t ht : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      1 + Matrix.single hp1 hp4 t := by
  rw [xeT, coe_uRootElt, uRootMat_swap]

theorem xe1_mem (h : UnitaryFieldData 2 f K) (t : K) : xe1 h t ∈ hypUnitriangular h 2 0 := by
  rw [mem_hypUnitriangular, coe_xe1]
  exact ⟨rx1_block h t, rx1_diag h t⟩

theorem xe2_mem (h : UnitaryFieldData 2 f K) (t : K) : xe2 h t ∈ hypUnitriangular h 2 0 := by
  rw [mem_hypUnitriangular, coe_xe2]
  exact ⟨rx2_block h t, rx2_diag h t⟩

theorem xeT_mem (h : UnitaryFieldData 2 f K) (t : K) (ht : t ∈ h.traceZero) :
    xeT h t ht ∈ hypUnitriangular h 2 0 := by
  rw [mem_hypUnitriangular, coe_xeT]
  exact ⟨single_block t, single_diag t⟩

theorem center_group (h : UnitaryFieldData 2 f K) {y : hypSU h 2 0}
    (hy : y ∈ hypUnitriangular h 2 0) (hc : ∀ v ∈ hypUnitriangular h 2 0, v * y = y * v) :
    ∃ n : K, ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      1 + Matrix.single hp1 hp4 n ∧ n + h.bar n = 0 := by
  obtain ⟨hbt, hd⟩ := mem_hypUnitriangular.mp hy
  have h1 : ∀ t : K, ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      rx1 h t = rx1 h t * ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    intro t
    have := congrArg (fun g : hypSU h 2 0 => ((g : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (hc (xe1 h t) (xe1_mem h t))
    simp only [Subgroup.coe_mul, Units.val_mul, coe_xe1] at this
    exact this.symm
  have h2 : ∀ t : K, ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      rx2 h t = rx2 h t * ((y : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
    intro t
    have := congrArg (fun g : hypSU h 2 0 => ((g : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K)) (hc (xe2 h t) (xe2_mem h t))
    simp only [Subgroup.coe_mul, Units.val_mul, coe_xe2] at this
    exact this.symm
  have hM := center_matrix h _ hbt hd h1 h2
  refine ⟨_, hM, ?_⟩
  have hg := (mem_hypSU.mp y.2).1
  rw [hM] at hg
  exact bar_of_unitary h _ hg

end Group

section Main

open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K]

theorem cenIn_two_iff (h : UnitaryFieldData 2 f K) (z : unitarySU 2 f K 4) :
    CenIn 2 z ↔ ((z : GL (Fin 4) K) = 1 ∨
      ∃ (w : Fin 4 → K) (c : K), IsIsoVec h w ∧ c ≠ 0 ∧ h.bar c = c ∧
        ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = tvMat h w c) := by
  have : CharP K 2 := h.charP
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  obtain ⟨P0, hP0⟩ := (unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)).2.1
  have hmaxU : MaxP 2 (hypUnitriangular h 2 0) := hP0 ▸ MaxP.of_sylow P0
  let E : hypSU h 2 0 ≃* unitarySU 2 f K 4 := hypTransport h hR
  have hEcoe : ∀ g : hypSU h 2 0, ((E g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      R * ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        transportInv h R :=
    fun g => coe_hypTransport hR g
  let U : Subgroup (unitarySU 2 f K 4) := (hypUnitriangular h 2 0).map E.toMonoidHom
  have hmaxU' : MaxP 2 U := hmaxU.map E
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsymm : ∀ z : unitarySU 2 f K 4, z ∈ U → (∀ u ∈ U, u * z = z * u) → ∃ n : K,
      ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = tvMat h (fun i : Fin 4 => R i hp1) n ∧
        n + h.bar n = 0 := by
    intro z hz hc
    have hyU : E.symm z ∈ hypUnitriangular h 2 0 := Subgroup.mem_map_equiv.mp hz
    have hcy : ∀ v ∈ hypUnitriangular h 2 0, v * E.symm z = E.symm z * v := by
      intro v hv
      have hu : E v ∈ U := Subgroup.mem_map_of_mem _ hv
      have h3 := congrArg E.symm (hc (E v) hu)
      simpa [map_mul] using h3
    obtain ⟨n, hn, hn0⟩ := center_group h hyU hcy
    refine ⟨n, ?_, hn0⟩
    have hzE : z = E (E.symm z) := (E.apply_symm_apply z).symm
    rw [hzE, hEcoe, hn, transport_one_add h hR n]
  have hw0 : (fun i : Fin 4 => R i hp1) ≠ 0 := by
    intro h0
    have hTR : transportInv h R * R = 1 := transportInv_mul hR
    have e0 : (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) = 0 := by
      have h1 : transportInv h R *ᵥ (R *ᵥ (Pi.single hp1 (1 : K) : HypIndex 2 0 → K)) =
          Pi.single hp1 (1 : K) := by
        rw [Matrix.mulVec_mulVec, hTR, Matrix.one_mulVec]
      have h2' : R *ᵥ (Pi.single hp1 (1 : K) : HypIndex 2 0 → K) = 0 := by
        funext i
        have := congrFun h0 i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
      rw [← h1, h2', Matrix.mulVec_zero]
    have := congrFun e0 hp1
    simp at this
  have hmat : ∀ g : unitarySU 2 f K 4, (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := fun g =>
    ((mem_unitarySU_iff h).mp g.2).2
  constructor
  · intro hc
    obtain ⟨P, hPM, hzP, hPC⟩ := (cenIn_iff_maxP z).mp hc
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Finite (unitarySU 2 f K 4) := by
      haveI := h.finite
      infer_instance
    haveI : Finite (Sylow 2 (unitarySU 2 f K 4)) := Finite.of_injective
      (fun Q : Sylow 2 (unitarySU 2 f K 4) => (Q : Subgroup (unitarySU 2 f K 4)))
      (fun Q Q' hQQ => Sylow.ext hQQ)
    obtain ⟨S, hS⟩ := hPM.exists_sylow
    let SU : Sylow 2 (unitarySU 2 f K 4) := ⟨U, hmaxU'.1, fun hQ hUQ => hmaxU'.2 _ hUQ hQ⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (unitarySU 2 f K 4) SU S
    have hcoe : (S : Subgroup (unitarySU 2 f K 4)) = MulAut.conj g • U := by
      rw [← hg]
      rfl
    have hmemP : ∀ x : unitarySU 2 f K 4, x ∈ P ↔ g⁻¹ * x * g ∈ U := by
      intro x
      rw [← hS, hcoe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def, mul_assoc]
    have hz'U : g⁻¹ * z * g ∈ U := (hmemP z).mp hzP
    have hz'c : ∀ u ∈ U, u * (g⁻¹ * z * g) = (g⁻¹ * z * g) * u := by
      intro u hu
      have hgu : g * u * g⁻¹ ∈ P := by
        rw [hmemP]
        simpa [mul_assoc] using hu
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hPC hgu)
      calc u * (g⁻¹ * z * g) = g⁻¹ * ((g * u * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * u * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * z * g) * u := by group
    obtain ⟨n, hn, hn0⟩ := hsymm (g⁻¹ * z * g) hz'U hz'c
    have hzeq : z * g = g * (g⁻¹ * z * g) := by group
    have hn' := hn
    simp only [Subgroup.coe_mul, Units.val_mul] at hn'
    have h4 := congrArg (fun x : unitarySU 2 f K 4 => ((x : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) hzeq
    simp only [Subgroup.coe_mul, Units.val_mul] at h4
    have hM := hmat g
    have hMi : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) = 1 := by
      rw [← Units.val_mul]
      simp
    have hzM : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        tvMat h (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i : Fin 4 => R i hp1)) n *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [h4, hn', mul_tvMat_eq h _ hM]
    have hzeqM : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        tvMat h (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i : Fin 4 => R i hp1)) n := by
      calc ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
          = ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
              (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                ((g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K)) := by
            rw [hMi, Matrix.mul_one]
        _ = (((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
              ((g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) := (Matrix.mul_assoc _ _ _).symm
        _ = _ := by rw [hzM, Matrix.mul_assoc, hMi, Matrix.mul_one]
    by_cases hn0' : n = 0
    · left
      apply Units.ext
      rw [hzeqM, hn0']
      simp [tvMat]
    · right
      have hMi' : ((((g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
        have h5 : ((g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) * (g : GL (Fin 4) K) = 1 := by simp
        have h6 := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) h5
        simpa using h6
      refine ⟨((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (fun i : Fin 4 => R i hp1), n,
        ⟨?_, ?_⟩, hn0', ?_, hzeqM⟩
      · intro h0
        apply hw0
        rw [← Matrix.one_mulVec (fun i : Fin 4 => R i hp1), ← hMi', ← Matrix.mulVec_mulVec, h0,
          Matrix.mulVec_zero]
      · rw [vnorm_mulVec h _ (hmat g), vnorm_col_hp1 h hR]
      · linear_combination hn0 - n * h2
  · rintro (hz1 | ⟨w, c, hw, hc0, hcbar, hzw⟩)
    · have hz1' : z = 1 := Subtype.ext (by simpa using hz1)
      rw [hz1']
      refine (cenIn_iff_maxP _).mpr ⟨U, hmaxU', one_mem U, fun u _ => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    · obtain ⟨g, μ, hμ0, hgw⟩ := exists_witt h hR hw
      have hμbar : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ0
      have hN0 : μ * h.bar μ ≠ 0 := mul_ne_zero hμ0 hμbar
      obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : K, n₀ = c * (μ * h.bar μ)⁻¹ := ⟨_, rfl⟩
      have hn₀N : n₀ * (μ * h.bar μ) = c := by
        rw [hn₀def, mul_assoc, inv_mul_cancel₀ hN0, mul_one]
      have hbar_n₀ : h.bar n₀ = n₀ := by
        rw [hn₀def, map_mul, map_inv₀, map_mul, h.bar_bar, hcbar, mul_comm (h.bar μ) μ]
      have htr : n₀ ∈ h.traceZero := by
        rw [UnitaryFieldData.mem_traceZero]
        unfold UnitaryFieldData.trace
        rw [hbar_n₀]
        linear_combination n₀ * h2
      have hz₀mat : ((E (xeT h n₀ htr) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          tvMat h (fun i : Fin 4 => R i hp1) n₀ := by
        rw [hEcoe, coe_xeT, transport_one_add h hR n₀]
      have hz₀U : E (xeT h n₀ htr) ∈ U := Subgroup.mem_map_of_mem _ (xeT_mem h n₀ htr)
      have hz₀C : U ≤ Subgroup.centralizer ({E (xeT h n₀ htr)} : Set (unitarySU 2 f K 4)) := by
        intro u hu
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        show E v * E (xeT h n₀ htr) = E (xeT h n₀ htr) * E v
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul, coe_xeT]
        exact unitri_commute _ (mem_hypUnitriangular.mp hv).1 (mem_hypUnitriangular.mp hv).2 n₀
      have hC : CenIn 2 (E (xeT h n₀ htr)) := (cenIn_iff_maxP _).mpr ⟨U, hmaxU', hz₀U, hz₀C⟩
      have hconj := CenIn.congr (MulAut.conj (E g)) hC
      have key : E g * E (xeT h n₀ htr) = z * E g := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        have hGw : ((E g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
            (fun i : Fin 4 => R i hp1) = μ • w := by
          rw [hEcoe]
          exact hgw
        rw [hz₀mat, mul_tvMat_eq h _ (hmat (E g)), hGw, tvMat_smul_vec, hn₀N, hzw]
      have hcon : MulAut.conj (E g) (E (xeT h n₀ htr)) = z := by
        rw [MulAut.conj_apply, key, mul_assoc, mul_inv_cancel, mul_one]
      rw [hcon] at hconj
      exact hconj

end Main

end MaxPAndNorms

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
