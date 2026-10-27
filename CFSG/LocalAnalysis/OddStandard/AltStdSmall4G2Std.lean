module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Term
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Lift8
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2ModZData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubeLift
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0StructOdd

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

namespace StdCoord

open ComponentClassification.GrSLit.L34Facts

@[expose] def conjM {q : ℕ} (k k' : Matrix (Fin 3) (Fin 3) (ZMod q)) (h : k' * k = 1) :
    Matrix (Fin 3) (Fin 3) (ZMod q) →* Matrix (Fin 3) (Fin 3) (ZMod q) where
  toFun M := k * M * k'
  map_one' := by
    show k * 1 * k' = 1
    rw [Matrix.mul_one, mul_eq_one_comm.1 h]
  map_mul' M N := by
    show k * (M * N) * k' = k * M * k' * (k * N * k')
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k' k, h, Matrix.one_mul]

theorem genRel_conj {X Y k k' : FourCube.Mat4} (h : k' * k = 1) (hr : FourCube.GenRel X Y) :
    FourCube.GenRel (k * X * k') (k * Y * k') := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have e : ∀ M, k * M * k' = conjM k k' h M := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e, ← map_mul, ← map_pow, h1, h2, h3, h4, map_one]

theorem exists_conj_std4 {X Y : FourCube.Mat4}
    (hr : FourCube.GenRel X Y) (hX : FourCube.redHom X = FourCube.redHom FourCube.X0)
    (hY : FourCube.redHom Y = FourCube.redHom FourCube.Y0) :
    ∃ k k' : FourCube.Mat4, k * k' = 1 ∧ k' * k = 1 ∧ FourCube.redHom k = 1 ∧
      k * X * k' = FourCube.X0 ∧ k * Y * k' = FourCube.Y0 := by
  have hYe := FourCube.eq_add_twoM hY
  have hY3 : Y * Y * Y = 1 := hr.2.1
  obtain ⟨m1, hm1⟩ := FourCube.complementA_holds _ (by rw [← hYe]; exact hY3)
  rw [← hYe] at hm1
  set k1 := 1 + FourCube.twoM m1 with hk1
  have hk11 := FourCube.twoM_mul_self m1
  have hY0 : k1 * Y * k1 = FourCube.Y0 := by rw [hm1, Matrix.mul_assoc, hk11, Matrix.mul_one]
  set X' := k1 * X * k1 with hX'
  have hX'r : FourCube.redHom X' = FourCube.redHom FourCube.X0 := by
    rw [hX', map_mul, map_mul, hk1, FourCube.redHom_k, hX, Matrix.one_mul, Matrix.mul_one]
  have hX'e := FourCube.eq_add_twoM hX'r
  have hrel : FourCube.GenRel X' FourCube.Y0 := by
    rw [← hY0]
    exact genRel_conj hk11 hr
  rw [hX'e] at hrel
  obtain ⟨m2, hm2Y, hm2X⟩ := FourCube.complementB_holds _ hrel
  rw [← hX'e] at hm2X
  set k2 := 1 + FourCube.twoM m2 with hk2
  have hk22 := FourCube.twoM_mul_self m2
  refine ⟨k2 * k1, k1 * k2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc k1 k1, hk11, Matrix.one_mul, hk22]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc k2 k2, hk22, Matrix.one_mul, hk11]
  · rw [map_mul, hk1, hk2, FourCube.redHom_k, FourCube.redHom_k, Matrix.one_mul]
  · calc k2 * k1 * X * (k1 * k2) = k2 * X' * k2 := by rw [hX']; simp only [Matrix.mul_assoc]
      _ = FourCube.X0 := by rw [hm2X, Matrix.mul_assoc, hk22, Matrix.mul_one]
  · calc k2 * k1 * Y * (k1 * k2) = k2 * (k1 * Y * k1) * k2 := by simp only [Matrix.mul_assoc]
      _ = FourCube.Y0 := by rw [hY0, hm2Y, Matrix.mul_assoc, hk22, Matrix.mul_one]

@[expose] def lift48 (k : FourCube.Mat4) : Matrix (Fin 3) (Fin 3) (ZMod 8) :=
  k.map fun x => (x.val : ZMod 8)

theorem red84_lift48 (k : FourCube.Mat4) : red84 (lift48 k) = k := by
  ext i j
  rw [red84_apply, lift48, Matrix.map_apply, map_natCast, ZMod.natCast_zmod_val]

theorem exists_lift_inv {k k' : FourCube.Mat4} (h : k * k' = 1) :
    ∃ K' : Matrix (Fin 3) (Fin 3) (ZMod 8), lift48 k * K' = 1 ∧ K' * lift48 k = 1 ∧
      red84 K' = k' := by
  have hr : red84 (lift48 k * lift48 k') = red84 1 := by
    rw [map_mul, red84_lift48, red84_lift48, h, map_one]
  have he := eq_add_fourM hr
  refine ⟨lift48 k' * (lift48 k * lift48 k'), ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, he, fourM_mul_self]
  · exact mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, he, fourM_mul_self])
  · rw [map_mul, map_mul, red84_lift48, red84_lift48, h, Matrix.mul_one]

theorem redHom_red84 (X : Matrix (Fin 3) (Fin 3) (ZMod 8)) :
    FourCube.redHom (red84 X) = red 3 X := by
  have key : ∀ x : ZMod 8, ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2)
      (ZMod.castHom (show 4 ∣ 8 by decide) (ZMod 4) x) = (ZMod.cast x : ZMod 2) := by decide
  ext i j
  rw [FourCube.redHom_apply, red84_apply, red_apply]
  exact key (X i j)

theorem genRel_red84 {X Y : Matrix (Fin 3) (Fin 3) (ZMod 8)} (h : GenRel8 X Y) :
    FourCube.GenRel (red84 X) (red84 Y) := by
  obtain ⟨s1, s2, s3, s4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, s1, map_one]
  · rw [← map_mul, ← map_mul, s2, map_one]
  · rw [← map_mul, ← map_pow, s3, map_one]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_pow, s4, map_one]

theorem redHom_eq_red (X : FourCube.Mat4) : FourCube.redHom X = red 2 X := by
  ext i j
  rw [FourCube.redHom_apply, red_apply, ZMod.castHom_apply]

theorem redHom_X0 : FourCube.redHom FourCube.X0 = x2M := by
  ext i j
  rw [FourCube.redHom_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem redHom_Y0 : FourCube.redHom FourCube.Y0 = y2M := by
  ext i j
  rw [FourCube.redHom_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem word4_x : FourCube.X0 * FourCube.Y0 * FourCube.X0 * FourCube.Y0 * FourCube.Y0 *
    FourCube.X0 = Z4M.dMat 1 0 0 := by
  decide

theorem word4_y : FourCube.X0 * FourCube.Y0 * FourCube.Y0 * FourCube.X0 * FourCube.Y0 *
    FourCube.X0 = Z4M.dMat 0 0 1 := by
  decide

theorem word8_x : X8 * Y8 * X8 * Y8 * Y8 * X8 = Z8M.dMat 1 0 0 := by
  decide

theorem word8_y : X8 * Y8 * Y8 * X8 * Y8 * X8 = Z8M.dMat 0 0 1 := by
  decide

theorem word2_x : x2M * y2M * x2M * y2M * y2M * x2M = unitri 1 0 0 := by
  decide

theorem word2_y : x2M * y2M * y2M * x2M * y2M * x2M = unitri 0 0 1 := by
  decide

@[expose] def tableHom {M : Type*} [Monoid M] (D : ZMod 2 → ZMod 2 → ZMod 2 → M)
    (hD : ∀ a b c a' b' c', D a b c * D a' b' c' = D (a + a') (b + b' + a * c') (c + c'))
    (h0 : D 0 0 0 = 1) : sylowT →* M where
  toFun t := D (tripleEquiv.symm t).1 (tripleEquiv.symm t).2.1 (tripleEquiv.symm t).2.2
  map_one' := by
    have e : tripleEquiv.symm (1 : sylowT) = (0, 0, 0) := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (Units.ext unitri_zero.symm)
    simp only [e, h0]
  map_mul' s t := by
    obtain ⟨⟨a, b, c⟩, rfl⟩ := tripleEquiv.surjective s
    obtain ⟨⟨a', b', c'⟩, rfl⟩ := tripleEquiv.surjective t
    have e : tripleEquiv (a, b, c) * tripleEquiv (a', b', c') =
        tripleEquiv (a + a', b + b' + a * c', c + c') :=
      Subtype.ext (Units.ext (unitri_mul a b c a' b' c'))
    simp only [e, Equiv.symm_apply_apply, hD]

theorem tableHom_apply {M : Type*} [Monoid M] (D : ZMod 2 → ZMod 2 → ZMod 2 → M) (hD) (h0)
    (a b c : ZMod 2) : tableHom D hD h0 (tripleEquiv (a, b, c)) = D a b c := by
  simp only [tableHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.symm_apply_apply]

end StdCoord

open StdCoord

section Coord

variable {G : Type} [Group G] {k : ℕ} {A : Subgroup G}

@[expose] def coordChange (K K' : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) (h1 : K * K' = 1)
    (h2 : K' * K = 1) :
    Multiplicative (Fin 3 → ZMod (2 ^ k)) ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)) where
  toFun v := Multiplicative.ofAdd (K *ᵥ Multiplicative.toAdd v)
  invFun v := Multiplicative.ofAdd (K' *ᵥ Multiplicative.toAdd v)
  left_inv v := by simp [mulVec_mulVec, h2]
  right_inv v := by simp [mulVec_mulVec, h1]
  map_mul' v w := by simp [mulVec_add]

variable (ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ k)))
  (K K' : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) (h1 : K * K' = 1) (h2 : K' * K = 1)

theorem el_coordChange (x : Fin 3 → ZMod (2 ^ k)) :
    el (ι.trans (coordChange K K' h1 h2)) x = el ι (K' *ᵥ x) := rfl

theorem mat_coordChange (g : normalizer (A : Set G)) :
    mat (ι.trans (coordChange K K' h1 h2)) g = K * mat ι g * K' := by
  refine matrix_ext_mulVec fun x => el_injective (ι.trans (coordChange K K' h1 h2)) ?_
  rw [← mat_spec, el_coordChange, el_coordChange, mat_spec, mulVec_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc K', ← Matrix.mul_assoc K', h2, Matrix.one_mul]

theorem ECoords.coordChange {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)}
    {hn : 8 ≤ n} (hι : ECoords θ hn k A ι) (hK' : red k K' = 1) :
    ECoords θ hn k A (ι.trans (coordChange K K' h1 h2)) := by
  refine ⟨hι.one_le, hι.E_le, fun v => ?_⟩
  rw [el_coordChange, ← hι.eps v]
  congr 1
  unfold liftE
  rw [mulVec_two_pow_val hι.one_le, hK', one_mulVec]

end Coord

theorem red_eq_one_of_mul {k : ℕ} (hk : 1 ≤ k) {K K' : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))}
    (h1 : K * K' = 1) (hK : red k K = 1) : red k K' = 1 := by
  have h := congrArg (red k) h1
  rwa [red_mul hk, hK, Matrix.one_mul, red_one hk] at h

section I1

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {m : ℕ} {A : Subgroup G}
  {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ m))}

omit [Finite G] in
theorem red_mat_eq_of_conj {hn : 8 ≤ n} (hι : ECoords θ hn m A ι) (g : normalizer (A : Set G))
    {M : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hg : ∀ v, (g : G) * epsV θ hn v * (g : G)⁻¹ = epsV θ hn (M *ᵥ v)) :
    red m (mat ι g) = M :=
  matrix_ext_mulVec fun v => epsV_injective θ hn (by rw [← red_mat ι hι g v, hg])

theorem mat_eq_one_of_red (c : Config G L Q n θ z) (hι : ECoords θ c.hn8 m A ι)
    {g : normalizer (A : Set G)} (hg : (g : G) ∈ KA L z A) (hred : red m (mat ι g) = 1) :
    mat ι g = 1 := by
  obtain ⟨a, b, hb, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  have hgE : (g : G) ∈ centralizer (E θ c.hn8 : Set G) := by
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨v, rfl⟩ := (mem_E_iff_epsV θ c.hn8 e).1 he
    have h1 := red_mat ι hι g v
    rw [hred, one_mulVec] at h1
    calc epsV θ c.hn8 v * (g : G) = (g : G) * epsV θ c.hn8 v * (g : G)⁻¹ * g := by rw [h1]
      _ = g * epsV θ c.hn8 v := by group
  have hr2 : ((g : G) ^ b) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hN, pow_orderOf_eq_one]
  have hgK := Subgroup.mem_inf.1 hg
  have hrL : (g : G) ^ b ∈ L := mem_L_of_two_pow c (pow_mem hgK.2 b) hr2
  have hrC0 : (g : G) ^ b ∈ N0.C0 θ c.hn8 z := by
    refine (N0.mem_C0_iff c.hn8 c _).2 ⟨fun i => ?_, ?_⟩
    · exact (mem_centralizer_iff.1 (pow_mem hgE b) _ (N0.eps_mem_E θ c.hn8 i)).symm
    · exact mem_centralizer_singleton_iff.1 (pow_mem (Subgroup.mem_inf.1 hgK.1).2 b)
  have hrE : (g : G) ^ b ∈ E θ c.hn8 :=
    ModIso.mem_E_of_mem_sup c (N0.mem_B0_of_two_pow c.hn8 c hrC0 hr2) hrL
  have hmat : mat ι g ^ b = 1 := by
    rw [← map_pow, mat_eq_one_iff]
    intro x hx
    rw [Subgroup.coe_pow, comm_of_coords ι (hι.E_le hrE) hx, mul_inv_cancel_right]
  exact eq_one_of_red_of_odd hred hb hmat

theorem mat_eq_of_red_eq (c : Config G L Q n θ z) (hι : ECoords θ c.hn8 m A ι)
    {g g' : normalizer (A : Set G)} (hg : (g : G) ∈ KA L z A) (hg' : (g' : G) ∈ KA L z A)
    (hred : red m (mat ι g) = red m (mat ι g')) : mat ι g = mat ι g' := by
  have hm := hι.one_le
  have h1 : mat ι (g⁻¹ * g') = 1 := by
    refine mat_eq_one_of_red c hι (mul_mem (inv_mem hg) hg') ?_
    rw [map_mul, red_mul hm, ← hred, ← red_mul hm, ← map_mul, inv_mul_cancel, map_one, red_one hm]
  calc mat ι g = mat ι g * mat ι (g⁻¹ * g') := by rw [h1, Matrix.mul_one]
    _ = mat ι g' := by rw [← map_mul, mul_inv_cancel_left]

omit [Finite G] in
theorem exists_lift {hn : 8 ≤ n} (h : LevelDatum θ hn z m A) (hι : ECoords θ hn m A ι)
    (M : GL (Fin 3) (ZMod 2)) : ∃ g : normalizer (A : Set G), (g : G) ∈ KA L z A ∧
      red m (mat ι g) = (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  obtain ⟨g, hgK, hgE⟩ := h.cover M
  exact ⟨⟨g, (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hgK).1).1⟩, hgK,
    red_mat_eq_of_conj hι _ hgE⟩

theorem genRel_of_lift (c : Config G L Q n θ z) (hι : ECoords θ c.hn8 m A ι)
    {kx ky : normalizer (A : Set G)} (hkx : (kx : G) ∈ KA L z A) (hky : (ky : G) ∈ KA L z A)
    (hrx : red m (mat ι kx) = x2M) (hry : red m (mat ι ky) = y2M) :
    mat ι kx * mat ι kx = 1 ∧ mat ι ky * mat ι ky * mat ι ky = 1 ∧
      (mat ι kx * mat ι ky) ^ 7 = 1 ∧
      (mat ι kx * mat ι ky * mat ι kx * (mat ι ky * mat ι ky)) ^ 4 = 1 := by
  have hm := hι.one_le
  obtain ⟨r1, r2, r3, r4⟩ := genRel_x2M_y2M
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul]
    refine mat_eq_one_of_red c hι (mul_mem hkx hkx) ?_
    rw [map_mul, red_mul hm, hrx, r1]
  · rw [← map_mul, ← map_mul]
    refine mat_eq_one_of_red c hι (mul_mem (mul_mem hky hky) hky) ?_
    rw [map_mul, map_mul, red_mul hm, red_mul hm, hry, r2]
  · rw [← map_mul, ← map_pow]
    refine mat_eq_one_of_red c hι (pow_mem (mul_mem hkx hky) 7) ?_
    rw [map_pow, map_mul, red_pow hm, red_mul hm, hrx, hry, r3]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_pow]
    refine mat_eq_one_of_red c hι
      (pow_mem (mul_mem (mul_mem (mul_mem hkx hky) hkx) (mul_mem hky hky)) 4) ?_
    rw [map_pow, map_mul, map_mul, map_mul, map_mul, red_pow hm, red_mul hm, red_mul hm,
      red_mul hm, red_mul hm, hrx, hry, r4]

end I1

section I3

open ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {A : Subgroup G}

theorem std_coords_two (c : Config G L Q n θ z)
    (h : LevelDatum θ c.hn8 z 2 A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 2)), ECoords θ c.hn8 2 A ι ∧
      ∃ kx ky : normalizer (A : Set G), (kx : G) ∈ KA L z A ∧ (ky : G) ∈ KA L z A ∧
        mat ι kx = FourCube.X0 ∧ mat ι ky = FourCube.Y0 := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  obtain ⟨kx, hkx, hrx⟩ := exists_lift h hι x2G
  obtain ⟨ky, hky, hry⟩ := exists_lift h hι y2G
  rw [val_x2G] at hrx
  rw [val_y2G] at hry
  obtain ⟨r1, r2, r3, r4⟩ := genRel_of_lift c hι hkx hky hrx hry
  obtain ⟨K, K', hKK', hK'K, hK1, hX, hY⟩ := exists_conj_std4 (X := mat ι kx) (Y := mat ι ky)
    ⟨r1, r2, r3, r4⟩ (by rw [redHom_eq_red, hrx, redHom_X0])
    (by rw [redHom_eq_red, hry, redHom_Y0])
  have hK1' : red 2 K = 1 := by rw [← redHom_eq_red]; exact hK1
  refine ⟨ι.trans (coordChange K K' hKK' hK'K),
    hι.coordChange ι K K' hKK' hK'K (red_eq_one_of_mul (by norm_num) hKK' hK1'),
    kx, ky, hkx, hky, ?_, ?_⟩
  · rw [mat_coordChange]
    exact hX
  · rw [mat_coordChange]
    exact hY

theorem std_coords_three
    (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z 3 A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 3)), ECoords θ c.hn8 3 A ι ∧
      ∃ kx ky : normalizer (A : Set G), (kx : G) ∈ KA L z A ∧ (ky : G) ∈ KA L z A ∧
        mat ι kx = X8 ∧ mat ι ky = Y8 := by
  obtain ⟨ι, hι⟩ := h.exists_ecoords
  obtain ⟨kx, hkx, hrx⟩ := exists_lift h hι x2G
  obtain ⟨ky, hky, hry⟩ := exists_lift h hι y2G
  rw [val_x2G] at hrx
  rw [val_y2G] at hry
  obtain ⟨r1, r2, r3, r4⟩ := genRel_of_lift c hι hkx hky hrx hry
  have hrel8 : GenRel8 (mat ι kx) (mat ι ky) := ⟨r1, r2, r3, r4⟩
  obtain ⟨k, k', hkk', hk'k, hk1, hX4, hY4⟩ := exists_conj_std4 (genRel_red84 hrel8)
    (by rw [redHom_red84, redHom_X0]; exact hrx) (by rw [redHom_red84, redHom_Y0]; exact hry)
  obtain ⟨K', hKK', hK'K, hK'r⟩ := exists_lift_inv hkk'
  set K := lift48 k with hK
  have hrel8' : GenRel8 (K * mat ι kx * K') (K * mat ι ky * K') := genRel8_conj hK'K hrel8
  have hX8 : red84 (K * mat ι kx * K') = FourCube.X0 := by
    rw [map_mul, map_mul, hK, red84_lift48, hK'r, hX4]
  have hY8 : red84 (K * mat ι ky * K') = FourCube.Y0 := by
    rw [map_mul, map_mul, hK, red84_lift48, hK'r, hY4]
  obtain ⟨P, P', hPP', hP'P, hP1, hPX, hPY⟩ := exists_conj_std8 hrel8' hX8 hY8
  have hT1 : (P * K) * (K' * P') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc K K', hKK', Matrix.one_mul, hPP']
  have hT2 : (K' * P') * (P * K) = 1 := mul_eq_one_comm.1 hT1
  have hTr : red 3 (P * K) = 1 := by
    rw [← redHom_red84, map_mul, hP1, Matrix.one_mul, hK, red84_lift48]
    exact hk1
  refine ⟨ι.trans (coordChange (P * K) (K' * P') hT1 hT2),
    hι.coordChange ι _ _ hT1 hT2 (red_eq_one_of_mul (by norm_num) hT1 hTr),
    kx, ky, hkx, hky, ?_, ?_⟩
  · rw [mat_coordChange, ← hPX]
    simp only [Matrix.mul_assoc]
  · rw [mat_coordChange, ← hPY]
    simp only [Matrix.mul_assoc]

end I3

section I4

open ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {m : ℕ} {A : Subgroup G}
  {ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ m))}

theorem kap_mem_KA (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A) (t : sylowT) :
    ModIso.kap θ c.hn8 (t : GL (Fin 3) (ZMod 2)) ∈ KA L z A :=
  Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨DU_le_normalizer c h (kap_mem_DU θ c.hn8 t),
    L_le_centralizer_z c (ModIso.kap_mem_L θ c.hn8 _)⟩, mem_sup_left (ModIso.kap_mem_L θ c.hn8 _)⟩

@[expose] noncomputable def kapN (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A) :
    sylowT →* normalizer (A : Set G) :=
  ((ModIso.kap θ c.hn8).comp sylowT.subtype).codRestrict _ fun t =>
    DU_le_normalizer c h (kap_mem_DU θ c.hn8 t)

theorem coe_kapN (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A) (t : sylowT) :
    (kapN c h t : G) = ModIso.kap θ c.hn8 (t : GL (Fin 3) (ZMod 2)) := rfl

theorem kap_conj_el_of_table (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z m A)
    (hι : ECoords θ c.hn8 m A ι)
    (D : ZMod 2 → ZMod 2 → ZMod 2 → Matrix (Fin 3) (Fin 3) (ZMod (2 ^ m)))
    (hD : ∀ a b c a' b' c', D a b c * D a' b' c' = D (a + a') (b + b' + a * c') (c + c'))
    (h0 : D 0 0 0 = 1)
    (hx : ∃ g : normalizer (A : Set G), (g : G) ∈ KA L z A ∧ mat ι g = D 1 0 0 ∧
      red m (mat ι g) = unitri 1 0 0)
    (hy : ∃ g : normalizer (A : Set G), (g : G) ∈ KA L z A ∧ mat ι g = D 0 0 1 ∧
      red m (mat ι g) = unitri 0 0 1) (a b d : ZMod 2) (x : Fin 3 → ZMod (2 ^ m)) :
    ModIso.kap θ c.hn8 (unitriGL a b d) * el ι x * (ModIso.kap θ c.hn8 (unitriGL a b d))⁻¹ =
      el ι (D a b d *ᵥ x) := by
  have hred : ∀ t : sylowT, red m (mat ι (kapN c h t)) =
      ((t : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := fun t =>
    red_mat_eq_of_conj hι _ fun v => by rw [coe_kapN, kap_conj_epsV]
  have hgen : ∀ t : sylowT, ∀ Dt : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ m)),
      (∃ g : normalizer (A : Set G), (g : G) ∈ KA L z A ∧ mat ι g = Dt ∧
        red m (mat ι g) = ((t : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) →
      mat ι (kapN c h t) = Dt := by
    rintro t Dt ⟨g, hgK, hgD, hgr⟩
    rw [← hgD]
    exact mat_eq_of_red_eq c hι (kap_mem_KA c h t) hgK (by rw [hred, hgr])
  have hF : (mat ι).comp (kapN c h) = tableHom D hD h0 := by
    refine MonoidHom.eq_of_eqOn_dense closure_uxT_uyT ?_
    rintro t (rfl | rfl)
    · rw [MonoidHom.comp_apply, hgen uxT (D 1 0 0) hx]
      exact (tableHom_apply D hD h0 1 0 0).symm
    · rw [MonoidHom.comp_apply, hgen uyT (D 0 0 1) hy]
      exact (tableHom_apply D hD h0 0 0 1).symm
  have h1 : mat ι (kapN c h (tripleEquiv (a, b, d))) = D a b d := by
    rw [← MonoidHom.comp_apply, hF, tableHom_apply]
  have h2 := mat_spec ι (kapN c h (tripleEquiv (a, b, d))) x
  rw [h1, coe_kapN] at h2
  exact h2

theorem exists_termData_std_two (c : Config G L Q n θ z)
    (h : LevelDatum θ c.hn8 z 2 A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 2)), ECoords θ c.hn8 2 A ι ∧
      ∀ (a b d : ZMod 2) (x : Fin 3 → ZMod (2 ^ 2)),
        ModIso.kap θ c.hn8 (unitriGL a b d) * el ι x * (ModIso.kap θ c.hn8 (unitriGL a b d))⁻¹ =
          el ι (Z4M.dMat a b d *ᵥ x) := by
  obtain ⟨ι, hι, kx, ky, hkx, hky, hX, hY⟩ := std_coords_two c h
  have hm : 1 ≤ 2 := by norm_num
  have hrx : red 2 (mat ι kx) = x2M := by rw [hX, ← redHom_eq_red, redHom_X0]
  have hry : red 2 (mat ι ky) = y2M := by rw [hY, ← redHom_eq_red, redHom_Y0]
  refine ⟨ι, hι, kap_conj_el_of_table c h hι (fun a b d => Z4M.dMat a b d) Z4M.dMat_mul
    Z4M.dMat_zero ⟨kx * ky * kx * ky * ky * kx, ?_, ?_, ?_⟩
    ⟨kx * ky * ky * kx * ky * kx, ?_, ?_, ?_⟩⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hkx hky) hkx) hky) hky) hkx
  · simp only [map_mul, hX, hY]
    exact word4_x
  · simp only [map_mul, red_mul hm, hrx, hry]
    exact word2_x
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hkx hky) hky) hkx) hky) hkx
  · simp only [map_mul, hX, hY]
    exact word4_y
  · simp only [map_mul, red_mul hm, hrx, hry]
    exact word2_y

theorem exists_termData_std_three
    (c : Config G L Q n θ z) (h : LevelDatum θ c.hn8 z 3 A) :
    ∃ ι : A ≃* Multiplicative (Fin 3 → ZMod (2 ^ 3)), ECoords θ c.hn8 3 A ι ∧
      ∀ (a b d : ZMod 2) (x : Fin 3 → ZMod (2 ^ 3)),
        ModIso.kap θ c.hn8 (unitriGL a b d) * el ι x * (ModIso.kap θ c.hn8 (unitriGL a b d))⁻¹ =
          el ι (Z8M.dMat a b d *ᵥ x) := by
  obtain ⟨ι, hι, kx, ky, hkx, hky, hX, hY⟩ := std_coords_three c h
  have hm : 1 ≤ 3 := by norm_num
  have hrx : red 3 (mat ι kx) = x2M := by
    rw [hX, ← redHom_red84, red84_X8, redHom_X0]
  have hry : red 3 (mat ι ky) = y2M := by
    rw [hY, ← redHom_red84, red84_Y8, redHom_Y0]
  refine ⟨ι, hι, kap_conj_el_of_table c h hι (fun a b d => Z8M.dMat a b d) Z8M.dMat_mul
    Z8M.dMat_zero ⟨kx * ky * kx * ky * ky * kx, ?_, ?_, ?_⟩
    ⟨kx * ky * ky * kx * ky * kx, ?_, ?_, ?_⟩⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hkx hky) hkx) hky) hky) hkx
  · simp only [map_mul, hX, hY]
    exact word8_x
  · simp only [map_mul, red_mul hm, hrx, hry]
    exact word2_x
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hkx hky) hky) hkx) hky) hkx
  · simp only [map_mul, hX, hY]
    exact word8_y
  · simp only [map_mul, red_mul hm, hrx, hry]
    exact word2_y

end I4

end CFSG.OddStandard.AltStdSmall4.G2
