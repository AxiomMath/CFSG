module

public import CFSG.HardMathSupport.U4FF.ClassLocCheck

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups

theorem matrix_sub_eq_add {k : Type*} [Field k] [CharP k 2] {n m : Type*} (M N : Matrix n m k) :
    M - N = M + N := by
  ext x y
  simp [Matrix.sub_apply, Matrix.add_apply, CharTwo.sub_eq_add]

section Masks

variable (n m : ℕ)

theorem toMat_zrow (zeta : ℕ) :
    (zrowOf n zeta).toMat 1 n = Matrix.of fun (_ : Fin 1) (x : Fin n) => bitF zeta (x : ℕ) := by
  ext i x
  have hx : (x : ℕ) < n := x.isLt
  have h1 : (zrowOf n zeta).getD (x : ℕ) 0 = if zeta.testBit (x : ℕ) then 1 else 0 := by
    simp [zrowOf, Array.getD_eq_getD_getElem?, hx]
  show bitF ((zrowOf n zeta).getD (x : ℕ) 0) (i : ℕ) = bitF zeta (x : ℕ)
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  rw [h1, hi]
  by_cases hb : zeta.testBit (x : ℕ)
  · simp [hb, bitF]
  · simp [hb, bitF]

theorem size_zrow (zeta : ℕ) : (zrowOf n zeta).size = n := by simp [zrowOf]

end Masks

section Spec

variable (fs : List FK) (m : ℕ) (bcols pmcols : MCols) (z zeta : ℕ)

theorem toMat_piMasks (hb : bcols.size = m) (hp : pmcols.size = ambDim fs) :
    (MCols.add (MCols.mul bcols pmcols)
        (MCols.mul (MCols.col z) (zrowOf (ambDim fs) zeta))).toMat (ambDim fs) (ambDim fs) =
      bcols.toMat (ambDim fs) m * pmcols.toMat m (ambDim fs) +
        vecMulVec (fun x : Fin (ambDim fs) => bitF z (x : ℕ))
          (fun x : Fin (ambDim fs) => bitF zeta (x : ℕ)) := by
  have hs1 : (MCols.mul bcols pmcols).size = ambDim fs := by rw [size_mul, hp]
  have hs2 : (MCols.mul (MCols.col z) (zrowOf (ambDim fs) zeta)).size = ambDim fs := by
    rw [size_mul, size_zrow]
  rw [toMat_add _ _ _ _ hs1 hs2, toMat_mul _ _ _ _ _ hb hp,
    toMat_mul _ _ _ _ _ (size_col z) (size_zrow _ zeta), toMat_col, toMat_zrow]
  congr 1
  ext i y
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply]

theorem size_piMasks (hp : pmcols.size = ambDim fs) :
    (MCols.add (MCols.mul bcols pmcols)
        (MCols.mul (MCols.col z) (zrowOf (ambDim fs) zeta))).size = ambDim fs := by
  rw [size_add _ _ (by rw [size_mul, size_mul, size_zrow, hp]), size_mul, hp]

@[expose, reducible] noncomputable def LocSpec.ofMasks
    (hb : bcols.size = m) (hp : pmcols.size = ambDim fs)
    (h1 : MCols.mul pmcols bcols = MCols.one m)
    (h2 : MCols.apply pmcols z = 0)
    (h3 : MCols.mul (zrowOf (ambDim fs) zeta) bcols = MCols.zero m)
    (h4 : MCols.apply (MCols.add (MCols.mul bcols pmcols)
        (MCols.mul (MCols.col z) (zrowOf (ambDim fs) zeta))) z = z)
    (h5 : ∀ i j : Fin 4, i ≠ j → ∀ r ∈ Finset.range (fs.length + 1),
      MCols.mul (MCols.add (MCols.mul bcols pmcols)
          (MCols.mul (MCols.col z) (zrowOf (ambDim fs) zeta)))
        (MCols.mul (tabD fs i j r) bcols) = MCols.mul (tabD fs i j r) bcols)
    (h6 : ∀ i j : Fin 4, i ≠ j → ∀ r ∈ Finset.range (fs.length + 1),
      MCols.apply (tabD fs i j r) z = if r = 0 then z else 0) : LocSpec fs where
  m := m
  B := bcols.toMat (ambDim fs) m
  Pm := pmcols.toMat m (ambDim fs)
  z := fun x => bitF z (x : ℕ)
  zeta := fun x => bitF zeta (x : ℕ)
  pm_B := by
    have := toMat_mul pmcols bcols m (ambDim fs) m hp hb
    rw [h1, toMat_one] at this
    exact this.symm
  pm_z := by
    have := toMat_apply pmcols m (ambDim fs) hp z
    rw [h2] at this
    funext i
    have h := congrFun this i
    simp only [bitF_zero] at h
    exact h.symm
  zeta_B := by
    have := toMat_mul (zrowOf (ambDim fs) zeta) bcols 1 (ambDim fs) m (size_zrow _ zeta) hb
    rw [h3, toMat_zero, toMat_zrow] at this
    funext t
    have h := congrFun (congrFun this 0) t
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using h.symm
  pi_z := by
    have hPi := toMat_piMasks fs m bcols pmcols z zeta hb hp
    have hs := size_piMasks fs bcols pmcols z zeta hp
    have h := toMat_apply _ (ambDim fs) (ambDim fs) hs z
    rw [h4, hPi] at h
    exact h.symm
  inv := by
    intro i j hij r
    by_cases hr : r < fs.length + 1
    · have hD : (tabD fs i j r).toMat (ambDim fs) (ambDim fs) = ambDF fs i j r := toMat_tab _
      have hs1 : (tabD fs i j r).size = ambDim fs := tab_size _
      have hPi := toMat_piMasks fs m bcols pmcols z zeta hb hp
      have hsPi := size_piMasks fs bcols pmcols z zeta hp
      have h := congrArg (fun A : MCols => A.toMat (ambDim fs) m) (h5 i j hij r
        (Finset.mem_range.mpr hr))
      rw [toMat_mul _ _ _ _ _ hsPi (by rw [size_mul, hb]), toMat_mul _ _ _ _ _ hs1 hb, hPi,
        hD] at h
      exact h
    · have hz : ambDF fs i j r = 0 := ambDF_eq_zero_of_lt fs i j (by omega)
      show _ * (ambDF fs i j r * _) = ambDF fs i j r * _
      rw [hz]
      simp
  z_fix := by
    intro i j hij r
    by_cases hr : r < fs.length + 1
    · have hD : (tabD fs i j r).toMat (ambDim fs) (ambDim fs) = ambDF fs i j r := toMat_tab _
      have hs1 : (tabD fs i j r).size = ambDim fs := tab_size _
      have h := toMat_apply (tabD fs i j r) (ambDim fs) (ambDim fs) hs1 z
      rw [h6 i j hij r (Finset.mem_range.mpr hr), hD] at h
      funext x
      have hx := congrFun h x
      by_cases h0 : r = 0
      · rw [if_pos h0] at hx ⊢
        exact hx.symm
      · rw [if_neg h0] at hx ⊢
        rw [bitF_zero] at hx
        exact hx.symm
    · have hz : ambDF fs i j r = 0 := ambDF_eq_zero_of_lt fs i j (by omega)
      have h0 : r ≠ 0 := by omega
      rw [hz]
      simp [h0]

end Spec

@[expose, reducible] noncomputable def locSpec (a b c : Bool) (h : LocValid1 a b c) : LocSpec (fsOf a b c) :=
  LocSpec.ofMasks (fsOf a b c) (locM a b c) (locData a b c).bcols (locData a b c).pmcols
    (locData a b c).z (locData a b c).zeta h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1

@[expose] def hwVec (fs : List FK) : Fin (ambDim fs) → ZMod 2 := fun x => bitF (1 <<< hwEnc fs) x

section Hw

variable {fs : List FK} (S : LocSpec fs) {k : Type*} [Field k] [CharP k 2]

theorem ambDF_zero (fs : List FK) (i j : Fin 4) : ambDF fs i j 0 = 1 := by
  have h : ambD fs i j 0 = 1 := by
    unfold ambD
    have : ((Finset.univ : Finset (Finset (Fin fs.length))).filter (fun S => S.card = 0)) =
        {∅} := by
      ext S
      simp [Finset.card_eq_zero]
    rw [this, Finset.sum_singleton]
    unfold ambZ
    simp only [Finset.notMem_empty, if_false]
    exact kronDep_one
  ext x y
  simp [ambDF, h, Matrix.submatrix_apply, Matrix.one_apply]

theorem vecMulVec_mulVec' {R : Type*} [CommSemiring R] {α : Type*} [Fintype α] (u w v : α → R) :
    vecMulVec u w *ᵥ v = (w ⬝ᵥ v) • u := by
  funext x
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem LocSpec.locMat_fixes {v : Fin (ambDim fs) → ZMod 2} (hv : S.Pi *ᵥ v = v)
    (hfix : ∀ i j : Fin 4, i < j → ∀ r ∈ Finset.range (fs.length + 1), 1 ≤ r →
      ambDF fs i j r *ᵥ v = 0) {i j : Fin 4} (hij : i ≠ j) (hlt : i < j) (t : k) :
    S.locMat k (Matrix.SpecialLinearGroup.transvection hij t) *ᵥ
        (S.Pmk k *ᵥ (fun x => f2 k (v x))) = S.Pmk k *ᵥ (fun x => f2 k (v x)) := by
  set vk : Fin (ambDim fs) → k := fun x => f2 k (v x) with hvk
  have hPi : S.Pik k *ᵥ vk = vk := by
    rw [LocSpec.Pik_eq_map, hvk, map_mulVec', hv]
  have hamb : ambRepF k fs (Matrix.SpecialLinearGroup.transvection hij t) *ᵥ vk = vk := by
    rw [ambRepF_transvection k fs hij t, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec]
    have hr' : ∀ r ∈ Finset.range (fs.length + 1), r ≠ 0 →
        (ambDF fs i j r).map (f2 k) *ᵥ vk = 0 := by
      intro r hrr hr0
      rw [hvk, map_mulVec', hfix i j hlt r hrr (Nat.one_le_iff_ne_zero.mpr hr0)]
      funext x
      simp
    rw [Finset.sum_eq_single 0 (fun r hrr hr0 => by rw [hr' r hrr hr0]; simp) (by simp)]
    rw [ambDF_zero]
    simp
  have hz := (S.Stab_all (k := k) (Matrix.SpecialLinearGroup.transvection hij t)).2
  have hBP : S.Bk k *ᵥ (S.Pmk k *ᵥ vk) = vk - (S.zetak k ⬝ᵥ vk) • S.zk k := by
    have h1 : S.Pik k *ᵥ vk = (S.Bk k * S.Pmk k) *ᵥ vk +
        (vecMulVec (S.zk k) (S.zetak k)) *ᵥ vk := by
      unfold LocSpec.Pik
      rw [Matrix.add_mulVec]
    rw [hPi, vecMulVec_mulVec', ← Matrix.mulVec_mulVec] at h1
    rw [eq_sub_iff_add_eq]
    exact h1.symm
  have hmain : S.locMat k (Matrix.SpecialLinearGroup.transvection hij t) *ᵥ
      (S.Pmk k *ᵥ vk) = S.Pmk k *ᵥ (ambRepF k fs
        (Matrix.SpecialLinearGroup.transvection hij t) *ᵥ (S.Bk k *ᵥ (S.Pmk k *ᵥ vk))) := by
    unfold LocSpec.locMat
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmain, hBP, Matrix.mulVec_sub, Matrix.mulVec_smul, hz, hamb, Matrix.mulVec_sub,
    Matrix.mulVec_smul, S.Pmk_z k]
  simp

end Hw

section Rank

variable {k : Type*} [Field k] [CharP k 2]

theorem rank_of_RankOK {m : ℕ} (M : MCols) (R : RankData) (h : RankOK m M R) :
    ((M.toMat m m).map (f2 k)).rank = R.r := by
  obtain ⟨hM, hx, hy, hxl, hyr, hMXY, hXl⟩ := h
  have h1 : M.toMat m m = MCols.toMat R.x m R.r * MCols.toMat R.y R.r m := by
    conv_lhs => rw [hMXY]
    exact toMat_mul R.x R.y m R.r m hx hy
  have h2 : MCols.toMat R.xl R.r m * (M.toMat m m * MCols.toMat R.yr m R.r) = 1 := by
    have e1 := toMat_mul R.xl (MCols.mul M R.yr) R.r m R.r hxl (by rw [size_mul, hyr])
    rw [hXl, toMat_one, toMat_mul M R.yr m m R.r hM hyr] at e1
    exact e1.symm
  have h1k : (M.toMat m m).map (f2 k) =
      (MCols.toMat R.x m R.r).map (f2 k) * (MCols.toMat R.y R.r m).map (f2 k) := by
    rw [h1, Matrix.map_mul]
  have h2k : (MCols.toMat R.xl R.r m).map (f2 k) *
      (((M.toMat m m).map (f2 k)) * (MCols.toMat R.yr m R.r).map (f2 k)) = 1 := by
    have := congrArg (fun A : Matrix (Fin R.r) (Fin R.r) (ZMod 2) => A.map (f2 k)) h2
    simpa [Matrix.map_mul] using this
  apply le_antisymm
  · rw [h1k]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  · have hr1 : (1 : Matrix (Fin R.r) (Fin R.r) k).rank = R.r := by
      rw [Matrix.rank_one, Fintype.card_fin]
    calc R.r = (1 : Matrix (Fin R.r) (Fin R.r) k).rank := hr1.symm
      _ = ((MCols.toMat R.xl R.r m).map (f2 k) *
          (((M.toMat m m).map (f2 k)) * (MCols.toMat R.yr m R.r).map (f2 k))).rank := by rw [h2k]
      _ ≤ (((M.toMat m m).map (f2 k)) * (MCols.toMat R.yr m R.r).map (f2 k)).rank :=
          Matrix.rank_mul_le_right _ _
      _ ≤ ((M.toMat m m).map (f2 k)).rank := Matrix.rank_mul_le_left _ _

end Rank

section Elem

theorem toMat_foldl_add {n : ℕ} (f : ℕ → MCols) (hf : ∀ r, (f r).size = n) :
    ∀ (l : List ℕ) (acc : MCols), acc.size = n →
      (l.foldl (fun A r => MCols.add A (f r)) acc).size = n ∧
      (l.foldl (fun A r => MCols.add A (f r)) acc).toMat n n =
        acc.toMat n n + (l.map fun r => (f r).toMat n n).sum := by
  intro l
  induction l with
  | nil =>
    intro acc hacc
    exact ⟨hacc, by simp⟩
  | cons r l ih =>
    intro acc hacc
    have hs : (MCols.add acc (f r)).size = n := by rw [size_add _ _ (by rw [hf, hacc]), hacc]
    obtain ⟨h1, h2⟩ := ih (MCols.add acc (f r)) hs
    refine ⟨h1, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [h2, toMat_add _ _ _ _ hacc (hf r), add_assoc]

theorem list_range_map_sum {α : Type*} [AddCommMonoid α] (g : ℕ → α) (m : ℕ) :
    ((List.range m).map g).sum = ∑ r ∈ Finset.range m, g r := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem elemMasks_size (fs : List FK) (i j : Fin 4) : (elemMasks fs i j).size = ambDim fs :=
  (toMat_foldl_add (fun r => tabD fs i j r) (fun r => tab_size _) (List.range (fs.length + 1))
    (MCols.zero (ambDim fs)) (size_zero _)).1

theorem toMat_elemMasks (fs : List FK) (i j : Fin 4) :
    (elemMasks fs i j).toMat (ambDim fs) (ambDim fs) =
      ∑ r ∈ Finset.range (fs.length + 1), ambDF fs i j r := by
  have h := (toMat_foldl_add (fun r => tabD fs i j r) (fun r => tab_size _)
    (List.range (fs.length + 1)) (MCols.zero (ambDim fs)) (size_zero _)).2
  rw [toMat_zero, zero_add, list_range_map_sum] at h
  have e : ∀ r, (tabD fs i j r).toMat (ambDim fs) (ambDim fs) = ambDF fs i j r :=
    fun r => toMat_tab _
  simp only [e] at h
  exact h

variable {k : Type*} [Field k] [CharP k 2]

theorem ambRepF_elem (fs : List FK) {i j : Fin 4} (hij : i ≠ j) :
    ambRepF k fs (Matrix.SpecialLinearGroup.transvection hij 1) =
      ((elemMasks fs i j).toMat (ambDim fs) (ambDim fs)).map (f2 k) := by
  rw [ambRepF_transvection k fs hij 1, toMat_elemMasks]
  have : (∑ r ∈ Finset.range (fs.length + 1), ambDF fs i j r).map (f2 k) =
      ∑ r ∈ Finset.range (fs.length + 1), (ambDF fs i j r).map (f2 k) :=
    map_sum (f2 k).mapMatrix.toAddMonoidHom _ _
  rw [this]
  simp

end Elem

section RankLoc

variable {k : Type*} [Field k] [CharP k 2]

@[expose] def a1 (k : Type*) [Field k] : SL(4, k) :=
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 3) (by decide) 1

@[expose] def a2 (k : Type*) [Field k] : SL(4, k) :=
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 2) (by decide) 1 *
    Matrix.SpecialLinearGroup.transvection (i := 1) (j := 3) (by decide) 1

theorem locMat_sub_one_of (a b c : Bool) (h1 : LocValid1 a b c) (A : SL(4, k))
    (E : MCols) (hE : E.size = ambDim (fsOf a b c))
    (hA : ambRepF k (fsOf a b c) A = (E.toMat (ambDim (fsOf a b c)) (ambDim (fsOf a b c))).map (f2 k)) :
    (locSpec a b c h1).locMat k A - 1 =
      ((locOpMasks (locData a b c) (MCols.add E (MCols.one (ambDim (fsOf a b c))))).toMat
        (locM a b c) (locM a b c)).map (f2 k) := by
  have hb := h1.1
  have hp := h1.2.1
  have hs : (MCols.add E (MCols.one (ambDim (fsOf a b c)))).size = ambDim (fsOf a b c) := by
    rw [size_add _ _ (by rw [size_one, hE]), hE]
  unfold locOpMasks
  rw [toMat_mul _ _ _ _ _ hp (by rw [size_mul, hb]),
    toMat_mul _ _ _ _ _ hs hb, toMat_add _ _ _ _ hE (size_one _), toMat_one]
  have hPmB : (locData a b c).pmcols.toMat (locM a b c) (ambDim (fsOf a b c)) *
      (locData a b c).bcols.toMat (ambDim (fsOf a b c)) (locM a b c) = 1 := by
    have := toMat_mul (locData a b c).pmcols (locData a b c).bcols (locM a b c)
      (ambDim (fsOf a b c)) (locM a b c) hp hb
    rw [h1.2.2.1, toMat_one] at this
    exact this.symm
  show (locSpec a b c h1).Pmk k * (ambRepF k (fsOf a b c) A * (locSpec a b c h1).Bk k) - 1 = _
  rw [hA]
  have hmapMB : ((locData a b c).pmcols.toMat (locM a b c) (ambDim (fsOf a b c))).map (f2 k) *
      ((locData a b c).bcols.toMat (ambDim (fsOf a b c)) (locM a b c)).map (f2 k) = 1 := by
    rw [← Matrix.map_mul, hPmB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_add _ (map_add (f2 k)),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    hmapMB]
  have e1 : (locSpec a b c h1).Pmk k =
      ((locData a b c).pmcols.toMat (locM a b c) (ambDim (fsOf a b c))).map (f2 k) := rfl
  have e2 : (locSpec a b c h1).Bk k =
      ((locData a b c).bcols.toMat (ambDim (fsOf a b c)) (locM a b c)).map (f2 k) := rfl
  rw [e1, e2]
  exact matrix_sub_eq_add _ _

theorem rank_locMat_a1 (a b c : Bool) (h : LocValid a b c) :
    ((locSpec a b c h.1).locMat k (a1 k) - 1).rank = (locData a b c).rk1.r := by
  rw [locMat_sub_one_of a b c h.1 (a1 k) (elemMasks (fsOf a b c) 0 3)
    (elemMasks_size _ _ _) (ambRepF_elem (fsOf a b c) (by decide : (0 : Fin 4) ≠ 3))]
  exact rank_of_RankOK _ _ h.2.1.1

theorem rank_locMat_a2 (a b c : Bool) (h : LocValid a b c) :
    ((locSpec a b c h.1).locMat k (a2 k) - 1).rank = (locData a b c).rk2.r := by
  have hs1 := elemMasks_size (fsOf a b c) 0 2
  have hs2 := elemMasks_size (fsOf a b c) 1 3
  rw [locMat_sub_one_of a b c h.1 (a2 k)
    (MCols.mul (elemMasks (fsOf a b c) 0 2) (elemMasks (fsOf a b c) 1 3))
    (by rw [size_mul, hs2])]
  · exact rank_of_RankOK _ _ h.2.1.2.1
  · show ambRepF k (fsOf a b c) (_ * _) = _
    rw [map_mul, ambRepF_elem (fsOf a b c) (by decide : (0 : Fin 4) ≠ 2),
      ambRepF_elem (fsOf a b c) (by decide : (1 : Fin 4) ≠ 3),
      toMat_mul _ _ _ _ _ hs1 hs2, Matrix.map_mul]

end RankLoc

section PiIota

variable {k : Type*} [Field k] [CharP k 2]

theorem locMat_transvection {fs : List FK} (S : LocSpec fs) {i j : Fin 4} (hij : i ≠ j) (t : k)
    (N : ℕ) (hN : fs.length + 1 ≤ N) :
    S.locMat k (Matrix.SpecialLinearGroup.transvection hij t) =
      ∑ r ∈ Finset.range N, t ^ r • (S.Pm * (ambDF fs i j r * S.B)).map (f2 k) := by
  unfold LocSpec.locMat
  rw [ambRepF_transvection k fs hij t]
  have h0 : ∀ r ∈ Finset.range N, r ∉ Finset.range (fs.length + 1) →
      t ^ r • (S.Pm * (ambDF fs i j r * S.B)).map (f2 k) = 0 := by
    intro r _ hr
    have : fs.length < r := by
      simp only [Finset.mem_range, not_lt] at hr
      omega
    rw [ambDF_eq_zero_of_lt fs i j this]
    simp
  rw [← Finset.sum_subset (Finset.range_mono hN) h0]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul]
  refine Finset.sum_congr rfl fun r _ => ?_
  show _ = t ^ r • (S.Pm * (ambDF fs i j r * S.B)).map (f2 k)
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem toMat_dlocMasks (a b c : Bool) (h1 : LocValid1 a b c) (i j : Fin 4) (r : ℕ) :
    (dlocMasks (fsOf a b c) (locData a b c) i j r).toMat (locM a b c) (locM a b c) =
      (locSpec a b c h1).Pm * (ambDF (fsOf a b c) i j r * (locSpec a b c h1).B) := by
  have hb := h1.1
  have hp := h1.2.1
  have ht : (tabD (fsOf a b c) i j r).size = ambDim (fsOf a b c) := tab_size _
  have hD : (tabD (fsOf a b c) i j r).toMat (ambDim (fsOf a b c)) (ambDim (fsOf a b c)) =
      ambDF (fsOf a b c) i j r := toMat_tab _
  unfold dlocMasks
  rw [toMat_mul (locData a b c).pmcols (MCols.mul (tabD (fsOf a b c) i j r) (locData a b c).bcols)
    (locM a b c) (ambDim (fsOf a b c)) (locM a b c) hp (by rw [size_mul, hb]),
    toMat_mul (tabD (fsOf a b c) i j r) (locData a b c).bcols (ambDim (fsOf a b c))
      (ambDim (fsOf a b c)) (locM a b c) ht hb, hD]

theorem size_dlocMasks (a b c : Bool) (h1 : LocValid1 a b c) (i j : Fin 4) (r : ℕ) :
    (dlocMasks (fsOf a b c) (locData a b c) i j r).size = locM a b c := by
  unfold dlocMasks
  rw [size_mul, size_mul, h1.1]

@[expose] def picMat (a b c : Bool) :
    Matrix (Fin (locM a b c)) (Fin (locM true true true)) (ZMod 2) :=
  (locData a b c).pic.toMat (locM a b c) (locM true true true)

@[expose] def iocMat (a b c : Bool) :
    Matrix (Fin (locM true true true)) (Fin (locM a b c)) (ZMod 2) :=
  (locData a b c).ioc.toMat (locM true true true) (locM a b c)

theorem f2_map_comm {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (A : Matrix p q (ZMod 2)) (X : Matrix q q (ZMod 2)) (Y : Matrix p p (ZMod 2))
    (e : A * X = Y * A) :
    A.map (f2 k) * X.map (f2 k) = Y.map (f2 k) * A.map (f2 k) := by
  have := congrArg (fun M => M.map (f2 k)) e
  simpa only [Matrix.map_mul] using this

theorem pi_equivariant (a b c : Bool) (h1 : LocValid1 a b c) (h3 : LocValid3 a b c)
    (hρ : LocValid1 true true true)
    {i j : Fin 4} (hij : i ≠ j) (hji : j < i) (t : k) :
    (picMat a b c).map (f2 k) *
        (locSpec true true true hρ).locMat k (Matrix.SpecialLinearGroup.transvection hij t) =
      (locSpec a b c h1).locMat k (Matrix.SpecialLinearGroup.transvection hij t) *
        (picMat a b c).map (f2 k) := by
  rw [locMat_transvection (locSpec true true true hρ) hij t 4 (by decide),
    locMat_transvection (locSpec a b c h1) hij t 4 (by
      cases a <;> cases b <;> cases c <;> decide)]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  congr 1
  have hmask := (h3.2.2.2.2.2.2.2 i j hji r hr).1
  have e := congrArg (fun A : MCols => A.toMat (locM a b c) (locM true true true)) hmask
  rw [toMat_mul _ _ _ _ _ h3.1 (size_dlocMasks true true true hρ i j r),
    toMat_mul _ _ _ _ _ (size_dlocMasks a b c h1 i j r) h3.1,
    toMat_dlocMasks true true true hρ, toMat_dlocMasks a b c h1] at e
  exact f2_map_comm _ _ _ e

theorem iota_equivariant (a b c : Bool) (h1 : LocValid1 a b c) (h3 : LocValid3 a b c)
    (hρ : LocValid1 true true true)
    {i j : Fin 4} (hij : i ≠ j) (hji : j < i) (t : k) :
    (iocMat a b c).map (f2 k) *
        (locSpec a b c h1).locMat k (Matrix.SpecialLinearGroup.transvection hij t) =
      (locSpec true true true hρ).locMat k (Matrix.SpecialLinearGroup.transvection hij t) *
        (iocMat a b c).map (f2 k) := by
  rw [locMat_transvection (locSpec true true true hρ) hij t 4 (by decide),
    locMat_transvection (locSpec a b c h1) hij t 4 (by
      cases a <;> cases b <;> cases c <;> decide)]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  congr 1
  have hmask := (h3.2.2.2.2.2.2.2 i j hji r hr).2
  have e := congrArg (fun A : MCols => A.toMat (locM true true true) (locM a b c)) hmask
  rw [toMat_mul _ _ _ _ _ h3.2.2.1 (size_dlocMasks a b c h1 i j r),
    toMat_mul _ _ _ _ _ (size_dlocMasks true true true hρ i j r) h3.2.2.1,
    toMat_dlocMasks true true true hρ, toMat_dlocMasks a b c h1] at e
  exact f2_map_comm _ _ _ e

end PiIota

end CFSG.HardMathSupport.U4FF
