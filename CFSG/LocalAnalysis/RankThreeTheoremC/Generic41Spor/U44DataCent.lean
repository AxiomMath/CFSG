module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44DataTorus
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.RankThree.PartOne.KF.R7Levi

public section

open Matrix CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data

variable {F : Type} [Field F] {n : ℕ}

@[expose] def blk (A : Matrix (Fin n) (Fin n) F) (c : F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem blk_cc (A : Matrix (Fin n) (Fin n) F) (c : F) (i j : Fin n) :
    blk A c i.castSucc j.castSucc = A i j := by
  simp only [blk, Matrix.of_apply, Fin.lastCases_castSucc]

theorem blk_cl (A : Matrix (Fin n) (Fin n) F) (c : F) (i : Fin n) :
    blk A c i.castSucc (Fin.last n) = 0 := by
  simp only [blk, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem blk_lc (A : Matrix (Fin n) (Fin n) F) (c : F) (j : Fin n) :
    blk A c (Fin.last n) j.castSucc = 0 := by
  simp only [blk, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem blk_ll (A : Matrix (Fin n) (Fin n) F) (c : F) :
    blk A c (Fin.last n) (Fin.last n) = c := by
  simp only [blk, Matrix.of_apply, Fin.lastCases_last]

theorem blk_mul (A A' : Matrix (Fin n) (Fin n) F) (c c' : F) :
    blk A c * blk A' c' = blk (A * A') (c * c') := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [blk_cl, blk_lc, blk_ll, mul_zero, Finset.sum_const_zero, zero_add]
    | cast j =>
      simp only [blk_cc, blk_lc, blk_ll, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [blk_cc, blk_cl, blk_ll, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    | cast j => simp only [blk_cc, blk_cl, blk_lc, mul_zero, add_zero, Matrix.mul_apply]

theorem blk_one : blk (1 : Matrix (Fin n) (Fin n) F) 1 = 1 := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_ll]; exact (Matrix.one_apply_eq _).symm
    | cast j => rw [blk_lc, Matrix.one_apply_ne]; exact (Fin.castSucc_lt_last j).ne'
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [blk_cl, Matrix.one_apply_ne]; exact (Fin.castSucc_lt_last i).ne
    | cast j => rw [blk_cc]; simp only [Matrix.one_apply, Fin.castSucc_inj]

theorem blk_inj {A A' : Matrix (Fin n) (Fin n) F} {c c' : F} (h : blk A c = blk A' c') :
    A = A' ∧ c = c' := by
  constructor
  · ext i j
    have := congrFun (congrFun h i.castSucc) j.castSucc
    rwa [blk_cc, blk_cc] at this
  · have := congrFun (congrFun h (Fin.last n)) (Fin.last n)
    rwa [blk_ll, blk_ll] at this

theorem det_blk (A : Matrix (Fin n) (Fin n) F) (c : F) : (blk A c).det = A.det * c := by
  rw [Matrix.det_succ_row (blk A c) (Fin.last n), Fin.sum_univ_castSucc]
  have h1 : ((blk A c).submatrix (Fin.last n).succAbove (Fin.last n).succAbove) = A := by
    ext i j
    rw [Matrix.submatrix_apply, Fin.succAbove_last, blk_cc]
  simp only [blk_lc, blk_ll, h1, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  simp only [Fin.val_last]
  rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul, mul_comm]

theorem blk_transpose (A : Matrix (Fin n) (Fin n) F) (c : F) : (blk A c)ᵀ = blk Aᵀ c := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [Matrix.transpose_apply, blk_ll]
    | cast j => simp only [Matrix.transpose_apply, blk_lc, blk_cl]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [Matrix.transpose_apply, blk_lc, blk_cl]
    | cast j => simp only [Matrix.transpose_apply, blk_cc]

theorem blk_map (τ : F →+* F) (A : Matrix (Fin n) (Fin n) F) (c : F) :
    (blk A c).map τ = blk (A.map τ) (τ c) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [Matrix.map_apply, blk_ll]
    | cast j => simp only [Matrix.map_apply, blk_lc, map_zero]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [Matrix.map_apply, blk_cl, map_zero]
    | cast j => simp only [Matrix.map_apply, blk_cc]

variable (F n) in
@[expose] def embMat : Matrix (Fin n) (Fin n) F →* Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun A := blk A 1
  map_one' := blk_one
  map_mul' A B := by rw [blk_mul, mul_one]

variable (F n) in
@[expose] def embGL : GL (Fin n) F →* GL (Fin (n + 1)) F := Units.map (embMat F n)

theorem coe_embGL (X : GL (Fin n) F) :
    ((embGL F n X : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      blk (X : Matrix (Fin n) (Fin n) F) 1 := rfl

theorem embGL_injective : Function.Injective (embGL F n) := by
  intro X Y hXY
  have h1 : blk (X : Matrix (Fin n) (Fin n) F) 1 = blk (Y : Matrix (Fin n) (Fin n) F) 1 :=
    congrArg (fun g : GL (Fin (n + 1)) F => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) hXY
  exact Units.ext (blk_inj h1).1

theorem embGL_mem {X : GL (Fin 3) F16} (hX : X ∈ unitarySU 2 2 F16 3) :
    embGL F16 3 X ∈ unitarySU 2 2 F16 4 := by
  rw [mem_unitarySU_iff unitaryFieldData] at hX ⊢
  obtain ⟨hdet, hu⟩ := hX
  refine ⟨?_, ?_⟩
  · rw [coe_embGL, det_blk, hdet, one_mul]
  · rw [coe_embGL, blk_map, blk_transpose, blk_mul, hu, map_one, mul_one, blk_one]

@[expose] noncomputable def embSU3 : ↥(unitarySU 2 2 F16 3) →* ↥(unitarySU 2 2 F16 4) :=
  ((embGL F16 3).comp (unitarySU 2 2 F16 3).subtype).codRestrict _ fun X => embGL_mem X.2

theorem embSU3_injective : Function.Injective embSU3 := fun _ _ hXY =>
  Subtype.ext (embGL_injective (congrArg Subtype.val hXY))

theorem exists_mem_range_embSU3 (g : ↥(unitarySU 2 2 F16 4))
    (h1 : ∀ j : Fin 3,
      ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3) j.castSucc = 0)
    (h2 : ∀ j : Fin 3,
      ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) j.castSucc (Fin.last 3) = 0)
    (h3 : ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3) (Fin.last 3) = 1) :
    g ∈ embSU3.range := by
  set M : Matrix (Fin 4) (Fin 4) F16 := ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) with hM
  set B : Matrix (Fin 3) (Fin 3) F16 := Matrix.of fun i j => M i.castSucc j.castSucc with hB
  have hMB : M = blk B 1 := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [blk_ll]; exact h3
      | cast j => rw [blk_lc]; exact h1 j
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [blk_cl]; exact h2 i
      | cast j => rw [blk_cc]; rfl
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff unitaryFieldData).mp g.2
  rw [← hM] at hdet hu
  have hBdet : B.det = 1 := by
    rw [hMB, det_blk, mul_one] at hdet
    exact hdet
  have hBu : (B.map unitaryFieldData.bar)ᵀ * B = 1 := by
    rw [hMB, blk_map, blk_transpose, blk_mul, ← blk_one] at hu
    exact (blk_inj hu).1
  have hunit : IsUnit B.det := hBdet ▸ isUnit_one
  let u : GL (Fin 3) F16 := Matrix.nonsingInvUnit B hunit
  have hu_mem : u ∈ unitarySU 2 2 F16 3 := by
    rw [mem_unitarySU_iff unitaryFieldData]
    exact ⟨hBdet, hBu⟩
  refine ⟨⟨u, hu_mem⟩, Subtype.ext (Units.ext ?_)⟩
  show blk B 1 = M
  exact hMB.symm

theorem card_su3 : Nat.card ↥(unitarySU 2 2 F16 3) = 62400 := by
  have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int
    (unitaryFieldData) (n := 3) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 15 * 65 := by decide
  rw [hprod] at h
  have : (Nat.card ↥(unitarySU 2 2 F16 3) : ℤ) = 62400 := by
    rw [show unitarySU 2 2 F16 3 = StatedSU 3 (2 ^ 2) F16 from rfl, h]
    norm_num
  exact_mod_cast this

theorem pow_entry_last {g : GL (Fin 4) F16}
    (h2 : ∀ j : Fin 3,
      ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) j.castSucc (Fin.last 3) = 0)
    (m : ℕ) : (((g ^ m : GL (Fin 4) F16)) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3) (Fin.last 3) =
      (((g : GL (Fin 4) F16)) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3) (Fin.last 3) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, ih, pow_succ]
    have hz : ∑ x : Fin 3, ((g ^ m : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3)
        x.castSucc * ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) x.castSucc (Fin.last 3) =
        0 := Finset.sum_eq_zero fun x _ => by rw [h2 x, mul_zero]
    rw [hz, zero_add]

theorem entry_last_pow_five {g : GL (Fin 4) F16} (hg : g ∈ unitarySU 2 2 F16 4)
    (h2 : ∀ j : Fin 3,
      ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) j.castSucc (Fin.last 3) = 0) :
    (((g : GL (Fin 4) F16)) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3) (Fin.last 3) ^ 5 = 1 := by
  obtain ⟨-, hu⟩ := (mem_unitarySU_iff unitaryFieldData).mp hg
  have := congrFun (congrFun hu (Fin.last 3)) (Fin.last 3)
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at this
  simp only [Matrix.transpose_apply, Matrix.map_apply, h2, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.one_apply_eq] at this
  rw [unitaryFieldData.bar_apply] at this
  rw [← this]
  ring

theorem not_card_nine_of_singleton (d : Fin 4 → F16ˣ)
    (hs : ∀ j : Fin 3, d j.castSucc ≠ d (Fin.last 3))
    (R : Subgroup ↥(unitarySU 2 2 F16 4))
    (hR : ∀ g ∈ R, (g : GL (Fin 4) F16) * diagU d = diagU d * (g : GL (Fin 4) F16))
    (hcard : Nat.card R = 9) : False := by
  have hdvd : ∀ g ∈ R, g ∈ embSU3.range := by
    intro g hg
    have hcomm := hR g hg
    have h1 : ∀ j : Fin 3, ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3)
        j.castSucc = 0 := fun j => apply_eq_zero_of_commute_diagU hcomm (hs j).symm
    have h2 : ∀ j : Fin 3, ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) j.castSucc
        (Fin.last 3) = 0 := fun j => apply_eq_zero_of_commute_diagU hcomm (hs j)
    have hc5 := entry_last_pow_five g.2 h2
    have h9 : ((g : GL (Fin 4) F16)) ^ 9 = 1 := by
      have := pow_card_eq_one' (G := ↥R) (x := ⟨g, hg⟩)
      rw [hcard] at this
      have h' := congrArg (fun x : ↥R => ((x : ↥(unitarySU 2 2 F16 4)) : GL (Fin 4) F16)) this
      simpa using h'
    have hc9 : ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16) (Fin.last 3) (Fin.last 3) ^ 9 =
        1 := by
      rw [← pow_entry_last h2 9, h9]
      simp
    have hc1 := pow_gcd_eq_one.mpr ⟨hc5, hc9⟩
    have : Nat.gcd 5 9 = 1 := by norm_num
    rw [this, pow_one] at hc1
    exact exists_mem_range_embSU3 g h1 h2 hc1
  have h := Subgroup.card_dvd_of_le (show R ≤ embSU3.range from fun g hg => hdvd g hg)
  rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective embSU3_injective).toEquiv, card_su3] at h
  norm_num at h

theorem not_nine_dvd_card_centralizer {n : Fin 4 → ZMod 5} (hn : ∑ i, n i = 0)
    {i₀ : Fin 4} (hs : ∀ j, j ≠ i₀ → n j ≠ n i₀) :
    ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer
      ({(⟨ldg n, ldg_mem_unitarySU hn⟩ : ↥(unitarySU 2 2 F16 4))} :
        Set ↥(unitarySU 2 2 F16 4))) := by
  intro h9
  set y : ↥(unitarySU 2 2 F16 4) := ⟨ldg n, ldg_mem_unitarySU hn⟩ with hy
  set C := Subgroup.centralizer ({y} : Set ↥(unitarySU 2 2 F16 4)) with hC
  obtain ⟨R, hRcard, -, hRC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (n := 2) (H := ⊥) (L := C) (by simp) (by simpa using h9) bot_le
  set τ : Equiv.Perm (Fin 4) := Equiv.swap i₀ (Fin.last 3) with hτ
  set P : ↥(unitarySU 2 2 F16 4) := ⟨permGL τ, permGL_mem_unitarySU unitaryFieldData τ⟩ with hP
  refine not_card_nine_of_singleton (dv n ∘ τ.symm) ?_ (R.map (MulAut.conj P).toMonoidHom) ?_ ?_
  · intro j
    have h1 : τ.symm (Fin.last 3) = i₀ := by
      rw [hτ, Equiv.symm_swap, Equiv.swap_apply_right]
    have h2 : τ.symm j.castSucc ≠ i₀ := by
      rw [hτ, Equiv.symm_swap]
      intro h
      have h' := Equiv.swap_apply_self i₀ (Fin.last 3) j.castSucc
      rw [h, Equiv.swap_apply_left] at h'
      exact (Fin.castSucc_lt_last j).ne h'.symm
    simp only [Function.comp_apply, h1]
    intro h
    exact hs _ h2 (pw_injective h)
  · rintro _ ⟨g, hg, rfl⟩
    have hgC : (g : GL (Fin 4) F16) * ldg n = ldg n * (g : GL (Fin 4) F16) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hRC hg)
      exact congrArg Subtype.val this
    have hconj : diagU (dv n ∘ τ.symm) =
        (permGL τ : GL (Fin 4) F16) * ldg n * (permGL τ : GL (Fin 4) F16)⁻¹ :=
      (permGL_conj_diagU τ (dv n)).symm
    rw [hconj]
    show (P : GL (Fin 4) F16) * (g : GL (Fin 4) F16) * (P : GL (Fin 4) F16)⁻¹ *
        ((permGL τ : GL (Fin 4) F16) * ldg n * (permGL τ : GL (Fin 4) F16)⁻¹) =
      ((permGL τ : GL (Fin 4) F16) * ldg n * (permGL τ : GL (Fin 4) F16)⁻¹) *
        ((P : GL (Fin 4) F16) * (g : GL (Fin 4) F16) * (P : GL (Fin 4) F16)⁻¹)
    have hPe : (P : GL (Fin 4) F16) = permGL τ := rfl
    rw [hPe]
    calc permGL τ * (g : GL (Fin 4) F16) * (permGL τ : GL (Fin 4) F16)⁻¹ *
          ((permGL τ : GL (Fin 4) F16) * ldg n * (permGL τ : GL (Fin 4) F16)⁻¹)
        = permGL τ * ((g : GL (Fin 4) F16) * ldg n) * (permGL τ : GL (Fin 4) F16)⁻¹ := by group
      _ = permGL τ * (ldg n * (g : GL (Fin 4) F16)) * (permGL τ : GL (Fin 4) F16)⁻¹ := by rw [hgC]
      _ = _ := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj P).injective, hRcard]
    norm_num

theorem diag_mem_torus {g : GL (Fin 4) F16} (hg : g ∈ unitarySU 2 2 F16 4)
    (hd : ((g : GL (Fin 4) F16) : Matrix (Fin 4) (Fin 4) F16).IsDiag) : g ∈ torusSU 5 4 F16 := by
  obtain ⟨d, rfl⟩ := exists_diagU_of_isDiag hd
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff unitaryFieldData).mp hg
  refine mem_torusSU_iff.mpr ⟨d, fun i => ?_, ?_, rfl⟩
  · have h1 := congrFun (congrFun hu i) i
    rw [diagU_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      unitaryFieldData.bar_apply] at h1
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [← h1]
    ring
  · rw [det_diagU] at hdet
    apply Units.ext
    simpa [Units.coe_prod] using hdet

theorem mem_torus_of_commute {n m : Fin 4 → ZMod 5}
    (h : ∀ i j, i ≠ j → n i ≠ n j ∨ m i ≠ m j) {g : GL (Fin 4) F16}
    (hg : g ∈ unitarySU 2 2 F16 4) (hgn : g * ldg n = ldg n * g) (hgm : g * ldg m = ldg m * g) :
    g ∈ torusSU 5 4 F16 := by
  refine diag_mem_torus hg fun i j hij => ?_
  rcases h i j hij with hn | hm
  · exact apply_eq_zero_of_commute_diagU (d := dv n) hgn (fun e => hn (pw_injective e))
  · exact apply_eq_zero_of_commute_diagU (d := dv m) hgm (fun e => hm (pw_injective e))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data
