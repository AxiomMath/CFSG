module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3DataProof
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase2Finite
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase3Branches
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion ThreeTen)
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

section Parabolic

variable {p : ℕ} [Fact p.Prime]

theorem coprime_card_GL_two_of_coprime {m : ℕ} (hcop : Nat.Coprime m (p * ((p - 1) * (p + 1)))) :
    Nat.Coprime m (Nat.card (GL (Fin 2) (ZMod p))) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  refine (Nat.Coprime.pow_right 2 hcop).coprime_dvd_right ⟨p * (p + 1), ?_⟩
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : p ≤ p ^ 2 := by nlinarith
  zify [h1, h2, hp1]
  ring

theorem matrix_eq_one_of_col_zero {m : ℕ} (g : Matrix (Fin 3) (Fin 3) (ZMod p))
    (h10 : g 1 0 = 0) (h20 : g 2 0 = 0) (hdet : g.det = 1) (hm : g ^ m = 1)
    (hcop : Nat.Coprime m (p * ((p - 1) * (p + 1)))) : g = 1 := by
  have hpow : ∀ k : ℕ, (g ^ k) 1 0 = 0 ∧ (g ^ k) 2 0 = 0 ∧ (g ^ k) 0 0 = g 0 0 ^ k ∧
      (g ^ k).submatrix Fin.succ Fin.succ = (g.submatrix Fin.succ Fin.succ) ^ k := by
    intro k
    induction k with
    | zero => simp [Matrix.submatrix_one _ (Fin.succ_injective _)]
    | succ k ih =>
      obtain ⟨a1, a2, a0, ablk⟩ := ih
      rw [pow_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Matrix.mul_apply, Fin.sum_univ_three, a1, h10, h20]
      · simp [Matrix.mul_apply, Fin.sum_univ_three, a2, h10, h20]
      · simp [Matrix.mul_apply, Fin.sum_univ_three, a0, h10, h20, pow_succ]
      · rw [pow_succ, ← ablk]
        ext i j
        have hi : (g ^ k) i.succ 0 = 0 := by
          fin_cases i
          · exact a1
          · exact a2
        simp [Matrix.mul_apply, Fin.sum_univ_succ, hi]
  obtain ⟨-, -, hlm, hblkm⟩ := hpow m
  rw [hm] at hlm hblkm
  rw [Matrix.submatrix_one _ (Fin.succ_injective _)] at hblkm
  have hdet' : g.det = g 0 0 * (g.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_three]
    simp [h10, h20, Fin.succAbove_zero]
  have hcop1 : Nat.Coprime m (p - 1) :=
    hcop.coprime_dvd_right ((Dvd.intro _ rfl).trans (Dvd.intro_left _ rfl))
  have hcopp : Nat.Coprime m p := hcop.coprime_dvd_right (Dvd.intro _ rfl)
  have hcopGL := coprime_card_GL_two_of_coprime hcop
  have hl0 : g 0 0 ≠ 0 := by
    intro h0
    rw [hdet, h0, zero_mul] at hdet'
    exact one_ne_zero hdet'
  have hl : g 0 0 = 1 := by
    let u : (ZMod p)ˣ := Units.mk0 _ hl0
    have hu : u ^ m = 1 := by
      ext
      simpa [u] using hlm.symm
    have hdvd1 : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hu
    have hdvd2 : orderOf u ∣ p - 1 := by
      rw [← ZMod.card_units p]
      exact orderOf_dvd_card
    have hord : orderOf u = 1 := Nat.dvd_one.mp (hcop1 ▸ Nat.dvd_gcd hdvd1 hdvd2)
    have hu1 : u = 1 := orderOf_eq_one_iff.mp hord
    have := congrArg Units.val hu1
    simpa [u] using this
  have hblkdet : (g.submatrix Fin.succ Fin.succ).det = 1 := by
    rw [hdet, hl, one_mul] at hdet'
    exact hdet'.symm
  have hblk : g.submatrix Fin.succ Fin.succ = 1 := by
    let U : GL (Fin 2) (ZMod p) :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by rw [hblkdet]; exact one_ne_zero)
    have hUval : (U : Matrix (Fin 2) (Fin 2) (ZMod p)) = g.submatrix Fin.succ Fin.succ := rfl
    have hU : U ^ m = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hUval, ← hblkm, Units.val_one]
    have hdvd1 : orderOf U ∣ m := orderOf_dvd_of_pow_eq_one hU
    have hdvd2 : orderOf U ∣ Nat.card (GL (Fin 2) (ZMod p)) := orderOf_dvd_natCard U
    have hord : orderOf U = 1 := Nat.dvd_one.mp (hcopGL ▸ Nat.dvd_gcd hdvd1 hdvd2)
    have hU1 : U = 1 := orderOf_eq_one_iff.mp hord
    have h := congrArg Units.val hU1
    rwa [hUval, Units.val_one] at h
  have h11 : g 1 1 = 1 := by simpa using congrFun (congrFun hblk 0) 0
  have h12 : g 1 2 = 0 := by simpa using congrFun (congrFun hblk 0) 1
  have h21 : g 2 1 = 0 := by simpa using congrFun (congrFun hblk 1) 0
  have h22 : g 2 2 = 1 := by simpa using congrFun (congrFun hblk 1) 1
  set N : Matrix (Fin 3) (Fin 3) (ZMod p) := g - 1 with hNdef
  have hN0 : ∀ i, N i 0 = 0 := by
    intro i
    fin_cases i <;> simp [hNdef, hl, h10, h20]
  have hN1 : ∀ j, N 1 j = 0 := by
    intro j
    fin_cases j <;> simp [hNdef, h10, h11, h12]
  have hN2 : ∀ j, N 2 j = 0 := by
    intro j
    fin_cases j <;> simp [hNdef, h20, h21, h22]
  have hNN : N * N = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_three, hN0, hN1, hN2]
  have hgN : g = 1 + N := by rw [hNdef]; abel
  have hpowN : ∀ k : ℕ, g ^ k = 1 + (k : ZMod p) • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, hgN]
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hNN, smul_zero, add_zero]
      push_cast
      rw [add_smul, one_smul]
      abel
  have hgp : g ^ p = 1 := by
    rw [hpowN p, ZMod.natCast_self, zero_smul, add_zero]
  have hg1 : g ^ (Nat.gcd m p) = 1 := pow_gcd_eq_one.mpr ⟨hm, hgp⟩
  rwa [hcopp.gcd_eq_one, pow_one] at hg1

theorem matrix_eq_one_of_row_zero {m : ℕ} (g : Matrix (Fin 3) (Fin 3) (ZMod p))
    (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) (hdet : g.det = 1) (hm : g ^ m = 1)
    (hcop : Nat.Coprime m (p * ((p - 1) * (p + 1)))) : g = 1 := by
  let r : Fin 3 ≃ Fin 3 := Fin.revPerm
  let g' : Matrix (Fin 3) (Fin 3) (ZMod p) := gᵀ.submatrix r r
  have hpow' : ∀ k : ℕ, g' ^ k = (g ^ k)ᵀ.submatrix r r := by
    intro k
    induction k with
    | zero => simp [g', Matrix.submatrix_one _ r.injective]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ', Matrix.transpose_mul, ← Matrix.submatrix_mul_equiv _ _ _ r]
  have h1' : g' 1 0 = 0 := by simpa [g', r] using h21
  have h2' : g' 2 0 = 0 := by simpa [g', r] using h20
  have hdet' : g'.det = 1 := by
    simp only [g']
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose, hdet]
  have hm' : g' ^ m = 1 := by
    rw [hpow' m, hm, Matrix.transpose_one, Matrix.submatrix_one _ r.injective]
  have hg' := matrix_eq_one_of_col_zero g' h1' h2' hdet' hm' hcop
  ext i j
  have h := congrFun (congrFun hg' (r j)) (r i)
  simp only [g', Matrix.submatrix_apply, Matrix.transpose_apply] at h
  have hrr : ∀ x : Fin 3, r (r x) = x := fun x => Fin.rev_rev x
  rw [hrr, hrr] at h
  rw [h]
  simp only [Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have : r j ≠ r i := fun e => hij (r.injective e).symm
    simp [hij, this]

theorem col_zero_of_mem_flagStabilizer_one {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ flagStabilizer 3 K ({1} : Set ℕ)) :
    (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  have hst : g ∈ stabilizer (flagSpace 3 K 1) := mem_flagStabilizer.1 hg 1 rfl
  have hv : (Pi.single 0 (1 : K) : Fin 3 → K) ∈ flagSpace 3 K 1 := by
    rw [mem_flagSpace]
    intro j hj
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
    simp [hj0]
  have hmem : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 (1 : K)) ∈ flagSpace 3 K 1 := by
    have h1 := Submodule.mem_map_of_mem (f := mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) hv
    rwa [mem_stabilizer.1 hst] at h1
  have h := mem_flagSpace.1 hmem
  refine ⟨?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h 1 (by simp)
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h 2 (by simp)

theorem row_zero_of_mem_flagStabilizer_two {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ flagStabilizer 3 K ({2} : Set ℕ)) :
    (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  have hst : g ∈ stabilizer (flagSpace 3 K 2) := mem_flagStabilizer.1 hg 2 rfl
  have hv : ∀ c : Fin 3, (c : ℕ) < 2 → (Pi.single c (1 : K) : Fin 3 → K) ∈ flagSpace 3 K 2 := by
    intro c hc
    rw [mem_flagSpace]
    intro j hj
    have hjc : j ≠ c := fun h => by subst h; omega
    simp [hjc]
  have hmem : ∀ c : Fin 3, (c : ℕ) < 2 →
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single c (1 : K)) ∈ flagSpace 3 K 2 := by
    intro c hc
    have h1 := Submodule.mem_map_of_mem (f := mulVecLin (g : Matrix (Fin 3) (Fin 3) K))
      (hv c hc)
    rwa [mem_stabilizer.1 hst] at h1
  refine ⟨?_, ?_⟩
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using
      mem_flagSpace.1 (hmem 0 (by simp)) 2 (by simp)
  · simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using
      mem_flagSpace.1 (hmem 1 (by simp)) 2 (by simp)

theorem eq_one_of_mem_maxParabolic_of_pow_eq_one {m : ℕ}
    {g : SpecialLinearGroup (Fin 3) (ZMod p)}
    (hg : g ∈ flagStabilizer 3 (ZMod p) ({1} : Set ℕ) ∨
      g ∈ flagStabilizer 3 (ZMod p) ({2} : Set ℕ))
    (hm : g ^ m = 1) (hcop : Nat.Coprime m (p * ((p - 1) * (p + 1)))) : g = 1 := by
  have hm' : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ m = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hm, Matrix.SpecialLinearGroup.coe_one]
  have hg1 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
    rcases hg with hg | hg
    · obtain ⟨h1, h2⟩ := col_zero_of_mem_flagStabilizer_one hg
      exact matrix_eq_one_of_col_zero _ h1 h2 g.2 hm' hcop
    · obtain ⟨h1, h2⟩ := row_zero_of_mem_flagStabilizer_two hg
      exact matrix_eq_one_of_row_zero _ h1 h2 g.2 hm' hcop
  exact Subtype.ext (hg1.trans Matrix.SpecialLinearGroup.coe_one.symm)

end Parabolic

section SplitTorus

variable {p : ℕ} [Fact p.Prime]

private def torusVec (u : (ZMod p)ˣ) (k : Fin 3) : Fin 3 → ZMod p :=
  fun l => if l = k then ((u⁻¹ * u⁻¹ : (ZMod p)ˣ) : ZMod p) else (u : ZMod p)

private theorem det_diagonal_torusVec (u : (ZMod p)ˣ) (k : Fin 3) :
    (diagonal (torusVec u k)).det = 1 := by
  have key : ∀ a b c : (ZMod p)ˣ, a * b * c = 1 → (a : ZMod p) * b * c = 1 := by
    intro a b c h
    rw [← Units.val_mul, ← Units.val_mul, h, Units.val_one]
  rw [det_diagonal, Fin.prod_univ_three]
  fin_cases k
  · exact key (u⁻¹ * u⁻¹) u u (by group)
  · exact key u (u⁻¹ * u⁻¹) u (by group)
  · exact key u u (u⁻¹ * u⁻¹) (by group)

private def torusSL (u : (ZMod p)ˣ) (k : Fin 3) : SpecialLinearGroup (Fin 3) (ZMod p) :=
  ⟨diagonal (torusVec u k), det_diagonal_torusVec u k⟩

private theorem torusSL_coe (u : (ZMod p)ˣ) (k : Fin 3) :
    (torusSL u k : Matrix (Fin 3) (Fin 3) (ZMod p)) = diagonal (torusVec u k) := rfl

private theorem torusSL_pow {d : ℕ} {u : (ZMod p)ˣ} (hu : u ^ d = 1) (k : Fin 3) :
    torusSL u k ^ d = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, torusSL_coe, diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
  congr 1
  funext l
  simp only [Pi.pow_apply, torusVec]
  split_ifs
  · rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hu, inv_one, one_mul, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]

private theorem torusSL_ne_one {u : (ZMod p)ˣ} (hu : u ≠ 1) (k : Fin 3) : torusSL u k ≠ 1 := by
  intro h
  obtain ⟨l, hl⟩ : ∃ l : Fin 3, l ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
  have h' := congrArg
    (fun g : SpecialLinearGroup (Fin 3) (ZMod p) => (g : Matrix (Fin 3) (Fin 3) (ZMod p)) l l) h
  simp only [torusSL_coe, diagonal_apply_eq, torusVec, if_neg hl,
    Matrix.SpecialLinearGroup.coe_one, one_apply_eq] at h'
  exact hu (Units.ext h')

private theorem torusSL_commute (u : (ZMod p)ˣ) (k k' : Fin 3) :
    Commute (torusSL u k) (torusSL u k') := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, torusSL_coe, diagonal_mul_diagonal]
  congr 1
  funext l
  exact mul_comm _ _

private theorem transvection_commute_torusSL (u : (ZMod p)ˣ)
    (t : TransvectionStruct (Fin 3) (ZMod p)) (k : Fin 3) (hik : t.i ≠ k) (hjk : t.j ≠ k) :
    Commute t.toSpecialLinearGroup (torusSL u k) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, TransvectionStruct.toSpecialLinearGroup_coe,
    torusSL_coe, TransvectionStruct.toMatrix, transvection]
  ext a b
  simp only [add_mul, mul_add, Matrix.add_apply, mul_diagonal, diagonal_mul, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [torusVec, if_neg hik, if_neg hjk, one_apply_ne t.hij]
    ring
  · rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [one_apply_ne hab]

private theorem mem_normalizer_zpowers_of_commute {G : Type*} [Group G] {x y : G}
    (h : Commute x y) : x ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun n hn => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  exact ((h.symm.zpow_left k).eq)

theorem not_dvd_sub_one_of_threeTenHyp {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p)) : ¬ d ∣ p - 1 := by
  intro hdvd
  have hh := hhyp
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have : Fact p.Prime := ⟨hp⟩
  have : Fact d.Prime := ⟨hd⟩
  have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) d
    (by rw [ZMod.card_units]; exact hdvd)
  have hud : u ^ d = 1 := hu ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact hd.one_lt.ne hu
  let E₀ : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    Subgroup.closure (Set.range (torusSL u))
  have hpair : (Set.range (torusSL u)).Pairwise Commute := by
    rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩ -
    exact torusSL_commute u k k'
  have hexp : ∀ g ∈ E₀, g ^ d = 1 := by
    let : CommGroup E₀ := Subgroup.closureCommGroupOfComm hpair
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact torusSL_pow hud k
    | one => exact one_pow d
    | mul x y hx hy ihx ihy =>
      have hc : Commute x y := congrArg Subtype.val (mul_comm (⟨x, hx⟩ : E₀) ⟨y, hy⟩)
      rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hE₀ : IsPGroup d E₀ := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  let ι : SpecialLinearGroup (Fin 3) (ZMod p) →* H := I.subtype.comp e.symm.toMonoidHom
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow d H, (Q : Subgroup H) = D := by
    have hD' := hD
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at hD'
    obtain ⟨-, hpg, hidx⟩ := hD'
    exact ⟨hpg.toSylow hidx, IsPGroup.toSylow_coe hpg hidx⟩
  obtain ⟨h, hhD⟩ := CFSG.GroupTheory.exists_map_conj_le_sylow Q (hE₀.map ι)
  rw [hQ] at hhD
  let ψ : SpecialLinearGroup (Fin 3) (ZMod p) →* H := (MulAut.conj h).toMonoidHom.comp ι
  have hψ : ∀ x, ψ x = h * (e.symm x : H) * h⁻¹ := fun x => by
    simp [ψ, ι, MulAut.conj_apply]
  have hψD : ∀ k, ψ (torusSL u k) ∈ D := fun k =>
    hhD (Subgroup.mem_map_of_mem _
      (Subgroup.mem_map_of_mem ι (Subgroup.subset_closure ⟨k, rfl⟩)))
  have hψI : ∀ x, ψ x ∈ I := fun x => by
    rw [hψ]
    exact hInormal.conj_mem _ (e.symm x).2 h
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    rw [hψ, hψ, mul_left_inj, mul_right_inj] at hxy
    exact e.symm.injective (Subtype.ext hxy)
  have htv : ∀ t : TransvectionStruct (Fin 3) (ZMod p), ψ t.toSpecialLinearGroup ∈ Y := by
    intro t
    have hex : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide
    obtain ⟨k, hik, hjk⟩ := hex t.i t.j t.hij
    have hAD : Subgroup.zpowers (ψ (torusSL u k)) ≤ D := Subgroup.zpowers_le.mpr (hψD k)
    have hAne : Subgroup.zpowers (ψ (torusSL u k)) ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      intro h1
      exact torusSL_ne_one hu1 k (hψinj (h1.trans ψ.map_one.symm))
    refine normalizer_inter_le_Y_of_nontrivial_le hh hAD hAne ⟨?_, (le_sup_left : I ≤ I ⊔ D) (hψI _)⟩
    exact mem_normalizer_zpowers_of_commute
      ((transvection_commute_torusSL u t k hik hjk).map ψ)
  have hW : Y.comap ψ = ⊤ := by
    rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨t, rfl⟩; exact htv t)
  have hIY : I ≤ Y := by
    intro z hz
    have hz' : h⁻¹ * z * h ∈ I := by
      simpa using hInormal.conj_mem z hz h⁻¹
    have hmem : ψ (e ⟨h⁻¹ * z * h, hz'⟩) ∈ Y := by
      have : e ⟨h⁻¹ * z * h, hz'⟩ ∈ Y.comap ψ := hW ▸ Subgroup.mem_top _
      exact this
    rw [hψ, MulEquiv.symm_apply_apply] at hmem
    simpa [mul_assoc] using hmem
  exact not_le_of_gt hYlt (sup_le hIY (d_le_Y_of_threeTenHyp hh))

end SplitTorus

theorem not_dvd_sq_add_add_one_of_threeTenHyp {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p)) (h1 : ¬ d ∣ p - 1) :
    ¬ d ∣ p ^ 2 + p + 1 := by
  intro hdvd
  have hh := hhyp
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have : Fact p.Prime := ⟨hp⟩
  have : Fact d.Prime := ⟨hd⟩
  have hPI : P ≤ I := p_sylow_le_of_oPPrimeHull_eq hp hI hP
  have hInormal : I.Normal := normal_of_oPPrimeHull_eq hI
  have hDY : D ≤ Y := d_le_Y_of_threeTenHyp hh
  have h2 : ¬ d ∣ p + 1 := by
    intro h
    have heq : p ^ 2 + p + 1 = p * (p + 1) + 1 := by ring
    rw [heq] at hdvd
    exact hd.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (h.mul_left p)).mp hdvd))
  have hcop : Nat.Coprime d (p * ((p - 1) * (p + 1))) :=
    Nat.Coprime.mul_right ((Nat.coprime_primes hd hp).mpr hdp)
      (Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hd).mpr h1)
        ((Nat.Prime.coprime_iff_not_dvd hd).mpr h2))
  have hdvdI : d ∣ Nat.card ↥I :=
    dvd_card_of_threeTenHyp_of_isSLType_of_not_dvd_sub_one hh e h1
  have hEne : D ⊓ I ≠ ⊥ := inf_ne_bot_of_dvd_card hD hInormal hdvdI
  let W : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    ((Y ⊓ I).subgroupOf I).map e.toMonoidHom
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P I := hP.of_le hPI le_top
  obtain ⟨Q₀, hQ₀⟩ := hPsyl.exists_sylow_eq_subgroupOf
  let Q : Sylow p (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    Q₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQeq : (Q : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p))) =
      (P.subgroupOf I).map e.toMonoidHom := by
    change (Q₀ : Subgroup ↥I).map e.toMonoidHom = (P.subgroupOf I).map e.toMonoidHom
    rw [hQ₀]
  obtain ⟨g, hg⟩ := exists_conj_borel_eq_normalizer Q
  have hNle : Subgroup.normalizer (P.subgroupOf I : Set ↥I) ≤ (Y ⊓ I).subgroupOf I := by
    have h := Subgroup.subgroupOf_mono I
      (le_inf hN inf_le_right : Subgroup.normalizer (P : Set H) ⊓ I ≤ Y ⊓ I)
    rwa [Subgroup.inf_subgroupOf_right, Subgroup.subgroupOf_normalizer_eq hPI] at h
  have hNW : Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 3) (ZMod p))) ≤ W := by
    calc Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 3) (ZMod p)))
        = Subgroup.normalizer ((P.subgroupOf I).map e.toMonoidHom :
            Set (SpecialLinearGroup (Fin 3) (ZMod p))) :=
          congrArg (fun S : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) =>
            Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 3) (ZMod p)))) hQeq
      _ = (Subgroup.normalizer (P.subgroupOf I : Set ↥I)).map e.toMonoidHom :=
          (Subgroup.map_equiv_normalizer_eq _ e).symm
      _ ≤ W := Subgroup.map_mono hNle
  let W' : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) := W.map (MulAut.conj g⁻¹).toMonoidHom
  have hcancel : ((upperTriangular 3 (ZMod p)).map
      (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
      upperTriangular 3 (ZMod p) := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (SpecialLinearGroup (Fin 3) (ZMod p)) := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hBW' : upperTriangular 3 (ZMod p) ≤ W' := by
    rw [← hcancel]
    refine Subgroup.map_mono ?_
    calc (upperTriangular 3 (ZMod p)).map (MulAut.conj g).toMonoidHom
        = Subgroup.normalizer (Q : Set (SpecialLinearGroup (Fin 3) (ZMod p))) := hg.symm
      _ ≤ W := hNW
  let EI : Subgroup ↥I := (D ⊓ I).subgroupOf I
  let F : Subgroup (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    (EI.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
  have hFW' : F ≤ W' :=
    Subgroup.map_mono (Subgroup.map_mono
      (Subgroup.subgroupOf_mono I (le_inf (inf_le_left.trans hDY) inf_le_right)))
  have hEIne : EI ≠ ⊥ := by
    intro hbot
    apply hEne
    have h : ((D ⊓ I).subgroupOf I).map I.subtype = ⊥ := by
      change EI.map I.subtype = ⊥
      rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : D ⊓ I ≤ I)] at h
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hE'ne : EI.map e.toMonoidHom ≠ ⊥ := fun hbot' =>
      hEIne ((Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) EI e.injective).mp hbot')
    exact hE'ne ((Subgroup.map_eq_bot_iff_of_injective
      (f := (MulAut.conj g⁻¹).toMonoidHom) _ (MulAut.conj g⁻¹).injective).mp hbot)
  have hFpg : IsPGroup d F := by
    have hEpg : IsPGroup d ↥(D ⊓ I) := hD.isPGroup.to_le inf_le_left
    have hEIpg : IsPGroup d EI := hEpg.comap_subtype
    exact (hEIpg.map e.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨⟨y, hyF⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hFne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hFpg ⟨y, hyF⟩
  have hyk : y ^ d ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hcopk : Nat.Coprime (d ^ k) (p * ((p - 1) * (p + 1))) := Nat.Coprime.pow_left k hcop
  rcases borel_overgroups_sl3 W' hBW' with htop | hQ1 | hQ2 | hB
  ·
    have hIY : I ≤ Y := by
      intro z hz
      have hs : (MulAut.conj g⁻¹).toMonoidHom (e ⟨z, hz⟩) ∈ W' := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨w, hwW, hw⟩ := Subgroup.mem_map.mp hs
      have hwx : w = e ⟨z, hz⟩ := (MulAut.conj g⁻¹).injective hw
      obtain ⟨i', hi', hi'e⟩ := Subgroup.mem_map.mp (hwx ▸ hwW)
      have hi'z : i' = ⟨z, hz⟩ := e.injective hi'e
      rw [hi'z, Subgroup.mem_subgroupOf] at hi'
      exact hi'.1
    exact not_le_of_gt hYlt (sup_le hIY hDY)
  · exact hy1' (eq_one_of_mem_maxParabolic_of_pow_eq_one
      (Or.inl (hQ1 ▸ hFW' hyF)) hyk hcopk)
  · exact hy1' (eq_one_of_mem_maxParabolic_of_pow_eq_one
      (Or.inr (hQ2 ▸ hFW' hyF)) hyk hcopk)
  ·
    have hyB : y ∈ upperTriangular 3 (ZMod p) := hB ▸ hFW' hyF
    have h10 := mem_upperTriangular.1 hyB 1 0 (by decide)
    have h20 := mem_upperTriangular.1 hyB 2 0 (by decide)
    have hm' : (y : Matrix (Fin 3) (Fin 3) (ZMod p)) ^ d ^ k = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hyk, Matrix.SpecialLinearGroup.coe_one]
    exact hy1' (Subtype.ext ((matrix_eq_one_of_col_zero _ h10 h20 y.2 hm' hcopk).trans
      Matrix.SpecialLinearGroup.coe_one.symm))

theorem threeTenTorusExclusion_of_threeTenHyp {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p)) : ThreeTenTorusExclusion p d :=
  ⟨not_dvd_sub_one_of_threeTenHyp hhyp e,
    not_dvd_sq_add_add_one_of_threeTenHyp hhyp e (not_dvd_sub_one_of_threeTenHyp hhyp e)⟩

theorem threeTenSL3Data_of_threeTenHyp {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (hSL : IsSLType 3 (ZMod p) ↥I) : ThreeTenSL3Data I D Y p d := by
  obtain ⟨e⟩ := hSL
  have : Fact p.Prime := ⟨hhyp.1⟩
  exact threeTenSL3Data_of_torusExclusion hhyp e (threeTenTorusExclusion_of_threeTenHyp hhyp e)

theorem threeTen_holds : ThreeTen :=
  threeTen_of_cases
      (threeTenCase1_of_data threeTenSL2Vacuity_holds
          (fun _ _ _ _ _ _ _ _ _ hhyp hSL => threeTenSL3Data_of_threeTenHyp hhyp hSL))
      (threeTenCase2_of_finiteInput threeTenCase2FiniteInput)
      (threeTenCase3_of_finiteInput threeTenCase3FiniteInput_holds)
      (threeTenCase4_of_finiteInput (threeTenCase4FiniteInput_of_ext threeTenCase4ExtFiniteInput))

end CFSG.LocalAnalysis.AGL81I.Section3
