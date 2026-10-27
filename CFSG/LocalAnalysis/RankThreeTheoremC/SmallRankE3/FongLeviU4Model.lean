module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviGeneric
public import CFSG.Quasithin.H13.U4ParTorus
public import CFSG.Quasithin.H13.U4ParYAmalgam
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630NineB
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

variable {m : ℕ} {K : Type} [Field K]

theorem rho2_eq_one_of_mem_radQ2 (h : UnitaryFieldData 2 m K) {g : hypSU h 2 0}
    (hg : g ∈ radQ2 h) : rho2 h g = 1 := by
  obtain ⟨a1, a2, a3, a4, -⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, a1, a2, a3, a4]

noncomputable def detRho2 (h : UnitaryFieldData 2 m K) : ↥(parP2 h) →* Kˣ where
  toFun g := ⟨(rho2 h (g : hypSU h 2 0)).det, (rho2 h ((g : hypSU h 2 0)⁻¹)).det, by
    have h1 := congrArg Matrix.det (rho2_mul h (g := (g : hypSU h 2 0))
      ((parP2 h).inv_mem g.2))
    rwa [mul_inv_cancel, rho2_one, det_one, det_mul, eq_comm] at h1, by
    have h1 := congrArg Matrix.det (rho2_mul h (g := (g : hypSU h 2 0)⁻¹) g.2)
    rwa [inv_mul_cancel, rho2_one, det_one, det_mul, eq_comm] at h1⟩
  map_one' := by
    apply Units.ext
    simp [rho2_one]
  map_mul' g g' := by
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [rho2_mul h g'.2, det_mul]

theorem mem_ker_detRho2 (h : UnitaryFieldData 2 m K) (g : ↥(parP2 h)) :
    g ∈ (detRho2 h).ker ↔ (g : hypSU h 2 0) ∈ parH2 h := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    exact ⟨g.2, by simpa [detRho2] using congrArg Units.val hg⟩
  · intro hg
    apply Units.ext
    simpa [detRho2] using hg.2

theorem relIndex_parH2_dvd (h : UnitaryFieldData 2 m K) :
    (parH2 h).relIndex (parP2 h) ∣ Nat.card K - 1 := by
  have hker : (parH2 h).subgroupOf (parP2 h) = (detRho2 h).ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_ker_detRho2]
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, ← Nat.card_units]
  exact Subgroup.card_subgroup_dvd_card _

theorem lv_u4_hypFlag_one_isotropic (h : UnitaryFieldData 2 m K) :
    ∀ x ∈ hypFlag h 2 0 1, ∀ y ∈ hypFlag h 2 0 1, hypForm h 2 0 x y = 0 := by
  rw [hypFlag_eq_posFlag h (by norm_num) (by norm_num : (1 : ℕ) ≤ 2 * 2 + 0)]
  exact UnitaryHigher.posFlag_isotropic h (by norm_num)

theorem lv_u4_finrank_hypFlag_one (h : UnitaryFieldData 2 m K) :
    Module.finrank K (hypFlag h 2 0 1) = 1 := by
  rw [hypFlag_eq_posFlag h (by norm_num) (by norm_num : (1 : ℕ) ≤ 2 * 2 + 0)]
  exact UnitaryHigher.finrank_posFlag (by norm_num)

theorem lv_u4_index_parP (h : UnitaryFieldData 2 m K) :
    (UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 1)).index =
      ((2 ^ m) ^ 2 + 1) * ((2 ^ m) ^ 3 + 1) := by
  have hm : m ≠ 0 := by have := h.one_le; omega
  have hq : 2 ≤ 2 ^ m := Nat.le_self_pow hm 2
  obtain ⟨-, hidx, -, -, hline, -, -⟩ :=
    UnitaryHigher.isotropic_stabilizer_index h (hypFlag h 2 0 1) (lv_u4_hypFlag_one_isotropic h)
  rw [lv_u4_finrank_hypFlag_one h] at hidx
  have hq2 : (2 : ℚ) ≤ ((2 ^ m : ℕ) : ℚ) := by exact_mod_cast hq
  have hIq : ((UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 1)).index : ℚ) =
      (((2 ^ m : ℕ) : ℚ) ^ 2 + 1) * (((2 ^ m : ℕ) : ℚ) ^ 3 + 1) := by
    rw [hidx, hline (2 * 2 + 0)]
    generalize ((2 ^ m : ℕ) : ℚ) = q at hq2 ⊢
    have hpos : (0 : ℚ) < q ^ 2 - 1 := by nlinarith
    rw [div_eq_iff hpos.ne', show (2 * 2 + 0 : ℕ) = 4 from rfl, show (4 - 1 : ℕ) = 3 from rfl]
    ring
  exact_mod_cast hIq

theorem lv_u4_card_core (q P I S : ℕ) (hq : 2 ≤ q) (hPI : P * I = S)
    (hI : I = (q ^ 2 + 1) * (q ^ 3 + 1))
    (hS : (S : ℤ) = (q : ℤ) ^ 6 * (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 4 - 1))) :
    P = q ^ 6 * (q ^ 2 - 1) ^ 2 := by
  subst hI
  subst hPI
  push_cast at hS
  have hX : ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 3 + 1) ≠ 0 := by positivity
  have key : ((P : ℤ) - (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) ^ 2) *
      (((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 3 + 1)) = 0 := by
    linear_combination hS
  have hP : (P : ℤ) = (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) ^ 2 := by
    have := (mul_eq_zero.mp key).resolve_right hX
    linarith
  have hle : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
  zify [hle]
  exact hP

theorem card_parP (h : UnitaryFieldData 2 m K) :
    Nat.card (parP h) = (2 ^ m) ^ 6 * ((2 ^ m) ^ 2 - 1) ^ 2 := by
  have hm : m ≠ 0 := by have := h.one_le; omega
  have hq : 2 ≤ 2 ^ m := Nat.le_self_pow hm 2
  have hPI := Subgroup.card_mul_index (H := UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 1))
  have hS := (card_hypSU h (r := 2) (ε := 0) (by norm_num)).1
  rw [show (2 * 2 + 0) * (2 * 2 + 0 - 1) / 2 = 6 by norm_num] at hS
  have hprod : ∏ i ∈ Finset.Icc 2 (2 * 2 + 0), (((2 ^ m : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((2 ^ m : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ m : ℕ) : ℤ) ^ 3 + 1) * (((2 ^ m : ℕ) : ℤ) ^ 4 - 1) := by
    rw [show Finset.Icc 2 (2 * 2 + 0) = {2, 3, 4} by rfl, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hS
  exact lv_u4_card_core (2 ^ m) _ _ _ hq hPI (lv_u4_index_parP h) hS

theorem lv_prod_ix (g : Ix → K) : ∏ a, g a = g ie1 * g ie2 * g if1 * g if2 := by
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul, mul_one, ie1, ie2, if1, if2]
  ring

theorem lv_diag_gram (h : UnitaryFieldData 2 m K) (d : Ix → K)
    (hpart : ∀ i, h.bar (d i) * d (hypPartner i) = 1) :
    ((diagonal d).map h.bar)ᵀ * hypGram 2 0 K * diagonal d = hypGram 2 0 K := by
  have hT : ((diagonal d).map h.bar)ᵀ = diagonal (fun i => h.bar (d i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [diagonal_apply, hij, Ne.symm hij]
  rw [hT]
  ext i j
  rw [mul_diagonal, diagonal_mul, hypGram_apply]
  split_ifs with hj
  · subst hj
    simpa using hpart i
  · simp

theorem lv_coe_pow_diag (h : UnitaryFieldData 2 m K) (g : hypSU h 2 0) (d : Ix → K)
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = diagonal d) (n : ℕ) :
    (((g ^ n : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = diagonal (fun i => d i ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, hg, diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_succ]

theorem lv_exists_diag_mem (h : UnitaryFieldData 2 m K) (d : Ix → K) (hd0 : ∀ i, d i ≠ 0)
    (hpart : ∀ i, h.bar (d i) * d (hypPartner i) = 1) (hdet : ∏ i, d i = 1) :
    ∃ g : hypSU h 2 0, ((g : GL Ix K) : Matrix Ix Ix K) = diagonal d := by
  have hinv : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd0 i)
  have hinv' : diagonal (fun i => (d i)⁻¹) * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd0 i)
  refine ⟨⟨⟨diagonal d, diagonal (fun i => (d i)⁻¹), hinv, hinv'⟩, ?_⟩, rfl⟩
  exact mem_gramSU.mpr ⟨lv_diag_gram h d hpart, det_diagonal.trans hdet⟩

theorem lv_exists_fixed_root (h : UnitaryFieldData 2 m K) {p : ℕ} [Fact p.Prime]
    (hdvd : p ∣ 2 ^ m - 1) :
    ∃ l : K, h.bar l = l ∧ l ≠ 0 ∧ l ^ p = 1 ∧ l ≠ 1 := by
  have := h.finite
  have hdvdU : p ∣ Nat.card (h.fixedField)ˣ := by
    rw [Nat.card_units, h.card_fixedField]
    exact hdvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (h.fixedField)ˣ) p hdvdU
  have hup : u ^ p = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact (Fact.out (p := p.Prime)).one_lt.ne hu
  have hl : ((u : h.fixedField) : K) ^ p = 1 := by
    have h2 := congrArg (fun z : (h.fixedField)ˣ => ((z : h.fixedField) : K)) hup
    simpa [Units.val_pow_eq_pow_val] using h2
  refine ⟨((u : h.fixedField) : K), h.mem_fixedField.mp (u : h.fixedField).2, ?_, hl, ?_⟩
  · rintro h0
    rw [h0, zero_pow (Fact.out (p := p.Prime)).ne_zero] at hl
    exact zero_ne_one hl
  · intro h1
    apply hu1
    exact Units.ext (Subtype.ext h1)

theorem hypSU_two_le_pRank_of_dvd_sub (h : UnitaryFieldData 2 m K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ m - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (hypSU h 2 0)) := by
  obtain ⟨l, hlbar, hl0, hlp, hl1⟩ := lv_exists_fixed_root h hdvd
  obtain ⟨x, hx⟩ := lv_exists_diag_mem h
    (fun i : Ix => if i = ie1 then l else if i = ie2 then 1 else if i = if1 then l⁻¹ else 1⁻¹)
    (by intro i; rcases ix_cases i with rfl | rfl | rfl | rfl <;> simp [hl0])
    (by intro i; rcases ix_cases i with rfl | rfl | rfl | rfl <;> simp [hlbar, hl0, map_inv₀])
    (by rw [lv_prod_ix]; simp [hl0])
  obtain ⟨y, hy⟩ := lv_exists_diag_mem h
    (fun i : Ix => if i = ie1 then 1 else if i = ie2 then l else if i = if1 then 1⁻¹ else l⁻¹)
    (by intro i; rcases ix_cases i with rfl | rfl | rfl | rfl <;> simp [hl0])
    (by intro i; rcases ix_cases i with rfl | rfl | rfl | rfl <;> simp [hlbar, hl0, map_inv₀])
    (by rw [lv_prod_ix]; simp [hl0])
  have hxpow : x ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [lv_coe_pow_diag h x _ hx p, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    rcases ix_cases i with rfl | rfl | rfl | rfl <;> simp [hlp]
  have hypow : y ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [lv_coe_pow_diag h y _ hy p, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    rcases ix_cases i with rfl | rfl | rfl | rfl <;> simp [hlp]
  have hx1 : x ≠ 1 := by
    intro hx1
    subst hx1
    have e := congrFun (congrFun hx ie1) ie1
    simp at e
    apply hl1
    simpa using e.symm
  have hy1 : y ≠ 1 := by
    intro hy1
    subst hy1
    have e := congrFun (congrFun hy ie2) ie2
    simp at e
    apply hl1
    simpa using e.symm
  have hcomm : Commute x y := by
    show x * y = y * x
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hx, hy, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hyz : y ∉ Subgroup.zpowers x := by
    intro hmem
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y x).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    have hA : (((x ^ n : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
        ((y : GL Ix K) : Matrix Ix Ix K) := by
      rw [hn]
    rw [lv_coe_pow_diag h x _ hx n, hy] at hA
    have e := congrFun (congrFun hA ie2) ie2
    simp at e
    apply hl1
    simpa using e.symm
  exact CFSG.GroupTheory.two_le_pRank_of_commute (H := ⊤) (Subgroup.mem_top x)
    (Subgroup.mem_top y) (orderOf_eq_prime hxpow hx1) (orderOf_eq_prime hypow hy1) hcomm hyz

theorem lv_sq_sub_one (x : ℕ) : x ^ 2 - 1 = (x + 1) * (x - 1) := by
  rw [← sq_tsub_sq x 1, one_pow]

theorem lv_dvd_sq_sub_one {p m : ℕ} (hdvd : p ∣ 2 ^ m + 1) : p ∣ (2 ^ m) ^ 2 - 1 := by
  rw [lv_sq_sub_one]
  exact Dvd.dvd.mul_right hdvd _

theorem lv_coe_torElt_pow (h : UnitaryFieldData 2 m K) {α : K} (hα : h.bar α * α = 1) (n : ℕ) :
    (((torElt h hα ^ n : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = torMat (α ^ n) := by
  induction n with
  | zero => simp [torMat_one]
  | succ n ih =>
    rw [pow_succ (torElt h hα), coe_mul_hypSU, ih, coe_torElt, torMat_mul, pow_succ α n]

theorem lv_levMat_comm_torMat (B : Matrix (Fin 2) (Fin 2) K) (α : K) :
    levMat B * torMat α = torMat α * levMat B := by
  ext i j
  rw [mul_apply, sum_ix, mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [levMat_apply, torMat, torDiag, diagonal_apply] <;> ring

theorem lv_levHom_ie1 (h : UnitaryFieldData 2 m K)
    (B : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    (((levHom h B : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 := by
  rw [coe_levHom, levMat_apply]
  simp

theorem lv_torElt_ie1 (h : UnitaryFieldData 2 m K) {α : K} (hα : h.bar α * α = 1) :
    (((torElt h hα : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = α := by
  rw [coe_torElt]
  simp [torMat, torDiag]

theorem hypSU_two_le_pRank_of_dvd_add (h : UnitaryFieldData 2 m K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ m + 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (hypSU h 2 0)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have := h.finite
  haveI : Finite h.fixedField := inferInstance
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    classical
    haveI := Fintype.ofFinite h.fixedField
    infer_instance
  have hdvdU : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, show 2 ^ (2 * m) = (2 ^ m) ^ 2 by rw [← pow_mul, mul_comm]]
    exact lv_dvd_sq_sub_one hdvd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvdU
  have hpK : (a : K) ^ p = 1 := by
    have h1 : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have hbar : h.bar (a : K) * (a : K) = 1 := by
    have h1 : a ^ (2 ^ m + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact hdvd)
    have h2 := congrArg Units.val h1
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    exact h2
  have ha1 : (a : K) ≠ 1 := by
    intro h1
    have h2 : a = 1 := Units.ext (by rw [Units.val_one]; exact h1)
    rw [h2, orderOf_one] at ha
    omega
  obtain ⟨α, hα1, hαbar, hαp⟩ : ∃ α : K, α ≠ 1 ∧ h.bar α * α = 1 ∧ α ^ p = 1 :=
    ⟨(a : K), ha1, hbar, hpK⟩
  have hdvdSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h.card_fixedField]
    exact Dvd.dvd.mul_left (lv_dvd_sq_sub_one hdvd) _
  obtain ⟨A, hA⟩ :=
    exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) h.fixedField) p hdvdSL
  have hlinj : Function.Injective (levHom h) := by
    intro B₁ B₂ hB
    have h12 := congrArg (rho h) hB
    rw [rho_levHom, rho_levHom] at h12
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hij : ((B₁ : Matrix (Fin 2) (Fin 2) h.fixedField) i j : K) =
        ((B₂ : Matrix (Fin 2) (Fin 2) h.fixedField) i j : K) :=
      congrFun (congrFun h12 i) j
    exact Subtype.ext hij
  have hu : orderOf (levHom h A) = p := (orderOf_injective (levHom h) hlinj A).trans hA
  have htp : torElt h hαbar ^ p = 1 := by
    apply CFSG.Quasithin.H13.U4Par.hypSU_ext h
    rw [lv_coe_torElt_pow h hαbar, hαp, torMat_one, Subgroup.coe_one, Units.val_one]
  have htne : torElt h hαbar ≠ 1 := by
    intro ht
    apply hα1
    have h1 : (((torElt h hαbar : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 =
        (((1 : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 := by rw [ht]
    rw [lv_torElt_ie1] at h1
    simpa using h1
  have htord : orderOf (torElt h hαbar) = p := orderOf_eq_prime htp htne
  have hcomm : Commute (levHom h A) (torElt h hαbar) := by
    show levHom h A * torElt h hαbar = torElt h hαbar * levHom h A
    apply CFSG.Quasithin.H13.U4Par.hypSU_ext h
    rw [coe_mul_hypSU, coe_mul_hypSU, coe_levHom, coe_torElt]
    exact lv_levMat_comm_torMat _ _
  have hnot : torElt h hαbar ∉ Subgroup.zpowers (levHom h A) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hk
    have h1 : (((levHom h (A ^ k) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 =
        (((torElt h hαbar : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 := by rw [hk]
    rw [lv_levHom_ie1, lv_torElt_ie1] at h1
    exact hα1 h1.symm
  exact CFSG.GroupTheory.two_le_pRank_of_commute (H := ⊤) (Subgroup.mem_top _)
    (Subgroup.mem_top _) hu htord hcomm hnot

theorem hypSU_parP2_levi (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpr : ¬ p ∣ Nat.card K - 1) {z : hypSU h 2 0} (hz : orderOf z = p)
    (hzP : z ∈ parP2 h) :
    LeviSec p (parP2 h) z ∧ LeviHom (parP2 h) (Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  haveI := h.finite
  haveI := h.charP
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYle : leviY (parP2 h) ≤ parH2 h := perfectCore_parP2_le_parH2 h
  have hYge : parH2 h ≤ leviY (parP2 h) :=
    (parH2_le_radQ2_sup h).trans
      (sup_le (radQ2_le_perfectCore_parP2 h hm) (lev2Hom_range_le_perfectCore h))
  have hY : leviY (parP2 h) = parH2 h := le_antisymm hYle hYge
  have hW : leviW (parP2 h) = radQ2 h := by
    refine le_antisymm (pCoreOf_perfectCore_parP2_le_radQ2 h) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (radQ2_le_perfectCore_parP2 h hm)
      ((CFSG.Quasithin.perfectCore_le (parP2 h)).trans (parP2_le_normalizer_radQ2 h))
      (radQ2_isPGroup h)
  have hrelq : ¬ p ∣ (leviY (parP2 h)).relIndex (parP2 h) := by
    rw [hY]
    exact fun hd => hpr (hd.trans (relIndex_parH2_dvd h))
  have hzY : z ∈ leviY (parP2 h) :=
    mem_of_orderOf_prime_of_coprime_relIndex (leviY_le _)
      (CFSG.Quasithin.perfectCore_normal (parP2 h)) hp hrelq hzP hz
  set Y := leviY (parP2 h) with hYdef
  have hYle' : Y ≤ parH2 h := hY.le
  let φ : ↥Y →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (rho2F h).comp (Subgroup.inclusion hYle')
  have hφ1 : ∀ y : ↥Y, φ y = 1 ↔ rho2 h (y : hypSU h 2 0) = 1 := by
    intro y
    constructor
    · intro hy
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K)) hy
      exact this
    · intro hy
      apply Subtype.ext
      exact hy
  have hφs : Function.Surjective φ := by
    intro A
    exact ⟨⟨lev2Hom h A, lev2Hom_range_le_perfectCore h ⟨A, rfl⟩⟩, rho2F_lev2Hom h A⟩
  have hker : ∀ y : ↥Y, (y : hypSU h 2 0) ∈ leviW (parP2 h) ↔ φ y = 1 := by
    intro y
    rw [hW, hφ1]
    constructor
    · exact rho2_eq_one_of_mem_radQ2 h
    · exact mem_radQ2_of_rho2 h (parH2_le_parP2 h (hYle' y.2))
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    isSimpleGroup_sl2_of_charTwo (F := K) (four_le_card h)
  have hnc : ¬ ∀ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b = b * a := fun hc => by
    obtain ⟨A, B, hAB⟩ := exists_sl2_ne_comm (F := K)
    exact hAB (hc A B)
  have hsec : S622IsSimpleSection Y (leviW (parP2 h)) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.isSimpleSection_of_surjective hnc φ hφs
      (leviW_le_leviY _) hker
  have hhom : LeviHom (parP2 h) (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine ⟨φ, hφs, ?_⟩
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
  have hW2 : IsPGroup 2 (leviW (parP2 h)) := hW ▸ radQ2_isPGroup h
  have hpW : ¬ p ∣ Nat.card (leviW (parP2 h)) := by
    obtain ⟨n, hn⟩ := hW2.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hpY : p ∣ Nat.card Y := by
    have h1 : orderOf (⟨z, hzY⟩ : ↥Y) ∣ Nat.card Y := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hz] at h1
  have hcardY : (leviW (parP2 h)).relIndex Y * Nat.card (leviW (parP2 h)) = Nat.card Y := by
    have h1 := Subgroup.relIndex_mul_card (H := leviW (parP2 h)) (K := Y)
    rwa [inf_of_le_left (leviW_le_leviY _)] at h1
  have hprel : p ∣ (leviW (parP2 h)).relIndex Y := by
    rw [← hcardY] at hpY
    rcases (Nat.Prime.dvd_mul hp).1 hpY with h1 | h1
    · exact h1
    · exact absurd h1 hpW
  exact ⟨⟨hzY, hsec, hprel, hpW⟩, hhom⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
