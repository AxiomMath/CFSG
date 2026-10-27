module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ExtStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Q8D8
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Shapes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem q8d8_inv_eq {x : K} (hx : x ^ 2 = 1) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two]
  exact hx

theorem q8d8_swap {x y t : K} (h : ⁅x, y⁆ = t) : x * y = t * (y * x) := by
  rw [← h, commutatorElement_def]
  group

theorem q8d8_comm_of_swap {x y t : K} (h : x * y = t * (y * x)) : ⁅x, y⁆ = t := by
  rw [commutatorElement_def, h]
  group

theorem q8d8_tt {t : K} (ht2 : t ^ 2 = 1) (w : K) : t * (t * w) = w := by
  rw [← mul_assoc, ← pow_two, ht2, one_mul]

theorem q8d8_swap_symm {x y t : K} (ht2 : t ^ 2 = 1) (h : x * y = t * (y * x)) :
    y * x = t * (x * y) := by
  rw [h, q8d8_tt ht2]

theorem q8d8_sq {x y t : K} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (h : ⁅x, y⁆ = t) :
    (x * y) ^ 2 = t := by
  rw [← h, commutatorElement_def, q8d8_inv_eq hx, q8d8_inv_eq hy, pow_two]
  simp only [mul_assoc]

theorem q8d8_comm_mul {x y z t : K} (ht2 : t ^ 2 = 1) (hty : y * t = t * y)
    (hxy : x * y = t * (y * x)) (hxz : x * z = t * (z * x)) :
    x * (y * z) = (y * z) * x := by
  calc x * (y * z) = (x * y) * z := by rw [mul_assoc]
    _ = t * (y * x) * z := by rw [hxy]
    _ = t * y * (x * z) := by simp only [mul_assoc]
    _ = t * y * (t * (z * x)) := by rw [hxz]
    _ = (t * y * t) * (z * x) := by simp only [mul_assoc]
    _ = y * (z * x) := by rw [mul_assoc t y t, hty, q8d8_tt ht2]
    _ = (y * z) * x := by rw [mul_assoc]

theorem q8d8_anti_prod {x y z t : K} (ht2 : t ^ 2 = 1) (hxt : x * t = t * x)
    (hyt : y * t = t * y) (hy2 : y ^ 2 = 1) (hxy : x * y = t * (y * x))
    (hyz : y * z = t * (z * y)) (hxz : x * z = t * (z * x)) :
    (x * y) * (y * z) = t * ((y * z) * (x * y)) := by
  have hyx : y * x = t * (x * y) := q8d8_swap_symm ht2 hxy
  have hzx : z * x = t * (x * z) := q8d8_swap_symm ht2 hxz
  have hy : y * y = 1 := by rw [← pow_two]; exact hy2
  have h1 : (x * y) * (y * z) = x * z := by
    rw [mul_assoc, ← mul_assoc y y z, hy, one_mul]
  have h3 : y * (x * z) = (x * z) * y := q8d8_comm_mul ht2 hxt hyx hyz
  have h4 : y * (x * z) * y = x * z := by
    rw [h3, mul_assoc, hy, mul_one]
  have h2 : (y * z) * (x * y) = t * (x * z) := by
    calc (y * z) * (x * y) = y * (z * x) * y := by simp only [mul_assoc]
      _ = y * (t * (x * z)) * y := by rw [hzx]
      _ = t * (y * (x * z) * y) := by
        rw [← mul_assoc y t, hyt]
        simp only [mul_assoc]
      _ = t * (x * z) := by rw [h4]
  rw [h1, h2, q8d8_tt ht2]

theorem q8d8_closure_comm {S T : Set K} (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x) :
    ∀ g ∈ Subgroup.closure S, ∀ h' ∈ Subgroup.closure T, g * h' = h' * g := by
  intro g hg h' hh'
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer (Subgroup.closure S : Set K) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g' hg'
    have h2 : Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set K) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (h x hx y hy).symm
    have h3 := h2 hg'
    rw [Subgroup.mem_centralizer_iff] at h3
    exact (h3 y rfl).symm
  have h3 := h1 hh'
  rw [Subgroup.mem_centralizer_iff] at h3
  exact h3 g hg

theorem q8d8_assemble {R A B : Subgroup K} {t : K} (hR : IsExt2 R t)
    (hcard : Nat.card R = 32) (hQ : Nonempty (A ≃* QuaternionGroup 2))
    (hD : Nonempty (B ≃* DihedralGroup 4)) (hA8 : Nat.card A = 8) (hB8 : Nat.card B = 8)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (htA : t ∈ A) (htB : t ∈ B)
    (hAcen : ∀ g ∈ A, (∀ h ∈ A, g * h = h * g) → g ∈ zpowers t)
    (hAR : A ≤ R) (hBR : B ≤ R) : smallRankIsQ8D8 R := by
  have hinf : A ⊓ B = zpowers t := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_inf] at hg
      exact hAcen g hg.1 (fun h hh => (hAB h hh g hg.2).symm)
    · rw [Subgroup.zpowers_le, Subgroup.mem_inf]
      exact ⟨htA, htB⟩
  have hcardinf : Nat.card ↥(A ⊓ B) = 2 := by
    rw [hinf, Nat.card_zpowers]
    exact orderOf_eq_prime hR.t_sq hR.t_ne
  have hcsup : Nat.card ↥(A ⊔ B) = 32 := by
    have h := shape5_card_sup_mul_inf hAB
    rw [hcardinf, hA8, hB8] at h
    omega
  have hsup : A ⊔ B = R :=
    Subgroup.eq_of_le_of_card_ge (sup_le hAR hBR) (by rw [hcard, hcsup])
  unfold smallRankIsQ8D8
  exact ⟨A, B, hQ, hD, hAB, hsup, hcardinf⟩

theorem q8d8_of_five_involutions {R : Subgroup K} {t : K} (hR : IsExt2 R t)
    (hcard : Nat.card R = 32) (s : Fin 5 → K) (hs : ∀ i, s i ∈ R ∧ s i ^ 2 = 1)
    (hcomm : ∀ i j, i ≠ j → ⁅s i, s j⁆ = t) : smallRankIsQ8D8 R := by
  have hsR : ∀ i, s i ∈ R := fun i => (hs i).1
  have hs2 : ∀ i, s i ^ 2 = 1 := fun i => (hs i).2
  have ht2 : t ^ 2 = 1 := hR.t_sq
  have ht1 : t ≠ 1 := hR.t_ne
  have hct : ∀ i, s i * t = t * s i := fun i => hR.t_comm _ (hsR i)
  have hsw : ∀ i j, i ≠ j → s i * s j = t * (s j * s i) :=
    fun i j hij => q8d8_swap (hcomm i j hij)
  have ha2 : (s 0 * s 1) ^ 2 = t := q8d8_sq (hs2 0) (hs2 1) (hcomm 0 1 (by decide))
  have hb2 : (s 1 * s 2) ^ 2 = t := q8d8_sq (hs2 1) (hs2 2) (hcomm 1 2 (by decide))
  have hab : ⁅s 0 * s 1, s 1 * s 2⁆ = t :=
    q8d8_comm_of_swap (q8d8_anti_prod ht2 (hct 0) (hct 1) (hs2 1) (hsw 0 1 (by decide))
      (hsw 1 2 (by decide)) (hsw 0 2 (by decide)))
  obtain ⟨hAQ, hAcard, hAcen⟩ := exists_Q8_subgroup ha2 hb2 hab ht2 ht1
  obtain ⟨hBD, hBcard⟩ := exists_D8_subgroup (hs2 3) (hs2 4) (hcomm 3 4 (by decide)) ht2 ht1
  have hcm : ∀ i j k, i ≠ j → i ≠ k → s i * (s j * s k) = (s j * s k) * s i :=
    fun i j k hij hik => q8d8_comm_mul ht2 (hct j) (hsw i j hij) (hsw i k hik)
  have hgen : ∀ x ∈ ({s 0 * s 1, s 1 * s 2} : Set K), ∀ y ∈ ({s 3, s 4} : Set K),
      x * y = y * x := by
    intro x hx y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hcm 3 0 1 (by decide) (by decide)).symm
    · exact (hcm 4 0 1 (by decide) (by decide)).symm
    · exact (hcm 3 1 2 (by decide) (by decide)).symm
    · exact (hcm 4 1 2 (by decide) (by decide)).symm
  have hAB := q8d8_closure_comm hgen
  have hmemA : ∀ x ∈ ({s 0 * s 1, s 1 * s 2} : Set K),
      x ∈ Subgroup.closure ({s 0 * s 1, s 1 * s 2} : Set K) := fun x hx =>
    Subgroup.subset_closure hx
  have hmemB : ∀ x ∈ ({s 3, s 4} : Set K), x ∈ Subgroup.closure ({s 3, s 4} : Set K) :=
    fun x hx => Subgroup.subset_closure hx
  have htA : t ∈ Subgroup.closure ({s 0 * s 1, s 1 * s 2} : Set K) := by
    rw [← ha2]
    exact Subgroup.pow_mem _ (hmemA _ (Set.mem_insert _ _)) 2
  have htB : t ∈ Subgroup.closure ({s 3, s 4} : Set K) := by
    have h3 : s 3 ∈ Subgroup.closure ({s 3, s 4} : Set K) := hmemB _ (Set.mem_insert _ _)
    have h4 : s 4 ∈ Subgroup.closure ({s 3, s 4} : Set K) :=
      hmemB _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [← hcomm 3 4 (by decide), commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h3 h4)
      (Subgroup.inv_mem _ h3)) (Subgroup.inv_mem _ h4)
  have hAR : Subgroup.closure ({s 0 * s 1, s 1 * s 2} : Set K) ≤ R := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact R.mul_mem (hsR 0) (hsR 1)
    · exact R.mul_mem (hsR 1) (hsR 2)
  have hBR : Subgroup.closure ({s 3, s 4} : Set K) ≤ R := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hsR 3
    · exact hsR 4
  exact q8d8_assemble hR hcard hAQ hBD hAcard hBcard hAB htA htB hAcen hAR hBR
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem fiveInv_zpowers_cases {t x : K} (ht2 : t ^ 2 = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hn : n = 2 * (n / 2) + n % 2 := (Int.mul_ediv_add_emod n 2).symm
  have h2 : t ^ (2 : ℤ) = 1 := by simpa using ht2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [hn, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hn, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem fiveInv_mul_self {t x : K} (ht2 : t ^ 2 = 1) (hx : x ∈ zpowers t) : x * x = 1 := by
  rcases fiveInv_zpowers_cases ht2 hx with rfl | rfl
  · simp
  · simpa [pow_two] using ht2

theorem fiveInv_inv_eq {t x : K} (ht2 : t ^ 2 = 1) (hx : x ∈ zpowers t) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (fiveInv_mul_self ht2 hx)

theorem fiveInv_commute_of_mem {R : Subgroup K} {t x r : K} (hR : IsExt2 R t) (hx : x ∈ zpowers t)
    (hr : r ∈ R) : r * x = x * r := by
  rcases fiveInv_zpowers_cases hR.t_sq hx with rfl | rfl
  · simp
  · exact hR.t_comm r hr

theorem fiveInv_conj_zpowers {t z x : K} (ht2 : t ^ 2 = 1) (hzt : z * t = t * z)
    (hx : x ∈ zpowers t) : z * x * z⁻¹ = x := by
  rcases fiveInv_zpowers_cases ht2 hx with rfl | rfl
  · simp
  · rw [hzt, mul_inv_cancel_right]

theorem fiveInv_comm_swap (a b : K) : a * b = ⁅a, b⁆ * (b * a) := by
  simp only [commutatorElement_def]; group

theorem fiveInv_comm_mul_right {R : Subgroup K} {t a b c : K} (hR : IsExt2 R t) (ha : a ∈ R)
    (hb : b ∈ R) (hc : c ∈ R) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h : b * ⁅a, c⁆ = ⁅a, c⁆ * b := fiveInv_commute_of_mem hR (hR.comm_mem a ha c hc) hb
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by simp only [mul_assoc]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by rw [h]; simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem fiveInv_comm_symm {R : Subgroup K} {t a b : K} (hR : IsExt2 R t) (ha : a ∈ R) (hb : b ∈ R) :
    ⁅b, a⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, fiveInv_inv_eq hR.t_sq (hR.comm_mem a ha b hb)]

theorem fiveInv_sq_mul {R : Subgroup K} {t Q s : K} (hR : IsExt2 R t) (hQ : Q ∈ R) (hs : s ∈ R)
    (hs2 : s ^ 2 = 1) : (Q * s) ^ 2 = Q ^ 2 * ⁅s, Q⁆ := by
  have hu : Q * ⁅s, Q⁆ = ⁅s, Q⁆ * Q := fiveInv_commute_of_mem hR (hR.comm_mem s hs Q hQ) hQ
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have hsw : s * Q = ⁅s, Q⁆ * (Q * s) := fiveInv_comm_swap s Q
  calc (Q * s) ^ 2 = Q * (s * Q) * s := by rw [pow_two]; simp only [mul_assoc]
    _ = Q * (⁅s, Q⁆ * (Q * s)) * s := by rw [hsw]
    _ = (Q * ⁅s, Q⁆) * Q * (s * s) := by group
    _ = ⁅s, Q⁆ * Q * Q := by rw [hss, hu]; group
    _ = Q ^ 2 * ⁅s, Q⁆ := by rw [pow_two, mul_assoc Q Q, hu, ← mul_assoc, hu]

theorem fiveInv_sq_five {R : Subgroup K} {t x0 x1 x2 x3 x4 : K} (hR : IsExt2 R t)
    (h0 : x0 ∈ R) (h1 : x1 ∈ R) (h2 : x2 ∈ R) (h3 : x3 ∈ R) (h4 : x4 ∈ R)
    (s0 : x0 ^ 2 = 1) (s1 : x1 ^ 2 = 1) (s2 : x2 ^ 2 = 1) (s3 : x3 ^ 2 = 1) (s4 : x4 ^ 2 = 1) :
    (x0 * x1 * x2 * x3 * x4) ^ 2 =
      ⁅x1, x0⁆ * (⁅x2, x0⁆ * ⁅x2, x1⁆) * (⁅x3, x0⁆ * ⁅x3, x1⁆ * ⁅x3, x2⁆) *
        (⁅x4, x0⁆ * ⁅x4, x1⁆ * ⁅x4, x2⁆ * ⁅x4, x3⁆) := by
  have h01 : x0 * x1 ∈ R := R.mul_mem h0 h1
  have h012 : x0 * x1 * x2 ∈ R := R.mul_mem h01 h2
  have h0123 : x0 * x1 * x2 * x3 ∈ R := R.mul_mem h012 h3
  rw [fiveInv_sq_mul hR h0123 h4 s4, fiveInv_sq_mul hR h012 h3 s3, fiveInv_sq_mul hR h01 h2 s2,
    fiveInv_sq_mul hR h0 h1 s1, s0, one_mul,
    fiveInv_comm_mul_right hR h4 h012 h3, fiveInv_comm_mul_right hR h4 h01 h2,
    fiveInv_comm_mul_right hR h4 h0 h1, fiveInv_comm_mul_right hR h3 h01 h2,
    fiveInv_comm_mul_right hR h3 h0 h1, fiveInv_comm_mul_right hR h2 h0 h1]

theorem fiveInv_shift {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hzt : z * t = t * z)
    {a : ℕ → K} (haR : ∀ n, a n ∈ R) (hsucc : ∀ n, a (n + 1) = z * a n * z⁻¹) (n m : ℕ) :
    ⁅a (n + 1), a (m + 1)⁆ = ⁅a n, a m⁆ := by
  rw [hsucc n, hsucc m, ← conjugate_commutatorElement]
  exact fiveInv_conj_zpowers hR.t_sq hzt (hR.comm_mem _ (haR n) _ (haR m))

theorem fiveInv_table {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hzt : z * t = t * z)
    {a : ℕ → K} (haR : ∀ n, a n ∈ R) (ha2 : ∀ n, a n ^ 2 = 1)
    (hsucc : ∀ n, a (n + 1) = z * a n * z⁻¹) (hper : ∀ n, a (n + 5) = a n) :
    ∃ b1 b2 : K, b1 ∈ zpowers t ∧ b2 ∈ zpowers t ∧
      (∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → ⁅a i, a j⁆ = b1 ∨ ⁅a i, a j⁆ = b2) ∧
      (a 0 * a 1 * a 2 * a 3 * a 4) ^ 2 =
        b1 * (b2 * b1) * (b2 * b2 * b1) * (b1 * b2 * b2 * b1) := by
  have hsh : ∀ n m, ⁅a (n + 1), a (m + 1)⁆ = ⁅a n, a m⁆ := fiveInv_shift hR hzt haR hsucc
  have hsy : ∀ n m, ⁅a m, a n⁆ = ⁅a n, a m⁆ := fun n m => fiveInv_comm_symm hR (haR n) (haR m)
  have a5 : a 5 = a 0 := hper 0
  have a6 : a 6 = a 1 := hper 1
  have p01 : ⁅a 0, a 1⁆ = ⁅a 0, a 1⁆ := rfl
  have p12 : ⁅a 1, a 2⁆ = ⁅a 0, a 1⁆ := hsh 0 1
  have p23 : ⁅a 2, a 3⁆ = ⁅a 0, a 1⁆ := (hsh 1 2).trans p12
  have p34 : ⁅a 3, a 4⁆ = ⁅a 0, a 1⁆ := (hsh 2 3).trans p23
  have p04 : ⁅a 0, a 4⁆ = ⁅a 0, a 1⁆ :=
    calc ⁅a 0, a 4⁆ = ⁅a 4, a 0⁆ := (hsy 0 4).symm
      _ = ⁅a 4, a 5⁆ := by rw [a5]
      _ = ⁅a 3, a 4⁆ := hsh 3 4
      _ = ⁅a 0, a 1⁆ := p34
  have p02 : ⁅a 0, a 2⁆ = ⁅a 0, a 2⁆ := rfl
  have p13 : ⁅a 1, a 3⁆ = ⁅a 0, a 2⁆ := hsh 0 2
  have p24 : ⁅a 2, a 4⁆ = ⁅a 0, a 2⁆ := (hsh 1 3).trans p13
  have p03 : ⁅a 0, a 3⁆ = ⁅a 0, a 2⁆ :=
    calc ⁅a 0, a 3⁆ = ⁅a 3, a 0⁆ := (hsy 0 3).symm
      _ = ⁅a 3, a 5⁆ := by rw [a5]
      _ = ⁅a 2, a 4⁆ := hsh 2 4
      _ = ⁅a 0, a 2⁆ := p24
  have p14 : ⁅a 1, a 4⁆ = ⁅a 0, a 2⁆ :=
    calc ⁅a 1, a 4⁆ = ⁅a 4, a 1⁆ := (hsy 1 4).symm
      _ = ⁅a 4, a 6⁆ := by rw [a6]
      _ = ⁅a 3, a 5⁆ := hsh 3 5
      _ = ⁅a 3, a 0⁆ := by rw [a5]
      _ = ⁅a 0, a 3⁆ := hsy 0 3
      _ = ⁅a 0, a 2⁆ := p03
  have e10 : ⁅a 1, a 0⁆ = ⁅a 0, a 1⁆ := hsy 0 1
  have e20 : ⁅a 2, a 0⁆ = ⁅a 0, a 2⁆ := hsy 0 2
  have e21 : ⁅a 2, a 1⁆ = ⁅a 0, a 1⁆ := (hsy 1 2).trans p12
  have e30 : ⁅a 3, a 0⁆ = ⁅a 0, a 2⁆ := (hsy 0 3).trans p03
  have e31 : ⁅a 3, a 1⁆ = ⁅a 0, a 2⁆ := (hsy 1 3).trans p13
  have e32 : ⁅a 3, a 2⁆ = ⁅a 0, a 1⁆ := (hsy 2 3).trans p23
  have e40 : ⁅a 4, a 0⁆ = ⁅a 0, a 1⁆ := (hsy 0 4).trans p04
  have e41 : ⁅a 4, a 1⁆ = ⁅a 0, a 2⁆ := (hsy 1 4).trans p14
  have e42 : ⁅a 4, a 2⁆ = ⁅a 0, a 2⁆ := (hsy 2 4).trans p24
  have e43 : ⁅a 4, a 3⁆ = ⁅a 0, a 1⁆ := (hsy 3 4).trans p34
  refine ⟨⁅a 0, a 1⁆, ⁅a 0, a 2⁆, hR.comm_mem _ (haR 0) _ (haR 1),
    hR.comm_mem _ (haR 0) _ (haR 2), ?_, ?_⟩
  · intro i j hi hj hij
    interval_cases i <;> interval_cases j <;>
      first
        | exact absurd rfl hij
        | exact Or.inl (by assumption)
        | exact Or.inr (by assumption)
  · rw [fiveInv_sq_five hR (haR 0) (haR 1) (haR 2) (haR 3) (haR 4) (ha2 0) (ha2 1) (ha2 2) (ha2 3)
      (ha2 4), e10, e20, e21, e30, e31, e32, e40, e41, e42, e43]

theorem fiveInv_fixed_of_conj {R : Subgroup K} {t z P u : K} (hR : IsExt2 R t) (hz : z ^ 5 = 1)
    (hzt : z * t = t * z) (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t) (hPR : P ∈ R)
    (hu : u ∈ zpowers t) (h : z * P * z⁻¹ = u * P) : P ∈ zpowers t := by
  rcases fiveInv_zpowers_cases hR.t_sq hu with h1 | h1
  · rw [h1, one_mul] at h
    exact hfix P hPR (by rw [← mul_inv_eq_iff_eq_mul]; exact h)
  · exfalso
    rw [h1] at h
    have hzt' : ∀ n : ℕ, z * t ^ n * z⁻¹ = t ^ n := fun n => by
      rw [(Commute.pow_right (show Commute z t from hzt) n).eq, mul_inv_cancel_right]
    have hind : ∀ n : ℕ, z ^ n * P * (z ^ n)⁻¹ = t ^ n * P := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc z ^ (n + 1) * P * (z ^ (n + 1))⁻¹ = z * (z ^ n * P * (z ^ n)⁻¹) * z⁻¹ := by group
          _ = z * (t ^ n * P) * z⁻¹ := by rw [ih]
          _ = (z * t ^ n * z⁻¹) * (z * P * z⁻¹) := by group
          _ = t ^ (n + 1) * P := by rw [hzt', h, pow_succ, mul_assoc]
    have h5 := hind 5
    have ht5 : t ^ 5 = t := by
      rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hR.t_sq]
      simp
    rw [hz, ht5] at h5
    have : t = 1 := by simpa using h5.symm
    exact hR.t_ne this

theorem fiveInv_prod_mem {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 5 = 1)
    (hzt : z * t = t * z) (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    {a : ℕ → K} (haR : ∀ n, a n ∈ R) (ha2 : ∀ n, a n ^ 2 = 1)
    (hsucc : ∀ n, a (n + 1) = z * a n * z⁻¹) (hper : ∀ n, a (n + 5) = a n) :
    a 0 * a 1 * a 2 * a 3 * a 4 ∈ zpowers t := by
  have hPR : a 0 * a 1 * a 2 * a 3 * a 4 ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (haR 0) (haR 1)) (haR 2)) (haR 3)) (haR 4)
  have hss : a 0 * a 0 = 1 := by rw [← pow_two]; exact ha2 0
  have hinv : (a 0)⁻¹ = a 0 := inv_eq_of_mul_eq_one_right hss
  have e0 : z * a 0 * z⁻¹ = a 1 := (hsucc 0).symm
  have e1 : z * a 1 * z⁻¹ = a 2 := (hsucc 1).symm
  have e2 : z * a 2 * z⁻¹ = a 3 := (hsucc 2).symm
  have e3 : z * a 3 * z⁻¹ = a 4 := (hsucc 3).symm
  have e4 : z * a 4 * z⁻¹ = a 0 := (hsucc 4).symm.trans (hper 0)
  have hconj : z * (a 0 * a 1 * a 2 * a 3 * a 4) * z⁻¹ =
      ⁅a 0, a 0 * a 1 * a 2 * a 3 * a 4⁆ * (a 0 * a 1 * a 2 * a 3 * a 4) := by
    calc z * (a 0 * a 1 * a 2 * a 3 * a 4) * z⁻¹
        = (z * a 0 * z⁻¹) * (z * a 1 * z⁻¹) * (z * a 2 * z⁻¹) * (z * a 3 * z⁻¹) *
          (z * a 4 * z⁻¹) := by group
      _ = a 1 * a 2 * a 3 * a 4 * a 0 := by rw [e0, e1, e2, e3, e4]
      _ = (a 0 * a 0) * a 1 * a 2 * a 3 * a 4 * a 0 := by rw [hss, one_mul]
      _ = a 0 * (a 0 * a 1 * a 2 * a 3 * a 4) * a 0 := by simp only [mul_assoc]
      _ = _ := by rw [commutatorElement_def, inv_mul_cancel_right, hinv]
  exact fiveInv_fixed_of_conj hR hz hzt hfix hPR (hR.comm_mem _ (haR 0) _ hPR) hconj

theorem fiveInv_eq_of_prod {t b1 b2 : K} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hb1 : b1 ∈ zpowers t)
    (hb2 : b2 ∈ zpowers t)
    (h : b1 * (b2 * b1) * (b2 * b2 * b1) * (b1 * b2 * b2 * b1) = 1) : b1 = b2 := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have htt' : ∀ x : K, t * (t * x) = x := fun x => by rw [← mul_assoc, htt, one_mul]
  rcases fiveInv_zpowers_cases ht2 hb1 with h1 | h1 <;>
    rcases fiveInv_zpowers_cases ht2 hb2 with h2 | h2
  · rw [h1, h2]
  · exfalso
    rw [h1, h2] at h
    apply ht1
    simpa [mul_assoc, htt, htt'] using h
  · exfalso
    rw [h1, h2] at h
    apply ht1
    simpa [mul_assoc, htt, htt'] using h
  · rw [h1, h2]

theorem fiveInv_conj_closure {S : Set K} {g : K}
    (hg : ∀ x ∈ S, g * x * g⁻¹ ∈ Subgroup.closure S) {x : K} (hx : x ∈ Subgroup.closure S) :
    g * x * g⁻¹ ∈ Subgroup.closure S := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hg x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ih

theorem fiveInv_not_abelian {R : Subgroup K} {t z : K}
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    {a : ℕ → K} (haR : ∀ n, a n ∈ R) (ha0 : a 0 ∉ zpowers t)
    (hsucc : ∀ n, a (n + 1) = z * a n * z⁻¹) (hper : ∀ n, a (n + 5) = a n)
    (hcomm5 : ∀ i j : ℕ, i < 5 → j < 5 → a i * a j = a j * a i) : False := by
  have hmod : ∀ n, a n = a (n % 5) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < 5
      · rw [Nat.mod_eq_of_lt hn]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
        rw [hper m, ih m (by omega), Nat.add_mod_right]
  have hcomm : ∀ n m, a n * a m = a m * a n := by
    intro n m
    rw [hmod n, hmod m]
    exact hcomm5 _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  have hAR : Subgroup.closure (Set.range a) ≤ R := by
    rw [Subgroup.closure_le]
    rintro _ ⟨n, rfl⟩
    exact haR n
  have hAc : ∀ x ∈ Subgroup.closure (Set.range a), ∀ y ∈ Subgroup.closure (Set.range a),
      x * y = y * x := by
    haveI : IsMulCommutative (Subgroup.closure (Set.range a)) :=
      Subgroup.isMulCommutative_closure (k := Set.range a)
        (by rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ _; exact hcomm n m)
    intro x hx y hy
    exact setLike_mul_comm hx hy
  have h4 : ∀ n, z⁻¹ * a n * z⁻¹⁻¹ = a (n + 4) := by
    intro n
    have h := hsucc (n + 4)
    have h' : a (n + 4 + 1) = a n := hper n
    rw [h'] at h
    rw [h]
    group
  have hznorm : z ∈ normalizer ((Subgroup.closure (Set.range a) : Subgroup K) : Set K) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact fiveInv_conj_closure (fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        rw [← hsucc n]
        exact Subgroup.subset_closure ⟨n + 1, rfl⟩) hx
    · intro hx
      have h2 := fiveInv_conj_closure (g := z⁻¹) (S := Set.range a) (fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        rw [h4 n]
        exact Subgroup.subset_closure ⟨n + 4, rfl⟩) hx
      have e : z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ = x := by group
      rw [e] at h2
      exact h2
  have h0 := hstar _ hAR hAc hznorm (a 0) (Subgroup.subset_closure ⟨0, rfl⟩)
  exact ha0 (hfix _ (haR 0) h0)

theorem fiveInv_main {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 5 = 1)
    (hzt : z * t = t * z) (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    {a : ℕ → K} (haR : ∀ n, a n ∈ R) (ha2 : ∀ n, a n ^ 2 = 1) (ha0 : a 0 ∉ zpowers t)
    (hsucc : ∀ n, a (n + 1) = z * a n * z⁻¹) (hper : ∀ n, a (n + 5) = a n) :
    ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → ⁅a i, a j⁆ = t := by
  obtain ⟨b1, b2, hb1, hb2, htab, hsq⟩ := fiveInv_table hR hzt haR ha2 hsucc hper
  have hP := fiveInv_prod_mem hR hz hzt hfix haR ha2 hsucc hper
  have hP2 : (a 0 * a 1 * a 2 * a 3 * a 4) ^ 2 = 1 := by
    rcases fiveInv_zpowers_cases hR.t_sq hP with h | h
    · rw [h, one_pow]
    · rw [h, hR.t_sq]
  rw [hsq] at hP2
  have hb : b1 = b2 := fiveInv_eq_of_prod hR.t_sq hR.t_ne hb1 hb2 hP2
  have hb1t : b1 = t := by
    rcases fiveInv_zpowers_cases hR.t_sq hb1 with h | h
    · exfalso
      refine fiveInv_not_abelian hfix hstar haR ha0 hsucc hper ?_
      intro i j hi hj
      by_cases hij : i = j
      · rw [hij]
      · rcases htab i j hi hj hij with h' | h'
        · exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [h', h])
        · exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [h', ← hb, h])
    · exact h
  intro i j hi hj hij
  rcases htab i j hi hj hij with h | h
  · rw [h, hb1t]
  · rw [h, ← hb, hb1t]

theorem five_involutions {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hcard : Nat.card R = 32)
    (hz : z ^ 5 = 1) (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z) :
    ∃ s : Fin 5 → K, (∀ i, s i ∈ R ∧ s i ^ 2 = 1) ∧ ∀ i j, i ≠ j → ⁅s i, s j⁆ = t := by
  obtain ⟨s₀, hs₀R, hs₀2, hs₀t⟩ := hR.exists_noncentral_involution (k := 2)
    (by rw [hcard]; norm_num) (le_refl 2)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → K, ∀ n, a n = z ^ n * s₀ * (z ^ n)⁻¹ := ⟨_, fun _ => rfl⟩
  have haR : ∀ n, a n ∈ R := fun n => by
    rw [ha n]
    exact (Subgroup.mem_set_normalizer_iff.mp (pow_mem hzR n) s₀).mp hs₀R
  have ha2 : ∀ n, a n ^ 2 = 1 := fun n => by
    rw [ha n, conj_pow, hs₀2]
    simp
  have ha0 : a 0 ∉ zpowers t := by
    rw [ha 0]
    simpa using hs₀t
  have hsucc : ∀ n, a (n + 1) = z * a n * z⁻¹ := fun n => by
    rw [ha, ha]
    group
  have hper : ∀ n, a (n + 5) = a n := fun n => by
    rw [ha, ha, pow_add, hz, mul_one]
  have hmain := fiveInv_main hR hz hzt hfix hstar haR ha2 ha0 hsucc hper
  refine ⟨fun i => a i, fun i => ⟨haR i, ha2 i⟩, ?_⟩
  intro i j hij
  exact hmain i j i.2 j.2 (fun h => hij (Fin.ext h))
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem shape_five {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hcard : Nat.card R = 32)
    (hz : z ^ 5 = 1) (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z) : smallRankIsQ8D8 R := by
  obtain ⟨s, hs, hcomm⟩ := five_involutions hR hcard hz hzR hzt hfix hstar
  exact q8d8_of_five_involutions hR hcard s hs hcomm
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
