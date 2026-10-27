module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SBasic
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Bender

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

open Subgroup CFSG CFSG.GH74.Uniqueness.Bender CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

theorem not_sq_dvd_of_squarefree {r : ℕ} (hr : r.Prime) (hr2 : Odd r) {n m : ℕ} (k : ℕ)
    (hn : n = 2 ^ k * m) (hm : Squarefree m) : ¬ r ^ 2 ∣ n := by
  intro h
  rw [hn] at h
  have hcop : Nat.Coprime (r ^ 2) (2 ^ k) := by
    apply Nat.Coprime.pow
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (fun h2 => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2
        subst this
        exact absurd hr2 (by decide))))
  have h2 : r ^ 2 ∣ m := hcop.dvd_of_dvd_mul_left h
  have := hm r (by rw [← sq]; exact h2)
  exact hr.one_lt.ne' (Nat.isUnit_iff.mp this)

theorem squarefree_255 : Squarefree 255 := by
  rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
  norm_num

theorem squarefree_1365 : Squarefree 1365 := by
  rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
  norm_num

theorem noN2_of_benderL216 {Y : Type} [Group Y] [Finite Y]
    (hB : BenderType Y 4 1 1) : NoN2 Y := by
  have hc := hB.center_eq_bot
  have hY : Nat.card Y = 4080 := by rw [hB.card_eq]; norm_num
  have hO : Nat.card (Outer Y) = 4 := hB.outer_linear.2
  have hA : Nat.card (MulAut Y) = 16320 := by rw [card_mulAut_eq_outer_mul hc, hY, hO]
  intro r V Z h
  have hsq := n2_sq_dvd h
  rw [hA] at hsq
  exact not_sq_dvd_of_squarefree h.1 h.2.1 6 (by norm_num) squarefree_255 hsq

theorem noN2_of_benderSz8 {Y : Type} [Group Y] [Finite Y]
    (hB : BenderType Y 3 2 1) : NoN2 Y := by
  have hc := hB.center_eq_bot
  have hY : Nat.card Y = 29120 := by rw [hB.card_eq]; norm_num
  have hO : Nat.card (Outer Y) ∣ 3 := hB.outer_suzuki.2.1
  have hA : Nat.card (MulAut Y) ∣ 87360 := by
    rw [card_mulAut_eq_outer_mul hc, hY]
    exact Nat.mul_dvd_mul_right hO 29120
  intro r V Z h
  have hsq := n2_sq_dvd h
  exact not_sq_dvd_of_squarefree h.1 h.2.1 6 (by norm_num) squarefree_1365 (hsq.trans hA)

theorem exists_conj_of_prime_index {Y : Type} [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime]
    {A B : Subgroup Y} (hA : IsPGroup p A) (hB : IsPGroup p B) (hAi : ¬ p ∣ A.index)
    (hBi : ¬ p ∣ B.index) : ∃ c : Y, ∀ x, x ∈ B ↔ c⁻¹ * x * c ∈ A := by
  classical
  let AS : Sylow p Y := hA.toSylow hAi
  let BS : Sylow p Y := hB.toSylow hBi
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq Y AS BS
  refine ⟨n, fun x => ?_⟩
  have h1 : ((n • AS : Sylow p Y) : Set Y) = ((BS : Sylow p Y) : Set Y) := by rw [hn]
  rw [Sylow.coe_smul] at h1
  have hBS : ((BS : Sylow p Y) : Set Y) = (B : Set Y) := rfl
  have hAS : ((AS : Sylow p Y) : Set Y) = (A : Set Y) := rfl
  rw [hBS, hAS] at h1
  have hx : x ∈ (B : Set Y) ↔ x ∈ MulAut.conj n • (A : Set Y) := by rw [h1]
  rw [SetLike.mem_coe] at hx
  rw [hx, Set.mem_smul_set_iff_inv_smul_mem]
  simp [mul_assoc]

theorem benderL28_no_commute {Y : Type} [Group Y] [Finite Y]
    (hB : BenderType Y 3 1 1) {g h : Y} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) (hh : h ^ 7 = 1)
    (hh1 : h ≠ 1) (hgh : g * h = h * g) : False := by
  classical
  obtain ⟨t, hcore⟩ := hB.exists_benderCore (default : Sylow 2 Y)
  have hP : IsPGroup 2 ((default : Sylow 2 Y) : Subgroup Y) := (default : Sylow 2 Y).isPGroup'
  set D : Subgroup Y := cartan ((default : Sylow 2 Y) : Subgroup Y) t with hD
  have hDcard : Nat.card D = 7 := by rw [hD, hcore.card_cartan]; norm_num
  have hYcard : Nat.card Y = 504 := by rw [hB.card_eq]; norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hDp : IsPGroup 7 D := IsPGroup.of_card (n := 1) (by rw [hDcard]; norm_num)
  have hDi : D.index = 72 := by
    have := Subgroup.card_mul_index D
    rw [hDcard, hYcard] at this
    omega
  have hord : orderOf h = 7 := orderOf_eq_prime hh hh1
  have hHcard : Nat.card (zpowers h) = 7 := by rw [Nat.card_zpowers, hord]
  have hHp : IsPGroup 7 (zpowers h) := IsPGroup.of_card (n := 1) (by rw [hHcard]; norm_num)
  have hHi : (zpowers h).index = 72 := by
    have := Subgroup.card_mul_index (zpowers h)
    rw [hHcard, hYcard] at this
    omega
  obtain ⟨c, hc⟩ := exists_conj_of_prime_index 7 hDp hHp (by rw [hDi]; norm_num)
    (by rw [hHi]; norm_num)
  have hh'D : c⁻¹ * h * c ∈ D := (hc h).mp (Subgroup.mem_zpowers h)
  have hh'1 : c⁻¹ * h * c ≠ 1 := by
    intro h1
    apply hh1
    have : h = c * (c⁻¹ * h * c) * c⁻¹ := by group
    rw [this, h1]; group
  have hcent := hcore.centralizer_cartan_eq hP hh'D hh'1
  have hcent' : centralizer ({c⁻¹ * h * c} : Set Y) = D := hcent
  have hg'D : c⁻¹ * g * c ∈ D := by
    rw [← hcent', Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * c * (c⁻¹ * h * c) = c⁻¹ * (g * h) * c := by group
      _ = c⁻¹ * (h * g) * c := by rw [hgh]
      _ = c⁻¹ * h * c * (c⁻¹ * g * c) := by group
  have h7 : (c⁻¹ * g * c) ^ 7 = 1 := by
    have := pow_card_eq_one' (G := D) (x := (⟨c⁻¹ * g * c, hg'D⟩ : D))
    rw [hDcard] at this
    simpa using congrArg Subtype.val this
  have h3 : (c⁻¹ * g * c) ^ 3 = 1 := by
    have := conj_pow (a := c⁻¹) (b := g) (i := 3)
    simp only [inv_inv] at this
    rw [this, hg]; group
  have h1 : c⁻¹ * g * c = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h7, h3⟩
    simpa using this
  apply hg1
  have : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
  rw [this, h1]; group

theorem noN2_of_benderL28 {Y : Type} [Group Y] [Finite Y]
    (hB : BenderType Y 3 1 1) : NoN2 Y := by
  classical
  have hc := hB.center_eq_bot
  have hinj := conj_injective_of_center_bot hc
  have hY : Nat.card Y = 504 := by rw [hB.card_eq]; norm_num
  have hO : Nat.card (Outer Y) = 3 := hB.outer_linear.2
  have hA : Nat.card (MulAut Y) = 1512 := by rw [card_mulAut_eq_outer_mul hc, hY, hO]
  intro r V Z h
  have hsq := n2_sq_dvd h
  rw [hA] at hsq
  obtain ⟨s, y, hs, hsodd, hsr, hys, hy1, -, hVy⟩ := n2_exists_prime_elt h
  obtain ⟨hr, hr2, hVe, hVc, -⟩ := h
  have : Fact s.Prime := ⟨hs⟩
  have hr3 : r = 3 := by
    have h1 : r ∣ 2 ^ 3 * 3 ^ 3 * 7 := by
      have : r ∣ r ^ 2 := dvd_pow_self r two_ne_zero
      exact this.trans hsq
    rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h3)
        subst this
        exact absurd hr2 (by decide)
      · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h3)
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h2
      subst this
      omega
  subst hr3
  have hs7 : s = 7 := by
    have hord : orderOf y = s := orderOf_eq_prime hys hy1
    have hdvd : s ∣ 1512 := by
      rw [← hA, ← hord]
      exact orderOf_dvd_natCard y
    have h1 : s ∣ 2 ^ 3 * 3 ^ 3 * 7 := hdvd
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hs).mp h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h3)
        subst this
        exact absurd hsodd (by decide)
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h3)) hsr
    · exact (Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h2
  subst hs7
  obtain ⟨v, hvV, hv1, hvin⟩ := exists_inner_ne_one V hVc (by rw [hO]; norm_num)
  have hv3 : v ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian v hvV
  have hyin : y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y := mem_inner_of_pow_eq_one hys (by rw [hO]; norm_num)
  obtain ⟨g, rfl⟩ : ∃ g : Y, MulAut.conj g = v := hvin
  obtain ⟨k, rfl⟩ : ∃ k : Y, MulAut.conj k = y := hyin
  have hcomm := hVy _ hvV
  refine benderL28_no_commute hB (g := g) (h := k) ?_ ?_ ?_ ?_ ?_
  · apply hinj; rw [map_pow, hv3, map_one]
  · rintro rfl; exact hv1 (map_one _)
  · apply hinj; rw [map_pow, hys, map_one]
  · rintro rfl; exact hy1 (map_one _)
  · apply hinj; rw [map_mul, map_mul, hcomm]

end CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem noN2_L28 (Y : Type) [Group Y] (h : LieModel Y .PSL 2 2 3) :
    NoN2 Y := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (S := Y) (f := 3) (by norm_num) h
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact CF67S.noN2_of_benderL28 (.linear 3 (by norm_num) e)

theorem noN2_L216 (Y : Type) [Group Y] (h : LieModel Y .PSL 2 2 4) :
    NoN2 Y := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (S := Y) (f := 4) (by norm_num) h
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact CF67S.noN2_of_benderL216 (.linear 4 (by norm_num) e)

theorem noN2_Sz8 (Y : Type) [Group Y] (h : LieModel Y .twistedB2 0 2 3) :
    NoN2 Y := by
  have hS : SuzukiModel Y 2 3 := by
    rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.Proofs2.ivk93m12_szModel_equiv hS
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  exact CF67S.noN2_of_benderSz8 (.suzuki 1 le_rfl e)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
