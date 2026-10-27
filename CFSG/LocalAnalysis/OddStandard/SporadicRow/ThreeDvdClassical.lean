module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Assembly.LowTwoRank CatLeaf

private lemma three_dvd_of_coprime {m d N : ℕ} (h : m * d = N) (hN : 3 ∣ N)
    (hd : ¬ 3 ∣ d) : 3 ∣ m := by
  have hcop : Nat.Coprime 3 d := (Nat.prime_three.coprime_iff_not_dvd).2 hd
  rw [← h] at hN
  exact hcop.dvd_of_dvd_mul_right hN

private lemma three_dvd_of_sq_dvd {m d e N : ℕ} (h : m * d = N) (hd : 0 < d)
    (hde : d ∣ e) (h3e : 3 ∣ e) (heN : e ^ 2 ∣ N) : 3 ∣ m := by
  have h3d : 3 * d ∣ e * e := Nat.mul_dvd_mul h3e hde
  have h3d2 : 3 * d ∣ e ^ 2 := by simpa [pow_two] using h3d
  have h3dN : 3 * d ∣ N := h3d2.trans heN
  rw [← h] at h3dN
  exact Nat.dvd_of_mul_dvd_mul_right hd h3dN

theorem three_dvd_of_classical {τ : StatedLieTag} {n p f m : ℕ}
    (ha : StatedLieAdmissible τ n p f)
    (hτ : τ = .PSL ∨ τ = .PSU ∨ τ = .PSp ∨ τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus)
    (hq : ¬ 3 ∣ p ^ f)
    (h : m * lieOrderDivisor τ n (p ^ f) = lieOrderNumerator τ n (p ^ f)) : 3 ∣ m := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    simp only [StatedLieAdmissible] at ha
    obtain ⟨hp, hf, hn, -, -⟩ := ha
    set q := p ^ f with hqdef
    rw [show lieOrderDivisor .PSL n q = Nat.gcd n (q - 1) from rfl] at h
    by_cases h3d : 3 ∣ Nat.gcd n (q - 1)
    · have h3n : 3 ∣ n := h3d.trans (Nat.gcd_dvd_left n (q - 1))
      have h3e : 3 ∣ q - 1 := h3d.trans (Nat.gcd_dvd_right n (q - 1))
      have hn3 : 3 ≤ n := by
        obtain ⟨k, rfl⟩ := h3n
        omega
      have hdpos : 0 < Nat.gcd n (q - 1) := Nat.gcd_pos_of_pos_left (q - 1) (by omega)
      refine three_dvd_of_sq_dvd h hdpos (Nat.gcd_dvd_right n (q - 1)) h3e ?_
      have hfac : (q - 1) ^ 2 ∣ lieOrderNumerator .PSL n q := by
        simp only [lieOrderNumerator]
        have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
          · exact Finset.mem_Icc.2 ⟨by omega, hn3⟩
        have hPdvd : (∏ i ∈ ({2, 3} : Finset ℕ), (q ^ i - 1)) ∣
            (∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)) :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
        have h23 : (∏ i ∈ ({2, 3} : Finset ℕ), (q ^ i - 1)) =
            (q ^ 2 - 1) * (q ^ 3 - 1) :=
          Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)
        have hsq : (q - 1) ^ 2 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
          rw [pow_two]
          exact Nat.mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one q 2)
            (Nat.sub_one_dvd_pow_sub_one q 3)
        exact Dvd.dvd.mul_left (hsq.trans (h23 ▸ hPdvd)) _
      exact hfac
    · refine three_dvd_of_coprime h ?_ h3d
      have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .PSL n q := by
        simp only [lieOrderNumerator]
        have hmem : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, hn⟩
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem) _
      exact (three_dvd_sq_sub_one hq).trans hfac
  ·
    simp only [StatedLieAdmissible] at ha
    obtain ⟨hp, hf, hn, -⟩ := ha
    set q := p ^ f with hqdef
    rw [show lieOrderDivisor .PSU n q = Nat.gcd n (q + 1) from rfl] at h
    by_cases h3d : 3 ∣ Nat.gcd n (q + 1)
    · have h3n : 3 ∣ n := h3d.trans (Nat.gcd_dvd_left n (q + 1))
      have h3e : 3 ∣ q + 1 := h3d.trans (Nat.gcd_dvd_right n (q + 1))
      have hn3 : 3 ≤ n := by
        obtain ⟨k, rfl⟩ := h3n
        omega
      have hdpos : 0 < Nat.gcd n (q + 1) := Nat.gcd_pos_of_pos_left (q + 1) (by omega)
      refine three_dvd_of_sq_dvd h hdpos (Nat.gcd_dvd_right n (q + 1)) h3e ?_
      have hfac : (q + 1) ^ 2 ∣ lieOrderNumerator .PSU n q := by
        simp only [lieOrderNumerator]
        have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
          · exact Finset.mem_Icc.2 ⟨by omega, hn3⟩
        have hPdvd : (∏ i ∈ ({2, 3} : Finset ℕ),
              (if Even i then q ^ i - 1 else q ^ i + 1)) ∣
            (∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)) :=
          Finset.prod_dvd_prod_of_subset _ _ _ hsub
        have h23 : (∏ i ∈ ({2, 3} : Finset ℕ),
              (if Even i then q ^ i - 1 else q ^ i + 1)) =
            (q ^ 2 - 1) * (q ^ 3 + 1) := by
          have hodd3 : ¬ Even (3 : ℕ) := by rintro ⟨k, hk⟩; omega
          rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3),
            if_pos (even_two : Even (2 : ℕ)), if_neg hodd3]
        have hsq : (q + 1) ^ 2 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
          rw [pow_two]
          refine Nat.mul_dvd_mul ?_ ?_
          · rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
            exact dvd_mul_right _ _
          · simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
        exact Dvd.dvd.mul_left (hsq.trans (h23 ▸ hPdvd)) _
      exact hfac
    · refine three_dvd_of_coprime h ?_ h3d
      have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .PSU n q := by
        simp only [lieOrderNumerator]
        have hmem : (2 : ℕ) ∈ Finset.Icc 2 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
        have hdvd := Finset.dvd_prod_of_mem
          (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem
        have hf2 : (if Even (2 : ℕ) then q ^ 2 - 1 else q ^ 2 + 1) = q ^ 2 - 1 := by
          rw [if_pos (even_two : Even (2 : ℕ))]
        rw [hf2] at hdvd
        exact Dvd.dvd.mul_left hdvd _
      exact (three_dvd_sq_sub_one hq).trans hfac
  ·
    simp only [StatedLieAdmissible] at ha
    obtain ⟨hp, hf, hn, -⟩ := ha
    set q := p ^ f with hqdef
    rw [show lieOrderDivisor .PSp n q = Nat.gcd 2 (q - 1) from rfl] at h
    refine three_dvd_of_coprime h ?_ ?_
    · have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .PSp n q := by
        simp only [lieOrderNumerator]
        have hmem : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
        simpa using Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem) _
      exact (three_dvd_sq_sub_one hq).trans hfac
    · intro hd
      have h32 : 3 ∣ 2 := hd.trans (Nat.gcd_dvd_left 2 (q - 1))
      norm_num at h32
  ·
    simp only [StatedLieAdmissible] at ha
    obtain ⟨hp, hf, hn, -⟩ := ha
    set q := p ^ f with hqdef
    rw [show lieOrderDivisor .POmegaOdd n q = 2 from rfl] at h
    refine three_dvd_of_coprime h ?_ ?_
    · have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .POmegaOdd n q := by
        simp only [lieOrderNumerator]
        have hmem : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
        simpa using Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem) _
      exact (three_dvd_sq_sub_one hq).trans hfac
    · norm_num
  ·
    simp only [StatedLieAdmissible] at ha
    obtain ⟨hp, hf, hn⟩ := ha
    set q := p ^ f with hqdef
    rw [show lieOrderDivisor .POmegaPlus n q = Nat.gcd 4 (q ^ n - 1) from rfl] at h
    refine three_dvd_of_coprime h ?_ ?_
    · have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .POmegaPlus n q := by
        simp only [lieOrderNumerator]
        have hmem : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
        simpa using Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem) _
      exact (three_dvd_sq_sub_one hq).trans hfac
    · intro hd
      have h34 : 3 ∣ 4 := hd.trans (Nat.gcd_dvd_left 4 (q ^ n - 1))
      norm_num at h34
  ·
    simp only [StatedLieAdmissible] at ha
    obtain ⟨hp, hf, hn⟩ := ha
    set q := p ^ f with hqdef
    rw [show lieOrderDivisor .POmegaMinus n q = Nat.gcd 4 (q ^ n + 1) from rfl] at h
    refine three_dvd_of_coprime h ?_ ?_
    · have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .POmegaMinus n q := by
        simp only [lieOrderNumerator]
        have hmem : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
        simpa using Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) hmem) _
      exact (three_dvd_sq_sub_one hq).trans hfac
    · intro hd
      have h34 : 3 ∣ 4 := hd.trans (Nat.gcd_dvd_left 4 (q ^ n + 1))
      norm_num at h34

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
