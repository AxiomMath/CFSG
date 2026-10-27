module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafExcOrd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafSp4C

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.X10

theorem cofactor_psl2_lt {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) < (q ^ 6) ^ 2 - 1 := by
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) ≤ q ^ 2 * (q ^ 3 + 1) * q ^ 4 :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have e1 : q ^ 2 * (q ^ 3 + 1) * q ^ 4 = q ^ 9 + q ^ 6 := by ring
  have h69 : q ^ 6 ≤ q ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1' : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h12 : 8 * q ^ 9 ≤ (q ^ 6) ^ 2 :=
    calc 8 * q ^ 9 ≤ q ^ 3 * q ^ 9 := Nat.mul_le_mul_right _ h8
      _ = (q ^ 6) ^ 2 := by ring
  omega

theorem g2_lt {q : ℕ} (hq : 3 ≤ q) :
    2 * (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) <
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
  have h3 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 9 ≤ q ^ 2 := by nlinarith
  have e6 : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    have h := Nat.sq_sub_sq (q ^ 3) 1
    rw [one_pow] at h
    rw [show q ^ 6 = (q ^ 3) ^ 2 by ring, h, mul_comm]
  have h4 : 2 * (q ^ 3 + 1) < q ^ 4 - 1 := by
    have : 3 * q ^ 3 ≤ q ^ 4 :=
      calc 3 * q ^ 3 ≤ q * q ^ 3 := Nat.mul_le_mul_right _ hq
        _ = q ^ 4 := by ring
    omega
  have hpos : 0 < q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
    Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by omega)
  calc 2 * (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1))
      = q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (2 * (q ^ 3 + 1)) := by rw [e6]; ring
    _ < q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := Nat.mul_lt_mul_of_pos_left h4 hpos

theorem d4_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    2 * (Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)) <
      Q ^ 12 * (Q ^ 4 - 1) * (Q ^ 6 - 1) * (Q ^ 8 - 1) := by
  have h2 : 4 ≤ Q ^ 2 := by nlinarith
  have h4 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h8 : Q ^ 4 ≤ Q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h6 : 1 ≤ Q ^ 6 - 1 := by
    have : Q ^ 2 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have e4 : Q ^ 4 - 1 = (Q ^ 2 - 1) * (Q ^ 2 + 1) := by
    have h := Nat.sq_sub_sq (Q ^ 2) 1
    rw [one_pow] at h
    rw [show Q ^ 4 = (Q ^ 2) ^ 2 by ring, h, mul_comm]
  have hk : 2 * (Q ^ 8 + Q ^ 4 + 1) < (Q ^ 2 + 1) * (Q ^ 8 - 1) := by
    have : 5 * (Q ^ 8 - 1) ≤ (Q ^ 2 + 1) * (Q ^ 8 - 1) := Nat.mul_le_mul_right _ (by omega)
    have h16 : 16 ≤ Q ^ 4 := by nlinarith
    omega
  have hpos : 0 < Q ^ 12 * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
    Nat.mul_pos (Nat.mul_pos (by positivity) h6) (by omega)
  calc 2 * (Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1))
      = Q ^ 12 * (Q ^ 6 - 1) * (Q ^ 2 - 1) * (2 * (Q ^ 8 + Q ^ 4 + 1)) := by ring
    _ < Q ^ 12 * (Q ^ 6 - 1) * (Q ^ 2 - 1) * ((Q ^ 2 + 1) * (Q ^ 8 - 1)) :=
        Nat.mul_lt_mul_of_pos_left hk hpos
    _ = Q ^ 12 * (Q ^ 4 - 1) * (Q ^ 6 - 1) * (Q ^ 8 - 1) := by rw [e4]; ring

theorem false_of_l4u4_of_excCompTag (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ' : StatedLieTag} {n' p f' f : ℕ} (hp2 : p ≠ 2) (hf : 1 ≤ f) (ht : ExcCompTag τ' n')
    (hadm' : StatedLieAdmissible τ' n' p f') (hX' : LieModel X τ' n' p f')
    (hX : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f)) :
    False := by
  have hp : p.Prime := hadm'.1
  have hQ3 : 3 ≤ p ^ f' := three_le_pow hp hp2 hadm'.2.1
  have hQ2 : 2 ≤ p ^ f' := by omega
  have hq3 : 3 ≤ p ^ f := three_le_pow hp hp2 hf
  have s1 : ∀ k, (p ^ f') ^ k - 1 ≤ (p ^ f') ^ k := fun k => Nat.sub_le _ _
  have a1 : ∀ k, (p ^ f') ^ k + 1 ≤ (p ^ f') ^ (k + 1) := pow_add_one_le hQ2
  have hl : ∀ k, 3 ≤ k → 16 * 1 ^ 2 < (p ^ f') ^ k := fun k hk => sixteen_lt_pow hQ3 hk
  obtain ⟨hX2, hXf⟩ := two_mul_card_l4u4 hp2 hX
  have hlow : (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) ≤
      Nat.card X * 2 := by
    rcases hX2 with h | h
    · exact h.ge
    · rw [h]
      gcongr
      omega
  rcases ht with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have h1 := card_psl2_mul_two hp hp2 hX'
    have h2 := (CatLeafProof.X10Sp.lieOrder_of_lieModel (Or.inl rfl) hp2 (by norm_num) hX').2
    simp only [lieSylowExponent] at h2
    have hf' : f' = 6 * f := by omega
    have hQ : p ^ f' = (p ^ f) ^ 6 := by rw [hf', ← pow_mul, mul_comm]
    rw [hQ] at h1
    have hq0 : 0 < (p ^ f) ^ 6 := by positivity
    have hup : Nat.card X * 2 ≤
        (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
      rcases hX2 with h | h
      · rw [h]
        gcongr
        omega
      · exact h.le
    have hlt := cofactor_psl2_lt (q := p ^ f) (by omega)
    have : (p ^ f) ^ 6 * (((p ^ f) ^ 6) ^ 2 - 1) ≤
        (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
      rw [← h1]
      calc Nat.card X * 2 ≤ _ := hup
        _ = _ := by ring
    exact absurd (Nat.le_of_mul_le_mul_left this hq0) (not_le.mpr hlt)
  · have hb : lieOrderCofactor .PSL 6 (p ^ f') ≤ 1 * (p ^ f') ^ 20 := by
      rw [one_mul]
      exact (prod_pow_sub_one_le _ _ fun i => i).trans_eq (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 15) (C := 20) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .PSL 8 (p ^ f') ≤ 1 * (p ^ f') ^ 35 := by
      rw [one_mul]
      exact (prod_pow_sub_one_le _ _ fun i => i).trans_eq (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 28) (C := 35) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  ·
    refine false_of_l4u4_of_cofactor_le (N := 15) (C := 21) (c := 1) hO hp2 hf hadm' hX' hX rfl
      ?_ fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
    simp only [lieOrderCofactor]
    rw [show Finset.Icc 2 6 = {2, 3, 4, 5, 6} from rfl, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num [Nat.even_iff]
    have hu := unitary_six_factor_le hQ2
    calc ((p ^ f') ^ 2 - 1) * (((p ^ f') ^ 3 + 1) * (((p ^ f') ^ 4 - 1) *
          (((p ^ f') ^ 5 + 1) * ((p ^ f') ^ 6 - 1))))
        = (((p ^ f') ^ 2 - 1) * ((p ^ f') ^ 4 - 1) * ((p ^ f') ^ 6 - 1)) *
          (((p ^ f') ^ 3 + 1) * ((p ^ f') ^ 5 + 1)) := by ring
      _ ≤ ((p ^ f') ^ 2 * (p ^ f') ^ 4 * (p ^ f') ^ 6) * (p ^ f') ^ 9 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (s1 2) (s1 4)) (s1 6)) hu
      _ = (p ^ f') ^ 21 := by ring
  · have hb : lieOrderCofactor .PSU 8 (p ^ f') ≤ 1 * (p ^ f') ^ 38 := by
      rw [one_mul]
      exact (prod_unitary_le hQ2 _).trans_eq (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 28) (C := 38) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .PSp 3 (p ^ f') ≤ 1 * (p ^ f') ^ 12 := by
      rw [one_mul]
      exact (prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 9) (C := 12) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .PSp 4 (p ^ f') ≤ 1 * (p ^ f') ^ 20 := by
      rw [one_mul]
      exact (prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 16) (C := 20) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .POmegaOdd 4 (p ^ f') ≤ 1 * (p ^ f') ^ 20 := by
      rw [one_mul]
      exact (prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 16) (C := 20) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .POmegaPlus 5 (p ^ f') ≤ 1 * (p ^ f') ^ 25 := by
      rw [one_mul]
      exact (mul_le_pow (s1 5) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 20) (C := 25) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .POmegaPlus 6 (p ^ f') ≤ 1 * (p ^ f') ^ 36 := by
      rw [one_mul]
      exact (mul_le_pow (s1 6) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 30) (C := 36) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .POmegaPlus 8 (p ^ f') ≤ 1 * (p ^ f') ^ 64 := by
      rw [one_mul]
      exact (mul_le_pow (s1 8) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 56) (C := 64) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .POmegaMinus 5 (p ^ f') ≤ 1 * (p ^ f') ^ 26 := by
      rw [one_mul]
      exact (mul_le_pow (a1 5) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)
    exact false_of_l4u4_of_cofactor_le (N := 20) (C := 26) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  ·
    obtain rfl : n' = 0 := hadm'.2.2.1
    obtain ⟨-, hc', hfac'⟩ := hO X .G2 0 p f' hadm' hX'
    simp only [lieSylowExponent] at hfac'
    have hff : f' = f := by omega
    subst hff
    simp only [lieOrderDivisor, lieOrderNumerator, mul_one] at hc'
    have := g2_lt hq3
    omega
  · have hb : lieOrderCofactor .F4 n' (p ^ f') ≤ 1 * (p ^ f') ^ 28 := by
      rw [one_mul]
      exact mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (s1 8)) (s1 6)) (s1 2)
    exact false_of_l4u4_of_cofactor_le (N := 24) (C := 28) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .E6 n' (p ^ f') ≤ 1 * (p ^ f') ^ 42 := by
      rw [one_mul]
      exact mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (s1 9))
        (s1 8)) (s1 6)) (s1 5)) (s1 2)
    exact false_of_l4u4_of_cofactor_le (N := 36) (C := 42) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .E7 n' (p ^ f') ≤ 1 * (p ^ f') ^ 70 := by
      rw [one_mul]
      exact mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow
        (s1 18) (s1 14)) (s1 12)) (s1 10)) (s1 8)) (s1 6)) (s1 2)
    exact false_of_l4u4_of_cofactor_le (N := 63) (C := 70) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .E8 n' (p ^ f') ≤ 1 * (p ^ f') ^ 128 := by
      rw [one_mul]
      exact mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow
        (mul_le_pow (s1 30) (s1 24)) (s1 20)) (s1 18)) (s1 14)) (s1 12)) (s1 8)) (s1 2)
    exact false_of_l4u4_of_cofactor_le (N := 120) (C := 128) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  · have hb : lieOrderCofactor .twistedE6 n' (p ^ f') ≤ 1 * (p ^ f') ^ 44 := by
      rw [one_mul]
      exact mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (a1 9))
        (s1 8)) (s1 6)) (a1 5)) (s1 2)
    exact false_of_l4u4_of_cofactor_le (N := 36) (C := 44) (c := 1) hO hp2 hf hadm' hX' hX rfl
      hb fun _ => ⟨by norm_num, hl _ (by norm_num)⟩
  ·
    obtain rfl : n' = 0 := hadm'.2.2
    obtain ⟨-, hc', hfac'⟩ := hO X .trialityD4 0 p f' hadm' hX'
    simp only [lieSylowExponent] at hfac'
    have hff : f = 2 * f' := by omega
    have hq : p ^ f = (p ^ f') ^ 2 := by rw [hff, mul_comm, pow_mul]
    simp only [lieOrderDivisor, lieOrderNumerator, mul_one] at hc'
    rw [hq] at hlow
    have := d4_lt hQ2
    have e : ((p ^ f') ^ 2) ^ 6 * (((p ^ f') ^ 2) ^ 2 - 1) * (((p ^ f') ^ 2) ^ 3 - 1) *
        (((p ^ f') ^ 2) ^ 4 - 1) =
        (p ^ f') ^ 12 * ((p ^ f') ^ 4 - 1) * ((p ^ f') ^ 6 - 1) * ((p ^ f') ^ 8 - 1) := by
      ring_nf
    rw [e] at hlow
    omega
  ·
    obtain ⟨k, hk⟩ := hadm'.2.2.2.2.1
    have h3f : (Nat.card X).factorization p = 3 * f' := (hO X _ n' p f' hadm' hX').2.2
    omega

end CFSG.ComponentClassification.GSThmB.Pump516
