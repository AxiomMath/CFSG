module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem g2_outerFix_arith {x s : ℕ} (hx : 3 ≤ x) (hs : 5 ≤ s)
    (h : x ^ s * ((x ^ s) ^ 2 - 1) ∣ CFSG.Open.ordG2 x) : False := by
  have hx0 : 0 < x := by omega
  have h2' : 0 < x ^ 2 - 1 := by
    have : 1 < x ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have h6' : 0 < x ^ 6 - 1 := by
    have : 1 < x ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hpos : 0 < CFSG.Open.ordG2 x := by
    unfold CFSG.Open.ordG2
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hx0 _) h6') h2'
  have hle := Nat.le_of_dvd hpos h
  have hup : CFSG.Open.ordG2 x < x ^ 14 := by
    unfold CFSG.Open.ordG2
    have e : x ^ 14 = x ^ 6 * x ^ 6 * x ^ 2 := by ring
    rw [e]
    have a1 : x ^ 6 - 1 < x ^ 6 := by omega
    have a2 : x ^ 2 - 1 ≤ x ^ 2 := Nat.sub_le _ _
    calc x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1) < x ^ 6 * x ^ 6 * (x ^ 2 - 1) := by
          apply Nat.mul_lt_mul_of_pos_right _ h2'
          exact Nat.mul_lt_mul_of_pos_left a1 (pow_pos hx0 _)
      _ ≤ x ^ 6 * x ^ 6 * x ^ 2 := Nat.mul_le_mul_left _ a2
  have hA : x ^ 5 ≤ x ^ s := Nat.pow_le_pow_right hx0 hs
  have hA2 : (x ^ 5) ^ 2 ≤ (x ^ s) ^ 2 := Nat.pow_le_pow_left hA 2
  have hB : x ^ 14 ≤ x ^ 5 * ((x ^ 5) ^ 2 - 1) := by
    have e1 : (x ^ 5) ^ 2 = x * x ^ 9 := by ring
    have h9 : 1 ≤ x ^ 9 := Nat.one_le_pow _ _ hx0
    have h3x : 3 * x ^ 9 ≤ x * x ^ 9 := Nat.mul_le_mul_right _ hx
    have h10 : x ^ 9 ≤ (x ^ 5) ^ 2 - 1 := by omega
    calc x ^ 14 = x ^ 5 * x ^ 9 := by ring
      _ ≤ x ^ 5 * ((x ^ 5) ^ 2 - 1) := Nat.mul_le_mul_left _ h10
  have hC : x ^ 5 * ((x ^ 5) ^ 2 - 1) ≤ x ^ s * ((x ^ s) ^ 2 - 1) :=
    Nat.mul_le_mul hA (Nat.sub_le_sub_right hA2 1)
  omega

theorem g2_false_of_outer_fixing_sl2 {p f s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ f) (hs : s.Prime) (hs5 : 5 ≤ s)
    (z : MulAut (adjointGroup Tag.G2 K)) (hz : orderOf z = s) (hzinn : ¬ IsInnerAut z)
    (S : Subgroup (adjointGroup Tag.G2 K))
    (hS : Nat.card S = Nat.card K * (Nat.card K ^ 2 - 1)) (hfix : ∀ x ∈ S, z x = x) :
    False := by
  have hsodd : Odd s := hs.odd_of_ne_two (by omega)
  obtain ⟨hsf, i, δ, τ, -, hτord, hδ⟩ :=
    g2_field_descent hp hp2 hf K hK hs hsodd hz hzinn
  have hzpow : ∀ n : ℕ, ∀ x ∈ S, (z ^ n) x = x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix x hx, ih x hx]
  have hmap : S.map δ.toMonoidHom ≤ fixSub (g2FieldHom K τ) := by
    rintro y ⟨x, hx, rfl⟩
    rw [mem_fixSub, ← hδ]
    show (δ * z ^ i * δ⁻¹) (δ x) = δ x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hzpow i x hx]
  obtain ⟨e⟩ := g2_fixSub_equiv (K := K) τ
  have hcardfix : Nat.card (fixSub (g2FieldHom K τ)) = CFSG.Open.ordG2 (p ^ (f / s)) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
      card_fixSubfield hp hf hK hτord]
  have hdvd : Nat.card S ∣ Nat.card (fixSub (g2FieldHom K τ)) := by
    have h1 : Nat.card (S.map δ.toMonoidHom) = Nat.card S :=
      Subgroup.card_map_of_injective δ.injective
    rw [← h1]
    exact Subgroup.card_dvd_of_le hmap
  have hm1 : 1 ≤ f / s := Nat.div_pos (Nat.le_of_dvd (by omega) hsf) hs.pos
  have hx3 : 3 ≤ p ^ (f / s) := by
    have h5 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 3 ≤ p := h5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (f / s) := Nat.pow_le_pow_right hp.pos hm1
  have hKx : Nat.card K = (p ^ (f / s)) ^ s := by
    rw [hK, ← pow_mul, Nat.div_mul_cancel hsf]
  rw [hS, hcardfix, hKx] at hdvd
  exact g2_outerFix_arith hx3 hs5 hdvd

end CFSG.GH74.GLS.Stage2.Bender.Thm1
