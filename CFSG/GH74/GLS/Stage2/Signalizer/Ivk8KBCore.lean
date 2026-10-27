module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Foundations.Basic
import CFSG.RankThree.Coprime.InvolutionFixedRankBound

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ComponentClassification.PSL3Four

theorem isConj_r₁_of_mem_S {c : ↥R}
    (hc : (c : Equiv.Perm (Fin 42)) ∈ S) (h2 : orderOf c = 2) : IsConj c r₁R := by
  rcases (orderOf_eq_two_iff c).1 h2 with h | h | h | h
  · exact h
  · exact absurd hc (not_mem_S_of_isConj h not_mem_S_r₂)
  · exact absurd hc (not_mem_S_of_isConj h not_mem_S_r₃)
  · exact absurd hc (not_mem_S_of_isConj h not_mem_S_r₄)

theorem core_cent
    (hcent : ∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d)
    {c : ↥R} (hcI : IsConj c r₁R)
    {X : Subgroup ↥R} (hX : IsPGroup 3 X) (hXc : ∀ x ∈ X, x * c = c * x)
    (hXn : ∀ g : ↥R, g * c = c * g → g ∈ normalizer (X : Set ↥R)) : X = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨g, hgR, hgc⟩ := eq_conj_of_isConj hcI
  have hr1 : ((r₁R : ↥R) : Equiv.Perm (Fin 42)) = r₁ := rfl
  rw [hr1] at hgc
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq X (by simpa using hn))
  have hdvd : 3 ∣ Nat.card X := by rw [hn]; exact dvd_pow_self 3 hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hy3 : (y.1 : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    have h1 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    simpa using congrArg (fun z : X => ((z.1 : ↥R) : Equiv.Perm (Fin 42))) h1
  have hy1 : (y.1 : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext (Subtype.ext (by simpa using h))
    rw [this, orderOf_one] at hy
    omega
  set y' : Equiv.Perm (Fin 42) := (y.1 : Equiv.Perm (Fin 42)) with hy'
  have hy'R : y' ∈ R := y.1.2
  have hgi : g⁻¹ ∈ R := R.inv_mem hgR
  obtain ⟨d, hdC, hdne⟩ := hcent (g⁻¹ * y' * g) (R.mul_mem (R.mul_mem hgi hy'R) hgR) (by
      intro h
      apply hy1
      calc y' = g * (g⁻¹ * y' * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group) (by
      have := conj_pow (a := g⁻¹) (b := y') (i := 3)
      rw [inv_inv] at this
      rw [this, hy3]; group)
  obtain ⟨hdr, hdS⟩ := Subgroup.mem_inf.1 hdC
  have hdr' : d * r₁ = r₁ * d := (Subgroup.mem_centralizer_singleton_iff.1 hdr)
  set d' : Equiv.Perm (Fin 42) := g * d * g⁻¹ with hd'
  have hd'S : d' ∈ S := conj_mem_S hgR hdS
  have hd'c : d' * (c : Equiv.Perm (Fin 42)) = (c : Equiv.Perm (Fin 42)) * d' := by
    rw [hgc, hd']
    calc g * d * g⁻¹ * (g * r₁ * g⁻¹) = g * (d * r₁) * g⁻¹ := by group
      _ = g * (r₁ * d) * g⁻¹ := by rw [hdr']
      _ = g * r₁ * g⁻¹ * (g * d * g⁻¹) := by group
  have hd'R : (⟨d', S_le_R hd'S⟩ : ↥R) ∈ normalizer (X : Set ↥R) := hXn _ (Subtype.ext hd'c)
  have hz : (⟨d', S_le_R hd'S⟩ : ↥R) * y.1 * (⟨d', S_le_R hd'S⟩ : ↥R)⁻¹ * y.1⁻¹ ∈ X := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hd'R y.1).1 y.2
    exact X.mul_mem h1 (X.inv_mem y.2)
  set z : ↥R := (⟨d', S_le_R hd'S⟩ : ↥R) * y.1 * (⟨d', S_le_R hd'S⟩ : ↥R)⁻¹ * y.1⁻¹ with hzdef
  have hzperm : (z : Equiv.Perm (Fin 42)) = d' * (y' * d'⁻¹ * y'⁻¹) := by
    rw [hzdef]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hy']
    group
  have hzS : (z : Equiv.Perm (Fin 42)) ∈ S := by
    rw [hzperm]
    exact S.mul_mem hd'S (conj_mem_S hy'R (S.inv_mem hd'S))
  have hzc : (z : Equiv.Perm (Fin 42)) * (c : Equiv.Perm (Fin 42)) =
      (c : Equiv.Perm (Fin 42)) * z := congrArg Subtype.val (hXc z hz)
  have hzC : g⁻¹ * (z : Equiv.Perm (Fin 42)) * g ∈ C₁ := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · have : (z : Equiv.Perm (Fin 42)) * (g * r₁ * g⁻¹) = (g * r₁ * g⁻¹) * z := by
        rw [← hgc]; exact hzc
      calc g⁻¹ * (z : Equiv.Perm (Fin 42)) * g * r₁
          = g⁻¹ * ((z : Equiv.Perm (Fin 42)) * (g * r₁ * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * r₁ * g⁻¹) * z) * g := by rw [this]
        _ = r₁ * (g⁻¹ * (z : Equiv.Perm (Fin 42)) * g) := by group
    · have := conj_mem_S hgi hzS
      simpa using this
  have hz64 : (z : Equiv.Perm (Fin 42)) ^ 64 = 1 := by
    have h1 : (⟨g⁻¹ * (z : Equiv.Perm (Fin 42)) * g, hzC⟩ : ↥C₁) ^ 64 = 1 := by
      have := pow_card_eq_one' (G := ↥C₁) (x := ⟨g⁻¹ * (z : Equiv.Perm (Fin 42)) * g, hzC⟩)
      rwa [card_C₁] at this
    have h2 : (g⁻¹ * (z : Equiv.Perm (Fin 42)) * g) ^ 64 = 1 := by
      simpa using congrArg Subtype.val h1
    have h3 := conj_pow (a := g⁻¹) (b := (z : Equiv.Perm (Fin 42))) (i := 64)
    rw [inv_inv] at h3
    rw [h3] at h2
    calc (z : Equiv.Perm (Fin 42)) ^ 64
        = g * (g⁻¹ * (z : Equiv.Perm (Fin 42)) ^ 64 * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hX) ⟨z, hz⟩
  have hz3k : (z : Equiv.Perm (Fin 42)) ^ (3 ^ k) = 1 := by
    have h1 : (⟨z, hz⟩ : X) ^ (3 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    simpa using congrArg (fun w : X => ((w.1 : ↥R) : Equiv.Perm (Fin 42))) h1
  have hz1 : (z : Equiv.Perm (Fin 42)) = 1 := by
    have hcop : Nat.gcd 64 (3 ^ k) = 1 :=
      Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 64 3)
    have := pow_gcd_eq_one.2 (⟨hz64, hz3k⟩ : (z : Equiv.Perm (Fin 42)) ^ 64 = 1 ∧
      (z : Equiv.Perm (Fin 42)) ^ (3 ^ k) = 1)
    rwa [hcop, pow_one] at this
  apply hdne
  rw [hzperm] at hz1
  have h3 : d' * (y' * d'⁻¹ * y'⁻¹) = 1 := hz1
  have h4 : d' * y' = y' * d' := by
    calc d' * y' = (d' * (y' * d'⁻¹ * y'⁻¹)) * (y' * d') := by group
      _ = y' * d' := by rw [h3, one_mul]
  calc d * (g⁻¹ * y' * g) = g⁻¹ * (d' * y') * g := by rw [hd']; group
    _ = g⁻¹ * (y' * d') * g := by rw [h4]
    _ = (g⁻¹ * y' * g) * d := by rw [hd']; group


theorem core_fix (hexp : ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1)
    (hfix : ∀ y ∈ R, y ∉ S → y ^ 3 = 1 → r₄ * y = y * r₄ →
      ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1)
    {P : Subgroup ↥R} (hP : IsPGroup 3 P) (hPc : ∀ x ∈ P, x * r₄R = r₄R * x)
    (hPn : ∀ d : ↥R, (d : Equiv.Perm (Fin 42)) ∈ C₄ → d ∈ normalizer (P : Set ↥R)) :
    Nat.card P ≤ 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ 241920 := by
    have := Subgroup.card_subgroup_dvd_card P
    rwa [card_R] at this
  have hn3 : n = 3 := by
    have h3 : 3 ≤ n := by
      by_contra hn3
      have : n ≤ 2 := by omega
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    by_contra hne
    have h4 : 4 ≤ n := by omega
    have : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 h4).trans (hn ▸ hdvd)
    norm_num at this
  have hP27 : Nat.card P = 27 := by rw [hn, hn3]; norm_num
  have hcube : ∀ x : ↥R, x ∈ P → (x : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : P) ^ 27 = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := ⟨x, hx⟩)
      rwa [hP27] at this
    have h2 : (x : Equiv.Perm (Fin 42)) ^ 27 = 1 := by
      simpa using congrArg (fun w : P => ((w.1 : ↥R) : Equiv.Perm (Fin 42))) h1
    exact hexp _ x.2 h2
  have hnotS : ∃ y ∈ P, (y : Equiv.Perm (Fin 42)) ∉ S := by
    by_contra hall
    push Not at hall
    let φ : ↥P →* ↥C₄ := MonoidHom.codRestrict ((R.subtype.comp P.subtype)) C₄ (fun x => by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hall x.1 x.2⟩
      have := congrArg Subtype.val (hPc x.1 x.2)
      exact this)
    have hinj : Function.Injective φ := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    have := Subgroup.card_dvd_of_injective φ hinj
    rw [hP27, card_C₄] at this
    omega
  obtain ⟨y, hyP, hyS⟩ := hnotS
  obtain ⟨d, hdC, hdne⟩ := hfix (y : Equiv.Perm (Fin 42)) y.2 hyS (hcube y hyP) (by
    have := congrArg Subtype.val (hPc y hyP)
    exact this.symm)
  obtain ⟨hdr, hdS⟩ := Subgroup.mem_inf.1 hdC
  have hdR : (⟨d, S_le_R hdS⟩ : ↥R) ∈ normalizer (P : Set ↥R) := hPn _ hdC
  have h1 := (Subgroup.mem_normalizer_iff.1 hdR y).1 hyP
  have h2 : y * ((⟨d, S_le_R hdS⟩ : ↥R) * y * (⟨d, S_le_R hdS⟩ : ↥R)⁻¹) ∈ P := P.mul_mem hyP h1
  have h3 := hcube _ h2
  apply hdne
  simpa using h3

theorem four_le_pRank_S_of_e16 (h : ∃ F : Subgroup (Equiv.Perm (Fin 42)), F ≤ S ∧
    Nat.card F = 16 ∧ (∀ f ∈ F, ∀ g ∈ F, f * g = g * f) ∧ ∀ f ∈ F, f * f = 1) :
    4 ≤ pRank 2 ↥S := by
  obtain ⟨F, hFS, hF16, hcomm, hsq⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsElementaryAbelian 2 ↥(F.subgroupOf S) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · exact Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => ?_
      exact Subtype.ext (Subtype.ext (by simpa [pow_two] using hsq _ g.2))
  have hk : Nat.card ↥(F.subgroupOf S) = 2 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFS).toEquiv, hF16]
    norm_num
  exact RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hE hk


theorem exists_normal_E
    (hexp : ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1) {C : Type} [Group C] (e : C ≃* ↥C₄) :
    ∃ E : Subgroup C, E.Normal ∧ Nat.card E = 9 ∧ IsElementaryAbelian 3 ↥E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (derivedSeries C 2) = 9 := by
    have h1 := map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 2
    have h2 := card_derivedSeries_C₄.2.2.1
    rw [← h1, Subgroup.card_map_of_injective e.injective] at h2
    exact h2
  refine ⟨derivedSeries C 2, inferInstance, hcard, ?_⟩
  have hcomm : IsMulCommutative ↥(derivedSeries C 2) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => ?_
  have h9 : g ^ 9 = 1 := by
    have := pow_card_eq_one' (G := ↥(derivedSeries C 2)) (x := g)
    rwa [hcard] at this
  have h9' : g.1 ^ 9 = 1 := by rw [← Subgroup.coe_pow, h9, Subgroup.coe_one]
  have h27 : (e g.1) ^ 27 = 1 := by
    rw [← map_pow, show (27 : ℕ) = 9 * 3 by norm_num, pow_mul, h9', one_pow, map_one]
  have h27' : ((e g.1 : ↥C₄) : Equiv.Perm (Fin 42)) ^ 27 = 1 := by
    simpa using congrArg Subtype.val h27
  have hR : ((e g.1 : ↥C₄) : Equiv.Perm (Fin 42)) ∈ R :=
    S_le_R (Subgroup.mem_inf.1 (e g.1).2).2
  have h3 : (e g.1) ^ 3 = 1 := Subtype.ext (by simpa using hexp _ hR h27')
  have h3' : g.1 ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, h3, map_one]
  exact Subtype.ext (by rw [Subgroup.coe_pow, h3', Subgroup.coe_one])


end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
