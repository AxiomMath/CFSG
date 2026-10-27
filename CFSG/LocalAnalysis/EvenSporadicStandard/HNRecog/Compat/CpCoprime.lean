module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpKleinQuot

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

private lemma conj_mul_conj_inv {X : Type} [Group X] {ρ x : X} (hρ : ρ * ρ = 1) :
    ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = x := by
  have hconj2 : MulAut.conj ρ * MulAut.conj ρ = 1 := by
    rw [← map_mul, hρ, map_one]
  rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.mul_apply, hconj2,
    MulAut.one_apply]

private lemma conj_inv_of_sq_eq_one {X : Type} [Group X] {ρ p : X} (hρ : ρ * ρ = 1) :
    ρ * (p⁻¹ * (ρ * p * ρ⁻¹)) * ρ⁻¹ = (p⁻¹ * (ρ * p * ρ⁻¹))⁻¹ := by
  have hconj2 : MulAut.conj ρ * MulAut.conj ρ = 1 := by
    rw [← map_mul, hρ, map_one]
  have haeq : p⁻¹ * (ρ * p * ρ⁻¹) = p⁻¹ * MulAut.conj ρ p := by rw [MulAut.conj_apply]
  rw [haeq, ← MulAut.conj_apply, map_mul, map_inv, ← MulAut.mul_apply, hconj2,
    MulAut.one_apply, mul_inv_rev, inv_inv]

private lemma commute_conj {X : Type} [Group X] {g v n : X} (hgv : Commute g v)
    (hvn : Commute v n) : Commute v (g * n * g⁻¹) :=
  (hgv.symm.mul_right hvn).mul_right hgv.symm.inv_right

private lemma commute_of_conj_eq {X : Type} [Group X] {g x : X}
    (h : g * x * g⁻¹ = x) : Commute g x := by
  rw [commute_iff_eq]
  have := congrArg (· * g) h
  simpa [mul_assoc] using this

private lemma conj_mem_closure {X : Type} [Group X] {S : Set X} {g : X}
    (hS : ∀ n ∈ S, g * n * g⁻¹ ∈ S) {d : X} (hd : d ∈ Subgroup.closure S) :
    g * d * g⁻¹ ∈ Subgroup.closure S := by
  induction hd using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS x hx)
  | one => simp
  | mul x y _ _ ihx ihy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact (Subgroup.closure S).mul_mem ihx ihy
  | inv x _ ihx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact (Subgroup.closure S).inv_mem ihx

private lemma exists_fixed_conj_of_odd {X : Type} [Group X] {D : Subgroup X} [Fintype D]
    (hDodd : Odd (Nat.card D)) {ρ : X} (hρ : ρ * ρ = 1)
    (hρD : ∀ d ∈ D, ρ * d * ρ⁻¹ ∈ D) {p : X}
    (hp : p⁻¹ * (ρ * p * ρ⁻¹) ∈ D) :
    ∃ d ∈ D, ρ * (p * d) * ρ⁻¹ = p * d := by
  classical
  have hcardodd : Odd (Fintype.card D) := by
    rwa [Nat.card_eq_fintype_card] at hDodd
  let a : D := ⟨p⁻¹ * (ρ * p * ρ⁻¹), hp⟩
  have ha_conj : ρ * (a : X) * ρ⁻¹ = (a : X)⁻¹ := by
    show ρ * (p⁻¹ * (ρ * p * ρ⁻¹)) * ρ⁻¹ = (p⁻¹ * (ρ * p * ρ⁻¹))⁻¹
    exact conj_inv_of_sq_eq_one hρ
  let f : D → D := fun d => ⟨a * (ρ * (d : X) * ρ⁻¹), D.mul_mem a.2 (hρD d d.2)⟩
  have hf : Function.Involutive f := by
    intro d
    apply Subtype.ext
    show a * (ρ * ((a * (ρ * (d : X) * ρ⁻¹)) : X) * ρ⁻¹) = (d : X)
    have hstep : ρ * ((a * (ρ * (d : X) * ρ⁻¹)) : X) * ρ⁻¹
        = (ρ * (a : X) * ρ⁻¹) * (ρ * (ρ * (d : X) * ρ⁻¹) * ρ⁻¹) := by group
    rw [hstep, ha_conj, mul_inv_cancel_left, conj_mul_conj_inv hρ]
  have hσ2 : (hf.toPerm f) ^ 2 = 1 := by
    ext d
    rw [pow_two, Equiv.Perm.mul_apply, Function.Involutive.coe_toPerm, hf d,
      Equiv.Perm.one_apply]
  have hσ : (hf.toPerm f) ^ 2 ^ 1 = 1 := by simpa using hσ2
  have hα : ¬ 2 ∣ Fintype.card D := hcardodd.not_two_dvd_nat
  obtain ⟨d, hd⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hα hσ
  refine ⟨d, d.2, ?_⟩
  have hfd : a * (ρ * (d : X) * ρ⁻¹) = (d : X) := by
    have h := congrArg (fun x : D => (x : X)) hd
    simpa [f] using h
  have hpa : p * (a : X) = ρ * p * ρ⁻¹ := by
    show p * (p⁻¹ * (ρ * p * ρ⁻¹)) = ρ * p * ρ⁻¹
    group
  calc ρ * (p * (d : X)) * ρ⁻¹
      = (p * (a : X)) * (ρ * (d : X) * ρ⁻¹) := by rw [hpa]; group
    _ = p * ((a : X) * (ρ * (d : X) * ρ⁻¹)) := by group
    _ = p * (d : X) := by rw [hfd]

theorem cp_klein_gen {X : Type} [Group X] {N : Subgroup X} [Finite N] (hN : N.Normal) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hNp : IsPGroup p N) {t t' : X} (ht : orderOf t = 2)
    (ht' : orderOf t' = 2) (hcomm : t * t' = t' * t) :
    N ≤ Subgroup.closure {n : X | n ∈ N ∧
      (t * n = n * t ∨ t' * n = n * t' ∨ t * t' * n = n * (t * t'))} := by
  classical
  let S : Set X := {n : X | n ∈ N ∧
    (t * n = n * t ∨ t' * n = n * t' ∨ t * t' * n = n * (t * t'))}
  let D : Subgroup X := Subgroup.closure S
  change N ≤ D
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  have ht'2 : t' * t' = 1 := by
    have h := pow_orderOf_eq_one t'
    rwa [ht', pow_two] at h
  have hcommC : Commute t t' := hcomm
  have htt'2 : (t * t') * (t * t') = 1 := by
    simpa [pow_two, ht2, ht'2] using hcommC.mul_pow 2
  have hSt : ∀ n ∈ S, t * n * t⁻¹ ∈ S := by
    rintro n ⟨hnN, hnt | hnt | hnt⟩
    · exact ⟨hN.conj_mem n hnN t, Or.inl (commute_conj (Commute.refl t) hnt).eq⟩
    · exact ⟨hN.conj_mem n hnN t, Or.inr (Or.inl (commute_conj hcommC hnt).eq)⟩
    · exact ⟨hN.conj_mem n hnN t,
        Or.inr (Or.inr (commute_conj ((Commute.refl t).mul_right hcommC) hnt).eq)⟩
  have hSt' : ∀ n ∈ S, t' * n * t'⁻¹ ∈ S := by
    rintro n ⟨hnN, hnt | hnt | hnt⟩
    · exact ⟨hN.conj_mem n hnN t', Or.inl (commute_conj hcommC.symm hnt).eq⟩
    · exact ⟨hN.conj_mem n hnN t', Or.inr (Or.inl (commute_conj (Commute.refl t') hnt).eq)⟩
    · exact ⟨hN.conj_mem n hnN t',
        Or.inr (Or.inr (commute_conj (hcommC.mul_left (Commute.refl t')).symm hnt).eq)⟩
  have hStt' : ∀ n ∈ S, (t * t') * n * (t * t')⁻¹ ∈ S := by
    rintro n ⟨hnN, hnt | hnt | hnt⟩
    · exact ⟨hN.conj_mem n hnN (t * t'),
        Or.inl (commute_conj ((Commute.refl t).mul_left hcommC.symm) hnt).eq⟩
    · exact ⟨hN.conj_mem n hnN (t * t'),
        Or.inr (Or.inl (commute_conj (hcommC.mul_left (Commute.refl t')) hnt).eq)⟩
    · exact ⟨hN.conj_mem n hnN (t * t'),
        Or.inr (Or.inr (commute_conj (Commute.refl (t * t')) hnt).eq)⟩
  have hDt : ∀ d ∈ D, t * d * t⁻¹ ∈ D := fun d hd => conj_mem_closure hSt hd
  have hDt' : ∀ d ∈ D, t' * d * t'⁻¹ ∈ D := fun d hd => conj_mem_closure hSt' hd
  have hDtt' : ∀ d ∈ D, (t * t') * d * (t * t')⁻¹ ∈ D := fun d hd =>
    conj_mem_closure hStt' hd
  have hDleN : D ≤ N := (Subgroup.closure_le N).mpr (fun n hn => hn.1)
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype D := Fintype.ofInjective (Subgroup.inclusion hDleN)
    (Subgroup.inclusion_injective hDleN)
  have hDp : IsPGroup p D := hNp.to_le hDleN
  have hDodd : Odd (Nat.card D) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  by_contra hND
  let H : Subgroup ↥N := D.subgroupOf N
  have hHne : H ≠ ⊤ := by
    intro hHtop
    apply hND
    intro n hn
    have hmem : (⟨n, hn⟩ : ↥N) ∈ H := by
      rw [hHtop]
      trivial
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHne
  haveI hNil : Group.IsNilpotent ↥N := IsPGroup.isNilpotent hNp
  have hHnorm : H < Subgroup.normalizer H :=
    Group.normalizerCondition_of_isNilpotent H hHlt
  obtain ⟨n₀, hn₀mem, hn₀not⟩ := IsConcreteLE.exists_of_lt hHnorm
  let P : Subgroup X := N ⊓ Subgroup.normalizer (D : Set X)
  have hPN : P ≤ N := inf_le_left
  haveI : Fintype P := Fintype.ofInjective (Subgroup.inclusion hPN)
    (Subgroup.inclusion_injective hPN)
  have hDP : D ≤ P := le_inf hDleN Subgroup.le_normalizer
  have hDn : ∀ q ∈ P, ∀ d ∈ D, q * d * q⁻¹ ∈ D := by
    intro q hq d hd
    exact (Subgroup.mem_normalizer_iff (H := D)).mp hq.2 d |>.mp hd
  have ht_normD : t ∈ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    exact ⟨hDt d, fun hd => by
      have h1 := hDt (t * d * t⁻¹) hd
      rwa [conj_mul_conj_inv ht2] at h1⟩
  have ht'_normD : t' ∈ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    exact ⟨hDt' d, fun hd => by
      have h1 := hDt' (t' * d * t'⁻¹) hd
      rwa [conj_mul_conj_inv ht'2] at h1⟩
  have hsP : ∀ q ∈ P, t * q * t⁻¹ ∈ P := by
    intro q hq
    refine ⟨hN.conj_mem q hq.1 t, ?_⟩
    exact (Subgroup.normalizer (D : Set X)).mul_mem
      ((Subgroup.normalizer (D : Set X)).mul_mem ht_normD hq.2)
      ((Subgroup.normalizer (D : Set X)).inv_mem ht_normD)
  have hrP : ∀ q ∈ P, t' * q * t'⁻¹ ∈ P := by
    intro q hq
    refine ⟨hN.conj_mem q hq.1 t', ?_⟩
    exact (Subgroup.normalizer (D : Set X)).mul_mem
      ((Subgroup.normalizer (D : Set X)).mul_mem ht'_normD hq.2)
      ((Subgroup.normalizer (D : Set X)).inv_mem ht'_normD)
  have hn₀normD : (n₀ : X) ∈ Subgroup.normalizer (D : Set X) := by
    have hmem : n₀ ∈ (Subgroup.normalizer (D : Set X)).subgroupOf N := by
      rw [Subgroup.subgroupOf_normalizer_eq hDleN]
      exact hn₀mem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hn₀P : (n₀ : X) ∈ P := ⟨n₀.2, hn₀normD⟩
  have hn₀notD : (n₀ : X) ∉ D := fun hd => hn₀not hd
  have h1 : ∀ q ∈ P, q⁻¹ * (t * q * t⁻¹) ∈ D → q ∈ D := by
    intro q hq hfix
    obtain ⟨d, hdD, hdfix⟩ := exists_fixed_conj_of_odd (D := D) hDodd ht2 hDt hfix
    have hmN : q * d ∈ N := N.mul_mem hq.1 (hDleN hdD)
    have hmS : q * d ∈ S := ⟨hmN, Or.inl (commute_of_conj_eq hdfix)⟩
    have hmD : q * d ∈ D := Subgroup.subset_closure hmS
    have hqeq : q = (q * d) * d⁻¹ := by group
    rw [hqeq]
    exact D.mul_mem hmD (D.inv_mem hdD)
  have h2 : ∀ q ∈ P, q⁻¹ * (t' * q * t'⁻¹) ∈ D → q ∈ D := by
    intro q hq hfix
    obtain ⟨d, hdD, hdfix⟩ := exists_fixed_conj_of_odd (D := D) hDodd ht'2 hDt' hfix
    have hmN : q * d ∈ N := N.mul_mem hq.1 (hDleN hdD)
    have hmS : q * d ∈ S := ⟨hmN, Or.inr (Or.inl (commute_of_conj_eq hdfix))⟩
    have hmD : q * d ∈ D := Subgroup.subset_closure hmS
    have hqeq : q = (q * d) * d⁻¹ := by group
    rw [hqeq]
    exact D.mul_mem hmD (D.inv_mem hdD)
  have h3 : ∀ q ∈ P, q⁻¹ * (t * (t' * q * t'⁻¹) * t⁻¹) ∈ D → q ∈ D := by
    intro q hq hfix
    have hEq : t * (t' * q * t'⁻¹) * t⁻¹ = (t * t') * q * (t * t')⁻¹ := by group
    have hfix' : q⁻¹ * ((t * t') * q * (t * t')⁻¹) ∈ D := by
      rw [hEq] at hfix
      exact hfix
    obtain ⟨d, hdD, hdfix⟩ := exists_fixed_conj_of_odd (D := D) hDodd htt'2 hDtt' hfix'
    have hmN : q * d ∈ N := N.mul_mem hq.1 (hDleN hdD)
    have hmS : q * d ∈ S := ⟨hmN, Or.inr (Or.inr (commute_of_conj_eq hdfix))⟩
    have hmD : q * d ∈ D := Subgroup.subset_closure hmS
    have hqeq : q = (q * d) * d⁻¹ := by group
    rw [hqeq]
    exact D.mul_mem hmD (D.inv_mem hdD)
  have hPleD : P ≤ D := cp_klein_quot (P := P) (D := D) hDP hDn ht2 ht'2 hsP hrP hDt hDt'
    h1 h2 h3
  exact hn₀notD (hPleD hn₀P)

end CFSG.EvenSporadicStandard.HNRecog.Section4
