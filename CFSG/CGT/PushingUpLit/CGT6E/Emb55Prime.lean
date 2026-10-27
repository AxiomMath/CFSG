module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Conj
public import CFSG.CGT.PushingUpLit.CGT6.Emb5FourT
public import CFSG.CGT.PushingUpLit.CGT6.EmbX

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

theorem exists_conj_of_card_prime {X : Type*} [Group X] [Finite X] (p : ℕ) [hp : Fact p.Prime]
    {P Q : Subgroup X} (hP : Nat.card P = p) (hQ : Nat.card Q = p)
    (hX : (Nat.card X).factorization p ≤ 1) :
    ∃ x : X, ∀ q ∈ Q, ∃ y ∈ P, q = x * y * x⁻¹ := by
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by simpa using hP)
  have hQp : IsPGroup p Q := IsPGroup.of_card (n := 1) (by simpa using hQ)
  obtain ⟨S₁, hS₁⟩ := hPp.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := hQp.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X S₁ S₂
  have hc : ∀ S : Sylow p X, Nat.card ↥(S : Subgroup X) ≤ p := fun S => by
    rw [S.card_eq_multiplicity]
    calc p ^ (Nat.card X).factorization p ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hX
      _ = p := pow_one p
  have hPS : P = (S₁ : Subgroup X) := Subgroup.eq_of_le_of_card_ge hS₁ (by rw [hP]; exact hc S₁)
  have hQS : Q = (S₂ : Subgroup X) := Subgroup.eq_of_le_of_card_ge hS₂ (by rw [hQ]; exact hc S₂)
  refine ⟨x, fun q hq => ?_⟩
  have h1 : q ∈ (S₂ : Subgroup X) := hQS ▸ hq
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  refine ⟨x⁻¹ * q * x, ?_, by group⟩
  rw [hPS]
  simpa [MulAut.smul_def, map_inv, MulAut.conj_apply] using h1

section MulAutPart

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

@[expose] def prodSub (N Y : Subgroup (MulAut V))
    (hYN : Y ≤ Subgroup.normalizer (N : Set (MulAut V))) : Subgroup (MulAut V) where
  carrier := {x | ∃ n ∈ N, ∃ y ∈ Y, x = n * y}
  one_mem' := ⟨1, N.one_mem, 1, Y.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, y₁, hy₁, rfl⟩ ⟨n₂, hn₂, y₂, hy₂, rfl⟩
    refine ⟨n₁ * (y₁ * n₂ * y₁⁻¹), ?_, y₁ * y₂, Y.mul_mem hy₁ hy₂, by group⟩
    exact N.mul_mem hn₁ ((Subgroup.mem_normalizer_iff.mp (hYN hy₁) n₂).mp hn₂)
  inv_mem' := by
    rintro _ ⟨n, hn, y, hy, rfl⟩
    refine ⟨y⁻¹ * n⁻¹ * y, ?_, y⁻¹, Y.inv_mem hy, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (hYN (Y.inv_mem hy)) n⁻¹).mp (N.inv_mem hn)
    simpa using this

theorem card_prodSub {N : Subgroup (MulAut V)} (hYN : Y ≤ Subgroup.normalizer (N : Set (MulAut V)))
    (hY : Nat.card ↥Y = 3) (hcop : Nat.Coprime (Nat.card ↥N) 3) :
    Nat.card ↥(prodSub N Y hYN) = 3 * Nat.card ↥N := by
  have hle1 : N ≤ prodSub N Y hYN := fun n hn => ⟨n, hn, 1, Y.one_mem, by simp⟩
  have hle2 : Y ≤ prodSub N Y hYN := fun y hy => ⟨1, N.one_mem, y, hy, by simp⟩
  have hsurj : Function.Surjective (fun p : N × Y =>
      (⟨(p.1 : MulAut V) * p.2, (p.1 : MulAut V), p.1.2, (p.2 : MulAut V), p.2.2, rfl⟩ :
        prodSub N Y hYN)) := by
    rintro ⟨_, n, hn, y, hy, rfl⟩
    exact ⟨(⟨n, hn⟩, ⟨y, hy⟩), rfl⟩
  have hup := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, hY] at hup
  have hd1 : Nat.card ↥N ∣ Nat.card ↥(prodSub N Y hYN) := Subgroup.card_dvd_of_le hle1
  have hd2 : 3 ∣ Nat.card ↥(prodSub N Y hYN) := hY ▸ Subgroup.card_dvd_of_le hle2
  have hd : 3 * Nat.card ↥N ∣ Nat.card ↥(prodSub N Y hYN) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hd2 hd1
  have hpos : 0 < Nat.card ↥(prodSub N Y hYN) := Nat.card_pos
  have := Nat.le_of_dvd hpos hd
  omega

omit [Finite V] in
theorem conjClosure_le_prodSub {N : Subgroup (MulAut V)}
    (hYN : Y ≤ Subgroup.normalizer (N : Set (MulAut V))) :
    conjClosure Y N ≤ prodSub N Y hYN := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  refine ⟨g * (y * g⁻¹ * y⁻¹), ?_, y, hy, by group⟩
  exact N.mul_mem hg ((Subgroup.mem_normalizer_iff.mp (hYN hy) g⁻¹).mp (N.inv_mem hg))

theorem _root_.CFSG.CGT.PushingUpLit.CGT6.Sec5Hyp.centralizes_of_normalized
    (h : Sec5Hyp V G T Y) {N : Subgroup (MulAut V)} (hNG : N ≤ G)
    (hYN : Y ≤ Subgroup.normalizer (N : Set (MulAut V)))
    (hTN : T ≤ Subgroup.normalizer (N : Set (MulAut V)))
    (hcop : Nat.Coprime (Nat.card ↥N) 6) : ∀ g ∈ N, ∀ y ∈ Y, y * g = g * y := by
  have hcop3 : Nat.Coprime (Nat.card ↥N) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
  have hcop2 : Nat.Coprime (Nat.card ↥N) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
  set X : Subgroup (MulAut V) := conjClosure Y N with hX
  have hYX : Y ≤ X := le_conjClosure
  have hXG : X ≤ G := by
    rw [hX, conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    exact G.mul_mem (G.mul_mem (hNG hg) (h.yle hy).1) (G.inv_mem (hNG hg))
  have hXP : X ≤ prodSub N Y hYN := conjClosure_le_prodSub hYN
  have hcardP := card_prodSub hYN h.ycard hcop3
  have hXdvd : Nat.card ↥X ∣ 3 * Nat.card ↥N := hcardP ▸ Subgroup.card_dvd_of_le hXP
  have hodd : Odd (Nat.card ↥X) :=
    Odd.of_dvd_nat (Odd.mul (by decide) (Nat.Coprime.odd_of_right hcop2)) hXdvd
  have h3N : ¬ 3 ∣ Nat.card ↥N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop3.symm
  have hfact : (Nat.card ↥X).factorization 3 ≤ 1 := by
    have h1 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (Nat.mul_ne_zero (by norm_num) Nat.card_pos.ne')).mpr hXdvd 3
    have h2 : (3 * Nat.card ↥N).factorization 3 = 1 := by
      rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne']
      simp [Nat.Prime.factorization_self Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd h3N]
    omega
  have hkey : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
    intro t ht
    have hle : X ≤ X.comap (MulAut.conj t).toMonoidHom := by
      rw [hX, conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      have hty : t * y = y * t := Subgroup.mem_centralizer_iff.mp (h.yle hy).2 t ht
      have hty' : t * y * t⁻¹ = y := by rw [hty]; group
      have e : t * (g * y * g⁻¹) * t⁻¹ = (t * g * t⁻¹) * y * (t * g * t⁻¹)⁻¹ := by
        calc t * (g * y * g⁻¹) * t⁻¹ = (t * g * t⁻¹) * (t * y * t⁻¹) * (t * g * t⁻¹)⁻¹ := by group
          _ = (t * g * t⁻¹) * y * (t * g * t⁻¹)⁻¹ := by rw [hty']
      have hgN : t * g * t⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hTN ht) g).mp hg
      show t * (g * y * g⁻¹) * t⁻¹ ∈ X
      rw [e]
      exact mem_conjClosure_of_mem hgN hy
    intro x hx
    exact hle hx
  have hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)) := fun t ht =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨hkey t ht x, fun hx => by
      have := hkey t⁻¹ (T.inv_mem ht) _ hx
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at this⟩
  have hgen : ∀ M : Subgroup (MulAut V), M ≤ X → Y ≤ M →
      X ≤ Subgroup.normalizer (M : Set (MulAut V)) → M = X := by
    intro M hMX hYM hXM
    refine le_antisymm hMX ?_
    rw [hX, conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, y, hy, rfl⟩
    have hcg : conjSub g Y ≤ X := fun z hz => by
      obtain ⟨y', hy', rfl⟩ := mem_conjSub.mp hz
      exact mem_conjClosure_of_mem hg hy'
    have hc1 : Nat.card ↥(Y.subgroupOf X) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv, h.ycard]
    have hc2 : Nat.card ↥((conjSub g Y).subgroupOf X) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcg).toEquiv, card_conjSub, h.ycard]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_conj_of_card_prime 3 hc1 hc2 hfact
    have hq : (⟨g * y * g⁻¹, hcg (conj_mem_conjSub hy)⟩ : ↥X) ∈ (conjSub g Y).subgroupOf X :=
      conj_mem_conjSub hy
    obtain ⟨y', hy', hq'⟩ := hx _ hq
    have hxy : g * y * g⁻¹ = (x : MulAut V) * y' * (x : MulAut V)⁻¹ := congrArg Subtype.val hq'
    rw [hxy]
    have hy'Y : (y' : MulAut V) ∈ Y := hy'
    exact (Subgroup.mem_normalizer_iff.mp (hXM x.2) _).mp (hYM hy'Y)
  have hXY : X = Y := h.eq_of_normalizes hXG hYX hodd hgen hTX
  intro g hg y hy
  have h1 : g * y * g⁻¹ ∈ X := mem_conjClosure_of_mem hg hy
  rw [hXY] at h1
  have hcN : g * y * g⁻¹ * y⁻¹ ∈ N := by
    have e : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem hg ((Subgroup.mem_normalizer_iff.mp (hYN hy) g⁻¹).mp (N.inv_mem hg))
  have hcY : g * y * g⁻¹ * y⁻¹ ∈ Y := Y.mul_mem h1 (Y.inv_mem hy)
  have hc1 : g * y * g⁻¹ * y⁻¹ = 1 := by
    have hz3 : (g * y * g⁻¹ * y⁻¹) ^ 3 = 1 := h.pow_three hcY
    have hord : orderOf (g * y * g⁻¹ * y⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hordN : orderOf (g * y * g⁻¹ * y⁻¹) ∣ Nat.card ↥N := by
      have := orderOf_dvd_natCard (⟨_, hcN⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop3 hordN hord)
  have h2 : g * y * g⁻¹ = y := mul_inv_eq_one.mp hc1
  calc y * g = (g * y * g⁻¹) * g := by rw [h2]
    _ = g * y := by group

end MulAutPart

end CFSG.CGT.PushingUpLit.CGT6E
