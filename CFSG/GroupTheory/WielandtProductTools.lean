module

public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.GroupTheory.SolvableMinimalNormalNode

public section

namespace CFSG.GroupTheory.WielandtProduct

open Subgroup
open scoped Pointwise

theorem eq_pow_mul_pow_of_prime_dvd {n p q : ℕ} (hn : n ≠ 0) (hpq : p ≠ q)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → r = p ∨ r = q) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ (s := {p, q}) ?_ _ (fun _ _ => pow_zero _),
    Finset.prod_pair hpq]
  intro r hr
  rw [Nat.support_factorization] at hr
  have := h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  simpa using this

theorem swap_sylowOf_of_isSolvable {X : Type*} [Group X] [Finite X] (hX : Group.IsSolvable X)
    {A B : Subgroup X} [Group.IsNilpotent A] [Group.IsNilpotent B]
    (hmul : ∀ g : X, ∃ a ∈ A, ∃ b ∈ B, g = a * b)
    (hcard : Nat.card X = Nat.card A * Nat.card B)
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hpB : ¬ p ∣ Nat.card B) (hqA : ¬ q ∣ Nat.card A) :
    ∀ t ∈ sylowOf B q, ∀ s ∈ sylowOf A p, ∃ s' ∈ sylowOf A p, ∃ t' ∈ sylowOf B q,
      t * s = s' * t' := by
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
  have hvp : (Nat.card X).factorization p = (Nat.card A).factorization p := by
    rw [hcard, Nat.factorization_mul hA0 hB0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpB, add_zero]
  have hvq : (Nat.card X).factorization q = (Nat.card B).factorization q := by
    rw [hcard, Nat.factorization_mul hA0 hB0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqA, zero_add]
  let π : Set Nat.Primes := {r | r.val = p ∨ r.val = q}
  have hSπ : CFSG.IsPiSubgroup π (sylowOf A p) := by
    intro r hr
    left
    obtain ⟨a, ha⟩ := (isPGroup_sylowOf (A := A) (p := p)).exists_card_eq
    rw [ha] at hr
    exact (Nat.prime_dvd_prime_iff_eq r.2 hp.out).1 (r.2.dvd_of_dvd_pow hr)
  obtain ⟨H, hH, hSH⟩ := CFSG.SolvableHall.solvable_hall_containment hX π _ hSπ
  have hpi : ¬ p ∣ H.index := fun h => hH.p_in_pi_of_p_dvd_index ⟨p, hp.out⟩ h (Or.inl rfl)
  have hqi : ¬ q ∣ H.index := fun h => hH.p_in_pi_of_p_dvd_index ⟨q, hq.out⟩ h (Or.inr rfl)
  have hXH : Nat.card X = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hi0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hvpH : (Nat.card H).factorization p = (Nat.card X).factorization p := by
    rw [hXH, Nat.factorization_mul hH0 hi0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpi, add_zero]
  have hvqH : (Nat.card H).factorization q = (Nat.card X).factorization q := by
    rw [hXH, Nat.factorization_mul hH0 hi0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqi, add_zero]
  have hHcard : Nat.card H =
      p ^ (Nat.card H).factorization p * q ^ (Nat.card H).factorization q :=
    eq_pow_mul_pow_of_prime_dvd hH0 hpq fun r hr hrH => hH.p_in_pi_of_p_dvd_card ⟨r, hr⟩ hrH
  let TH : Sylow q H := Classical.arbitrary _
  let T₁ : Subgroup X := (TH : Subgroup H).map H.subtype
  have hT₁H : T₁ ≤ H := Subgroup.map_subtype_le _
  have hT₁card : Nat.card T₁ = q ^ (Nat.card X).factorization q := by
    rw [card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity, hvqH]
  let T1S : Sylow q X := Sylow.ofCard T₁ hT₁card
  let TS : Sylow q X := Sylow.ofCard (sylowOf B q) (by rw [card_sylowOf, hvq])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X TS T1S
  obtain ⟨a, ha, b, hb, rfl⟩ := hmul x
  have hmemT₁ : ∀ y, y ∈ T₁ ↔ (a * b)⁻¹ * y * (a * b) ∈ sylowOf B q := by
    intro y
    have h1 : y ∈ T1S ↔ y ∈ (a * b) • TS := by rw [hx]
    rw [mem_smul_sylow_iff] at h1
    exact h1
  have hT1 : ∀ t ∈ sylowOf B q, a * t * a⁻¹ ∈ T₁ := by
    intro t ht
    rw [hmemT₁]
    have hbt : b⁻¹ * t * b ∈ sylowOf B q := by
      have := ((mem_normalizer_iff.mp (le_normalizer_sylowOf (B.inv_mem hb))) t).mp ht
      simpa using this
    have e : (a * b)⁻¹ * (a * t * a⁻¹) * (a * b) = b⁻¹ * t * b := by group
    rw [e]
    exact hbt
  have hT1' : ∀ t₁ ∈ T₁, a⁻¹ * t₁ * a ∈ sylowOf B q := by
    intro t₁ ht₁
    rw [hmemT₁] at ht₁
    have := ((mem_normalizer_iff.mp (le_normalizer_sylowOf hb)) _).mp ht₁
    have e : b * ((a * b)⁻¹ * t₁ * (a * b)) * b⁻¹ = a⁻¹ * t₁ * a := by group
    rw [e] at this
    exact this
  have hHST : ∀ h ∈ H, ∃ s ∈ sylowOf A p, ∃ t ∈ T₁, h = s * t := by
    have hcS : Nat.card ((sylowOf A p).subgroupOf H) = p ^ (Nat.card H).factorization p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, card_sylowOf, hvpH, hvp]
    have hcT : Nat.card (T₁.subgroupOf H) = q ^ (Nat.card H).factorization q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁H).toEquiv, hT₁card, hvqH]
    have hcomp : IsComplement' ((sylowOf A p).subgroupOf H) (T₁.subgroupOf H) := by
      refine Subgroup.isComplement'_of_coprime ?_ ?_
      · rw [hcS, hcT]
        exact hHcard.symm
      · rw [hcS, hcT]
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp.out hq.out).2 hpq)
    intro h hh
    have hmem : (⟨h, hh⟩ : H) ∈
        ((sylowOf A p).subgroupOf H : Set H) * ((T₁.subgroupOf H : Subgroup H) : Set H) := by
      rw [hcomp.mul_eq]
      trivial
    obtain ⟨s, hs, t, ht, hst⟩ := Set.mem_mul.mp hmem
    exact ⟨s, hs, t, ht, by simpa using (congrArg Subtype.val hst).symm⟩
  intro t ht s hs
  have hs₁ : a * s * a⁻¹ ∈ sylowOf A p :=
    ((mem_normalizer_iff.mp (le_normalizer_sylowOf ha)) s).mp hs
  obtain ⟨s₂, hs₂, t₂, ht₂, he⟩ :=
    hHST _ (H.mul_mem (hT₁H (hT1 t ht)) (hSH hs₁))
  refine ⟨a⁻¹ * s₂ * a, ?_, a⁻¹ * t₂ * a, hT1' t₂ ht₂, ?_⟩
  · have := ((mem_normalizer_iff.mp (le_normalizer_sylowOf (A.inv_mem ha))) s₂).mp hs₂
    simpa using this
  · have e : t * s = a⁻¹ * (a * t * a⁻¹ * (a * s * a⁻¹)) * a := by group
    rw [e, he]
    group

theorem exists_isPGroup_normal_le {X : Type*} [Group X] [Finite X] (hX : Group.IsSolvable X)
    {H : Subgroup X} (hHn : H.Normal) (hne : H ≠ ⊥) :
    ∃ N : Subgroup X, N.Normal ∧ N ≠ ⊥ ∧ N ≤ H ∧ ∃ r : ℕ, r.Prime ∧ IsPGroup r N := by
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  let 𝓝 : Set (Subgroup X) := {N | N.Normal ∧ N ≠ ⊥ ∧ N ≤ H}
  obtain ⟨N, hN⟩ := 𝓝.toFinite.exists_minimal ⟨H, hHn, hne, le_rfl⟩
  obtain ⟨hNn, hNb, hNH⟩ := hN.prop
  have hmin : ∀ M : Subgroup X, M.Normal → M ≠ ⊥ → M ≤ N → M = N := fun M hM hMb hMN =>
    le_antisymm hMN (hN.le_of_le ⟨hM, hMb, hMN.trans hNH⟩ hMN)
  obtain ⟨r, d, hr, -, -, hcard⟩ :=
    CFSG.SolvableHall.solvable_minimal_normal_elementary_abelian (hNn := hNn) hX N hNb hmin
  have : Fact r.Prime := ⟨hr⟩
  exact ⟨N, hNn, hNb, hNH, r, hr, IsPGroup.of_card hcard⟩

theorem exists_isNormalPComplement {X : Type*} [Group X] [Finite X] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (S : Sylow p X) (R : Sylow q X) (H : Subgroup X)
    (hSR : ∀ s ∈ (S : Subgroup X), ∀ r ∈ (R : Subgroup X), Commute s r)
    (hRH : normalizer (R : Set X) ≤ H)
    (hH : ∀ h ∈ H, ∃ k : ℕ, ∀ s ∈ (S : Subgroup X), Commute (h ^ p ^ k) s) :
    ∃ K : Subgroup X, CFSG.GroupTheory.IsNormalPComplement p K :=
  (CFSG.GroupTheory.frobenius_normal_p_complement p).1.2 fun Q hQ =>
    isPGroup_automizer S R H hSR hRH hH Q hQ

theorem card_conjClass_eq_index {X : Type*} [Group X] [Finite X] (x : X) :
    Nat.card (ConjClasses.mk x).carrier = (centralizer ({x} : Set X)).index := by
  have h1 : (MulAction.stabilizer (ConjAct X) x).index = Nat.card (ConjClasses.mk x).carrier := by
    rw [MulAction.index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses, Nat.card_coe_set_eq]
  have h2 := (MulAction.stabilizer (ConjAct X) x).card_mul_index
  have h3 := (centralizer ({x} : Set X)).card_mul_index
  rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h2
  have h4 : Nat.card (ConjAct X) = Nat.card X := Nat.card_congr ConjAct.ofConjAct.toEquiv
  have hpos : 0 < Nat.card (centralizer ({x} : Set X)) := Nat.card_pos
  rw [← h1]
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans (h4.trans h3.symm))

end CFSG.GroupTheory.WielandtProduct
