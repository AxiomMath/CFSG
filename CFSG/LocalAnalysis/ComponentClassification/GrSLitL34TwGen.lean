module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

private theorem exists_commuting_in_coset {M B : Type*} [Group M] [Finite M] [Group B]
    (ρ : M →* B) (hker : Odd (Nat.card ρ.ker)) {a u : M} (ha : a * a = 1)
    (hc : ρ u * ρ a = ρ a * ρ u) : ∃ u' : M, ρ u' = ρ u ∧ a * u' = u' * a := by
  classical
  have hρa : ρ a * ρ a = 1 := by rw [← map_mul, ha, map_one]
  let f : M → M := fun k => u⁻¹ * (a * (u * k) * a)
  have hf_mem : ∀ k : M, k ∈ ρ.ker → f k ∈ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    simp only [f, map_mul, map_inv, hk, mul_one]
    rw [← hc, mul_assoc, hρa, mul_one, inv_mul_cancel]
  have hf_inv : ∀ k : M, f (f k) = k := by
    intro k
    simp only [f]
    calc u⁻¹ * (a * (u * (u⁻¹ * (a * (u * k) * a))) * a)
        = u⁻¹ * ((a * a) * (u * k) * (a * a)) := by group
      _ = k := by rw [ha]; group
  let σ : Equiv.Perm ρ.ker :=
    Function.Involutive.toPerm (fun k => ⟨f k, hf_mem k k.2⟩) fun k => Subtype.ext (hf_inv k)
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext k
    exact hf_inv k
  haveI : Fintype ρ.ker := Fintype.ofFinite _
  have hodd : ¬ 2 ∣ Fintype.card ρ.ker := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨t, ht⟩ := hker
    omega
  obtain ⟨k₀, hk₀⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hσ
  have hfix : u⁻¹ * (a * (u * (k₀ : M)) * a) = k₀ := congrArg Subtype.val hk₀
  have h1 : a * (u * (k₀ : M)) * a = u * k₀ := by
    calc a * (u * (k₀ : M)) * a = u * (u⁻¹ * (a * (u * (k₀ : M)) * a)) := by group
      _ = u * k₀ := by rw [hfix]
  refine ⟨u * k₀, ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp k₀.2, mul_one]
  · calc a * (u * (k₀ : M)) = a * (u * (k₀ : M)) * (a * a) := by rw [ha, mul_one]
      _ = (a * (u * (k₀ : M)) * a) * a := by group
      _ = (u * k₀) * a := by rw [h1]

theorem exists_invol_lift_commuting {M B : Type*} [Group M] [Finite M] [Group B] (ρ : M →* B)
    (hker : Odd (Nat.card ρ.ker)) {a u : M} (ha : a * a = 1) (hu : ρ u * ρ u = 1)
    (hc : ρ u * ρ a = ρ a * ρ u) (hne : ρ u ≠ 1) :
    ∃ y : M, y * y = 1 ∧ ρ y = ρ u ∧ y * a = a * y := by
  clear hne
  obtain ⟨u', hρu', hcomm⟩ := exists_commuting_in_coset ρ hker ha hc
  have hv : u' * u' ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, hρu', hu]
  obtain ⟨j, hj⟩ : Odd (orderOf (u' * u')) :=
    Odd.of_dvd_nat hker (Subgroup.orderOf_dvd_natCard ρ.ker hv)
  refine ⟨u' ^ orderOf (u' * u'), ?_, ?_, ?_⟩
  · rw [← (Commute.refl u').mul_pow, pow_orderOf_eq_one]
  · rw [map_pow, hρu', hj, pow_succ, pow_mul, pow_two, hu, one_pow, one_mul]
  · exact ((Commute.pow_right (show Commute a u' from hcomm) _).eq).symm

theorem exists_conj_of_ker {M B : Type*} [Group M] [Finite M] [Group B] (ρ : M →* B)
    (hker : Odd (Nat.card ρ.ker)) {m₁ m₂ : M} (h₁ : m₁ * m₁ = 1) (h₂ : m₂ * m₂ = 1)
    (h : ρ m₁ = ρ m₂) : ∃ o : M, ρ o = 1 ∧ o⁻¹ * m₁ * o = m₂ := by
  have hm₁ : m₁⁻¹ = m₁ := inv_eq_of_mul_eq_one_right h₁
  have hm₂ : m₂⁻¹ = m₂ := inv_eq_of_mul_eq_one_right h₂
  have hx : m₁ * m₂ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, ← h, ← map_mul, h₁, map_one]
  obtain ⟨j, hj⟩ : Odd (orderOf (m₁ * m₂)) :=
    Odd.of_dvd_nat hker (Subgroup.orderOf_dvd_natCard ρ.ker hx)
  have hconj : m₁ * (m₁ * m₂) = (m₁ * m₂)⁻¹ * m₁ := by
    rw [← mul_assoc, h₁, one_mul, mul_inv_rev, hm₁, hm₂, mul_assoc, h₁, mul_one]
  have hpow : m₁ * (m₁ * m₂) ^ (j + 1) = ((m₁ * m₂)⁻¹) ^ (j + 1) * m₁ :=
    SemiconjBy.pow_right hconj (j + 1)
  have hsq : (m₁ * m₂) ^ (j + 1) * (m₁ * m₂) ^ (j + 1) = m₁ * m₂ := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf (m₁ * m₂) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  refine ⟨(m₁ * m₂) ^ (j + 1), ?_, ?_⟩
  · rw [map_pow, MonoidHom.mem_ker.mp hx, one_pow]
  · calc ((m₁ * m₂) ^ (j + 1))⁻¹ * m₁ * (m₁ * m₂) ^ (j + 1)
        = ((m₁ * m₂) ^ (j + 1))⁻¹ * (m₁ * (m₁ * m₂) ^ (j + 1)) := by rw [mul_assoc]
      _ = ((m₁ * m₂) ^ (j + 1))⁻¹ * (((m₁ * m₂) ^ (j + 1))⁻¹ * m₁) := by rw [hpow, inv_pow]
      _ = ((m₁ * m₂) ^ (j + 1) * (m₁ * m₂) ^ (j + 1))⁻¹ * m₁ := by rw [mul_inv_rev, mul_assoc]
      _ = m₂ := by
        rw [hsq, mul_inv_rev, hm₁, hm₂, mul_assoc, h₁, mul_one]

theorem odd_card_of_perfect_quotient {H Q A : Type*} [Group H] [Finite H] [Group Q] [Group A]
    [Group.IsSolvable A] (f : H →* A) (hf : Odd (Nat.card f.ker)) (π : H →* Q)
    (hπ : Function.Surjective π) (hQ : Group.IsPerfect Q) : Odd (Nat.card Q) := by
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable A).solvable
  have h1 : derivedSeries H n ≤ f.ker := by
    intro x hx
    have hfx : f x ∈ derivedSeries A n :=
      map_derivedSeries_le_derivedSeries f n (Subgroup.mem_map_of_mem f hx)
    rw [hn, Subgroup.mem_bot] at hfx
    exact hfx
  have h2 : f.ker.map π = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : Subgroup Q) = derivedSeries Q n := (Group.IsPerfect.derivedSeries_eq_top Q n).symm
      _ = (derivedSeries H n).map π := (map_derivedSeries_eq hπ n).symm
      _ ≤ f.ker.map π := Subgroup.map_mono h1
  have h3 : Nat.card Q ∣ Nat.card f.ker := by
    have := Subgroup.card_map_dvd (H := f.ker) π
    rwa [h2, Subgroup.card_top] at this
  exact Odd.of_dvd_nat hf h3

theorem exists_lift_two_subgroup {Y H : Type*} [Group Y] [Finite Y] [Group H] (π : Y →* H)
    (hker : Odd (Nat.card π.ker)) {E : Subgroup H} (hE : IsPGroup 2 E) (hEr : E ≤ π.range) :
    ∃ E' : Subgroup Y, IsPGroup 2 E' ∧ E'.map π = E ∧ Nat.card E' = Nat.card E := by
  have hmap : (E.comap π).map π = E := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hEr]
  haveI : Finite π.range := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  haveI : Finite E :=
    Finite.of_injective (Subgroup.inclusion hEr) (Subgroup.inclusion_injective hEr)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hE
  have hdvd : 2 ^ k ∣ Nat.card (E.comap π) := by
    have := Subgroup.card_map_dvd (H := E.comap π) π
    rwa [hmap, hk] at this
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hE'card : Nat.card (K.map (E.comap π).subtype) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective (E.comap π).subtype_injective, hK]
  have hle : K.map (E.comap π).subtype ≤ E.comap π := Subgroup.map_subtype_le K
  have hbot : π.ker ⊓ K.map (E.comap π).subtype = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hE'card]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hker)
  have hcardmap : Nat.card ((K.map (E.comap π).subtype).map π) =
      Nat.card (K.map (E.comap π).subtype) := by
    rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hbot, Subgroup.relIndex_bot_left]
  have hmapE : (K.map (E.comap π).subtype).map π = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact (Subgroup.map_mono hle).trans hmap.le
    · rw [hcardmap, hE'card, hk]
  exact ⟨K.map (E.comap π).subtype, IsPGroup.of_card hE'card, hmapE, by rw [hE'card, hk]⟩

end CFSG.ComponentClassification.GrSLit.L34Tw
