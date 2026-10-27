module

public import CFSG.GroupTheory.GLS2.NumberTheory.PrimeSupport
public import CFSG.GroupTheory.GLS2.GroupTheory.PiComponents
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.SecondGeneration

variable {G : Type*} [Group G]

theorem exists_primeSupported_preimage_of_surjective
    {H : Type*} [Group H] [Finite G] (π : Set ℕ)
    (f : G →* H) (hf : Function.Surjective f) {y : H}
    (hy : primeSupported π (orderOf y)) :
    ∃ x : G, primeSupported π (orderOf x) ∧ f x = y := by
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨a, b, hab, _, ha, hb⟩ :=
    exists_mul_primeSupported_compl πᶜ (orderOf_pos x)
  have horder : orderOf (x ^ a) ∣ b := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hab, pow_orderOf_eq_one]
  have hb' : primeSupported π b := by simpa using hb
  have hx : primeSupported π (orderOf (x ^ a)) :=
    fun q hq hqd => hb' q hq (dvd_trans hqd horder)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime
    (coprime_of_primeSupported_compl ha (by simpa using hy))
  refine ⟨(x ^ a) ^ k, ?_, ?_⟩
  · exact fun q hq hqd => hx q hq (dvd_trans hqd (orderOf_pow_dvd k))
  · simpa only [map_pow] using hk

theorem closure_primeSupported_compl_characteristic (π : Set ℕ) :
    (Subgroup.closure {x : G | primeSupported πᶜ (orderOf x)}).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun e => ?_
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change primeSupported πᶜ (orderOf (e y))
    simpa only [Set.mem_setOf_eq, e.orderOf_eq] using hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change primeSupported πᶜ (orderOf (e.symm x))
    simpa only [Set.mem_setOf_eq, e.symm.orderOf_eq] using hx

theorem exists_primeSupported_pow_mem_closure
    [Finite G] (π : Set ℕ) (x : G) :
    ∃ m : ℕ, 0 < m ∧ primeSupported π m ∧
      x ^ m ∈ Subgroup.closure {y : G | primeSupported πᶜ (orderOf y)} := by
  obtain ⟨a, b, hab, ha, hπ, hπ'⟩ := exists_mul_primeSupported_compl π (orderOf_pos x)
  have horder : orderOf (x ^ a) ∣ b := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← hab, pow_orderOf_eq_one]
  refine ⟨a, ha, hπ, Subgroup.subset_closure ?_⟩
  exact fun q hq hqorder => hπ' q hq (dvd_trans hqorder horder)

theorem closure_primeSupported_compl_le_iff
    [Finite G] (π : Set ℕ) (N : Subgroup G) :
    Subgroup.closure {x : G | primeSupported πᶜ (orderOf x)} ≤ N ↔
      ∀ x : G, ∃ m : ℕ, 0 < m ∧ primeSupported π m ∧ x ^ m ∈ N := by
  constructor
  · intro h x
    obtain ⟨m, hm, hπ, hxm⟩ := exists_primeSupported_pow_mem_closure π x
    exact ⟨m, hm, hπ, h hxm⟩
  · intro h
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨m, _, hπ, hxm⟩ := h x
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (coprime_of_primeSupported_compl hπ hx)
    rw [← hk]
    exact N.pow_mem hxm k

theorem closure_primeSupported_compl_eq_iInf
    [Finite G] (π : Set ℕ) :
    Subgroup.closure {x : G | primeSupported πᶜ (orderOf x)} =
      ⨅ (N : Subgroup G) (_ : N.Normal ∧
        ∀ x : G, ∃ m : ℕ, 0 < m ∧ primeSupported π m ∧ x ^ m ∈ N), N := by
  let R := Subgroup.closure {x : G | primeSupported πᶜ (orderOf x)}
  let : R.Characteristic := closure_primeSupported_compl_characteristic π
  apply le_antisymm
  · refine le_iInf fun N => le_iInf fun hN => ?_
    exact (closure_primeSupported_compl_le_iff π N).mpr hN.2
  · exact iInf_le_of_le R (iInf_le _
      ⟨inferInstance, fun x => exists_primeSupported_pow_mem_closure π x⟩)

theorem piResidual_eq_closure_primeSupported_compl (π : Set Nat.Primes) [Finite G] :
    piResidual π G =
      Subgroup.closure {x : G | ∀ q : Nat.Primes, q.val ∣ orderOf x → q ∉ π} := by
  have hsupport (m : ℕ) :
      primeSupported (Subtype.val '' π) m ↔
        ∀ q : Nat.Primes, q.val ∣ m → q ∈ π := by
    constructor
    · intro hm q hqm
      obtain ⟨r, hr, hrq⟩ := hm q.val q.property hqm
      have heq : r = q := Subtype.ext hrq
      exact heq ▸ hr
    · intro hm q hq hqm
      exact ⟨⟨q, hq⟩, hm ⟨q, hq⟩ hqm, rfl⟩
  have hgenerators :
      {x : G | primeSupported (Subtype.val '' π)ᶜ (orderOf x)} =
        {x : G | ∀ q : Nat.Primes, q.val ∣ orderOf x → q ∉ π} := by
    ext x
    constructor
    · intro hx q hq hqπ
      exact hx q.val q.property hq ⟨q, hqπ, rfl⟩
    · intro hx q _ hqorder
      rintro ⟨r, hr, hrq⟩
      exact hx r (hrq.symm ▸ hqorder) hr
  calc
    piResidual π G =
        ⨅ (N : Subgroup G) (_ : N.Normal ∧
          ∀ x : G, ∃ m : ℕ, 0 < m ∧
            primeSupported (Subtype.val '' π) m ∧ x ^ m ∈ N), N := by
      simp_rw [piResidual, hsupport]
    _ = Subgroup.closure {x : G | primeSupported (Subtype.val '' π)ᶜ (orderOf x)} :=
      (closure_primeSupported_compl_eq_iInf (Subtype.val '' π)).symm
    _ = _ := congrArg Subgroup.closure hgenerators

theorem map_piResidual_le
    {H : Type*} [Group H] [Finite G] [Finite H]
    (π : Set Nat.Primes) (f : G →* H) :
    (piResidual π G).map f ≤ piResidual π H := by
  rw [piResidual_eq_closure_primeSupported_compl,
    piResidual_eq_closure_primeSupported_compl, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨x, hx, rfl⟩ q hq
  exact hx q (dvd_trans hq (orderOf_map_dvd f x))

theorem map_piResidual_eq_of_surjective
    {H : Type*} [Group H] [Finite G] [Finite H]
    (π : Set Nat.Primes) (f : G →* H) (hf : Function.Surjective f) :
    (piResidual π G).map f = piResidual π H := by
  apply le_antisymm (map_piResidual_le π f)
  rw [piResidual_eq_closure_primeSupported_compl, Subgroup.closure_le]
  intro y hy
  have hySupport : primeSupported (Subtype.val '' π)ᶜ (orderOf y) := by
    intro q hq hqd
    rintro ⟨r, hr, hrq⟩
    exact hy r (hrq.symm ▸ hqd) hr
  obtain ⟨x, hx, rfl⟩ :=
    exists_primeSupported_preimage_of_surjective (Subtype.val '' π)ᶜ f hf hySupport
  refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
  rw [piResidual_eq_closure_primeSupported_compl]
  apply Subgroup.subset_closure
  intro q hqd hqπ
  exact hx q.val q.property hqd ⟨q, hqπ, rfl⟩

instance piResidual_characteristic [Finite G] (π : Set Nat.Primes) :
    (piResidual π G).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun e =>
    map_piResidual_eq_of_surjective π e.toMonoidHom e.surjective

instance piResidual_normal [Finite G] (π : Set Nat.Primes) :
    (piResidual π G).Normal := inferInstance

theorem oPrimeResidual_eq_piResidual_compl_singleton
    [Finite G] (p : Nat.Primes) :
    GH74.GLS.oPrimeResidual p.val G = piResidual ({p} : Set Nat.Primes)ᶜ G := by
  rw [piResidual_eq_closure_primeSupported_compl]
  unfold GH74.GLS.oPrimeResidual
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
  constructor
  · rintro ⟨k, hk⟩ q hq
    apply Subtype.ext
    exact Nat.prime_eq_prime_of_dvd_pow q.property p.property
      (hq.trans (orderOf_dvd_of_pow_eq_one hk))
  · intro hx
    have hpow : orderOf x = p.val ^ (orderOf x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos x).ne'
        fun hq hd => congrArg Subtype.val (hx ⟨_, hq⟩ hd)
    exact ⟨(orderOf x).primeFactorsList.length, by rw [← hpow, pow_orderOf_eq_one]⟩

theorem map_oPrimeResidualOf_eq
    {H : Type*} [Group H] [Finite G] [Finite H] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (X : Subgroup G) :
    (GH74.GLS.oPrimeResidualOf p X).map f = GH74.GLS.oPrimeResidualOf p (X.map f) := by
  let r : Nat.Primes := ⟨p, Fact.out⟩
  let φ : X →* X.map f := f.subgroupMap X
  have hmap := map_piResidual_eq_of_surjective ({r} : Set Nat.Primes)ᶜ φ
    (f.subgroupMap_surjective X)
  rw [← oPrimeResidual_eq_piResidual_compl_singleton r,
    ← oPrimeResidual_eq_piResidual_compl_singleton r] at hmap
  calc
    (GH74.GLS.oPrimeResidualOf p X).map f =
        ((GH74.GLS.oPrimeResidual p X).map φ).map (X.map f).subtype := by
      simp only [GH74.GLS.oPrimeResidualOf, Subgroup.map_map]
      rfl
    _ = GH74.GLS.oPrimeResidualOf p (X.map f) := by rw [hmap]; rfl

end CFSG.SecondGeneration
