module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Normalizer

variable {G : Type} [Group G]

def conjOn (L : Subgroup G) (h : G) (hh : h ∈ normalizer (L : Set G)) : ↥L ≃* ↥L where
  toFun x := ⟨h * x * h⁻¹, (mem_normalizer_iff.mp hh x).mp x.2⟩
  invFun x := ⟨h⁻¹ * x * h, by simpa using (mem_normalizer_iff.mp (inv_mem hh) x).mp x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem le_normalizer_of_characteristic {L H : Subgroup G} (hH : H ≤ normalizer (L : Set G))
    (C : Subgroup ↥L) [C.Characteristic] : H ≤ normalizer ((C.map L.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  have hfwd : ∀ c : ↥L, c ∈ C → (conjOn L h (hH hh) c) ∈ C := by
    intro c hc
    have hfix := Subgroup.characteristic_iff_comap_eq.mp ‹C.Characteristic› (conjOn L h (hH hh))
    have : c ∈ C.comap (conjOn L h (hH hh)).toMonoidHom := by rw [hfix]; exact hc
    exact this
  have hbwd : ∀ c : ↥L, (conjOn L h (hH hh) c) ∈ C → c ∈ C := by
    intro c hc
    have hfix := Subgroup.characteristic_iff_comap_eq.mp ‹C.Characteristic› (conjOn L h (hH hh))
    have : c ∈ C.comap (conjOn L h (hH hh)).toMonoidHom := hc
    rwa [hfix] at this
  intro x
  by_cases hxL : x ∈ L
  · constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨conjOn L h (hH hh) c, hfwd c hc, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : (y : G) = h * x * h⁻¹ := hyx
      have h2 : conjOn L h (hH hh) ⟨x, hxL⟩ = y := by
        apply Subtype.ext
        exact h1.symm
      exact ⟨⟨x, hxL⟩, hbwd _ (h2 ▸ hy), rfl⟩
  · constructor
    · rintro ⟨c, _, rfl⟩
      exact absurd c.2 hxL
    · rintro ⟨y, _, hyx⟩
      apply absurd _ hxL
      have : h * x * h⁻¹ ∈ L := hyx ▸ y.2
      exact (mem_normalizer_iff.mp (hH hh) x).mpr this

theorem le_normalizer_Ep (p : ℕ) (M : Subgroup G) : M ≤ normalizer ((Ep p M : Subgroup G) : Set G) :=
  le_normalizer_of_characteristic (le_normalizer_Fm M) (pPrimeCore p ↥(Fm M))

theorem Ep_le_Fm (p : ℕ) (M : Subgroup G) : Ep p M ≤ Fm M := Subgroup.map_subtype_le _

theorem commutator_eq_bot_of_coprime {M A B : Subgroup G} (hA : M ≤ normalizer (A : Set G))
    (hB : M ≤ normalizer (B : Set G)) (hAM : A ≤ M) (hBM : B ≤ M)
    (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B)) : ⁅A, B⁆ = ⊥ := by
  have hdisj : A ⊓ B = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [eq_bot_iff, ← hdisj, le_inf_iff, Subgroup.commutator_le, Subgroup.commutator_le]
  constructor
  · intro a ha b hb
    have h1 : b⁻¹ * a * b ∈ A := by
      have := (mem_normalizer_iff.mp (hA (hBM (inv_mem hb))) a).mp ha
      simpa using this
    have : ⁅a, b⁆ = (a * (b * a⁻¹ * b⁻¹)) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact A.mul_mem ha (by
      have := (mem_normalizer_iff.mp (hA (hBM hb)) a⁻¹).mp (A.inv_mem ha)
      exact this)
  · intro a ha b hb
    have : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp [commutatorElement_def]
    rw [this]
    exact B.mul_mem ((mem_normalizer_iff.mp (hB (hAM ha)) b).mp hb) (B.inv_mem hb)

end Normalizer

section Fitting

variable {G : Type} [Group G] [Finite G]

theorem commute_Op_Ep (r : ℕ) (hr : r.Prime) (M : Subgroup G) : ⁅Op r M, Ep r M⁆ = ⊥ := by
  refine commutator_eq_bot_of_coprime (le_normalizer_Op r M) (le_normalizer_Ep r M) (Op_le r M)
    ((Ep_le_Fm r M).trans (Fm_le M)) ?_
  have h1 : Nat.card ↥(Ep r M) = Nat.card ↥(pPrimeCore r ↥(Fm M)) :=
    Subgroup.card_map_of_injective (Fm M).subtype_injective
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_Op r hr M)
  rw [hn, h1]
  exact Nat.Coprime.pow_left n (pPrimeCore_coprime_card (p := r) (G := ↥(Fm M)))

end Fitting

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_idem {z : G} (hz : orderOf z = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA : IsPGroup p ↥A) (hn : z ∈ normalizer (A : Set G)) :
    ⁅⁅A, zpowers z⁆, zpowers z⁆ = ⁅A, zpowers z⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime A (zpowers z) ?_
    (Subgroup.zpowers_le.mpr hn)
  obtain ⟨n, hn'⟩ := (IsPGroup.iff_card).mp hA
  rw [Nat.card_zpowers, hz, hn']
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

theorem not_isPGroup_of_twoPrimes {X : Subgroup G} (hX : TwoPrimes X) {q : ℕ} (hq : q.Prime) :
    ¬ IsPGroup q ↥X := by
  intro hP
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have hsub : piOf X ⊆ {q} := by
    intro r hr
    have : r ∣ q ^ n := hn ▸ hr.2
    exact (Nat.prime_dvd_prime_iff_eq hr.1 hq).mp (hr.1.dvd_of_dvd_pow this)
  have : (piOf X).ncard ≤ 1 := by
    calc (piOf X).ncard ≤ ({q} : Set ℕ).ncard := Set.ncard_le_ncard hsub (Set.finite_singleton q)
      _ = 1 := Set.ncard_singleton q
  unfold TwoPrimes at hX
  omega

end Coprime

section Conj

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g w : G} : w ∈ conjugate H g ↔ g * w * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro h
    refine ⟨g * w * g⁻¹, h, ?_⟩
    simp [mul_assoc]

end Conj

end CFSG.GH74.GLS.Stage2.Bender.Thm1
