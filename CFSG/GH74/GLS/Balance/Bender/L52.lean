module

public import CFSG.GH74.GLS.Balance.Bender.Aux1
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.GH74.GLS.Balance.PStarComp

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance.BenderExt
open scoped commutatorElement

theorem commute_of_mem_conjugate {H : Type*} [Group H] {A : Subgroup H} (g : H)
    (hA : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s) :
    ∀ x ∈ conjugate A g, ∀ y ∈ conjugate A g, x * y = y * x := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [← map_mul, ← map_mul, hA s hs t ht]

theorem bender_l52iii (p : ℕ) [Fact p.Prime] : BenderL52iii p := by
  intro H _ _ K hK hK1 hmin
  have hp : p.Prime := Fact.out
  have hcn : (⁅K, K⁆).Normal := inferInstance
  have hcle : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_left (H₁ := K) (H₂ := K)
  rcases hmin ⁅K, K⁆ hcle hcn with h | h
  ·
    have hcomm : K ≤ centralizer (K : Set H) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := K)).mp h
    have : IsMulCommutative K := (Subgroup.le_centralizer_iff_isMulCommutative (K := K)).mp hcomm
    have : Group.IsSolvable ↥K := inferInstance
    have : CFSG.IsMinimalNormal K := ⟨fun M _ hMK => hmin M hMK inferInstance⟩
    obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian K
    have hpow : ∀ y : K, y ^ q = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p
    have hcop : Nat.Coprime p (Nat.card ↥(oResidual p ↥K)) := by
      by_cases hqp : q = p
      · subst hqp
        have hbot : oResidual q ↥K = ⊥ := by
          refine le_bot_iff.mp ?_
          unfold oResidual
          rw [Subgroup.closure_le]
          intro y hy
          have hy' : Nat.Coprime (orderOf y) q := hy
          have hdvd : orderOf y ∣ q := orderOf_dvd_of_pow_eq_one (hpow y)
          have : orderOf y = 1 := Nat.Coprime.eq_one_of_dvd hy' hdvd
          show y = 1
          exact orderOf_eq_one_iff.mp this
        rw [hbot]
        simp
      · have hKp : IsPGroup q ↥K := fun g => ⟨1, by rw [pow_one]; exact hpow g⟩
        have : Fact q.Prime := ⟨hq⟩
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hKp)
        have h1 : Nat.Coprime p (q ^ n) :=
          Nat.Coprime.pow_right n ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
        exact Nat.Coprime.coprime_dvd_right
          (hn ▸ Subgroup.card_subgroup_dvd_card (oResidual p ↥K)) h1
    exact bender_l52i p _ hcop
  ·
    have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr h
    have htop : oResidual p ↥K = ⊤ := oResidual_eq_top_of_isPerfect hperf
    obtain ⟨r, S, hr, hSK, hSimple, hconj, hSnorm, e, he⟩ :=
      CFSG.LocalCores.minimal_normal_simple_factors hK hK1 (fun M hM hle => hmin M hle hM)
    have hS : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      obtain ⟨i₀, hi₀⟩ := hcon
      have hcomm_i0 : ∀ s ∈ S i₀, ∀ t ∈ S i₀, s * t = t * s := fun s hs t ht =>
        congrArg Subtype.val (hi₀ ⟨s, hs⟩ ⟨t, ht⟩)
      have hcomm_all : ∀ j, ∀ a b : S j, a * b = b * a := by
        intro j a b
        obtain ⟨g, hg⟩ := hconj i₀ j
        apply Subtype.ext
        have h1 := commute_of_mem_conjugate g hcomm_i0
        have ha : (a : H) ∈ conjugate (S i₀) g := hg ▸ a.2
        have hb : (b : H) ∈ conjugate (S i₀) g := hg ▸ b.2
        exact h1 a ha b hb
      have hKcomm : ∀ x y : ↥K, x * y = y * x := by
        intro x y
        obtain ⟨a, rfl⟩ := e.surjective x
        obtain ⟨b, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        funext j
        exact hcomm_all j (a j) (b j)
      have hKbot : ⁅K, K⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (hKcomm ⟨y, hy⟩ ⟨x, hx⟩)
      exact hK1 (by rw [← h]; exact hKbot)
    have : ∀ i, IsSimpleGroup ↥(S i) := hSimple
    have hlayer : layer ↥K = ⊤ :=
      CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Fin r) (S := fun i => ↥(S i)) hS e.symm
    have hK_p : IsPStar p ↥K := by
      have h1 : IsPStar p ↥(layer ↥K) := isPStar_layer_general (X := ↥K)
      rw [hlayer] at h1
      exact IsPStar.of_mulEquiv (Subgroup.topEquiv (G := ↥K)) h1
    rw [htop]
    exact IsPStar.of_mulEquiv (Subgroup.topEquiv (G := ↥K)).symm hK_p

end CFSG.GH74.GLS.Balance
