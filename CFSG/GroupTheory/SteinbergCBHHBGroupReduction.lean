module

public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.SteinbergCBHHBMinimalConfig
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Subgroup CFSG.LocalCores CFSG.HallHigman

theorem isPiSeparable_compl {π : Set Nat.Primes} {X : Type*} [Group X]
    (hX : IsPiSeparable π X) : IsPiSeparable πᶜ X := by
  intro H hH T _ hs
  rcases hX H hH T hs with h | h
  · exact Or.inr fun q hq hqc => hqc (h q hq)
  · exact Or.inl fun q hq => h q hq

theorem eq_top_of_forall_prime_sylow_le {M : Type*} [Group M] [Finite M] (H : Subgroup M)
    (h : ∀ q : ℕ, q.Prime → ∃ S : Sylow q M, (S : Subgroup M) ≤ H) : H = ⊤ := by
  classical
  have hcardM : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hcardH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hdvd : Nat.card M ∣ Nat.card H := by
    rw [← Nat.factorization_le_iff_dvd hcardM hcardH]
    intro q
    by_cases hq : q.Prime
    · have : Fact q.Prime := ⟨hq⟩
      obtain ⟨S, hS⟩ := h q hq
      have h1 : Nat.card S ∣ Nat.card H := Subgroup.card_dvd_of_le hS
      rw [Sylow.card_eq_multiplicity] at h1
      exact (hq.pow_dvd_iff_le_factorization hcardH).1 h1
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  exact Subgroup.eq_top_of_card_eq H (le_antisymm (Subgroup.card_le_card_group H)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hcardH) hdvd))

theorem exists_invariant_qsubgroup_not_centralized {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : IsPSolvable p X)
    (hO : CFSG.piCore {q : Nat.Primes | q.val = p} X = ⊥) (x : X) {n : ℕ} (hn : 1 ≤ n)
    (hx : orderOf x = p ^ n) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ ∃ S : Subgroup X, IsPGroup q S ∧
      x ∈ normalizer (S : Set X) ∧ ∃ a ∈ S, x ^ (p ^ (n - 1)) * a ≠ a * x ^ (p ^ (n - 1)) := by
  classical
  set π : Set Nat.Primes := {q | q.val ≠ p} with hπ
  set N := CFSG.piCore π X with hNdef
  have hπc : πᶜ = {q : Nat.Primes | q.val = p} := by
    ext q
    simp [hπ]
  have hsep : IsPiSeparable π X := by
    have h1 := isPiSeparable_compl (isPiSeparable_of_isPSolvable hp.out hX)
    have h2 : ({q : Nat.Primes | q.val = p}ᶜ : Set Nat.Primes) = π := by
      ext q
      simp [hπ]
    rwa [h2] at h1
  have hcent : centralizer (N : Set X) ≤ N :=
    centralizer_piCore_le_piCore hsep (by rw [hπc]; exact hO)
  have hNpi := piCore_isPiSubgroup (G := X) π
  set z := x ^ (p ^ (n - 1)) with hzdef
  have hzord : orderOf z = p := by
    rw [hzdef, orderOf_pow' x (pow_ne_zero _ hp.out.ne_zero), hx]
    have h1 : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [h1, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _)]
  have hpN : ¬ p ∣ Nat.card N := by
    intro h
    exact hNpi ⟨p, hp.out⟩ h rfl
  have hzN : z ∉ N := by
    intro hz
    apply hpN
    have := orderOf_dvd_natCard (⟨z, hz⟩ : N)
    rwa [Subgroup.orderOf_mk, hzord] at this
  obtain ⟨a, haN, hza⟩ : ∃ a ∈ N, z * a ≠ a * z := by
    by_contra hcon
    push Not at hcon
    exact hzN (hcent (mem_centralizer_iff.2 fun a ha => (hcon a ha).symm))
  have hxN : x ∈ normalizer (N : Set X) := by
    have : N.Normal := (prime_set_core_normal π).2
    rw [normalizer_eq_top]
    exact mem_top x
  let _ := conjZpowers N x hxN
  have hsmul : ∀ (u : zpowers x) (g : N), ((u • g : N) : X) = (u : X) * g * (u : X)⁻¹ :=
    fun _ _ => rfl
  have hApg : IsPGroup p (zpowers x) := IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hx])
  have hcop : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpN
  by_contra hcon
  push Not at hcon
  apply hza
  have hsyl : ∀ q : ℕ, q.Prime → ∃ T : Sylow q N, ∀ t ∈ (T : Subgroup N), z * t = t * z := by
    intro q hq
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨T, -, hTinv⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p q hp.out
      hq hApg hcop (⊥ : Subgroup N) (IsPGroup.of_bot) (fun u g hg => by
        rw [mem_bot] at hg ⊢
        rw [hg, smul_one])
    refine ⟨T, fun t ht => ?_⟩
    set S := (T : Subgroup N).map N.subtype with hSdef
    have hmemS : ∀ (u : zpowers x) (g : N), g ∈ (T : Subgroup N) → u • g ∈ (T : Subgroup N) := by
      intro u g hg
      have h1 := Subgroup.smul_mem_pointwise_smul g u (T : Subgroup N) hg
      rw [← Sylow.pointwise_smul_def, hTinv u] at h1
      exact h1
    have hxS : x ∈ normalizer (S : Set X) := by
      rw [mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨g', hg', rfl⟩
        exact ⟨_, hmemS ⟨x, mem_zpowers x⟩ g' hg', rfl⟩
      · rintro ⟨g', hg', hgg'⟩
        refine ⟨_, hmemS ⟨x⁻¹, inv_mem (mem_zpowers x)⟩ g' hg', ?_⟩
        rw [Subgroup.coe_subtype, hsmul]
        change x⁻¹ * (g' : X) * x⁻¹⁻¹ = g
        rw [show (g' : X) = x * g * x⁻¹ from hgg']
        group
    by_cases hqp : q = p
    ·
      subst hqp
      have hT1 : t = 1 := by
        have h1 : orderOf t ∣ Nat.card N := orderOf_dvd_natCard t
        obtain ⟨k, hk⟩ := (T.isPGroup' ⟨t, ht⟩)
        have h2 : orderOf t ∣ q ^ k := by
          rw [← Subgroup.orderOf_mk t ht]
          exact orderOf_dvd_of_pow_eq_one hk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 h2
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · rw [hj0, pow_zero] at hj
          exact orderOf_eq_one_iff.1 hj
        · exfalso
          apply hpN
          rw [hj] at h1
          exact (dvd_pow_self q (by omega)).trans h1
      rw [hT1]
      simp
    · have hSq : IsPGroup q S := (T.isPGroup').map N.subtype
      have := hcon q hq hqp S hSq hxS (t : X) ⟨t, ht, rfl⟩
      exact this
  have hH : (centralizer ({z} : Set X)).comap N.subtype = ⊤ := by
    refine eq_top_of_forall_prime_sylow_le _ fun q hq => ?_
    obtain ⟨T, hT⟩ := hsyl q hq
    refine ⟨T, fun t ht => ?_⟩
    rw [mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff]
    exact (hT t ht).symm
  have hamem : (⟨a, haN⟩ : N) ∈ (centralizer ({z} : Set X)).comap N.subtype := by
    rw [hH]
    exact mem_top _
  rw [mem_comap, Subgroup.coe_subtype, mem_centralizer_singleton_iff] at hamem
  exact hamem.symm

end CFSG.GroupTheory.HallHigmanB
