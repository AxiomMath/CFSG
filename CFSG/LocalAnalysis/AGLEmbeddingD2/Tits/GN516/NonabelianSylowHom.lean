module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

theorem hom_eq_one_of_abelian_two_subgroups
    {A Γ : Type*} [Group A] [Finite A] [Group Γ]
    (hperf : commutator A = ⊤) (hsimple : IsSimpleGroup (A ⧸ Subgroup.center A))
    (hodd : ∀ z ∈ Subgroup.center A, Odd (orderOf z))
    (P : Subgroup A) (hP : IsPGroup 2 P) (hnon : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (ψ : A →* Γ)
    (hab : ∀ Q : Subgroup Γ, IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    ∀ x, ψ x = 1 := by
  by_cases hc : ψ.ker ≤ Subgroup.center A
  · exfalso
    obtain ⟨a, ha, b, hb, hne⟩ := hnon
    apply hne
    have h1 := hab (P.map ψ) (hP.map ψ) (ψ a) ⟨a, ha, rfl⟩ (ψ b) ⟨b, hb, rfl⟩
    set c : A := a * b * a⁻¹ * b⁻¹ with hcdef
    have hcP : c ∈ P := P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    have hcK : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have hcZ : c ∈ Subgroup.center A := hc hcK
    obtain ⟨k, hk⟩ := hP ⟨c, hcP⟩
    have hk' : c ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hord : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hodd' := hodd c hcZ
    have h2 : orderOf c = 1 := by
      obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [hj', h0]; rfl
      · exfalso
        rw [hj'] at hodd'
        exact (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩)) hodd'
    have hc1 : c = 1 := orderOf_eq_one_iff.1 h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [← hcdef, hc1, one_mul]
  ·
    have hKn : ψ.ker.Normal := inferInstance
    obtain ⟨k, hkK, hkZ⟩ := Set.not_subset.1 hc
    let q := QuotientGroup.mk' (Subgroup.center A)
    have hnb : ψ.ker.map q ≠ ⊥ := by
      intro h
      apply hkZ
      have : q k ∈ ψ.ker.map q := ⟨k, hkK, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff k).1 this
    have htop : ψ.ker.map q = ⊤ := by
      have : (ψ.ker.map q).Normal := Subgroup.Normal.map hKn q (QuotientGroup.mk'_surjective _)
      exact (hsimple.eq_bot_or_eq_top_of_normal (ψ.ker.map q)).resolve_left hnb
    have hdecomp : ∀ x : A, ∃ z ∈ Subgroup.center A, ψ x = ψ z := by
      intro x
      have : q x ∈ ψ.ker.map q := htop ▸ Subgroup.mem_top _
      obtain ⟨k', hk', hkq⟩ := this
      have hz : k'⁻¹ * x ∈ Subgroup.center A := (QuotientGroup.eq.1 hkq)
      refine ⟨k'⁻¹ * x, hz, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk', inv_one, one_mul]
    have hcomm : commutator A ≤ ψ.ker := by
      rw [commutator_def]
      refine Subgroup.closure_le _ |>.2 ?_
      rintro _ ⟨x, -, y, -, rfl⟩
      obtain ⟨z1, hz1, e1⟩ := hdecomp x
      obtain ⟨z2, hz2, e2⟩ := hdecomp y
      have hc12 : z1 * z2 = z2 * z1 := (Subgroup.mem_center_iff.1 hz2 z1)
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, e1, e2,
        ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 hc12, map_one]
    intro x
    exact MonoidHom.mem_ker.1 (hcomm (hperf ▸ Subgroup.mem_top x))

end CFSG.AGLEmbeddingD2.Tits.GN516
