module

public import CFSG.GH74.GLS.Stage4.T2P71FrC
public import CFSG.GH74.GLS.Stage4.RestX2Q3

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem W_inv (h : T6Ctx N u p) : ∀ r ∈ Wsub N, N.z * r * N.z⁻¹ * r ∈ N.X₂ := by
  refine (t6_inv_mod (R := Wsub N) (X := N.X₂) ?_ Wsub_card_odd h.sec5.loc.z_ord ?_ (W_Cz h)).1
  · intro x hx r hr
    exact Subgroup.mem_centralizer_iff.1 (Wsub_le_C₂ hr) x hx
  · exact Subgroup.mem_normalizer_fintype (fun n hn => Wsub_norm (z_mem_M₂ h) hn)

theorem p71Frattini_core (h : T6Ctx N u p) (h' : T6Ctx N.swap u p)
    (hnotsyl : ¬ ∃ S : Sylow p G, (S : Subgroup G) ≤ Subgroup.centralizer ({N.z} : Set G)) :
    ∃ t ∈ R₂ N p, t ∉ N.X₂ ∧ ∀ x ∈ N.X₁, t * x = x * t := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp := h.prime
  have hz2 := h.ctx.zz
  have hzord : orderOf N.z = 2 := h.sec5.loc.z_ord
  obtain ⟨P, hPC, hPp, hXP, hPc, hmax⟩ := exists_Pmax h
  set A : Subgroup G := Subgroup.centralizer (P : Set G) with hA
  have hlt := Z_lt_sylow h h' hPC hPp hXP hmax hnotsyl
  have hzP : ∀ x ∈ P, N.z * x = x * N.z := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hPC hx)).symm
  have hzA : N.z ∈ A := Subgroup.mem_centralizer_iff.2 (fun x hx => (hzP x hx).symm)
  have hA2 : (Nat.card ↥A).factorization 2 = 1 := A_card2 h h' hXP hzA
  have hTp : IsPGroup 2 ↥(Subgroup.zpowers N.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; norm_num)
  have hTA : Subgroup.zpowers N.z ≤ A := Subgroup.zpowers_le.2 hzA
  have hTidx : ¬ 2 ∣ (Subgroup.zpowers N.z).relIndex A := by
    intro hd
    have := Subgroup.relIndex_mul_card (Subgroup.zpowers N.z) A
    rw [inf_eq_left.2 hTA, Nat.card_zpowers, hzord] at this
    have h4 : 2 ^ 2 ∣ Nat.card ↥A := by
      rw [← this]
      simpa [pow_two] using Nat.mul_dvd_mul hd (dvd_refl 2)
    have h5 := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h4
    omega
  have hab : ∀ a ∈ Subgroup.zpowers N.z, ∀ b ∈ Subgroup.zpowers N.z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self N.z i j).eq
  have hN : ∀ n ∈ A, (∀ t ∈ Subgroup.zpowers N.z, n * t * n⁻¹ ∈ Subgroup.zpowers N.z) →
      Odd (orderOf n) → ∀ t ∈ Subgroup.zpowers N.z, n * t = t * n := by
    intro n hn hnT _ t ht
    have hmem := hnT N.z (Subgroup.mem_zpowers _)
    have hnz : n * N.z * n⁻¹ = N.z := by
      rcases t2C_zpowers_cases hz2 hmem with h1 | h1
      · exfalso
        have : N.z = n⁻¹ * (n * N.z * n⁻¹) * n := by group
        rw [h1] at this
        exact h.ctx.z_ne (by simpa using this)
      · exact h1
    have hc : Commute n N.z := by
      show n * N.z = N.z * n
      calc n * N.z = (n * N.z * n⁻¹) * n := by group
        _ = N.z * n := by rw [hnz]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact (hc.zpow_right k).eq
  obtain ⟨K, hKA, hKn, hKodd, hKcard⟩ :=
    t6_two_complement A (Subgroup.zpowers N.z) hTA hTp hTidx hab hN
  have hKodd' : Odd (Nat.card ↥K) := Nat.odd_iff.2 (by omega)
  obtain ⟨Q, hQK, hQp, hQc, hQz⟩ := t6_exists_invariant_sylow hTp hKodd'
    (fun g hg k hk => hKn g (hTA hg) k hk) hp
  have hQcard : Nat.card ↥Q = p ^ (Nat.card ↥A).factorization p := by
    rw [hQc]
    congr 1
    have h2p : (Nat.factorization 2) p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      exact h.p_ne_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd))
    rw [hKcard, Nat.card_zpowers, hzord, Nat.factorization_mul Nat.card_pos.ne' (by norm_num),
      Finsupp.add_apply, h2p]
    simp
  have hQA : Q ≤ A := hQK.trans hKA
  have hQB : Q ≤ Subgroup.normalizer (P : Set G) := hQA.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hex : ∃ q ∈ Q, N.z * q * N.z⁻¹ * q⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hQC : Q ≤ Subgroup.centralizer ({N.z} : Set G) := by
      intro q hq
      have h1 := hcon q hq
      have h2 : N.z * q * N.z⁻¹ = q := by
        calc N.z * q * N.z⁻¹ = (N.z * q * N.z⁻¹ * q⁻¹) * q := by group
          _ = q := by rw [h1, one_mul]
      have h3 : q * N.z = N.z * q := by
        calc q * N.z = (N.z * q * N.z⁻¹) * N.z := by rw [h2]
          _ = N.z * q := by group
      exact Subgroup.mem_centralizer_singleton_iff.2 h3
    have hPQp : IsPGroup p ↥(Q ⊔ P) := hQp.to_sup_of_normal_right' hPp hQB
    have hle := hmax (Q ⊔ P) (sup_le hQC hPC) hPQp
    have hPeq : P = Q ⊔ P := Subgroup.eq_of_le_of_card_ge (le_sup_right) hle
    have hQP : Q ≤ P := by rw [hPeq]; exact le_sup_left
    have hle2 : Nat.card ↥Q ≤ Nat.card ↥(P ⊓ A) := Subgroup.card_le_of_le (le_inf hQP hQA)
    rw [hQcard] at hle2
    exact absurd hlt (not_lt.2 hle2)
  obtain ⟨q, hq, hqt⟩ := hex
  set t : G := N.z * q * N.z⁻¹ * q⁻¹ with ht
  have hzQ := hQz N.z (Subgroup.mem_zpowers _) q hq
  have htQ : t ∈ Q := Q.mul_mem hzQ (Q.inv_mem hq)
  have htA : t ∈ A := hQA htQ
  have htc : ∀ x ∈ P, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 htA x hx).symm
  have hqC₂ : q ∈ C₂ N := by
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hQA hq) x (hXP (Subgroup.mem_sup_right hx))).symm.symm
  obtain ⟨c', hc'C, k, hk, hqck, hc'z⟩ := Zstar_C₂ h q hqC₂
  have hzM := z_mem_M₂ h
  have hc'M : c' ∈ M₂ N := C₂_le_M₂ hc'C
  have hzc' : N.z * c' * N.z⁻¹ = c' := by
    calc N.z * c' * N.z⁻¹ = (c' * N.z) * N.z⁻¹ := by rw [hc'z]
      _ = c' := by group
  have htW : t ∈ Wsub N := by
    have e : t = c' * (N.z * k * N.z⁻¹ * k⁻¹) * c'⁻¹ := by
      rw [ht, hqck]
      calc N.z * (c' * k) * N.z⁻¹ * (c' * k)⁻¹
          = (N.z * c' * N.z⁻¹) * (N.z * k * N.z⁻¹) * k⁻¹ * c'⁻¹ := by group
        _ = c' * (N.z * k * N.z⁻¹ * k⁻¹) * c'⁻¹ := by rw [hzc']; group
    rw [e]
    have h1 : N.z * k * N.z⁻¹ ∈ Wsub N := Wsub_norm hzM hk
    have h2 : N.z * k * N.z⁻¹ * k⁻¹ ∈ Wsub N := (Wsub N).mul_mem h1 ((Wsub N).inv_mem hk)
    exact Wsub_norm hc'M h2
  have htp : IsPGroup p ↥(Subgroup.zpowers t) := by
    intro g
    obtain ⟨j, hj⟩ := hQp ⟨t, htQ⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨j, ?_⟩
    apply Subtype.ext
    show (g : G) ^ (p ^ j) = 1
    have ht1 : t ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht1, one_zpow]
  have htC₂ : Subgroup.zpowers t ≤ C₂ N := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    exact (htc x (hXP (Subgroup.mem_sup_right hx))).symm
  have hWz : Subgroup.zpowers t ≤ Wsub N := Subgroup.zpowers_le.2 htW
  have htR : Subgroup.zpowers t ≤ R₂ N p :=
    R_le_R₂' h htp htC₂ (fun r hr => W_inv h r (hWz hr))
  refine ⟨t, htR (Subgroup.mem_zpowers t), ?_, fun x hx => htc x (hXP (Subgroup.mem_sup_left hx))⟩
  intro htX
  have hz' : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  have hzt : N.z * t * N.z⁻¹ = t⁻¹ := by
    have e1 : N.z * t * N.z⁻¹ = (N.z * N.z) * q * N.z⁻¹ * q⁻¹ * N.z⁻¹ := by rw [ht]; group
    have e2 : t⁻¹ = q * N.z * q⁻¹ * N.z⁻¹ := by rw [ht]; group
    rw [e1, e2, hz2, one_mul, hz']
  have hzcX := z_cent_X₂ h htX
  have hzt' : N.z * t * N.z⁻¹ = t := by
    calc N.z * t * N.z⁻¹ = (t * N.z) * N.z⁻¹ := by rw [← hzcX]
      _ = t := by group
  have hsq : t * t = 1 := by
    have : t = t⁻¹ := by rw [← hzt, hzt']
    calc t * t = t * t⁻¹ := by rw [← this]
      _ = 1 := by group
  have hodd := t6_odd_of_pGroup hp h.p_ne_two hQp htQ
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
  · exact hqt (orderOf_eq_one_iff.1 h4)
  · rw [h4] at hodd; exact absurd hodd (by decide)

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
