module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathBound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem pow_four_eq_one_of_wreath {K : Type*} [Group K] [Finite K] {z : K} (hz : z * z = 1)
    {N₁ N₂ : Subgroup (K ⧸ fusionOddCore K)}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : Disjoint N₁ N₂) (hN : (N₁ ⊔ N₂).Normal)
    (hidx : (N₁ ⊔ N₂).index = 2)
    (hconj : N₁.map (MulAut.conj (QuotientGroup.mk z : K ⧸ fusionOddCore K)).toMonoidHom = N₂)
    (hF₁ : ∀ P : Subgroup (K ⧸ fusionOddCore K), P ≤ N₁ → Nat.card P = 8 → ∀ a ∈ N₁,
      (∀ x ∈ P, a * x = x * a) → a * a = 1)
    (hF₂ : ∀ P : Subgroup (K ⧸ fusionOddCore K), P ≤ N₂ → Nat.card P = 8 → ∀ a ∈ N₂,
      (∀ x ∈ P, a * x = x * a) → a * a = 1)
    {D : Subgroup K} (hD2 : ∀ d ∈ D, ∃ k : ℕ, orderOf d = 2 ^ k) (hD8 : Nat.card D = 8)
    (hDz : ∀ d ∈ D, d * z = z * d)
    (hDN : ∀ d ∈ D, (QuotientGroup.mk d : K ⧸ fusionOddCore K) ∈ N₁ ⊔ N₂)
    {u : K} (hu : ∃ k : ℕ, orderOf u = 2 ^ k) (huD : ∀ d ∈ D, u * d = d * u) : u ^ 4 = 1 := by
  set O := fusionOddCore K with hO
  have hOodd : Odd (Nat.card O) := odd_natCard_fusionOddCore K
  have key : ∀ g : K, g ∈ O → (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1 := by
    intro g hg hk
    obtain ⟨k, hk⟩ := hk
    have h1 : orderOf g ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hg
    have hodd : Odd (orderOf g) := Odd.of_dvd_nat hOodd h1
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra hk0
      have : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, hk0⟩)
      exact (Nat.not_even_iff_odd.2 hodd) this
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  let πD : D →* K ⧸ O := (QuotientGroup.mk' O).comp D.subtype
  have hinj : Function.Injective πD := by
    rw [injective_iff_map_eq_one]
    intro d hd1
    have hdO : (d : K) ∈ O := (QuotientGroup.eq_one_iff _).1 hd1
    exact Subtype.ext (key d hdO (hD2 d d.2))
  have hDbar8 : Nat.card πD.range = 8 := by
    rw [← hD8]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hmemD : ∀ x ∈ πD.range, ∃ d ∈ D, (QuotientGroup.mk d : K ⧸ O) = x := by
    rintro _ ⟨d, rfl⟩
    exact ⟨d, d.2, rfl⟩
  set σ : K ⧸ O := QuotientGroup.mk z with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← QuotientGroup.mk_mul, hz, QuotientGroup.mk_one]
  have hDbarN : πD.range ≤ N₁ ⊔ N₂ := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := hmemD x hx
    exact hDN d hd
  have hDbarσ : ∀ x ∈ πD.range, σ * x * σ⁻¹ = x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := hmemD x hx
    have : z * d * z⁻¹ = d := by
      have := hDz d hd
      calc z * d * z⁻¹ = (d * z) * z⁻¹ := by rw [← this]
        _ = d := by group
    rw [hσdef, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  set u' : K ⧸ O := QuotientGroup.mk (u ^ 2) with hu'def
  have hu'N : u' ∈ N₁ ⊔ N₂ := by
    have := Subgroup.pow_index_mem (N₁ ⊔ N₂) (QuotientGroup.mk u : K ⧸ O)
    rw [hidx, ← QuotientGroup.mk_pow] at this
    exact this
  have hu'D : ∀ x ∈ πD.range, u' * x = x * u' := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := hmemD x hx
    rw [hu'def, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have h1 := huD d hd
    calc u ^ 2 * d = u * (u * d) := by rw [pow_two, mul_assoc]
      _ = u * (d * u) := by rw [h1]
      _ = (u * d) * u := by rw [mul_assoc]
      _ = (d * u) * u := by rw [h1]
      _ = d * u ^ 2 := by rw [pow_two, mul_assoc]
  have hsq := wreath_sq_eq_one (Y := K ⧸ O) (N₁ := N₁) (N₂ := N₂) (σ := σ)
    (fun b hb => mem_centralizer_iff.2 fun a ha => hc a ha b hb) hd hσ2 hconj hF₁ hF₂ πD.range
    hDbar8 hDbarN hDbarσ hu'N hu'D
  have hu4 : u ^ 4 ∈ O := by
    rw [← QuotientGroup.eq_one_iff, show u ^ 4 = u ^ 2 * u ^ 2 by rw [← pow_add],
      QuotientGroup.mk_mul]
    exact hsq
  apply key _ hu4
  obtain ⟨k, hk⟩ := hu
  have h1 : orderOf (u ^ 4) ∣ 2 ^ k := hk ▸ orderOf_pow_dvd 4
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨j, hj⟩


theorem perm_six_pow_sixty (σ : Equiv.Perm (Fin 6)) : σ ^ 60 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType]
  rw [Multiset.lcm_dvd]
  intro p hp
  have h1 := Equiv.Perm.two_le_of_mem_cycleType hp
  have h2 := Equiv.Perm.le_card_support_of_mem_cycleType hp
  have h3 : σ.support.card ≤ 6 := by simpa using Finset.card_le_univ σ.support
  have h4 : p ≤ 6 := by omega
  interval_cases p <;> norm_num

theorem a6_pow_four_of_pow_eight (a : alternatingGroup (Fin 6)) (h : a ^ 8 = 1) : a ^ 4 = 1 := by
  have h60 : a ^ 60 = 1 := Subtype.ext (by simpa using perm_six_pow_sixty (a : Equiv.Perm (Fin 6)))
  have := (pow_gcd_eq_one (a := a) (m := 8) (n := 60)).2 ⟨h, h60⟩
  simpa using this

theorem eq_one_of_mem_fusionOddCore {K : Type*} [Group K] [Finite K] {g : K}
    (hg : g ∈ fusionOddCore K) (hk : ∃ k : ℕ, orderOf g = 2 ^ k) : g = 1 := by
  obtain ⟨k, hk⟩ := hk
  have h1 : orderOf g ∣ Nat.card (fusionOddCore K) := Subgroup.orderOf_dvd_natCard _ hg
  have hodd : Odd (orderOf g) := Odd.of_dvd_nat (odd_natCard_fusionOddCore K) h1
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.1 hk

theorem no_element_of_order_eight {K : Type*} [Group K] [Finite K] {z : K} (hz2 : z * z = 1)
    (hL64 : Lemma64Conclusion K (QuotientGroup.mk z))
    (hA6 : ∀ N : Subgroup (K ⧸ fusionOddCore K), Nonempty (↥N ≃* alternatingGroup (Fin 6)) →
      ∀ P : Subgroup (K ⧸ fusionOddCore K), P ≤ N → Nat.card P = 8 → ∀ a ∈ N,
        (∀ x ∈ P, a * x = x * a) → a * a = 1)
    {D : Subgroup K} (hD2 : ∀ d ∈ D, ∃ k : ℕ, orderOf d = 2 ^ k) (hD8 : Nat.card D = 8)
    (hDz : ∀ d ∈ D, d * z = z * d) (hDK : D ≤ commutator K) {u : K} (hu : orderOf u = 8)
    (huD : ∀ d ∈ D, u * d = d * u) : False := by
  have hu4 : u ^ 4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hu] at this
    omega
  have hu2k : ∃ k : ℕ, orderOf u = 2 ^ k := ⟨3, by rw [hu]; norm_num⟩
  have hu4o : ∃ k : ℕ, orderOf (u ^ 4) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hu2k
    have h1 : orderOf (u ^ 4) ∣ 2 ^ k := hk ▸ orderOf_pow_dvd 4
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨j, hj⟩
  unfold Lemma64Conclusion at hL64
  rcases hL64 with ⟨⟨e⟩⟩ | ⟨N₁, N₂, ⟨e₁⟩, ⟨e₂⟩, hc, hd, hN, hidx, hσ, hconj⟩
  ·
    have h8 : (e (QuotientGroup.mk u : K ⧸ fusionOddCore K)) ^ 8 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, ← hu, pow_orderOf_eq_one, QuotientGroup.mk_one,
        map_one]
    have h4 : (e (QuotientGroup.mk u : K ⧸ fusionOddCore K)) ^ 4 = 1 := by
      set w := e (QuotientGroup.mk u : K ⧸ fusionOddCore K) with hw
      have h8' : w.2 ^ 8 = 1 := by
        have := congrArg Prod.snd h8
        simpa using this
      have h4' : w.2 ^ 4 = 1 := a6_pow_four_of_pow_eight _ h8'
      have h1 : w.1 ^ 4 = 1 := by
        have : ∀ x : Multiplicative (ZMod 2), x ^ 4 = 1 := by decide
        exact this _
      exact Prod.ext h1 h4'
    have : (QuotientGroup.mk (u ^ 4) : K ⧸ fusionOddCore K) = 1 := by
      apply e.injective
      rw [QuotientGroup.mk_pow, map_pow, h4, map_one]
    exact hu4 (eq_one_of_mem_fusionOddCore ((QuotientGroup.eq_one_iff _).1 this) hu4o)
  ·
    have hDN : ∀ d ∈ D, (QuotientGroup.mk d : K ⧸ fusionOddCore K) ∈ N₁ ⊔ N₂ := by
      have hcyc : IsCyclic ((K ⧸ fusionOddCore K) ⧸ (N₁ ⊔ N₂)) := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card (p := 2) (by
          rw [← Subgroup.index, hidx])
      have hQ : ∀ x y : (K ⧸ fusionOddCore K) ⧸ (N₁ ⊔ N₂), x * y = y * x := fun x y =>
        (IsCyclic.commGroup : CommGroup ((K ⧸ fusionOddCore K) ⧸ (N₁ ⊔ N₂))).mul_comm x y
      have hcomm : ∀ a b : K ⧸ fusionOddCore K, a * b * a⁻¹ * b⁻¹ ∈ N₁ ⊔ N₂ := by
        intro a b
        rw [← QuotientGroup.eq_one_iff]
        have e1 : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) :
            (K ⧸ fusionOddCore K) ⧸ (N₁ ⊔ N₂)) =
            ((QuotientGroup.mk a * QuotientGroup.mk b) * (QuotientGroup.mk a)⁻¹) *
              (QuotientGroup.mk b)⁻¹ := rfl
        rw [e1, hQ (QuotientGroup.mk a) (QuotientGroup.mk b)]
        simp [mul_assoc]
      have hle : _root_.commutator K ≤
          (N₁ ⊔ N₂).comap (QuotientGroup.mk' (fusionOddCore K)) := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro g _ h _
        exact hcomm (QuotientGroup.mk g) (QuotientGroup.mk h)
      intro d hd
      exact hle (hDK hd)
    have hF : ∀ (P : Subgroup (K ⧸ fusionOddCore K)), P ≤ N₁ → Nat.card P = 8 → ∀ a ∈ N₁,
        (∀ x ∈ P, a * x = x * a) → a * a = 1 := fun P hP => hA6 N₁ ⟨e₁⟩ P hP
    have hF' : ∀ (P : Subgroup (K ⧸ fusionOddCore K)), P ≤ N₂ → Nat.card P = 8 → ∀ a ∈ N₂,
        (∀ x ∈ P, a * x = x * a) → a * a = 1 := fun P hP => hA6 N₂ ⟨e₂⟩ P hP
    exact hu4 (pow_four_eq_one_of_wreath hz2 hc hd hN hidx hconj hF hF' hD2 hD8 hDz hDN hu2k huD)

end CFSG.EvenSporadicStandard.Fin76b
