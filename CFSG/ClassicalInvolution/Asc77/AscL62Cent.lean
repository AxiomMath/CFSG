module

public import CFSG.ClassicalInvolution.Asc77.AscL62Pair

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {z t : G}

theorem Pair.centralizes_of_normalizes (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : Pair Ω K J z t) {x : G} (hxJ : x ∈ J) (hxx : x * x = t) {A : Subgroup G} (hAK : A ≤ K)
    (hA : IsCyclic ↥A) (hA2 : IsPGroup 2 ↥A) (hxA : conjSub x A = A) :
    ∀ a ∈ A, a * x = x * a := by
  by_cases hA1 : Nat.card A ≤ 1
  · intro a ha
    have hbot : A = ⊥ := Subgroup.eq_bot_of_card_le A hA1
    rw [hbot, Subgroup.mem_bot] at ha
    rw [ha, one_mul, mul_one]
  push Not at hA1
  have hzA : z ∈ A := mem_of_uniqueInvolution_of_pGroup h.hz hAK hA2 (by omega)
  have hxz : x * z * x⁻¹ = z := by
    have h1 : x * z * x⁻¹ ∈ A := by
      have := conj_mem_conjSub (n := x) hzA
      rwa [hxA] at this
    have h2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
      calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
        _ = 1 := by rw [h.hz.sq]; group
    rcases h.hz.unique _ (hAK h1) h2 with h3 | h3
    · exfalso
      apply h.hz.ne_one
      have := congrArg (fun w => x⁻¹ * w * x) h3
      simpa [mul_assoc] using this
    · exact h3
  have hzx : x * z = z * x := by
    have := congrArg (fun w => w * x) hxz
    simpa [mul_assoc] using this
  have hxt1 : x * x ≠ 1 := by rw [hxx]; exact h.ht.ne_one
  have hx4 : x ^ 4 = 1 := by
    have : x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, hxx]
    exact h.ht.sq
  have hord : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) (by simpa [pow_two] using hxt1)
      (by simpa using hx4)
    simpa using this
  set V₀ : Subgroup G := Subgroup.zpowers x with hV₀
  have hV₀card : Nat.card V₀ = 4 := by rw [hV₀, Nat.card_zpowers, hord]
  have hV₀2 : IsPGroup 2 ↥V₀ := IsPGroup.of_card (n := 2) (by rw [hV₀card]; norm_num)
  have hV₀J : V₀ ≤ J := Subgroup.zpowers_le.mpr hxJ
  have htV₀ : t ∈ V₀ := by
    rw [← hxx]
    exact V₀.mul_mem (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x)
  have hV₀c : V₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzx)
  have hV₀K : V₀ ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq h.hK h.hJ h.ne h.hz hV₀J hV₀2 (by omega) hV₀c
  have hV₀A : V₀ ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hxA)
  have hP : IsPGroup 2 ↥(V₀ ⊔ A) := hV₀2.to_sup_of_normal_right' hA2 hV₀A
  have hPN : V₀ ⊔ A ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hV₀K (hAK.trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRinv⟩ := exists_sylow_normalized hP hPN
  have hVR : ∀ y ∈ V₀, conjSub y R = R := fun y hy => hRinv y ((le_sup_left : V₀ ≤ V₀ ⊔ A) hy)
  have hAN : A ≤ Subgroup.normalizer (R : Set G) := fun a ha =>
    mem_normalizer_iff_conjSub_eq.mpr (hRinv a ((le_sup_right : A ≤ V₀ ⊔ A) ha))
  have hAR : A ≤ R := by
    have hAR2 : IsPGroup 2 ↥(A ⊔ R) := hA2.to_sup_of_normal_right' hR.2.1 hAN
    have := hR.2.2 (A ⊔ R) (sup_le hAK hR.1) hAR2 le_sup_right
    exact le_sup_left.trans this.le
  have hcfg : CoreCfg R V₀ z t := h.coreCfg hp hΩ hR hV₀2 hV₀J htV₀ hVR
  have hV₀ne : V₀ ≠ Subgroup.zpowers t := by
    intro heq
    have h2 : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
    rw [← heq] at h2
    omega
  have hU4 := hcfg.four_le_natCard_cent hV₀ne
  have hU2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := hR.2.1.to_inf_left
  have hUK : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ K := inf_le_left.trans hR.1
  have hUN : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq h.hJ h.hK h.ne.symm h.ht hUK hU2 (by omega)
      inf_le_right
  have hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({t} : Set G), ∀ v ∈ V₀, u * v = v * u := by
    intro u hu v hv
    exact h.comm_of_normalizes hR.1 hR.2.1 hV₀J hVR hu.1 (hUN hu) hv
  exact hcfg.cyclic_le_centralizer hAR hA (fun y hy => mem_normalizer_iff_conjSub_eq.mp (hV₀A hy))
    (Subgroup.mem_zpowers x) hxx hcomm

end CFSG.ClassicalInvolution.Asc77.AscL62
