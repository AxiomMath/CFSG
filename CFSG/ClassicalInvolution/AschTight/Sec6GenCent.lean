module

public import CFSG.ClassicalInvolution.Asc77.AscL62Cyc
public import CFSG.ClassicalInvolution.AschTight.Sec6GenPair

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {z t : G}

theorem Pair.centralizes_of_normalizes (hΩ : HypOmegaGen Ω)
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
    le_normalizer_of_le_centralizer hΩ h.hK h.hJ h.ne h.hz hV₀J hV₀2 (by omega) hV₀c
  have hV₀A : V₀ ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hxA)
  have hP : IsPGroup 2 ↥(V₀ ⊔ A) := hV₀2.to_sup_of_normal_right' hA2 hV₀A
  have hPN : V₀ ⊔ A ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hV₀K (hAK.trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hP hPN
  have hVR : ∀ y ∈ V₀, conjSub y R = R := fun y hy => hRinv y ((le_sup_left : V₀ ≤ V₀ ⊔ A) hy)
  have hAN : A ≤ Subgroup.normalizer (R : Set G) := fun a ha =>
    mem_normalizer_iff_conjSub_eq.mpr (hRinv a ((le_sup_right : A ≤ V₀ ⊔ A) ha))
  have hAR : A ≤ R := by
    have hAR2 : IsPGroup 2 ↥(A ⊔ R) := hA2.to_sup_of_normal_right' hR.2.1 hAN
    have := hR.2.2 (A ⊔ R) (sup_le hAK hR.1) hAR2 le_sup_right
    exact le_sup_left.trans this.le
  have hcfg : CoreCfg R V₀ z t := h.coreCfg hΩ hR hV₀2 hV₀J htV₀ hVR
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
    le_normalizer_of_le_centralizer hΩ h.hJ h.hK h.ne.symm h.ht hUK hU2 (by omega)
      inf_le_right
  have hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({t} : Set G), ∀ v ∈ V₀, u * v = v * u := by
    intro u hu v hv
    exact h.comm_of_normalizes hR.1 hR.2.1 hV₀J hVR hu.1 (hUN hu) hv
  exact hcfg.cyclic_le_centralizer hAR hA (fun y hy => mem_normalizer_iff_conjSub_eq.mp (hV₀A hy))
    (Subgroup.mem_zpowers x) hxx hcomm

theorem eq_of_commutes_of_natCard_eq (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {A A' : Subgroup G} (hAK : A ≤ K) (hA'K : A' ≤ K)
    (hA : IsCyclic ↥A) (hA' : IsCyclic ↥A') (hA2 : IsPGroup 2 ↥A) (hA'2 : IsPGroup 2 ↥A')
    (h4 : 4 ≤ Nat.card A) (hcard : Nat.card A = Nat.card A') (hcomm : Commutes A A') :
    A = A' := by
  have hP : IsPGroup 2 ↥(A ⊔ A') :=
    hA2.to_sup_of_normal_right' hA'2 (le_normalizer_of_commutes hcomm)
  obtain ⟨R, hR, hPR⟩ := IsSylow2In.exists_ge hP (sup_le hAK hA'K)
  have hquat : IsQuatSub R := isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR)
  have hzR : z ∈ R :=
    mem_of_uniqueInvolution_of_pGroup hz hR.1 hR.2.1 (by have := hquat.eight_le; omega)
  have hzR' : IsUniqueInvolution R z := isUniqueInvolution_of_le hz hR.1 hzR
  obtain ⟨g, hg⟩ := hA.exists_generator
  obtain ⟨g', hg'⟩ := hA'.exists_generator
  have hAeq := eq_zpowers_of_generator g hg
  have hA'eq := eq_zpowers_of_generator g' hg'
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hgo : orderOf (g : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  have hgo' : orderOf (g' : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg', ← hcard, hk]
  rw [hAeq, hA'eq]
  exact zpowers_eq_of_commute_of_orderOf_eq hquat hzR' (hPR ((le_sup_left : A ≤ A ⊔ A') g.2))
    (hPR ((le_sup_right : A' ≤ A ⊔ A') g'.2)) (hcomm g g.2 g' g'.2) hk2 hgo hgo'

theorem Pair.exists_core (hΩ : HypOmegaGen Ω)
    (h : Pair Ω K J z t) {x : G} (hxJ : x ∈ J) {m : ℕ} (hm : 2 ≤ m) (hxo : orderOf x = 2 ^ m)
    {A : Subgroup G} (hAK : A ≤ K) (hA2 : IsPGroup 2 ↥A) (hA1 : 2 ≤ Nat.card A)
    (hxA : conjSub x A = A) :
    ∃ R : Subgroup G, IsSylow2In R K ∧ A ≤ R ∧ CoreCfg R (Subgroup.zpowers x) z t ∧
      Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) ∧
      (∀ y ∈ Subgroup.zpowers x, conjSub y R = R) ∧
      (∀ u ∈ R ⊓ Subgroup.centralizer ({t} : Set G), ∀ v ∈ Subgroup.zpowers x, u * v = v * u) ∧
      CoreDich R (Subgroup.zpowers x) t := by
  have h4m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hzA : z ∈ A := mem_of_uniqueInvolution_of_pGroup h.hz hAK hA2 hA1
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
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    omega
  set V₀ : Subgroup G := Subgroup.zpowers x with hV₀
  have hV₀card : Nat.card V₀ = 2 ^ m := by rw [hV₀, Nat.card_zpowers, hxo]
  have hV₀2 : IsPGroup 2 ↥V₀ := IsPGroup.of_card (n := m) hV₀card
  have hV₀J : V₀ ≤ J := Subgroup.zpowers_le.mpr hxJ
  have htV₀ : t ∈ V₀ := by
    obtain ⟨y, hy, hy2, hy1⟩ := exists_involution_pow hx1 hxo
    rcases h.ht.unique y (hV₀J hy) hy2 with h1 | h1
    · exact absurd h1 hy1
    · rw [← h1]
      exact hy
  have hV₀c : V₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzx)
  have hV₀K : V₀ ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer hΩ h.hK h.hJ h.ne h.hz hV₀J hV₀2
      (by rw [hV₀card]; omega) hV₀c
  have hV₀A : V₀ ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hxA)
  have hP : IsPGroup 2 ↥(V₀ ⊔ A) := hV₀2.to_sup_of_normal_right' hA2 hV₀A
  have hPN : V₀ ⊔ A ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hV₀K (hAK.trans Subgroup.le_normalizer)
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hP hPN
  have hVR : ∀ y ∈ V₀, conjSub y R = R := fun y hy => hRinv y ((le_sup_left : V₀ ≤ V₀ ⊔ A) hy)
  have hAN : A ≤ Subgroup.normalizer (R : Set G) := fun a ha =>
    mem_normalizer_iff_conjSub_eq.mpr (hRinv a ((le_sup_right : A ≤ V₀ ⊔ A) ha))
  have hAR : A ≤ R := by
    have hAR2 : IsPGroup 2 ↥(A ⊔ R) := hA2.to_sup_of_normal_right' hR.2.1 hAN
    have := hR.2.2 (A ⊔ R) (sup_le hAK hR.1) hAR2 le_sup_right
    exact le_sup_left.trans this.le
  have hcfg : CoreCfg R V₀ z t := h.coreCfg hΩ hR hV₀2 hV₀J htV₀ hVR
  have hV₀ne : V₀ ≠ Subgroup.zpowers t := by
    intro heq
    have h2 : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
    rw [← heq, hV₀card] at h2
    omega
  have hU4 := hcfg.four_le_natCard_cent hV₀ne
  have hU2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := hR.2.1.to_inf_left
  have hUK : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ K := inf_le_left.trans hR.1
  have hUN : R ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_le_centralizer hΩ h.hJ h.hK h.ne.symm h.ht hUK hU2 (by omega)
      inf_le_right
  have hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({t} : Set G), ∀ v ∈ V₀, u * v = v * u := by
    intro u hu v hv
    exact h.comm_of_normalizes hR.1 hR.2.1 hV₀J hVR hu.1 (hUN hu) hv
  exact ⟨R, hR, hAR, hcfg, hV₀K, hVR, hcomm, hcfg.core_dichotomy hV₀ne hcomm⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
