module

public import CFSG.GH74.Uniqueness.Section165B0

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec165

theorem not_fixed_of_dvd
    {F : Subgroup X} {k : ℕ} (hk : 1 ≤ k)
    (hF : Bender.BenderType ↥F (2 * k) 1 1) {a : X} (ha : a ∈ normalizer (F : Set X))
    (ha2 : a * a = 1) (hout : ¬ ∃ g : ↥F, ∀ x : ↥F, conjAut ha x = g * x * g⁻¹)
    (hiso : Nonempty (Bender.autFixed (conjAut ha) ≃* CFSG.Theory.Comparator.PSL2Model k))
    {Q₀ : Sylow 2 ↥F} {z' : ↥F} (hzR : z' ∈ Bender.rootCenter (Q₀ : Subgroup ↥F)) (hz'1 : z' ≠ 1)
    (hza : conjAut ha z' = z') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1)
    {y : ↥F} (hyB : y ∈ Bender.borel (Q₀ : Subgroup ↥F)) (hyo : orderOf y = p)
    (hya : conjAut ha y = y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hiso
  set H' := Bender.autFixed (conjAut ha) with hH'
  have hyH : y ∈ H' := Bender.mem_autFixed_iff.mpr hya
  have hzH : z' ∈ H' := Bender.mem_autFixed_iff.mpr hza
  have hzQ : z' ∈ (Q₀ : Subgroup ↥F) := (Bender.mem_rootCenter_iff.mp hzR).1
  have hcardH : Nat.card ↥H' = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact Bender.card_psl2_even k hk
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  ·
    have hk1' : k = 1 := by omega
    subst hk1'
    have h6 : Nat.card ↥H' = 6 := by rw [hcardH]; norm_num
    have hp3 : p = 3 := by
      have h3 : p ∣ 3 := by simpa using hpk
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    set C' := H' ⊓ Bender.borel (Q₀ : Subgroup ↥F) with hC'
    have hz2 : orderOf z' = 2 := by
      obtain ⟨t₀, hc⟩ := hF.exists_benderCore Q₀
      exact (hc.involution_iff.mpr ⟨hzR, hz'1⟩).2
    have h2 : 2 ∣ Nat.card ↥C' := by
      have := orderOf_dvd_natCard (⟨z', mem_inf.mpr ⟨hzH, Bender.le_borel _ hzQ⟩⟩ : ↥C')
      rwa [Subgroup.orderOf_mk, hz2] at this
    have h3 : 3 ∣ Nat.card ↥C' := by
      have := orderOf_dvd_natCard (⟨y, mem_inf.mpr ⟨hyH, hyB⟩⟩ : ↥C')
      rwa [Subgroup.orderOf_mk, hyo, hp3] at this
    have h6' : 6 ∣ Nat.card ↥C' := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    have hle : C' ≤ H' := inf_le_left
    have hCH : C' = H' := Subgroup.eq_of_le_of_card_ge hle (by
      rw [h6]
      exact Nat.le_of_dvd Nat.card_pos h6')
    have hHB : H' ≤ Bender.borel (Q₀ : Subgroup ↥F) := hCH ▸ inf_le_right
    have hBG : CFSG.BenderSuzuki.IsBenderGroup ↥F :=
      Bender.isBenderGroup_iff_exists_benderType.mpr ⟨_, _, _, hF⟩
    obtain ⟨-, hS⟩ := Bender.bender_outer_involution hBG (conjAut ha) (conjAut_mul_self ha ha2) hout
    obtain ⟨x, hxa, hxN⟩ := hS Q₀
    exact hxN (hHB (Bender.mem_autFixed_iff.mpr hxa))
  ·
    have hBT : Bender.BenderType ↥H' k 1 1 := Bender.BenderType.linear k hk2 e
    set V : Subgroup ↥H' := (Q₀ : Subgroup ↥F).subgroupOf H' with hV
    have hV2 : IsPGroup 2 V := Q₀.isPGroup'.comap_subtype
    have hzV : (⟨z', hzH⟩ : ↥H') ∈ V := mem_subgroupOf.mpr hzQ
    have hV1 : V ≠ ⊥ := by
      intro hbot
      rw [hbot, mem_bot] at hzV
      exact hz'1 (congrArg Subtype.val hzV)
    obtain ⟨Q', hVQ'⟩ := hV2.exists_le_sylow
    obtain ⟨t', hc'⟩ := hBT.exists_benderCore Q'
    have hN := Bender.IsStronglyEmbedded.normalizer_le hc'.strong
      (hVQ'.trans (Bender.le_borel _)) hV2 hV1
    have hyN : (⟨y, hyH⟩ : ↥H') ∈ normalizer (V : Set ↥H') := by
      rw [mem_normalizer_iff]
      intro v
      rw [hV, mem_subgroupOf, mem_subgroupOf]
      exact (mem_normalizer_iff.mp hyB (v : ↥F))
    have hyB' := hN hyN
    have hdvd := orderOf_dvd_natCard (⟨⟨y, hyH⟩, hyB'⟩ : ↥(Bender.borel (Q' : Subgroup ↥H')))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hyo, hc'.card_borel, pow_one, mul_one] at hdvd
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hdvd' : p ∣ 2 ^ k - 1 := hcop.dvd_of_dvd_mul_left hdvd
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub hpk hdvd'
      rwa [show 2 ^ k + 1 - (2 ^ k - 1) = 2 by omega] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem exists_inverted_of_outer
    (S : ZDSetup X Z M) {F : Subgroup X} {k : ℕ} (hk : 1 ≤ k)
    (hF : Bender.BenderType ↥F (2 * k) 1 1) {z t a : X} (hz : z ∈ Z) (hzM : z ∈ M)
    (hzF : z ∈ F) (htM : t ∉ M) (htF : t ∈ F) (ht2 : t * t = 1)
    (ha : a ∈ normalizer (F : Set X)) (haD : a ∈ M ⊓ conjugate M t) (ha2 : a * a = 1)
    (haz : a * z = z * a) (hout : ¬ ∃ g : ↥F, ∀ x : ↥F, conjAut ha x = g * x * g⁻¹)
    (hiso : Nonempty (Bender.autFixed (conjAut ha) ≃* CFSG.Theory.Comparator.PSL2Model k))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1) :
    ∃ x ∈ (M ⊓ conjugate M t) ⊓ F, orderOf x = p ∧ t * x * t⁻¹ = x⁻¹ ∧ a * x * a⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hFM : ¬ F ≤ M := fun h => htM (h htF)
  obtain ⟨Q₀, hzR, hQ₀⟩ := Sec164.exists_sylow_borel_eq S hF hz hzM hzF hFM
  obtain ⟨hc, hcart⟩ := Sec164.cartan_eq_comap hF hQ₀ htF htM ht2
  have hcardC := hc.card_cartan
  have hinvC := hc.ncard_inv
  have hcycC := hc.isCyclic
  have hcbC : Bender.cartan (Q₀ : Subgroup ↥F) ⟨t, htF⟩ ≤ Bender.borel (Q₀ : Subgroup ↥F) :=
    Bender.cartan_le_borel _ _
  generalize Bender.cartan (Q₀ : Subgroup ↥F) ⟨t, htF⟩ = Ca at hcardC hinvC hcycC hcbC hcart
  have hpdvd : p ∣ Nat.card ↥Ca := by
    rw [hcardC, mul_one, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    have e : 4 ^ k - 1 = (2 ^ k + 1) * (2 ^ k - 1) := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h4 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
        rw [← mul_pow]
        norm_num
      rw [h4]
      zify [h1, show 1 ≤ 2 ^ k * 2 ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity)]
      ring
    rw [e]
    exact Dvd.dvd.mul_right hpk _
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Ca) p hpdvd
  set x₁ : ↥F := (x₀ : ↥F) with hx₁
  have hx₁C : x₁ ∈ Ca := x₀.2
  have hx₁o : orderOf x₁ = p := by rw [hx₁, Subgroup.orderOf_coe, hx₀]
  have hinvAll : ∀ y ∈ Ca, (⟨t, htF⟩ : ↥F) * y * ⟨t, htF⟩ = y⁻¹ := by
    have hsub : {y : ↥F | y ∈ Ca ∧ (⟨t, htF⟩ : ↥F) * y * ⟨t, htF⟩ = y⁻¹} ⊆ (Ca : Set ↥F) :=
      fun y hy => hy.1
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [hinvC, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcardC, mul_one])
      (Set.toFinite _)
    intro y hy
    have : y ∈ {y : ↥F | y ∈ Ca ∧ (⟨t, htF⟩ : ↥F) * y * ⟨t, htF⟩ = y⁻¹} := by
      rw [heq]; exact hy
    exact this.2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hαC : ∀ y ∈ Ca, conjAut ha y ∈ Ca := by
    intro y hy
    rw [hcart] at hy ⊢
    rw [mem_comap] at hy ⊢
    rw [Subgroup.coe_subtype, conjAut_apply]
    exact mul_mem (mul_mem haD hy) (inv_mem haD)
  have hcomm : ∀ y₁ ∈ Ca, ∀ y₂ ∈ Ca, y₁ * y₂ = y₂ * y₁ := by
    intro y₁ hy₁ y₂ hy₂
    exact congrArg Subtype.val (IsCyclic.commGroup.mul_comm (⟨y₁, hy₁⟩ : ↥Ca) ⟨y₂, hy₂⟩)
  have hza : conjAut ha ⟨z, hzF⟩ = ⟨z, hzF⟩ := conjAut_fix ha haz
  have hz'1 : (⟨z, hzF⟩ : ↥F) ≠ 1 := by
    intro h
    have := S.invariant.1 z hz
    rw [show z = 1 from congrArg Subtype.val h, orderOf_one] at this
    omega
  set u₁ := x₁ * conjAut ha x₁ with hu₁
  have hαα : conjAut ha (conjAut ha x₁) = x₁ := by
    have := congrArg (fun σ : MulAut ↥F => σ x₁) (conjAut_mul_self ha ha2)
    simpa using this
  have hu₁C : u₁ ∈ Ca := mul_mem hx₁C (hαC _ hx₁C)
  have hu₁fix : conjAut ha u₁ = u₁ := by
    rw [hu₁, map_mul, hαα]
    exact hcomm _ (hαC _ hx₁C) _ hx₁C
  have hu₁1 : u₁ = 1 := by
    by_contra hne
    have hpow : u₁ ^ p = 1 := by
      rw [hu₁, (Commute.mul_pow (hcomm _ hx₁C _ (hαC _ hx₁C)) p), ← map_pow,
        ← hx₁o, pow_orderOf_eq_one, map_one, one_mul]
    have hord : orderOf u₁ = p := orderOf_eq_prime hpow hne
    have hu₁B : u₁ ∈ Bender.borel (Q₀ : Subgroup ↥F) := hcbC hu₁C
    exact not_fixed_of_dvd hk hF ha ha2 hout hiso hzR hz'1 hza hp hp2 hpk hu₁B hord hu₁fix
  have hαx : conjAut ha x₁ = x₁⁻¹ := eq_inv_of_mul_eq_one_right hu₁1
  refine ⟨(x₁ : X), ?_, by rw [Subgroup.orderOf_coe, hx₁o], ?_, ?_⟩
  · have := hx₁C
    rw [hcart, mem_comap] at this
    exact mem_inf.mpr ⟨this, x₁.2⟩
  · have := congrArg Subtype.val (hinvAll x₁ hx₁C)
    simp only [coe_mul, coe_inv] at this
    rw [hti]
    exact this
  · have := congrArg Subtype.val hαx
    rw [conjAut_apply] at this
    rw [this, coe_inv]

end Sec165

end CFSG.GH74.Uniqueness
