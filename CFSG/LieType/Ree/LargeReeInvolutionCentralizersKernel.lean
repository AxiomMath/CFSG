module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LieType.Ree.LargeReeInvolution

open Subgroup

theorem kernel_not_isPGroup_of_isSimpleGroup {R : Type*} [Group R] [Finite R] [IsSimpleGroup R]
    (hnab : ∃ x y : R, x * y ≠ y * x) {p : ℕ} [Fact p.Prime] : ¬ IsPGroup p R := by
  intro hp
  have := hp.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center R) with h | h
  · obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : center R)
    rw [h, mem_bot] at hx
    exact hx1 (Subtype.ext hx)
  · obtain ⟨x, y, hxy⟩ := hnab
    exact hxy ((mem_center_iff.1 (h ▸ mem_top y : y ∈ center R)) x)

variable {G : Type*} [Group G] {N R : Subgroup G}

theorem kernel_exists_mul_eq (hN : N.Normal) (hNR : N ⊔ R = ⊤) (g : G) :
    ∃ n ∈ N, ∃ r ∈ R, n * r = g :=
  mem_sup_of_normal_left.1 (hNR ▸ mem_top g)

@[expose] def kernelInnerActing (hN : N.Normal) (R : Subgroup G) : Subgroup R where
  carrier := {r | ∃ n ∈ N, ∀ x ∈ N, (r : G) * x * (r : G)⁻¹ = n * x * n⁻¹}
  one_mem' := ⟨1, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro r₁ r₂ ⟨n₁, hn₁, h₁⟩ ⟨n₂, hn₂, h₂⟩
    refine ⟨(r₁ : G) * n₂ * (r₁ : G)⁻¹ * n₁, mul_mem (hN.conj_mem _ hn₂ _) hn₁, fun x hx => ?_⟩
    have e₁ := h₁ x hx
    have e₂ := h₂ x hx
    calc ((r₁ * r₂ : R) : G) * x * ((r₁ * r₂ : R) : G)⁻¹ =
        (r₁ : G) * ((r₂ : G) * x * (r₂ : G)⁻¹) * (r₁ : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
      _ = (r₁ : G) * (n₂ * x * n₂⁻¹) * (r₁ : G)⁻¹ := by rw [e₂]
      _ = ((r₁ : G) * n₂ * (r₁ : G)⁻¹) * ((r₁ : G) * x * (r₁ : G)⁻¹) *
          ((r₁ : G) * n₂ * (r₁ : G)⁻¹)⁻¹ := by group
      _ = ((r₁ : G) * n₂ * (r₁ : G)⁻¹) * (n₁ * x * n₁⁻¹) *
          ((r₁ : G) * n₂ * (r₁ : G)⁻¹)⁻¹ := by rw [e₁]
      _ = (r₁ : G) * n₂ * (r₁ : G)⁻¹ * n₁ * x * ((r₁ : G) * n₂ * (r₁ : G)⁻¹ * n₁)⁻¹ := by
          group
  inv_mem' := by
    rintro r ⟨n, hn, h⟩
    refine ⟨n⁻¹, inv_mem hn, fun x hx => ?_⟩
    have hz : (r : G)⁻¹ * x * (r : G) ∈ N := by
      have := hN.conj_mem _ hx (r : G)⁻¹
      rwa [inv_inv] at this
    have e := h _ hz
    have e' : x = n * ((r : G)⁻¹ * x * (r : G)) * n⁻¹ := by
      rw [← e]
      group
    calc ((r⁻¹ : R) : G) * x * ((r⁻¹ : R) : G)⁻¹ = (r : G)⁻¹ * x * (r : G) := by
          simp only [Subgroup.coe_inv, inv_inv]
      _ = n⁻¹ * (n * ((r : G)⁻¹ * x * (r : G)) * n⁻¹) * n⁻¹⁻¹ := by group
      _ = n⁻¹ * x * n⁻¹⁻¹ := by rw [← e']

theorem kernelInnerActing_normal (hN : N.Normal) : (kernelInnerActing hN R).Normal where
  conj_mem := by
    rintro r ⟨n, hn, h⟩ s
    refine ⟨(s : G) * n * (s : G)⁻¹, hN.conj_mem _ hn _, fun x hx => ?_⟩
    have hx' : (s : G)⁻¹ * x * (s : G) ∈ N := by
      have := hN.conj_mem _ hx (s : G)⁻¹
      rwa [inv_inv] at this
    have e := h _ hx'
    calc ((s * r * s⁻¹ : R) : G) * x * ((s * r * s⁻¹ : R) : G)⁻¹ =
        (s : G) * ((r : G) * ((s : G)⁻¹ * x * (s : G)) * (r : G)⁻¹) * (s : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
      _ = (s : G) * (n * ((s : G)⁻¹ * x * (s : G)) * n⁻¹) * (s : G)⁻¹ := by rw [e]
      _ = (s : G) * n * (s : G)⁻¹ * x * ((s : G) * n * (s : G)⁻¹)⁻¹ := by group

theorem kernelInnerActing_eq_bot [Finite G] (hN : N.Normal) (hN2 : IsPGroup 2 N)
    [IsSimpleGroup R]
    (hRnab : ∃ x y : R, x * y ≠ y * x) (hact : ∃ r ∈ R, ∃ n ∈ N, r * n ≠ n * r) :
    kernelInnerActing hN R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := kernelInnerActing_normal (R := R) hN
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (kernelInnerActing hN R)).resolve_right
    fun htop => ?_
  set φ : R →* MulAut N := (MulAut.conjNormal (H := N)).comp R.subtype with hφ
  have hrange : φ.range ≤ (MulAut.conj : N →* MulAut N).range := by
    rintro _ ⟨r, rfl⟩
    obtain ⟨n, hn, h⟩ : r ∈ kernelInnerActing hN R := htop ▸ mem_top r
    refine ⟨⟨n, hn⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [MulAut.conj_apply, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
    exact (h x x.2).symm
  have hInn : IsPGroup 2 (MulAut.conj : N →* MulAut N).range := hN2.of_surjective
    (MulAut.conj : N →* MulAut N).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have hφP : IsPGroup 2 φ.range := hInn.to_le hrange
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hker | hker
  ·
    refine kernel_not_isPGroup_of_isSimpleGroup hRnab (hφP.of_injective φ.rangeRestrict ?_)
    rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_rangeRestrict, hker]
  ·
    obtain ⟨r, hr, n, hn, hrn⟩ := hact
    have h1 : φ ⟨r, hr⟩ = 1 := (MonoidHom.mem_ker).1 (hker ▸ mem_top _)
    have h2 := congrArg (fun α : MulAut N => (α ⟨n, hn⟩ : G)) h1
    simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
      MulAut.one_apply] at h2
    exact hrn (calc r * n = r * n * r⁻¹ * r := by group
      _ = n * r := by rw [h2])

theorem kernel_selfCentralizing [Finite G] (hN : N.Normal) (hN2 : IsPGroup 2 N)
    (hNR : N ⊔ R = ⊤) [IsSimpleGroup R] (hRnab : ∃ x y : R, x * y ≠ y * x)
    (hact : ∃ r ∈ R, ∃ n ∈ N, r * n ≠ n * r) :
    centralizer (N : Set G) ≤ N ∧ (∀ M : Subgroup G, M.Normal → IsPGroup 2 M → M ≤ N) ∧
      ∀ M : Subgroup G, M.Normal → Odd (Nat.card M) → M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := kernelInnerActing_eq_bot hN hN2 hRnab hact
  have hC : centralizer (N : Set G) ≤ N := by
    intro g hg
    obtain ⟨n, hn, r, hr, rfl⟩ := kernel_exists_mul_eq hN hNR g
    have hrK : (⟨r, hr⟩ : R) ∈ kernelInnerActing hN R := by
      refine ⟨n⁻¹, inv_mem hn, fun x hx => ?_⟩
      have e : x * (n * r) = n * r * x := mem_centralizer_iff.1 hg x hx
      calc r * x * r⁻¹ = n⁻¹ * ((n * r) * x * (n * r)⁻¹) * n := by group
        _ = n⁻¹ * (x * (n * r) * (n * r)⁻¹) * n := by rw [e]
        _ = n⁻¹ * x * n⁻¹⁻¹ := by group
    rw [hK, mem_bot] at hrK
    have hr1 : r = 1 := congrArg Subtype.val hrK
    rw [hr1, mul_one]
    exact hn
  refine ⟨hC, fun M hM hM2 => ?_, fun M hM hModd => ?_⟩
  ·
    have hMN2 : IsPGroup 2 (M ⊔ N : Subgroup G) := hM2.to_sup_of_normal_right hN2
    have hnorm : ((M ⊔ N).subgroupOf R).Normal := by
      have : (M ⊔ N).Normal := Subgroup.sup_normal M N
      exact this.subgroupOf R
    have hbot : (M ⊔ N).subgroupOf R = ⊥ := by
      refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊔ N).subgroupOf R)).resolve_right
        fun htop => ?_
      refine kernel_not_isPGroup_of_isSimpleGroup hRnab (p := 2) ?_
      have h1 : IsPGroup 2 ((M ⊔ N).subgroupOf R) := hMN2.comap_subtype
      rw [htop] at h1
      exact h1.of_equiv Subgroup.topEquiv
    intro m hm
    obtain ⟨n, hn, r, hr, rfl⟩ := kernel_exists_mul_eq hN hNR m
    have hrMN : r ∈ M ⊔ N := by
      have : r = n⁻¹ * (n * r) := by group
      rw [this]
      exact mul_mem (mem_sup_right (inv_mem hn)) (mem_sup_left hm)
    have hr1 : (⟨r, hr⟩ : R) ∈ (M ⊔ N).subgroupOf R := hrMN
    rw [hbot, mem_bot] at hr1
    have hr1' : r = 1 := congrArg Subtype.val hr1
    rw [hr1', mul_one]
    exact hn
  ·
    have hMN : M ⊓ N = ⊥ := by
      have h2 : IsPGroup 2 (M ⊓ N : Subgroup G) := hN2.to_inf_right
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      have hdvd : Nat.card (M ⊓ N : Subgroup G) ∣ Nat.card M :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [hk] at hdvd
      have hk0 : k = 0 := by
        by_contra hk0
        have h2dvd : 2 ∣ Nat.card M := (dvd_pow_self 2 hk0).trans hdvd
        exact (Nat.not_even_iff_odd.2 hModd) (even_iff_two_dvd.2 h2dvd)
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hle : M ≤ centralizer (N : Set G) := fun m hm => mem_centralizer_iff.2 fun x hx => by
      have hcM : m * x * m⁻¹ * x⁻¹ ∈ M := by
        have h1 : x * m⁻¹ * x⁻¹ ∈ M := hM.conj_mem _ (inv_mem hm) x
        have h2 := mul_mem hm h1
        rwa [show m * (x * m⁻¹ * x⁻¹) = m * x * m⁻¹ * x⁻¹ by group] at h2
      have hcN : m * x * m⁻¹ * x⁻¹ ∈ N := mul_mem (hN.conj_mem _ hx m) (inv_mem hx)
      have hc : m * x * m⁻¹ * x⁻¹ ∈ M ⊓ N := mem_inf.2 ⟨hcM, hcN⟩
      rw [hMN, mem_bot] at hc
      have : m * x * m⁻¹ * x⁻¹ = 1 := hc
      calc x * m = (m * x * m⁻¹ * x⁻¹)⁻¹ * (m * x) := by group
        _ = m * x := by rw [this, inv_one, one_mul]
    rw [eq_bot_iff]
    intro m hm
    have hmN := hC (hle hm)
    have : m ∈ M ⊓ N := mem_inf.2 ⟨hm, hmN⟩
    rwa [hMN] at this

end CFSG.LieType.Ree.LargeReeInvolution
