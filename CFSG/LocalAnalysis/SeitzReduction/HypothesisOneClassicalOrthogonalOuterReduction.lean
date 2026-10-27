module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic

public section

namespace CFSG.SeitzReduction

namespace OmegaOuter

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem pow_two_eq_one_of_conj_le {C : Type*} [Group C] {E : Subgroup (MulAut C)}
    (hconj : ∀ P : Subgroup (MulAut C), IsPGroup 2 P →
      ∃ ψ : MulAut C, P.map (MulAut.conj ψ⁻¹).toMonoidHom ≤ E)
    (h : ∀ x ∈ E, orderOf x = 2 → ∀ β ∈ E, β * x = x * β →
      (∀ c : C, x c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1)
    {x : MulAut C} (hx : orderOf x = 2) {β : MulAut C} {k : ℕ} (hβk : orderOf β = 2 ^ k)
    (hβx : β * x = x * β) (hβ : ∀ c : C, x c = c → Odd (orderOf c) → β c = c) :
    β ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hB : IsPGroup 2 (zpowers β) := IsPGroup.of_card (by rw [Nat.card_zpowers, hβk])
  have hβC : zpowers β ≤ centralizer ({x} : Set (MulAut C)) :=
    zpowers_le.2 (mem_centralizer_singleton_iff.2 hβx)
  have hnorm : zpowers x ≤ normalizer (zpowers β : Set (MulAut C)) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.1 (hβC hy)
  obtain ⟨ψ, hψ⟩ := hconj _ (hX.to_sup_of_normal_right' hB hnorm)
  set γ := MulAut.conj ψ⁻¹ with hγdef
  have hγ : ∀ (y : MulAut C) (c : C), γ y c = ψ⁻¹ (y (ψ c)) := fun y c => by
    rw [hγdef, MulAut.conj_apply, inv_inv, MulAut.mul_apply, MulAut.mul_apply]
  have hxE : γ x ∈ E := hψ (mem_map_of_mem _ (mem_sup_left (mem_zpowers x)))
  have hβE : γ β ∈ E := hψ (mem_map_of_mem _ (mem_sup_right (mem_zpowers β)))
  have hx2 : orderOf (γ x) = 2 := by rw [MulEquiv.orderOf_eq, hx]
  have hcomm : γ β * γ x = γ x * γ β := by rw [← map_mul, ← map_mul, hβx]
  have hfix : ∀ c : C, γ x c = c → Odd (orderOf c) → γ β c = c := by
    intro c hxc hc
    rw [hγ] at hxc ⊢
    have hxc' : x (ψ c) = ψ c := by
      have h1 := congrArg ψ hxc
      rwa [MulAut.apply_inv_self] at h1
    rw [hβ (ψ c) hxc' (by rwa [MulEquiv.orderOf_eq]), MulAut.inv_apply_self]
  have h2 := h _ hxE hx2 _ hβE hcomm hfix
  rw [← map_pow] at h2
  exact (MulEquiv.map_eq_one_iff γ).1 h2

theorem noNormalZ4OrZ2xZ4_of_conj_le {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {E : Subgroup (MulAut C)}
    (hconj : ∀ P : Subgroup (MulAut C), IsPGroup 2 P →
      ∃ ψ : MulAut C, P.map (MulAut.conj ψ⁻¹).toMonoidHom ≤ E)
    (h : ∀ x ∈ E, orderOf x = 2 → ∀ β ∈ E, β * x = x * β →
      (∀ c : C, x c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1)
    {x : MulAut C} (hx : orderOf x = 2) {H : Subgroup (MulAut C)} (hH : inner C ≤ H) :
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({x} : Set (MulAut C))) := by
  have hmem : ∀ c : C, x c = c →
      MulAut.conj c ∈ H ⊓ centralizer ({x} : Set (MulAut C)) := fun c hc =>
    mem_inf.2 ⟨hH ⟨c, rfl⟩, mem_centralizer_singleton_iff.2 (conj_mul_eq_mul_conj_of_apply_eq hc)⟩
  refine noNormalZ4OrZ2xZ4_of_forall_commute
    (S := {y | ∃ c : C, x c = c ∧ Odd (orderOf c) ∧ (y : MulAut C) = MulAut.conj c}) ?_ ?_
  · rintro y ⟨c, -, hc, hy⟩
    rw [← Subgroup.orderOf_coe, hy]
    exact hc.of_dvd_nat (orderOf_map_dvd _ c)
  · intro β hβ hβ4
    have hβx : (β : MulAut C) * x = x * β := mem_centralizer_singleton_iff.1 (mem_inf.1 β.2).2
    have hfix : ∀ c : C, x c = c → Odd (orderOf c) → (β : MulAut C) c = c := fun c hxc hc =>
      apply_eq_of_mul_conj_eq hinj
        (congrArg Subtype.val (hβ ⟨MulAut.conj c, hmem c hxc⟩ ⟨c, hxc, hc, rfl⟩))
    have hβ4' : orderOf (β : MulAut C) = 2 ^ 2 := by rw [Subgroup.orderOf_coe, hβ4]; norm_num
    have hdvd : orderOf (β : MulAut C) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (pow_two_eq_one_of_conj_le hconj h hx hβ4' hβx hfix)
    rw [Subgroup.orderOf_coe, hβ4] at hdvd
    exact absurd hdvd (by norm_num)

theorem hypothesisOne_of_conj_le {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hcore : ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ centralizer ({α} : Set (MulAut C))) = ⊥)
    {E : Subgroup (MulAut C)}
    (hconj : ∀ P : Subgroup (MulAut C), IsPGroup 2 P →
      ∃ ψ : MulAut C, P.map (MulAut.conj ψ⁻¹).toMonoidHom ≤ E)
    (h : ∀ x ∈ E, orderOf x = 2 → ∀ β ∈ E, β * x = x * β →
      (∀ c : C, x c = c → Odd (orderOf c) → β c = c) → β ^ 2 = 1) :
    HypothesisOne C :=
  hypothesisOne_of_centralizers fun M hM x hxM hx2 =>
    ⟨hcore M hM x hxM hx2, noNormalZ4OrZ2xZ4_of_conj_le hinj hconj h hx2 hM⟩

end OmegaOuter

end CFSG.SeitzReduction
