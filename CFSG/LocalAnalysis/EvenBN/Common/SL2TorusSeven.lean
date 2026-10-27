module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusSix

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix Subgroup
open scoped MatrixGroups

theorem card_ker_powMonoidHom_of_dvd {A : Type*} [CommGroup A] [IsCyclic A] [Finite A] {m : ℕ}
    (hm : m ∣ Nat.card A) : Nat.card (powMonoidHom m : A →* A).ker = m := by
  rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hm]

theorem exists_ne_one_mem_centralizer_of_not_dvd {G : Type*} [Group G] {M T Y : Subgroup G}
    [Finite Y] [Finite T] (hTM : T ≤ normalizer (M : Set G)) (hYM : Y ≤ normalizer (M : Set G))
    (hinner : ∀ y ∈ Y, ∃ τ ∈ T, ∀ x ∈ M, y * x * y⁻¹ = τ * x * τ⁻¹)
    (hdvd : ¬ Nat.card Y ∣ Nat.card T) : ∃ y ∈ Y, y ≠ 1 ∧ y ∈ centralizer (M : Set G) := by
  set φY : Y →* MulAut M := M.normalizerMonoidHom.comp (Subgroup.inclusion hYM) with hφY
  set φT : T →* MulAut M := M.normalizerMonoidHom.comp (Subgroup.inclusion hTM) with hφT
  have hle : φY.range ≤ φT.range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨τ, hτ, hτx⟩ := hinner y y.2
    refine ⟨⟨τ, hτ⟩, ?_⟩
    ext x
    exact (hτx x x.2).symm
  have hdvdT : Nat.card φY.range ∣ Nat.card T :=
    (Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd φT)
  by_contra hcon
  have hker : φY.ker = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rw [MonoidHom.mem_ker] at hy
    rw [mem_bot]
    by_contra hy1
    refine hcon ⟨y, y.2, fun h => hy1 (Subtype.ext h), mem_centralizer_iff.2 fun x hx => ?_⟩
    have h0 := congrArg Subtype.val (DFunLike.congr_fun hy (⟨x, hx⟩ : M))
    have h' : (y : G) * x * (y : G)⁻¹ = x := h0
    exact (mul_inv_eq_iff_eq_mul.1 h').symm
  have hcard : Nat.card φY.range = Nat.card Y := by
    have := Subgroup.card_ker_mul_card_range φY
    rwa [hker, Subgroup.card_bot, one_mul] at this
  exact hdvd (hcard ▸ hdvdT)

variable {k : Type*} [Field k] [CharP k 2]

theorem exists_conj_eq_of_odd_of_mem_normalizer [Finite k] {n : ℕ}
    (hk : Nat.card k = (2 ^ n) ^ 2) (h8 : 8 ≤ Nat.card k) {G : Type*} [Group G]
    {X W : Subgroup G} (ψ : X ≃* SL(2, k)) {d : G} (hdX : d ∈ X) (hd1 : d ≠ 1)
    (hd : orderOf d = 2 ^ n - 1) (hWX : W ≤ X) (hW : Nat.card W = Nat.card k)
    (hdW : d ∈ normalizer (W : Set G)) {g : G} (hg : Odd (orderOf g))
    (hgX : g ∈ normalizer (X : Set G)) (hgW : g ∈ normalizer (W : Set G))
    (hgd : g * d = d * g) :
    ∃ τ ∈ X, τ * d = d * τ ∧ ∀ x ∈ X, g * x * g⁻¹ = τ * x * τ⁻¹ := by
  set d' : X := ⟨d, hdX⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hord : orderOf d' = 2 ^ n - 1 := by rw [← Subgroup.orderOf_coe]; exact hd
  have hq : Nat.card k - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = t + 1 := ⟨2 ^ n - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    rw [hk, ht, Nat.add_sub_cancel, show (t + 1) ^ 2 = t * (t + 1 + 1) + 1 by ring,
      Nat.add_sub_cancel]
  have hd'q : d' ^ (Nat.card k - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hord ▸ hq ▸ dvd_mul_right _ _)
  obtain ⟨ψ₁, μ, -, -, hC⟩ := exists_mulEquiv_map_centralizer_zpowers ψ hd'1 hd'q
  have hmemC : ∀ y : X, y ∈ centralizer (zpowers d' : Set X) ↔ (y : G) * d = d * y := by
    intro y
    rw [centralizer_zpowers, mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set gN : normalizer (X : Set G) := ⟨g, hgX⟩ with hgN
  set φ : MulAut SL(2, k) := MulAut.congr ψ₁ (X.normalizerMonoidHom gN) with hφ
  have hφX : ∀ y : X, φ (ψ₁ y) = ψ₁ (X.normalizerMonoidHom gN y) := fun y => by
    simp [hφ, MulAut.congr_apply]
  have hfix : ∀ x ∈ torusSL k, φ x = x := by
    rw [← hC]
    rintro _ ⟨y, hy, rfl⟩
    have hgy : g * y = y * g := commute_of_odd_of_mem_normalizer hk ψ hdX hd1 hd hWX hW hdW hg
      hgX hgW hgd y.2 ((hmemC y).1 hy)
    show φ (ψ₁ y) = ψ₁ y
    rw [hφX]
    congr 1
    apply Subtype.ext
    rw [coe_normalizerMonoidHom_apply]
    show g * y * g⁻¹ = y
    rw [hgy, mul_inv_cancel_right]
  obtain ⟨τ', hτ', hτφ⟩ := exists_eq_conj_of_forall_torusSL h8 φ hfix
  have hτC : ψ₁.symm τ' ∈ centralizer (zpowers d' : Set X) := by
    rw [← hC] at hτ'
    obtain ⟨y, hy, rfl⟩ := hτ'
    simpa using hy
  refine ⟨(ψ₁.symm τ' : G), (ψ₁.symm τ').2, (hmemC _).1 hτC, fun x hx => ?_⟩
  have e := hτφ (ψ₁ ⟨x, hx⟩)
  rw [hφX] at e
  have e2 : X.normalizerMonoidHom gN ⟨x, hx⟩ = ψ₁.symm τ' * ⟨x, hx⟩ * (ψ₁.symm τ')⁻¹ := by
    apply ψ₁.injective
    rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have := congrArg Subtype.val e2
  rw [coe_normalizerMonoidHom_apply] at this
  exact this

end CFSG.LocalAnalysis.EvenBN.Common
