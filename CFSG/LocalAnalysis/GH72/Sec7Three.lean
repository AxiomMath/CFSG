module

public import CFSG.LocalAnalysis.GH72.Sec7Fusion
public import CFSG.LocalAnalysis.GH72.StrongEmbed
public import CFSG.LocalAnalysis.GH72.Sec7Tools

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped MatrixGroups

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem M₀_le_M : 𝔖.M₀ A ≤ 𝔖.M A :=
  sup_le ((commutator_le_self _).trans (map_subtype_le _)) (Sec7.O_le _)

theorem N₀_le_N : 𝔖.N₀ A ≤ 𝔖.N A :=
  sup_le ((commutator_le_self _).trans (map_subtype_le _)) (Sec7.O_le _)

omit [Finite G] in
theorem mul_self_of_isE16 (hA : IsE16 A) {a : G} (ha : a ∈ A) : a * a = 1 := by
  have := hA.1.2 a ha
  rwa [pow_two] at this

omit [Finite G] in
theorem orderOf_eq_two_of_isE16 (hA : IsE16 A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact mul_self_of_isE16 hA ha) ha1

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

omit hAS in
theorem false_of_le
    (h412 : ∀ (H : Subgroup G), H ≠ ⊤ → 𝔖.M A ≤ H → 𝔖.N A ≤ H →
      ∀ t ∈ H, orderOf t = 2 → ∃ h ∈ H, h * t * h⁻¹ ∈ A)
    (h415 : ∀ (a : G), a ∈ A → a ≠ 1 →
      C a ≤ xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) ⊔
        (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)))
    (h66 : ∀ (s₁ s₂ : G), s₁ ∈ 𝔖.S₁ → s₂ ∈ 𝔖.S₂ → orderOf s₁ = 2 → orderOf s₂ = 2 →
      O (C s₁) ⊓ O (C s₂) = ⊥)
    {K : Subgroup G} (hK : K ≠ ⊤) (hSK : (𝔖.S : Subgroup G) ≤ K)
    (hNS : normalizer ((𝔖.S : Subgroup G) : Set G) ≤ K) (hMK : 𝔖.M A ≤ K) (hNK : 𝔖.N A ≤ K)
    (hAK : normalizer (A : Set G) ≤ K) : False := by
  have hCa : ∀ a ∈ A, a ≠ 1 → C a ≤ K := by
    intro a ha ha1
    have hxy : xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) = ⊥ := by
      refine eq_bot_iff.mpr (iSup₂_le fun x hx => iSup_le fun hx1 => iSup₂_le fun y hy =>
        iSup_le fun hy1 => ?_)
      show O (C a) ⊓ O (C x) ⊓ O (C y) ≤ ⊥
      rw [inf_assoc]
      refine inf_le_right.trans (le_of_eq ?_)
      exact h66 x y hx.2 hy.2 (orderOf_eq_two_of_isE16 hA hx.1 hx1)
        (orderOf_eq_two_of_isE16 hA hy.1 hy1)
    refine (h415 a ha ha1).trans ?_
    rw [hxy, bot_sup_eq]
    exact sup_le (sup_le (inf_le_right.trans (𝔖.M₀_le_M.trans hMK))
      (inf_le_right.trans (𝔖.N₀_le_N.trans hNK))) (inf_le_right.trans hAK)
  have hC : ∀ t ∈ K, orderOf t = 2 → C t ≤ K := by
    intro t ht ht2
    obtain ⟨h, hh, hht⟩ := h412 K hK hMK hNK t ht ht2
    have ha1 : h * t * h⁻¹ ≠ 1 := by
      intro h1
      have : t = 1 := by
        calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    intro c hc
    have hc' : h * c * h⁻¹ ∈ C (h * t * h⁻¹) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      calc h * c * h⁻¹ * (h * t * h⁻¹) = h * (c * t) * h⁻¹ := by group
        _ = h * (t * c) * h⁻¹ := by rw [hc]
        _ = h * t * h⁻¹ * (h * c * h⁻¹) := by group
    have := hCa _ hht ha1 hc'
    have heq : c = h⁻¹ * (h * c * h⁻¹) * h := by group
    rw [heq]
    exact mul_mem (mul_mem (inv_mem hh) this) hh
  exact not_stronglyEmbedded_of_productFusion 𝔖.decomp 𝔖.fusion K
    (stronglyEmbedded_of_centralizers K hK 𝔖.S hSK hNS hC)

omit hAS hA in
theorem not_isSolvable_psl2_five : ¬ Group.IsSolvable (PSL(2, ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : 3 < Nat.card (ZMod 5) := by rw [Nat.card_zmod]; norm_num
  have : IsSimpleGroup (PSL(2, ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
  have hperf :=
    (CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod 5) hcard).commutator_eq_top
  intro hsolv
  have hne : (⊤ : Subgroup (PSL(2, ZMod 5))) ≠ ⊥ := top_ne_bot
  exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne (by rw [← _root_.commutator_def, hperf])

omit hAS hA in
theorem not_quotIs_psl2_five_of_isSolvable (hsolv : Group.IsSolvable (𝔖.N A)) :
    ¬ QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => Nonempty (L ≃* PSL(2, ZMod 5))) := by
  rintro ⟨L, _, f, hf, -, ⟨e⟩⟩
  have : Group.IsSolvable (𝔖.N₀ A) :=
    solvable_of_solvable_injective (f := inclusion 𝔖.N₀_le_N) (inclusion_injective _)
  have : Group.IsSolvable L := solvable_of_surjective hf
  exact not_isSolvable_psl2_five (solvable_of_surjective (f := e.toMonoidHom) e.surjective)

theorem prop_7_3_of
    (h412 : ∀ (H : Subgroup G), H ≠ ⊤ → 𝔖.M A ≤ H → 𝔖.N A ≤ H →
      ∀ t ∈ H, orderOf t = 2 → ∃ h ∈ H, h * t * h⁻¹ ∈ A)
    (h415 : ∀ (a : G), a ∈ A → a ≠ 1 →
      C a ≤ xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) ⊔
        (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)))
    (h416 : 𝔖.M A = ⨆ (T₂ : Subgroup G) (_ : T₂ ≤ 𝔖.S₂) (_ : T₂ ≠ ⊥),
        𝔖.M A ⊓ normalizer (T₂ : Set G) ∧
      (¬ QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => Nonempty (L ≃* PSL(2, ZMod 5))) →
        𝔖.N A = ⨆ (T₁ : Subgroup G) (_ : T₁ ≤ 𝔖.S₁) (_ : T₁ ≠ ⊥),
          𝔖.N A ⊓ normalizer (T₁ : Set G)))
    (h66 : ∀ (s₁ s₂ : G), s₁ ∈ 𝔖.S₁ → s₂ ∈ 𝔖.S₂ → orderOf s₁ = 2 → orderOf s₂ = 2 →
      O (C s₁) ⊓ O (C s₂) = ⊥) :
    (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
    (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal) := by
  have hY : 𝔖.Y A ≠ ⊥ ∧ 𝔖.Y A ≤ 𝔖.S₂ := by
    obtain ⟨-, -, h₂⟩ := 𝔖.decomp.e16_split hAS hA
    refine ⟨fun h => ?_, inf_le_right⟩
    have h4 := h₂.2.2
    rw [show A ⊓ 𝔖.S₂ = 𝔖.Y A from rfl, h, card_bot] at h4
    exact absurd h4 (by norm_num)
  have hX : 𝔖.X A ≠ ⊥ ∧ 𝔖.X A ≤ 𝔖.S₁ := by
    obtain ⟨-, h₁, -⟩ := 𝔖.decomp.e16_split hAS hA
    refine ⟨fun h => ?_, inf_le_right⟩
    have h4 := h₁.2.2
    rw [show A ⊓ 𝔖.S₁ = 𝔖.X A from rfl, h, card_bot] at h4
    exact absurd h4 (by norm_num)
  have hS₁ne : 𝔖.S₁ ≠ ⊥ := fun h => hX.1 (eq_bot_iff.mpr (h ▸ hX.2))
  have hS₂ne : 𝔖.S₂ ≠ ⊥ := fun h => hY.1 (eq_bot_iff.mpr (h ▸ hY.2))
  have hS : (𝔖.S : Subgroup G) = 𝔖.S₁ ⊔ 𝔖.S₂ := 𝔖.decomp.sup_eq.symm
  refine ⟨fun hsolv N₁ hN₁ => ?_, fun hsolv M₁ hM₁ => ?_⟩
  · obtain ⟨hN₁N, hN₁n, -, hsyl, -, hT₂⟩ := hN₁
    by_contra hnorm
    set K := normalizer (N₁ : Set G) with hKdef
    have hK : K ≠ ⊤ := fun h => hnorm (normalizer_eq_top_iff.mp h)
    have hT : ∀ T₂ : Subgroup G, T₂ ≤ 𝔖.S₂ → T₂ ≠ ⊥ → normalizer (T₂ : Set G) ≤ K := fun T₂ h h' =>
      (normal_subgroupOf_iff_le_normalizer (hT₂ T₂ h h').1).mp (hT₂ T₂ h h').2
    have hS₂K : 𝔖.S₂ ≤ K := le_normalizer.trans (hT 𝔖.S₂ le_rfl hS₂ne)
    have hS₁K : 𝔖.S₁ ≤ K := hsyl.le.trans le_normalizer
    refine 𝔖.false_of_le hA h412 h415 h66 hK (hS ▸ sup_le hS₁K hS₂K)
      ((𝔖.normalizer_S_le (Or.inr rfl)).trans (hT 𝔖.S₂ le_rfl hS₂ne)) ?_
      ((normal_subgroupOf_iff_le_normalizer hN₁N).mp hN₁n)
      ((𝔖.normalizer_A_le (Or.inr rfl) hAS hA).trans (hT _ hY.2 hY.1))
    rw [h416.1]
    exact iSup₂_le fun T₂ hT₂' => iSup_le fun hT₂ne => inf_le_right.trans (hT T₂ hT₂' hT₂ne)
  · obtain ⟨hM₁M, hM₁n, -, hsyl, -, hT₁⟩ := hM₁
    by_contra hnorm
    set K := normalizer (M₁ : Set G) with hKdef
    have hK : K ≠ ⊤ := fun h => hnorm (normalizer_eq_top_iff.mp h)
    have hT : ∀ T₁ : Subgroup G, T₁ ≤ 𝔖.S₁ → T₁ ≠ ⊥ → normalizer (T₁ : Set G) ≤ K := fun T₁ h h' =>
      (normal_subgroupOf_iff_le_normalizer (hT₁ T₁ h h').1).mp (hT₁ T₁ h h').2
    have hS₁K : 𝔖.S₁ ≤ K := le_normalizer.trans (hT 𝔖.S₁ le_rfl hS₁ne)
    have hS₂K : 𝔖.S₂ ≤ K := hsyl.le.trans le_normalizer
    refine 𝔖.false_of_le hA h412 h415 h66 hK (hS ▸ sup_le hS₁K hS₂K)
      ((𝔖.normalizer_S_le (Or.inl rfl)).trans (hT 𝔖.S₁ le_rfl hS₁ne))
      ((normal_subgroupOf_iff_le_normalizer hM₁M).mp hM₁n) ?_
      ((𝔖.normalizer_A_le (Or.inl rfl) hAS hA).trans (hT _ hX.2 hX.1))
    rw [h416.2 (𝔖.not_quotIs_psl2_five_of_isSolvable hsolv)]
    exact iSup₂_le fun T₁ hT₁' => iSup_le fun hT₁ne => inf_le_right.trans (hT T₁ hT₁' hT₁ne)

end Sec4Setting

end CFSG.GH72
