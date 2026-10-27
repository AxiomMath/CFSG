module

public import CFSG.LocalAnalysis.GH72.Sec7M1

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Foote81L6.TStruct (IsFourIn)

namespace Sec7

theorem exists_perfect_of_not_isSolvable {K : Type*} [Group K] [Finite K]
    (h : ¬ Group.IsSolvable K) : ∃ P : Subgroup K, ⁅P, P⁆ = P ∧ P ≠ ⊥ := by
  have : Finite (Subgroup K) :=
    Finite.of_injective (fun H : Subgroup K => (H : Set K)) SetLike.coe_injective
  have hanti : Antitone (derivedSeries K) := antitone_nat_of_succ_le fun n => by
    rw [derivedSeries_succ]
    exact commutator_le_self _
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨derivedSeries K n, ?_, fun hb => h (Group.IsSolvable.mk ⟨n, hb⟩)⟩
  rw [← derivedSeries_succ]
  exact (hn (n + 1) n.le_succ).symm

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_quotIs {N : Subgroup G}
    (h : QuotIs (⁅O2 N, O2 N⁆ ⊔ O N) (O N) (fun L _ => Group.IsSolvable L)) :
    Group.IsSolvable N := by
  set N₀ := ⁅O2 N, O2 N⁆ ⊔ O N with hN₀def
  obtain ⟨L, _, f, -, hker, hL⟩ := h
  have hN₀ : Group.IsSolvable N₀ := by
    have hodd : Odd (Nat.card f.ker) := by
      rw [hker]
      have hc : Nat.card ((O N).subgroupOf N₀) = Nat.card (O N ⊓ N₀ : Subgroup G) := by
        rw [← subgroupOf_map_subtype, card_map_of_injective N₀.subtype_injective]
      rw [hc]
      exact Odd.of_dvd_nat (card_O_odd N) (card_dvd_of_le inf_le_left)
    have : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have := hL
    exact solvable_of_ker_le_range f.ker.subtype f (range_subtype f.ker).ge
  by_contra hns
  obtain ⟨P, hP, hP1⟩ := exists_perfect_of_not_isSolvable hns
  set P' : Subgroup G := P.map N.subtype with hP'def
  have hP'N : P' ≤ N := map_subtype_le P
  have hP'perf : ⁅P', P'⁆ = P' := by rw [hP'def, ← map_commutator, hP]
  have hP'N₀ : P' ≤ N₀ := by
    have h1 := CFSG.GorensteinWalter.perfect_subgroup_le_twoResidualOf N P' hP'N
      (Subgroup.isPerfect_iff.2 hP'perf)
    calc P' = ⁅P', P'⁆ := hP'perf.symm
      _ ≤ ⁅O2 N, O2 N⁆ := commutator_mono h1 h1
      _ ≤ N₀ := le_sup_left
  have hsub : ⁅P'.subgroupOf N₀, P'.subgroupOf N₀⁆ = P'.subgroupOf N₀ := by
    apply map_injective N₀.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hP'N₀, hP'perf]
  have hne : P'.subgroupOf N₀ ≠ ⊥ := by
    intro hb
    have : P' = ⊥ := by
      rw [← inf_of_le_left hP'N₀, ← subgroupOf_map_subtype, hb, Subgroup.map_bot]
    exact hP1 ((map_eq_bot_iff_of_injective P N.subtype_injective).mp this)
  exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hsub

end Sec7

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem S_le_normalizer_S₁ : (𝔖.S : Subgroup G) ≤ normalizer (𝔖.S₁ : Set G) := fun _ hs =>
  Subgroup.mem_normalizer_fintype fun _ hg => 𝔖.decomp.conj_mem_left hs hg

theorem S_le_normalizer_S₂ : (𝔖.S : Subgroup G) ≤ normalizer (𝔖.S₂ : Set G) := fun _ hs =>
  Subgroup.mem_normalizer_fintype fun _ hg => 𝔖.decomp.conj_mem_right hs hg

omit [Finite G] in
theorem ne_bot_of_isFourIn {D V : Subgroup G} (hV : IsFourIn D V) : V ≠ ⊥ := by
  intro h
  have h4 := hV.2.2
  rw [h, card_bot] at h4
  exact absurd h4 (by norm_num)

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem prop_7_2_of
    (h47 : ∀ A' : Subgroup G, A' ≤ 𝔖.S → IsE16 A' →
      QuotIs (𝔖.M₀ A') (O (𝔖.M A')) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A') ∧
      𝔖.M A' = 𝔖.M₀ A' ⊔ (𝔖.M A' ⊓ normalizer (A' : Set G)) ∧
      𝔖.M A' = 𝔖.M₀ A' ⊔ (𝔖.M A' ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A', x ≠ 1 → O2 (C x) = (O2 (𝔖.M A') ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A', x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A' ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : ∀ A' : Subgroup G, A' ≤ 𝔖.S → IsE16 A' →
      QuotIs (𝔖.N₀ A') (O (𝔖.N A')) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A') ∧
      𝔖.N A' = 𝔖.N₀ A' ⊔ (𝔖.N A' ⊓ normalizer (A' : Set G)) ∧
      𝔖.N A' = 𝔖.N₀ A' ⊔ (𝔖.N A' ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A', y ≠ 1 → O2 (C y) = (O2 (𝔖.N A') ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A', y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A' ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h49 : ∀ A' : Subgroup G, A' ≤ 𝔖.S → IsE16 A' →
      (∀ T₁ : Subgroup G, T₁ ≤ 𝔖.S₁ → T₁ ≠ ⊥ →
        ∀ K ∈ ({centralizer (T₁ : Set G), normalizer (T₁ : Set G)} : Set (Subgroup G)),
          let K₀ := (K ⊓ 𝔖.M₀ A') ⊔ O K
          K₀ ≤ K ∧ (K₀.subgroupOf K).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ K₀ ∧
            QuotIso K₀ (O K) (𝔖.M₀ A') (O (𝔖.M A'))) ∧
      (∀ T₂ : Subgroup G, T₂ ≤ 𝔖.S₂ → T₂ ≠ ⊥ →
        ∀ K ∈ ({centralizer (T₂ : Set G), normalizer (T₂ : Set G)} : Set (Subgroup G)),
          let K₀ := (K ⊓ 𝔖.N₀ A') ⊔ O K
          K₀ ≤ K ∧ (K₀.subgroupOf K).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ K₀ ∧
            QuotIso K₀ (O K) (𝔖.N₀ A') (O (𝔖.N A'))))
    (h411 : ∀ A' : Subgroup G, A' ≤ 𝔖.S → IsE16 A' →
      (∀ x ∈ 𝔖.X A', x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A' ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A'⁆ ⊔ ⁅⁅D, 𝔖.Y A'⁆, ⁅D, 𝔖.Y A'⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ 𝔖.Y A', y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A' ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A'⁆ ⊔ ⁅⁅D, 𝔖.X A'⁆, ⁅D, 𝔖.X A'⁆⁆ ≤ O (C y)))
    (h413 : ∀ A' : Subgroup G, A' ≤ 𝔖.S → IsE16 A' → ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A') (O (𝔖.M A')) → ∀ x ∈ 𝔖.X A', x ≠ 1 → x ∈ H →
        O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A') (O (𝔖.N A')) → ∀ y ∈ 𝔖.Y A', y ≠ 1 → y ∈ H →
        O H ⊓ C y ≤ O (C y)))
    (h417 : ∀ (H : Subgroup G), H.Normal →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H)
    (h66 : ∀ (s₁ s₂ : G), s₁ ∈ 𝔖.S₁ → s₂ ∈ 𝔖.S₂ → orderOf s₁ = 2 → orderOf s₂ = 2 →
      O (C s₁) ⊓ O (C s₂) = ⊥) :
    (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁) := by
  obtain ⟨-, h₁, h₂⟩ := 𝔖.decomp.e16_split hAS hA
  have hd := 𝔖.decomp
  refine ⟨?_, fun hns => ?_⟩
  ·
    have h75 : ∀ (L : Type) [Group L], IsL2OrA7 L 7 → IsL2OrA7 L 5 := by
      rintro L _ (h | ⟨p, k, hp, hp2, hq, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, k, hp, hp2, le_trans (by norm_num) hq, he⟩
    refine Sec7.exists_M₁_of 𝔖.M 𝔖.M₀ (fun _ => rfl) (fun _ => rfl) hd.dih₁ hd.commute
      𝔖.S_le_normalizer_S₁ hAS hA (isKleinFour_of_isFourIn h₂) (ne_bot_of_isFourIn h₁)
      (fun V hV => ⟨V ⊔ (A ⊓ 𝔖.S₂), sup_le (hV.1.trans hd.le_left) (inf_le_right.trans hd.le_right),
        hd.isE16_sup hV h₂, rfl, hd.sup_inf_left hV.1 inf_le_right,
        hd.sup_inf_right hV.1 inf_le_right⟩)
      (fun T hT hT1 => 𝔖.normalizer_ne_top (Or.inl rfl) h417 hT hT1) ?_ ?_
      (fun A' hA'S hA' _ => (h49 A' hA'S hA').1)
      (fun A' hA'S hA' _ q hq hq1 D hD hDodd hAD =>
        le_sup_left.trans ((h411 A' hA'S hA').2 q hq hq1 D hD hDodd hAD))
      (fun A' hA'S hA' _ H hH => (h413 A' hA'S hA' H hH).1) h66
    · obtain ⟨L, _, f, hf, hker, hL⟩ := (h47 A hAS hA).1
      exact ⟨L, _, f, hf, hker, h75 L hL⟩
    · intro A' hA'S hA' _
      obtain ⟨L, _, f, hf, hker, hL⟩ := (h47 A' hA'S hA').1
      exact ⟨L, _, f, hf, hker, Or.inl (h75 L hL)⟩
  ·
    refine Sec7.exists_M₁_of 𝔖.N 𝔖.N₀ (fun _ => rfl) (fun _ => rfl) hd.isDih₂
      (le_centralizer_iff.mp hd.commute) 𝔖.S_le_normalizer_S₂ hAS hA (isKleinFour_of_isFourIn h₁)
      (ne_bot_of_isFourIn h₂)
      (fun V hV => ⟨V ⊔ (A ⊓ 𝔖.S₁),
        sup_le (hV.1.trans hd.le_right) (inf_le_right.trans hd.le_left),
        by rw [sup_comm]; exact hd.isE16_sup h₁ hV, rfl,
        by rw [sup_comm]; exact hd.sup_inf_right inf_le_right hV.1,
        by rw [sup_comm]; exact hd.sup_inf_left inf_le_right hV.1⟩)
      (fun T hT hT1 => 𝔖.normalizer_ne_top (Or.inr rfl) h417 hT hT1) ?_
      (fun A' hA'S hA' _ => (h48 A' hA'S hA').1)
      (fun A' hA'S hA' _ => (h49 A' hA'S hA').2)
      (fun A' hA'S hA' _ q hq hq1 D hD hDodd hAD =>
        le_sup_left.trans ((h411 A' hA'S hA').1 q hq hq1 D hD hDodd hAD))
      (fun A' hA'S hA' _ H hH => (h413 A' hA'S hA' H hH).2)
      (fun p q hp hq hp2 hq2 => by rw [inf_comm]; exact h66 q p hq hp hq2 hp2)
    obtain ⟨L, _, f, hf, hker, hL⟩ := (h48 A hAS hA).1
    rcases hL with hL | hL
    · exact ⟨L, _, f, hf, hker, hL⟩
    refine absurd (Sec7.isSolvable_of_quotIs (N := 𝔖.N A) ⟨L, _, f, hf, hker, ?_⟩) hns
    have := hL
    have : Finite L := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (IsPGroup.of_card (p := 2) (G := L) (n := 2)
      (by rw [IsKleinFour.card_four]; norm_num)).isNilpotent
    infer_instance

end Sec4Setting

end CFSG.GH72
