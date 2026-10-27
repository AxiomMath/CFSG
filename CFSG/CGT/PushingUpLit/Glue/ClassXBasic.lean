module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.CGT.PushingUpLit.SubnormalTwoGroup

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open scoped commutatorElement

section Quotient

theorem center_sl2_eq_bot (F : Type) [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hsq : (r - 1) ^ 2 = 0 := by
    have : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
    rw [this, hr2, h2, zero_mul, sub_zero, one_add_one_eq_two]
    exact h2
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 hsq)
  subst hr1
  apply Subtype.ext
  rw [← hrA]
  simp

theorem quot_normal_bot_or_top {L : Type} [Group L] [Finite L] (h : InClassX L)
    (N : Subgroup (L ⧸ pCore 2 L)) [N.Normal] : N = ⊥ ∨ N = ⊤ := by
  rcases h.2 with ⟨n, hn, φ, -⟩ | ⟨n, hn, φ, -⟩
  · by_cases hn1 : n = 1
    · subst hn1
      have h3 : Nat.card (L ⧸ pCore 2 L) = 3 := by
        rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp only [Fintype.card_fin]
        norm_num [Nat.factorial]
      have : Fact (Nat.card (L ⧸ pCore 2 L)).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
      exact N.eq_bot_or_eq_top_of_prime_card
    · have hs : IsSimpleGroup (alternatingGroup (Fin (2 * n + 1))) :=
        alternatingGroup.isSimpleGroup (by simp; omega)
      have : IsSimpleGroup (L ⧸ pCore 2 L) := φ.isSimpleGroup
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  · rcases h.1.quotient_type with hqs | hprime
    · have hc : Subgroup.center (L ⧸ pCore 2 L) = ⊥ := by
        have h1 := Subgroup.map_center_eq φ
        rw [center_sl2_eq_bot (GaloisField 2 n)] at h1
        exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h1
      have : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ Subgroup.center (L ⧸ pCore 2 L)) := hqs.2.1
      let f : (L ⧸ pCore 2 L) →* (L ⧸ pCore 2 L) ⧸ Subgroup.center (L ⧸ pCore 2 L) :=
        QuotientGroup.mk' _
      have hinj : Function.Injective f := by
        rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hc]
      have hN : (N.map f).Normal := Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h1 | h1
      · left
        exact (Subgroup.map_eq_bot_iff_of_injective N hinj).1 h1
      · right
        rw [← Subgroup.comap_map_eq_self_of_injective hinj N, h1, Subgroup.comap_top]
    · have : Fact (Nat.card (L ⧸ pCore 2 L)).Prime := ⟨hprime⟩
      exact N.eq_bot_or_eq_top_of_prime_card

end Quotient

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem inClassX_normal_le_or_sup {X N : Subgroup G} (hX : InClassX ↥X) (hNX : N ≤ X)
    (hn : X ≤ Subgroup.normalizer (N : Set G)) : N ≤ oTwoIn X ∨ N ⊔ oTwoIn X = X := by
  have hnorm : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hn
  let f : ↥X →* ↥X ⧸ pCore 2 ↥X := QuotientGroup.mk' _
  have hN : ((N.subgroupOf X).map f).Normal :=
    Subgroup.Normal.map hnorm f (QuotientGroup.mk'_surjective _)
  rcases quot_normal_bot_or_top hX ((N.subgroupOf X).map f) with h1 | h1
  · left
    have hle : N.subgroupOf X ≤ pCore 2 ↥X := by
      intro x hx
      have : f x ∈ (N.subgroupOf X).map f := Subgroup.mem_map_of_mem f hx
      rw [h1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    intro g hg
    have hgX : g ∈ X := hNX hg
    have hx : (⟨g, hgX⟩ : ↥X) ∈ N.subgroupOf X := hg
    exact ⟨⟨g, hgX⟩, hle hx, rfl⟩
  · right
    refine le_antisymm (sup_le hNX (oTwoIn_le X)) fun g hg => ?_
    have hmem : f ⟨g, hg⟩ ∈ (N.subgroupOf X).map f := by
      rw [h1]
      trivial
    obtain ⟨x, hx, hxg⟩ := hmem
    have hx2 : (x⁻¹ * ⟨g, hg⟩ : ↥X) ∈ pCore 2 ↥X := by
      have : f (x⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hxg, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have hxN : (x : G) ∈ N := hx
    have hxc : ((x⁻¹ * ⟨g, hg⟩ : ↥X) : G) ∈ oTwoIn X := ⟨_, hx2, rfl⟩
    have : g = (x : G) * ((x⁻¹ * ⟨g, hg⟩ : ↥X) : G) := by simp
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hxN) (Subgroup.mem_sup_right hxc)

theorem isShortGroup_eq_of_sup_oTwoIn {X N : Subgroup G} (hX : IsShortGroup ↥X) (hNX : N ≤ X)
    (hn : X ≤ Subgroup.normalizer (N : Set G)) (hsup : N ⊔ oTwoIn X = X) : N = X := by
  have hNP : N ≤ Subgroup.normalizer (oTwoIn X : Set G) :=
    hNX.trans (normalizer_le_normalizer_oTwoIn X |> fun h => Subgroup.le_normalizer.trans h)
  have hdec : ∀ b ∈ X, ∃ y ∈ N, ∃ q ∈ oTwoIn X, q ∈ X ∧ y * q = b := by
    intro b hb
    have hb' : b ∈ ((N ⊔ oTwoIn X : Subgroup G) : Set G) := by
      show b ∈ N ⊔ oTwoIn X
      rw [hsup]
      exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right N (oTwoIn X) hNP] at hb'
    obtain ⟨y, hy, q, hq, hyq⟩ := hb'
    exact ⟨y, hy, q, hq, oTwoIn_le X hq, hyq⟩
  refine le_antisymm hNX (noTwoQuot_of_short hX N (fun g hg n hn' => ?_) fun g hg => ?_)
  · exact (Subgroup.mem_normalizer_iff.1 (hn hg) n).1 hn'
  · exact SubTwo.exists_pow_mem_of_decomp hn (isPGroup_oTwoIn X) hdec g hg

theorem isShortGroup_ne_bot {X : Subgroup G} (hX : IsShortGroup ↥X) : X ≠ ⊥ := fun h =>
  blockU_ne_bot_of_short hX (le_bot_iff.1 (h ▸ blockU_le X))

theorem isShortGroup_not_isPGroup {X : Subgroup G} (hX : IsShortGroup ↥X) : ¬ IsPGroup 2 X := by
  intro hp
  have hle : X ≤ ⊥ := noTwoQuot_of_short hX ⊥
    (fun g _ n hn => by
      rw [Subgroup.mem_bot] at hn
      simp [hn])
    (fun g hg => by
      obtain ⟨k, hk⟩ := hp ⟨g, hg⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  exact isShortGroup_ne_bot hX (le_bot_iff.1 hle)

theorem isShortGroup_not_commutative {X : Subgroup G} (hX : IsShortGroup ↥X) :
    ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro h
  apply blockU_ne_bot_of_short hX
  unfold blockU
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  exact Subgroup.mem_centralizer_iff.2 fun b hb => h b hb a (oTwoIn_le X ha)

end Ambient

end CFSG.CGT.PushingUpLit.Glue
