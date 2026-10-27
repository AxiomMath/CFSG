module

public import CFSG.Goldschmidt75.Sec43

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.center_eq_bot (h : MinCE G T S₁ S₂) : center G = ⊥ := by
  have := h.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h0 | h0
  · exact h0
  · exfalso
    apply h.fail
    have hle : normalClosure (S₁ : Set G) ≤ centralizer (normalClosure (S₂ : Set G) : Set G) :=
      fun x _ => mem_centralizer_iff.mpr fun y _ => (mem_center_iff.mp (h0 ▸ mem_top x) y)
    rw [commutator_eq_bot_iff_le_centralizer.mpr hle]
    exact bot_le

theorem le_centralizer_or_of_commutator_eq_bot {L : Type*} [Group L] [Finite L]
    {H₁ H₂ K : Subgroup L} (hH₁ : H₁.Normal) (hH₂ : H₂.Normal) (hH : ⁅H₁, H₂⁆ = ⊥)
    (hK : CFSG.IsComponent K) :
    H₁ ≤ centralizer (K : Set L) ∨ H₂ ≤ centralizer (K : Set L) := by
  have key : ∀ {H : Subgroup L}, ⁅K, H⁆ = ⊥ → H ≤ centralizer (K : Set L) := fun h1 =>
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h1)
  rcases CFSG.LocalCores.component_normal_subgroup hK hH₁ with h1 | h1
  · rcases CFSG.LocalCores.component_normal_subgroup hK hH₂ with h2 | h2
    · exfalso
      obtain ⟨a, b, hab⟩ := hK.1.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center K) b
      apply hab
      rw [← map_mul, ← map_mul]
      congr 1
      have hxy : ⁅(x : L), (y : L)⁆ = 1 := by
        have := commutator_mem_commutator (h1 x.2) (h2 y.2)
        rwa [hH, mem_bot] at this
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact commutatorElement_eq_one_iff_mul_comm.mp hxy)
    · exact Or.inr (key h2)
  · exact Or.inl (key h1)

theorem MinCE.coreSep (h : MinCE G T S₁ S₂) : CoreSep S₁ S₂ := by
  intro t ht ht2 K hK
  set L := centralizer ({t} : Set G) with hL
  have hLtop : L ≠ ⊤ := by
    intro htop
    have htc : t ∈ center G := mem_center_iff.mpr fun g => by
      have hg : g ∈ L := by rw [htop]; exact mem_top g
      exact mem_centralizer_singleton_iff.mp hg
    rw [h.center_eq_bot, mem_bot] at htc
    exact ne_one_of_orderOf_eq_two ht2 htc
  obtain ⟨P, Q₁, Q₂, hRQ₁, hRQ₂, hQ₁L, hQ₂L, hQ₁P, hQ₂P, hQ₁c, hQ₂c, hQc, hQd⟩ :=
    h.exists_hat (L := L) (R₁ := S₁ ⊓ L) (R₂ := S₂ ⊓ L) inf_le_left inf_le_left inf_le_right
      inf_le_right
  have hA := thmA_in (h.ihG L (card_lt_of_ne_top hLtop)) P hQ₁P hQ₂P hQ₁c hQ₂c hQc hQd
  have hnormal : ∀ Q : Subgroup G, (barOf L (normalClosureIn L Q)).Normal := by
    intro Q
    have hn : ((normalClosureIn L Q).subgroupOf L).Normal :=
      (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr
        (le_normalizer_normalClosureIn L Q)
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hcomm : ⁅barOf L (normalClosureIn L Q₁), barOf L (normalClosureIn L Q₂)⁆ = ⊥ := by
    have h₁ : normalClosureIn L Q₁ ≤ L := map_subtype_le _
    have h₂ : normalClosureIn L Q₂ ≤ L := map_subtype_le _
    rw [← G37.barOf_commutator h₁ h₂, G37.barOf_eq_bot_iff
      ((commutator_mono h₁ h₂).trans (commutator_le_self L))]
    exact hA
  have hS : ∀ {S Q : Subgroup G}, S ⊓ L ≤ Q → barOf L S ≤ barOf L (normalClosureIn L Q) := by
    rintro S Q hSQ _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr ⟨x, subset_normalClosure (mem_subgroupOf.mpr
      (hSQ (mem_inf.mpr ⟨mem_subgroupOf.mp hx, x.2⟩))), rfl⟩, rfl⟩
  rcases le_centralizer_or_of_commutator_eq_bot (hnormal Q₁) (hnormal Q₂) hcomm hK with h1 | h1
  · exact Or.inl ((hS hRQ₁).trans h1)
  · exact Or.inr ((hS hRQ₂).trans h1)

end CFSG.Goldschmidt75
