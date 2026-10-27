module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescKind
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescXOut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5KindCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5GrpCentral
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem kind5_of_kindM_desc {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hM : Asc82Tab6M) (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) (hs2 : orderOf s = 2)
    (hnc : s ∉ centralizer (L : Set G)) {k : ℕ} (hk : k < 6)
    (h : KindM (DescL L t) (descElt L t s hs) k) : Kind5 L s k :=
  (t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc hk).mpr h

theorem t5_kind5_ne_central {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsOm6Z2 L)
    {s : G} (hs2 : orderOf s = 2) (hs : s ∈ normalizer (L : Set G)) {i : ℕ} (hi : i < 6)
    (h : Kind5 L s i) : s ∉ centralizer (L : Set G) := by
  interval_cases i
  · exact h.2
  · exact asc82Tab5_kind_ne_central_of G L hL s hs2 hs (Or.inl h)
  · exact asc82Tab5_kind_ne_central_of G L hL s hs2 hs (Or.inr (Or.inl h))
  · exact asc82Tab5_kind_ne_central_of G L hL s hs2 hs (Or.inr (Or.inr (Or.inl h)))
  · exact asc82Tab5_kind_ne_central_of G L hL s hs2 hs (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact asc82Tab5_kind_ne_central_of G L hL s hs2 hs (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem asc82Tab5_classify_of (hM : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        s ∈ centralizer (L : Set G) ∨ Kind5 L s 0 ∨ Kind5 L s 1 ∨ Kind5 L s 2 ∨ Kind5 L s 3 ∨
          Kind5 L s 4 ∨ Kind5 L s 5
  := by
  intro G _ _ L hL s hs2 hs
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  by_cases hc : s ∈ centralizer (L : Set G)
  · exact Or.inl hc
  · have hs2' : orderOf (descElt L t s hs) = 2 := t5_desc_orderOf hL ht ht2 hs hs2 hc
    have hs' : descElt L t s hs ∈ normalizer (DescL L t : Set (DescG L t)) :=
      t5_desc_mem_normalizer L t hs
    rcases hM.classify (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2)
        (descElt L t s hs) hs2' hs' with hcen | h0 | h1 | h4 | h2 | h3 | h5
    · exact absurd ((t5_desc_mem_centralizer_iff hL ht ht2 hs).mp hcen) hc
    · exact Or.inr (Or.inl (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 0) (by norm_num) h0))
    · exact Or.inr (Or.inr (Or.inl
        (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 1) (by norm_num) h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 4) (by norm_num) h4))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 2) (by norm_num) h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 3) (by norm_num) h3)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 5) (by norm_num) h5))))))

theorem asc82Tab5_excl_of (hM : Asc82Tab6M) (hX : Asc82Tab6MExcl) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        ∀ i j : ℕ, i < 6 → j < 6 → i ≠ j → Kind5 L s i → ¬ Kind5 L s j
  := by
  intro G _ _ L hL s hs2 hs i j hi hj hij hKi hKj
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  have hnc : s ∉ centralizer (L : Set G) := t5_kind5_ne_central hL hs2 hs hi hKi
  have hs2' : orderOf (descElt L t s hs) = 2 := t5_desc_orderOf hL ht ht2 hs hs2 hnc
  have hs' : descElt L t s hs ∈ normalizer (DescL L t : Set (DescG L t)) :=
    t5_desc_mem_normalizer L t hs
  exact hX (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2) (descElt L t s hs) hs2' hs'
    i j hi hj hij ((t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc hi).mp hKi)
    ((t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc hj).mp hKj)

theorem asc82Tab5_layer_trivial_of (hM : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
        layerCent L s = ⊥ → Kind5 L s 0 ∨ Kind5 L s 3
  := by
  intro G _ _ L hL s hs2 hs hbot
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  by_cases hc : s ∈ centralizer (L : Set G)
  · exact absurd hbot (sec5_layerCent_ne_bot_of_mem_centralizer hL.1 hc)
  · have hs2' : orderOf (descElt L t s hs) = 2 := t5_desc_orderOf hL ht ht2 hs hs2 hc
    have hs' : descElt L t s hs ∈ normalizer (DescL L t : Set (DescG L t)) :=
      t5_desc_mem_normalizer L t hs
    have hbot' : layerCent (DescL L t) (descElt L t s hs) = ⊥ :=
      (t5_desc_layerCent_bot_iff hL ht ht2 hs).mpr hbot
    rcases (hM.layer_trivial (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2)
        (descElt L t s hs) hs2' hs').mp hbot' with h0 | h3
    · exact Or.inl (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 0) (by norm_num) h0)
    · exact Or.inr (kind5_of_kindM_desc hM hL ht ht2 hs hs2 hc (k := 3) (by norm_num) h3)

theorem asc82Tab5_xout_eq_of (hM : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
        XOut L s = layerCent L s
  := by
  intro G _ _ L hL s hs2 hs hne
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  by_cases hc : s ∈ centralizer (L : Set G)
  · have hlayer : layerCent L s = L := sec5_layerCent_of_mem_centralizer hL.1 hc
    have hinf : L ⊓ centralizer ({s} : Set G) = L := by
      rw [inf_eq_left]
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hc x hx
    rw [hlayer]
    unfold XOut
    rw [hinf, t5_xout_central hL.1 ht ht2]
  · have hne' : layerCent (DescL L t) (descElt L t s hs) ≠ ⊥ := fun h =>
      hne ((t5_desc_layerCent_bot_iff hL ht ht2 hs).mp h)
    exact t5_desc_xout_eq_layer hL ht ht2 hs
      (hM.xout_eq (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2)
        (descElt L t s hs) (t5_desc_orderOf hL ht ht2 hs hs2 hc)
        (t5_desc_mem_normalizer L t hs) hne')

theorem asc82Tab5_xout_i3_of (hM : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → Kind5 L s 3 →
        XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G)))
  := by
  intro G _ _ L hL s hs2 hs hk
  obtain ⟨t, ht, ht2⟩ := t5_exists_central_involution hL
  have hnc : s ∉ centralizer (L : Set G) :=
    t5_kind5_ne_central hL hs2 hs (i := 3) (by norm_num) hk
  have hs2' : orderOf (descElt L t s hs) = 2 := t5_desc_orderOf hL ht ht2 hs hs2 hnc
  have hs' : descElt L t s hs ∈ normalizer (DescL L t : Set (DescG L t)) :=
    t5_desc_mem_normalizer L t hs
  have hk' : ∃ α : ℤˣ, InducesTypeSome (DescL L t) (descElt L t s hs) 6 (-1) 3 α :=
    (t5_desc_kind_iff hM hL ht ht2 hs hs2 hnc (k := 3) (by norm_num)).mp hk
  exact t5_desc_xout_eq_pCore hL ht ht2 hs
    (hM.xout_i3 (DescG L t) (DescL L t) (t5_isOm6M_descL hL ht ht2)
      (descElt L t s hs) hs2' hs' hk')

end CFSG.OddStandard.SmallF3.Omega
