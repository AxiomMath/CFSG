module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ : Type} [Group Γ] [Finite Γ] {D : TabData} {elt : ℕ → Γ}

private theorem map_subtype_injective {A : Subgroup Γ} :
    Function.Injective (Subgroup.map (A.subtype : ↥A →* Γ)) := by
  intro P Q h
  apply le_antisymm
  · intro x hx
    have hx' : A.subtype x ∈ Q.map A.subtype := by
      rw [← h]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro x hx
    have hx' : A.subtype x ∈ P.map A.subtype := by
      rw [h]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem sectionalTwoRank_eq_of_data {S X : Subgroup Γ} (hS : IsPGroup 2 S) (hXS : X ≤ S)
    {k : ℕ} (hk : 1 ≤ k)
    (hup : ∀ P : Subgroup Γ, P ≤ S → ∃ s : Finset Γ, s.card ≤ k ∧ closure (s : Set Γ) = P)
    {Y : Type} [Group Y] (π : ↥X →* Y) (hπ : Function.Surjective π)
    (hY : ∀ s : Finset Y, s.card ≤ k - 1 → closure (s : Set Y) ≠ ⊤) :
    GH74.sectionalTwoRank ↥S = k := by
  classical
  have hupS : GH74.SectionalTwoRankLE ↥S k := by
    intro P _
    obtain ⟨s, hscard, hsc⟩ := hup (P.map S.subtype) (Subgroup.map_subtype_le P)
    have hlift : ∀ x ∈ s, ∃ p : ↥S, S.subtype p = x := by
      intro x hx
      have hx' : x ∈ P.map S.subtype := hsc ▸ Subgroup.subset_closure hx
      obtain ⟨p, _, hp⟩ := hx'
      exact ⟨p, hp⟩
    let f : Γ → ↥S := fun x => if h : ∃ p : ↥S, S.subtype p = x then h.choose else 1
    have hf : ∀ x ∈ s, S.subtype (f x) = x := by
      intro x hx
      have h : f x = (hlift x hx).choose := dif_pos (hlift x hx)
      rw [h]; exact (hlift x hx).choose_spec
    let s' : Finset ↥S := s.image f
    have hs'card : s'.card ≤ k := le_trans Finset.card_image_le hscard
    refine ⟨s', hs'card, ?_⟩
    apply map_subtype_injective
    rw [MonoidHom.map_closure]
    have himg : S.subtype '' (s' : Set ↥S) = (s : Set Γ) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        rw [hf z hz]
        exact Finset.mem_coe.mpr hz
      · intro hx
        exact ⟨f x, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩), hf x hx⟩
    rw [himg, hsc]
  have hlow : ∀ r ≤ k - 1, ¬ GH74.SectionalTwoRankLE ↥S r := by
    intro r hr hLE
    have hPpg : IsPGroup 2 (X.subgroupOf S) :=
      hS.of_injective (Subgroup.subtype (X.subgroupOf S)) (fun a b h => Subtype.ext h)
    obtain ⟨s', hs'card, hs'clos⟩ := hLE (X.subgroupOf S) hPpg
    let e := Subgroup.subgroupOfEquivOfLe hXS
    let φ : ↥(X.subgroupOf S) →* Y := π.comp e.toMonoidHom
    have hφsurj : Function.Surjective φ := by
      intro y
      obtain ⟨x, hx⟩ := hπ y
      exact ⟨e.symm x, by simp [φ, hx]⟩
    let s₁ : Finset ↥(X.subgroupOf S) :=
      s'.attach.image (fun a => ⟨a.1, by
        have h : a.1 ∈ closure (s' : Set ↥S) := Subgroup.subset_closure a.2
        rwa [hs'clos] at h⟩)
    have hs₁card : s₁.card ≤ s'.card := by
      calc s₁.card ≤ s'.attach.card := Finset.card_image_le
        _ = s'.card := Finset.card_attach
    have hs₁top : Subgroup.closure (s₁ : Set ↥(X.subgroupOf S)) = ⊤ := by
      apply map_subtype_injective (A := X.subgroupOf S)
      rw [MonoidHom.map_closure]
      have himg : (Subgroup.subtype (X.subgroupOf S)) '' (s₁ : Set ↥(X.subgroupOf S)) =
          (s' : Set ↥S) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
          rw [← ha]
          exact a.2
        · intro hx
          refine ⟨⟨x, ?_⟩, ?_, rfl⟩
          · have h : x ∈ closure (s' : Set ↥S) := Subgroup.subset_closure hx
            rwa [hs'clos] at h
          · exact Finset.mem_coe.mpr (Finset.mem_image.mpr
              ⟨⟨x, hx⟩, Finset.mem_attach .., Subtype.ext rfl⟩)
      have hmap_top : (⊤ : Subgroup ↥(X.subgroupOf S)).map
          (Subgroup.subtype (X.subgroupOf S)) = X.subgroupOf S := by
        apply le_antisymm
        · exact Subgroup.map_subtype_le ⊤
        · intro x hx
          exact ⟨⟨x, hx⟩, trivial, rfl⟩
      rw [himg, hs'clos, hmap_top]
    have htsup : Subgroup.closure ((s₁.image φ : Finset Y) : Set Y) = ⊤ := by
      rw [Finset.coe_image, ← MonoidHom.map_closure, hs₁top,
        Subgroup.map_top_of_surjective φ hφsurj]
    exact hY (s₁.image φ) (le_trans Finset.card_image_le (le_trans hs₁card
      (le_trans hs'card hr))) htsup
  have hk_mem : k ∈ {r | GH74.SectionalTwoRankLE ↥S r} := hupS
  rw [GH74.sectionalTwoRank]
  apply le_antisymm
  · exact Nat.sInf_le hk_mem
  · apply le_csInf ⟨k, hk_mem⟩
    intro r hr
    by_contra hlt
    push Not at hlt
    exact hlow r (by omega) hr

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
