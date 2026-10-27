module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Merge
public import CFSG.GH74.Generic.Sections
public import CFSG.GH74.GLS.LU.Local.A3Reduce

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.IVK
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def IVK_9_5At_gh (q : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → IsKGroupNative J → GHList J →
    ∀ z : J, orderOf z = 2 → Odd q →
      HasSL2Model ↥(Ez z) (fun r => r = q) →
      (∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 J ε q

theorem IVK_9_5At_gh_of {q : ℕ} (h : IVK_9_5At q) : IVK_9_5At_gh q :=
  fun J _ _ hs hK _ z hz hodd hsl hcyc => h J hs hK z hz hodd hsl hcyc

@[expose] def GHSub (Y : Type) [Group Y] : Prop :=
  ∀ L : Subgroup (barQ Y), IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) → GHList ↥L

theorem ghSub_centralizer {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G) (hK : KGH G)
    {x : G} (hx : x ≠ 1) : GHSub (CY G x) := by
  intro L hs hn
  have hne : centralizer ({x} : Set G) ≠ ⊤ := by
    intro h
    have hz : x ∈ center G := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({x} : Set G) := by rw [h]; exact mem_top g
      exact ((mem_centralizer_iff.mp this) x (Set.mem_singleton x)).symm
    have hsimple : IsSimpleGroup G := hG.1
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h1 | h1
    · rw [h1, mem_bot] at hz
      exact hx hz
    · obtain ⟨a, b, hab⟩ := hG.2.1
      apply hab
      have : a ∈ center G := by rw [h1]; exact mem_top a
      exact (mem_center_iff.mp this b).symm
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let Kpre : Subgroup ↥C := L.comap (barMk ↥C)
  let H : Subgroup G := Kpre.map C.subtype
  have hHle : H ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH : H ≠ ⊤ := fun h => hne (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H := Kpre.equivMapOfInjective C.subtype C.subtype_injective
  let q : ↥Kpre →* ↥L := ((barMk ↥C).comp Kpre.subtype).codRestrict L fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := barMk_surjective (Y := ↥C) (k : barQ ↥C)
    exact ⟨⟨c, show barMk ↥C c ∈ L by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H →* ↥L := q.comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f := hq'.comp e₁.symm.surjective
  exact CFSG.GH74.Generic.ghList_of_surjection hK hH f hf hs hn

end CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.LU.Local

@[expose] def IVK_9_5At_gh_all : Prop :=
  ∀ q : ℕ, 5 ≤ q → IVK_9_5At_gh q

theorem ivk_9_5At_gh_all_of_all (h : IVK_9_5At_all) : IVK_9_5At_gh_all :=
  fun q hq => IVK_9_5At_gh_of (h q hq)

theorem ivk_9_5At_gh_five_of_all (h : IVK_9_5At_gh_all) : IVK_9_5At_gh 5 :=
  h 5 le_rfl

end CFSG.GH74.GLS.IVK.Proofs2
