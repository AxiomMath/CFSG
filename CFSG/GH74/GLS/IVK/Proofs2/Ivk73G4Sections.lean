module

public import CFSG.GH74.Generic.Sections

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG

theorem exists_noncomm_of_le_isQuasisimple {G : Type} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    (hq : IsQuasisimple ↥A) : ∃ a b : ↥B, a * b ≠ b * a := by
  obtain ⟨-, -, a', b', hab'⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  refine ⟨⟨a, hAB a.2⟩, ⟨b, hAB b.2⟩, fun hh => hab' ?_⟩
  have hh' : (a : G) * (b : G) = (b : G) * (a : G) := congrArg (fun z : ↥B => (z : G)) hh
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext hh')

theorem ghList_of_le_ne_top {G : Type} [Group G] (hK : KGH G) {N L : Subgroup G} (hN : N ≠ ⊤)
    (hLN : L ≤ N) (hs : IsSimpleGroup ↥L) (hn : ∃ a b : ↥L, a * b ≠ b * a) : GHList ↥L :=
  Generic.ghList_of_surjection hK (fun h => hN (top_le_iff.1 (h ▸ hLN))) (MonoidHom.id ↥L)
    Function.surjective_id hs hn

theorem ghList_of_subgroup_of_quotient {G : Type} [Group G] (hK : KGH G) {M : Subgroup G} (hM : M ≠ ⊤)
    {Y : Type} [Group Y] (π : ↥M →* Y) (hπ : Function.Surjective π) (L : Subgroup Y)
    (hs : IsSimpleGroup ↥L) (hn : ∃ a b : ↥L, a * b ≠ b * a) : GHList ↥L := by
  let Kpre : Subgroup ↥M := L.comap π
  let H : Subgroup G := Kpre.map M.subtype
  have hHle : H ≤ M := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH : H ≠ ⊤ := fun h => hM (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H := Kpre.equivMapOfInjective M.subtype M.subtype_injective
  let q : ↥Kpre →* ↥L := (π.comp Kpre.subtype).codRestrict L fun k => k.2
  have hq : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := hπ (k : Y)
    exact ⟨⟨c, show π c ∈ L by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H →* ↥L := q.comp e₁.symm.toMonoidHom
  exact Generic.ghList_of_surjection hK hH f (hq.comp e₁.symm.surjective) hs hn

end CFSG.GH74.GLS.IVK
