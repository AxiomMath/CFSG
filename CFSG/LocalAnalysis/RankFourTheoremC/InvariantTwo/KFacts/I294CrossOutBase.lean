module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X]

noncomputable def outerHomOfNormal (L : Subgroup X) [L.Normal] : X →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp (MulAut.conjNormal : X →* MulAut ↥L)

theorem conjNormal_injective (L : Subgroup X) [L.Normal] (hcen : centralizer (L : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hg ⟨h, hh⟩)
    have h2 : g * h * g⁻¹ = h := by simpa [MulAut.conjNormal_apply] using h1
    calc h * g = (g * h * g⁻¹) * g := by rw [h2]
      _ = g * h := by group
  rw [hcen, Subgroup.mem_bot] at hgc
  exact hgc

theorem mem_of_outerHomOfNormal_eq_one (L : Subgroup X) [L.Normal]
    (hcen : centralizer (L : Set X) = ⊥) {g : X} (hg : outerHomOfNormal L g = 1) : g ∈ L := by
  have h1 : MulAut.conjNormal (H := L) g ∈ inner ↥L :=
    (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨l, hl⟩ := h1
  have h2 : MulAut.conjNormal (H := L) (l : X) = MulAut.conj l := MulAut.conjNormal_val (h := l)
  have h3 : g = (l : X) :=
    conjNormal_injective L hcen (by rw [h2, hl])
  rw [h3]
  exact l.2

theorem pRank_quotient_le_pRank_outer {p : ℕ} [Fact p.Prime] (L : Subgroup X) [L.Normal]
    (hcen : centralizer (L : Set X) = ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup (Outer ↥L)) := by
  have hlift : ∀ g ∈ L, outerHomOfNormal L g = 1 := by
    intro g hg
    have h1 : MulAut.conjNormal (H := L) g = MulAut.conj (⟨g, hg⟩ : L) :=
      MulAut.conjNormal_val (h := ⟨g, hg⟩)
    change QuotientGroup.mk' (inner ↥L) (MulAut.conjNormal (H := L) g) = 1
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨⟨g, hg⟩, rfl⟩
  let ψ : X ⧸ L →* Outer ↥L := QuotientGroup.lift L (outerHomOfNormal L) hlift
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    have hg : outerHomOfNormal L g = 1 := ha
    exact (QuotientGroup.eq_one_iff g).2 (mem_of_outerHomOfNormal_eq_one L hcen hg)
  exact CFSG.SectionRank.pRank_top_le_of_injective (Fact.out : p.Prime).one_lt ψ hψ

end CFSG.LocalAnalysis.RankFourTheoremC
