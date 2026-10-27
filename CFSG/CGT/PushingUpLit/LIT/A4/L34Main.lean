module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Five
public import CFSG.CGT.PushingUpLit.LIT.A4.L34Four

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

namespace Two.Cfg

variable {t : Two G} (h : t.Cfg)
include h

theorem pair_of_violation [Finite G] (hle₁ : ∀ g, conjSub g t.X₁ ≤ t.M → g ∈ t.M)
    (hle₂ : ∀ g, conjSub g t.X₂ ≤ t.M → g ∈ t.M)
    (hnorm : Subgroup.normalizer (t.A : Set G) ≤ t.M) {g : G} (hg : g ∉ t.M)
    (hB : conjSub g t.A ≤ t.M) : Pair t (t.conj g) where
  cM := h
  cN := h.conj_cfg g
  AleN := by
    have hs := h.conj_cfg g
    have hU4 : Nat.card (t.conj g).V₁ = 4 := hs.card_V₁
    have hUsq : ∀ x ∈ (t.conj g).V₁, x * x = 1 := fun x hx => hs.sq_V₁ hx
    have hUM : (t.conj g).V₁ ≤ t.M := by
      refine le_trans (Two.V₁_le_A (t.conj g)) ?_
      rw [Two.conj_A]
      exact hB
    have key := lemma1 h hUM (isKleinFour_of_card_four hU4 hUsq)
      (fun u hu hu1 => hs.cent u hu1 (hUsq u hu)
        (Or.inr fun x hx => hs.comm u ((t.conj g).V₁_le hu) x hx))
    exact sup_le key.1 key.2
  BleM := by
    rw [Two.conj_A]
    exact hB
  X₁nle := by
    intro hX
    apply hg
    have h1 := conjSub_mono (g := g⁻¹) hX
    rw [show (t.conj g).M = conjSub g t.M from rfl, conjSub_inv_conjSub] at h1
    have := hle₁ g⁻¹ h1
    simpa using t.M.inv_mem this
  X₂nle := by
    intro hX
    apply hg
    have h1 := conjSub_mono (g := g⁻¹) hX
    rw [show (t.conj g).M = conjSub g t.M from rfl, conjSub_inv_conjSub] at h1
    have := hle₂ g⁻¹ h1
    simpa using t.M.inv_mem this
  Y₁nle := fun hY => hg (hle₁ g hY)
  Y₂nle := fun hY => hg (hle₂ g hY)
  card := (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  AneB := by
    intro e
    apply hg
    apply hnorm
    rw [Two.conj_A] at e
    have := mem_normalizer_of_conjSub_eq (g₁ := g) (g₂ := 1) (X := t.A)
      (by rw [conjSub_one]; exact e.symm)
    simpa using this

theorem sc [Finite G] (hle₁ : ∀ g, conjSub g t.X₁ ≤ t.M → g ∈ t.M)
    (hle₂ : ∀ g, conjSub g t.X₂ ≤ t.M → g ∈ t.M)
    (hnorm : Subgroup.normalizer (t.A : Set G) ≤ t.M) :
    ∀ g, conjSub g t.A ≤ t.M → g ∈ t.M := by
  intro g hB
  by_contra hg
  have hp := h.pair_of_violation hle₁ hle₂ hnorm hg hB
  exact hp.lemma5 hp.comm_AB

theorem lemma34 [Finite G] (hle₁ : ∀ g, conjSub g t.X₁ ≤ t.M → g ∈ t.M)
    (hle₂ : ∀ g, conjSub g t.X₂ ≤ t.M → g ∈ t.M)
    (hnorm : Subgroup.normalizer (t.A : Set G) ≤ t.M) {U : Subgroup G} (hUM : U ≤ t.M)
    (hU : IsKleinFour ↥U) {g : G}
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ conjSub g t.M) : g ∈ t.M := by
  by_contra hg
  have h1 := lemma1 h hUM hU hC
  have hs := h.conj_cfg g
  have hV₁sq : ∀ x ∈ t.V₁, x * x = 1 := fun x hx => h.sq_V₁ hx
  have h2 := lemma1 hs (N := t.M) (U := t.V₁) h1.1
    (isKleinFour_of_card_four h.card_V₁ hV₁sq)
    (fun v hv hv1 => h.cent v hv1 (hV₁sq v hv)
      (Or.inr fun x hx => h.comm v (t.V₁_le hv) x hx))
  have hB : conjSub g t.A ≤ t.M := by
    rw [← Two.conj_A]
    exact sup_le h2.1 h2.2
  exact hg (h.sc hle₁ hle₂ hnorm g hB)

end Two.Cfg

end CFSG.CGT.PushingUpLit.A4.L34
