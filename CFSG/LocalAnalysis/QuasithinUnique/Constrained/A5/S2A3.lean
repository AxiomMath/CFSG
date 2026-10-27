module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A2

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem cj_normalizer (g : G) (X : Subgroup G) :
    cj g (Subgroup.normalizer (X : Set G)) = Subgroup.normalizer (cj g X : Set G) :=
  Subgroup.map_equiv_normalizer_eq X (MulAut.conj g)

omit [Finite G] in
theorem cj_I_of_mem_SI {s : G} (hs : s ∈ s2SI S L) : cj s (s2I S L) = s2I S L := by
  rw [cj_s2I hs.1, Data.cj_SI_L hs]

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem cj_SI {s : G} (hs : s ∈ S) : cj s (s2SI S L) = s2SI S L := by
  have hn := c.data.SI_normal
  have hle : cj s (s2SI S L) ≤ s2SI S L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_cj_iff.1 hy
    have := hn.conj_mem (⟨x, hx.1⟩ : ↥S) (Subgroup.mem_subgroupOf.2 hx) ⟨s, hs⟩
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_subgroupOf.1 this
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_cj])

theorem cj_Phi_swap {s : G} (hs : s ∈ S) (hsn : s ∉ s2SI S L) :
    cj s (frattiniOf (s2I S L)) = frattiniOf (s2I S (cj t L)) := by
  rw [cj_frattiniOf, cj_s2I hs, (c.data.swap_of_not_mem hs hsn).1]

theorem not_le_D₂ {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) {X : Subgroup G} (hX : X ≤ s2I S (cj t L))
    (hu : ∀ u₀ ∈ blockU (cj t L), u₀ ≠ 1 → P₂.bf u₀ = zv → u₀ ∈ s2Phi S L → u₀ ∈ X) : False := by
  obtain ⟨u₀, hu₀, hu₀1, hb, hΦ⟩ := c.exists_u₀ hE hI
  have : u₀ ∈ blockU (cj t L) ⊓ s2I S (cj t L) := ⟨hu₀, hX (hu u₀ hu₀ hu₀1 hb hΦ)⟩
  rw [c.dir₂.2.1, Subgroup.mem_bot] at this
  exact hu₀1 this

theorem SI_frat {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) :
    s2SI S L = S ⊓ Subgroup.normalizer (frattiniOf (s2I S L) : Set G) := by
  apply le_antisymm
  · refine le_inf s2SI_le_S fun s hs => ?_
    exact mem_normalizer_frattiniOf (mem_normalizer_iff_cj.2 (cj_I_of_mem_SI hs))
  · rintro s ⟨hsS, hsN⟩
    by_contra hsSI
    have h1 := c.cj_Phi_swap hsS hsSI
    have h2 : cj s (frattiniOf (s2I S L)) = frattiniOf (s2I S L) := mem_normalizer_iff_cj.1 hsN
    have hle : frattiniOf (s2I S L) ≤ s2I S (cj t L) := by
      rw [← h2, h1]
      exact Subgroup.map_subtype_le _
    exact c.not_le_D₂ hE hI (X := frattiniOf (s2I S L)) hle fun u₀ _ _ _ hΦ => hΦ.1

theorem SI_phi {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) :
    s2SI S L = S ⊓ Subgroup.normalizer (s2Phi S L : Set G) := by
  apply le_antisymm
  · refine le_inf s2SI_le_S fun s hs => ?_
    have h1 : s ∈ Subgroup.normalizer (frattiniOf (s2I S L) : Set G) :=
      mem_normalizer_frattiniOf (mem_normalizer_iff_cj.2 (cj_I_of_mem_SI hs))
    have h2 : s ∈ Subgroup.normalizer (Subgroup.centralizer (s2SI S L : Set G) : Set G) :=
      mem_normalizer_centralizer (Subgroup.le_normalizer hs)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  · rintro s ⟨hsS, hsN⟩
    by_contra hsSI
    have hφ : cj s (s2Phi S L) = s2Phi S L := mem_normalizer_iff_cj.1 hsN
    have hcalc : cj s (s2Phi S L) =
        frattiniOf (s2I S (cj t L)) ⊓ Subgroup.centralizer (s2SI S L : Set G) := by
      unfold s2Phi
      rw [cj_inf, c.cj_Phi_swap hsS hsSI, cj_centralizer, c.cj_SI hsS]
    have hle : s2Phi S L ≤ s2I S (cj t L) := by
      rw [← hφ, hcalc]
      exact inf_le_left.trans (Subgroup.map_subtype_le _)
    exact c.not_le_D₂ hE hI (X := s2Phi S L) hle fun u₀ _ _ _ hΦ => hΦ

theorem phi_ne {P₂ : A5Pi (cj t L)} (hE : P₂.im (baum S) = Estd)
    (hI : P₂.im (s2I S L) = Estd) : s2Phi S L ≠ ⊥ := by
  obtain ⟨u₀, -, hu₀1, -, hΦ⟩ := c.exists_u₀ hE hI
  intro h
  rw [h, Subgroup.mem_bot] at hΦ
  exact hu₀1 hΦ

end Ctx

end CFSG.QuasithinUnique.A5.S2
