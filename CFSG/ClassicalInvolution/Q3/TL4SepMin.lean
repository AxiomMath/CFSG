module

public import CFSG.ClassicalInvolution.Q3.TL4SepSub

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G]

theorem conjInvariant_conjClass (K : Subgroup G) :
    ConjInvariant (CoreAssembly.conjClass K) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K⟩

theorem conjInvariant_union {Δ₁ Δ₂ : Set (Subgroup G)} (h₁ : ConjInvariant Δ₁)
    (h₂ : ConjInvariant Δ₂) : ConjInvariant (Δ₁ ∪ Δ₂) := by
  rintro n K (hK | hK)
  · exact Or.inl (h₁ n K hK)
  · exact Or.inr (h₂ n K hK)

theorem oddCore_eq_bot_of_normal [Finite G] (hO : classicalInvolutionOddCore G = ⊥)
    {M : Subgroup G} (hM : M.Normal) : classicalInvolutionOddCore ↥M = ⊥ :=
  CFSG.ComponentClassification.OddCore.subnormal_corefree hO M
    (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))

structure T4Min (r : ℕ) (G : Type) [Group G] [Finite G] (Δ : Set (Subgroup G))
    (J L : Subgroup G) : Prop where
  ih : Thm4RBelow r (Nat.card G)
  hyp : T4Hyp r G Δ
  memJ : J ∈ Δ
  memL : L ∈ Δ
  notConj : ¬ ∃ g : G, conjSub g J = L
  notComm : ¬ Commutes J L

variable [Finite G] {Δ : Set (Subgroup G)} {J L : Subgroup G}

theorem T4Min.two (h : T4Min r G Δ J L) :
    T4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L where
  ih := h.ih
  hyp := by
    refine h.hyp.sub ?_ (conjInvariant_union (conjInvariant_conjClass J)
      (conjInvariant_conjClass L))
    rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact h.hyp.hyp.conjInvariant g J h.memJ
    · exact h.hyp.hyp.conjInvariant g L h.memL
  memJ := Or.inl (CoreAssembly.mem_conjClass_self J)
  memL := Or.inr (CoreAssembly.mem_conjClass_self L)
  notConj := h.notConj
  notComm := h.notComm

theorem T4Min.omegaGen_eq_top (h : T4Min r G Δ J L) : omegaGen Δ = ⊤ := by
  by_contra hne
  set M := omegaGen Δ
  have hOM : classicalInvolutionOddCore ↥M = ⊥ :=
    oddCore_eq_bot_of_normal h.hyp.odd (omegaGen_normal h.hyp.hyp.conjInvariant)
  have hlt : Nat.card M < Nat.card G := lt_of_le_of_ne (Subgroup.card_le_card_group _)
    (fun e => hne ((Subgroup.card_eq_iff_eq_top _).mp e))
  have hJM : J ≤ M := le_omegaGen h.memJ
  have hLM : L ≤ M := le_omegaGen h.memL
  have hc := h.ih ↥M hlt _ (h.hyp.restrict M hOM) (J.subgroupOf M) ⟨J, h.memJ, hJM, rfl⟩
    (L.subgroupOf M) ⟨L, h.memL, hLM, rfl⟩ fun hex => by
      obtain ⟨g, -, hg⟩ := exists_conjSub_of_restrict hJM hLM hex
      exact h.notConj ⟨g, hg⟩
  exact h.notComm (commutes_of_restrict hJM hLM hc)

theorem thm4RBelow_of_min {n : ℕ} (hmin : ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
      ∀ J L : Subgroup G, T4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
      omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ → False) :
    Thm4RBelow r n := by
  suffices h : ∀ m, m ≤ n → Thm4RBelow r m from h n le_rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmn G _ _ hG Δ hΔ J hJ L hL hnc
    by_contra hcomm
    have hm : T4Min r G Δ J L := ⟨ih _ hG (hG.le.trans hmn), hΔ, hJ, hL, hnc, hcomm⟩
    exact hmin G (lt_of_lt_of_le hG hmn) J L hm.two hm.two.omegaGen_eq_top

end CFSG.ClassicalInvolution.Q3.TL4
