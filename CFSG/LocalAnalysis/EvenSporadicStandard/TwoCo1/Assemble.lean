module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Isolation
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def co0C2 : ℕ := 2 ^ 22 * 3 ^ 5 * 5 ^ 2 * 7

@[expose] def co0C3 : ℕ := 2 ^ 18 * 3 ^ 3 * 5 * 11

@[expose] def Co0LocalFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), orderOf z = 2 →
    centralizer ({z} : Set G) = L → (center L).map L.subtype = zpowers z →
    Nat.card (center L) = 2 → Group.IsPerfect L → IsSporadic (L ⧸ center L) .Co1 →
    Co0Facts L z co0C2 co0C3

@[expose] def OctadIsolation : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → Nat.card (center L) = 2 →
    IsSporadic (L ⧸ center L) .Co1 → ∀ z : G, orderOf z = 2 → centralizer ({z} : Set G) = L →
      (center L).map L.subtype = zpowers z → ∀ g : G, ¬ InvType L z co0C2 (g * z * g⁻¹)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.false_of_co0Facts (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h2 : Nat.card (center L) = 2)
    (hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) {c₂ c₃ : ℕ}
    (hno8 : ∀ z : G, orderOf z = 2 → (center L).map L.subtype = zpowers z →
      ∀ v ∈ L, v ^ 8 ≠ z)
    (hconj : ∀ z : G, orderOf z = 2 → (center L).map L.subtype = zpowers z →
      ∀ y y', InvType L z c₃ y → InvType L z c₃ y' → ∃ h ∈ L, h * y' * h⁻¹ = y)
    (hD : ∀ z : G, orderOf z = 2 → (center L).map L.subtype = zpowers z →
      centralizer ({z} : Set G) = L → ∀ g : G, ¬ InvType L z c₂ (g * z * g⁻¹))
    (hfac : ∀ z : G, orderOf z = 2 → (center L).map L.subtype = zpowers z →
      centralizer ({z} : Set G) = L → Co0Facts L z c₂ c₃) : False := by
  have := h.simple
  obtain ⟨z, hz2, hZz, -, hCz⟩ := h.exists_standard_form_of_inner hS h2 hinn
  obtain ⟨g, hgz, hcomm⟩ := exists_fused_commuting_involution h.nonabelian hz2
  exact (hfac z hz2 hZz hCz).false_of_fused (hno8 z hz2 hZz) (hconj z hz2 hZz)
    (hD z hz2 hZz hCz) hz2 hCz hgz hcomm

theorem forall_eq_conj_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ α : MulAut X, ∃ g, α = MulAut.conj g) : ∀ α : MulAut Y, ∃ g, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := h ((MulAut.congr e).symm α)
  refine ⟨e g, ?_⟩
  have := congrArg (MulAut.congr e) hg
  rw [MulEquiv.apply_symm_apply] at this
  rw [this]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem hypothesisOne_of_isSporadic {Y : Type} [Group Y] {s : TauCeti.SporadicName}
    (h : IsSporadic Y s) (hI : HypothesisOne (Carrier s)) : HypothesisOne Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI

theorem allInner_of_isSporadic {Y : Type} [Group Y] {s : TauCeti.SporadicName}
    (h : IsSporadic Y s) (hinn : ∀ α : MulAut (Carrier s), ∃ g, α = MulAut.conj g) :
    ∀ α : MulAut Y, ∃ g, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  exact forall_eq_conj_of_mulEquiv e.symm hinn

theorem twoCo1_not_standard_of_inputs (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Co1)
    (hI : HypothesisOne (Carrier .Co1))
    (hinn : ∀ α : MulAut (Carrier .Co1), ∃ g, α = MulAut.conj g)
    (hno8 : ∀ z : G, orderOf z = 2 → (center L).map L.subtype = zpowers z →
      ∀ v ∈ L, v ^ 8 ≠ z)
    (hconj : ∀ z : G, orderOf z = 2 → (center L).map L.subtype = zpowers z →
      ∀ y y', InvType L z co0C3 y → InvType L z co0C3 y' → ∃ h ∈ L, h * y' * h⁻¹ = y)
    (hD : OctadIsolation) (hco0 : Co0LocalFacts) : False := by
  have hI' := hypothesisOne_of_isSporadic hQ hI
  have hinn' := allInner_of_isSporadic hQ hinn
  have hS := h.card_sylow_eq_two_of_inner hI' hinn'
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  exact h.false_of_co0Facts hS h2 hinn' hno8 hconj
    (fun z hz2 hZz hCz => hD G L h h2 hQ z hz2 hCz hZz) fun z hz2 hZz hCz =>
    hco0 G L z hz2 hCz hZz h2 this hQ

end CFSG.EvenSporadicStandard.TwoCo1
