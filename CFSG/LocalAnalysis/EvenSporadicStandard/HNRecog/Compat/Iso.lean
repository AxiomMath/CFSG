module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Adj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpCardOrb
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpRegGraph
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpStabEq

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3 CFSG.Monster.GMS

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

theorem theta_injOn [Finite G] [Finite G'] (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x y : G} (hx : IsConj a x)
    (hy : IsConj a y) (hxy : θ x = θ y) : x = y :=
  cp_theta_injOn h h' hα hθ hx hy hxy

theorem card_conjVert_eq [Finite G] [Finite G'] (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α) : Nat.card (ConjVert a) = Nat.card (ConjVert a') :=
  cp_card_conjVert_eq h h'

theorem exists_graphIso_of_injective_regular {V W : Type} [Finite V] [Finite W]
    (Γ₁ : SimpleGraph V) (Γ₂ : SimpleGraph W) (φ : V → W) (hinj : Function.Injective φ)
    (hadj : ∀ u v, Γ₁.Adj u v → Γ₂.Adj (φ u) (φ v)) (hcard : Nat.card V = Nat.card W) (d : ℕ)
    (hd₁ : ∀ v, Nat.card {u // Γ₁.Adj v u} = d) (hd₂ : ∀ w, Nat.card {u // Γ₂.Adj w u} = d) :
    Nonempty (Γ₁ ≃g Γ₂) :=
  cp_graphIso_of_injective_regular Γ₁ Γ₂ φ hinj hadj hcard d hd₁ hd₂

theorem theta_graphIso [Finite G] [Finite G'] (hC : Cover4A) (hW : Wit20) (hG : Gen2A)
    (h29 : Segev29) (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) : Nonempty (Gamma a ≃g Gamma a') := by
  let φ : ConjVert a → ConjVert a' := fun v => ⟨θ v, hθ.typed h h' hα v.2⟩
  have hinj : Function.Injective φ := fun u v huv =>
    Subtype.ext (theta_injOn h h' hα hθ u.2 v.2 (congrArg Subtype.val huv))
  refine exists_graphIso_of_injective_regular (Gamma a) (Gamma a') φ hinj ?_
    (card_conjVert_eq h h' hα) 2200 (cp_card_adj h) (cp_card_adj h')
  intro u v huv
  rw [gamma_adj_iff] at huv ⊢
  obtain ⟨hne, hconj⟩ := huv
  exact ⟨fun e => hne (hinj e), (theta_adj hC hW hG h29 h h' hα hθ u.2 ⟨v.2, hconj⟩).2⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
