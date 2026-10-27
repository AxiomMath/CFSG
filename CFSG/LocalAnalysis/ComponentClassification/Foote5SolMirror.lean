module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

variable {G : Type*} [Group G]

@[expose] def MirrorStep (Y X : Subgroup G) : Prop :=
  ∃ (z s : G) (D : Subgroup G), orderOf z = 2 ∧ orderOf s = 2 ∧ z * s = s * z ∧
    IsTwoComponentIn Y (centralizer ({z} : Set G)) ∧ conjugate Y s ≠ Y ∧
    IsTwoComponentIn X (centralizer ({s} : Set G)) ∧
    IsTwoComponentIn D (centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G)) ∧
    D ≤ Y ⊔ conjugate Y s ∧ D ≤ X ⊔ conjugate X z

@[expose] def GSMirrorReach (J M : Subgroup G) : Prop :=
  Relation.ReflTransGen (fun Y X : Subgroup G => (∃ a b : G, GrSLit.GSWeakCorr a Y b X) ∨
    MirrorStep Y X ∨ ∃ g : G, X = conjugate Y g) J M

@[expose] def GSMirrorMaximal (J : Subgroup G) : Prop :=
  ∀ M : Subgroup G, GSMirrorReach J M → Nonempty (J ⧸ Open.fusionZStar J ≃* M ⧸ Open.fusionZStar M)

namespace GSMirrorReach

variable {J Y X : Subgroup G}

theorem refl (J : Subgroup G) : GSMirrorReach J J := Relation.ReflTransGen.refl

theorem tail_corr {a b : G} (h : GSMirrorReach J Y) (hC : GrSLit.GSWeakCorr a Y b X) :
    GSMirrorReach J X :=
  Relation.ReflTransGen.tail h (Or.inl ⟨a, b, hC⟩)

theorem tail_mirror (h : GSMirrorReach J Y) (hM : MirrorStep Y X) : GSMirrorReach J X :=
  Relation.ReflTransGen.tail h (Or.inr (Or.inl hM))

theorem conj (h : GSMirrorReach J Y) (g : G) : GSMirrorReach J (conjugate Y g) :=
  Relation.ReflTransGen.tail h (Or.inr (Or.inr ⟨g, rfl⟩))

theorem of_weakReach (h : GrSLit.GSWeakReach J X) : GSMirrorReach J X :=
  Relation.ReflTransGen.mono (fun _ _ ⟨a, b, hC⟩ => Or.inl ⟨a, b, hC⟩) _ _ h

end GSMirrorReach

theorem GSMirrorMaximal.gsWeakMaximalComponent {J : Subgroup G} (h : GSMirrorMaximal J)
    (hJ : ∃ a : G, orderOf a = 2 ∧ J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))) :
    GrSLit.GSWeakMaximalComponent J :=
  ⟨hJ, fun M hM => h M (GSMirrorReach.of_weakReach hM)⟩

end CFSG.ComponentClassification.FooteLit
