module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V]

@[expose] def vecStab (G : Subgroup (MulAut V)) (u : V) : Subgroup (MulAut V) :=
  G ⊓ MulAction.stabilizer (MulAut V) u

theorem mem_vecStab {G : Subgroup (MulAut V)} {u : V} {g : MulAut V} :
    g ∈ vecStab G u ↔ g ∈ G ∧ g u = u := by
  simp [vecStab, MulAction.mem_stabilizer_iff]

structure CbAlg (Y : Subgroup (MulAut V)) (t : MulAut V) (m : ℕ) (X : Subgroup (MulAut V)) :
    Prop where
  Y_le : Y ≤ X
  alt : ∃ (θ : ↥X ≃* alternatingGroup (Fin (m + 2))) (a b : Fin (m + 2))
      (hn : ∀ x ∈ X, t * x * t⁻¹ ∈ X),
      a ≠ b ∧ (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (m + 2) {a, b} ∧
      IsNatSectionWith (altAct (m + 2)) θ (commV X) ⊥ ∧
      ∀ (x : MulAut V) (hx : x ∈ X),
        (θ ⟨t * x * t⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
          Equiv.swap a b * (θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * (Equiv.swap a b)⁻¹

structure IsCbLift (G Y : Subgroup (MulAut V)) (t : MulAut V) (m : ℕ)
    (X : Subgroup (MulAut V)) : Prop extends CbAlg Y t m X where
  le_G : X ≤ G
  nontrivial : fixV X ⊓ commV (Subgroup.zpowers t) ≠ ⊥
  subnormal : ∀ u ∈ fixV X ⊓ commV (Subgroup.zpowers t), u ≠ 1 →
    (X.subgroupOf (vecStab G u)).IsSubnormal

end CFSG.CGT.PushingUpLit.CGT6
