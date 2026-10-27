module
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

theorem isPSolvable_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.HallHigman.IsPSolvable p A) : CFSG.HallHigman.IsPSolvable p B := by
  intro H hH T hT hs
  have hH' : (H.comap e.toMonoidHom).IsSubnormal := hH.comap e.toMonoidHom
  let ψ : ↥(H.comap e.toMonoidHom) ≃* ↥H :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1) }
  have hψ : Function.Surjective ψ.toMonoidHom := ψ.surjective
  have hTn : (T.comap ψ.toMonoidHom).Normal := Subgroup.Normal.comap inferInstance _
  have hmap : (T.comap ψ.toMonoidHom).map ψ.toMonoidHom = T :=
    Subgroup.map_comap_eq_self_of_surjective hψ T
  have hiso : (↥(H.comap e.toMonoidHom) ⧸ T.comap ψ.toMonoidHom) ≃* (↥H ⧸ T) :=
    QuotientGroup.congr (T.comap ψ.toMonoidHom) T ψ hmap
  have hs' : IsSimpleGroup (↥(H.comap e.toMonoidHom) ⧸ T.comap ψ.toMonoidHom) := by
    have := hs
    exact hiso.isSimpleGroup
  have key := hA (H.comap e.toMonoidHom) hH' (T.comap ψ.toMonoidHom) hs'
  have hidx : (T.comap ψ.toMonoidHom).index = T.index := by
    show Nat.card _ = Nat.card _
    exact Nat.card_congr hiso.toEquiv
  rw [hidx] at key
  exact key

theorem le_center_of_isPSolvable {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 X) {N : Subgroup X} (hN : N.Normal)
    (hNs : CFSG.HallHigman.IsPSolvable 3 ↥N) : N ≤ Subgroup.center X := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with htop | hcen
  · subst htop
    exact absurd (isPSolvable_of_mulEquiv Subgroup.topEquiv hNs) hns
  · exact hcen

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

end
