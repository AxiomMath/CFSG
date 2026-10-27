module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonAction
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonPoints

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.Assembly.LowTwoRank

theorem hexagon_facts {F : Type} [Field F] (hF : Nat.card F = 9) :
    (incGraph F).Connected ∧ (incGraph F).girth = 12 ∧ (incGraph F).diam = 6 ∧
    (pointGraph F).Connected ∧ (pointGraph F).diam = 3 ∧
    (∀ (p : NonisoLine F) (k : Fin 4),
      {q : NonisoLine F | (pointGraph F).dist p q = k}.ncard = ![1, 6, 24, 32] k) ∧
    (∀ (p : NonisoLine F) (T : HexLine F), ∃! q : NonisoLine F, q ∈ T.1 ∧
      ∀ q' ∈ T.1, (pointGraph F).dist p q ≤ (pointGraph F).dist p q') := by
  obtain ⟨-, hconn, hgirth, hdiam, hΓconn, hΓdiam, hlayer, hnear⟩ := (hexagonData hF).hexagon
  exact ⟨hconn, hgirth, hdiam, hΓconn, hΓdiam, hlayer, hnear⟩

theorem mem_lineActLin_iff {F : Type} [Field F] (hF : Nat.card F = 9) (g : StatedSU 3 3 F)
    (T : HexLine F) (q : NonisoLine F) :
    q ∈ (lineActLin hF g T).1 ↔ ∃ p ∈ T.1,
      q.1 = p.1.map (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  rw [mem_lineActLin]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, lineAct_val hF g a⟩
  · rintro ⟨a, ha, hqa⟩
    exact ⟨a, ha, Subtype.ext ((lineAct_val hF g a).trans hqa.symm)⟩

theorem unitary_three_over_nine_orthogonality_generalized_hexagon {F : Type} [Field F]
    (hF : Nat.card F = 9) :
    let h : (Fin 3 → F) → (Fin 3 → F) → F := fun u v => ∑ j, u j ^ 3 * v j
    let P := {L : Submodule F (Fin 3 → F) // Module.finrank F L = 1 ∧ ∃ v ∈ L, h v v ≠ 0}
    let Lin := {T : Finset P // T.card = 3 ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ∀ x ∈ a.1, ∀ y ∈ b.1, h x y = 0}
    let G : SimpleGraph (P ⊕ Lin) :=
      SimpleGraph.fromRel fun a b => ∃ p T, a = Sum.inl p ∧ b = Sum.inr T ∧ p ∈ T.1
    let Γ : SimpleGraph P := SimpleGraph.fromRel fun p q => ∃ T : Lin, p ∈ T.1 ∧ q ∈ T.1
    let act : StatedSU 3 3 F → Submodule F (Fin 3 → F) → Submodule F (Fin 3 → F) :=
      fun g L => L.map (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (StatedSU 3 3 F : Set (GL (Fin 3) F)) =
      {A : GL (Fin 3) F | ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * A = 1 ∧
        (A : Matrix (Fin 3) (Fin 3) F).det = 1} ∧
    Nat.card P = 63 ∧ Nat.card Lin = 63 ∧
    (∀ T : Lin, T.1.card = 3) ∧ (∀ p : P, {T : Lin | p ∈ T.1}.ncard = 3) ∧
    G.Connected ∧ G.girth = 12 ∧ G.diam = 6 ∧
    Γ.Connected ∧ Γ.diam = 3 ∧
    (∀ (p : P) (k : Fin 4), {q : P | Γ.dist p q = k}.ncard = ![1, 6, 24, 32] k) ∧
    (∀ (p : P) (T : Lin), ∃! q : P, q ∈ T.1 ∧ ∀ q' ∈ T.1, Γ.dist p q ≤ Γ.dist p q') ∧
    (∃ ρ : StatedSU 3 3 F →* (G ≃g G), Function.Injective ρ ∧
      (∀ (g : StatedSU 3 3 F) (p : P), ∃ p' : P, ρ g (Sum.inl p) = Sum.inl p' ∧
        p'.1 = act g p.1) ∧
      (∀ (g : StatedSU 3 3 F) (T : Lin), ∃ T' : Lin, ρ g (Sum.inr T) = Sum.inr T' ∧
        ∀ q : P, q ∈ T'.1 ↔ ∃ p ∈ T.1, q.1 = act g p.1)) ∧
    Nat.card (StatedSU 3 3 F) = 6048 ∧ Group.IsPerfect (StatedSU 3 3 F) ∧
    StatedClassicalModel (StatedSU 3 3 F) .PSU 3 3 1 := by
  intro h P Lin G Γ act
  obtain ⟨hconn, hgirth, hdiam, hΓconn, hΓdiam, hΓlayer, hnear⟩ := hexagon_facts hF
  exact ⟨coe_statedSU hF, card_nonisoLine hF, card_hexLine hF, fun T => T.2.1,
    ncard_lines_through hF, hconn, hgirth, hdiam, hΓconn, hΓdiam, hΓlayer, hnear,
    ⟨incAction hF, incAction_injective hF, fun g p => ⟨lineAct hF g p, rfl, lineAct_val hF g p⟩,
      fun g T => ⟨lineActLin hF g T, rfl, mem_lineActLin_iff hF g T⟩⟩, card_statedSU hF,
    isPerfect_statedSU_three_three hF, classicalModel_statedSU hF⟩

end CFSG.LinearGroups.UnitaryThreeOverNine
