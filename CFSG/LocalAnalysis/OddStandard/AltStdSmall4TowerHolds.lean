module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerEmbed
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4WFDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Main
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarCases

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}

theorem exists_ident_card (hO : GL62.GL62OvergroupsEq) (c : Config G L Q n θ z)
    (hH : HData θ c.hn8 z T) :
    ∃ (cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G) (Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2)),
      ModIso.TCoords z T (ModIso.kap θ c.hn8) (E θ c.hn8) cT ∧
      (∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
        (g : G) * cT v w * (g : G)⁻¹ =
          cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
              Fin.append v w))
            (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
              Fin.append v w))) ∧
      (((Hbar T).map Ψ.toMonoidHom = GL62.B₀ ∧ Nat.card (Hbar T) = 336) ∨
        ((Hbar T).map Ψ.toMonoidHom = GL62.MN ∧ Nat.card (Hbar T) = 1008) ∨
        ((Hbar T).map Ψ.toMonoidHom = GL62.MW ∧ Nat.card (Hbar T) = 56448) ∨
        ((Hbar T).map Ψ.toMonoidHom = GL62.MS ∧ Nat.card (Hbar T) = 120960) ∨
        ((Hbar T).map Ψ.toMonoidHom = GL62.MG ∧ Nat.card (Hbar T) = 362880)) := by
  obtain ⟨cT, hc, hact⟩ := ModIso.exists_tCoords_act c hH
  obtain ⟨hB, hC⟩ := HbarCoords.hbar_transport_of c hH hc hact
  refine ⟨cT, HbarCoords.psi hc, hc, fun g v w => HbarCoords.conj_eq_psi_normAct hc g v w, ?_⟩
  have hcard := HbarCoords.card_map_psi c hc
  rcases hO _ hB hC with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [hcard] at h2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))

theorem sec4WreathFalseBig_of (hW : WrFalse) :
    Sec4WreathFalseBig := by
  intro G _ _ L Q n θ z c T _ hH hWS
  obtain ⟨X, hXN, -, hXC, hcov, hX⟩ := exists_wreath_compl c hH hWS
  have hcardH : Nat.card (Hbar T) = 56448 := (card_hbar_eq_of_compl hXN hXC hcov).trans hX
  obtain ⟨cT, Ψ, hc, hΨ, hcase⟩ := exists_ident_card GL62.gl62OvergroupsEq_holds c hH
  have hMW : (Hbar T).map Ψ.toMonoidHom = GL62.MW := by
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · omega
    · exact h
    · omega
    · omega
  obtain ⟨ι, hι, hιz⟩ := exists_embedding_MW c hH hWS hc hΨ hMW
  exact hW G c.ot.std.simple c.ot.std.nonab z (centHyp_of_config c) ι hι hιz

theorem sec4HbarNotSL_of (hS : SlFalse) : Sec4HbarNotSL := by
  intro G _ _ L Q n θ z c T hH
  obtain ⟨cT, Ψ, hc, hΨ, hcase⟩ := exists_ident_card GL62.gl62OvergroupsEq_holds c hH
  have key : (Hbar T).map Ψ.toMonoidHom = GL62.MS ∨ (Hbar T).map Ψ.toMonoidHom = GL62.MG →
      False := fun hX => by
    obtain ⟨ι, hι, hιz⟩ := exists_embedding_MS c hH hc hΨ hX
    exact hS G c.ot.std.simple c.ot.std.nonab z (centHyp_of_config c) ι hι hιz
  constructor
  · intro h120
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · omega
    · omega
    · exact key (Or.inl h)
    · omega
  · intro h362
    rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · omega
    · omega
    · omega
    · exact key (Or.inr h)

end CFSG.OddStandard.AltStdSmall4.Tower
