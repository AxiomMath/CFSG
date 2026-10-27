module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerEmbedW
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerEmbedS
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerEmbedCard

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G} {Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2)}

theorem exists_embedding_MW (c : Config G L Q n θ z)
    (hH : HData θ c.hn8 z T) (hW : WreathStruct z T)
    (hc : ModIso.TCoords z T (ModIso.kap θ c.hn8) (E θ c.hn8) cT)
    (hΨ : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
      (g : G) * cT v w * (g : G)⁻¹ =
        cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w))
          (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w)))
    (hX : (Hbar T).map Ψ.toMonoidHom = GL62.MW) :
    ∃ ι : Grp wrS →* G, Function.Injective ι ∧ ι (t₀ wrS z0_mem_wrS) = z := by
  obtain ⟨X, hXN, hzX, hXC, hcov, -⟩ := exists_wreath_compl c hH hW
  have h2 : ∀ x ∈ X, x ∈ centralizer (T : Set G) → ∀ k : ℕ, x ^ 2 ^ k = 1 → x = 1 :=
    fun x hx hxC _ _ => by
      have h := mem_inf.2 ⟨hx, hxC⟩
      rwa [hXC, mem_bot] at h
  have hSH : wrS ≤ (Hbar T).map Ψ.toMonoidHom := by
    rw [hX]
    exact wrS_le_MW
  exact exists_embedding_of_cover hc hΨ hXN hzX c.ot.cyc.mul_self h2 hcov card_wrS hSH z0_mem_wrS
    (φ := affAct wrS) fun _ _ => rfl

theorem exists_embedding_MS (c : Config G L Q n θ z)
    (hH : HData θ c.hn8 z T)
    (hc : ModIso.TCoords z T (ModIso.kap θ c.hn8) (E θ c.hn8) cT)
    (hΨ : ∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
      (g : G) * cT v w * (g : G)⁻¹ =
        cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w))
          (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            Fin.append v w)))
    (hX : (Hbar T).map Ψ.toMonoidHom = GL62.MS ∨ (Hbar T).map Ψ.toMonoidHom = GL62.MG) :
    ∃ ι : Grp slS →* G, Function.Injective ι ∧ ι (t₀ slS z0_mem_slS) = z := by
  obtain ⟨X, hXN, hzX, h2, hcov⟩ := exists_sl_compl hH c.ot.cyc.mul_self hc hΨ hX
  have hSH : slS ≤ (Hbar T).map Ψ.toMonoidHom := by
    rcases hX with h | h <;> rw [h]
    · exact slS_le_MS
    · exact slS_le_MS.trans MS_le_MG
  exact exists_embedding_of_cover hc hΨ hXN hzX c.ot.cyc.mul_self h2 hcov card_slS hSH z0_mem_slS
    (φ := affAct slS) fun _ _ => rfl

end CFSG.OddStandard.AltStdSmall4.Tower
