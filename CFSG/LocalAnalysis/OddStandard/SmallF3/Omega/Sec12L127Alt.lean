module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127Nat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec127_not_isZ4Pow4 {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) :
    ¬ IsZ4Pow4 V := by
  rintro ⟨e⟩
  let a : Fin 4 → Multiplicative (ZMod 4) := Pi.mulSingle 0 (Multiplicative.ofAdd 1)
  have ha2 : a ^ 2 ≠ 1 := by decide
  apply ha2
  have hx : ((e.symm a : ↥V) : G) ^ 2 = 1 := hV.2 _ (e.symm a).2
  have hx' : (e.symm a) ^ 2 = 1 := Subtype.ext (by simpa using hx)
  have := congrArg e hx'
  simpa using this

theorem sec127_not_perm_iso {X : Subgroup G}
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    ¬ Nonempty (↥X ≃* Equiv.Perm (Fin 5)) := by
  rintro ⟨e⟩
  have h1 := sec127_card_alt5 hA5
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin] at h1
  exact absurd h1 (by decide)

theorem sec127_alt1 {t : G} {S L E X : Subgroup G} (hX : Sec12X t S L E X)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (hV : CFSG.Open.IsElemAbelian 2 (secV t S L E)) :
    ∃ V1 V2 : Subgroup G, V1 ⊔ V2 = secV t S L E ∧ V1 ⊓ V2 = ⊥ ∧
      ∃ φ1 φ2 : (Fin 5 → ZMod 2) → G, Sec127NatCoord V1 X φ1 ∧ Sec127NatCoord V2 X φ2 := by
  rcases hX.alt with ⟨-, V1, V2, hsup, hinf, hcase⟩ | ⟨hZ4, -⟩
  · rcases hcase with ⟨-, h1, h2⟩ | ⟨hS5, -, -⟩
    · obtain ⟨φ1, hφ1⟩ := sec127_natCoord_of h1
      obtain ⟨φ2, hφ2⟩ := sec127_natCoord_of h2
      exact ⟨V1, V2, hsup, hinf, φ1, φ2, hφ1, hφ2⟩
    · exact absurd hS5 (sec127_not_perm_iso hA5)
  · exact absurd hZ4 (sec127_not_isZ4Pow4 hV)

end CFSG.OddStandard.SmallF3.Omega
