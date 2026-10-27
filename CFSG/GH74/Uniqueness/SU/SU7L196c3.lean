module

public import CFSG.GH74.Uniqueness.SU.SU7L196c2
public import CFSG.GH74.Uniqueness.SU.SU7L195
public import CFSG.GH74.Uniqueness.SU.SU7L196c1

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG
  CFSG.GH74.Uniqueness.SU.SU9

namespace L196c

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem lemma196c (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) {a : G}
    (ha : a ∈ A) (haU : a ∉ U) :
    Nonempty (↥(centralizer ({a} : Set G)) ≃*
        alternatingGroup (Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
      (commutator ↥(centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype = U := by
  have h194M : pPrimeCore 2 ↥M = ⊥ := (L194.lemma194_of_ctx hKI3 hKI4 hc).1
  have hTM' := L195.normalizes_T hKI3 hKI4 hc
  have hCT := L195.cent_M_le_T hKI3 hKI4 hc
  have hMcard := L195.card_M hKI3 hKI4 hc
  obtain ⟨w, hwM, hwa, hw⟩ := exists_w hc h194M hTM' hMcard ha haU
  have hCG : centralizer ({a} : Set G) ≤ M :=
    cent_le_M hKI3 hKI4 hc h194M hTM' hCT hMcard ha haU hwM hwa hw
  have hce : centralizer ({a} : Set G) = (A ⊓ centralizer ({w} : Set G)) ⊔ (zpowers w ⊔ U) := by
    have := CM.cent_eq hc h194M hTM' hCT hMcard ha haU hwM hwa hw
    rwa [inf_eq_left.2 hCG] at this
  exact ⟨nonempty_mulEquiv_cent hc hTM' hCT ha haU hwM hwa hw hce,
    commutator_cent_eq hc hTM' hCT ha haU hwM hwa hw hce⟩

end L196c

end CFSG.GH74.Uniqueness.SU.SU7
