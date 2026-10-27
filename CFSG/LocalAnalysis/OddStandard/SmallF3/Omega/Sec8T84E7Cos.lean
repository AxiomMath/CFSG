module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8S87a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E7Ded

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_cos_cases (F : Sec8T84Base) (hCos : Asc82OutCosets) (h89 : Asc82Lemma89)
    {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) :
    S = zpowers t ⊔ (S ⊓ L) ∨
      ∃ γ ∈ S, InducesOutsideGStar L 6 (-1) γ ∧ S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L) := by
  have hS3 : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS3.component.isQuasisimple, hctx.omega6m⟩
  have hLt : L ≤ centralizer ({t} : Set G) := hS3.component.le
  have hNmem : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hS3
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLt hNmem hctx.sylow
  have hSylN : IsSylow2Of S (normalizer (L : Set G)) :=
    sec8s_sylow_normalizer F.h36 F.h68 F.h85 F.h86 (asc82Sec8B_of F.hM) hctx
  have hBle : B ≤ S ⊓ L := by rw [inf_comm]; exact hctx.B_le
  have hNB : IsNormalE16In (S ⊓ L) B := by
    obtain ⟨B₁, B₂, -, hNB1, hNB2, honly⟩ := F.hM.sylow_E16 G L hLM (S ⊓ L) hP
    rcases honly B hBle hctx.B_e16 with h | h
    · exact h ▸ hNB1
    · exact h ▸ hNB2
  have hno : ∀ y ∈ S, ∀ α : ℤˣ,
      ¬ InducesTypeSome L y 6 (-1) 1 α ∧ ¬ InducesTypeSome L y 6 (-1) 3 α :=
    fun y _ α => F.h87 G t L S z g B hctx y α
  obtain ⟨eL⟩ := (F.hM.aut_B G L hLM (S ⊓ L) hP B hBle hctx.B_e16).1
  obtain ⟨eC⟩ := h89 G t L S z g B hctx
  have hcardL : Nat.card (autIn L B) = Nat.card (alternatingGroup (Fin 6)) :=
    Nat.card_congr eL.toEquiv
  have hcardC : Nat.card (autIn (centralizer ({t} : Set G)) B) =
      Nat.card (alternatingGroup (Fin 6)) :=
    Nat.card_congr eC.toEquiv
  have hLC : autIn L B ≤ autIn (centralizer ({t} : Set G)) B :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (B : Set G)) hLt)
  have hCeq : autIn L B = autIn (centralizer ({t} : Set G)) B :=
    Subgroup.eq_of_le_of_card_ge hLC (by rw [hcardC, hcardL])
  have hSC : autIn S B ≤ autIn (centralizer ({t} : Set G)) B :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (normalizer (B : Set G)) hctx.sylow.1)
  have haut : autIn S B ≤ autIn L B := by
    rw [hCeq]; exact hSC
  rcases hCos G L S B hLM hSylN hNB hno haut with hleft | ⟨γ, hγS, hγ, hright⟩
  · left
    exact (sec8t84_ded (M := S ⊓ L) inf_le_left hSylN.1
      (F.h86 G t L S z g B hctx) hleft).trans (sup_comm (S ⊓ L) (zpowers t))
  · right
    refine ⟨γ, hγS, hγ, ?_⟩
    have hMS : zpowers γ ⊔ (S ⊓ L) ≤ S :=
      sup_le (Subgroup.zpowers_le.mpr hγS) inf_le_left
    have h := sec8t84_ded (M := zpowers γ ⊔ (S ⊓ L)) hMS hSylN.1
      (F.h86 G t L S z g B hctx) hright
    calc S = (zpowers γ ⊔ (S ⊓ L)) ⊔ zpowers t := h
      _ = (zpowers t ⊔ zpowers γ) ⊔ (S ⊓ L) := by
            rw [sup_comm (zpowers γ ⊔ (S ⊓ L)) (zpowers t), ← sup_assoc]

end CFSG.OddStandard.SmallF3.Omega
