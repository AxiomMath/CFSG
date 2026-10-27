module

public import CFSG.GH74.Generic.BProg.B2.T4PGVSet
public import CFSG.GH74.Generic.BProg.B2.T4PGVL4

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.RankThree.PerfectCover Subgroup

theorem puL5_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuL5 A) :
    PuL5 B := by
  obtain ⟨p, f, hp, hp2, hf, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ := h
  · exact ⟨p, f, hp, hp2, hf, Or.inl ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩
  · exact ⟨p, f, hp, hp2, hf, Or.inr ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩⟩

theorem puL3sq_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuL3sq A) :
    PuL3sq B := by
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
  exact ⟨p, f, hp, hp2, hf, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩

theorem puL4Any_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : PuL4Any A) :
    PuL4Any B := by
  obtain ⟨p, f, hp, hp2, hf, hm | hm⟩ := h
  · exact ⟨p, f, hp, hp2, hf, Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm)⟩
  · exact ⟨p, f, hp, hp2, hf, Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm)⟩

theorem vertQ3_of_table (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hT : Q3Table) :
    P151V.VertGenFor (fun _ _ => True) (fun Y _ => CFSG.Blueprint.LieModel Y .PSL 3 3 1) := by
  intro X _ _ _ _ σ hσ L hL hGH _ hLσ hnt J hJ hJL hQ _ e₁ e₂ he₁ he₂ h₁ h₂ h₁₂ h₁1 h₂1 hne
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  obtain ⟨N, _, _, H, t, K, hs, ⟨eH⟩⟩ :=
    exists_q3Cent_of_vert hGA hL hσσ hLσ hnt hJ hJL hQ he₁ he₂ h₁ h₂ h₁1 h₂1 hne
  have hu₁ : (⟨e₁, hJL he₁⟩ : ↥L) * ⟨e₁, hJL he₁⟩ = 1 := Subtype.ext h₁
  have hu₂ : (⟨e₂, hJL he₂⟩ : ↥L) * ⟨e₂, hJL he₂⟩ = 1 := Subtype.ext h₂
  have hu₁₂ : (⟨e₁, hJL he₁⟩ : ↥L) * ⟨e₂, hJL he₂⟩ = ⟨e₂, hJL he₂⟩ * ⟨e₁, hJL he₁⟩ :=
    Subtype.ext h₁₂
  have hu₁1 : (⟨e₁, hJL he₁⟩ : ↥L) ≠ 1 := fun h => h₁1 (congrArg Subtype.val h)
  have hu₂1 : (⟨e₂, hJL he₂⟩ : ↥L) ≠ 1 := fun h => h₂1 (congrArg Subtype.val h)
  have hune : (⟨e₁, hJL he₁⟩ : ↥L) ≠ ⟨e₂, hJL he₂⟩ := fun h => hne (congrArg Subtype.val h)
  have htop : centralizer ({(⟨e₁, hJL he₁⟩ : ↥L)} : Set ↥L) ⊔
      centralizer ({(⟨e₂, hJL he₂⟩ : ↥L)} : Set ↥L) ⊔
      centralizer ({(⟨e₁, hJL he₁⟩ : ↥L) * ⟨e₂, hJL he₂⟩} : Set ↥L) = ⊤ := by
    rcases hT N H t K hs (GHList.of_mulEquiv eH hGH) with h5 | h3 | h4
    · have h5' : PuL5 (↥L ⧸ center ↥L) := puL5_of_mulEquiv eH.symm h5
      exact P151V.sup_centralizer_eq_top_of_genInner hL.1 (GenLocL5Out.genInner_of_puL5 h5')
        (P151V.odd_card_center_of_odd_hopf hL.1 (P151V.odd_hopfMultiplier_of_puL5 hGA h5'))
        hu₁ hu₂ hu₁₂ hu₁1 hu₂1 hune
    · have h3' : PuL3sq (↥L ⧸ center ↥L) := puL3sq_of_mulEquiv eH.symm h3
      obtain ⟨p', f', hp', hp2', -, hm'⟩ := h3'
      exact P151V.sup_centralizer_eq_top_of_genInner hL.1
        (P151P.genInner_of_isL3Odd ⟨p', 2 * f', hp', hp2', Or.inl hm'⟩)
        (P151V.odd_card_center_of_odd_hopf hL.1 (P151V.odd_hopfMultiplier_of_puL3sq hGA
          (puL3sq_of_mulEquiv eH.symm h3)))
        hu₁ hu₂ hu₁₂ hu₁1 hu₂1 hune
    · have h4' : PuL4Any (↥L ⧸ center ↥L) := puL4Any_of_mulEquiv eH.symm h4
      have eJ : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
      have hJq : IsQuasisimple ↥(J.subgroupOf L) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm (Prop31.isQuasisimple_of_isCompIn hJ)
      exact sup_centralizer_eq_top_of_puL4Any hGA hL.1 h4' hJq
        (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr eJ)
        (by rw [card_hopfMultiplier_of_q3 hGA hQ]; exact odd_one)
        (Subgroup.mem_subgroupOf.2 he₁) (Subgroup.mem_subgroupOf.2 he₂) hu₁ hu₂ hu₁₂ hu₁1 hu₂1 hune
  have hle := P151P.le_sup_of_top htop
  exact hle

end CFSG.GH74.Generic.BProg.B2.T4.PGV
