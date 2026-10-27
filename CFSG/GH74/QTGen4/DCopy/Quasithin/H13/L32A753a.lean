module

public import CFSG.Quasithin.H13.L32A753a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A5Props
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace L32A

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx753

variable {T L V K : Subgroup G}

theorem exists_not1471_F4 (C : Ctx753 T L V K) (h38 : Lemma14_7_38_F4) :
    ∃ (γ γ' : F8.Geom T L (hz T V)) (g h : ↥((L ⊔ T) ⊔ hz T V)),
      Not1471 T L V (hz T V) γ γ' g h := by
  obtain ⟨γ, γ', g, s⟩ := C.hF98.exists_F8Setup
  exact L32A.exists_not1471 C.hF98 s (h38 G T L V (hz T V) C.setting γ γ' g s)

end Ctx753

theorem ctx753_of_F4 (h30 : Lemma14_7_30_F4) (h48 : Lemma14_7_48_F4) (h52 : Thm14_7_52_F4)
    {T L V H K : Subgroup G} (S : Setting147 G T L V H) (hK : K ∈ cComp H)
    (hU3 : IsPSU 3 3 1 (cStar K)) : H = hz T V ∧ Ctx753 T L V K := by
  obtain ⟨hKT, hG1, -, hU, -⟩ := h52 G T L V H S K hK
  obtain ⟨K', hC, -, hUK⟩ := h48 G T L V H S
  have hKK' : K = K' := by
    have : K ∈ ({K'} : Set (Subgroup G)) := hC ▸ hK
    exact this
  subst hKK'
  obtain ⟨-, -, -, hF⟩ := h30 G T L V H S K hK
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_cComp_eq hC
  have hTH : T ≤ H := hKT ▸ le_sup_right
  have hKH : K ≤ H := hKT ▸ le_sup_left
  have hcl : conjClosure K T = K := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (le_conjClosure K T)
    exact (Subgroup.mem_normalizer_iff.mp (hHN (hTH ht)) k).mp hk
  have hH' : conjClosure K T ⊔ (L32A.l1 T L V ⊔ T) = H := by
    rw [hcl]
    refine le_antisymm (sup_le hKH (sup_le (le_sup_left.trans S.hz.1.1) hTH)) ?_
    rw [hKT]
    exact sup_le_sup_left le_sup_right K
  rw [hH'] at hF
  have hV1 : Nat.card (fsuV1 T V) = 2 := hF.toHypF98.toHypF91.card_V₁
  have hHz : H = hz T V := by
    rw [hG1, A6.g1, normalizer_eq_centralizer_of_card_two hV1]
  subst hHz
  exact ⟨rfl, ⟨S.hyp, S, hC, hKT, hU, hU ▸ hUK, hU3, hF⟩⟩

end L32A

end CFSG.Quasithin.H13
