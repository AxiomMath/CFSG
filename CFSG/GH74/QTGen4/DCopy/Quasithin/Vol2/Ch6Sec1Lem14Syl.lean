module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Syl
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Hyp611Nat

variable {T M L V : Subgroup G} {n : ℕ}

theorem normalizer_thompsonJ_Q_le_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n) :
    Subgroup.normalizer (thompsonJ (ch6Q T V) : Set G) ≤ M := by
  have hU := h.toHyp611.isUniqueM_F4 h432
  have hQ := h.toHyp611.centralizer_eq
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLTJ : L ⊔ T ≤ Subgroup.normalizer (thompsonJ (ch6Q T V) : Set G) :=
    hLTQ.trans (GammaExtra.normalizer_le_normalizer_thompsonJ (ch6Q T V))
  have hJ1 : thompsonJ (ch6Q T V) ≠ ⊥ := by
    intro h0
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian (ch6Q T V)
    have hVA : Nat.card V ≤ Nat.card A := hA.2.2 V h.le_Q h.toHyp611.isElemAbelian
    have hA1 : A = ⊥ := eq_bot_iff.mpr (h0 ▸ GammaExtra.le_thompsonJ hA)
    rw [hA1, Subgroup.card_bot] at hVA
    exact h.toHyp611.ne_bot (Subgroup.eq_bot_of_card_le V hVA)
  exact le_of_isUniqueM_of_le_twoLocal hU hLTJ
    ⟨_, hJ1, GammaExtra.isPGroup_thompsonJ hQ2, rfl⟩

theorem lemma_6_1_14_one_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))) :
    IsSylowIn 2 (ch6Q T V ⊔ Subgroup.zpowers t)
        (Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G)) ∧
      Subgroup.normalizer (thompsonJ (ch6Q T V ⊔ Subgroup.zpowers t) : Set G) ≤ M ∧
      IsSylowIn 2 (T ⊓ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
        (Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  have hQU : ch6Q T V ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le inf_le_left)
  have hRT : R ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)
  have hRU : R ≤ Subgroup.centralizer (U : Set G) := sup_le hQU (Subgroup.zpowers_le.mpr htU)
  have hCN : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCTU : T ⊓ Subgroup.centralizer (U : Set G) = R :=
    le_antisymm (h.centralizer_fix_le htT ht) (le_inf hRT hRU)
  have hNJ := h.normalizer_thompsonJ_Q_le_F4 h432
  have hJR : thompsonJ R = thompsonJ (ch6Q T V) :=
    h.thompsonJ_eq_Q htT ht le_sup_left hRT (hRU.trans hCN)
  have hQTU : ch6Q T V ≤ T ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf inf_le_left (hQU.trans hCN)
  have hJTU : thompsonJ (T ⊓ Subgroup.normalizer (U : Set G)) = thompsonJ (ch6Q T V) :=
    h.thompsonJ_eq_Q htT ht hQTU inf_le_left inf_le_right
  have hNR : Subgroup.normalizer (R : Set G) ≤ M := by
    refine (GammaExtra.normalizer_le_normalizer_thompsonJ R).trans ?_
    rw [hJR]
    exact hNJ
  refine ⟨?_, by rw [hJR]; exact hNJ, ?_⟩
  ·
    have hnorm : ((M ⊓ Subgroup.centralizer (U : Set G)).subgroupOf
        (M ⊓ Subgroup.normalizer (U : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_left M hCN)]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx.1, F7.normalizer_le_normalizer_centralizer _ hx.2⟩
    have h1 := hSyl.inf_normal (inf_le_inf_left M hCN) hnorm
    have e : (T ⊓ Subgroup.normalizer (U : Set G)) ⊓ (M ⊓ Subgroup.centralizer (U : Set G)) =
        R := by
      rw [← hCTU]
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans hCN))
          (le_inf (inf_le_left.trans h.T_le) inf_le_right)
    rw [e] at h1
    refine isSylowIn_of_normalizer_le h1 inf_le_right ?_
    exact fun x hx => ⟨hNR hx.2, hx.1⟩
  · refine isSylowIn_of_normalizer_le hSyl inf_le_right ?_
    intro x hx
    refine ⟨?_, hx.1⟩
    have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ _ hx.2
    rw [hJTU] at h1
    exact hNJ h1

theorem lemma_6_1_14_three_F4 (h6110 : Stmt6_1_10_F4) (h : Hyp611Nat G T M L V n) {t : G}
    (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) :
    wClos V 0 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V ∧
      (2 < n → wClos V 1 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V) := by
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV =>
    ((h6110 _ T M L V n h).2.1 hV).1
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  have hQU : ch6Q T V ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le inf_le_left)
  have hRT : R ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)
  have hRU : R ≤ Subgroup.centralizer (U : Set G) := sup_le hQU (Subgroup.zpowers_le.mpr htU)
  have hkey : ∀ i : ℕ, i + 2 ≤ n → wClos V i R ≤ ch6Q T V := by
    intro i hi
    refine wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAR, g, hAg, hm⟩ := hA
    have hAS := h.le_S_of_le_conj hs hAg (hAR.trans hRT) (by rw [hm]; exact hi)
    intro a ha
    exact ⟨hRT (hAR ha), h.mem_centralizer_of_mem_S_of_fix htT ht (hAS ha) (hRU (hAR ha))⟩
  exact ⟨hkey 0 (by have := h.two_le; omega), fun hn => hkey 1 (by omega)⟩

end Hyp611Nat

end CFSG.Quasithin.H13
