module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Lm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Tw
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g_gamma_two (F : Sec8T84Base) (hSw : Sec8T84OuterSwaps)
    (hTw : Sec8T84FactTwist) {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z g : G} {B E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}
    (hE : Sec8E G t L S z g B E) (hgood : S ⊓ L ≤ normalizer (E : Set G))
    (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2)
    (hST : S ⊓ normalizer (E : Set G) ≤ T) {γ : G} (hγ : γ ∈ S ⊓ normalizer (T : Set G))
    (hγT : γ ∉ T) (hγ2 : γ * γ = 1) (hout : InducesOutsideGStar L 6 (-1) γ)
    (hgen : S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L))
    (hE1 : E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2)
    (hE0 : (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E)
    (hU1 : (V1 ⊔ F1).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F1)
    (hU2 : (V2 ⊔ F2).map (MulAut.conj γ).toMonoidHom = V2 ⊔ F2) :
    (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G) ≤ L ∧
      ∃ γ2 : G, γ2 ∈ S ∧ orderOf γ2 = 2 ∧ InducesOutsideGStar L 6 (-1) γ2 ∧
        S = zpowers t ⊔ zpowers γ2 ⊔ (S ⊓ L) ∧ t * γ2 = γ2 * t ∧
        E.map (MulAut.conj γ2).toMonoidHom = F1 ⊔ F2 ∧
        (F1 ⊔ F2).map (MulAut.conj γ2).toMonoidHom = E ∧
        (V1 ⊔ F1).map (MulAut.conj γ2).toMonoidHom = V1 ⊔ F1 ∧
        (V2 ⊔ F2).map (MulAut.conj γ2).toMonoidHom = V2 ⊔ F2 ∧
        IsElemAb2 ((V1 ⊔ F1) ⊓ centralizer ({γ2} : Set G)) 2 ∧
        IsElemAb2 ((V2 ⊔ F2) ⊓ centralizer ({γ2} : Set G)) 2 := by
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2 := h.D
  have hSC : S ≤ centralizer ({t} : Set G) := hctx.sylow.1
  have hLC : L ≤ centralizer ({t} : Set G) := hctx.component.le
  have htS : t ∈ S := sec4_t_mem_S hctx.sylow hctx.involution
  obtain ⟨hγS, -⟩ := Subgroup.mem_inf.mp hγ
  have hγt : γ * t = t * γ := Subgroup.mem_centralizer_singleton_iff.mp (hSC hγS)
  obtain ⟨hBγle, r, hrP, hr2, hrout, hea⟩ := sec8t84g4_twist F hSw hTw hctx hγS hγ2 hout
  have hrS : r ∈ S := (Subgroup.mem_inf.mp hrP).1
  have hBeq : B = E ⊓ centralizer ({t} : Set G) := hE.cent_t.symm
  have hBγeq : B.map (MulAut.conj γ).toMonoidHom = (F1 ⊔ F2) ⊓ centralizer ({t} : Set G) := by
    rw [hBeq, sec8t84g4_map_cent_inf hγt, hE1]
  have hJ0 : (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G) =
      B ⊔ B.map (MulAut.conj γ).toMonoidHom := by
    rw [hBγeq, sec8t84g4_J0_eq D, ← hBeq]
  have hJ0L : (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G) ≤ L := by
    rw [hJ0]
    exact sup_le (hctx.B_le.trans inf_le_left) (hBγle.trans inf_le_right)
  refine ⟨hJ0L, ?_⟩
  have hrT : r ∈ T := hST (Subgroup.mem_inf.mpr ⟨hrS, hgood hrP⟩)
  obtain ⟨k, hk, hkr⟩ : ∃ k : G, (k = 1 ∨ k = t) ∧ k * r ∈ T1 ⊔ T2 := by
    rcases sec8t84g4_T_decomp D.wr D.T_eq hrT with h1 | ⟨d, hd, hrd⟩
    · exact ⟨1, Or.inl rfl, by rwa [one_mul]⟩
    · refine ⟨t, Or.inr rfl, ?_⟩
      rw [hrd, ← mul_assoc, D.t_sq, one_mul]
      exact hd
  have hkS : k ∈ S := by
    rcases hk with hk1 | hk1 <;> rw [hk1]
    · exact one_mem S
    · exact htS
  have hkC : ∀ x ∈ S, x * k = k * x := by
    intro x hx
    rcases hk with hk1 | hk1 <;> rw [hk1]
    · rw [mul_one, one_mul]
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hSC hx)
  have hkk : k * k = 1 := by
    rcases hk with hk1 | hk1 <;> rw [hk1]
    · exact mul_one 1
    · exact D.t_sq
  have hkL : k ∈ centralizer (L : Set G) := by
    rcases hk with hk1 | hk1 <;> rw [hk1]
    · exact one_mem _
    · exact sec8t84g4_mem_centralizer_of_le hLC
  have hkz : k ∈ zpowers t := by
    rcases hk with hk1 | hk1 <;> rw [hk1]
    · exact one_mem _
    · exact Subgroup.mem_zpowers t
  have hJk : ∀ x ∈ (E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G), x * k = k * x := by
    intro x hx
    rcases hk with hk1 | hk1 <;> rw [hk1]
    · rw [mul_one, one_mul]
    · exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hTle : T1 ⊔ T2 ≤ T := by
    rw [D.T_eq]
    exact le_sup_right
  have hdT : k * r ∈ T1 ⊔ T2 := hkr
  have hγ2eq : γ * (k * r) = (γ * r) * k := by
    rw [← hkC r hrS]
    exact (mul_assoc γ r k).symm
  have hγrk : (γ * r) * k = k * (γ * r) := hkC _ (mul_mem hγS hrS)
  have hγ2sq : (γ * (k * r)) * (γ * (k * r)) = 1 := by
    rw [hγ2eq]
    calc ((γ * r) * k) * ((γ * r) * k) = (γ * r) * (k * (γ * r)) * k := by group
      _ = (γ * r) * ((γ * r) * k) * k := by rw [← hγrk]
      _ = ((γ * r) * (γ * r)) * (k * k) := by group
      _ = 1 := by rw [hr2, hkk, one_mul]
  have hγ2T : γ * (k * r) ∉ T := fun hmem => hγT (by
    have h2 := mul_mem hmem (inv_mem (hTle hdT))
    rwa [mul_inv_cancel_right] at h2)
  have hγ2ne : γ * (k * r) ≠ 1 := fun h1 => hγ2T (by
    rw [h1]
    exact one_mem T)
  have hdE : k * r ∈ normalizer (E : Set G) := h.T_syl.1 (hTle hdT)
  obtain ⟨hdV1, hdV2, hdF1, hdF2⟩ := sec8t84g4_norm_VF D _ hdT
  have hdE0 : k * r ∈ normalizer ((F1 ⊔ F2 : Subgroup G) : Set G) :=
    sec8t84g4_mem_normalizer_sup hdF1 hdF2
  have hdU1 : k * r ∈ normalizer ((V1 ⊔ F1 : Subgroup G) : Set G) :=
    sec8t84g4_mem_normalizer_sup hdV1 hdF1
  have hdU2 : k * r ∈ normalizer ((V2 ⊔ F2 : Subgroup G) : Set G) :=
    sec8t84g4_mem_normalizer_sup hdV2 hdF2
  have hE1' : E.map (MulAut.conj (γ * (k * r))).toMonoidHom = F1 ⊔ F2 := by
    rw [sec8t84g4_map_conj_mul hdE]
    exact hE1
  have hE0' : (F1 ⊔ F2).map (MulAut.conj (γ * (k * r))).toMonoidHom = E := by
    rw [sec8t84g4_map_conj_mul hdE0]
    exact hE0
  have hU1' : (V1 ⊔ F1).map (MulAut.conj (γ * (k * r))).toMonoidHom = V1 ⊔ F1 := by
    rw [sec8t84g4_map_conj_mul hdU1]
    exact hU1
  have hU2' : (V2 ⊔ F2).map (MulAut.conj (γ * (k * r))).toMonoidHom = V2 ⊔ F2 := by
    rw [sec8t84g4_map_conj_mul hdU2]
    exact hU2
  have hγ2t : (γ * (k * r)) * t = t * (γ * (k * r)) := by
    have hc : Commute t (γ * (k * r)) :=
      (show Commute t γ from hγt.symm).mul_right
        ((show Commute t k from hkC t htS).mul_right
          (show Commute t r from (Subgroup.mem_centralizer_singleton_iff.mp (hSC hrS)).symm))
    exact hc.symm.eq
  have hKlein : IsElemAb2
      (((E ⊔ (F1 ⊔ F2)) ⊓ centralizer ({t} : Set G)) ⊓ centralizer ({γ * (k * r)} : Set G)) 2 := by
    rw [hγ2eq, sec8t84g4_inf_cent_mul hJk, hJ0]
    exact hea
  have hγ2N : γ * (k * r) ∈ normalizer ((V1 ⊔ F1 : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hU1'
  obtain ⟨hC1, hC2⟩ := sec8t84g4_klein_transfer D hγ2t hγ2N hKlein
  have hgen2 : S = zpowers t ⊔ zpowers (γ * (k * r)) ⊔ (S ⊓ L) := by
    have hmem : (γ * (k * r)) * r⁻¹ * k⁻¹ ∈ zpowers t ⊔ zpowers (γ * (k * r)) ⊔ (S ⊓ L) :=
      mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_right (inv_mem hrP)))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (inv_mem hkz)))
    have e : (γ * (k * r)) * r⁻¹ * k⁻¹ = γ := by group
    rw [e] at hmem
    refine le_antisymm ?_ ?_
    · calc S = zpowers t ⊔ zpowers γ ⊔ (S ⊓ L) := hgen
        _ ≤ zpowers t ⊔ zpowers (γ * (k * r)) ⊔ (S ⊓ L) :=
          sup_le (sup_le (le_sup_left.trans le_sup_left) (Subgroup.zpowers_le.mpr hmem))
            le_sup_right
    · exact sup_le (sup_le (Subgroup.zpowers_le.mpr htS)
        (Subgroup.zpowers_le.mpr (mul_mem hγS (mul_mem hkS hrS)))) inf_le_left
  refine ⟨γ * (k * r), mul_mem hγS (mul_mem hkS hrS),
    orderOf_eq_prime (by rw [pow_two]; exact hγ2sq) hγ2ne, ?_, hgen2, hγ2t.symm, hE1', hE0', hU1',
    hU2', hC1, hC2⟩
  rw [hγ2eq]
  exact sec8t84g4_outer_mul_cent hrout hkL

end CFSG.OddStandard.SmallF3.Omega
