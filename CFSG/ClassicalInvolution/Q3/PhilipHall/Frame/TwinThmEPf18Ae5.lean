module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf18Ae5Aux
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmE

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem exists_sq_ne_one_of_mem_USet (F : TwinDisc.ExitO2.Q8Fam Y Δ) {U : Subgroup Y}
    (hU : U ∈ USet Δ) : ∃ j ∈ U, j * j ≠ 1 := by
  obtain ⟨R, ⟨M, hM, P, rfl⟩, hUR, hcyc, hrel⟩ := hU
  have hRcard : Nat.card (Subgroup.map M.subtype (P : Subgroup ↥M)) = 8 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity P]
    have h8 : Nat.card ↥M = 2 ^ 3 := F.card M hM
    rw [h8, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hUcard : Nat.card ↥U = 4 := by
    have := Subgroup.relIndex_mul_card (H := U)
      (K := Subgroup.map M.subtype (P : Subgroup ↥M))
    rw [inf_eq_left.mpr hUR, hrel, hRcard] at this
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥U)
  rw [hUcard] at hg
  refine ⟨g, g.2, fun h1 => ?_⟩
  have h2 : g ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext h1
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hg] at this
  omega

theorem ae5_label_eq_of_omegaStarNbr (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5)
    {L J : Subgroup Y} (hL : L ∈ Δ) (hJ : J ∈ omegaStarNbr Δ L)
    {α β : Finset (Fin 5)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool}
    (hlL : (L.subgroupOf (pSpan Δ)).map I.φ = AE.memBar α h b)
    (hlJ : (J.subgroupOf (pSpan Δ)).map I.φ = AE.memBar β h' c) : α = β := by
  obtain ⟨hJΔ, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨j, hjU, hj2⟩ := exists_sq_ne_one_of_mem_USet F hU
  have h8 : ∀ L ∈ Δ, Nat.card ↥L = 8 := fun L hL => (F.card L hL).trans (by norm_num)
  obtain ⟨zL, hzL⟩ := (F.hyp.omega1 L hL).1
  have hjJ : j ∈ J := hUJ hjU
  have hxz : j * zL * j⁻¹ = zL :=
    hzL.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hUN hjU))
  have hxz' : zL * j = j * zL := by
    calc zL * j = (j * zL * j⁻¹) * j := by rw [hxz]
      _ = j * zL := by group
  have hzφ := phi_map_eq_zBar I.φ (le_refl 5) hL (h8 L hL) hlL hzL
  have hmem : I.φ ⟨j, le_pSpan hJΔ hjJ⟩ ∈ AE.memBar β h' c := by
    rw [← hlJ]
    exact I.mem_map hJΔ hjJ
  have hcomm : AE.zBar α h * I.φ ⟨j, le_pSpan hJΔ hjJ⟩ =
      I.φ ⟨j, le_pSpan hJΔ hjJ⟩ * AE.zBar α h := by
    rw [← hzφ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxz'
  have hsq : I.φ ⟨j, le_pSpan hJΔ hjJ⟩ * I.φ ⟨j, le_pSpan hJΔ hjJ⟩ ≠ 1 := by
    intro e
    apply hj2
    refine phi_injOn I.φ (le_refl 5) hJΔ (h8 J hJΔ) hlJ (mul_mem hjJ hjJ) J.one_mem ?_
    rw [show (⟨j * j, le_pSpan hJΔ (mul_mem hjJ hjJ)⟩ : ↥(pSpan Δ)) =
      ⟨j, le_pSpan hJΔ hjJ⟩ * ⟨j, le_pSpan hJΔ hjJ⟩ from rfl, map_mul, e]
    exact (map_one I.φ).symm
  exact AE.Ae5Aux.eq_of_comm_zBar hmem hsq hcomm

theorem ae5_not_dstarConnected (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : TC.Thin.AEIdent Δ 5)
    {K : Subgroup Y} (hK : K ∈ Δ) (hconn : ∀ L ∈ Δ, L ∈ dstarComp Δ K)
    (htw : ∃ K' ∈ twinSet Δ K, K' ≠ K) : False := by
  clear htw
  obtain ⟨α0, h0, b0, hl0⟩ := I.label K hK
  have hconst : ∀ L, Relation.ReflTransGen (dstarAdj Δ) K L → L ∈ Δ ∧
      ∃ (h : α0.card = 4) (b : Bool), (L.subgroupOf (pSpan Δ)).map I.φ = AE.memBar α0 h b := by
    intro L hKL
    induction hKL with
    | refl => exact ⟨hK, h0, b0, hl0⟩
    | @tail L J _ hadj ih =>
      obtain ⟨hJ, hJn⟩ := hadj
      obtain ⟨hL, h1, b1, hlL⟩ := ih
      obtain ⟨β, h', c, hlJ⟩ := I.label J hJ
      have hαβ : α0 = β := by
        rcases hJn with hJn | hJn
        · exact ae5_label_eq_of_omegaStarNbr F I hL hJn hlL hlJ
        · exact (ae5_label_eq_of_omegaStarNbr F I hJ hJn hlJ hlL).symm
      subst hαβ
      exact ⟨hJ, h', c, hlJ⟩
  classical
  obtain ⟨m1, hm1⟩ : α0.Nonempty := Finset.card_pos.mp (by rw [h0]; norm_num)
  have hα'card : (Finset.univ.erase m1).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  obtain ⟨L, hL, hlL⟩ := I.label_surj (Finset.univ.erase m1) hα'card true
  obtain ⟨-, h2, b2, hl2⟩ := hconst L (hconn L hL)
  have hz : AE.zBar (Finset.univ.erase m1) hα'card ∈ AE.memBar α0 h2 b2 := by
    rw [← hl2, hlL]
    exact AE.zBar_mem_memBar _ _ _
  rcases AE.eq_of_mem_memBar_mul_self (le_refl 5) hz (AE.zBar_mul_self _ _) with e | e
  · exact AE.zBar_ne_one (le_refl 5) _ _ e
  · have := AE.eq_of_zBar_eq (by norm_num) e
    have hm : m1 ∈ Finset.univ.erase m1 := by rw [this]; exact hm1
    simp at hm

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
