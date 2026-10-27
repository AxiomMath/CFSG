module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3317A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322A

public section
namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP vecStab permAct7_apply)
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem natural_F4 (h8 : Stmt3_3_8) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14_F4) (h17 : Stmt3_3_17_F4)
    (h : Hyp331 G T M L D) (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      AlternatingNatural (autOn L (vPlus L T)) (commVPlus L T L) ⊥ 7 := by
  obtain ⟨hab, hc⟩ := L3317.alt7_cases_F4 h8 h10 h14 h e
  refine ⟨hab, ?_⟩
  rcases hc with hn | hc4
  · exact hn
  · exfalso
    have h6 := h17 G T M L D h ⟨e⟩
    rw [h6] at hc4
    norm_num at hc4

theorem normalizer_commV_le_F4 (h5 : Stmt3_3_5) (h14 : Stmt3_3_14_F4) (h : Hyp331 G T M L D)
    (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)) :
    Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (le_M h5 h hML (sup_le (L3317.le_normalizer_commV h) (L3317.T_le_normalizer_commV hTL))
    ?_).trans (h14 G T M L D h).2
  have hp : IsPGroup 2 ↥⁅vPlus L T, L⁆ := isPGroup_two_of_sq_eq_one fun w => by
    rw [sq]
    exact A7.sq_eq_one_of_vec ψ w
  have hle : ⁅vPlus L T, L⁆ ≤ pCoreOf 2 (Subgroup.normalizer
      ((⁅vPlus L T, L⁆ : Subgroup G) : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp
  intro hb
  rw [hb, le_bot_iff] at hle
  have h64 := A7.nat_card_of_vec ψ
  rw [hle, Subgroup.card_bot] at h64
  norm_num at h64

theorem exists_coord322_F4 (h5 : Stmt3_3_5) (h8 : Stmt3_3_8) (h10 : Stmt3_3_10)
    (h14 : Stmt3_3_14_F4) (h17 : Stmt3_3_17_F4) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) :
    ∃ ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7), Coord322 T L ψ := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hab, hnat⟩ := natural_F4 h8 h10 h14 h17 h e
  obtain ⟨ψ, hLact, hLonto⟩ := exists_coord h hnat
  have hLW := L3317.le_normalizer_commV h
  have hTW := L3317.T_le_normalizer_commV hTL
  have hNact := A7.nact_of_lact hLW hLact hLonto (normalizer_commV_le_F4 h5 h14 h hML hTL ψ)
  obtain ⟨τ, hτ⟩ := exists_relabel_aligned h.sylow ψ hLW hTW hLonto hNact
  refine ⟨ψ.trans (A7.relabelE τ), ⟨fun l hl => ?_, fun σ hσ => ?_, fun n hn => ?_,
    fun t ht => ?_, fun σ hσ => ?_⟩⟩
  · obtain ⟨σ, hσ, hact⟩ := hLact l hl
    exact ⟨τ * σ * τ⁻¹, (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ,
      (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  · have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := hLonto _ hσ'
    exact ⟨l, hl, (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  · obtain ⟨σ, hact⟩ := hNact n hn
    exact ⟨τ * σ * τ⁻¹, (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  · obtain ⟨σ, hact⟩ := hNact t (hTW ht)
    have hact' := (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact
    exact ⟨_, ((hτ _).1 ⟨t, ht, hact'⟩).1, hact'⟩
  · have hσA := (Subgroup.mem_inf.1 hσ).2
    have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσA τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := hLonto _ hσ'
    exact (hτ σ).2 ⟨(Subgroup.mem_inf.1 hσ).1, l, hLW hl,
      (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩

end CFSG.Quasithin.H13.L3322
