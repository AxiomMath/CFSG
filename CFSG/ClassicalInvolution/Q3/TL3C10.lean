module

public import CFSG.ClassicalInvolution.Q3.TL3TwistQuot
public import CFSG.ClassicalInvolution.Q3.TL3C8

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Sub

variable {Y : Type} [Group Y] [Finite Y]

theorem oddCore_eq_bot_of_isSubnormal {H : Subgroup Y} (hH : IsSubnormal H ⊤)
    (hO : classicalInvolutionOddCore Y = ⊥) : classicalInvolutionOddCore ↥H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  set N : Subgroup Y := (classicalInvolutionOddCore ↥H).map H.subtype with hNdef
  have hodd : Odd (Nat.card N) :=
    (CFSG.ComponentClassification.OddCore.odd_card ↥H).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hNs : IsSubnormal N ⊤ := by
    have h1 : IsSubnormal (classicalInvolutionOddCore ↥H) ⊤ :=
      IsSubnormal.step le_top (by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
        intro y _
        exact Subgroup.mem_normalizer_iff.mpr fun n =>
          ⟨fun hn => (classicalInvolutionOddCore_normal ↥H).conj_mem n hn y, fun hn => by
            have := (classicalInvolutionOddCore_normal ↥H).conj_mem _ hn y⁻¹
            simpa [mul_assoc] using this⟩) (IsSubnormal.refl ⊤)
    exact isSubnormal_top_map_subtype hH h1
  have hNle : N ≤ Balance.oddCoreIn ⊤ := Balance.le_oddCoreIn_of_isSubnormal hNs hodd
  have htop : Balance.oddCoreIn (⊤ : Subgroup Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    set M : Subgroup Y := (componentClassificationOddCore ↥(⊤ : Subgroup Y)).map
      (⊤ : Subgroup Y).subtype with hM
    have hMn : M.Normal := (componentClassificationOddCore_normal _).map _
      (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
    have hModd : Odd (Nat.card M) :=
      (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hMle : M ≤ classicalInvolutionOddCore Y := le_sSup ⟨hMn, hModd⟩
    rw [hO] at hMle
    exact hMle ⟨w, hw, rfl⟩
  have hxN : (x : Y) ∈ N := ⟨x, hx, rfl⟩
  have h1 := hNle hxN
  rw [htop, Subgroup.mem_bot] at h1
  exact (Subgroup.mem_bot).mpr (Subtype.ext h1)

omit [Finite Y] in
theorem exists_normal_two_of_isSubnormal {H : Subgroup Y} (hH : IsSubnormal H ⊤)
    {P : Subgroup H} (hPn : P.Normal) (hP2 : IsPGroup 2 P) :
    ∃ Q : Subgroup Y, Q.Normal ∧ IsPGroup 2 Q ∧ P.map H.subtype ≤ Q := by
  have hPs : IsSubnormal P ⊤ :=
    IsSubnormal.step le_top (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
      intro y _
      exact Subgroup.mem_normalizer_iff.mpr fun n =>
        ⟨fun hn => hPn.conj_mem n hn y, fun hn => by
          have := hPn.conj_mem _ hn y⁻¹
          simpa [mul_assoc] using this⟩) (IsSubnormal.refl ⊤)
  have hP's := isSubnormal_top_map_subtype hH hPs
  have hP'2 : IsPGroup 2 (P.map H.subtype) := hP2.map _
  exact ⟨pCoreOf 2 ⊤,
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_of_normal 2 ⊤ inferInstance,
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 ⊤,
    CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hP's hP'2⟩

theorem inO2_of_section_inO2 (hO : classicalInvolutionOddCore Y = ⊥) {K : Subgroup Y} {x : Y}
    (hx : x ∈ subnormalClosure K)
    (h : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(subnormalClosure K))
      (⟨x, hx⟩ : subnormalClosure K))) :
    ∃ Q : Subgroup Y, Q.Normal ∧ IsPGroup 2 Q ∧ x ∈ Q := by
  have hH := isSubnormal_subnormalClosure K
  have hOH := oddCore_eq_bot_of_isSubnormal hH hO
  have hN2 : IsPGroup 2 ↥(classicalInvolutionOddCore ↥(subnormalClosure K)) := by
    rw [hOH]
    exact IsPGroup.of_bot
  obtain ⟨P, hPn, hP2, hxP⟩ := TwistQ.inO2_of hN2 h
  obtain ⟨Q, hQn, hQ2, hPQ⟩ := exists_normal_two_of_isSubnormal hH hPn hP2
  exact ⟨Q, hQn, hQ2, hPQ ⟨_, hxP, rfl⟩⟩

omit [Finite Y] in
theorem twoIn_of_centralizer {u x : Y} (hx : x ∈ Subgroup.centralizer ({u} : Set Y))
    {Q : Subgroup ↥(Subgroup.centralizer ({u} : Set Y))} (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q)
    (hxQ : (⟨x, hx⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ Q) : TC.TwoIn u x := by
  refine ⟨Q.map (Subgroup.centralizer ({u} : Set Y)).subtype, ⟨Subgroup.map_subtype_le _,
    hQ2.map _, ?_⟩, ⟨_, hxQ, rfl⟩⟩
  rintro c hc _ ⟨q, hq, rfl⟩
  exact ⟨⟨c, hc⟩ * q * ⟨c, hc⟩⁻¹, hQn.conj_mem q hq ⟨c, hc⟩, rfl⟩

theorem card_centralizer_lt {t : Y} (ht : orderOf t = 2) (hE2 : ¬ TightInO2 t) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) < Nat.card Y := by
  have hne : Subgroup.centralizer ({t} : Set Y) ≠ ⊤ := by
    intro htop
    apply hE2
    have hcen : ∀ g : Y, g * t = t * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    have htc : t ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr hcen
    have hle : Subgroup.zpowers t ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr htc
    refine ⟨Subgroup.zpowers t, ⟨fun n hn g => ?_⟩, ?_, Subgroup.mem_zpowers t⟩
    · have hgn : g * n = n * g := Subgroup.mem_center_iff.mp (hle hn) g
      rw [hgn, mul_inv_cancel_right]
      exact hn
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have h3 := Subgroup.card_le_card_group (Subgroup.centralizer ({t} : Set Y))
  have h4 : Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) ≠ Nat.card Y :=
    fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h)
  omega

end Sub

end CFSG.ClassicalInvolution.Q3
