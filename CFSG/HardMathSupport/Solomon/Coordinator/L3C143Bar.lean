module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

theorem isSLThreeExc_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsSLThreeExc Y) : IsSLThreeExc Y' := by
  obtain ⟨K, hK, hf, hc, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, hc, ⟨e.symm.trans f⟩⟩

theorem isSUThreeExc_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsSUThreeExc Y) : IsSUThreeExc Y' := by
  obtain ⟨K, hK, hf, q, hc, hq, ⟨f⟩⟩ := h
  exact ⟨K, hK, hf, q, hc, hq, ⟨e.symm.trans f⟩⟩

theorem isAltType_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : Lemma25Ns.IsAltType Y) : Lemma25Ns.IsAltType Y' := by
  obtain ⟨n, ⟨f⟩⟩ := h
  exact ⟨n, ⟨e.symm.trans f⟩⟩

theorem centre_quot_equiv {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) :
    IsPGroup 3 (Subgroup.center (barOf 3 L)) ∧
      Nonempty ((barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃* (↥L ⧸ oPrimeP 3 ↥L)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hL
  have hZeq : Subgroup.center (barOf 3 L) = CFSG.pCore 3 (barOf 3 L) := by
    refine le_antisymm ?_ (pCore_le_center hp hq)
    intro z hz
    refine mem_pCore_of_forall_comm_aux hp fun w => ?_
    exact (Subgroup.mem_center_iff.1 hz w)
  refine ⟨by rw [hZeq]; exact CFSG.pCore_isPGroup, ?_⟩
  have hle : GLAPPrimeCore 3 ↥L ≤ oPrimeP 3 ↥L := by
    intro l hl
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l ∈ CFSG.pCore 3 (barOf 3 L)
    rw [show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) l = 1 from
      (QuotientGroup.eq_one_iff l).2 hl]
    exact Subgroup.one_mem _
  have hmap : (oPrimeP 3 ↥L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) =
      Subgroup.center (barOf 3 L) := by
    rw [hZeq]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient (GLAPPrimeCore 3 ↥L) (oPrimeP 3 ↥L) hle)⟩

theorem oPrimePOf_le_self {G : Type*} [Group G] (J : Subgroup G) : oPrimePOf 3 J ≤ J :=
  Subgroup.map_subtype_le _

theorem exists_hat_component {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b} : Set G)) J) :
    ∃ Jh : Subgroup (barOf 3 L), GLAPComponent 3 (fixSub (barAut 3 L ⟨b, hb⟩)) Jh ∧
      Nonempty (barOf 3 J ≃* barOf 3 Jh) ∧ Nat.card (barOf 3 J) ∣ Nat.card (barOf 3 L) := by
  obtain ⟨J₁, hJ₁, rfl⟩ := exists_comp_subgroupOf
    (inf_le_left : L ⊓ Subgroup.centralizer ({b} : Set G) ≤ L) hJ
  refine ⟨_, comp_map_fixSub hb hb3 hJ₁, ⟨liftEquiv J₁⟩, ?_⟩
  rw [Nat.card_congr (liftEquiv J₁).toEquiv]
  exact (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥(J₁.map (QuotientGroup.mk'
    (GLAPPrimeCore 3 ↥L))))).trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.HardMathSupport.Solomon.Coordinator
