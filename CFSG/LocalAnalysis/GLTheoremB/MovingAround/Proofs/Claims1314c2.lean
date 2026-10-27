module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1314b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1314c2

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

abbrev hyperW (p : ℕ) {X : Type} [Group X] (K Z : Subgroup X) : Subgroup X :=
  ⨆ (z : X) (_ : z ∈ Z) (_ : z ≠ 1),
    (GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
      GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)))

@[expose] def Input23_23N : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (K A Z : Subgroup X),
    IsComponentOf K ⊤ → IsLieChar (· = 2) ↥K →
    IsSCp p ⊤ A → CFSG.Open.pRank p A = 3 → A ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
    IsEkIn p 2 A Z → Z ≤ Subgroup.normalizer (K : Set X) →
    (p = 5 → ¬ Lemma1314.I2310Exc5 K) →
    (∃ z ∈ Z, z ≠ 1 ∧ ¬ Group.IsSolvable ↥(K ⊓ Subgroup.centralizer ({z} : Set X))) →
      K ≤ Subgroup.normalizer (hyperW p K Z : Set X)

section GroupTheory

variable {X : Type} [Group X]

theorem hyperW_le (p : ℕ) (K Z : Subgroup X) : hyperW p K Z ≤ K := by
  refine iSup₂_le fun z _ => iSup_le fun _ => sup_le ?_ ?_
  · exact (Lemma114Layer.glaPPrimeCoreOf_le_self p _).trans inf_le_left
  · exact (sSup_le fun L hL => (show GLAPComponent p _ L from hL).1).trans inf_le_left

theorem le_of_le_normalizer {K W : Subgroup X} (hK : CFSG.Open.IsQuasisimple ↥K) (hWK : W ≤ K)
    (hN : K ≤ Subgroup.normalizer (W : Set X)) (hW : ¬ W ≤ (Subgroup.center ↥K).map K.subtype) :
    K ≤ W := by
  haveI : (W.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWK).2 hN
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK (W.subgroupOf K) with
    h | h
  · exact absurd (fun w hw => ⟨⟨w, hWK hw⟩, h (Subgroup.mem_subgroupOf.2 hw), rfl⟩) hW
  · intro k hk
    have hk' : (⟨k, hk⟩ : ↥K) ∈ W.subgroupOf K := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hk'

theorem isSolvable_of_le_center {K J : Subgroup X} (hJ : J ≤ (Subgroup.center ↥K).map K.subtype) :
    Group.IsSolvable ↥J := by
  refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
  obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.1 (hJ a.2)
  obtain ⟨c', -, hcb⟩ := Subgroup.mem_map.1 (hJ b.2)
  have hcc : c' * c = c * c' := Subgroup.mem_center_iff.1 hc c'
  show (a : X) * b = b * a
  rw [← hca, ← hcb]
  exact congrArg Subtype.val hcc.symm

end GroupTheory

section ChevGenGen

theorem chevGenGenBlock_of_input23_23N (hL1313 : Lemma1313Statement) (hL133 : Lemma133Statement)
    (hN : Input23_23N) : Claims1314.ChevGenGenBlock := by
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR b hb hb1 hA3 hii hC2 hexc
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := h139a.1
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  obtain ⟨-, ⟨hLc, hL0bc, -⟩, -, -⟩ := hL1313 h hU hb hb1
  have hLc' : GLAPComponent p (Cg d) (Lemma1314.LOf p L0 d b) := hLc
  have hL0bc' : GLAPComponent p (Lemma1314.LOf p L0 d b ⊓ Cg b) (Lemma1314.L0bOf p L0 b) := hL0bc
  have hUN : U ≤ Subgroup.normalizer (Lemma1314.LOf p L0 d b : Set G) :=
    Lemma1314c.U_le_normalizer_LOf h h139a hL133 Bridges2.lemma133_comp_holds hU hb hb1
  rw [Claims1314.uConjJoin_eq_of_le_normalizer hUN]
  set L : Subgroup G := Lemma1314.LOf p L0 d b with hLdef
  set L0b : Subgroup G := Lemma1314.L0bOf p L0 b with hL0bdef
  have hLC : L ≤ Cg d := hLc'.1
  have hLsn : IsSubnormal L (Cg d) := hLc'.2.1
  have hbU : b ∈ U := Claims1314.mem_of_mem_centBar hb
  have hUC : U ≤ Cg d := hU.2.1
  have hUel : IsElemAbelian p U := hU.1.2.1
  have hUp : IsPGroup p ↥U := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hUel.2 g.1 g.2)⟩
  have hAel : IsElemAbelian p A := h.pair.1.2.1.1.1.2.1
  have hAp : IsPGroup p ↥A := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hAel.2 g.1 g.2)⟩
  have hdA : d ∈ A := h.hD.1 h.hd.1
  have hd1 : d ≠ 1 := h.hd.2
  have hdp : d ^ p = 1 := hAel.2 d hdA
  have hdC : d ∈ Cg d := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hAC : A ≤ Cg d := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨d, hdA⟩ ⟨a, ha⟩)
  have hKc : IsComponentOf (barX p (Cg d) L) ⊤ := Lemma1314.isComponentOf_barX_of_glaPComponent hLc'
  have hKlie : IsLieChar (· = 2) ↥(barX p (Cg d) L) :=
    Lemma1314.isLieChar_of_equiv (quotEquivBarX hp hLC hLsn).symm _ hC2
  have hAG : IsSCp p ⊤ A := (lemma104_ii_holds h.toSec13.toSec11.toSec10Fails h.pair).2
  have hAsc : IsSCp p ⊤ (barX p (Cg d) A) := by
    have hNp : ¬ p ∣ Nat.card ↥(GLAPPrimeCore p ↥(Cg d)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(Cg d)))
    exact isSCp_map_quotient (GLAPPrimeCore p ↥(Cg d)) hNp (isSCp_subgroupOf hAG hAC)
  have hArank : CFSG.Open.pRank p (barX p (Cg d) A) = 3 := (rank_barX_of_isPGroup hp hAp hAC).trans hA3
  have hAcent : barX p (Cg d) A ⊓
      Subgroup.centralizer (barX p (Cg d) L : Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d))) ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) (⟨d, hdC⟩ : ↥(Cg d)) ∈ barX p (Cg d) A ⊓
        Subgroup.centralizer (barX p (Cg d) L : Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d))) := by
      refine Subgroup.mem_inf.2 ⟨⟨⟨d, hdC⟩, Subgroup.mem_subgroupOf.2 hdA, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l, -, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 l.2)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Claims1314b.mk_ne_one hdC hdp hd1 hmem
  have hZA : barX p (Cg d) U ≤ barX p (Cg d) A :=
    CFSG.LocalAnalysis.GLTheoremB.barX_mono p (Claims1314.U_le_A h hU hUR)
  have hZel : IsElemAbelian p (barX p (Cg d) U) := isElemAbelian_barX hUel
  have hZcard : Nat.card (barX p (Cg d) U) = p ^ 2 :=
    (Claims1314b.card_barX_of_isPGroup hp hUp hUC).trans hU.1.2.2
  have hZN : barX p (Cg d) U ≤
      Subgroup.normalizer (barX p (Cg d) L : Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d))) :=
    barX_le_normalizer hUN
  have hbC : b ∈ Cg d := hUC hbU
  have hbp : b ^ p = 1 := hUel.2 b hbU
  have hbcent := barX_inf_centralizer hp hbC hLC (hUN hbU) (Claims1314b.isPGroup_zpowers hbp)
  have hcompb : GLAPComponent p (barX p (Cg d) (L ⊓ Cg b)) (barX p (Cg d) L0b) :=
    Prop115b.barX_glaPComponent_of_le hp (inf_le_left.trans hLC) hL0bc'
  have hcompb' : GLAPComponent p (barX p (Cg d) L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) (⟨b, hbC⟩ : ↥(Cg d))} :
        Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d)))) (barX p (Cg d) L0b) := by
    rw [← hbcent]
    exact hcompb
  have hJns : ¬ Group.IsSolvable ↥(barX p (Cg d) L0b) := by
    intro hsolv
    haveI := hsolv
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple
      (Lemma1313.isQuasisimple_barOf_of_pComp hcompb) inferInstance
  have hns : ¬ Group.IsSolvable ↥(barX p (Cg d) L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) (⟨b, hbC⟩ : ↥(Cg d))} :
        Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d)))) := by
    intro hsolv
    haveI := hsolv
    exact hJns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hcompb'.1))
  have hbbU : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) (⟨b, hbC⟩ : ↥(Cg d)) ∈ barX p (Cg d) U :=
    ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbU, rfl⟩
  have hbb1 := Claims1314b.mk_ne_one hbC hbp hb1
  have hnorm := hN p hp hp5 _ (barX p (Cg d) L) (barX p (Cg d) A) (barX p (Cg d) U)
    hKc hKlie hAsc hArank hAcent ⟨hZA, hZel, hZcard⟩ hZN hexc ⟨_, hbbU, hbb1, hns⟩
  have hJW : barX p (Cg d) L0b ≤ hyperW p (barX p (Cg d) L) (barX p (Cg d) U) :=
    le_iSup₂_of_le (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) (⟨b, hbC⟩ : ↥(Cg d))) hbbU
      (le_iSup_of_le hbb1 (le_sup_of_le_right (le_sSup (s := {J | GLAPComponent p
        (barX p (Cg d) L ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) (⟨b, hbC⟩ : ↥(Cg d))} :
            Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d)))) J}) hcompb')))
  have hWnc : ¬ hyperW p (barX p (Cg d) L) (barX p (Cg d) U) ≤
      (Subgroup.center ↥(barX p (Cg d) L)).map (barX p (Cg d) L).subtype :=
    fun hc => hJns (isSolvable_of_le_center (hJW.trans hc))
  have hmain : barX p (Cg d) L ≤ hyperW p (barX p (Cg d) L) (barX p (Cg d) U) :=
    le_of_le_normalizer hKc.2.2 (hyperW_le p _ _) hnorm hWnc
  refine hmain.trans (iSup₂_le fun z' hz' => iSup_le fun hz'1 => ?_)
  obtain ⟨w, hw, rfl⟩ := hz'
  have hwU : (w : G) ∈ U := Subgroup.mem_subgroupOf.1 hw
  have hw1 : (w : G) ≠ 1 := by
    intro h1
    apply hz'1
    have : w = 1 := Subtype.ext h1
    rw [this, map_one]
  have hwp : (w : G) ^ p = 1 := hUel.2 _ hwU
  have hcent := barX_inf_centralizer hp w.2 hLC (hUN hwU) (Claims1314b.isPGroup_zpowers hwp)
  have hDC : L ⊓ Cg (w : G) ≤ Cg d := inf_le_left.trans hLC
  have hY : barX p (Cg d) L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg d)) w} : Set (↥(Cg d) ⧸ GLAPPrimeCore p ↥(Cg d))) =
      barX p (Cg d) (L ⊓ Cg (w : G)) := hcent.symm
  rw [hY]
  refine sup_le ((Claims1314b.core_barX_le hDC).trans (CFSG.LocalAnalysis.GLTheoremB.barX_mono p ?_))
    ((Claims1314b.layer_barX_le hDC).trans (CFSG.LocalAnalysis.GLTheoremB.barX_mono p ?_))
  · exact le_iSup₂_of_le (w : G) hwU (le_iSup_of_le hw1 le_sup_left)
  · refine le_trans ?_ (le_iSup₂_of_le (w : G) hwU (le_iSup_of_le hw1 le_sup_right))
    refine sSup_le fun H hH => ?_
    have hH' : GLAPComponent p (L ⊓ Cg (w : G)) H := hH
    have hsn : IsSubnormal (L ⊓ Cg (w : G)) (Cg2 d (w : G)) := by
      rw [Lemma1314c.cg2_eq_inf]
      exact isSubnormal_inf hLsn _
    exact le_iSup₂_of_le (f := fun (H : Subgroup G)
        (_ : GLAPComponent p (Cg2 d (w : G)) H ∧ H ≤ L) => H) H
      ⟨CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_isSubnormal' hp hsn hH',
        hH'.1.trans inf_le_left⟩ le_rfl

end ChevGenGen

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1314c2

end
