module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_RedDefs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Glue
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i112b_twoLocalRank_le_of_injective {Z X : Type*} [Group Z] [Finite Z] [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (ι : Z →* X) (hι : Function.Injective ι) :
    GLATwoLocalRank p Z ≤ GLATwoLocalRank p X := by
  have : Fact p.Prime := ⟨hp⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card X := hE ▸ Subgroup.card_le_card_group E
    change CFSG.Open.pRank p H ≤ Nat.card X
    omega
  refine csSup_le' fun k hk => ?_
  obtain ⟨H, ⟨T, hT, hT2, rfl⟩, rfl⟩ := hk
  have hTm : T.map ι ≠ ⊥ := fun h => hT ((Subgroup.map_eq_bot_iff_of_injective T hι).1 h)
  have h1 : CFSG.Open.pRank p (Subgroup.normalizer (T : Set Z)) =
      CFSG.Open.pRank p ((Subgroup.normalizer (T : Set Z)).map ι) :=
    (pRank_map_eq_of_injective hp.one_lt ι hι _).symm
  have h2 : CFSG.Open.pRank p ((Subgroup.normalizer (T : Set Z)).map ι) ≤
      CFSG.Open.pRank p (Subgroup.normalizer ((T.map ι : Subgroup X) : Set X)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.le_normalizer_map ι)
  have h3 : CFSG.Open.pRank p (Subgroup.normalizer ((T.map ι : Subgroup X) : Set X)) ≤
      GLATwoLocalRank p X :=
    le_csSup hbdd ⟨_, ⟨T.map ι, hTm, hT2.map _, rfl⟩, rfl⟩
  exact h1.trans_le (h2.trans h3)

theorem i112b_center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center A = ⊥) : Subgroup.center B = ⊥ := by
  rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]

theorem i112b_glaPComponent_of_isComponentOf {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hO : GLAPPrimeCore p Q = ⊥) {M : Subgroup Q} (hM : IsComponentOf M ⊤) :
    GLAPComponent p ⊤ M := by
  have hcore : GLAPPrimeCore p ↥(⊤ : Subgroup Q) = ⊥ := by
    have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q)
    rw [hO] at h
    exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).injective
      (by simpa using h)
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Q))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  refine ⟨le_top, hM.2.1, ?_, ?_⟩
  · have hsn : IsSubnormal (barX p ⊤ M) ⊤ := by
      have := isSubnormal_barX p (C := (⊤ : Subgroup Q)) hM.2.1
      rwa [barX_self] at this
    refine ⟨le_top, hsn, ?_⟩
    let e : ↥M ≃* ↥(barX p (⊤ : Subgroup Q) M) :=
      (Subgroup.subgroupOfEquivOfLe (le_top : M ≤ ⊤)).symm.trans
        (Subgroup.equivMapOfInjective _ _ hinj)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hM.2.2
  · intro J hJ _ heq
    have : J.subgroupOf (⊤ : Subgroup Q) = M.subgroupOf (⊤ : Subgroup Q) :=
      Subgroup.map_injective hinj heq
    have h2 : J = M := by
      have := congrArg (Subgroup.map (⊤ : Subgroup Q).subtype) this
      rwa [Subgroup.map_subgroupOf_eq_of_le le_top, Subgroup.map_subgroupOf_eq_of_le le_top]
        at this
    exact hJ.ne h2

theorem i112_of_red (h : I112Red) : I112 := by
  intro X _ _ hX p hp hp2 B hB hrank L hL hnL
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  set N : Subgroup ↥(⊤ : Subgroup X) := GLAPPrimeCore p ↥(⊤ : Subgroup X) with hNdef
  have hN : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  set ι : ↥(⊤ : Subgroup X) →* X := (⊤ : Subgroup X).subtype with hιdef
  have hι : Function.Injective ι := Subtype.val_injective
  have hQK : CFSG.Open.IsKGroup (↥(⊤ : Subgroup X) ⧸ N) :=
    isKGroup_quotient' (isKGroup_subgroup' hX _) N
  have hQcore : GLAPPrimeCore p (↥(⊤ : Subgroup X) ⧸ N) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBel : IsElemAbelian p (barX p ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :=
    isElemAbelian_barX hB
  have hrankQ : GLATwoLocalRank p (↥(⊤ : Subgroup X) ⧸ N) ≤
      CFSG.Open.pRank p (barX p ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) := by
    rw [rank_barX_of_isPGroup hp hBp le_top]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hN).trans
      ((i112b_twoLocalRank_le_of_injective hp ι hι).trans hrank)
  have hnLQ : ¬ (barX p ⊤ B : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) ≤
      Subgroup.normalizer ((barX p ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :
        Set (↥(⊤ : Subgroup X) ⧸ N)) := by
    intro hle
    apply hnL
    intro b hb
    exact i113g_mem_normalizer_of_bar hL (hle ⟨⟨b, Subgroup.mem_top b⟩, hb, rfl⟩)
  have hLbar : GLAPComponent p ⊤ (barX p ⊤ L : Subgroup (↥(⊤ : Subgroup X) ⧸ N)) :=
    i112b_glaPComponent_of_isComponentOf hQcore hL.2.2.1
  obtain ⟨h3, hrel, hcen⟩ := h (↥(⊤ : Subgroup X) ⧸ N) hQK p hp hp2 hQcore _ hBel hrankQ _ hLbar
    hnLQ
  rw [i113g_relIndex_barX hL] at hrel
  refine ⟨h3, hrel, ?_⟩
  have e := quotEquivBarX hp (le_top : L ≤ ⊤) hL.2.1
  rcases hcen with hc | hc
  · left
    intro hbot
    exact hc (i112b_center_eq_bot_of_equiv e hbot)
  · right
    exact i113g_isL2_of_equiv e.symm hc

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
