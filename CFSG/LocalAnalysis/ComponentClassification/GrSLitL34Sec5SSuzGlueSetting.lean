module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoreAt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {τ : ∀ (X : Type) [Group X], Prop} {t : G}
  {P : Subgroup G}

namespace L34NormalSettingAt

theorem gwTwoBalanced (h : L34NormalSettingAt τ G t P) : GWTwoBalanced G :=
  GrSLit.gwTwoBalanced_of_locallyTwoBalanced GrSLit.solomonCommutingCoreInput h.1.2.2.2.2.2.1

theorem commutator_self (h : L34NormalSettingAt τ G t P) : ⁅P, P⁆ = P := by
  have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent h.2.2.2.1
  have h2 : Group.IsPerfect ↥P :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe h.2.2.1).toMonoidHom)
      (subgroupOfEquivOfLe h.2.2.1).surjective
  exact (Subgroup.isPerfect_iff (H := P)).mp h2

theorem centralizer_le_normalizer (h : L34NormalSettingAt τ G t P) :
    centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
  (normal_subgroupOf_iff_le_normalizer h.2.2.1).mp h.2.2.2.2.1

end L34NormalSettingAt

theorem suz_cover_of_isPComponent
    (ht : orderOf t = 2) (hPt : P ≤ centralizer ({t} : Set G))
    (hPc : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hS : Blueprint.NativeSporadic.IsSporadic (↥P ⧸ Open.fusionZStar ↥P) .Suz) :
    (center (↥P ⧸ pPrimeCore 2 ↥P) = ⊥ ∧
        Blueprint.NativeSporadic.IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .Suz ∧ t ∉ P) ∨
      (Nat.card (center (↥P ⧸ pPrimeCore 2 ↥P)) = 2 ∧ Group.IsPerfect (↥P ⧸ pPrimeCore 2 ↥P) ∧
        Blueprint.NativeSporadic.IsSporadic
          ((↥P ⧸ pPrimeCore 2 ↥P) ⧸ center (↥P ⧸ pPrimeCore 2 ↥P)) .Suz) := by
  set O : Subgroup ↥P := pPrimeCore 2 ↥P with hO
  set Pb : Type := ↥P ⧸ O with hPb
  change (center Pb = ⊥ ∧ Blueprint.NativeSporadic.IsSporadic Pb .Suz ∧ t ∉ P) ∨
      (Nat.card (center Pb) = 2 ∧ Group.IsPerfect Pb ∧
        Blueprint.NativeSporadic.IsSporadic (Pb ⧸ center Pb) .Suz)
  have hperfP : Group.IsPerfect ↥P := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hPc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPt).toMonoidHom)
      (subgroupOfEquivOfLe hPt).surjective
  haveI : Group.IsPerfect ↥P := hperfP
  have hperfPb : Group.IsPerfect Pb :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hObot : pPrimeCore 2 Pb = ⊥ := by
    change pPrimeCore 2 (↥P ⧸ pPrimeCore 2 ↥P) = ⊥
    exact CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥P) 2
  have hZ2 : IsPGroup 2 (center Pb) := Sol78.center_isPGroup_two hObot
  obtain ⟨eC⟩ := CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥P
  have hsimpleS : IsSimpleGroup (↥P ⧸ Open.fusionZStar ↥P) :=
    CFSG.EvenSporadicStandard.Solomon78.suz_isSimpleGroup_of_isSporadic hS
  haveI : IsSimpleGroup (↥P ⧸ Open.fusionZStar ↥P) := hsimpleS
  have hsimple : IsSimpleGroup (Pb ⧸ center Pb) := MulEquiv.isSimpleGroup eC
  have hq : CFSG.Assembly.IsQuasisimple Pb :=
    ⟨Group.isPerfect_def.mp hperfPb, hsimple⟩
  have hsp : Blueprint.NativeSporadic.IsSporadic (Pb ⧸ center Pb) .Suz :=
    ⟨eC.trans hS.some⟩
  have hZ : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound :=
    suzCentralTwoGroupOrderBound_holds
  have hcardle : Nat.card (center Pb) ≤ 2 := hZ Pb hq hZ2 hsp
  by_cases hc : center Pb = ⊥
  · refine Or.inl ⟨hc, ?_, ?_⟩
    · have q : Pb ⧸ center Pb ≃* Pb :=
        (QuotientGroup.quotientMulEquivOfEq (G := Pb) hc).trans
          (QuotientGroup.quotientBot (G := Pb))
      exact ⟨q.symm.trans hsp.some⟩
    · intro htP
      let t' : ↥P := ⟨t, htP⟩
      have ht'2 : t' * t' = 1 := by
        apply Subtype.ext
        change t * t = 1
        rw [← pow_two, ← ht, pow_orderOf_eq_one]
      have ht'ne : t' ≠ 1 := by
        intro h1
        have ht1 : t ≠ 1 := by
          intro h2
          rw [h2, orderOf_one] at ht
          norm_num at ht
        exact ht1 (congrArg Subtype.val h1)
      have ht'ord : orderOf t' = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact ht'2) ht'ne
      have ht'cen : t' ∈ center ↥P := by
        rw [mem_center_iff]
        intro x
        apply Subtype.ext
        exact mem_centralizer_singleton_iff.mp (hPt x.2)
      have hmem : QuotientGroup.mk' O t' ∈ center Pb :=
        Subgroup.map_center_le_center (QuotientGroup.mk'_surjective O)
          (Subgroup.mem_map_of_mem (QuotientGroup.mk' O) ht'cen)
      have htO : t' ∈ O :=
        (QuotientGroup.eq_one_iff (N := O) t').mp (Subgroup.mem_bot.mp (hc ▸ hmem))
      have hdvd : orderOf t' ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O htO
      rw [ht'ord] at hdvd
      have hOodd : Odd (Nat.card O) := by
        change Odd (Nat.card (pPrimeCore 2 ↥P))
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      obtain ⟨m, hm⟩ := hOodd
      obtain ⟨k, hk⟩ := hdvd
      omega
  · refine Or.inr ⟨?_, hperfPb, hsp⟩
    have hgt : 1 < Nat.card (center Pb) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := center Pb)).mpr hc
    omega

theorem L34NormalSettingAt.suz_cover
    (h : L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P) :
    (center (↥P ⧸ pPrimeCore 2 ↥P) = ⊥ ∧
        Blueprint.NativeSporadic.IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .Suz ∧ t ∉ P) ∨
      (Nat.card (center (↥P ⧸ pPrimeCore 2 ↥P)) = 2 ∧ Group.IsPerfect (↥P ⧸ pPrimeCore 2 ↥P) ∧
        Blueprint.NativeSporadic.IsSporadic
          ((↥P ⧸ pPrimeCore 2 ↥P) ⧸ center (↥P ⧸ pPrimeCore 2 ↥P)) .Suz) :=
  suz_cover_of_isPComponent h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2

theorem odd_card_oddIn (P : Subgroup G) : Odd (Nat.card (oddIn P)) := by
  rw [oddIn, card_map_of_injective P.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

end CFSG.ComponentClassification.GrSLit.L34Sec5S
