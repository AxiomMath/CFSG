module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T173

private lemma not_dvd_card_center_of_isPGroup_two {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : IsPGroup 2 (Subgroup.center ↥S)) :
    ¬ p ∣ Nat.card (Subgroup.center ↥S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  rw [hn]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

theorem concl_of_trichotomy {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) {G₀ : Type} [Group G₀] [Finite G₀] (M : S172X.S172Model S B G₀)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hfact : ∀ (A : Subgroup G₀) (d : G₀), GLAIsBmax p A → IsStdElt p A d →
      StdVanishes A d ∨ StdTyped p A d ∨ StdExtends p A d) :
    T173Concl p S B K N := by
  obtain ⟨d, hdstd, -, hKd⟩ := exists_std_elt hcfg M hcfg.std
  have hKS : K ≤ S := K_le_of_cfg173 hcfg
  have hIS : closureIn K N ≤ S := closureIn_le_of_normal hcfg.normal hKS
  have hbmax : GLAIsBmax p M.β.range := isBmax_range hcfg M hZ
  have hlow : innerClosure M.β.range d ≤ piImg M (closureIn K N) := innerClosure_le_piImg hcfg M hZ hKd
  unfold T173Concl
  rcases hfact _ d hbmax hdstd with hV | hT | hE
  · exfalso
    obtain ⟨T', hT'1, hT'2, hT'N⟩ := exists_two_subgroup_of_hc hcfg M
    exact hV ⟨T', hT'1, hT'2, (sup_le_sup_right hlow _).trans hT'N⟩
  · left
    obtain ⟨hfam, h126⟩ := hT
    have hup : piImg M (closureIn K N) ≤ stdFamily p M.β.range d :=
      piImg_closureIn_le_stdFamily hcfg M hKd
    have heq : piImg M (closureIn K N) = innerClosure M.β.range d := le_antisymm (hup.trans hfam) hlow
    exact type126_of_model hcfg.prime M ⟨hcfg.qs.1⟩ hKS hIS (isPerfect_K hcfg)
      (isPerfect_closureIn (isPerfect_K hcfg)) hKd heq h126
  · right
    exact exists_alt_iv_of_model hcfg M hZ hKd hE

theorem i173FactD_of_models
    (hRig : CFSG.StandardType.GGLabelRigidInput) (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb)
    (hSplit : ModelFactSplit) (hFrame : ModelFactFrameD) (hMixed : ModelFactMixedD) : T173.I173FactD := by
  intro p Ω _ _ S B N D K x hcfg hD
  obtain ⟨l, f, F, hFf, hFfin, hFchar, V, hVa, hVm, hVfd, Q, hl, hF, hnd, hdim, hplus, harith, hZ, hM⟩ :=
    exists_model_D hRig hb hOdd hcfg hD
  obtain ⟨M⟩ := hM
  refine concl_of_trichotomy hcfg M (not_dvd_card_center_of_isPGroup_two hcfg.prime hcfg.odd hZ) ?_
  intro A d hA hd
  rcases harith with hdiv | ⟨hf1, hp3⟩
  · exact Or.inl (hSplit F V Q l p hnd hdim hl hcfg.prime hcfg.odd (by rw [hF]; exact hdiv) A d hA hd)
  · subst hp3
    have hq : Nat.card F = 2 := by rw [hF, hf1]; norm_num
    rcases Nat.even_or_odd l with he | ho
    · exact (hMixed F V Q l hnd hdim hl he hplus hq A d hA hd).imp id Or.inr
    · exact (hFrame hb F V Q l hnd hdim hl ho hplus hq A d hA hd).imp id Or.inl

theorem i173FactTD_of_models
    (hRig : CFSG.StandardType.GGLabelRigidInput) (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb)
    (hSplit : ModelFactSplit) (hFrame : ModelFactFrameTD) (hMixed : ModelFactMixedTD) : T173.I173FactTD := by
  intro p Ω _ _ S B N D K x hcfg hD
  obtain ⟨l, f, F, hFf, hFfin, hFchar, V, hVa, hVm, hVfd, Q, hl, hF, hnd, hdim, hminus, harith, hZ, hM⟩ :=
    exists_model_TD hRig hb hOdd hcfg hD
  obtain ⟨M⟩ := hM
  refine concl_of_trichotomy hcfg M (not_dvd_card_center_of_isPGroup_two hcfg.prime hcfg.odd hZ) ?_
  intro A d hA hd
  rcases harith with hdiv | hdiv
  · exact Or.inl (hSplit F V Q l p hnd hdim hl hcfg.prime hcfg.odd (by rw [hF]; exact hdiv) A d hA hd)
  · rcases Nat.even_or_odd l with he | ho
    · exact (hFrame hb F V Q l p hnd hdim hl he hminus hcfg.prime hcfg.odd (by rw [hF]; exact hdiv) A d hA
        hd).imp id Or.inl
    · exact (hMixed F V Q l p hnd hdim hl ho hminus hcfg.prime hcfg.odd (by rw [hF]; exact hdiv) A d hA
        hd).imp id Or.inr

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
