module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertFacts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23.Map
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23.Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23.Ident

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
  CFSG.RankThree.PartTwo.Census.Carrier.G2Three

section Assembly


theorem le_and_mem_q8Fam (hR : S7.RowClassAEmpty) {m : ℕ} {Y : Type} [Group Y] [Finite Y]
    {Φ : Set (Subgroup Y)} {K : Subgroup Y} (hc : Ctx m Y Φ K) (h2 : NoNormalTwo Y)
    (hF : FStarSimple Y) (hcl : ¬ SubClass Φ K (genFittingFStar Y))
    (hLc : Nat.card (genFittingFStar Y) = 4245696) {M : Subgroup Y} (hM : M ∈ Φ) :
    M ≤ genFittingFStar Y ∧ M ∈ q8Fam Y := by
  set L := genFittingFStar Y with hLdef
  haveI : IsSimpleGroup ↥L := hF.1
  have hLn : L.Normal := genFittingFStar_normal Y
  have hC := S7Ident.centralizer_eq_bot_of_fStarSimple hF
  obtain ⟨z, hz⟩ := (hc.hyp.hyp.omega1 M hM).1
  set H := omegaGen (S7Ident.lOrbit L M) with hH
  obtain ⟨hzH, hO⟩ :=
    S7Ident.orbitHyp_of_ctx hc h2 hF hM (S7.aEmpty_lOrbit hR hc h2 hF hcl hM) hz
  have hI := S7Ident.orbitIdent_of_stepIH hc.ih
    (by rw [← hc.card]; exact Subgroup.card_le_card_group _) hO
  have hMne : M ≠ ⊥ := fun h => hz.ne_one (Subgroup.mem_bot.mp (h ▸ hz.mem))
  have hLH : L ≤ H := S7Ident.le_omegaGen_lOrbit hLn hC hMne
  have hMH : M ≤ H := le_omegaGen S7Ident.mem_lOrbit_self
  have hcard : Nat.card ↥(L.subgroupOf H) = 4245696 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv, hLc]
  have hcH : Nat.card (genFittingFStar ↥H) = 4245696 := by
    rw [S7Ident.genFittingFStar_eq_of_le hLn hF.2 hC hLH, hcard]
  have hl := orbitLie_of_card_fStar hO hI hcH
  haveI : (L.subgroupOf H).Normal := hLn.subgroupOf H
  have hne : L.subgroupOf H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have htop := eq_top_of_orbitLie hO hl (L.subgroupOf H) hne
  have hHL : H ≤ L := fun x hx => by
    have : (⟨x, hx⟩ : ↥H) ∈ L.subgroupOf H := htop ▸ Subgroup.mem_top _
    exact this
  refine ⟨hMH.trans hHL, ?_⟩
  obtain ⟨f⟩ := nonempty_mulEquiv_q8_of_orbitLie hO hl
  exact ⟨(Subgroup.subgroupOfEquivOfLe hMH).symm.trans f⟩

theorem thm3RTwoClassG23_of_ident (hR : S7.RowClassAEmpty) (m : ℕ) : Thm3RTwoClassG23 m := by
  intro Y _ _ Φ K hc _ h2 hF hcl hG
  set L := genFittingFStar Y with hLdef
  obtain ⟨θ₀⟩ := HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel hG
  let θ : ↥L ≃* H3 := θ₀.trans adjointEquivR3
  have hLc : Nat.card ↥L = 4245696 := by
    rw [Nat.card_congr θ.toEquiv]
    exact card_R3
  have hmem := fun M (hM : M ∈ Φ) => le_and_mem_q8Fam hR hc h2 hF hcl hLc hM
  have hLtop : L = ⊤ := by
    rw [eq_top_iff, ← hc.gen]
    exact iSup₂_le fun M hM => (hmem M hM).1
  let eY : Y ≃* ↥L := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)
  let D : G23Data Y := g23Data_R3.map (eY.trans θ).symm
  obtain ⟨J, hJ, hJK⟩ : ∃ J ∈ Φ, ∀ a : Y, conjSub a K ≠ J := by
    by_contra hno
    push_neg at hno
    exact hcl fun N hN => by
      obtain ⟨a, ha⟩ := hno N hN
      exact ⟨a, by rw [hLtop]; trivial, ha⟩
  have hΦ : Φ = q8Fam Y :=
    D.eq_q8Fam (fun M hM => (hmem M hM).2) hc.hyp.hyp.conjInvariant hc.mem hJ hJK
  subst hΦ
  have hA := D.aStar_eq hc.mem
  have hV := D.vStar_eq hc.mem
  refine ⟨⟨hA.trans hV.symm, fun L' hL' hnot => absurd (by rw [hV]; exact hL') hnot⟩, Or.inl ?_⟩
  show CFSG.Blueprint.LieModel (SecQuot (omegaGen (aStar (q8Fam Y) K))) .G2 0 3 1
  rw [hA, hc.gen]
  exact CFSG.Blueprint.LieModel.of_mulEquiv (eY.symm.trans (S5.secQuotTopEquiv' hc.odd)) hG


theorem thm3RTwoClassG23_proved (m : ℕ) : Thm3RTwoClassG23 m :=
  thm3RTwoClassG23_of_ident S7Cert.rowClassAEmpty_proved m

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7G23
