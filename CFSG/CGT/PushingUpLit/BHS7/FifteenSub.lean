module

public import CFSG.CGT.PushingUpLit.BHS7.FifteenHyp
public import CFSG.CGT.PushingUpLit.BHS7.FifteenComp
public import CFSG.CGT.PushingUpLit.BHS7.ClaimA

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem mem_normalizer_iSup_dBar {g : MulAut ↥(vSub G T)} (hg : g ∈ autOn G (vSub G T)) :
    g ∈ Subgroup.normalizer ((⨆ B ∈ dBar G T, B : Subgroup (MulAut ↥(vSub G T))) :
      Set (MulAut ↥(vSub G T))) := by
  have key : ∀ g ∈ autOn G (vSub G T),
      A1b.conjSub g (⨆ B ∈ dBar G T, B : Subgroup (MulAut ↥(vSub G T))) ≤ ⨆ B ∈ dBar G T, B := by
    intro g hg
    rw [A1b.conjSub, Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hB x hx => ?_
    exact mem_iSup_dBar (conj_mem_dBar hB hg) hx
  exact B6.mem_normalizer_of_conjSub_le (key g hg) (key g⁻¹ ((autOn G (vSub G T)).inv_mem hg))

theorem mem_normalizer_of_conjSub_eq {G' : Type*} [Group G'] {g : G'} {H : Subgroup G'}
    (h : A1b.conjSub g H = H) : g ∈ Subgroup.normalizer (H : Set G') := by
  refine B6.mem_normalizer_of_conjSub_le h.le ?_
  have : A1b.conjSub g⁻¹ H = H := by
    calc A1b.conjSub g⁻¹ H = A1b.conjSub g⁻¹ (A1b.conjSub g H) := by rw [h]
      _ = H := by rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
  exact this.le

omit [Finite Γ] in
theorem liftSub_mono {V A : Subgroup Γ} {Y Y' : Subgroup (MulAut ↥V)} (h : Y ≤ Y') :
    liftSub V A Y ≤ liftSub V A Y' := fun _ hg => by
  obtain ⟨hgA, hgN, hgY⟩ := mem_liftSub_iff.1 hg
  exact mem_liftSub_iff.2 ⟨hgA, hgN, h hgY⟩

omit [Finite Γ] in
theorem mem_normalizer_liftSub {V A : Subgroup Γ} {Y : Subgroup (MulAut ↥V)} {t : Γ}
    (ht : t ∈ Subgroup.normalizer (V : Set Γ)) (htA : t ∈ A)
    (htY : conjAct V ⟨t, ht⟩ ∈ Subgroup.normalizer (Y : Set (MulAut ↥V))) :
    t ∈ Subgroup.normalizer ((liftSub V A Y : Subgroup Γ) : Set Γ) := by
  have h1 : A1b.conjSub t (liftSub V A Y) = liftSub V A Y := by
    rw [liftSub_conjSub ht htA, conjSub_eq_of_mem_normalizer' htY]
  have htN : t⁻¹ ∈ Subgroup.normalizer (V : Set Γ) := Subgroup.inv_mem _ ht
  have htY' : conjAct V ⟨t⁻¹, htN⟩ ∈ Subgroup.normalizer (Y : Set (MulAut ↥V)) := by
    have : conjAct V ⟨t⁻¹, htN⟩ = (conjAct V ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact Subgroup.inv_mem _ htY
  have h2 : A1b.conjSub t⁻¹ (liftSub V A Y) = liftSub V A Y := by
    rw [liftSub_conjSub htN (A.inv_mem htA), conjSub_eq_of_mem_normalizer' htY']
  exact B6.mem_normalizer_of_conjSub_le h1.le h2.le

theorem fifteen_comp (h : MinCex G T) (h5 : Seven5 G T)
    (h13 : Seven13 G T) (h14 : Seven14 G T) :
    ∃ E : Subgroup (MulAut ↥(vSub G T)),
      @IsCompType ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub h.charTwo h.sylow)) E ∧
      E ≤ autOn G (vSub G T) ∧ IsSubnormal (liftSub (vSub G T) G E) G ∧
      ¬ liftSub (vSub G T) G E ≤ cStarIn G T ∧
      baum T ≤ Subgroup.normalizer ((liftSub (vSub G T) G E : Subgroup Γ) : Set Γ) ∧
      ∀ b ∈ baum T, ∀ hb : b ∈ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ),
        A1b.conjSub (conjAct (vSub G T) ⟨b, hb⟩) E = E := by
  classical
  have hG := h.charTwo
  have hT : IsSylowTwoOf T G := h.sylow
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub hG hT
  let _ : CommGroup ↥(vSub G T) := commGroupOfElemAbelian hV
  have hTG : T ≤ G := hT.1
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hV2 : ∀ v : ↥(vSub G T), v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hV.2 v v.2)
  have hH := hyp43_dBar h h5 h13 h14
  obtain ⟨F, hF, hFC⟩ := exists_isBTBlock_not_le h h5
  obtain ⟨A, hpair⟩ := h14 F hF hFC
  have hAy : A ∈ ySet G T := ⟨F, hF, hFC, hpair⟩
  set P' : Subgroup (MulAut ↥(vSub G T)) := ⨆ B ∈ dBar G T, B with hP'
  have hFP : autOn F (vSub G T) ≤ P' := autOn_le_iSup_dBar hTG hF.le hAy hpair.2.1
  have hout : autOn A (vSub G T) ∈ dOut P' (dBar G T) (P' ⊓ mBar G T) :=
    ⟨autOn_mem_dBar hAy, not_mem_dCore_of_block hV hTG hF.le hAy hpair.2.1 hFC hFP
      (inf_le_right.trans inf_le_right)⟩
  obtain ⟨hA₀E, hEP, hPN, htype, hconj⟩ := component_of_hyp43 hH hV2 rfl rfl rfl hout
  set E : Subgroup (MulAut ↥(vSub G T)) :=
    compGen P' (dBar G T) (P' ⊓ mBar G T) (autOn A (vSub G T)) with hE
  have hP'G : P' ≤ autOn G (vSub G T) := iSup₂_le fun B hB => le_autOn_of_mem_dBar hB hTG
  have hEG : E ≤ autOn G (vSub G T) := hEP.trans hP'G
  have hAG : A ≤ G := hpair.1.trans ((inf_le_left : baum T ≤ T).trans hTG)
  have hFE : autOn F (vSub G T) ≤ E := by
    have h1 : autOn F (vSub G T) = ⁅autOn F (vSub G T), autOn A (vSub G T)⁆ := by
      rw [← autOn_commutator_eq (hF.le.trans hGN) (hAG.trans hGN), hpair.2.1]
    rw [h1]
    refine Subgroup.commutator_le.2 fun e he a ha => ?_
    rw [commutatorElement_def]
    have h2 : e * a * e⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (hPN (hFP he)) a).1 (hA₀E ha)
    exact E.mul_mem h2 (E.inv_mem (hA₀E ha))
  have hFÊ : F ≤ liftSub (vSub G T) G E := fun x hx =>
    mem_liftSub_iff.2 ⟨hF.le hx, hGN (hF.le hx),
      hFE (mem_autOn_iff.2 ⟨⟨x, hGN (hF.le hx)⟩, hx, rfl⟩)⟩
  have hBT : ∀ b ∈ baum T, ∀ hb : b ∈ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ),
      A1b.conjSub (conjAct (vSub G T) ⟨b, hb⟩) E = E := by
    intro b hbB hb
    have hbT : b ∈ T := (inf_le_left : baum T ≤ T) hbB
    have hbN : b ∈ Subgroup.normalizer (F : Set Γ) := baum_le_normalizer_of_isBTBlock hF hbB
    have hX : autOn F (vSub G T) ≠ ⊥ :=
      CFSG.CGT.PushingUpLit.BHS5.autOn_ne_bot_of_not_le_centralizer (hF.le.trans hGN)
        (fun hc => hFC (fun x hx => centralizer_vSub_le_cStarIn G T ⟨hF.le hx, hc hx⟩))
    refine hconj _ (mem_autOn_iff.2 ⟨⟨b, hb⟩, hbT, rfl⟩) _ hX hFE ?_
    rw [← autOn_conjSub hb, conjSub_eq_of_mem_normalizer' hbN]
  refine ⟨E, ?_, hEG, ?_, ?_, ?_, hBT⟩
  · exact (htype.imp (fun h => ⟨_, h⟩) fun h => ⟨_, _, h⟩)
  ·
    have hN₁G : liftSub (vSub G T) G P' ≤ G := liftSub_le G P'
    have hÊN₁ : liftSub (vSub G T) G E ≤ liftSub (vSub G T) G P' := liftSub_mono hEP
    have hN₁N : liftSub (vSub G T) G P' ≤ Subgroup.normalizer
        ((liftSub (vSub G T) G E : Subgroup Γ) : Set Γ) := fun t ht => by
      obtain ⟨htG, htN, htP⟩ := mem_liftSub_iff.1 ht
      exact mem_normalizer_liftSub htN htG (hPN htP)
    have hGN₁ : G ≤ Subgroup.normalizer ((liftSub (vSub G T) G P' : Subgroup Γ) : Set Γ) :=
      fun g hg => mem_normalizer_liftSub (hGN hg) hg
        (mem_normalizer_iSup_dBar (mem_autOn_iff.2 ⟨⟨g, hGN hg⟩, hg, rfl⟩))
    exact IsSubnormal.step hÊN₁ ((Subgroup.normal_subgroupOf_iff_le_normalizer hÊN₁).2 hN₁N)
      (isSubnormal_of_le_of_le_normalizer hN₁G hGN₁)
  · exact fun hle => hFC (hFÊ.trans hle)
  · intro b hbB
    have hbT : b ∈ T := (inf_le_left : baum T ≤ T) hbB
    have hbG : b ∈ G := hTG hbT
    exact mem_normalizer_liftSub (hGN hbG) hbG (mem_normalizer_of_conjSub_eq (hBT b hbB (hGN hbG)))

end CFSG.CGT.PushingUpLit.BHS7
