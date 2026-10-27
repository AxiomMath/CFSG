module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Base
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S17

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem img_E (h10 : Node10 d z₀) (h49 : d.Thm49Statement) (hd : d.Hyp) : img d d.E = ⊥ :=
  imgIn_eq_bot_of_le_centralizer d.s56V ((hd.s56_E_le_V h49).trans (V_le_Cv h10))

theorem E_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : d.E ≤ Hg d :=
  ((hd.s56_E_le_V h49).trans (V_le_M)).trans (M_le_Hg h49 hd)

theorem zpowers_t_le_Hg (h49 : d.Thm49Statement) (hd : d.Hyp) : zpowers d.t ≤ Hg d :=
  zpowers_le.2 (t_mem_Hg h49 hd)

theorem img_A (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀) :
    img d d.A = zpowers (star d d.t) := by
  show imgIn d.s56V (d.E ⊔ zpowers d.t) = _
  rw [imgIn_sup_of_le d.s56V (E_le_Hg h49 hd) (zpowers_t_le_Hg h49 hd), img_E h10 h49 hd |> fun h =>
    show imgIn d.s56V d.E = ⊥ from h, bot_sup_eq, imgIn_zpowers d.s56V (t_mem_Hg h49 hd)]
  rfl

theorem V5_mem_Cv (h10 : Node10 d z₀) {y : G} (hy : IsV5 d y) (hys : y ∈ sylT d)
    (hyz : y * z₀ = z₀ * y) : y ∈ Cv d := by
  obtain ⟨hc, -⟩ := h10.1 y hy hys hyz
  exact mem_centralizer_iff.2 fun v hv => (hc v (V_le_Q2 hv)).symm

theorem IsV5.mem_M (hd : d.Hyp) {y : G} (hy : IsV5 d y) : y ∈ d.M := by
  obtain ⟨hyC, hρ⟩ := hy
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  show y ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
  rw [hd.mem_normalizer_tSup_iff hED hyC, hρ]
  exact Model.twoF4H_le_normalizer_hatE (Model.twoF4S_le_twoF4H (Model.parrottV_mem_twoF4S 5))

theorem img_centralizer_A (h49 : d.Thm49Statement) (hd : d.Hyp) (h10 : Node10 d z₀)
    (hV5 : d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y) :
    img d (centralizer (d.A : Set G)) = zpowers (star d d.t) := by
  rcases hd.centralizer_A with ⟨-, hC⟩ | ⟨hr, hC⟩
  · rw [hC]
    exact img_A h49 hd h10
  · obtain ⟨y, hy, hys, hyz⟩ := hV5 hr
    obtain ⟨hyC, hρ⟩ := hy
    rw [hC y hyC hρ]
    have hyM : y ∈ Hg d := M_le_Hg h49 hd (IsV5.mem_M hd ⟨hyC, hρ⟩)
    have h1 : imgIn d.s56V (zpowers y) = ⊥ := by
      rw [imgIn_zpowers d.s56V hyM]
      have : actFun d.s56V y = 1 := (actFun_eq_one_iff d.s56V hyM).2
        (V5_mem_Cv h10 ⟨hyC, hρ⟩ hys hyz)
      rw [this]
      simp
    show imgIn d.s56V (d.A ⊔ zpowers y) = _
    have hA : d.A ≤ normalizer (d.s56V : Set G) := (d.s56_A_le_M).trans (M_le_Hg h49 hd)
    rw [imgIn_sup_of_le d.s56V hA (zpowers_le.2 hyM), h1, sup_bot_eq]
    exact img_A h49 hd h10

theorem CMt_inf_V (h49 : d.Thm49Statement) (hd : d.Hyp) : CMt d ⊓ d.s56V = d.E := by
  refine le_antisymm (fun v hv => ?_) (fun e he => ?_)
  · obtain ⟨⟨-, hvC⟩, hvV⟩ := hv
    have hvt : v * d.t = d.t * v := mem_centralizer_singleton_iff.1 hvC
    exact (hd.s56_V_eps_eq_one_iff h49 hvV).1 (hd.s56_eps_of_comm hvt)
  · exact ⟨mem_inf.2 ⟨d.s56_E_le_M he, mem_centralizer_singleton_iff.2
      (hd.L_comm_t (d.s56_E_le_L he))⟩, hd.s56_E_le_V h49 he⟩

theorem CMt_sup_V (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    CMt d ⊔ d.s56V = d.M := by
  refine le_antisymm (sup_le CMt_le_M V_le_M) (fun m hm => ?_)
  obtain ⟨v, hvV, hvc⟩ := exists_V_mul h49 hd hz hm
  have : m = (v * (v⁻¹ * m)) := by group
  rw [this]
  exact mul_mem (mem_sup_right hvV) (mem_sup_left hvc)

theorem card_M_eq (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀) :
    Nat.card d.M = 32 * Nat.card (CMt d) := by
  have h := card_sup_mul_card_inf' (H := CMt d) (N := d.s56V)
    (CMt_le_M.trans (M_le_Hg h49 hd))
  rw [CMt_sup_V h49 hd hz, CMt_inf_V h49 hd, h10.card_V, (hd.A_facts).1] at h
  have h2 : Nat.card d.M * 32 = Nat.card (CMt d) * 2 ^ 10 := h
  omega

theorem CMt_inf_Cv (hd : d.Hyp) (h49 : d.Thm49Statement) :
    CMt d ⊓ centralizer (d.s56V : Set G) = centralizer (d.A : Set G) ⊓ centralizer (d.s56V : Set G) := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨hgC, hgV⟩ := hg
    refine ⟨hd.s56_mem_centralizer_A_iff.2 ⟨fun e he => ?_, ?_⟩, hgV⟩
    · exact mem_centralizer_iff.1 hgV e (hd.s56_E_le_V h49 he)
    · exact mem_centralizer_singleton_iff.1 (mem_inf.1 hgC).2
  · obtain ⟨hgA, hgV⟩ := hg
    exact ⟨mem_inf.2 ⟨d.s56_centralizer_A_le_M hgA,
      mem_centralizer_singleton_iff.2 (hd.s56_mem_centralizer_A_iff.1 hgA).2⟩, hgV⟩

theorem card_zpowers_star_t (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    Nat.card (zpowers (star d d.t)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf (star d d.t) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact star_t_mul_self h49 hd) (star_t_ne h49 hd hz)
  rw [Nat.card_zpowers, ho]

theorem card_img_CMt (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (hV5 : d.ρ.range = ⊤ → ∃ y, IsV5 d y ∧ y ∈ sylT d ∧ y * z₀ = z₀ * y) :
    Nat.card (img d (CMt d)) = 640 := by
  have hC1 := card_imgIn_mul_card d.s56V (CMt d)
  have hA1 := card_imgIn_mul_card d.s56V (centralizer (d.A : Set G))
  have hCle : CMt d ≤ normalizer (d.s56V : Set G) := CMt_le_Hg h49 hd
  have hAle : centralizer (d.A : Set G) ≤ normalizer (d.s56V : Set G) :=
    d.s56_centralizer_A_le_M.trans (M_le_Hg h49 hd)
  rw [inf_eq_left.2 hCle] at hC1
  rw [inf_eq_left.2 hAle] at hA1
  have himg : imgIn d.s56V (centralizer (d.A : Set G)) = zpowers (star d d.t) :=
    img_centralizer_A h49 hd h10 hV5
  rw [himg, card_zpowers_star_t h49 hd hz] at hA1
  have hk : Nat.card (centralizer (d.A : Set G) ⊓ centralizer (d.s56V : Set G) : Subgroup G) =
      Nat.card (CMt d ⊓ centralizer (d.s56V : Set G) : Subgroup G) := by rw [CMt_inf_Cv hd h49]
  obtain ⟨hMc, -, -, -, -, -, -⟩ := hd.s56_structure_M h49
  have hM32 := card_M_eq h49 hd hz h10
  have hkpos : 0 < Nat.card (CMt d ⊓ centralizer (d.s56V : Set G) : Subgroup G) := Nat.card_pos
  rw [← hk] at hC1
  show Nat.card (imgIn d.s56V (CMt d)) = 640
  have h1 : 32 * (Nat.card (imgIn d.s56V (CMt d)) *
      Nat.card (centralizer (d.A : Set G) ⊓ centralizer (d.s56V : Set G) : Subgroup G)) =
      20480 * Nat.card (centralizer (d.A : Set G) ⊓ centralizer (d.s56V : Set G) : Subgroup G) := by
    rw [hC1, ← hM32, hMc]
    omega
  have h2 : Nat.card (imgIn d.s56V (CMt d)) * Nat.card (centralizer (d.A : Set G) ⊓
      centralizer (d.s56V : Set G) : Subgroup G) = 640 * Nat.card (centralizer (d.A : Set G) ⊓
      centralizer (d.s56V : Set G) : Subgroup G) := by omega
  exact Nat.eq_of_mul_eq_mul_right (hk ▸ hkpos) h2

theorem Xg_le_CMt (hd : d.Hyp) : Xg d ≤ CMt d :=
  zpowers_le.2 (mem_inf.2 ⟨hd.s56_x5_mem_M, mem_centralizer_singleton_iff.2 hd.s56_x5_comm_t⟩)

theorem t_mem_CMt : d.t ∈ CMt d :=
  mem_inf.2 ⟨t_mem_M, mem_centralizer_singleton_iff.2 rfl⟩

theorem Us_le_img_CMt (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) :
    Us d ≤ img d (CMt d) := by
  have h1 : Us d = ⁅img d (d.s56Q0 ⊓ CMt d), img d (Xg d)⁆ := by
    unfold Us
    rw [pCoreOf_CMt h49 hd hz]
  rw [h1]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have ha' : a ∈ img d (CMt d) := imgIn_mono _ inf_le_right ha
  have hb' : b ∈ img d (CMt d) := imgIn_mono _ (Xg_le_CMt hd) hb
  exact (img d (CMt d)).mul_mem ((img d (CMt d)).mul_mem ((img d (CMt d)).mul_mem ha' hb')
    ((img d (CMt d)).inv_mem ha')) ((img d (CMt d)).inv_mem hb')

theorem P_le_img_CMt (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {y₁ : G}
    (hy : IsV1 d z₀ y₁) :
    (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) ≤ img d (CMt d) := by
  refine sup_le (sup_le (Us_le_img_CMt h49 hd hz) (imgIn_mono _ (Xg_le_CMt hd))) ?_
  rw [star_eq, ← imgIn_zpowers d.s56V (y1_mem_Hg h49 hd hy)]
  exact imgIn_mono _ (zpowers_le.2 (hy.mem_CMt hd))

theorem P_le_stab (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {y₁ : G} (hy : IsV1 d z₀ y₁) :
    (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) ≤
      MulAction.stabilizer (MulAut ↥d.s56V) (⟨z₀, hz.mem_V⟩ : ↥d.s56V) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Us_eq_img_Q h49 hd hz h10]
    exact imgIn_le_stabilizer d.s56V d.s56Q _ (fun g hg _ => hz.comm_Q g hg)
  · refine imgIn_le_stabilizer d.s56V (Xg d) _ (fun g hg _ => ?_)
    obtain ⟨n, rfl⟩ := hg
    exact (Commute.zpow_left (show Commute d.x₅ z₀ from hz.comm_x) n).eq
  · rw [star_eq, ← imgIn_zpowers d.s56V (y1_mem_Hg h49 hd hy)]
    refine imgIn_le_stabilizer d.s56V (zpowers y₁) _ (fun g hg _ => ?_)
    obtain ⟨n, rfl⟩ := hg
    exact (Commute.zpow_left (show Commute y₁ z₀ from hy.2.1) n).eq

theorem card_P (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h05 : Node05 d z₀)
    (h10 : Node10 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    Nat.card (Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) : Subgroup (MulAut ↥d.s56V)) = 320 := by
  have hfrob := hy.isFrob h49 hd hz h10
  have hQ2 : IsPGroup 2 (img d d.s56Q) :=
    isPGroup_imgIn d.s56V (IsPGroup.to_le (Data.s56_Q0_isPGroup d) (Q_le_Q0 hd))
  have hxn : star d d.x₅ ∈ normalizer ((img d d.s56Q : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) :=
    actFun_mem_normalizer_imgIn d.s56V d.s56Q (x5_mem_Hg h49 hd)
      (hd.s56_M_le_normalizer_Q h49 hd.s56_x5_mem_M)
  have hyn : star d y₁ ∈ normalizer ((img d d.s56Q : Subgroup (MulAut ↥d.s56V)) :
      Set (MulAut ↥d.s56V)) :=
    actFun_mem_normalizer_imgIn d.s56V d.s56Q (y1_mem_Hg h49 hd hy)
      (hd.s56_M_le_normalizer_Q h49 (hy.mem_M hd))
  have hX : img d (Xg d) = zpowers (star d d.x₅) :=
    imgIn_zpowers d.s56V (x5_mem_Hg h49 hd)
  rw [Us_eq_img_Q h49 hd hz h10, hX, hfrob.card_sup_of_isPGroup hQ2 hxn hyn,
    card_img_Q h49 hd h05 h10]
  norm_num

theorem node17s (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h05 : Node05 d z₀)
    (h09 : Node09 d z₀) (h10 : Node10 d z₀) : Node17s d z₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hV5, -⟩ := h09
  have hUs := Us_eq_img_Q h49 hd hz h10
  refine ⟨?_, ?_, ?_⟩
  · rw [hUs]
    exact isElemAbelian_img_Q h49 hd h10
  · rw [hUs, card_img_Q h49 hd h05 h10]
    norm_num
  · intro y₁ hy
    set P : Subgroup (MulAut ↥d.s56V) := Us d ⊔ img d (Xg d) ⊔ zpowers (star d y₁) with hP
    have hPC : P ≤ img d (CMt d) := P_le_img_CMt h49 hd hz hy
    have hPstab := P_le_stab h49 hd hz h10 hy
    have htnot : star d d.t ∉ P := fun h => star_t_not_mem_stab h49 hd hz (hPstab h)
    have hbot : zpowers (star d d.t) ⊓ P = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      obtain ⟨haT, haP⟩ := ha
      rcases eq_one_or_of_mem_zpowers (star_t_mul_self h49 hd) haT with h | h
      · rw [h]
        exact one_mem _
      · exact absurd (h ▸ haP) htnot
    have hcent : ∀ a ∈ P, star d d.t * a = a * star d d.t := by
      intro a ha
      obtain ⟨c, hcC, hcN, rfl⟩ := (mem_imgIn_iff d.s56V (CMt d)).1 (hPC ha)
      have hct : d.t * c = c * d.t := (mem_centralizer_singleton_iff.1 (mem_inf.1 hcC).2).symm
      exact actFun_comm_of_comm d.s56V hct
    refine ⟨?_, hbot, hcent⟩
    have htC : zpowers (star d d.t) ≤ img d (CMt d) := by
      rw [star_eq, ← imgIn_zpowers d.s56V (t_mem_Hg h49 hd)]
      exact imgIn_mono _ (zpowers_le.2 t_mem_CMt)
    have hle : zpowers (star d d.t) ⊔ P ≤ img d (CMt d) := sup_le htC hPC
    have hPnorm : P ≤ normalizer ((zpowers (star d d.t) : Subgroup (MulAut ↥d.s56V)) :
        Set (MulAut ↥d.s56V)) := by
      intro a ha
      have hac : a ∈ centralizer ((zpowers (star d d.t) : Subgroup (MulAut ↥d.s56V)) :
          Set (MulAut ↥d.s56V)) := by
        rw [mem_centralizer_iff]
        intro g hg
        obtain ⟨n, rfl⟩ := hg
        exact (Commute.zpow_left (show Commute (star d d.t) a from hcent a ha) n).eq
      exact Subgroup.centralizer_le_normalizer _ hac
    have hcardsup : Nat.card (zpowers (star d d.t) ⊔ P : Subgroup (MulAut ↥d.s56V)) = 640 := by
      rw [card_sup_of_inf_eq_bot' hPnorm hbot, card_zpowers_star_t h49 hd hz,
        card_P h49 hd hz h05 h10 hy]
    have hcardC : Nat.card (img d (CMt d)) = 640 := card_img_CMt h49 hd hz h10 hV5
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardsup, hcardC])).symm

theorem step17s_holds : Step17s := by
  intro G _ _ d z₀ h49 hd hz h05 h09 h10
  exact node17s h49 hd hz h05 h09 h10

end S17



end CFSG.LocalAnalysis.EvenBN.Tits.N
