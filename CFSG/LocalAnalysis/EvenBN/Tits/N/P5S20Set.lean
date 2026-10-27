module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Base
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KSet

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem img_Xg (h49 : d.Thm49Statement) (hd : d.Hyp) : img d (Xg d) = zpowers (star d d.x₅) :=
  imgIn_zpowers d.s56V (x5_mem_Hg h49 hd)

theorem Us_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Us d = ⁅img d (pCoreOf 2 (CMt d)), zpowers (star d d.x₅)⁆ := by
  unfold Us
  rw [img_Xg h49 hd]

theorem Ws_eq (h49 : d.Thm49Statement) (hd : d.Hyp) :
    Ws d = ⁅W0s d, zpowers (star d d.x₅)⁆ := by
  unfold Ws
  rw [img_Xg h49 hd]

theorem star_x5_ne_one_of_card (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hUcard : Nat.card (Us d) = 16) : star d d.x₅ ≠ 1 := by
  intro h1
  have hU : Us d = ⊥ := by
    rw [Us_eq h49 hd, h1, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
  rw [hU] at hUcard
  simp at hUcard

theorem isF20_star (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) {y₁ : G}
    (hy : IsV1 d z₀ y₁) (hUcard : Nat.card (Us d) = 16) :
    IsF20 (star d d.x₅) (star d y₁) := by
  refine ⟨star_x5_pow_five h49 hd, star_x5_ne_one_of_card h49 hd hUcard, ?_, ?_⟩
  · rw [star_eq, ← actFun_pow d.s56V (y1_mem_Hg h49 hd hy), hy.pow_four hd hz, actFun_one]
  · rw [star_eq, star_eq, ← actFun_conj d.s56V (y1_mem_Hg h49 hd hy) (x5_mem_Hg h49 hd),
      hy.conj_x5 hd, actFun_pow d.s56V (x5_mem_Hg h49 hd)]

theorem F20_le_normalizer_Us (h49 : d.Thm49Statement) (hd : d.Hyp) {y₁ : G} (hy : IsV1 d z₀ y₁)
    (hF : IsF20 (star d d.x₅) (star d y₁)) :
    F20 (star d d.x₅) (star d y₁) ≤ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set _) := by
  have hUs := Us_eq h49 hd
  rw [F20]
  refine sup_le ?_ ?_
  · rw [hUs]
    exact (le_sup_right : zpowers (star d d.x₅) ≤
      img d (pCoreOf 2 (CMt d)) ⊔ zpowers (star d d.x₅)).trans
      (CFSG.LocalAnalysis.EvenBN.Tits.S56.commutator_normalized _ _)
  · rw [Subgroup.zpowers_le, hUs]
    have h1 : star d y₁ ∈ normalizer ((img d (pCoreOf 2 (CMt d)) : Subgroup _) : Set _) :=
      actFun_mem_normalizer_imgIn d.s56V _ (y1_mem_Hg h49 hd hy)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CMt d) (hy.mem_CMt hd))
    exact normalizer_commutator_of_mem h1 hF.y_mem_normalizer

theorem Ks_dec (hCcent : img d (CMt d) = centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d)
    (hprod : (W0s d : Set (MulAut ↥d.s56V)) *
      (img d (Kg d ⊓ centralizer ({d.t} : Set G)) : Set (MulAut ↥d.s56V)) = ((Ks d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V))) :
    ∀ k ∈ Ks d, ∃ w ∈ W0s d, ∃ c ∈ img d (CMt d), k = w * c := by
  intro k hk
  have hk' : k ∈ ((Ks d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := hk
  rw [← hprod] at hk'
  obtain ⟨w, hw, c, hc, rfl⟩ := hk'
  refine ⟨w, hw, c, ?_, rfl⟩
  obtain ⟨g, hgK, hgN, rfl⟩ := (mem_imgIn_iff d.s56V _).1 hc
  rw [hCcent]
  refine ⟨mem_centralizer_singleton_iff.2 ?_, actFun_mem_imgIn hgN hgN⟩
  exact actFun_comm_of_comm d.s56V (mem_centralizer_singleton_iff.1 hgK.2)

theorem trans_of_delta (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hΔ : ∀ x ∈ DeltaS d, ∃ w ∈ W0s d, w * star d d.t * w⁻¹ = x) :
    ∀ q ∈ Hs d, q * star d d.t * q⁻¹ ∈ (Us d ⊔ zpowers (star d d.t) : Subgroup (MulAut ↥d.s56V)) →
      ∃ w ∈ W0s d, w * star d d.t * w⁻¹ = q * star d d.t * q⁻¹ := by
  intro q hq hmem
  obtain ⟨g, -, hgN, rfl⟩ := (mem_imgIn_iff d.s56V (Hg d)).1 hq
  refine hΔ _ ⟨hmem, g, hgN, ?_⟩
  show actFun d.s56V (g * d.t * g⁻¹) = actFun d.s56V g * star d d.t * (actFun d.s56V g)⁻¹
  exact actFun_conj d.s56V hgN (t_mem_Hg h49 hd)

theorem star_t_not_mem_Ws (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hWg : img d (Wg d z₀) = Ws d) : star d d.t ∉ Ws d := by
  intro ht
  rw [← hWg] at ht
  obtain ⟨g, hgW, hgN, hgeq⟩ := (mem_imgIn_iff d.s56V (Wg d z₀)).1 ht
  have hgc : g ∈ centralizer ({z₀} : Set G) := hgW.2
  have hfix : actFun d.s56V g ⟨z₀, hz.mem_V⟩ = ⟨z₀, hz.mem_V⟩ :=
    (actFun_fixes_iff d.s56V hgN ⟨z₀, hz.mem_V⟩).2 (mem_centralizer_singleton_iff.1 hgc)
  apply star_t_not_mem_stab h49 hd hz
  have hgeq' : actFun d.s56V d.t = actFun d.s56V g := hgeq.symm
  show actFun d.s56V d.t ⟨z₀, hz.mem_V⟩ = ⟨z₀, hz.mem_V⟩
  rw [hgeq']
  exact hfix

theorem kset_of_nodes (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h17s : Node17s d z₀) (h17 : Node17 d z₀) (h18 : Node18 d) (h19 : Node19 d z₀)
    {y₁ : G} (hy : IsV1 d z₀ y₁) :
    KSet (Hs d) (img d (CMt d)) (Us d) (Ks d) (W0s d) (Ws d) (star d d.x₅) (star d y₁)
      (star d d.t) := by
  obtain ⟨hUab, hUcard, hdec⟩ := h17s
  obtain ⟨hC1, hC2, hC3⟩ := hdec y₁ hy
  rw [img_Xg h49 hd] at hC1 hC2 hC3
  obtain ⟨-, -, -, hCcent, -, -⟩ := h17
  obtain ⟨hA1, -, -, -⟩ := h18
  obtain ⟨-, ⟨-, hquot, hcent, hΔ, hprod⟩, -, -, hWg, hWquot, hWab, hWcard⟩ := h19
  have hF := isF20_star h49 hd hz hy hUcard
  exact
    { frob := hF
      t_sq := star_t_mul_self h49 hd
      t_x := actFun_comm_of_comm d.s56V hd.s56_x5_comm_t.symm
      t_y := actFun_comm_of_comm d.s56V (mem_centralizer_singleton_iff.1 hy.mem_C).symm
      U_ab := hUab
      U_card := hUcard
      C_def := hC1
      C_inf := hC2
      C_comm := hC3
      C_cent := hCcent
      FU := F20_le_normalizer_Us h49 hd hy hF
      K_def := rfl
      W0_p := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Ks d)
      W0_K := CFSG.LieType.BorelTits.pCoreOf_le 2 (Ks d)
      K_W0 := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Ks d)
      W_def := Ws_eq h49 hd
      W0_quot := hquot
      W0_cent_t := hcent
      trans := trans_of_delta h49 hd hΔ
      K_dec := Ks_dec hCcent hprod
      W_card := hWcard
      W_ab := hWab
      U_le_W := hWquot.1
      t_not_mem_W := star_t_not_mem_Ws h49 hd hz hWg
      A1 := hA1 }

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
