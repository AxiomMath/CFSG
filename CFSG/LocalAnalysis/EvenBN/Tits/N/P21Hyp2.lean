module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Hyp
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Norm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section Generic

variable {Γ : Type*} [Group Γ]

theorem p21_actFun_zpow (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) (k : ℤ) :
    actFun S (g ^ k) = actFun S g ^ k := by
  have h := map_zpow (conjActHom S) ⟨g, hg⟩ k
  rw [actFun_of_mem S hg, actFun_of_mem S (zpow_mem hg k)]
  exact h

theorem p21_imgIn_zpowers_le (S : Subgroup Γ) {g : Γ} (hg : g ∈ normalizer (S : Set Γ)) :
    imgIn S (zpowers g) ≤ zpowers (actFun S g) := by
  intro y hy
  obtain ⟨h, hh, hhN, rfl⟩ := (mem_imgIn_iff S _).1 hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
  exact mem_zpowers_iff.2 ⟨k, (p21_actFun_zpow S hg k).symm⟩

end Generic

section Vocab

variable {G : Type} [Group G] [Finite G]
  {d : Data G} {z₀ : G}

theorem p21_alpha_zpow {g : G} (hg : g ∈ Ig d) (k : ℤ) : alpha d (g ^ k) = alpha d g ^ k := by
  have h := congrArg (fun y : ↥(Ialpha d) => (y : MulAut ↥(Ws d))) (map_zpow (alphaHom d) ⟨g, hg⟩ k)
  simp only [Subgroup.coe_zpow, alphaHom_coe] at h
  exact h

end Vocab

section Heavy

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem p21_isPGroup_Xg (hd : d.Hyp) : IsPGroup 5 (Xg d) :=
  IsPGroup.of_card (n := 1) (by
    rw [pow_one]
    exact (Nat.card_zpowers d.x₅).trans hd.s56_orderOf_x5)

theorem p21_centralizer_Xs (hd : d.Hyp) (h19 : Node19 d z₀) (h19b : Node19b d z₀) :
    Ws d ⊓ centralizer ((img d (Xg d) : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) =
      ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, -, -, he3, -⟩ := h19
  have hP : IsPGroup 2 (W0s d) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Ks d)
  have hX : IsPGroup 5 (img d (Xg d)) := isPGroup_imgIn d.s56V (p21_isPGroup_Xg hd)
  have hXP : img d (Xg d) ≤ normalizer ((W0s d : Subgroup (MulAut ↥d.s56V)) : Set _) :=
    fun x hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Ks d) (h19b hx)
  have hab : IsMulCommutative (⁅W0s d, img d (Xg d)⁆ : Subgroup (MulAut ↥d.s56V)) := he3.1
  exact P5.centralizer_commutator_eq_bot (by norm_num) hP hX hXP hab

theorem p21_fix_x5 (h49 : d.Thm49Statement) (hd : d.Hyp) (h19 : Node19 d z₀)
    (h19b : Node19b d z₀) (h20 : Node20 d z₀) {w : ↥(Ws d)} (hw : alpha d d.x₅ w = w) :
    w = 1 := by
  have hx5 := p21_x5_mem_Ig h49 hd h19b h20
  have hcomm : star d d.x₅ * (w : MulAut ↥d.s56V) = (w : MulAut ↥d.s56V) * star d d.x₅ :=
    (actFun_fixes_iff (Ws d) (star_mem_normalizer_Ws hx5) w).1 hw
  have hmem : (w : MulAut ↥d.s56V) ∈
      Ws d ⊓ centralizer ((img d (Xg d) : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
    refine Subgroup.mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : y ∈ zpowers (star d d.x₅) := p21_imgIn_zpowers_le d.s56V (x5_mem_Hg h49 hd) hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy'
    exact (Commute.zpow_left (show Commute (star d d.x₅) (w : MulAut ↥d.s56V) from hcomm) k).eq
  rw [p21_centralizer_Xs hd h19 h19b] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

theorem p21_alpha_x5_pow_five (hd : d.Hyp) (hx5 : d.x₅ ∈ Ig d) : alpha d d.x₅ ^ 5 = 1 := by
  have h5 : d.x₅ ^ 5 = 1 := by
    rw [← hd.s56_orderOf_x5]
    exact pow_orderOf_eq_one _
  rw [← alpha_pow hx5 5, h5, alpha_one]

theorem p21_alpha_x5_ne_one (h49 : d.Thm49Statement) (hd : d.Hyp) (h19 : Node19 d z₀)
    (h19b : Node19b d z₀) (h20 : Node20 d z₀) : alpha d d.x₅ ≠ 1 := by
  intro h
  have hbot : Ws d = ⊥ := by
    refine eq_bot_iff.2 fun w hw => ?_
    have := p21_fix_x5 h49 hd h19 h19b h20 (w := ⟨w, hw⟩) (by rw [h]; rfl)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hcard : Nat.card ↥(Ws d) = 2 ^ 8 := h19.2.2.2.2.2.2.2
  rw [Subgroup.card_eq_one.2 hbot] at hcard
  norm_num at hcard

theorem p21_Alpha_Xg (h49 : d.Thm49Statement) (hd : d.Hyp) (h19b : Node19b d z₀)
    (h20 : Node20 d z₀) : Alpha d (Xg d) = zpowers (alpha d d.x₅) := by
  have hx5 := p21_x5_mem_Ig h49 hd h19b h20
  have hXle : Xg d ≤ Ig d := zpowers_le.2 hx5
  ext y
  rw [mem_Alpha_iff hXle, mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    exact ⟨k, (p21_alpha_zpow hx5 k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨d.x₅ ^ k, zpow_mem (mem_zpowers _) k, p21_alpha_zpow hx5 k⟩

end Heavy

end CFSG.LocalAnalysis.EvenBN.Tits.N
