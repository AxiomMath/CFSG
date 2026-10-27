module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaCentral
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.Dedekind
public import CFSG.CGT.PushingUpLit.BHS7.SevenSix

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem baum_le_baumG : baum T ≤ baumG G T := by
  have := baum_conjSub_le_baumG (G := G) (T := T) (x := 1) G.one_mem
  rwa [A1b.conjSub_one] at this

theorem omega_commute (h : MinCex G T) {E F : Subgroup Γ}
    (hE : E ∈ omegaSet G T) (hF : F ∈ omegaSet G T) (hne : E ≠ F) :
    ∀ x ∈ E, ∀ y ∈ F, x * y = y * x := by
  intro x hx y hy
  have h1 := omega_comm h hF hE hne
  have h2 : ⁅x, y⁆ ∈ (⁅E, F⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hx hy
  rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem omega_commutator_mem (h : MinCex G T) {E : Subgroup Γ}
    (hE : E ∈ omegaSet G T) {b c : Γ} (hb : b ∈ baum T) (hc : c ∈ baumG G T) :
    b * c * b⁻¹ * c⁻¹ ∈ E ⊔ Subgroup.centralizer (blockW E : Set Γ) := by
  have hEb : IsBTBlock G T E := omega_isBTBlock h hE
  have hEG : E ∈ btBlocksG G T := (mem_btBlocksMax_of_mem_bStarG hE.1).1
  obtain ⟨-, hBN⟩ := six_twelve_a h.charTwo h.sylow hEG hE.2
  rcases hEb.type with ⟨n, hn2, hn⟩ | ⟨m, hm, hn⟩
  · have hBG : baumG G T ≤ E ⊔ Subgroup.centralizer (blockW E : Set Γ) := by
      refine iSup₂_le fun y hy => ?_
      have hEy : IsBTBlock G (A1b.conjSub y T) E :=
        six_twelve_b_of_not_le_cStar h.charTwo h.sylow hEG hE.2 hy
          (omega_not_le_cStarIn_conj h hE hy)
      exact baum_le_sup_centralizer_of_sl h.charTwo (isSylowTwoOf_conjSub_of_mem
        (h.sylow : IsSylowTwoOf T G) hy) hEy hn2 hn
    have hb' := hBG (baum_le_baumG hb)
    have hc' := hBG hc
    exact mul_mem (mul_mem (mul_mem hb' hc') (inv_mem hb')) (inv_mem hc')
  · exact block_alt_commutator h.charTwo h.sylow hEb hm hn (hBN (baum_le_baumG hb)) (hBN hc)

theorem commutator_mem_omegaJoin_sup_omegaR (h : MinCex G T) {b c : Γ}
    (hb : b ∈ baum T) (hc : c ∈ baumG G T) :
    b * c * b⁻¹ * c⁻¹ ∈ omegaJoin G T ⊔ omegaR G T := by
  classical
  have hfin : (omegaSet G T).Finite := Set.toFinite _
  have hz : ∀ E ∈ hfin.toFinset, b * c * b⁻¹ * c⁻¹ ∈
      E ⊔ Subgroup.centralizer (blockW E : Set Γ) := fun E hE =>
    omega_commutator_mem h (hfin.mem_toFinset.mp hE) hb hc
  have hcomm : ∀ E ∈ hfin.toFinset, ∀ F ∈ hfin.toFinset, E ≠ F →
      ∀ x ∈ E, ∀ y ∈ F, x * y = y * x := fun E hE F hF hne =>
    omega_commute h (hfin.mem_toFinset.mp hE) (hfin.mem_toFinset.mp hF) hne
  have hD := inter_sup_centralizer_le hfin.toFinset hcomm hz
  have hJ : (⨆ E ∈ hfin.toFinset, E : Subgroup Γ) = omegaJoin G T :=
    le_antisymm (iSup₂_le fun E hE => le_omegaJoin (hfin.mem_toFinset.mp hE))
      (iSup₂_le fun E hE => le_iSup₂_of_le (f := fun (E' : Subgroup Γ)
        (_ : E' ∈ hfin.toFinset) => E') E (hfin.mem_toFinset.mpr hE) le_rfl)
  have hW : (⨆ E ∈ hfin.toFinset, blockW E : Subgroup Γ) = omegaW G T :=
    le_antisymm (iSup₂_le fun E hE => blockW_le_omegaW (hfin.mem_toFinset.mp hE))
      (iSup₂_le fun E hE => le_iSup₂_of_le (f := fun (E' : Subgroup Γ)
        (_ : E' ∈ hfin.toFinset) => blockW E') E (hfin.mem_toFinset.mpr hE) le_rfl)
  rw [hJ, hW] at hD
  have hbG : b ∈ G := h.sylow.1 ((inf_le_left : baum T ≤ T) hb)
  have hcG : c ∈ G := baumG_le (h.sylow : IsSylowTwoOf T G) hc
  have hzG : b * c * b⁻¹ * c⁻¹ ∈ G :=
    mul_mem (mul_mem (mul_mem hbG hcG) (G.inv_mem hbG)) (G.inv_mem hcG)
  have hJn : omegaJoin G T ≤ Subgroup.normalizer
      ((Subgroup.centralizer (omegaW G T : Set Γ) : Subgroup Γ) : Set Γ) := fun g hg =>
    B6.le_normalizer_centralizer le_normalizer_omegaW (omegaJoin_le hg)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hJn] at hD
  obtain ⟨g₀, hg₀, r, hr, hzr⟩ := hD
  have hrG : r ∈ G := by
    have : r = g₀⁻¹ * (b * c * b⁻¹ * c⁻¹) := by rw [← hzr]; group
    rw [this]
    exact mul_mem (G.inv_mem (omegaJoin_le hg₀)) hzG
  rw [← hzr]
  exact mul_mem (le_sup_left (a := omegaJoin G T) hg₀)
    (le_sup_right (b := omegaR G T) ⟨hrG, hr⟩)

theorem exists_baumG_mul (h : MinCex G T) {x : Γ} (hx : x ∈ G) :
    ∃ c ∈ baumG G T, ∃ n ∈ G ⊓ Subgroup.normalizer (baum T : Set Γ), x = c * n := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hTx : IsSylowTwoOf (A1b.conjSub x T) G := isSylowTwoOf_conjSub_of_mem hT hx
  have hBG : baumG G T ≤ G := baumG_le hT
  obtain ⟨c, hc, hcb⟩ := exists_conj_baum_of_le_of_le (N := baumG G T) hT hTx hBG
    baum_le_baumG (baum_conjSub_le_baumG hx)
  have hcG : c ∈ G := hBG hc
  rw [baum_conjSub] at hcb
  refine ⟨c, hc, c⁻¹ * x, ⟨G.mul_mem (G.inv_mem hcG) hx, ?_⟩, by group⟩
  apply BHS.mem_normalizer_of_conjSub_eq
  rw [A1b.conjSub_mul, hcb, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]

theorem baumG_le_sup (h : MinCex G T) :
    baumG G T ≤ baum T ⊔ (omegaJoin G T ⊔ omegaR G T) := by
  have hT : IsSylowTwoOf T G := h.sylow
  refine iSup₂_le fun y hy => ?_
  have hTy : IsSylowTwoOf (A1b.conjSub y T) G := isSylowTwoOf_conjSub_of_mem hT hy
  obtain ⟨c, hc, hcb⟩ := exists_conj_baum_of_le_of_le (N := baumG G T) hT hTy (baumG_le hT)
    baum_le_baumG (baum_conjSub_le_baumG hy)
  intro u hu
  rw [hcb, A1b.mem_conjSub_iff] at hu
  have hq := inv_mem (commutator_mem_omegaJoin_sup_omegaR h hu hc)
  have hu' : u = (c⁻¹ * u * c * c * (c⁻¹ * u * c)⁻¹ * c⁻¹)⁻¹ * (c⁻¹ * u * c) := by group
  rw [hu']
  exact mul_mem (le_sup_right (a := baum T) hq) (le_sup_left (b := omegaJoin G T ⊔ omegaR G T) hu)

theorem le_cStarIn_sup_omegaJoin (h : MinCex G T)
    (hR : omegaR G T ≤ cStarIn G T) : G ≤ cStarIn G T ⊔ omegaJoin G T := by
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  intro x hx
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_baumG_mul h hx
  have hcB : c ∈ cStarIn G T ⊔ omegaJoin G T := by
    have h1 : baumG G T ≤ cStarIn G T ⊔ omegaJoin G T := by
      refine (baumG_le_sup h).trans (sup_le ?_ (sup_le le_sup_right ?_))
      · exact ((inf_le_left : baum T ≤ T).trans (le_cStarIn_self h.sylow h.ne)).trans le_sup_left
      · exact hR.trans le_sup_left
    exact h1 hc
  exact mul_mem hcB ((le_sup_left : cStarIn G T ≤ cStarIn G T ⊔ omegaJoin G T)
    (inf_normalizer_baum_le_cStarIn hb0 hn))

end CFSG.CGT.PushingUpLit.BHS7
