module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {E N W : Subgroup G}

private lemma card_mulAut_le_twentyfour {W : Type*} [Group W] [Finite W] (h : Nat.card W ≤ 4) :
    Nat.card (MulAut W) ≤ 24 := by
  have h1 : Nat.card (MulAut W) ≤ Nat.card (Equiv.Perm W) :=
    Nat.card_le_card_of_injective (fun f : MulAut W => f.toEquiv) MulEquiv.toEquiv_injective
  rw [Nat.card_perm] at h1
  calc Nat.card (MulAut W) ≤ Nat.factorial (Nat.card W) := h1
    _ ≤ Nat.factorial 4 := Nat.factorial_le h
    _ = 24 := by norm_num

theorem y7c_gl3_small_central (hE : IsGL3Ext E N) (hW : E ≤ normalizer (W : Set G))
    (hN : N ≤ centralizer (W : Set G)) (hcard : Nat.card W ≤ 4) :
    E ≤ centralizer (W : Set G) := by
  obtain ⟨_, hsec⟩ := hE
  obtain ⟨hNn, he⟩ := hsec
  haveI := hNn
  obtain ⟨e⟩ := he
  haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI : IsSimpleGroup (↥E ⧸ N.subgroupOf E) := e.isSimpleGroup
  let ρ : ↥E →* MulAut ↥W := W.normalizerMonoidHom.comp (Subgroup.inclusion hW)
  have hρ_apply : ∀ y : ↥E, ρ y = W.normalizerMonoidHom (Subgroup.inclusion hW y) :=
    fun _ => rfl
  have hker : N.subgroupOf E ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, hρ_apply]
    have hnN : ((n : ↥E) : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hmem : Subgroup.inclusion hW n ∈ W.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa [Subgroup.coe_inclusion] using hN hnN
    exact MonoidHom.mem_ker.mp hmem
  let ρ' : (↥E ⧸ N.subgroupOf E) →* MulAut ↥W := QuotientGroup.lift (N.subgroupOf E) ρ hker
  have hρ'_apply : ∀ y : ↥E, ρ' (QuotientGroup.mk' (N.subgroupOf E) y) = ρ y := fun _ => rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ'.ker with hbot | htop
  · exfalso
    have hinj : Function.Injective ρ' := (MonoidHom.ker_eq_bot_iff ρ').mp hbot
    have hcardQ : Nat.card (↥E ⧸ N.subgroupOf E) = 168 := by
      rw [Nat.card_congr e.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]
    have hle : 168 ≤ Nat.card (MulAut ↥W) := by
      rw [← hcardQ]
      exact Nat.card_le_card_of_injective ρ' hinj
    have h24 : Nat.card (MulAut ↥W) ≤ 24 := card_mulAut_le_twentyfour (W := ↥W) hcard
    omega
  · intro x hx
    have hxker : QuotientGroup.mk' (N.subgroupOf E) (⟨x, hx⟩ : ↥E) ∈ ρ'.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    have hρx : ρ (⟨x, hx⟩ : ↥E) = 1 := by
      have := MonoidHom.mem_ker.mp hxker
      rw [hρ'_apply] at this
      exact this
    have harg : Subgroup.inclusion hW (⟨x, hx⟩ : ↥E) ∈ W.normalizerMonoidHom.ker := by
      rw [MonoidHom.mem_ker]
      rw [hρ_apply] at hρx
      exact hρx
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at harg
    simpa [Subgroup.coe_inclusion] using harg

theorem y7c_gl3_card_ge_eight (hE : IsGL3Ext E N) (hW : E ≤ normalizer (W : Set G))
    (hN : N ≤ centralizer (W : Set G)) (hWe : IsElemAbelian 2 W) (hne : W ≠ ⊥)
    (hfix : centIn W E = ⊥) : 8 ≤ Nat.card W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 ↥W := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hWe.2 (g : G) g.2⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hWp
  by_contra hlt
  have hlt' : Nat.card W < 8 := by omega
  have hk3 : k < 3 := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [hk, h8] at hlt'
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt'
  have hcard4 : Nat.card W ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hEW : E ≤ centralizer (W : Set G) := y7c_gl3_small_central hE hW hN hcard4
  have hWle : W ≤ centIn W E := by
    intro w hw
    unfold centIn
    rw [Subgroup.mem_inf]
    refine ⟨hw, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hEW he)) w hw).symm
  have hbot : W ≤ ⊥ := by rw [← hfix]; exact hWle
  exact hne (eq_bot_iff.mpr hbot)

theorem y7c_gl3_irreducible (hE : IsGL3Ext E N) (hW : E ≤ normalizer (W : Set G))
    (hN : N ≤ centralizer (W : Set G)) (hcard : Nat.card W = 8) (hfix : centIn W E = ⊥)
    {W' : Subgroup G} (hW'W : W' ≤ W) (hW'E : E ≤ normalizer (W' : Set G)) :
    W' = ⊥ ∨ W' = W := by
  have hdiv : Nat.card W' ∣ 2 ^ 3 := by
    simpa [hcard] using Subgroup.card_dvd_of_le hW'W
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hNW' : N ≤ centralizer (W' : Set G) :=
    hN.trans (Subgroup.centralizer_le (fun x hx => hW'W hx))
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | hk3eq
  · left
    have hcard4 : Nat.card W' ≤ 4 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    have hEW' : E ≤ centralizer (W' : Set G) := y7c_gl3_small_central hE hW'E hNW' hcard4
    have hW'le : W' ≤ centIn W E := by
      intro w hw
      unfold centIn
      rw [Subgroup.mem_inf]
      refine ⟨hW'W hw, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact ((Subgroup.mem_centralizer_iff.mp (hEW' he)) w hw).symm
    have : W' ≤ ⊥ := by rw [← hfix]; exact hW'le
    exact eq_bot_iff.mpr this
  · right
    exact Subgroup.eq_of_le_of_card_ge hW'W (by rw [hcard, hk, hk3eq]; norm_num)

end CFSG.OddStandard.HigherRank.YamadaG23
