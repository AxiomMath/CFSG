module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmQ3LBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Cent
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Phi
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace Q3L

variable {Y : Type} [Group Y] [Finite Y] {t : Y}

theorem commute_of_model {N : Subgroup Y} [N.Normal] {P : Type} [Group P] {ι : P →* Y}
    (hι : Function.Injective ι) (hιN : ι.range = N) {u : P} (hιu : ι u = t) {H₀ : Subgroup P}
    (hq : CFSG.IsQuasisimple ↥H₀) (hH₀ : H₀ ≤ Subgroup.centralizer {u})
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer {u} → ⁅M, M⁆ = M → M ≤ H₀)
    {X : Subgroup Y} (hX : CFSG.Open.IsSubnormal X (Subgroup.centralizer ({t} : Set Y)))
    (hXs : Group.IsSolvable ↥X) : ∀ a ∈ H₀.map ι, ∀ x ∈ X, a * x = x * a := by
  set H : Subgroup Y := H₀.map ι with hHdef
  set D : Subgroup Y := N ⊓ Subgroup.centralizer ({t} : Set Y) with hD
  have hH₀p : ⁅H₀, H₀⁆ = H₀ := Subgroup.isPerfect_iff.mp hq.1
  have hHN : H ≤ N := hιN ▸ Subgroup.map_le_range ι H₀
  have hHt : H ≤ Subgroup.centralizer ({t} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hιu, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hH₀ hx)]
  have hHD : H ≤ D := le_inf hHN hHt
  have hHp : ⁅H, H⁆ = H := by rw [hHdef, ← Subgroup.map_commutator, hH₀p]
  have hmaxD : ∀ M : Subgroup Y, M ≤ D → ⁅M, M⁆ = M → M ≤ H := by
    intro M hMD hMp
    have hMr : M ≤ ι.range := hιN ▸ (hMD.trans inf_le_left)
    have hM0 : ⁅M.comap ι, M.comap ι⁆ = M.comap ι := Subgroup.map_injective hι (by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hMr, hMp])
    have hM0t : M.comap ι ≤ Subgroup.centralizer {u} := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp ((hMD hx).2)
      rw [← hιu, ← map_mul, ← map_mul] at h1
      exact hι h1
    rw [← Subgroup.map_comap_eq_self hMr]
    exact Subgroup.map_mono (hmax _ hM0t hM0)
  have hHDn : (H.subgroupOf D).Normal := by
    refine ⟨fun m hm c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have hM := hmaxD (H.map (MulAut.conj (c : Y)).toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem c.2 (hHD hx)) (inv_mem c.2))
      (by rw [← Subgroup.map_commutator, hHp])
    have := hM ⟨m, hm, rfl⟩
    simpa using this
  have hDC : CFSG.Open.IsSubnormal D (Subgroup.centralizer ({t} : Set Y)) := by
    have := isSubnormal_inf_normal (Subgroup.centralizer ({t} : Set Y)) N
    rwa [inf_comm] at this
  have hHs : CFSG.Open.IsSubnormal H (Subgroup.centralizer ({t} : Set Y)) :=
    CFSG.Open.IsSubnormal.step hHD hHDn hDC
  have hHq : CFSG.IsQuasisimple ↥H :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective H₀ ι hι) hq
  exact commute_of_solvable_subnormal hHs hHq hX hXs

end Q3L


namespace Q3L

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_u₁ (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    {ι : SL(2 + 3, ZMod 3) →* Y} (hι : Function.Injective ι) (hιN : ι.range = N)
    (hιu : ι Q3L5.u₁ = t) {s : Y} (hsK : s ∈ tightCore R) (hsN : s ∈ N) (hs4 : orderOf s = 4) :
    False := by
  have hq : CFSG.IsQuasisimple ↥Q3L5.H₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective Q3L5.blk₃_injective)
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 (ZMod 3) le_rfl)
  obtain ⟨g, hgc, hne, -, hz'⟩ := exists_twin h
  have hKsolv := isSolvable_core h
  have hcK := commute_of_model hι hιN hιu hq Q3L5.H₁_le Q3L5.perfect_le_H₁ (isSubnormal_core h)
    hKsolv
  have hcK' := commute_of_model hι hιN hιu hq Q3L5.H₁_le Q3L5.perfect_le_H₁
    (isSubnormal_of_hypOmegaGen h.core.hyp ⟨g, rfl⟩ hz') (isSolvable_conjSub g hKsolv)
  have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) := h.core.datum.cent (tightCore_le R hsK)
  have hrange : ∀ x ∈ N, x ∈ Subgroup.centralizer ({t} : Set Y) →
      (∀ a ∈ Q3L5.H₁.map ι, a * x = x * a) → x ∈ (ι.comp Q3L5.φ).range := by
    intro x hxN hxt hxH
    obtain ⟨p, rfl⟩ : x ∈ ι.range := hιN ▸ hxN
    have hpH : ι p ∈ Subgroup.centralizer (Q3L5.H₁.map ι : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hxH a ha
    obtain ⟨hpu, hpH'⟩ := Q3L5.mem_centralizer_of_model hι hιu hxt hpH
    obtain ⟨A, rfl⟩ := Q3L5.mem_range_φ hpu hpH'
    exact ⟨A, rfl⟩
  have hs : s ∈ (ι.comp Q3L5.φ).range := hrange s hsN hsC fun a ha => hcK a ha s hsK
  have hs' : g * s * g⁻¹ ∈ (ι.comp Q3L5.φ).range :=
    hrange _ ((inferInstance : N.Normal).conj_mem s hsN g)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgc hsC) (Subgroup.inv_mem _ hgc))
      fun a ha => hcK' a ha _ (conj_mem_conjSub hsK)
  exact false_of_twin_hom h (θ := ι.comp Q3L5.φ) (hι.comp Q3L5.φ_injective) gl23_q8 hgc hne hsK
    hs4 hs hs'

theorem false_of_u₂ (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    {ι : SL(4 + 1, ZMod 3) →* Y} (hι : Function.Injective ι) (hιN : ι.range = N)
    (hιu : ι Q3L5.u₂ = t) {s : Y} (hsK : s ∈ tightCore R) (hsN : s ∈ N) (hs4 : orderOf s = 4) :
    False := by
  have hq : CFSG.IsQuasisimple ↥Q3L5.H₂ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective Q3L5.blk₄_injective)
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 (ZMod 3) (by norm_num))
  have hcK := commute_of_model hι hιN hιu hq Q3L5.H₂_le Q3L5.perfect_le_H₂ (isSubnormal_core h)
    (isSolvable_core h)
  have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) := h.core.datum.cent (tightCore_le R hsK)
  obtain ⟨p, rfl⟩ : s ∈ ι.range := hιN ▸ hsN
  have hpH : ι p ∈ Subgroup.centralizer (Q3L5.H₂.map ι : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcK a ha _ hsK
  obtain ⟨hpu, hpH'⟩ := Q3L5.mem_centralizer_of_model hι hιu hsC hpH
  have h2 : ι p ^ 2 = 1 := by rw [sq, ← map_mul, Q3L5.mul_self_of_mem_H₂ hpu hpH', map_one]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hs4] at this
  norm_num at this

end Q3L

theorem leaf_l53 {n : ℕ} : TwinLeafS n fun F _ => LieModel F .PSL 5 3 1 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hm => by
    haveI := h.core.simple
    haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
    have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
      Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
    obtain ⟨htN, s, hsK, hsN, hs4⟩ := exists_u1_of_outTwoCyclic h hC
      (outTwoCyclic_PSL5 Nat.prime_three le_rfl (by norm_num) hm)
    obtain ⟨e₀⟩ := Q3L5.exists_mulEquiv_sl5 hm
    set N : Subgroup Y := genFittingFStar Y with hNdef
    have ht2 : t * t = 1 := by rw [← sq, ← h.core.datum.order, pow_orderOf_eq_one]
    have hz : e₀ ⟨t, htN⟩ * e₀ ⟨t, htN⟩ = 1 := by
      rw [← map_mul, ← map_one e₀]
      exact congrArg e₀ (Subtype.ext ht2)
    have hz1 : e₀ ⟨t, htN⟩ ≠ 1 := fun h1 => by
      have h2 : (⟨t, htN⟩ : N) = 1 := e₀.injective (h1.trans (map_one e₀).symm)
      have := h.core.datum.order
      rw [show t = 1 from congrArg Subtype.val h2, orderOf_one] at this
      exact absurd this (by norm_num)
    obtain ⟨c, hc⟩ := Q3L5.exists_conj_u hz hz1
    set e : N ≃* SL(5, ZMod 3) := e₀.trans (MulAut.conj c⁻¹) with he
    set ι : SL(5, ZMod 3) →* Y := N.subtype.comp e.symm.toMonoidHom with hιdef
    have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
    have hιN : ι.range = N := by
      rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hιt : ι (c⁻¹ * e₀ ⟨t, htN⟩ * c) = t := by
      have h1 : e ⟨t, htN⟩ = c⁻¹ * e₀ ⟨t, htN⟩ * c := by
        rw [he, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
      rw [hιdef, MonoidHom.comp_apply, ← h1]
      simp
    rcases hc with hc | hc
    · exact Q3L.false_of_u₁ h (ι := ι) hι hιN ((congrArg ι hc.symm).trans hιt) hsK hsN hs4
    · exact Q3L.false_of_u₂ h (ι := ι) hι hιN ((congrArg ι hc.symm).trans hιt) hsK hsN hs4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
