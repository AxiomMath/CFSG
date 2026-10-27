module

import CFSG.ClassicalInvolution.Q3.Q3T7P24EngB
public import CFSG.ClassicalInvolution.Asc77.AscS24BQ
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF04x
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF05

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_eq_of_commute (hΩ : HypOmegaMod Ω) {J : Subgroup G} (hJ : J ∈ Ω) {x : G}
    (hx : x ∈ J) (o : orderOf x = 4) {w : G} (hw : w * x = x * w) : conjSub w J = J := by
  have hJw : conjSub w J ∈ Ω := hΩ.conjInvariant w J hJ
  have hxw : x ∈ conjSub w J := by
    rw [mem_conjSub_iff]
    have : w⁻¹ * x * w = x := by
      calc w⁻¹ * x * w = w⁻¹ * (x * w) := by group
        _ = w⁻¹ * (w * x) := by rw [hw]
        _ = x := by group
    rw [this]; exact hx
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers x) := T7A.isPGroup_zpowers_of_orderOf_four o
  have h4 : 4 ≤ Nat.card ↥(Subgroup.zpowers x) := by rw [Nat.card_zpowers, o]
  exact hΩ.eq_of_le_of_le hJw hJ h2 h4 (Subgroup.zpowers_le.mpr hxw) (Subgroup.zpowers_le.mpr hx)

end

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

@[expose] def A : Subgroup G :=
  (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) ⊓ Subgroup.centralizer (R : Set G) ⊓
    Subgroup.normalizer (K' : Set G) ⊓ Subgroup.normalizer (C.D.F.ρ₃.K : Set G)

theorem mem_A {a : G} : a ∈ C.A ↔ a ∈ (S : Subgroup G) ∧ a ∈ Subgroup.centralizer (W : Set G) ∧
    a ∈ Subgroup.centralizer (R : Set G) ∧ a ∈ Subgroup.normalizer (K' : Set G) ∧
    a ∈ Subgroup.normalizer (C.D.F.ρ₃.K : Set G) := by
  simp only [A, Subgroup.mem_inf, and_assoc]

include C in
theorem inf_S_eq_R' : K' ⊓ (S : Subgroup G) = R' := by
  have hR'syl : IsSylow2In R' K' := T7C.isSylow2In_of_mem_RSet_of_le
    C.hyp C.hK'tw.1 C.hd.hR'.1 C.hd.hR'.2.1
  exact hR'syl.2.2 _ inf_le_left S.isPGroup'.to_inf_right (le_inf C.hd.hR'.2.1 C.hd.hR'.2.2)

theorem card_R' : Nat.card ↥R' = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₂) := by
  have h := Q3CL.Thompson.D_card C.D.c.hΩ C.D.c.hW C.D.F.ρ'.hR
  rw [← C.D.h₂] at h
  exact (congrArg (fun X : Subgroup G => Nat.card ↥X) C.hR').symm.trans h

theorem t_not_mem_zpowers : C.D.F.ρ'.r ∉ Subgroup.zpowers C.D.x₂ := fun h =>
  C.D.F.ρ'.hrW ((Subgroup.zpowers_le.mpr C.D.x₂_mem) h)

include C in
theorem W_le_normalizer (L : Subgroup G) (hL : L ∈ Ω) {x : G} (hx : x ∈ L ⊓ W)
    (o : orderOf x = 4) : W ≤ Subgroup.normalizer (L : Set G) := by
  intro w hw
  have hc : w * x = x * w :=
    Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW w hw x hx.2
  exact mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_commute C.hyp hL hx.1 o hc)

theorem s_conj_z : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = z * C.D.F.j := by
  have e1 : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = C.D.F.ρ₃.r * C.D.x₁ ^ 2 * C.D.F.ρ₃.r⁻¹ := by
    rw [C.x₁_sq]
  have e2 : C.D.F.ρ₃.r * C.D.x₁ ^ 2 * C.D.F.ρ₃.r⁻¹ = C.D.x₁ ^ 2 * C.D.x₃ ^ 2 := by
    rw [← conj_pow, C.D.s₁, C.D.comm13.mul_pow]
  have e3 : C.D.x₁ ^ 2 * C.D.x₃ ^ 2 = z * C.D.F.j := by
    rw [C.x₁_sq, C.x₃_sq]
  exact e1.trans (e2.trans e3)

include C in
theorem fix_of_trivMu {t : G} (htN : t ∈ Subgroup.normalizer (W : Set G)) (hT : TrivMu Ω W t)
    (ρ : Thompson.Rep Ω W) : conjSub t ρ.K = ρ.K := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.fix_of_trivMu_of C.D.c htN hT ρ

theorem x₁_mem_MGrp : C.D.x₁ ∈ MGrp Ω W :=
  Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR ((congrArg (fun X => C.D.x₁ ∈ X) C.hR).mpr C.x₁_mem_R)

theorem x₃_mem_MGrp : C.D.x₃ ∈ MGrp Ω W :=
  Thompson.le_MGrp_of_mem_D C.D.F.ρ₃.hR C.x₃_mem_R₃

include C in
theorem W_le_P : W ≤ (S : Subgroup G) ⊓ MGrp Ω W := by
  intro w hw
  refine ⟨C.hd.hWS hw, ?_⟩
  obtain ⟨a, b, rfl⟩ := C.exists_nf hw
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ C.x₁_mem_MGrp a)
    (Subgroup.zpow_mem _ C.x₃_mem_MGrp b)

theorem conj_x₃_zpow_r (n : ℤ) :
    C.D.x₃ ^ n * C.D.F.ρ.r * (C.D.x₃ ^ n)⁻¹ = C.D.x₁ ^ (-n) * C.D.F.ρ.r := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.conj_x₃_zpow_r_of C.D.r₃ C.D.comm13 n

theorem r_mul_x₁_zpow (k : ℤ) : C.D.F.ρ.r * C.D.x₁ ^ k = C.D.x₁ ^ (-k) * C.D.F.ρ.r := by
  have h : C.D.F.ρ.r * C.D.x₁ ^ k * C.D.F.ρ.r⁻¹ = C.D.x₁ ^ (-k) := by
    rw [← conj_zpow, C.D.r₁, inv_zpow, zpow_neg]
  calc C.D.F.ρ.r * C.D.x₁ ^ k = C.D.F.ρ.r * C.D.x₁ ^ k * C.D.F.ρ.r⁻¹ * C.D.F.ρ.r := by group
    _ = C.D.x₁ ^ (-k) * C.D.F.ρ.r := by rw [h]

include C in
theorem inf_S_eq_R : K ⊓ (S : Subgroup G) = R :=
  C.hRsyl.2.2 _ inf_le_left S.isPGroup'.to_inf_right (le_inf C.hd.hR.2.1 C.hd.hR.2.2)

theorem card_R : Nat.card ↥R = 2 * Nat.card ↥(Subgroup.zpowers C.D.x₁) := by
  have h := Q3CL.Thompson.D_card C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
  rw [← C.D.h₁] at h
  exact (congrArg (fun X : Subgroup G => Nat.card ↥X) C.hR).symm.trans h

theorem r_not_mem_zpowers : C.D.F.ρ.r ∉ Subgroup.zpowers C.D.x₁ := fun h =>
  C.D.F.ρ.hrW ((Subgroup.zpowers_le.mpr C.D.x₁_mem) h)

include C in
theorem exists_W_mul_mem_centralizer {t : G} (htS : t ∈ (S : Subgroup G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) (htK : conjSub t K = K) :
    ∃ w ∈ W, w * t ∈ Subgroup.centralizer (R : Set G) := by
  obtain ⟨r, hr⟩ : ∃ r, r = C.D.F.ρ.r := ⟨_, rfl⟩
  have hrR : r ∈ R := hr ▸ C.r_mem_R
  have hrU : r ∉ Subgroup.zpowers C.D.x₁ := hr ▸ C.r_not_mem_zpowers
  have hU : Subgroup.zpowers C.D.x₁ ≤ R := Subgroup.zpowers_le.mpr C.x₁_mem_R
  have htx : t * C.D.x₁ = C.D.x₁ * t :=
    (Subgroup.mem_centralizer_iff.mp htW _ C.D.x₁_mem).symm
  have htR : t * r * t⁻¹ ∈ R := by
    rw [← C.inf_S_eq_R]
    refine ⟨?_, S.mul_mem (S.mul_mem htS (C.hd.hR.2.2 hrR)) (S.inv_mem htS)⟩
    have h := conj_mem_conjSub (n := t) (hr ▸ C.r_mem_K : r ∈ K)
    rwa [htK] at h
  have hux : ∀ k : ℤ, t * C.D.x₁ ^ k * t⁻¹ = C.D.x₁ ^ k := fun k => by
    rw [← conj_zpow, htx, mul_inv_cancel_right]
  rcases mem_or_inv_mul_mem hU C.card_R hrR hrU htR with h | h
  · exfalso
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hrU
    have e : r = t⁻¹ * (t * r * t⁻¹) * t := by group
    rw [e, ← hk]
    have e2 : t⁻¹ * C.D.x₁ ^ k * t = C.D.x₁ ^ k := by
      calc t⁻¹ * C.D.x₁ ^ k * t = t⁻¹ * (t * C.D.x₁ ^ k * t⁻¹) * t := by rw [hux]
        _ = C.D.x₁ ^ k := by group
    rw [e2]
    exact Subgroup.zpow_mem_zpowers _ _
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have htr : t * r * t⁻¹ = r * C.D.x₁ ^ k := by
      rw [hk]; group
    obtain ⟨w, hw⟩ : ∃ w, w = C.D.x₃ ^ (-k) := ⟨_, rfl⟩
    have hwx : ∀ i : ℤ, w * C.D.x₁ ^ i = C.D.x₁ ^ i * w := fun i => by
      rw [hw]; exact (C.D.comm13.symm.zpow_zpow (-k) i).eq
    have hwr : w * r * w⁻¹ = C.D.x₁ ^ k * r := by
      have h2 := C.conj_x₃_zpow_r (-k)
      rw [neg_neg, ← hw, ← hr] at h2
      exact h2
    have hrk : r * C.D.x₁ ^ k = C.D.x₁ ^ (-k) * r := by rw [hr]; exact C.r_mul_x₁_zpow k
    have hc : (w * t) * r * (w * t)⁻¹ = r := by
      calc (w * t) * r * (w * t)⁻¹ = w * (t * r * t⁻¹) * w⁻¹ := by group
        _ = w * r * w⁻¹ * (w * C.D.x₁ ^ k * w⁻¹) := by rw [htr]; group
        _ = C.D.x₁ ^ k * (r * C.D.x₁ ^ k) := by rw [hwr, hwx k]; group
        _ = r := by rw [hrk]; group
    have hwW : w ∈ W := hw ▸ W.zpow_mem C.D.x₃_mem _
    refine ⟨w, hwW, ?_⟩
    have hax : (w * t) * C.D.x₁ = C.D.x₁ * (w * t) := by
      have h1 := hwx 1
      rw [zpow_one] at h1
      rw [mul_assoc, htx, ← mul_assoc, h1, mul_assoc]
    have has : (w * t) * r = r * (w * t) := by
      calc (w * t) * r = (w * t) * r * (w * t)⁻¹ * (w * t) := by group
        _ = r * (w * t) := by rw [hc]
    have hle := commute_of_index_two hU C.card_R hrR hrU hax has
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
