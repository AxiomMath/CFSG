module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6DNorm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bMain
public import CFSG.ClassicalInvolution.AschTight.Hall196Syl

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6DN

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

theorem isPGroup_center_of_oddCore_eq_bot {X : Type*} [Group X] [Finite X]
    (hO : classicalInvolutionOddCore X = ⊥) : IsPGroup 2 ↥(Subgroup.center X) := by
  intro z
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z : X)).ne'
  set w : X := (z : X) ^ (2 ^ k) with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hkm ▸ dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hwc : ∀ g : X, g * w = w * g := fun g =>
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ z.2 _) g
  haveI hN : (Subgroup.zpowers w).Normal := ⟨fun a ha g => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : g * w ^ i * g⁻¹ = w ^ i := by
      rw [((Commute.zpow_right (hwc g) i)).eq, mul_inv_cancel_right]
    rw [h1]
    exact Subgroup.zpow_mem_zpowers w i⟩
  have hodd : Odd (Nat.card ↥(Subgroup.zpowers w)) := by
    rw [Nat.card_zpowers, hwo]; exact hm
  have hle := Hall196.le_classicalInvolutionOddCore hodd
  rw [hO] at hle
  have hw1 : w = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers w))
  have hm1 : m = 1 := by rw [← hwo, hw1, orderOf_one]
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact hw1

variable {n : ℕ}


variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {c : Y}

theorem mem_pSpan_PY (L : A6c.LayerCtx Ω c) {g : Y} (hg : g ∈ rLayer Ω c) :
    g ∈ pSpan (A6c.PY Ω c) := by
  rw [A6c.pSpan_PY L.h2]; exact hg

theorem le_pCoreOf_of_perm (L : A6c.LayerCtx Ω c) {g : Y} (hg : g ∈ rLayer Ω c)
    (hperm : permQ 6 (L.I.φ ⟨g, mem_pSpan_PY L hg⟩) = 1) : g ∈ pCoreOf 2 (rLayer Ω c) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hspan := A6c.pSpan_PY (Ω := Ω) (c := c) L.h2
  set Sp := pSpan (A6c.PY Ω c) with hSp
  set N : Subgroup Y := (((permQ 6).comp L.I.φ).ker).map Sp.subtype with hN
  have hOY : classicalInvolutionOddCore ↥(rLayer Ω c) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp L.hO
  have hOS : classicalInvolutionOddCore ↥Sp = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv (MulEquiv.subgroupCongr hspan).symm hOY
  have hZ := isPGroup_center_of_oddCore_eq_bot hOS
  have hNle : N ≤ rLayer Ω c := by
    rw [← hspan]; exact Subgroup.map_subtype_le _
  have hNnorm : rLayer Ω c ≤ Subgroup.normalizer (N : Set Y) := by
    intro a ha
    have haS : a ∈ Sp := mem_pSpan_PY L ha
    have key : ∀ b ∈ Sp, ∀ y ∈ N, b * y * b⁻¹ ∈ N := by
      intro b hb y hy
      obtain ⟨n, hn, rfl⟩ := hy
      refine ⟨⟨b, hb⟩ * n * ⟨b, hb⟩⁻¹, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hn ⊢
      simp only [MonoidHom.comp_apply, map_mul, map_inv] at hn ⊢
      rw [hn, mul_one, mul_inv_cancel]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact key a haS y
    · intro hy
      have h := key a⁻¹ (Sp.inv_mem haS) _ hy
      have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
      rwa [e] at h
  have hN2 : IsPGroup 2 ↥N := by
    rintro ⟨_, n, hn, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hn
    have hsq : L.I.φ n * L.I.φ n = 1 := mul_self_of_mem_ker_permQ hn
    have hnn : n * n ∈ L.I.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hsq]
    obtain ⟨k, hk⟩ := hZ ⟨n * n, L.I.ker_le hnn⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (n * n) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    have : (n : ↥Sp) ^ 2 ^ (k + 1) = 1 := by
      calc n ^ 2 ^ (k + 1) = (n ^ 2) ^ 2 ^ k := by rw [pow_succ, mul_comm, pow_mul]
        _ = (n * n) ^ 2 ^ k := by rw [sq]
        _ = 1 := hk'
    exact congrArg Subtype.val this
  have hle := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNle hNnorm hN2
  exact hle ⟨⟨g, mem_pSpan_PY L hg⟩, by
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]; exact hperm, rfl⟩

theorem v3AE6CentE_proved : V3AE6CentE n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr x hx hxE g hg
  obtain ⟨L⟩ := A6c.exists_layerCtx H
  have hn5 : 5 ≤ 6 := by norm_num
  set c := u₁ * u₂ with hc
  set v := L.ρ x with hv
  have hvx : A6c.IsConj L.I x v := L.hρ.conj x hx
  have hxY : ∀ z ∈ rLayer (CoreAssembly.conjClass (tightCore R)) c,
      x * z * x⁻¹ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) c := by
    intro z hz
    have h := TwinMu.Pf3.conjSub_rLayer L.hΩ hx
    rw [← h]
    exact conj_mem_conjSub hz
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (piSub 6) v
  have hwv : mkQ 6 w = v := hw
  have hperm : w.perm = 1 := by
    refine perm_eq_one_of_fix_four hn5 fun α hα => ?_
    obtain ⟨J, hJ, hlab⟩ := L.I.label_surj α hα true
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution L.hΩ hJ.1
    have hzY : z ∈ rLayer (CoreAssembly.conjClass (tightCore R)) c := by
      rw [← A6c.pSpan_PY L.h2]; exact le_pSpan hJ hz.mem
    set zs : ↥(pSpan (A6c.PY (CoreAssembly.conjClass (tightCore R)) c)) :=
      ⟨z, le_pSpan hJ hz.mem⟩ with hzs
    have hzmem : L.I.φ zs ∈ memBar α hα true := by
      rw [← hlab]
      exact ⟨zs, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    have hzsq : L.I.φ zs * L.I.φ zs = 1 := by
      rw [← map_mul]
      have : zs * zs = 1 := Subtype.ext hz.sq
      rw [this, map_one]
    have hz1 : L.I.φ zs ≠ 1 := by
      intro h1
      have h0 : (1 : ↥(pSpan (A6c.PY (CoreAssembly.conjClass (tightCore R)) c))) =
          ⟨1, le_pSpan hJ (one_mem J)⟩ := rfl
      have := phi_injOn L.I.φ hn5 hJ (L.h8 J hJ.1) hlab hz.mem (one_mem J)
        (by rw [h1, ← h0, map_one])
      exact hz.ne_one this
    have hzbar : L.I.φ zs = zBar α hα :=
      (eq_of_mem_memBar_mul_self hn5 hzmem hzsq).resolve_left hz1
    have hzE : z ∈ ae6E (CoreAssembly.conjClass (tightCore R)) c := by
      unfold ae6E
      refine le_pCoreOf_of_perm L hzY ?_
      have e : (⟨z, mem_pSpan_PY L hzY⟩ :
          ↥(pSpan (A6c.PY (CoreAssembly.conjClass (tightCore R)) c))) = zs := rfl
      rw [e, hzbar]
      show permQ 6 (mkQ 6 (zOf (emb α hα))) = 1
      rw [permQ_mkQ, zOf_perm]
    have hxz : x * z * x⁻¹ = z := by
      rw [hxE z hzE, mul_inv_cancel_right]
    have hvz : v * zBar α hα * v⁻¹ = zBar α hα := by
      have h1 := hvx z zs.2 (by rw [hxz]; exact zs.2)
      have e : (⟨x * z * x⁻¹, by rw [hxz]; exact zs.2⟩ :
          ↥(pSpan (A6c.PY (CoreAssembly.conjClass (tightCore R)) c))) = zs := Subtype.ext hxz
      rw [e, hzbar] at h1
      exact h1.symm
    obtain ⟨b', hb'⟩ := exists_conj_memBar_map w α hα true
    have hmem2 : v * zBar α hα * v⁻¹ ∈ memBar (α.map w.perm.toEmbedding)
        (by rw [Finset.card_map]; exact hα) b' := by
      rw [← hb', hwv]
      exact conj_mem_conjSub (zBar_mem_memBar α hα true)
    have hsq2 : (v * zBar α hα * v⁻¹) * (v * zBar α hα * v⁻¹) = 1 := by
      rw [hvz]; exact zBar_mul_self α hα
    have hne2 : v * zBar α hα * v⁻¹ ≠ 1 := by
      rw [hvz]; exact zBar_ne_one hn5 α hα
    have hz2 := (eq_of_mem_memBar_mul_self hn5 hmem2 hsq2).resolve_left hne2
    rw [hvz] at hz2
    exact (eq_of_zBar_eq (by norm_num) hz2).symm
  have hpv : permQ 6 v = 1 := by rw [← hwv, permQ_mkQ, hperm]
  have hxg : x * g * x⁻¹ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) c := hxY g hg
  have hcomm : x * g * x⁻¹ * g⁻¹ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) c :=
    Subgroup.mul_mem _ hxg (Subgroup.inv_mem _ hg)
  unfold ae6E
  refine le_pCoreOf_of_perm L hcomm ?_
  have h1 := hvx g (mem_pSpan_PY L hg) (mem_pSpan_PY L hxg)
  have e : (⟨x * g * x⁻¹ * g⁻¹, mem_pSpan_PY L hcomm⟩ :
      ↥(pSpan (A6c.PY (CoreAssembly.conjClass (tightCore R)) c))) =
      ⟨x * g * x⁻¹, mem_pSpan_PY L hxg⟩ * (⟨g, mem_pSpan_PY L hg⟩)⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_inv, h1]
  simp only [map_mul, map_inv, hpv, inv_one, one_mul, mul_one, mul_inv_cancel]

theorem v3AE6DNorm_proved (hC : V3AE6EComm n) : V3AE6DNorm n :=
  v3AE6DNorm_of A6b.v3AE6E_proved hC v3AE6CentE_proved

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6DN
