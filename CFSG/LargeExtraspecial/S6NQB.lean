module

public import CFSG.LargeExtraspecial.S6NQ
public import CFSG.LargeExtraspecial.S6FiveB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] def PairGen (S : Setting G) (g : G) (t : S.O) : Prop :=
  ∀ k k' : S.M, S.ρ k ∈ Rbar S g t → S.ρ k' ∈ Rbar S g t →
    (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g) →
    Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t

theorem exists_mul_of_pair (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {k k' : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hgen : Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t)
    (hN0 : Nbar S g t = N0bar S g t) {x : S.O} (hx : x ∈ Nbar S g t) :
    ∃ y ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t, ∃ w ∈ S.Lbar ((k' : G) * g) ⊓ Nbar S g t,
      x = y * w := by
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have hDb := Lbar_mul_mem_Dset htk'
  let P : Subgroup S.O :=
    { carrier := {x | ∃ y ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t,
        ∃ w ∈ S.Lbar ((k' : G) * g) ⊓ Nbar S g t, x = y * w}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, w₁, hw₁, rfl⟩ ⟨y₂, hy₂, w₂, hw₂, rfl⟩
        refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, (y₂⁻¹ * w₁ * y₂) * w₂, mul_mem ?_ hw₂, by group⟩
        have := conj_mem_of_mem_Nbar H hDb (inv_mem hy₂.2) hw₁
        rwa [inv_inv] at this
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨y, hy, w, hw, rfl⟩
        refine ⟨y⁻¹, inv_mem hy, y * w⁻¹ * y⁻¹, ?_, by group⟩
        exact conj_mem_of_mem_Nbar H hDb hy.2 (inv_mem hw) }
  have hle : Nbar S g t ≤ P := by
    rw [(timmesfeld_6_5_N H ht hk hk' hgen hN0).1]
    exact sup_le (fun y hy => ⟨y, hy, 1, one_mem _, by simp⟩)
      (fun w hw => ⟨1, one_mem _, w, hw, by simp⟩)
  exact hle hx

theorem nqHyp_of_pair (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t)
    (hk' : S.ρ k' ∈ Rbar S g t)
    (hgen : Rbar S g t ≤ (S.Lbar ((k : G) * g) ⊔ S.Lbar ((k' : G) * g)) ⊔ Nbar S g t)
    (hN0 : Nbar S g t = N0bar S g t) : NQHyp S g t :=
  ⟨H.conj_mem, timmesfeld_6_5_comm H C ht ht1 hVQ hk hk' hgen hN0,
    timmesfeld_6_5_sq H C ht ht1 hVQ hk hk' hgen hN0⟩

theorem nqSub_map_nqHom {t : S.O} [NQHyp S g t] {g₀ g₁ : G} {k : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hg : (k : G) * g₀ = g₁) :
    (nqSub S g t (S.Lbar g₀)).map (nqHom S g t ⟨_, hk⟩ : NQ S g t →ₗ[ZMod 2] _) =
      nqSub S g t (S.Lbar g₁) := by
  subst hg
  ext m
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨nConj ⟨_, hk⟩ n, ?_, rfl⟩
    rw [coe_nConj]
    exact conj_mem_Lbar_mul S k hn
  · rintro ⟨n, hn, rfl⟩
    refine ⟨nqMk (nConj (⟨_, hk⟩⁻¹ : Rbar S g t) n), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [coe_nConj]
      rw [mem_Lbar_mul_iff] at hn
      simpa using hn
    · change nqMk (nConj ⟨_, hk⟩ (nConj (⟨_, hk⟩⁻¹ : Rbar S g t) n)) = nqMk n
      congr 1
      exact Subtype.ext (by simp [coe_nConj, mul_assoc])

section Fix

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) (hgen : PairGen S g t) (hN0 : Nbar S g t = N0bar S g t)
  [NQHyp S g t]
include H C ht ht1 hVQ hgen hN0

theorem mem_Lbar_of_comm_mem (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    {k₀ : S.M} (hk₀ : S.ρ k₀ ∈ Rbar S g t) {x : S.O} (hx : x ∈ Nbar S g t)
    (hfix : ∀ l ∈ S.Lbar ((k₀ : G) * g), l * x * l⁻¹ * x⁻¹ ∈ zpowers t) :
    x ∈ S.Lbar ((k₀ : G) * g) := by
  have htc := mem_Lbar_mul_of_mem_Rbar H ht hk₀
  set kd : S.M := k₀ * h with hkd
  have hkdR : S.ρ kd ∈ Rbar S g t := by rw [hkd, map_mul]; exact mul_mem hk₀ hh
  set h₁ : S.M := k₀ * h * k₀⁻¹ with hh₁
  have hh₁R : S.ρ h₁ ∈ Rbar S ((k₀ : G) * g) t := by
    rw [Rbar_mul, hh₁, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem hk₀ hh) (inv_mem hk₀)
  have hcoe₁ : (h₁ : G) * ((k₀ : G) * g) = (kd : G) * g := by
    simp [hh₁, hkd, mul_assoc]
  have hb₁ : (h₁ : G) * ((k₀ : G) * g) * S.z * ((h₁ : G) * ((k₀ : G) * g))⁻¹ ∉
      S.Qa ((k₀ : G) * g) := by
    rw [hcoe₁, mem_Qa_mul_iff]
    convert hb using 1
    simp [hkd, mul_assoc]
  have h3₁ : 3 ≤ finrank (ZMod 2) (Vt S ((k₀ : G) * g) t) := by rwa [Vt_mul]
  obtain ⟨y, hyL, hyb⟩ := exists_L0_not_mem_Qa (H.mul k₀) (C.mul k₀) htc ht1
    (not_V_le_Qa_mul H hVQ hk₀) h3₁ hh₁R hb₁
  rw [hcoe₁] at hyb
  have hyLb : S.ρ y ∈ S.Lbar ((k₀ : G) * g) := ρ_mem_Lbar S hyL
  have hyR : S.ρ y ∈ Rbar S g t := Lbar_mul_le_Rbar htc hyLb
  have hykdR : S.ρ (y * kd) ∈ Rbar S g t := by rw [map_mul]; exact mul_mem hyR hkdR
  have hyb' : ((y * kd : S.M) : G) * g * S.z * (((y * kd : S.M) : G) * g)⁻¹ ∉
      S.Qa ((kd : G) * g) := by
    convert hyb using 2
    simp [mul_assoc]
  have hgen' := hgen kd (y * kd) hkdR hykdR hyb'
  have hinf := timmesfeld_6_5_inf H ht hkdR hykdR hgen' hN0 C ht1 hVQ
  have hprod : ∀ n : Nbar S g t, ∃ x₁ x₂ : Nbar S g t, (x₁ : S.O) ∈ S.Lbar ((kd : G) * g) ∧
      (x₂ : S.O) ∈ S.Lbar (((y * kd : S.M) : G) * g) ∧ n = x₁ * x₂ := by
    intro n
    obtain ⟨y₁, hy₁, y₂, hy₂, e⟩ := exists_mul_of_pair H ht hkdR hykdR hgen' hN0 n.2
    exact ⟨⟨y₁, hy₁.2⟩, ⟨y₂, hy₂.2⟩, hy₁.1, hy₂.1, Subtype.ext e⟩
  have hcompl := isCompl_nqSub hprod hinf
  obtain ⟨r, hr⟩ : ∃ r : Rbar S g t, (r : S.O) = S.ρ y := ⟨⟨_, hyR⟩, rfl⟩
  have hyy : S.ρ y * S.ρ y = 1 := mul_self_of_mem_Lbar S (H.mul k₀).conj_mem hyLb
  have hrr : r * r = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hr, hyy]; rfl)
  have hσσ : ∀ m, nqHom S g t r (nqHom S g t r m) = m := fun m => by
    show nqLin r (nqLin r m) = m
    rw [nqLin_comp, hrr, nqLin_one]
  have hσB : ∀ m ∈ nqSub S g t (S.Lbar ((kd : G) * g)),
      nqHom S g t r m ∈ nqSub S g t (S.Lbar (((y * kd : S.M) : G) * g)) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨nConj r n, ?_, (nqHom_mk r n).symm⟩
    rw [coe_nConj, hr, show ((y * kd : S.M) : G) * g = (y : G) * ((kd : G) * g) by
      simp [mul_assoc]]
    exact conj_mem_Lbar_mul S y hn
  have hσB' : ∀ m ∈ nqSub S g t (S.Lbar (((y * kd : S.M) : G) * g)),
      nqHom S g t r m ∈ nqSub S g t (S.Lbar ((kd : G) * g)) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨nConj r n, ?_, (nqHom_mk r n).symm⟩
    have hyyQ : ((y * y : S.M) : G) ∈ S.QG := by
      rw [← S.ρ_eq_one_iff, map_mul]; exact hyy
    have e : S.Lbar ((y : G) * (((y * kd : S.M) : G) * g)) = S.Lbar ((kd : G) * g) := by
      rw [show (y : G) * (((y * kd : S.M) : G) * g) = ((y * y : S.M) : G) * ((kd : G) * g) by
        simp [mul_assoc], Lbar_mul_of_mem_QG S hyyQ]
    rw [coe_nConj, hr, ← e]
    exact conj_mem_Lbar_mul S y hn
  have hfixσ : ∀ n : Nbar S g t, (S.ρ y) * n * (S.ρ y)⁻¹ * (n : S.O)⁻¹ ∈ zpowers t →
      nqHom S g t r (nqMk n) = nqMk n := by
    intro n hn
    rw [nqHom_mk, nqMk_nConj_eq_iff, hr]
    exact hn
  let F : Submodule (ZMod 2) (NQ S g t) :=
    { carrier := {m | nqHom S g t r m = m}
      add_mem' := fun {a b} ha hb => by
        change nqHom S g t r (a + b) = a + b
        rw [map_add]
        exact congrArg₂ (· + ·) ha hb
      zero_mem' := map_zero _
      smul_mem' := fun c a ha => by
        change nqHom S g t r (c • a) = c • a
        rw [map_smul]
        exact congrArg (c • ·) ha }
  have hAF : nqSub S g t (S.Lbar ((k₀ : G) * g)) ≤ F := by
    rintro _ ⟨n, hn, rfl⟩
    refine hfixσ n ?_
    rw [Lbar_comm S (H.mul k₀).conj_mem hyLb hn, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hdim : finrank (ZMod 2) ↥(nqSub S g t (S.Lbar ((kd : G) * g))) =
      finrank (ZMod 2) ↥(nqSub S g t (S.Lbar ((k₀ : G) * g))) := by
    have hh₁R' : S.ρ h₁ ∈ Rbar S g t := by
      rw [hh₁, map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem hk₀ hh) (inv_mem hk₀)
    have e := nqSub_map_nqHom (g₀ := (k₀ : G) * g) hh₁R' hcoe₁
    exact (congrArg (fun P : Submodule (ZMod 2) (NQ S g t) => finrank (ZMod 2) P) e).symm.trans
      (LinearEquiv.finrank_map_eq _ _)
  have hFle := finrank_le_of_swap' (nqHom S g t r) hσσ
    (X := ⊥) (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]) bot_le
    hcompl.sup_eq_top hcompl.inf_eq_bot hσB hσB' le_top (F := F) (fun w hw => by
      have hw' : nqHom S g t r w = w := hw
      rw [Submodule.mem_bot, hw', sub_self])
  have hAeq := Submodule.eq_of_le_of_finrank_le hAF (hFle.trans hdim.le)
  have hmem : nqMk (⟨x, hx⟩ : Nbar S g t) ∈ F := hfixσ _ (hfix _ hyLb)
  rw [← hAeq] at hmem
  exact (mem_nqSub htc ⟨x, hx⟩).mp hmem

end Fix

end CFSG.LargeExtraspecial.S6
