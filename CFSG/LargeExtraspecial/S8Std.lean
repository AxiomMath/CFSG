module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S8FusA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

structure Std (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) where
  Q : QuadraticForm (ZMod 2) (Vt S g t)
  hQ : Q.polarBilin.Nondegenerate
  hpol : Q.polarBilin = beta H C ht ht1 hVQ
  hX : RmodN S g t = omegaGroup Q hQ
  hE : LmodN S g t = pointRadical Q (aV ht)
  hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))
  hQa : Q (aV ht) = 0
  m : ℕ
  hm : 2 ≤ m
  hdim : finrank (ZMod 2) (Vt S g t) = 2 * m
  hA : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) *
    2 ^ (finrank (ZMod 2) (Vt S g t) - 1) = 2 ^ S.width
  hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t
  h : S.M
  hh : S.ρ h ∈ Rbar S g t
  hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g
  hPab : S.clSub (S.QG ⊓ S.Qa g) ⊓ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ≤ Vt S g t
  hNc : ∀ x ∈ Nbar S g t, ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t
  hNsq : ∀ x ∈ Nbar S g t, x * x ∈ zpowers t
  hgen : PairGen S g t
  hN0 : Nbar S g t = N0bar S g t
  hR : RadBound S g t

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem Std.nonempty (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) : Nonempty (Std H C ht ht1 hVQ) := by
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have hgen := pairGen_of_omegaCase H hNo C ht ht1 hVQ hΩ
  have hN0 := Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ
  have hgen' : Rbar S g t ≤ S.Lbar ((1 : S.M) * g) ⊔ S.Lbar ((h : G) * g) ⊔ Nbar S g t := by
    have := hgen 1 h (by rw [map_one]; exact one_mem _) hh
      (by rw [OneMemClass.coe_one, one_mul]; exact hb)
    rwa [OneMemClass.coe_one] at this
  have h1R : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
  have hNc := timmesfeld_6_5_comm H C ht ht1 hVQ h1R hh hgen' hN0
  have hNsq := timmesfeld_6_5_sq H C ht ht1 hVQ h1R hh hgen' hN0
  exact ⟨{
    Q := Q
    hQ := hQ
    hpol := hpol
    hX := hX
    hE := hE
    hsing := hsing
    hQa := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
    m := m
    hm := by omega
    hdim := by omega
    hA := card_Abar_of_omegaCase H hNo C ht ht1 hVQ hΩ
    hN := fun x hx w hw => timmesfeld_6_1_one H C ht ht1 hVQ hh hb hCE hNo hΩ hx hw
    h := h
    hh := hh
    hb := hb
    hPab := clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb (radBound_of_omegaCase H C ht ht1 hVQ hΩ)
    hNc := hNc
    hNsq := hNsq
    hgen := hgen
    hN0 := hN0
    hR := radBound_of_omegaCase H C ht ht1 hVQ hΩ }⟩

namespace Std

variable (D : Std H C ht ht1 hVQ)

@[expose] def IsMinus : Prop :=
  ∀ T : Submodule (ZMod 2) (Vt S g t), (∀ x ∈ T, D.Q x = 0) → finrank (ZMod 2) T < D.m

include D in
theorem isPGroup_Nbar : IsPGroup 2 (Nbar S g t) := by
  intro x
  refine ⟨2, ?_⟩
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hx := D.hNsq x x.2
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, show 2 ^ 2 = 2 + 2 from rfl, pow_add,
    pow_two]
  rcases eq_one_or_eq_of_mem_zpowers htt hx with h1 | h1
  · rw [h1, one_mul]
  · rw [h1, htt]

include D in
theorem three_le_finrank : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
  have := D.hdim; have := D.hm; omega

theorem polar_aV_bV : polar D.Q (aV ht) (bV (mem_Lbar_of_pair H ht D.hh)) = 1 := by
  rw [← polarBilin_apply_apply, D.hpol]
  exact beta_aV_bV H C ht ht1 hVQ D.hh D.hb

theorem Q_bV : D.Q (bV (mem_Lbar_of_pair H ht D.hh)) = 0 := by
  have heR : resV H.conj_mem t ⟨S.ρ D.h, D.hh⟩ ∈ omegaGroup D.Q D.hQ := by
    rw [← D.hX, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  rw [← resV_aV H.conj_mem ht D.hh (mem_Lbar_of_pair H ht D.hh),
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_omegaGroup.mp heR).1, D.hQa]

end Std

end CFSG.LargeExtraspecial.S8
