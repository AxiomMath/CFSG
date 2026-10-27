module

public import CFSG.LargeExtraspecial.S8KI
public import CFSG.LargeExtraspecial.S8KH

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

structure Red4 (D : Std H C ht ht1 hVQ) : Prop where
  hCE : CentralExtInput.{u}
  hNo : NoA2 S g
  hΩ : OmegaCase H C ht ht1 hVQ
  hm4 : D.m = 4
  hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t
  hn : S.width ≠ 12
  hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t

theorem mem_CMt_of_mem_conjCentM {σ : S.O} (hσ : σ ∈ conjCentM S t) : σ ∈ CMt S t :=
  mem_CMt.mpr ⟨hσ.1, hσ.2.1⟩

theorem conj_mul_self (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {x : S.O} :
    x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
    _ = 1 := by rw [htt]; group

theorem mul_self_of_mem_conjCentM (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {σ : S.O}
    (hσ : σ ∈ conjCentM S t) : σ * σ = 1 := by
  obtain ⟨-, -, x, -, rfl⟩ := hσ
  exact conj_mul_self H ht

namespace Red4

variable {D : Std H C ht ht1 hVQ} (R : Red4 D)
include R

theorem nqHyp : NQHyp S g t :=
  have _ := R.hm4
  timmesfeld_6_5_nqHyp H C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb

theorem six_le : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim, R.hm4]; norm_num

theorem hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
  fun _ hk => cl_mem_orbit_of_omegaCase R.hCE H R.hNo C R.hΩ R.six_le hk

theorem fix_Vt {σ : S.O} (hσ : σ ∈ conjCentM S t) :
    ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  step1_fix_Vt R.hCE R.hNo R.hΩ D R.hA7 (Or.inr R.hm4) R.hsub
    (fun h => by
      rcases h with ⟨h3, -⟩ | ⟨-, h12⟩
      · have := R.hm4
        omega
      · exact R.hn h12) σ hσ

theorem inf_eq_bot {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    Vt S g t ⊓ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
  have hσV := R.fix_Vt hσ
  obtain ⟨-, hσt, x, hxM, hxσ⟩ := hσ
  have hnf : ¬ ∀ w ∈ Wt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := fun hflag =>
    hσN (mem_Nbar_of_flag R.hCE R.hNo R.hΩ D (by rw [R.hm4]; norm_num) R.hfus R.hsub hxM hxσ
      hσt hσV hflag)
  exact (finrank_inf_of_four R.hCE R.hNo R.hΩ D R.hm4 hxM hxσ hσt hσV hnf).2

theorem N1bar_spec {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    N1bar S g t σ ≤ Nbar S g t ∧
      (∀ a ∈ N1bar S g t σ, ∀ b ∈ N1bar S g t σ, a * b = b * a ∧ a * a = 1) ∧
      ∀ a ∈ N1bar S g t σ, a * σ = σ * a := by
  have hσV := R.fix_Vt hσ
  obtain ⟨-, hσt, x, hxM, hxσ⟩ := hσ
  exact N1bar_elemAbelian D (by rw [R.hm4]; norm_num) R.hfus R.hsub hxM hxσ hσt hσV hσN

theorem nqSub_N1bar_eq [NQHyp S g t] {σ : S.O} (hσ : σ ∈ conjCentM S t)
    (hσN : σ ∉ Nbar S g t) :
    nqSub S g t (N1bar S g t σ) = nqSub S g t (S9.Fbar S g t) ⊔
      (nqSub S g t (S9.Fbar S g t)).map
        (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) := by
  have hσV := R.fix_Vt hσ
  have hσK := mem_CMt_of_mem_conjCentM hσ
  rw [nqSub_N1bar H hσK (R.N1bar_spec hσ hσN).1]
  obtain ⟨-, hσt, x, hxM, hxσ⟩ := hσ
  exact range_nqComm_eq_of_four R.hCE R.hNo R.hΩ D R.hm4 R.hsub hxM hxσ hσt hσV hσN hσK

theorem N1bar_eq {σ σ' : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t)
    (hσ' : σ' ∈ conjCentM S t) (hσ'N : σ' ∉ Nbar S g t) :
    N1bar S g t σ = N1bar S g t σ' := by
  have := R.nqHyp
  exact eq_of_nqSub_eq (R.N1bar_spec hσ hσN).1 (R.N1bar_spec hσ' hσ'N).1 t_mem_N1bar
    t_mem_N1bar ((R.nqSub_N1bar_eq hσ hσN).trans (R.nqSub_N1bar_eq hσ' hσ'N).symm)

theorem fixSub_N1bar {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    fixSub S (N1bar S g t σ) = Wt S g t ⊓ fixSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  fixSub_N1bar_eq R.hCE R.hNo R.hΩ D hσ.2.1 (mul_self_of_mem_conjCentM H ht hσ) (R.fix_Vt hσ)
    (R.inf_eq_bot hσ hσN)

theorem sup_commSpace_eq {σ σ' : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t)
    (hσ' : σ' ∈ conjCentM S t) (hσ'N : σ' ∉ Nbar S g t) :
    Vt S g t ⊔ commSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      Vt S g t ⊔ commSpace (σ' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  refine sup_commSpace_eq_of_inf_fixSpace_eq ?_
  rw [← R.fixSub_N1bar hσ hσN, ← R.fixSub_N1bar hσ' hσ'N, R.N1bar_eq hσ hσN hσ' hσ'N]

end Red4

end CFSG.LargeExtraspecial.S8
