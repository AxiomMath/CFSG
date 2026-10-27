module

public import CFSG.LargeExtraspecial.S10FiveA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem gen_Gm : ∀ γ : Gm, ∃ i < 3, ∃ j < 2, ∃ i' < 3, ∃ j' < 2,
    γ = τ₁ ^ j * σ₁ ^ i * (τ₂ ^ j' * σ₂ ^ i') := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

section NQ

variable [NQHyp S g t]

theorem nqLin_eq_of_pi_eq {X : Hyp10 S g t} (F : Frame X) {r s : Rbar S g t}
    (h : F.π r = F.π s) (m : NQ S g t) : nqLin r m = nqLin s m := by
  have hn : ((s⁻¹ * r : Rbar S g t) : S.O) ∈ Nbar S g t :=
    (F.ker _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
  have e : r = s * (s⁻¹ * r) := by group
  have h1 : nqLin (s⁻¹ * r) m = m := nqHom_apply_of_mem hn m
  calc nqLin r m = nqLin (s * (s⁻¹ * r)) m := by rw [← e]
    _ = nqLin s (nqLin (s⁻¹ * r) m) := (nqLin_comp _ _ _).symm
    _ = nqLin s m := by rw [h1]

variable (S g t) in
@[expose] noncomputable def nqFix (v : NQ S g t) : Subgroup (Rbar S g t) where
  carrier := {r | nqLin r v = v}
  mul_mem' := fun {r s} hr hs => by
    change nqLin (r * s) v = v
    rw [← nqLin_comp, show nqLin s v = v from hs, show nqLin r v = v from hr]
  one_mem' := nqLin_one v
  inv_mem' := fun {r} hr => by
    change nqLin r⁻¹ v = v
    calc nqLin r⁻¹ v = nqLin r⁻¹ (nqLin r v) := by rw [show nqLin r v = v from hr]
      _ = v := by rw [nqLin_comp, inv_mul_cancel, nqLin_one]

theorem fix_all_of_fix_gen {X : Hyp10 S g t} (F : Frame X) {rd re r₁ r₂ : Rbar S g t}
    (hd : F.π rd = σ₁) (he : F.π re = σ₂) (h₁ : F.π r₁ = τ₁) (h₂ : F.π r₂ = τ₂)
    {v : NQ S g t} (hvd : nqLin rd v = v) (hve : nqLin re v = v) (hv₁ : nqLin r₁ v = v)
    (hv₂ : nqLin r₂ v = v) (r : Rbar S g t) : nqLin r v = v := by
  obtain ⟨i, -, j, -, i', -, j', -, hγ⟩ := gen_Gm (F.π r)
  have hw : F.π r = F.π (r₁ ^ j * rd ^ i * (r₂ ^ j' * re ^ i')) := by
    rw [hγ, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h₁, hd, h₂, he]
  rw [nqLin_eq_of_pi_eq F hw]
  have hmem : r₁ ^ j * rd ^ i * (r₂ ^ j' * re ^ i') ∈ nqFix S g t v :=
    mul_mem (mul_mem (pow_mem hv₁ j) (pow_mem hvd i)) (mul_mem (pow_mem hv₂ j') (pow_mem hve i'))
  exact hmem

end NQ

theorem eq_zero_of_fix_all (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) [NQHyp S g t]
    {v : NQ S g t} (hv : ∀ r : Rbar S g t, nqLin r v = v) : v = 0 := by
  obtain ⟨n, rfl⟩ := nqMk_surjective v
  have hcomm : ∀ r ∈ Rbar S g t, r * n * r⁻¹ * (n : S.O)⁻¹ ∈ zpowers t := fun r hr =>
    (nqMk_nConj_eq_iff ⟨r, hr⟩ n).mp (hv ⟨r, hr⟩)
  obtain ⟨k, hk, hβ, hb⟩ := X.exists_pair
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    rw [X.h4]
    norm_num
  have h1R : S.ρ (1 : S.M) ∈ Rbar S g t := by
    rw [map_one]
    exact one_mem _
  have hnL := mem_Lbar_of_comm_mem X.H X.C X.ht X.ht1 X.hVQ X.pairGen (X.N0 hCE) h3 hk hb h1R
    n.2 (fun l hl => hcomm l (by simpa using Lbar_le_Rbar X.ht (by simpa using hl)))
  have hnLb := mem_Lbar_of_comm_mem X.H X.C X.ht X.ht1 X.hVQ X.pairGen (X.N0 hCE) h3 hk hb hk
    n.2 (fun l hl => hcomm l (Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar X.H X.ht hk) hl))
  rw [nqMk_eq_zero_iff, ← Abar_inf_Bbar hCE X hk hβ]
  exact ⟨⟨by simpa using hnL, n.2⟩, hnLb, n.2⟩

end CFSG.LargeExtraspecial.S10
