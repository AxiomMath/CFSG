module

public import CFSG.LargeExtraspecial.S13Four
public import CFSG.LargeExtraspecial.S10SixE
public import CFSG.LargeExtraspecial.S10FourI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem Vt_le_Wt_of_mem_Nbar {s s' : S.O} (X' : Hyp10 S g s') (hs' : s' ∈ Nbar S g s) :
    Vt S g s ≤ Wt S g s' := by
  rw [← (commSpace_t_eq X'.H X'.C X'.ht X'.ht1 X'.hVQ).2]
  intro v hv
  exact mem_fixSpace.mpr (hs'.2 v hv)

theorem mem_Nbar_symm {s s' : S.O} (X : Hyp10 S g s) (X' : Hyp10 S g s')
    (hs' : s' ∈ Nbar S g s) : s ∈ Nbar S g s' := by
  have h1 := Vt_le_Wt_symm (Vt_le_Wt_of_mem_Nbar X' hs')
  rw [← (commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).2] at h1
  exact ⟨Lbar_le_Rbar X'.ht X.ht, fun v hv => mem_fixSpace.mp (h1 hv)⟩

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem Abar_le_Ebar (hCE : CentralExtInput.{u}) {s : S.O} (X : Hyp10 S g s) :
    S.Lbar g ⊓ Nbar S g s ≤ Ebar S g K := by
  intro x hx
  by_contra hxE
  have h1 := Y.finrank_commSpace_of_not_mem (Subgroup.mem_inf.mp hx).1 hxE
  have h2 := finrank_commSpace_le_six hCE X hx
  have h7 := Y.seven_le
  omega

theorem exists_triple (hCE : CentralExtInput.{u}) :
    ∃ t τ : S.O, ∃ _ : Hyp10 S g t, ∃ _ : Hyp10 S g τ, ∃ _ : Hyp10 S g (τ * t),
      τ ∈ Nbar S g t ∧ τ ≠ t := by
  obtain ⟨t, X, -, -, k, hkN, hτA, hτt⟩ := Y.sec10
  exact ⟨t, _, X, X.conj' hkN rfl, by
    obtain ⟨h', hh'N, hh'⟩ := exists_conj_eq_mul_t hCE X hkN rfl (Subgroup.mem_inf.mp hτA).2 hτt
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hh'N.1)
    have hmN : S.ρ m ∈ normalizer (S.Lbar g : Set S.O) :=
      mem_normalizer_of_fix_a X (MonoidHom.mem_range.mpr ⟨m, rfl⟩) (hh'N.2 _ (cl_a_mem_Vt X.ht))
    exact (X.conj' hkN rfl).conj' hmN hh'.symm, (Subgroup.mem_inf.mp hτA).2, hτt⟩

end Hyp13

end CFSG.LargeExtraspecial.S13
