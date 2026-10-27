module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Ly
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultReduce
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultSqFree
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThree

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup CFSG CFSG.Blueprint

@[expose] def LyMultFive : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J →
    NativeSporadic.IsSporadic (J ⧸ Subgroup.center J) .Ly → IsPGroup 5 (Subgroup.center J) →
      Subsingleton ↥(Subgroup.center J)

theorem lyMultTrivial_of_five
    (h5 : LyMultFive) : LyMultTrivial := by
  intro J _ _ hJ hLy
  by_contra hne
  obtain ⟨eT⟩ := hLy
  let π : J →* (J ⧸ Subgroup.center J) := QuotientGroup.mk' (Subgroup.center J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center J := QuotientGroup.ker_mk' _
  have hne' : π.ker ≠ ⊥ := by
    rw [hker]
    intro h
    apply hne
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : (a : J) ∈ (⊥ : Subgroup J) := h ▸ a.2
    have hb : (b : J) ∈ (⊥ : Subgroup J) := h ▸ b.2
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  obtain ⟨p, hp, J₁, _, _, π₁, hs₁, hperf₁, hz₁, hpg₁, hne₁⟩ :=
    exists_pgroup_central_ext π hπ hJ.1 hker.le hne'
  have hTfin : Finite (J ⧸ Subgroup.center J) := inferInstance
  have hcard : Nat.card (J ⧸ Subgroup.center J) = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have := Fact.mk hp
  by_cases h2 : p = 2
  · subst h2
    exact hne₁ (lyMult_two ⟨eT⟩ π₁ hs₁ hperf₁ hz₁ hpg₁)
  by_cases h3 : p = 3
  · subst h3
    exact hne₁ (lyMult_three ⟨eT⟩ π₁ hs₁ hperf₁ hz₁ hpg₁)
  by_cases h5' : p = 5
  · subst h5'
    have hsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.2.1
    have hnab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a :=
      exists_noncomm_of_simple (by rw [hcard]; norm_num)
    obtain ⟨hTq, hTZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
    have hq₁ : IsQuasisimple J₁ :=
      (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf₁ π₁ hs₁ hz₁).mpr hTq
    have hcen₁ : Subgroup.center J₁ = π₁.ker := by
      rw [← CFSG.LocalCores.comap_center_eq_of_perfect hperf₁ π₁ hs₁ hz₁, hTZ,
        MonoidHom.comap_bot]
    have hsp : NativeSporadic.IsSporadic (J₁ ⧸ Subgroup.center J₁) .Ly :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hcen₁).trans
        (QuotientGroup.quotientKerEquivOfSurjective π₁ hs₁)).trans eT⟩
    have hsub := h5 J₁ hq₁ hsp (hcen₁ ▸ hpg₁)
    apply hne₁
    rw [← hcen₁]
    exact Subgroup.eq_bot_of_subsingleton _
  · exact hne₁ (ker_eq_bot_of_not_sq_dvd π₁ hs₁ hperf₁ hz₁ hpg₁
      (by rw [hcard]; exact not_sq_dvd_lyOrder hp h2 h3 h5'))

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
