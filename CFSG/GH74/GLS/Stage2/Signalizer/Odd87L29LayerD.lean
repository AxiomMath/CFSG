module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW

open Subgroup CFSG

theorem layer_eq_of_simple_normal {D : Type} [Group D] [Finite D] (M : Subgroup D) [M.Normal]
    (hq : Group.IsSolvable (D ⧸ M)) (L₀ : Subgroup ↥M) [L₀.Normal] (hsimp : IsSimpleGroup ↥L₀)
    (hnab : ∃ a b : ↥L₀, a * b ≠ b * a)
    (hperf : ∀ J : Subgroup ↥M, Group.IsPerfect ↥J → J ≤ L₀) :
    Nonempty (↥(layer D) ≃* ↥L₀) := by
  let P : Subgroup D := L₀.map M.subtype
  let eP : ↥L₀ ≃* ↥P := L₀.equivMapOfInjective M.subtype M.subtype_injective
  have hQ : IsQuasisimple ↥L₀ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hPcomp : IsComponent P :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eP hQ,
      Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal ‹L₀.Normal›)
        (Subgroup.Normal.isSubnormal ‹M.Normal›)⟩
  have hPsimple : IsSimpleGroup ↥P := eP.symm.isSimpleGroup
  have hcomp : ∀ K : Subgroup D, IsComponent K → K = P := by
    intro K hK
    have hKperf : Group.IsPerfect ↥K := hK.1.1
    have hKM : K ≤ M := by
      by_contra hKM
      have hne : K.map (QuotientGroup.mk' M) ≠ ⊥ := fun hbot => hKM (by
        have h := (Subgroup.map_eq_bot_iff _).mp hbot
        rwa [QuotientGroup.ker_mk'] at h)
      have : Nontrivial ↥(K.map (QuotientGroup.mk' M)) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      have : Group.IsPerfect ↥(K.map (QuotientGroup.mk' M)) := Group.IsPerfect.map _
      exact Group.IsPerfect.not_isSolvable ↥(K.map (QuotientGroup.mk' M)) inferInstance
    have hKMperf : Group.IsPerfect ↥(K.subgroupOf M) :=
      let e := Subgroup.subgroupOfEquivOfLe hKM
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hKL₀ : K.subgroupOf M ≤ L₀ := hperf _ hKMperf
    have hKP : K ≤ P := fun x hx =>
      ⟨⟨x, hKM hx⟩, hKL₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hPsimple
        (hK.2.subgroupOf (K := P)) with hbot | htop
    · exfalso
      have hdis : Disjoint K P := Subgroup.subgroupOf_eq_bot.mp hbot
      have hKbot : K = ⊥ := disjoint_self.mp (hdis.mono_right hKP)
      have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      exact (Subgroup.nontrivial_iff_ne_bot K).mp this hKbot
    · exact le_antisymm hKP (Subgroup.subgroupOf_eq_top.mp htop)
  have hlayer : layer D = P :=
    le_antisymm (sSup_le fun K hK => (hcomp K hK).le) (le_sSup hPcomp)
  exact ⟨(MulEquiv.subgroupCongr hlayer).trans eP.symm⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW
