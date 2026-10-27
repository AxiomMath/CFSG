module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Facts
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRes
public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1PlaneAlg

public section

namespace CFSG.GroupTheory.AltSevenModule

open CFSG.Quasithin
open CFSG.LocalAnalysis.RankThreeTheoremC

theorem isIrrSec_of_card_sixteen {U : Type} [CommGroup U] (hcard : Nat.card U = 16)
    {L : Subgroup (MulAut U)} (π : ↥(alternatingGroup (Fin 7)) ≃* ↥L) :
    XMod.IsIrrSec ↥L (⊥ : Subgroup U) ⊤ := by
  classical
  haveI hfinU : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI hntU : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  refine ⟨bot_lt_top, ?_⟩
  let ρ : ↥(alternatingGroup (Fin 7)) →* MulAut U := L.subtype.comp π.toMonoidHom
  have hinj : Function.Injective ρ := fun a b hab => π.injective (Subtype.ext hab)
  let c : ↥(alternatingGroup (Fin 7)) :=
    ⟨CFSG.RankThree.PartTwo.KFacts.KP2.cOne, a7m_cOne_mem⟩
  have hf3 : ρ c ^ 3 = 1 := by
    rw [← map_pow]
    have h : c ^ 3 = 1 := Subtype.ext (by decide)
    rw [h, map_one]
  have hfix : ∀ u, ρ c u = u → u = 1 :=
    fun u hu => a7m_eq_one_of_fix_cOne hcard ρ hinj hu
  haveI hsimpleA7 : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup ↥L := π.symm.isSimpleGroup
  have hcardL : Nat.card ↥L = 2520 := by
    rw [← Nat.card_congr π.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  intro J hJ _ _
  have hJinv : ∀ x ∈ J, ρ c x ∈ J := by
    intro x hx
    have h := hJ (π c) x hx
    simpa [ρ, Subgroup.smul_def, MulAut.smul_def] using h
  have h3 := a7m_card_mod_three (ρ c) hf3 hfix J hJinv
  have hdvd : Nat.card J ∣ 16 := hcard ▸ Subgroup.card_subgroup_dvd_card J
  have hmem : Nat.card J ∈ Nat.divisors 16 := by simpa using hdvd
  have e16 : Nat.divisors 16 = {1, 2, 4, 8, 16} := by decide
  rw [e16] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hclass : Nat.card J = 1 ∨ Nat.card J = 4 ∨ Nat.card J = 16 := by omega
  rcases hclass with h1 | h4 | htop
  · left
    exact Subgroup.eq_bot_of_card_eq J h1
  · exfalso
    have hLstab : L ≤ CFSG.CGT.PushingUpLit.CGT6.stabW J := by
      intro a ha w
      constructor
      · intro hw
        have h := hJ ⟨a, ha⟩ w hw
        simpa [Subgroup.smul_def, MulAut.smul_def] using h
      · intro hw
        have h := hJ (⟨a, ha⟩ : ↥L)⁻¹ ((a : MulAut U) w) (by
          simpa [Subgroup.smul_def, MulAut.smul_def] using hw)
        simpa [Subgroup.smul_def, MulAut.smul_def, MulAut.inv_apply_self] using h
    let φ : ↥L →* MulAut ↥J :=
      (CFSG.CGT.PushingUpLit.CGT6.restrictW J).comp (Subgroup.inclusion hLstab)
    have hker : φ.ker = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
      · exfalso
        have hinjφ : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hb
        have hle : Nat.card ↥L ≤ Nat.card (MulAut ↥J) :=
          Nat.card_le_card_of_injective φ hinjφ
        have hperm : Nat.card (MulAut ↥J) ≤ Nat.card (Equiv.Perm ↥J) :=
          Nat.card_le_card_of_injective (fun e : MulAut ↥J => e.toEquiv)
            MulEquiv.toEquiv_injective
        have h24 : Nat.card (Equiv.Perm ↥J) = 24 := by
          rw [Nat.card_perm, h4]
          norm_num
        omega
      · exact ht
    have hfixJ : ∀ x ∈ J, ρ c x = x := by
      intro x hx
      have h1 : φ (π c) = 1 := by
        have hmem : π c ∈ φ.ker := by
          rw [hker]
          exact Subgroup.mem_top _
        exact MonoidHom.mem_ker.mp hmem
      have h2 := congrArg (fun f : MulAut ↥J => (((f ⟨x, hx⟩ : ↥J) : U))) h1
      simpa [φ, ρ, CFSG.CGT.PushingUpLit.CGT6.coe_restrictW] using h2
    have hJbot : J = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hfix x (hfixJ x hx)
    rw [hJbot, Subgroup.card_bot] at h4
    omega
  · right
    exact Subgroup.eq_top_of_card_eq J (by rw [htop, hcard])

end CFSG.GroupTheory.AltSevenModule
