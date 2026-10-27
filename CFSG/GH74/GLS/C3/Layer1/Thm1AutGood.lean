module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutL2
public import CFSG.Dihedral.NormalOddSubgroupModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoComponents
public import CFSG.Dihedral.Glauberman.DicksonMaxSubfield
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK Equiv

theorem isOddPrimePower_of_odd (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  have := hp
  obtain ⟨n, hpp, hn⟩ := FiniteField.card F p
  refine ⟨p, n, hpp, ?_, n.pos, ?_⟩
  · by_contra hp2
    rw [Nat.not_odd_iff_even] at hp2
    have : Even (Nat.card F) := by
      rw [Nat.card_eq_fintype_card, hn]
      exact Nat.even_pow.2 ⟨hp2, PNat.ne_zero n⟩
    exact (Nat.not_even_iff_odd.2 hodd) this
  · rw [Nat.card_eq_fintype_card, hn]

theorem perm5_pPrimeCore_eq_bot : pPrimeCore 2 (Perm (Fin 5)) = ⊥ := by
  set N := pPrimeCore 2 (Perm (Fin 5)) with hN
  have hodd : Odd (Nat.card N) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hle : N ≤ alternatingGroup (Fin 5) :=
    GorensteinWalter.odd_card_subgroup_le_normal_index_two _ N
      (inferInstance : (alternatingGroup (Fin 5)).Normal) alternatingGroup.index_eq_two hodd
  have hN' : (N.subgroupOf (alternatingGroup (Fin 5))).Normal :=
    (inferInstance : N.Normal).subgroupOf _
  have hodd' : Odd (Nat.card ↥(N.subgroupOf (alternatingGroup (Fin 5)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hodd
  have hbot := DihedralBlueprint.normal_odd_eq_bot_of_alternating_model
    (G := ↥(alternatingGroup (Fin 5))) (n := 5) le_rfl ⟨MulEquiv.refl _⟩
    (N.subgroupOf (alternatingGroup (Fin 5))) hN' hodd'
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 5))) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
    hx
  rw [hbot, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')

theorem alt5_exists_noncomm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc := alternatingGroup.center_eq_bot (α := Fin 5)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have : Nontrivial (alternatingGroup (Fin 5)) :=
    alternatingGroup.nontrivial_of_three_le_card
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  have hxc : x ∈ Subgroup.center (alternatingGroup (Fin 5)) :=
    Subgroup.mem_center_iff.2 (fun g => h g x)
  rw [hc, Subgroup.mem_bot] at hxc
  exact hx hxc

theorem alt5_isComponent : IsComponent (alternatingGroup (Fin 5) : Subgroup (Perm (Fin 5))) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  refine ⟨(LocalCores.isQuasisimple_of_isSimpleGroup alt5_exists_noncomm).1, ?_⟩
  exact Subgroup.Normal.isSubnormal inferInstance

theorem pgl2_pPrimeCore_eq_bot (F₀ : Type) [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀)) :
    pPrimeCore 2 (GorensteinWalter.PGL2 F₀) = ⊥ := by
  have : Finite (GorensteinWalter.PGL2 F₀) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact DihedralBlueprint.normal_odd_eq_bot_of_pgl2_model F₀ (isOddPrimePower_of_odd F₀ hodd)
    (MulEquiv.refl _) _ inferInstance (Nat.coprime_two_left.1 pPrimeCore_coprime_card)

theorem pgl2_isComponent (F₀ : Type) [Field F₀] [Finite F₀] (hodd : Odd (Nat.card F₀))
    (h3 : 3 < Nat.card F₀) :
    IsComponent (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range :=
  ⟨ComponentClassification.CatalogueBLinearTwo.pglPSLRange_quasisimple F₀ h3,
    (Glauberman.Dickson.MaxSubfield.toPGL_range_normal (isOddPrimePower_of_odd F₀ hodd)
      h3).isSubnormal⟩

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem goodC_of_fieldAut (hF : L2Field F) (h9 : Nat.card F ≠ 9) (e : K ≃* L2 F) {σ : MulAut K}
    (hσ : σ ∈ fieldAutSub e) (hσ2 : orderOf σ = 2) : GoodC K σ := by
  obtain ⟨τ, rfl⟩ := hσ
  have hinj : Function.Injective (fieldAutHom e) := fun a b hab => by
    have := congrArg (fieldProj e) hab
    rwa [fieldProj_fieldAutHom, fieldProj_fieldAutHom] at this
  have hτ2 : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) hinj τ]
    exact hσ2
  obtain ⟨F₀, hF₀, hFin₀, hcard, ⟨eqv⟩⟩ :=
    (ivk_1_4a F hF K e τ).2.2 (by rw [hτ2]; exact even_two)
  rw [hτ2] at hcard
  have hodd₀ : Odd (Nat.card F₀) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have : Even (Nat.card F) := by
      rw [← hcard]
      exact Nat.even_pow.2 ⟨hne, by norm_num⟩
    exact (Nat.not_even_iff_odd.2 hF.1) this
  have h3₀ : 3 < Nat.card F₀ := by
    by_contra hle
    push Not at hle
    have hq3 : 3 < Nat.card F := hF.2
    obtain ⟨m, hm⟩ := hodd₀
    interval_cases hq : Nat.card F₀
    · omega
    · have : Nat.card F = 1 := by rw [← hcard]; norm_num
      omega
    · omega
    · have : Nat.card F = 9 := by rw [← hcard]; norm_num
      exact h9 this
  have : Finite (GorensteinWalter.PGL2 F₀) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact ⟨GorensteinWalter.PGL2 F₀, inferInstance, inferInstance, pgl2_pPrimeCore_eq_bot F₀ hodd₀,
    ⟨_, pgl2_isComponent F₀ hodd₀ h3₀⟩, ⟨eqv⟩⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1
