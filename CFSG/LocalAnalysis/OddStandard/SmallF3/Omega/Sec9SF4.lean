module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SF1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
import CFSG.GH74.GLS.Bg.TwoGroups.L26Abel
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

theorem sec9f_equiv_E16 {B : Subgroup G} (hB : IsElemAb2 B 4) : Nonempty (↥B ≃* E16) := by
  obtain ⟨e⟩ := CFSG.GH74.GLS.Bg.TwoGroups.L26.elemAbelian_equiv
    (fun a b : ↥B => Subtype.ext (CFSG.Open.IsElemAbelian.comm hB.1 a.2 b.2))
    (fun a : ↥B => Subtype.ext (by
      simpa using CFSG.Open.IsElemAbelian.mul_self_eq_one hB.1 a.2))
    4 hB.2
  exact ⟨e.trans (MulEquiv.piMultiplicative (fun _ : Fin 4 => ZMod 2))⟩

theorem sec9f_rho {X B : Subgroup G} (hX : X ≤ normalizer (B : Set G)) :
    ∃ ρ : ↥X →* MulAut ↥B, ρ.ker = (X ⊓ centralizer (B : Set G)).subgroupOf X ∧
      ρ.range = autIn X B := by
  refine ⟨B.normalizerMonoidHom.comp (Subgroup.inclusion hX), ?_, ?_⟩
  · ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : (B.normalizerMonoidHom (Subgroup.inclusion hX x)) ⟨b, hb⟩ = ⟨b, hb⟩ := by
        rw [← MonoidHom.comp_apply, hx]
        rfl
      have hcoe : (x : G) * (b : G) * (x : G)⁻¹ = (b : G) := by
        have h := congrArg (fun y : ↥B => (y : G)) hb'
        simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h
      calc b * (x : G) = ((x : G) * b * (x : G)⁻¹) * (x : G) := by rw [hcoe]
        _ = (x : G) * b := by group
    · rintro ⟨-, hxcent⟩
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion, MulAut.one_apply]
      have hcomm : (b : G) * (x : G) = (x : G) * (b : G) :=
        Subgroup.mem_centralizer_iff.mp hxcent (b : G) b.2
      rw [← hcomm]
      group
  · rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl

theorem sec9f_E1_core (hctx : Sec9Ctx G t L S z g B t₀)
    (τ : ↥(centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) →* ↥B)
    (hker : τ.ker = (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B).subgroupOf
      (centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)))
    (hK0 : oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B ≤
      centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G))
    (htop : τ.range = ⊤) :
    ∃ E1 : Subgroup G, Asub9 t t₀ B ≤ E1 ∧
      E1 ≤ centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) ∧
      E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) =
        centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) ∧
      ∃ φ : ↥E1 →* ↥B, Function.Surjective φ ∧ φ.ker = (Asub9 t t₀ B).subgroupOf E1 := by
  classical
  have hAelem : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) := sec9n_A_elem hctx
  have hBA : B ≤ Asub9 t t₀ B := le_sup_right
  have hAleN : Asub9 t t₀ B ≤ centMod (Asub9 t t₀ B) B :=
    sec9n_le_centMod hBA (fun a ha a' ha' => hAelem.comm ha ha')
  have hAleCentB : Asub9 t t₀ B ≤ centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hAelem.comm (hBA hb) ha
  have hAleC : Asub9 t t₀ B ≤ centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) :=
    le_inf hAleN hAleCentB
  have hidx : ∃ k : ℕ,
      (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B).relIndex
        (centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) = 2 ^ k := by
    refine ⟨4, ?_⟩
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, htop, Subgroup.card_top]
    exact hctx.B_e16.2
  have hAp : IsPGroup 2 (Asub9 t t₀ B) := CFSG.Open.IsElemAbelian.isPGroup hAelem
  obtain ⟨E1, hE1syl, hAE1⟩ := sec68_exists_sylow_ge (B := Asub9 t t₀ B)
    (H := centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) hAp hAleC
  have hE1C : E1 ≤ centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) := hE1syl.1
  have hE1K0 : E1 ⊔ (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B) =
      centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) :=
    sec9f_sylow_sup hE1syl hK0 hidx
  have hEO : E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) =
      centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G) := by
    have h1 : E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) =
        E1 ⊔ (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B) := by
      rw [← sup_assoc, sup_eq_left.mpr (le_trans hAE1 le_sup_left)]
    rw [h1, hE1K0]
  have hOleN : oddCoreIn (centMod (Asub9 t t₀ B) B) ≤ centMod (Asub9 t t₀ B) B :=
    (oddCoreIn_normal _).1
  have hnormO : centMod (Asub9 t t₀ B) B ≤
      normalizer (oddCoreIn (centMod (Asub9 t t₀ B) B) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOleN).mp (oddCoreIn_normal _).2
  have hAO : ∀ a ∈ Asub9 t t₀ B, ∀ o ∈ oddCoreIn (centMod (Asub9 t t₀ B) B),
      a * o * a⁻¹ ∈ oddCoreIn (centMod (Asub9 t t₀ B) B) := by
    intro a ha o ho
    exact (Subgroup.mem_normalizer_iff.mp (hnormO (hAleN ha)) o).mp ho
  have hOodd : Odd (Nat.card (oddCoreIn (centMod (Asub9 t t₀ B) B))) :=
    odd_card_oddCoreIn _
  have hinf : E1 ⊓ (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B) =
      Asub9 t t₀ B :=
    sec9f_inf_eq hE1syl.2.1 hAE1 hOodd hAO
  have hsup : E1.subgroupOf (centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G)) ⊔ τ.ker =
      ⊤ := by
    rw [hker, ← Subgroup.subgroupOf_sup hE1C hK0, hE1K0, Subgroup.subgroupOf_self]
  have hφtop : (τ.comp (Subgroup.inclusion hE1C)).range = ⊤ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact (sec9f_map_eq_range τ
      (E1.subgroupOf (centMod (Asub9 t t₀ B) B ⊓ centralizer (B : Set G))) hsup).trans htop
  have hsurj : Function.Surjective (τ.comp (Subgroup.inclusion hE1C)) :=
    MonoidHom.range_eq_top.mp hφtop
  have hkerφ : (τ.comp (Subgroup.inclusion hE1C)).ker =
      (Asub9 t t₀ B).subgroupOf E1 := by
    have h1 : (τ.comp (Subgroup.inclusion hE1C)).ker =
        (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B).subgroupOf E1 := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
      constructor
      · intro hx
        have hxker : Subgroup.inclusion hE1C x ∈ τ.ker := hx
        rw [hker, Subgroup.mem_subgroupOf] at hxker
        simpa using hxker
      · intro hx
        have hxker : Subgroup.inclusion hE1C x ∈ τ.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          simpa using hx
        exact hxker
    rw [h1, Subgroup.subgroupOf_inj,
      inf_comm (oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B) E1,
      inf_eq_left.mpr hAE1]
    exact hinf
  exact ⟨E1, hAE1, hE1C, hEO, τ.comp (Subgroup.inclusion hE1C), hsurj, hkerφ⟩

end CFSG.OddStandard.SmallF3.Omega
