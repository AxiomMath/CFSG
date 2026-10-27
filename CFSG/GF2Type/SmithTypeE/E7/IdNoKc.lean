module

public import CFSG.GF2Type.SmithTypeE.E7.KcCount
public import CFSG.GF2Type.SmithTypeE.DMod.StabOrbit
public import CFSG.LargeExtraspecial.S4DsetCard
public import CFSG.LargeExtraspecial.S14Early

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 QuadraticMap
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)
open CFSG.GF2Type.SmithTypeE.DMod
open CFSG.SmithD6

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Cert


theorem map_Lbar_mul_eq_of (ψ : S.Mbar ≃* TD6) {g : G} {A : Subgroup TD6}
    (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom = A) (h : S.M) :
    ((S.Lbar ((h : G) * g)).subgroupOf S.Mbar).map ψ.toMonoidHom =
      A.map (MulAut.conj (ψ (rhoM S h))).toMonoidHom := by
  rw [← hψ, subgroupOf_Lbar_mul h, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv]


theorem exists_line_Lin01 : ∃ k : Fin 365211, lineSet k.val =
    {((0 : Fin 6 → ZMod 2), Pi.single 0 1), (0, Pi.single 1 1),
      (0, Pi.single 0 1 + Pi.single 1 1)} := by
  obtain ⟨p, hp, -⟩ := exists_line_siegel (F_single_ne_zero 0) (F_single_ne_zero 1)
    (F_single_ne (show (1 : Fin 6) ≠ 0 by decide)) (tsPair_F (show (0 : Fin 6) ≠ 1 by decide))
  refine ⟨p, ?_⟩
  rw [hp]
  simp [lineOfPair, Prod.mk_add_mk]

theorem tvP_mem_UFix_Cc_of_line {k : Fin 365211}
    (hl : lineSet k.val = {((0 : Fin 6 → ZMod 2), Pi.single 0 1), (0, Pi.single 1 1),
      (0, Pi.single 0 1 + Pi.single 1 1)}) : (⟨tvP k, tvP_mem k⟩ : TD6) ∈ UFix Cc := by
  rw [tvP_mem_UFix_Cc_iff]
  intro x hx
  exact (Cc_singular_iff_C0 x).2 ((Lin01_le_iff hl).1 Lin01_le_C0 x hx)

theorem exists_Dset_ncard_eq (ψ : S.Mbar ≃* TD6) {g : G}
    (c : TD6) (hψ : ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom =
      (UFix Cc).map (MulAut.conj c).toMonoidHom) :
    ∃ t : S.O, t ∈ S.Lbar g ∧ t ≠ 1 ∧ (S4.Dset S g t).ncard = 2025 := by
  obtain ⟨k₀, hk₀⟩ := exists_line_Lin01
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : TD6, t₀ = ⟨tvP k₀, tvP_mem k₀⟩ := ⟨_, rfl⟩
  have ht₀ : t₀ ∈ UFix Cc := by
    rw [ht₀def]
    exact tvP_mem_UFix_Cc_of_line hk₀
  have ht₀1 : t₀ ≠ 1 := by
    rw [ht₀def]
    exact fun h => tvP_ne_one k₀ (congrArg Subtype.val h)
  obtain ⟨t', ht'def⟩ : ∃ t' : TD6, t' = c * t₀ * c⁻¹ := ⟨_, rfl⟩
  have ht'X : t' ∈ ((S.Lbar g).subgroupOf S.Mbar).map ψ.toMonoidHom := by
    rw [hψ, ht'def]
    exact ⟨t₀, ht₀, rfl⟩
  obtain ⟨x₀, hx₀, hx₀t⟩ := ht'X
  have hψx₀ : ψ x₀ = t' := hx₀t
  have hmemX : ∀ X : Subgroup S.O, (x₀ : S.O) ∈ X ↔
      t' ∈ (X.subgroupOf S.Mbar).map ψ.toMonoidHom := by
    intro X
    rw [← hψx₀]
    exact (Subgroup.mem_subgroupOf (H := X) (K := S.Mbar) (h := x₀)).symm.trans
      (Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective).symm
  refine ⟨(x₀ : S.O), Subgroup.mem_subgroupOf.mp hx₀, ?_, ?_⟩
  · intro h1
    have h2 : x₀ = 1 := Subtype.ext h1
    have h3 : t' = 1 := by rw [← hψx₀, h2, map_one]
    apply ht₀1
    have h4 : c * t₀ * c⁻¹ = 1 := by rw [← ht'def]; exact h3
    calc t₀ = c⁻¹ * (c * t₀ * c⁻¹) * c := by group
      _ = 1 := by rw [h4]; group
  · obtain ⟨Θ, hΘ⟩ : ∃ Θ : Subgroup S.O → Subgroup TD6, Θ = fun X =>
        (((X.subgroupOf S.Mbar).map ψ.toMonoidHom)).map (MulAut.conj c⁻¹).toMonoidHom :=
      ⟨_, rfl⟩
    have hinj : Set.InjOn Θ (S4.Dset S g (x₀ : S.O)) := by
      rintro X₁ ⟨h₁, rfl, -⟩ X₂ ⟨h₂, rfl, -⟩ hΘ'
      rw [hΘ] at hΘ'
      have e1 := Subgroup.map_injective (MulAut.conj c⁻¹).injective hΘ'
      have e2 := Subgroup.map_injective ψ.injective e1
      rw [subgroupOf_inj, inf_eq_left.mpr (S.Lbar_le_Mbar _),
        inf_eq_left.mpr (S.Lbar_le_Mbar _)] at e2
      exact e2
    have himg : Θ '' (S4.Dset S g (x₀ : S.O)) = {Y : Subgroup TD6 | ∃ c' : TD6,
        Y = (UFix Cc).map (MulAut.conj c').toMonoidHom ∧ t₀ ∈ Y} := by
      ext Y
      constructor
      · rintro ⟨X, ⟨h, rfl, htX⟩, rfl⟩
        refine ⟨c⁻¹ * (ψ (rhoM S h) * c), ?_, ?_⟩
        · rw [hΘ]
          show ((((S.Lbar ((h : G) * g)).subgroupOf S.Mbar).map ψ.toMonoidHom)).map
            (MulAut.conj c⁻¹).toMonoidHom = _
          rw [map_Lbar_mul_eq_of ψ hψ h, map_conj_mul_gen (UFix Cc) c⁻¹ (ψ (rhoM S h) * c),
            map_conj_mul_gen (UFix Cc) (ψ (rhoM S h)) c]
        · have h1 := (hmemX _).1 htX
          rw [hΘ]
          refine ⟨t', h1, ?_⟩
          show c⁻¹ * t' * c⁻¹⁻¹ = t₀
          rw [ht'def]
          group
      · rintro ⟨c'', hY, ht₀Y⟩
        obtain ⟨h, hh⟩ := exists_rhoM_eq (ψ.symm (c * c'' * c⁻¹))
        have hm : ψ (rhoM S h) = c * c'' * c⁻¹ := by rw [hh, MulEquiv.apply_symm_apply]
        have hΘX : Θ (S.Lbar ((h : G) * g)) = Y := by
          rw [hΘ]
          show ((((S.Lbar ((h : G) * g)).subgroupOf S.Mbar).map ψ.toMonoidHom)).map
            (MulAut.conj c⁻¹).toMonoidHom = Y
          have e : c⁻¹ * (c * c'' * c⁻¹ * c) = c'' := by group
          rw [map_Lbar_mul_eq_of ψ hψ h, ← map_conj_mul_gen (UFix Cc) (ψ (rhoM S h)) c,
            ← map_conj_mul_gen (UFix Cc) c⁻¹ (ψ (rhoM S h) * c), hm, e, hY]
        have ht₀X : t₀ ∈ Θ (S.Lbar ((h : G) * g)) := by
          rw [hΘX]
          exact ht₀Y
        rw [hΘ] at ht₀X
        obtain ⟨y, hy, hyt⟩ := ht₀X
        have hyt' : y = t' := by
          have h5 : c⁻¹ * y * c⁻¹⁻¹ = t₀ := hyt
          rw [ht'def, ← h5]
          group
        rw [hyt'] at hy
        exact ⟨S.Lbar ((h : G) * g), ⟨h, rfl, (hmemX _).2 hy⟩, hΘX⟩
    rw [← hinj.ncard_image, himg]
    exact ncard_conj_Kc t₀ ⟨k₀, by rw [ht₀def], hk₀⟩

theorem not_conj_Kc [IsSimpleGroup G] (I : Inputs10)
    (hTI : WeaklyClosedTITransitive.{0}) (hw : S.width = 16) (ψ₀ : S.Mbar ≃* TD6) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (c : TD6) :
    ((S.Lbar g).subgroupOf S.Mbar).map ψ₀.toMonoidHom ≠
      (UFix Cc).map (MulAut.conj c).toMonoidHom := by
  intro hψ
  have hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) := ⟨ψ₀.trans omegaTD6.symm⟩
  have hno := noA2_of_insp5 I hw hO haQ hne
  have hirr := irreducible I.hDW hw hO haQ hne
  have H := hyp4_of hTI (by omega) haQ hne hno hirr
  have C := cons311_of hTI (by omega) haQ hne hno hirr
  obtain ⟨t, ht, ht1, hcard⟩ := exists_Dset_ncard_eq ψ₀ c hψ
  exact S4.Dset_ncard_ne_2025 H (noA2_of hno) C ht ht1 hcard

end Cert

end CFSG.GF2Type.SmithTypeE.E7
