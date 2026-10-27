module

public import CFSG.GF2Type.SmithTypeE.E7.TransMain
public import CFSG.GF2Type.SmithTypeE.E7.ModelEquiv
public import CFSG.GF2Type.SmithTypeE.E7.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.DMod CFSG.SmithD6

variable {G : Type} [Group G] [Finite G]

@[expose] def TwoRankMbar (S : Setting G) : Prop :=
  ∀ E : Subgroup S.O, E ≤ S.Mbar → CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15

section Main

variable {S : Setting G}
  [IsSimpleGroup G]

omit
  [IsSimpleGroup G] in
theorem Phi_eq_rhoMod_of_cl {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {ψ : S.Mbar ≃* TD6}
    (hψ : ∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
      φ (S.cl (c * u * c⁻¹)) = rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u)))
    (m : S.M) : Phi S φ m = rhoMod (ψ (rhoM S m)) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, hcl⟩ := S.exists_cl (φ.symm v)
  have hv : v = φ (S.cl u) := by rw [hcl, LinearEquiv.apply_symm_apply]
  rw [hv, Phi_cl m hu]
  exact hψ (m : G) m.2 u hu

omit
  [IsSimpleGroup G] in
theorem twoRankMbar_of_TD6 (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (h : ∀ E : Subgroup TD6, CFSG.IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ 15) :
    TwoRankMbar S := by
  obtain ⟨e⟩ := hO
  intro E hE hel
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hel
  have h1 : CFSG.IsElementaryAbelian 2 (E.subgroupOf S.Mbar) :=
    CFSG.IsElementaryAbelian.subgroupOf hE
  have h2 : CFSG.IsElementaryAbelian 2 ((E.subgroupOf S.Mbar).map (e.trans omegaTD6).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map (e.trans omegaTD6).toMonoidHom
  have h3 := h _ h2
  rw [Subgroup.card_map_of_injective (e.trans omegaTD6).injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv] at h3
  exact h3

theorem exists_Phi_eq_rhoMod (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} (hφ : SmithE7Clauses1235 S φ) :
    ∃ ψ : S.Mbar ≃* TD6, ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)) := by
  obtain ⟨ψ, hψ⟩ := exists_isModelPhi_of_clauses hO hφ
  exact ⟨ψ, Phi_eq_rhoMod_of_cl hψ⟩

theorem smithE7E33_of_clauses (hrank : TwoRankMbar S) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} (hφ : SmithE7Clauses1235 S φ) (g : G)
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) :
    ∃ v : G, IsConj S.z v ∧ v ∈ S.QG ∧ v ∈ S.Qa g := by
  obtain ⟨ψ, hΦ⟩ := exists_Phi_eq_rhoMod hO hφ
  have hcl2 : ∀ i < 75735, ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ φ (S.cl c) = wtV i := by
    intro i hi
    obtain ⟨c, hc, hcQ, hcw⟩ := hφ.2.1 i hi
    exact ⟨c, hc, hcQ, eq_wtV_of_code32 hcw⟩
  have hiso : ∀ u v, polar (S.q.comp (φ.symm : (Fin 32 → ZMod 2) →ₗ[ZMod 2] S.Qt)) u v =
      fModel u v := by
    intro u v
    have h := isometry hΦ (φ.symm u) (φ.symm v)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [h]
    simp only [QuadraticMap.polar, comp_apply, LinearEquiv.coe_coe, map_add]
  exact smithE7E33_of_model hrank hw ψ (fun m => hΦ m) hcl2 hiso g hxM hxQ

theorem smithE7E33_of (hTI : WeaklyClosedTITransitive.{0}) (I : SMK.Inputs10)
    (hAS : AschbacherSmithWideInput)
    (hrank : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
      S.width = 16 → Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6) → TwoRankMbar S) :
    SmithE7E33 := by
  intro G _ _ _ S hw hO g hxM hxQ
  obtain ⟨φ, hφ⟩ := clauses1235 hTI I hAS S hw hO
  exact smithE7E33_of_clauses (hrank G S hw hO) hw hO hφ g hxM hxQ

end Main

end CFSG.GF2Type.SmithTypeE.E7
