module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SymThreePerm
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G} {r s : ℕ}

noncomputable abbrev sym3Y (M : Subgroup G) (i₀ : Fin r) (f₀ : Fin s) (θ : ↥M →* Perm (OmegaE r s)) :
    Subgroup G := ((YStar i₀ f₀).comap θ).map M.subtype

noncomputable abbrev sym3P (M : Subgroup G) (θ : ↥M →* Perm (OmegaE r s)) : Subgroup G :=
  ((Wr r s).comap θ).map M.subtype

theorem sym3_facts (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    (θ : ↥M →* Perm (OmegaE r s)) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r s), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r s) (i₀ : Fin r) (f₀ : Fin s) :
    thompsonJ S ≤ sym3P M θ ∧ sym3P M θ ≤ S ∧ sym3P M θ ≤ sym3Y M i₀ f₀ θ ∧
      ¬ 2 ∣ (sym3P M θ).relIndex (sym3Y M i₀ f₀ θ) ∧
      Nonempty (↥(sym3Y M i₀ f₀ θ) ⧸ CFSG.pCore 2 ↥(sym3Y M i₀ f₀ θ) ≃* Perm (Fin 3)) := by
  classical
  have hJS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hWR : Wr r s ≤ θ.range := by
    rw [← hW]
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  have hAltR : alternatingGroup (OmegaE r s) ≤ θ.range := fun x hx => by
    obtain ⟨m, hm⟩ := hAlt x hx
    exact ⟨m, hm⟩
  have hYR : YStar i₀ f₀ ≤ θ.range := YStar_le i₀ f₀ hWR hAltR
  let Ymat : Subgroup ↥M := (YStar i₀ f₀).comap θ
  let Pmat : Subgroup ↥M := (Wr r s).comap θ
  have hPS : ∀ p : ↥M, p ∈ Pmat → (p : G) ∈ S := by
    intro p hp
    have hp' : θ p ∈ ((thompsonJ S).subgroupOf M).map θ := by rw [hW]; exact hp
    obtain ⟨j, hj, hjp⟩ := hp'
    have h1 : θ (j⁻¹ * p) = 1 := by rw [map_mul, map_inv, hjp, inv_mul_cancel]
    have h2 := hker _ h1
    have hjS : (j : G) ∈ S := hJS (Subgroup.mem_subgroupOf.1 hj)
    have : (p : G) = (j : G) * ((j⁻¹ * p : ↥M) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]
    exact S.mul_mem hjS h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxM : x ∈ M := hSM (hJS hx)
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show θ ⟨x, hxM⟩ ∈ Wr r s
    rw [← hW]
    exact ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hPS p hp
  · exact Subgroup.map_mono fun p hp => Wr_le_YStar i₀ f₀ hp
  · rw [Subgroup.relIndex_map_map_of_injective _ _ M.subtype_injective, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self hYR, YStar_relIndex_Wr]
    omega
  ·
    let e : ↥Ymat ≃* ↥(Ymat.map M.subtype) := Subgroup.equivMapOfInjective Ymat M.subtype
      M.subtype_injective
    let θY : ↥Ymat →* ↥(YStar i₀ f₀) :=
      (θ.comp Ymat.subtype).codRestrict (YStar i₀ f₀) fun y => y.2
    haveI : Fintype (X3 i₀ f₀) := Fintype.ofFinite _
    let e3 : X3 i₀ f₀ ≃ Fin 3 := Fintype.equivFinOfCardEq (by
      rw [← Nat.card_eq_fintype_card]; exact card_X3 i₀ f₀)
    let ρ : ↥(Ymat.map M.subtype) →* Perm (Fin 3) :=
      e3.permCongrHom.toMonoidHom.comp ((rhoStar i₀ f₀).comp (θY.comp e.symm.toMonoidHom))
    have hθY : Function.Surjective θY := by
      rintro ⟨y, hy⟩
      obtain ⟨m, hm⟩ := hYR hy
      exact ⟨⟨m, show θ m ∈ YStar i₀ f₀ by rw [hm]; exact hy⟩, Subtype.ext hm⟩
    have hρs : Function.Surjective ρ := by
      refine e3.permCongrHom.surjective.comp ?_
      exact (rhoStar_surjective i₀ f₀).comp (hθY.comp e.symm.surjective)
    have hρk : IsPGroup 2 ρ.ker := by
      have hle : ρ.ker ≤ S.subgroupOf (Ymat.map M.subtype) := by
        intro y hy
        rw [Subgroup.mem_subgroupOf]
        rw [MonoidHom.mem_ker] at hy
        have h1 : rhoStar i₀ f₀ (θY (e.symm y)) = 1 := by
          have hy' : e3.permCongrHom (rhoStar i₀ f₀ (θY (e.symm y))) = 1 := hy
          exact e3.permCongrHom.injective (hy'.trans (map_one _).symm)
        obtain ⟨y', hy'⟩ : ∃ y' : ↥Ymat, e y' = y := ⟨e.symm y, e.apply_symm_apply y⟩
        rw [← hy'] at h1 ⊢
        simp only [MulEquiv.symm_apply_apply] at h1
        have hf : (θ y'.1) (Sum.inr f₀) = Sum.inr f₀ := by
          have hx0 := congrArg (fun π : Perm (X3 i₀ f₀) =>
            ((π ⟨Sum.inr f₀, Or.inr (Or.inr rfl)⟩ : X3 i₀ f₀) : OmegaE r s)) h1
          simp only [rhoStar_apply, Perm.coe_one] at hx0
          exact hx0
        have hWm : θ y'.1 ∈ Wr r s :=
          mem_Wr_of_mem_YStar i₀ f₀ (show θ y'.1 ∈ YStar i₀ f₀ from y'.2) hf
        exact hPS y'.1 hWm
      exact (hS2.comap_subtype (K := Ymat.map M.subtype)).to_le hle
    exact ⟨quotientPCorePerm (Or.inl rfl) ρ hρs hρk⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
