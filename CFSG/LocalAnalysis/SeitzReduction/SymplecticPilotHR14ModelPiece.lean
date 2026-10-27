module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelTorus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartBasic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective coe_statedSpMap
  statedSpMap_comp centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longRootSp2)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

section Generic

variable {A B : Type*} [Group A] [Group B]

theorem centralizer_map_mulEquiv_toMonoidHom (φ : A ≃* B) (X : Subgroup A) :
    centralizer ((X.map φ.toMonoidHom : Subgroup B) : Set B) =
      (centralizer (X : Set A)).map φ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h z hz
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ z) ⟨z, hz, rfl⟩
  · rintro h _ ⟨z, hz, rfl⟩
    change φ z * φ x = φ x * φ z
    rw [← map_mul, ← map_mul, h z hz]

theorem fixedSubgroup_eq_map_of_congr (ε : A ≃* B) {θ : MulAut A} {γ β : MulAut B}
    (h : MulAut.congr ε θ = γ * β * γ⁻¹) :
    fixedSubgroup θ = ((fixedSubgroup β).map γ.toMonoidHom).map ε.symm.toMonoidHom := by
  have h1 : θ = MulAut.congr ε.symm (MulAut.congr γ β) := by
    rw [LinearPilot.mulAut_congr_eq_mul γ β, ← h]
    ext x
    simp [MulAut.congr_apply]
  rw [h1, LinearPilot.fixedSubgroup_congr_eq_map, LinearPilot.fixedSubgroup_congr_eq_map]

end Generic

section FieldMap

variable {K F : Type} [Field K] [Field F] {n : ℕ}

theorem statedSpMap_symm_apply (σ : K ≃+* F) (x : StatedSp n F) :
    statedSpMap (σ : K →+* F) n (statedSpMap (σ.symm : F →+* K) n x) = x := by
  rw [statedSpMap_comp]
  apply Subtype.ext
  apply Units.ext
  rw [coe_statedSpMap]
  ext a b
  simp

theorem statedSpMap_surjective (σ : K ≃+* F) :
    Function.Surjective (statedSpMap (σ : K →+* F) n) :=
  fun x => ⟨_, statedSpMap_symm_apply σ x⟩

theorem card_statedSp_eq_of_ringEquiv (σ : K ≃+* F) :
    Nat.card (StatedSp n K) = Nat.card (StatedSp n F) :=
  Nat.card_congr (Equiv.ofBijective _ ⟨statedSpMap_injective _ n, statedSpMap_surjective σ⟩)

theorem statedSpMap_diagSp (σ : K →+* F) (t : Fin n → Kˣ) :
    statedSpMap σ n (diagSp K n t) = diagSp F n (fun i => Units.map (σ : K →* F) (t i)) := by
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_statedSpMap,
    CFSG.SeitzReduction.F4Pilot.coe_map_GL, ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    mat_diagSp, mat_diagSp, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext a
  rcases a with j | j <;> simp

theorem statedSpMap_mem_leviTorusSp' (σ : K →+* F) {J : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ leviTorusSp K J) : statedSpMap σ n x ∈ leviTorusSp F J := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [statedSpMap_diagSp]
  refine diagSp_mem_leviTorusSp fun j hj => ⟨fun h => ?_, fun h => ?_⟩
  · simp only [(ht j hj).1 h]
  · simp only [(ht j hj).2 h, map_one]

theorem statedSpMap_diagSp_mulSingle (σ : K →+* F) (i : Fin n) (κ : Kˣ) :
    statedSpMap σ n (diagSp K n (Pi.mulSingle i κ)) =
      diagSp F n (Pi.mulSingle i (Units.map (σ : K →* F) κ)) := by
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, coe_statedSpMap,
    CFSG.SeitzReduction.F4Pilot.coe_map_GL, ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    mat_diagSp, mat_diagSp, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext a
  rcases a with j | j <;> by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]
  · subst hj
    simp
  · simp [hj]

end FieldMap

section Coordinates

variable {n : ℕ} {K F : Type} [Field K] [Field F] [Finite F] [CharP F 2]

theorem perfectCore_centralizer_conj_torus_le (hF : 4 ≤ Nat.card F) (hn : 1 ≤ n) {last : Fin n}
    (hlast : last.val + 1 = n) (σ : K ≃+* F) {κ₀ : Kˣ} (hκ₀ : κ₀ ≠ 1) (u : StatedSp n K) :
    perfectCore (centralizer ((((leviTorusSp K {last}).map (MulAut.conj u).toMonoidHom).map
        ((spModelPSL n F).comp (statedSpMap (σ : K →+* F) n)) : Subgroup (projectiveSL (2 * n) F)) :
          Set (projectiveSL (2 * n) F))) ≤ (spModelPSL n F).range := by
  set ρ := (spModelPSL n F).comp (statedSpMap (σ : K →+* F) n) with hρ
  set T := leviTorusSp K ({last} : Finset (Fin n)) with hT
  have hY : (T.map (MulAut.conj u).toMonoidHom).map ρ =
      ((T.map (statedSpMap (σ : K →+* F) n)).map (spModelPSL n F)).map
        (MulAut.conj (ρ u)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp [hρ, MulAut.conj_apply]
  rw [hY, centralizer_map_mulEquiv_toMonoidHom (MulAut.conj (ρ u)), ← map_perfectCore]
  have hTF : T.map (statedSpMap (σ : K →+* F) n) ≤ leviTorusSp F ({last} : Finset (Fin n)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact statedSpMap_mem_leviTorusSp' _ hx
  have hκ : Units.map ((σ : K →+* F) : K →* F) κ₀ ≠ 1 := by
    intro h
    apply hκ₀
    apply Units.ext
    have h1 := congrArg (fun v : Fˣ => (v : F)) h
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_one] at h1
    apply σ.injective
    rw [Units.val_one, map_one]
    exact h1
  have hTκ : ∀ i : Fin n, i.val + 1 < n →
      diagSp F n (Pi.mulSingle i (Units.map ((σ : K →+* F) : K →* F) κ₀)) ∈
        T.map (statedSpMap (σ : K →+* F) n) := by
    intro i hi
    refine ⟨diagSp K n (Pi.mulSingle i κ₀), ?_, statedSpMap_diagSp_mulSingle _ i κ₀⟩
    refine diagSp_mem_leviTorusSp fun j hj => ⟨fun h => ?_, fun h => ?_⟩
    · rw [Finset.mem_singleton] at hj
      rw [hj] at h
      omega
    · rw [Finset.mem_singleton] at hj
      rw [hj]
      have hil : i ≠ last := fun e => by rw [e] at hi; omega
      simp [Ne.symm hil]
  rw [perfectCore_centralizer_map_spModelPSL hF hn hlast _ hTF hκ hTκ]
  rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
  refine ⟨statedSpMap (σ : K →+* F) n u * x * (statedSpMap (σ : K →+* F) n u)⁻¹, ?_⟩
  simp [hρ, MulAut.conj_apply]

end Coordinates

end CFSG.SeitzReduction.SymplecticPilot
