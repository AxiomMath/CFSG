module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1AxisMap
public import CFSG.ClassicalGroups.Alternating.RT1SpFaithful
public import CFSG.ClassicalGroups.Alternating.RT1SpTwist
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseI

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem setting_of_contract (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hN : 4 ≤ finrank K N) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hS₀ : ∃ v₀ : N, v₀ ≠ 0 ∧ ∃ c₀ : K, c₀ ≠ 0 ∧
      finrank K (movedSpace (ρ (Tsp hBN v₀ c₀))) = 2 ∧
      ∀ w ∈ movedSpace (ρ (Tsp hBN v₀ c₀)), Qf w = 0)
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0) (hV : commutatorSpace ρ.range = ⊤) :
    Setting hBN Qf ρ := by
  obtain ⟨v₀, hv₀, c₀, hc₀, hfin, hsing⟩ := hS₀
  have hS : IsLongRootElement Qf (ρ (Tsp hBN v₀ c₀)) :=
    (isLongRootElement_iff hnd).2 ⟨hρQ _, hfin, hsing⟩
  have hne : ρ (Tsp hBN v₀ c₀) ≠ 1 := by
    intro h
    rw [h, movedSpace_one_eq_bot, finrank_bot] at hfin
    exact absurd hfin (by norm_num)
  have hinj : Function.Injective ρ :=
    injective_of_apply_Tsp_ne_one hq hBN hBNnd (by omega) ρ hne
  refine ⟨hq, hBNnd, hN, hnd, hρQ, ?_, hC, hV, hinj⟩
  intro v hv c hc
  obtain ⟨g, hg⟩ := exists_gsp_conj_Tsp_eq hBN hBNnd hv₀ hv hc₀ hc
  have e : ρ (Tsp hBN v c) = ρ g * ρ (Tsp hBN v₀ c₀) * (ρ g)⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv]
  rw [e]
  exact IsLongRootElement.conj
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)) hS

section Aux

variable {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : Setting hBN Qf ρ)

include hs

theorem qf_axisMap_eq_zero
    (hII : ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
      axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥)
    {a : N} (ha : a ≠ 0) {u : V} (hu : u ∈ rootSpace hBN ρ a) {F : N →+ V} (hFa : F a = u)
    (hF : ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x)) (x : N) : Qf (F x) = 0 := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
    exact QuadraticMap.map_zero Qf
  · obtain ⟨g, rfl⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hs.nondegN ha hx
    rw [hF, hFa, hs.iso]
    exact (rootSpace_totallySingular_and_fixed hs hII ha).1 u hu

theorem eq_top_of_forall_axis_le {W : Submodule K V}
    (hax : ∀ (x : N) (c : K), axis hBN ρ x c ≤ W) : W = ⊤ := by
  let H : Subgroup (Gsp BN) :=
    { carrier := {g | ∀ v, ρ g v - v ∈ W}
      one_mem' := fun v => by simp
      mul_mem' := fun {g h} hg hh v => by
        have e : ρ (g * h) v - v = (ρ g (ρ h v) - ρ h v) + (ρ h v - v) := by
          rw [map_mul, LinearEquiv.mul_apply]
          abel
        rw [e]
        exact W.add_mem (hg _) (hh v)
      inv_mem' := fun {g} hg v => by
        have h1 : ρ g (ρ g⁻¹ v) = v := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        have e : ρ g⁻¹ v - v = -(ρ g (ρ g⁻¹ v) - ρ g⁻¹ v) := by
          rw [h1]
          abel
        rw [e]
        exact W.neg_mem (hg _) }
  have htop : H = ⊤ := eq_top_of_forall_Tsp_mem hBN hs.nondegN fun x c v =>
    hax x c (sub_mem_movedSpace (ρ (Tsp hBN x c)) v)
  have hle : commutatorSpace ρ.range ≤ W := by
    rw [commutatorSpace, Submodule.span_le]
    rintro w ⟨h, ⟨g, rfl⟩, v, rfl⟩
    have hg : g ∈ H := by
      rw [htop]
      exact Subgroup.mem_top g
    exact hg v
  rw [hs.gen] at hle
  exact top_le_iff.mp hle

end Aux

theorem exists_decomposition_of_siegel_of_caseII (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hN : 4 ≤ finrank K N) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hS₀ : ∃ v₀ : N, v₀ ≠ 0 ∧ ∃ c₀ : K, c₀ ≠ 0 ∧
      finrank K (movedSpace (ρ (Tsp hBN v₀ c₀))) = 2 ∧
      ∀ w ∈ movedSpace (ρ (Tsp hBN v₀ c₀)), Qf w = 0)
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0) (hV : commutatorSpace ρ.range = ⊤)
    (hII : ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
      axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥) :
    ∃ W₁ W₂ : Submodule K V, IsCompl W₁ W₂ ∧
      (∀ w ∈ W₁, Qf w = 0) ∧ (∀ w ∈ W₂, Qf w = 0) ∧
      (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
      ∃ (σ : K ≃+* K) (F : N →+ V), (∀ (c : K) x, F (c • x) = σ c • F x) ∧
        Function.Injective F ∧ (∀ x, F x ∈ W₁) ∧ (∀ w ∈ W₁, ∃ x, F x = w) ∧
        ∀ g x, F (g.app x) = ρ g (F x) := by
  have hs := setting_of_contract hq hBN hBNnd hN Qf hnd ρ hρQ hS₀ hC hV
  obtain ⟨a, ha⟩ : ∃ a : N, a ≠ 0 := by
    have : Nontrivial N := Module.nontrivial_of_finrank_pos (R := K) (M := N) (by omega)
    exact exists_ne 0
  obtain ⟨u₁, u₂, σ₁, σ₂, hu₁, hu₂, hli, hσ⟩ := exists_twisted_basis hs hII ha
  obtain ⟨F₁, hF₁a, hF₁⟩ := exists_axisMap hs hII ha hu₁
  obtain ⟨F₂, hF₂a, hF₂⟩ := exists_axisMap hs hII ha hu₂
  have hF₁σ := axisMap_smul hs ha hF₁a hF₁ fun g c hg => (hσ g c hg).1
  have hF₂σ := axisMap_smul hs ha hF₂a hF₂ fun g c hg => (hσ g c hg).2
  have hu₁0 : u₁ ≠ 0 := hli.ne_zero 0
  have hu₂0 : u₂ ≠ 0 := hli.ne_zero 1
  have hF₁0 : F₁ ≠ 0 := fun h => hu₁0 (by rw [← hF₁a, h]; rfl)
  have hF₂0 : F₂ ≠ 0 := fun h => hu₂0 (by rw [← hF₂a, h]; rfl)
  obtain ⟨hspan₁, hirr₁⟩ := twisted_natural_irreducible hBN hBNnd σ₁ F₁ hF₁σ ρ hF₁ hF₁0
  obtain ⟨hspan₂, -⟩ := twisted_natural_irreducible hBN hBNnd σ₂ F₂ hF₂σ ρ hF₂ hF₂0
  set W₁ : Submodule K V := Submodule.span K (Set.range F₁) with hW₁
  set W₂ : Submodule K V := Submodule.span K (Set.range F₂) with hW₂
  have hmem₁ : ∀ x, F₁ x ∈ W₁ := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hmem₂ : ∀ x, F₂ x ∈ W₂ := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hsing₁ : ∀ w ∈ W₁, Qf w = 0 := fun w hw => by
    obtain ⟨x, rfl⟩ := hspan₁ w hw
    exact qf_axisMap_eq_zero hs hII ha hu₁ hF₁a hF₁ x
  have hsing₂ : ∀ w ∈ W₂, Qf w = 0 := fun w hw => by
    obtain ⟨x, rfl⟩ := hspan₂ w hw
    exact qf_axisMap_eq_zero hs hII ha hu₂ hF₂a hF₂ x
  have hinv₁ : ∀ g : Gsp BN, ∀ w ∈ W₁, ρ g w ∈ W₁ := fun g w hw => by
    obtain ⟨x, rfl⟩ := hspan₁ w hw
    rw [← hF₁]
    exact hmem₁ _
  have hinv₂ : ∀ g : Gsp BN, ∀ w ∈ W₂, ρ g w ∈ W₂ := fun g w hw => by
    obtain ⟨x, rfl⟩ := hspan₂ w hw
    rw [← hF₂]
    exact hmem₂ _
  have hinv : ∀ g : Gsp BN, ∀ w ∈ W₁ ⊔ W₂, ρ g w ∈ W₁ ⊔ W₂ := fun g w hw => by
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    exact Submodule.add_mem_sup (hinv₁ g w₁ hw₁) (hinv₂ g w₂ hw₂)
  have hroot : rootSpace hBN ρ a ≤ W₁ ⊔ W₂ := by
    rw [← span_pair_eq_of_finrank_eq_two (finrank_rootSpace hs hII ha).1 hu₁ hu₂ hli,
      Submodule.span_le]
    rintro x (rfl | rfl)
    · exact Submodule.mem_sup_left (hF₁a ▸ hmem₁ a)
    · exact Submodule.mem_sup_right (hF₂a ▸ hmem₂ a)
  have hax : ∀ (x : N) (c : K), axis hBN ρ x c ≤ W₁ ⊔ W₂ := by
    intro x c
    by_cases hx : x = 0
    · rw [hx, axis_zero_point hBNnd]
      exact bot_le
    · obtain ⟨g, rfl⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hBNnd ha hx
      rw [← map_axis_eq]
      rintro _ ⟨w, hw, rfl⟩
      exact hinv g w (hroot (axis_le_rootSpace a c hw))
  have hsup : W₁ ⊔ W₂ = ⊤ := eq_top_of_forall_axis_le hs hax
  have hinf : W₁ ⊓ W₂ = ⊥ := by
    by_contra hne
    have hU := hirr₁ (W₁ ⊓ W₂) hne inf_le_left
      (fun g w hw => ⟨hinv₁ g w hw.1, hinv₂ g w hw.2⟩)
    have hW₁₂ : W₁ ≤ W₂ := calc W₁ = W₁ ⊓ W₂ := hU.symm
      _ ≤ W₂ := inf_le_right
    have hW₂top : W₂ = ⊤ := by
      rw [← hsup]
      exact (sup_eq_right.mpr hW₁₂).symm
    have hall : ∀ v : V, Qf v = 0 := fun v => hsing₂ v (hW₂top ▸ Submodule.mem_top)
    refine hu₁0 (hnd u₁ fun y => ?_)
    have h := QuadraticMap.map_add Qf u₁ y
    rw [hall (u₁ + y), hall u₁, hall y] at h
    linear_combination -h
  exact ⟨W₁, W₂, ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩, hsing₁, hsing₂, hinv₁, hinv₂,
    σ₁, F₁, hF₁σ, injective_of_twisted_equivariant hBN hBNnd σ₁ F₁ hF₁σ ρ hF₁ hF₁0, hmem₁, hspan₁,
    hF₁⟩

theorem exists_decomposition_of_siegel (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hN : 4 ≤ finrank K N) (Qf : QuadraticForm K V)
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : Gsp BN →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hS₀ : ∃ v₀ : N, v₀ ≠ 0 ∧ ∃ c₀ : K, c₀ ≠ 0 ∧
      finrank K (movedSpace (ρ (Tsp hBN v₀ c₀))) = 2 ∧
      ∀ w ∈ movedSpace (ρ (Tsp hBN v₀ c₀)), Qf w = 0)
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0)
    (hV : commutatorSpace ρ.range = ⊤) :
    ∃ W₁ W₂ : Submodule K V, IsCompl W₁ W₂ ∧
      (∀ w ∈ W₁, Qf w = 0) ∧ (∀ w ∈ W₂, Qf w = 0) ∧
      (∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) ∧ (∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂) ∧
      ∃ (σ : K ≃+* K) (F : N →+ V), (∀ (c : K) x, F (c • x) = σ c • F x) ∧
        Function.Injective F ∧ (∀ x, F x ∈ W₁) ∧ (∀ w ∈ W₁, ∃ x, F x = w) ∧
        ∀ g x, F (g.app x) = ρ g (F x) :=
  exists_decomposition_of_siegel_of_caseII hq hBN hBNnd hN Qf hnd ρ hρQ hS₀ hC hV
    (caseII_of_setting (setting_of_contract hq hBN hBNnd hN Qf hnd ρ hρQ hS₀ hC hV))

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
