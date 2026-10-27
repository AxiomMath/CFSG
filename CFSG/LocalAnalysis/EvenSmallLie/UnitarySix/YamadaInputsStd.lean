module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSU
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsFlag
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSylow

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ABGLocalTools
open scoped MatrixGroups

variable {n : ℕ} {F : Type} [Field F] [Finite F] {G : Type*} [Group G] {K : Subgroup G}

omit [Finite F] in
theorem revGL_map_equiv (σ : F ≃+* F) :
    (revGL n F : Matrix (Fin n) (Fin n) F).map σ = revGL n F := by
  ext i j
  rw [Matrix.map_apply, revGL_apply]
  split_ifs <;> simp

omit [Finite F] in
theorem stdSL_inv_center (E : GL (Fin n) F) {z : SL(n, F)} (hz : z ∈ center SL(n, F)) :
    (stdSL n F E 1 0)⁻¹ z = z := by
  calc (stdSL n F E 1 0)⁻¹ z = (stdSL n F E 1 0)⁻¹ (stdSL n F E 1 0 z) := by
        rw [stdSL_conj_center E hz]
    _ = z := MulAut.inv_apply_self _ _ z

theorem exists_std_graphField (hF : Nat.card F = 4) (ψ : SL(n, F) →* K)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center SL(n, F)) {t : G} {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2) {H : GL (Fin n) F}
    (hH : ∀ x, t * (ψ x : G) * t⁻¹ =
      ψ ((stdSL n F H 1 0 * stdSL n F 1 σ 1 * (stdSL n F H 1 0)⁻¹) x)) :
    ∃ φ : SL(n, F) →* K, Function.Surjective φ ∧ φ.ker = ψ.ker ∧
      ∀ x, t * (φ x : G) * t⁻¹ = φ (stdSL n F (revGL n F) σ 1 x) := by
  obtain ⟨Q, hQ⟩ := exists_witt hF hσ n
  have hconj := conj_graphField_eq σ H revGL_mul_self hQ
  set c := stdSL n F (H * Q) 1 0 with hc
  refine ⟨ψ.comp c.toMonoidHom, fun k => ?_, ?_, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := hψ k
    exact ⟨c⁻¹ x, by simp⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      have h1 : c x ∈ ψ.ker := h
      have h2 : x = c x := by
        calc x = c⁻¹ (c x) := (MulAut.inv_apply_self _ _ _).symm
          _ = c x := stdSL_inv_center _ (hker h1)
      rw [h2]
      exact h
    · intro h
      change ψ (c x) = 1
      rw [stdSL_conj_center _ (hker h), h]
  · change t * (ψ (c x) : G) * t⁻¹ = ψ (c (stdSL n F (revGL n F) σ 1 x))
    rw [hH, hconj, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

omit [Finite F] in
theorem centralizer_eq_slUnitary (hF : Nat.card F = 4) (hn : 1 ≤ n) (φ : SL(n, F) →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center SL(n, F)) {t : G} {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2)
    (hact : ∀ x, t * (φ x : G) * t⁻¹ = φ (stdSL n F (revGL n F) σ 1 x)) :
    K ⊓ centralizer ({t} : Set G) =
      (slUnitary (σ : F →+* F) (revGL n F : Matrix (Fin n) (Fin n) F)).map (K.subtype.comp φ) := by
  rw [centralizer_eq_map_fixSub φ hφ hact fun x z hz hxz => ⟨1, one_mem _, by
    rw [mul_one, hxz, eq_one_of_graphField_eq_mul hF hσ hn revGL_mul_self revGL_transpose
      (revGL_map_equiv σ) (hker hz) hxz, mul_one]⟩, fixSub_stdSL_graphField revGL_mul_self]

theorem card_ker_dvd_three (hF : Nat.card F = 4) (hn : 1 ≤ n) (φ : SL(n, F) →* K)
    (hker : φ.ker ≤ center SL(n, F)) : Nat.card φ.ker ∣ 3 := by
  have h := card_scalars_dvd (K := F) hn
  rw [scalars_eq_center, hF] at h
  exact (card_dvd_of_le hker).trans h

omit [Finite F] in
theorem card_map_mul_card_ker' (φ : SL(n, F) →* K) {S : Subgroup SL(n, F)} (hS : φ.ker ≤ S) :
    Nat.card (S.map (K.subtype.comp φ)) * Nat.card φ.ker = Nat.card S := by
  set f := (K.subtype.comp φ).comp S.subtype
  have hkerf : f.ker = φ.ker.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change ((φ s : K) : G) = 1 ↔ φ s = 1
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have h := card_ker_mul_card_range f
  rw [hkerf, MonoidHom.range_comp, range_subtype,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv] at h
  rw [mul_comm, h]

theorem eq_map_unitriangular [Finite G] (hF : Nat.card F = 4) (hn : 1 ≤ n) (φ : SL(n, F) →* K)
    (hφ : Function.Surjective φ) {u : SL(n, F)} (hu : u ∈ unitriangular n F)
    (hreg : ∀ i j : Fin n, (j : ℕ) = i + 1 → (u : Matrix (Fin n) (Fin n) F) i j ≠ 0)
    {P₀ : Subgroup G} (hP₀ : IsSylowOf 2 P₀ K) (huP : (φ u : G) ∈ P₀) :
    P₀ = (unitriangular n F).map (K.subtype.comp φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_two_of_card_four hF
  set f := K.subtype.comp φ with hf
  obtain ⟨PU, hPU⟩ := exists_sylow_unitriangular (K := F) 2 hn
  have hU2 : IsPGroup 2 (unitriangular n F) := hPU ▸ PU.isPGroup'
  have hrange : f.range = K := by
    rw [hf, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map,
      range_subtype]
  set R := P₀.comap f
  have huR : u ∈ R := huP
  have hz2 : IsPGroup 2 (zpowers u) := hU2.to_le (zpowers_le.mpr hu)
  obtain ⟨T, hT, huT⟩ := exists_isSylowOf_ge hz2 (zpowers_le.mpr huR)
  have hTU : T ≤ unitriangular n F :=
    le_unitriangular_of_regular_mem 2 hn hu hreg hT.isPGroup (huT (mem_zpowers u))
  have hRmap : R.map f = P₀ := by
    rw [map_comap_eq, hrange, inf_eq_right.mpr hP₀.le]
  have hTmap : IsSylowOf 2 (T.map f) P₀ := hRmap ▸ isSylowOf_map f hT
  have hP₀T : P₀ = T.map f := hTmap.eq_of_le hTmap.le le_rfl hP₀.isPGroup
  refine (hP₀.eq_of_le (hP₀T ▸ map_mono hTU) ?_ (hU2.map f)).symm
  rw [← hrange]
  exact map_le_range f _

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
