module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsStd
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsGen
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ABGLocalTools
open scoped MatrixGroups

variable {F : Type} [Field F]

variable (F) in
@[expose] def u₆Mat : Matrix (Fin 6) (Fin 6) F :=
  !![1, 1, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 1, 1, 1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 1]

theorem u₆Mat_upper : ∀ i j : Fin 6, j < i → u₆Mat F i j = 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [u₆Mat]

theorem u₆Mat_diag : ∀ i : Fin 6, u₆Mat F i i = 1 := by
  intro i
  fin_cases i <;> simp [u₆Mat]

theorem det_u₆Mat : (u₆Mat F).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => u₆Mat_upper i j h)]
  simp [u₆Mat_diag]

variable (F) in
@[expose] def u₆ : SL(6, F) := ⟨u₆Mat F, det_u₆Mat⟩

theorem u₆_mem_unitriangular : u₆ F ∈ unitriangular 6 F :=
  ⟨u₆Mat_upper, u₆Mat_diag⟩

theorem u₆_reg : ∀ i j : Fin 6, (j : ℕ) = i + 1 → (u₆ F : Matrix (Fin 6) (Fin 6) F) i j ≠ 0 := by
  intro i j h
  change u₆Mat F i j ≠ 0
  fin_cases i <;> fin_cases j <;> simp_all [u₆Mat]

theorem u₆Mat_map (σ : F →+* F) : (u₆Mat F).map σ = u₆Mat F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u₆Mat]

theorem revGL_six_eq : (revGL 6 F : Matrix (Fin 6) (Fin 6) F) =
    !![0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 1, 0;
       0, 0, 0, 1, 0, 0;
       0, 0, 1, 0, 0, 0;
       0, 1, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0] := by
  ext i j
  rw [revGL_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem u₆_unitary [CharP F 2] :
    (u₆Mat F)ᵀ * (revGL 6 F : Matrix (Fin 6) (Fin 6) F) * u₆Mat F = revGL 6 F := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [revGL_six_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u₆Mat, Matrix.mul_apply, Fin.sum_univ_succ, h2]

theorem u₆_mem_slUnitary [CharP F 2] (σ : F →+* F) :
    u₆ F ∈ slUnitary σ (revGL 6 F : Matrix (Fin 6) (Fin 6) F) := by
  rw [mem_slUnitary]
  change ((u₆Mat F).map σ)ᵀ * _ * u₆Mat F = _
  rw [u₆Mat_map, u₆_unitary]

@[expose] def X05 (c : F) : SL(6, F) :=
  SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) c

theorem coe_X05 (c : F) : (X05 c : Matrix (Fin 6) (Fin 6) F) = Matrix.transvection 0 5 c :=
  rfl

theorem X05_mul (c d : F) : X05 c * X05 d = X05 (c + d) :=
  Subtype.ext (Matrix.transvection_mul_transvection_same 0 5 (by decide) c d)

theorem X05_zero : X05 (0 : F) = 1 :=
  Subtype.ext (Matrix.transvection_zero 0 5)

theorem X05_inv (c : F) : (X05 c)⁻¹ = X05 (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [X05_mul, add_neg_cancel, X05_zero])

theorem X05_mul_inv (c d : F) : X05 c * (X05 d)⁻¹ = X05 (c - d) := by
  rw [X05_inv, X05_mul, sub_eq_add_neg]

theorem X05_mem_unitriangular (c : F) : X05 c ∈ unitriangular 6 F :=
  transvection_mem_unitriangular (show (0 : Fin 6) < 5 by decide) c

theorem X05_mul_comm (c : F) {u : SL(6, F)} (hu : u ∈ unitriangular 6 F) :
    X05 c * u = u * X05 c := by
  have hrow : ∀ j : Fin 6, j ≠ 5 → (u : Matrix (Fin 6) (Fin 6) F) 5 j = 0 := fun j hj =>
    hu.1 5 j (lt_of_le_of_ne (Fin.le_last j) hj)
  have hcol : ∀ i : Fin 6, i ≠ 0 → (u : Matrix (Fin 6) (Fin 6) F) i 0 = 0 := fun i hi =>
    hu.1 i 0 (Fin.pos_iff_ne_zero.mpr hi)
  have h00 : (u : Matrix (Fin 6) (Fin 6) F) 0 0 = 1 := hu.2 0
  have h55 : (u : Matrix (Fin 6) (Fin 6) F) 5 5 = 1 := hu.2 5
  suffices h : Matrix.transvection 0 5 c * (u : Matrix (Fin 6) (Fin 6) F) =
      (u : Matrix (Fin 6) (Fin 6) F) * Matrix.transvection 0 5 c from Subtype.ext h
  ext i j
  by_cases hi : i = 0 <;> by_cases hj : j = 5
  · subst hi hj
    simp [h00, h55]
  · subst hi
    simp [Matrix.mul_transvection_apply_of_ne _ _ _ _ hj, hrow j hj]
  · subst hj
    simp [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi, hcol i hi]
  · simp [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi,
      Matrix.mul_transvection_apply_of_ne _ _ _ _ hj]

theorem stdSL_revGL_X05 [CharP F 2] (σ : F ≃+* F) (c : F) :
    stdSL 6 F (revGL 6 F) σ 1 (X05 c) = X05 (σ c) := by
  have hneg : σ (-c) = σ c := by rw [map_neg, CharTwo.neg_eq]
  have h : (stdSL 6 F (revGL 6 F) σ 1 (X05 c) : Matrix (Fin 6) (Fin 6) F) =
      (X05 (σ c) : Matrix (Fin 6) (Fin 6) F) := by
    rw [coe_stdSL_graphField, inv_eq_self_of_mul_self revGL_mul_self, X05_inv, coe_X05, coe_X05,
      Matrix.transvection, Matrix.transvection, Matrix.map_add _ (map_add σ),
      Matrix.map_one _ (map_zero σ) (map_one σ)]
    simp only [Matrix.map_single]
    rw [hneg, transpose_add, transpose_one, transpose_single, revGL_six_eq_antiId,
      CFSG.LieType.Chevalley.E6GraphLevi.antiId_mul_mul_antiId]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact Subtype.ext h

theorem X05_mem_slUnitary [CharP F 2] (σ : F ≃+* F) {a : F} (ha : σ a = a) :
    X05 a ∈ slUnitary (σ : F →+* F) (revGL 6 F : Matrix (Fin 6) (Fin 6) F) := by
  rw [← fixSub_stdSL_graphField revGL_mul_self σ, mem_fixSub, stdSL_revGL_X05, ha]

section Main

variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

theorem sub_fixed_of_card_four [Finite F] (hF : Nat.card F = 4) {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2) (c : F) : σ (c - σ c) = c - σ c := by
  have : Fintype F := Fintype.ofFinite F
  have h4 : c ^ 4 = c := by
    have := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hF] at this
  have : CharP F 2 := charP_two_of_card_four hF
  have h : (c ^ 2) ^ 2 = c := by rw [← pow_mul]; exact h4
  rw [map_sub, hσ, hσ, h, sub_eq_add_neg, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.neg_eq,
    add_comm]

theorem eq_sup_normalizer_std (hF : Nat.card F = 4) (φ : SL(6, F) →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center SL(6, F)) {t : G} {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2)
    (hact : ∀ x, t * (φ x : G) * t⁻¹ = φ (stdSL 6 F (revGL 6 F) σ 1 x))
    {S₀ P₀ : Subgroup G} (hS₀ : IsSylowOf 2 S₀ (K ⊓ centralizer ({t} : Set G)))
    (hP₀ : IsSylowOf 2 P₀ K) (hSP : S₀ ≤ P₀) (huS : (φ (u₆ F) : G) ∈ S₀) :
    K = (K ⊓ centralizer ({t} : Set G)) ⊔
      (P₀ ⊓ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : CharP F 2 := charP_two_of_card_four hF
  set f := K.subtype.comp φ with hf
  set C := K ⊓ centralizer ({t} : Set G) with hCdef
  have hC : C = (slUnitary (σ : F →+* F) (revGL 6 F : Matrix (Fin 6) (Fin 6) F)).map f :=
    centralizer_eq_slUnitary hF (by norm_num) φ hφ hker hσ hact
  obtain ⟨PU, hPU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 6) (by norm_num)
  have hU2 : IsPGroup 2 (unitriangular 6 F) := hPU ▸ PU.isPGroup'
  have hPeq : P₀ = (unitriangular 6 F).map f :=
    eq_map_unitriangular hF (by norm_num) φ hφ u₆_mem_unitriangular u₆_reg hP₀ (hSP huS)
  have hSeq : S₀ = (unitriangular 6 F).map f ⊓ C :=
    (hS₀.eq_of_le (le_inf (hPeq ▸ hSP) hS₀.le) inf_le_right
      ((hU2.map f).to_le inf_le_left)).symm
  have hrange : f.range = K := by
    rw [hf, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφ, ← MonoidHom.range_eq_map,
      range_subtype]
  have hXN : ∀ c : F, f (X05 c) ∈ P₀ ⊓ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G) := by
    intro c
    refine ⟨hPeq ▸ ⟨X05 c, X05_mem_unitriangular c, rfl⟩, mem_normalizer_sup_zpowers ?_ ?_⟩
    · intro a ha
      have ha' : a ∈ (unitriangular 6 F).map f ⊓ C := hSeq ▸ ha
      obtain ⟨v, hv, rfl⟩ := ha'.1
      rw [← map_mul, ← map_inv, ← map_mul, X05_mul_comm c hv, mul_inv_cancel_right]
      exact (le_sup_left : S₀ ≤ S₀ ⊔ zpowers t) ha
    · have h1 : f (X05 c) * t * (f (X05 c))⁻¹ = f (X05 (c - σ c)) * t := by
        have h2 : t * f (X05 c) * t⁻¹ = f (X05 (σ c)) := by
          change t * (φ (X05 c) : G) * t⁻¹ = φ (X05 (σ c))
          rw [hact, stdSL_revGL_X05]
        rw [← X05_mul_inv, map_mul, map_inv, ← h2]
        group
      rw [h1]
      refine mul_mem ((le_sup_left : S₀ ≤ S₀ ⊔ zpowers t) ?_)
        ((le_sup_right : zpowers t ≤ S₀ ⊔ zpowers t) (mem_zpowers t))
      rw [hSeq]
      exact ⟨⟨_, X05_mem_unitriangular _, rfl⟩, hC ▸ ⟨_, X05_mem_slUnitary σ
        (sub_fixed_of_card_four hF hσ c), rfl⟩⟩
  refine le_antisymm ?_ (sup_le inf_le_left (inf_le_left.trans hP₀.le))
  rw [← hrange, MonoidHom.range_eq_map, ← closure_unitarySL_transvection_eq_top hF
    (σ : F →+* F) hσ, MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx | ⟨c, rfl⟩, rfl⟩
  · refine (le_sup_left : C ≤ C ⊔ (P₀ ⊓ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G))) ?_
    rw [hC, slUnitary_six_eq]
    exact ⟨x, hx, rfl⟩
  · exact (le_sup_right : P₀ ⊓ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G) ≤ C ⊔ _)
      (hXN c)

theorem eq_sup_normalizer_of_graphField (hF : Nat.card F = 4) (φ : SL(6, F) →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center SL(6, F)) {t : G} {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2)
    (hact : ∀ x, t * (φ x : G) * t⁻¹ = φ (stdSL 6 F (revGL 6 F) σ 1 x))
    {S₀ P₀ : Subgroup G} (hS₀ : IsSylowOf 2 S₀ (K ⊓ centralizer ({t} : Set G)))
    (hP₀ : IsSylowOf 2 P₀ K) (hSP : S₀ ≤ P₀) :
    K = (K ⊓ centralizer ({t} : Set G)) ⊔
      (P₀ ⊓ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : CharP F 2 := charP_two_of_card_four hF
  set f := K.subtype.comp φ with hf
  set S := slUnitary (σ : F →+* F) (revGL 6 F : Matrix (Fin 6) (Fin 6) F) with hSdef
  have hC : K ⊓ centralizer ({t} : Set G) = S.map f :=
    centralizer_eq_slUnitary hF (by norm_num) φ hφ hker hσ hact
  obtain ⟨PU, hPU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 6) (by norm_num)
  have hU2 : IsPGroup 2 (unitriangular 6 F) := hPU ▸ PU.isPGroup'
  have hu₆ : u₆ F ∈ unitriangular 6 F ⊓ S := ⟨u₆_mem_unitriangular, u₆_mem_slUnitary _⟩
  have hSU : IsSylowOf 2 (unitriangular 6 F ⊓ S) S := by
    obtain ⟨T, hT, hST⟩ := exists_isSylowOf_ge (hU2.to_le inf_le_left) inf_le_right
    have hTU : T ≤ unitriangular 6 F :=
      le_unitriangular_of_regular_mem 2 (by norm_num) u₆_mem_unitriangular u₆_reg hT.isPGroup
        (hST hu₆)
    rwa [le_antisymm (le_inf hTU hT.le) hST] at hT
  have hfSU : IsSylowOf 2 ((unitriangular 6 F ⊓ S).map f) (K ⊓ centralizer ({t} : Set G)) :=
    hC ▸ isSylowOf_map f hSU
  obtain ⟨k, hkC, hk⟩ := hfSU.exists_mem_conj hS₀
  obtain ⟨g, hgS, rfl⟩ := (hC ▸ hkC : k ∈ S.map f)
  have hγg : stdSL 6 F (revGL 6 F) σ 1 g = g := by
    have := hgS
    rwa [hSdef, ← fixSub_stdSL_graphField revGL_mul_self σ] at this
  set φ' := φ.comp (MulAut.conj g).toMonoidHom with hφ'
  have hφ'surj : Function.Surjective φ' := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨g⁻¹ * x * g, by simp [hφ', mul_assoc]⟩
  have hker' : φ'.ker ≤ center SL(6, F) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ center SL(6, F) := hker hx
    have h3 : x = g * x * g⁻¹ := by
      have h5 := mem_center_iff.mp h1 g
      have h4 : g * x * g⁻¹ * g = g * x := by group
      rw [h4] at h5
      exact (mul_left_cancel h5).symm
    rw [h3]
    exact h1
  have hact' : ∀ x, t * (φ' x : G) * t⁻¹ = φ' (stdSL 6 F (revGL 6 F) σ 1 x) := by
    intro x
    change t * (φ (g * x * g⁻¹) : G) * t⁻¹ = φ (g * stdSL 6 F (revGL 6 F) σ 1 x * g⁻¹)
    rw [hact]
    congr 2
    rw [map_mul (stdSL 6 F (revGL 6 F) σ 1), map_mul (stdSL 6 F (revGL 6 F) σ 1),
      map_inv (stdSL 6 F (revGL 6 F) σ 1), hγg]
  have huS : (φ' (u₆ F) : G) ∈ S₀ := by
    rw [hk]
    refine ⟨u₆ F, hu₆, ?_⟩
    change (φ (u₆ F) : G) = (φ g : G)⁻¹ * φ (g * u₆ F * g⁻¹) * φ g
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact eq_sup_normalizer_std hF φ' hφ'surj hker' hσ hact' hS₀ hP₀ hSP huS

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
