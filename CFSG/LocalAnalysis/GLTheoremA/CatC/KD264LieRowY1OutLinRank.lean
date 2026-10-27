module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem kdY1Out_exists_isPrimitiveRoot_three (K : Type) [Field K] [Finite K]
    (h : 3 ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3
    (by rwa [Nat.card_eq_fintype_card] at hdvd)
  exact ⟨(x : K), IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hx)⟩

abbrev kdY1Mu3 (K : Type) [Field K] : Subgroup Kˣ := rootsOfUnity 3 K

section Diag

variable (K : Type) [Field K]

@[expose] def kdY1Ent (x : Fin 4 → Kˣ) (k : ℕ) : Kˣ :=
  if h : k < 4 then x ⟨k, h⟩ else if k = 4 then (∏ i, x i)⁻¹ else 1

theorem kdY1Ent_mul (x y : Fin 4 → Kˣ) (k : ℕ) :
    kdY1Ent K (x * y) k = kdY1Ent K x k * kdY1Ent K y k := by
  unfold kdY1Ent
  split_ifs with h1 h2
  · rfl
  · simp [Finset.prod_mul_distrib, mul_inv, mul_comm]
  · simp

theorem kdY1Ent_one (k : ℕ) : kdY1Ent K 1 k = 1 := by
  unfold kdY1Ent
  split_ifs <;> simp

theorem kdY1Ent_four (x : Fin 4 → Kˣ) : kdY1Ent K x 4 = (∏ i, x i)⁻¹ := by
  simp [kdY1Ent]

theorem prod_kdY1Ent (x : Fin 4 → Kˣ) {m : ℕ} (hm : 5 ≤ m) :
    ∏ j : Fin m, kdY1Ent K x j = 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun k => kdY1Ent K x k) m]
  have hsub : Finset.range 5 ⊆ Finset.range m := Finset.range_subset_range.mpr hm
  have hf : ∀ k ∈ Finset.range m, k ∉ Finset.range 5 → kdY1Ent K x k = 1 := by
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    unfold kdY1Ent
    rw [dif_neg (by omega), if_neg (by omega)]
  rw [← Finset.prod_subset hsub hf, Finset.prod_range_succ, kdY1Ent_four]
  have h4 : ∏ k ∈ Finset.range 4, kdY1Ent K x k = ∏ i : Fin 4, x i := by
    simp [Finset.prod_range_succ, kdY1Ent, Fin.prod_univ_four]
  rw [h4, mul_inv_cancel]

@[expose] def kdY1Diag (m : ℕ) (x : Fin 4 → Kˣ) : Matrix (Fin m) (Fin m) K :=
  Matrix.diagonal fun j => (kdY1Ent K x j : K)

theorem kdY1Diag_det {m : ℕ} (hm : 5 ≤ m) (x : Fin 4 → Kˣ) :
    (kdY1Diag K m x).det = 1 := by
  rw [kdY1Diag, Matrix.det_diagonal]
  have h := congrArg (fun u : Kˣ => (u : K)) (prod_kdY1Ent K x hm)
  simpa [Units.coe_prod] using h

@[expose] def kdY1SL {m : ℕ} (hm : 5 ≤ m) (x : Fin 4 → Kˣ) : Matrix.SpecialLinearGroup (Fin m) K :=
  ⟨kdY1Diag K m x, kdY1Diag_det K hm x⟩

@[expose] def kdY1Hom {m : ℕ} (hm : 5 ≤ m) : (Fin 4 → Kˣ) →* Matrix.SpecialLinearGroup (Fin m) K where
  toFun x := kdY1SL K hm x
  map_one' := by
    apply Subtype.ext
    simp [kdY1SL, kdY1Diag, kdY1Ent_one]
  map_mul' x y := by
    apply Subtype.ext
    show kdY1Diag K m (x * y) = kdY1Diag K m x * kdY1Diag K m y
    rw [kdY1Diag, kdY1Diag, kdY1Diag, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [kdY1Ent_mul]

end Diag

section Phi

variable (K : Type) [Field K]
theorem kdY1Hom_apply_diag {m : ℕ} (hm : 5 ≤ m) (x : Fin 4 → Kˣ) (i : Fin m) :
    ((kdY1Hom K hm x : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) i i =
      (kdY1Ent K x i : K) := by
  change kdY1Diag K m x i i = _
  rw [kdY1Diag, Matrix.diagonal_apply_eq]

@[expose] def kdY1Coord : (Fin 4 → kdY1Mu3 K) →* (Fin 4 → Kˣ) where
  toFun x i := (x i : Kˣ)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def kdY1Phi {m : ℕ} (hm : 6 ≤ m) : (Fin 4 → kdY1Mu3 K) →* projectiveSL m K :=
  (proj m K).comp ((kdY1Hom K (by omega : 5 ≤ m)).comp (kdY1Coord K))

theorem kdY1Phi_injective {m : ℕ} (hm : 6 ≤ m) : Function.Injective (kdY1Phi K hm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, kdY1Phi, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hx
  obtain ⟨c, -, hmat⟩ := hx
  rw [MonoidHom.comp_apply] at hmat
  have hentry : ∀ i : Fin m, (kdY1Ent K (kdY1Coord K x) i : K) = c := by
    intro i
    have h := congrFun (congrFun hmat i) i
    rw [kdY1Hom_apply_diag, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
    exact h
  have h5 := hentry ⟨5, by omega⟩
  have hc1 : (c : K) = 1 := by
    rw [← h5]
    simp [kdY1Ent]
  have hcoord : ∀ k : ℕ, (hk : k < 4) → ((x ⟨k, hk⟩ : kdY1Mu3 K) : Kˣ) = 1 := by
    intro k hk
    have h := hentry ⟨k, by omega⟩
    rw [hc1] at h
    have h' : kdY1Ent K (kdY1Coord K x) k = 1 := Units.ext (by simpa using h)
    simpa [kdY1Ent, hk, kdY1Coord] using h'
  rw [Subgroup.mem_bot]
  funext i
  exact Subtype.ext (by simpa using hcoord i.1 i.2)

theorem kdY1Phi_range_isElemAbelian {m : ℕ} (hm : 6 ≤ m) :
    CFSG.Open.IsElemAbelian 3 (kdY1Phi K hm).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · intro z hz
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
    have hy : y ^ 3 = 1 := by
      funext i
      have h3 : ((y i : kdY1Mu3 K) : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp (y i).2
      apply Subtype.ext
      simpa using h3
    rw [← map_pow, hy, map_one]

theorem kdY1Phi_card [Finite K] {m : ℕ} (hm : 6 ≤ m) (h : 3 ∣ Nat.card K - 1) :
    Nat.card (kdY1Phi K hm).range = 3 ^ 4 := by
  obtain ⟨ζ, hζ⟩ := kdY1Out_exists_isPrimitiveRoot_three K h
  have hmu : Nat.card (kdY1Mu3 K) = 3 := hζ.card_rootsOfUnity
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (kdY1Phi_injective K hm),
    Subgroup.card_top, Nat.card_fun, hmu]
  simp

theorem exists_elemAbelian_card_81 [Finite K] {m : ℕ} (hm : 6 ≤ m) (h : 3 ∣ Nat.card K - 1) :
    ∃ E : Subgroup (projectiveSL m K), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 :=
  ⟨(kdY1Phi K hm).range, kdY1Phi_range_isElemAbelian K hm, kdY1Phi_card K hm h⟩

end Phi



end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
