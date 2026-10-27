module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open scoped Polynomial

theorem mem_subfield_of_pow_four {K : Type} [Field K] (K₀ : Subfield K)
    (hK₀ : Nat.card K₀ = 4) {t : K} (ht : t ^ 4 = t) : t ∈ K₀ := by
  classical
  have hfin : Finite K₀ := Nat.finite_of_card_ne_zero (by rw [hK₀]; norm_num)
  let _ : Fintype K₀ := Fintype.ofFinite K₀
  have hsub : (K₀ : Set K) ⊆ {t | t ^ 4 = t} := fun y hy => by
    have h := FiniteField.pow_card (⟨y, hy⟩ : K₀)
    rw [← Nat.card_eq_fintype_card, hK₀] at h
    exact congrArg Subtype.val h
  have hP0 : (Polynomial.X ^ 4 - Polynomial.X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K (by norm_num)
  have hroots : {t : K | t ^ 4 = t} ⊆
      ((Polynomial.X ^ 4 - Polynomial.X : K[X]).roots.toFinset : Set K) := fun y hy => by
    simp [Polynomial.mem_roots hP0, sub_eq_zero.2 (show y ^ 4 = y from hy)]
  have hfinR : ({t : K | t ^ 4 = t}).Finite := (Finset.finite_toSet _).subset hroots
  have hle : ({t : K | t ^ 4 = t}).ncard ≤ 4 :=
    calc ({t : K | t ^ 4 = t}).ncard
        ≤ ((Polynomial.X ^ 4 - Polynomial.X : K[X]).roots.toFinset : Set K).ncard :=
          Set.ncard_le_ncard hroots (Finset.finite_toSet _)
      _ = (Polynomial.X ^ 4 - Polynomial.X : K[X]).roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ Multiset.card (Polynomial.X ^ 4 - Polynomial.X : K[X]).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ 4 - Polynomial.X : K[X]).natDegree := Polynomial.card_roots' _
      _ = 4 := FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num)
  have heq : (K₀ : Set K) = {t | t ^ 4 = t} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfinR
    rw [← Nat.card_coe_set_eq]
    exact hle.trans (le_of_eq hK₀.symm)
  have : t ∈ (K₀ : Set K) := by rw [heq]; exact ht
  exact this

section Transport

variable {p f : ℕ} {K L : Type} [Field K] [Field L]

theorem map_bar (hK : UnitaryFieldData p f K) (hL : UnitaryFieldData p f L) (φ : K →+* L)
    (x : K) : φ (hK.bar x) = hL.bar (φ x) := by
  simp only [UnitaryFieldData.bar_apply, map_pow]

theorem map_mem_unitarySU (hK : UnitaryFieldData p f K) (hL : UnitaryFieldData p f L)
    (φ : K →+* L) {A : GL (Fin 3) K} (hA : A ∈ unitarySU p f K 3) :
    GeneralLinearGroup.map φ A ∈ unitarySU p f L 3 := by
  rw [mem_unitarySU_iff hK] at hA
  rw [mem_unitarySU_iff hL]
  obtain ⟨hdet, hbar⟩ := hA
  have hmat : ((GeneralLinearGroup.map φ A : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (A : Matrix (Fin 3) (Fin 3) K).map φ := rfl
  rw [hmat]
  refine ⟨?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · have h1 : ((A : Matrix (Fin 3) (Fin 3) K).map φ).map hL.bar =
        ((A : Matrix (Fin 3) (Fin 3) K).map hK.bar).map φ :=
      Matrix.ext fun i j => (map_bar hK hL φ _).symm
    rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, hbar, Matrix.map_one _ (map_zero φ)
      (map_one φ)]

@[expose] noncomputable def suMap (hK : UnitaryFieldData p f K) (hL : UnitaryFieldData p f L)
    (φ : K →+* L) : unitarySU p f K 3 →* unitarySU p f L 3 :=
  ((GeneralLinearGroup.map φ).comp (unitarySU p f K 3).subtype).codRestrict (unitarySU p f L 3)
    fun g => map_mem_unitarySU hK hL φ g.2

theorem coe_suMap (hK : UnitaryFieldData p f K) (hL : UnitaryFieldData p f L) (φ : K →+* L)
    (g : unitarySU p f K 3) :
    (((suMap hK hL φ g : unitarySU p f L 3) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map φ :=
  rfl

theorem suMap_injective (hK : UnitaryFieldData p f K) (hL : UnitaryFieldData p f L)
    (φ : K →+* L) : Function.Injective (suMap hK hL φ) := by
  intro g g' hg
  refine Subtype.ext (Units.ext ?_)
  have := congrArg (fun x : unitarySU p f L 3 =>
    ((x : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) hg
  exact Matrix.map_injective φ.injective this

theorem suMap_suMap (hK : UnitaryFieldData p f K) (hL : UnitaryFieldData p f L)
    (e : K ≃+* L) (s : unitarySU p f L 3) :
    suMap hK hL e.toRingHom (suMap hL hK e.symm.toRingHom s) = s := by
  refine Subtype.ext (Units.ext ?_)
  change (((s : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).map e.symm.toRingHom).map
    e.toRingHom = _
  rw [Matrix.map_map]
  ext i j
  simp

end Transport

theorem eq_top_of_closure_eq_top {G S : Type*} [Group G] [Group S] (φ : G →* S)
    (hφ : Function.Injective φ) {T : Set S} (hT : Subgroup.closure T = ⊤) {H : Subgroup G}
    (hsub : ∀ t ∈ T, ∃ g ∈ H, φ g = t) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hle : Subgroup.closure T ≤ H.map φ := by
    rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨g', hg', rfl⟩ := hsub t ht
    exact ⟨g', hg', rfl⟩
  have hg : φ g ∈ Subgroup.closure T := by
    rw [hT]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxg⟩ := hle hg
  rwa [← hφ hxg]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
