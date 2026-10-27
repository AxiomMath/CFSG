module

public import Certificates.Certificate22612
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.GL42

open Matrix Subgroup

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

abbrev GL4 : Type := GL (Fin 4) (ZMod 2)

namespace V4c

@[expose] def toVec (v : V4c) : Fin 4 → ZMod 2 := ![v.x0, v.x1, v.x2, v.x3]

@[expose] def ofVec (v : Fin 4 → ZMod 2) : V4c := ⟨v 0, v 1, v 2, v 3⟩

theorem toVec_ofVec (v : Fin 4 → ZMod 2) : (ofVec v).toVec = v := by
  funext i
  fin_cases i <;> rfl

theorem toVec_zero : zero.toVec = 0 := by
  funext i
  fin_cases i <;> rfl

theorem mem_all (v : V4c) : v ∈ all := by
  obtain ⟨a, b, c, d⟩ := v
  revert a b c d
  decide

end V4c

namespace M4c

@[expose] def toMat (A : M4c) : M4 := Matrix.of ![A.r0.toVec, A.r1.toVec, A.r2.toVec, A.r3.toVec]

@[expose] def ofMat (M : M4) : M4c :=
  ⟨V4c.ofVec (M 0), V4c.ofVec (M 1), V4c.ofVec (M 2), V4c.ofVec (M 3)⟩

theorem ofMat_toMat (A : M4c) : ofMat A.toMat = A := rfl

theorem toMat_injective : Function.Injective toMat := fun A B h => by
  rw [← ofMat_toMat A, h, ofMat_toMat]

theorem toMat_mul (A B : M4c) : (A.mul B).toMat = A.toMat * B.toMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, mul, mulVec, transpose, V4c.dot, V4c.toVec, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

theorem toMat_one : one.toMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, one, V4c.toVec]

theorem toVec_mulVec (A : M4c) (v : V4c) : (A.mulVec v).toVec = A.toMat *ᵥ v.toVec := by
  funext i
  fin_cases i <;>
    simp [toMat, mulVec, V4c.dot, V4c.toVec, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem toMat_ofFun (f : Fin 4 → Fin 4 → ZMod 2) : (ofFun f).toMat = Matrix.of f := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end M4c

theorem e0_mul_self : ∀ e ∈ e0c, e.mul e = M4c.one := by decide

theorem toMat_transc {i j : Fin 4} (hij : i ≠ j) : (transc i j).toMat = transvection i j 1 := by
  ext r s
  rw [transc, M4c.toMat_ofFun, Matrix.of_apply, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases h1 : r = s
  · subst h1
    have h : ¬ (i = r ∧ j = r) := fun h => hij (h.1.trans h.2.symm)
    simp [h]
  · by_cases h2 : r = i ∧ s = j
    · obtain ⟨rfl, rfl⟩ := h2
      simp [h1]
    · have h2' : ¬ (i = r ∧ j = s) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      simp [h1, h2, h2']

theorem exists_transAt {i j : Fin 4} (hij : i ≠ j) : ∃ m < 12, transAt m = transc i j := by
  revert i j
  decide

theorem transc_mul_self {i j : Fin 4} (hij : i ≠ j) :
    (transc i j).toMat * (transc i j).toMat = 1 := by
  rw [toMat_transc hij, transvection_mul_transvection_same i j hij,
    show (1 + 1 : ZMod 2) = 0 by decide, transvection_zero]

theorem conjAt_close {k i : ℕ} (hk : k < 70) (hi : i < 12) :
    closeIdx k i < 70 ∧ SetEq (conjT (transAt i) (conjAt k)) (conjAt (closeIdx k i)) :=
  Certificates.certificate22612.1 k (List.mem_range.mpr hk) i (List.mem_range.mpr hi)

theorem conjAt_wit {k : ℕ} (hk : k < 70) :
    WitP (conjAt k) (witAt k) :=
  Certificates.certificate22612.2 k (List.mem_range.mpr hk)

@[expose] def listSet (C : List M4c) : Set M4 := {y | ∃ c ∈ C, c.toMat = y}

@[expose] def conjSet (M : M4) (C : List M4c) : Set M4 := {y | ∃ c ∈ C, M⁻¹ * c.toMat * M = y}

theorem listSet_eq_of_setEq {A B : List M4c} (h : SetEq A B) : listSet A = listSet B := by
  ext y
  exact ⟨fun ⟨c, hc, hy⟩ => ⟨c, h.1 c hc, hy⟩, fun ⟨c, hc, hy⟩ => ⟨c, h.2 c hc, hy⟩⟩

theorem conjSet_one (C : List M4c) : conjSet 1 C = listSet C := by
  ext y
  simp only [conjSet, listSet, inv_one, Matrix.one_mul, Matrix.mul_one, Set.mem_ofPred_eq]

theorem conjSet_mul {A B : M4} {C C' : List M4c} (h : conjSet A C = listSet C') :
    conjSet (A * B) C = conjSet B C' := by
  ext y
  simp only [conjSet, Set.mem_ofPred_eq, Matrix.mul_inv_rev]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c', hc', he⟩ : A⁻¹ * c.toMat * A ∈ listSet C' := by rw [← h]; exact ⟨c, hc, rfl⟩
    exact ⟨c', hc', by rw [he]; simp only [Matrix.mul_assoc]⟩
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨c, hc, he⟩ : c'.toMat ∈ conjSet A C := by rw [h]; exact ⟨c', hc', rfl⟩
    exact ⟨c, hc, by rw [← he]; simp only [Matrix.mul_assoc]⟩

theorem exists_conjSet_eq {M : M4} (hM : M.det ≠ 0) :
    ∀ k < 70, ∃ k' < 70, conjSet M (conjAt k) = listSet (conjAt k') := by
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun N => ∀ k < 70, ∃ k' < 70, conjSet N (conjAt k) = listSet (conjAt k')) M hM ?_ ?_ ?_
  · intro D hD k hk
    have h1 : ∀ i, D i = 1 := by
      intro i
      have hi : D i ≠ 0 := by
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      revert hi
      generalize D i = x
      revert x
      decide
    have hD1 : diagonal D = 1 := by
      rw [show D = fun _ => 1 from funext h1]
      exact diagonal_one
    exact ⟨k, hk, by rw [hD1, conjSet_one]⟩
  · rintro ⟨i, j, hij, c⟩ k hk
    rw [TransvectionStruct.toMatrix_mk]
    rcases (show c = 0 ∨ c = 1 by revert c; decide) with rfl | rfl
    · exact ⟨k, hk, by rw [transvection_zero, conjSet_one]⟩
    · obtain ⟨m, hm, hmt⟩ := exists_transAt hij
      obtain ⟨hk', hset⟩ := conjAt_close hk hm
      refine ⟨closeIdx k m, hk', ?_⟩
      rw [← listSet_eq_of_setEq hset, ← toMat_transc hij, ← hmt]
      have hinv : ((transAt m).toMat)⁻¹ = (transAt m).toMat :=
        inv_eq_left_inv (by rw [hmt]; exact transc_mul_self hij)
      ext y
      simp only [conjSet, listSet, conjT, List.mem_map, Set.mem_ofPred_eq, hinv]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨_, ⟨c, hc, rfl⟩, by rw [M4c.toMat_mul, M4c.toMat_mul]⟩
      · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
        exact ⟨c, hc, by rw [M4c.toMat_mul, M4c.toMat_mul]⟩
  · intro A B _ _ hA hB k hk
    obtain ⟨k₁, hk₁, h₁⟩ := hA k hk
    obtain ⟨k₂, hk₂, h₂⟩ := hB k₁ hk₁
    exact ⟨k₂, hk₂, (conjSet_mul h₁).trans h₂⟩

theorem mul_self_eq_one_of_pow_four {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : ∀ s ∈ S, s * s = 1) {g : G} (hg : g ^ 4 = 1) : g * g = 1 := by
  have hP : IsPGroup 2 (zpowers g) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G S Q
  have hgQ : g ∈ ((a • S : Sylow 2 G) : Subgroup G) := hQ (mem_zpowers g)
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hgQ
  obtain ⟨s, hs, rfl⟩ := hgQ
  rw [MulAut.smul_def, MulAut.conj_apply]
  calc a * s * a⁻¹ * (a * s * a⁻¹) = a * (s * s) * a⁻¹ := by group
    _ = 1 := by rw [hS s hs, mul_one, mul_inv_cancel]

theorem mem_of_comm {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {g : G} (hg : g * g = 1)
    (hc : ∀ s ∈ S, s * g = g * s) : g ∈ S := by
  have hP : IsPGroup 2 (zpowers g) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [pow_one, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two, hg]))
  have hN : g ∈ normalizer ((S : Subgroup G) : Set G) := mem_normalizer_fintype fun s hs => by
    rw [← hc s hs, mul_inv_cancel_right]
    exact hs
  have h := (hP.inf_normalizer_sylow S).le (mem_inf.mpr ⟨mem_zpowers g, hN⟩)
  exact (mem_inf.mp h).2

section Transitive

variable {G : Type*} [Group G] [Finite G] (ρ : G →* GL4)

omit [Finite G] in
theorem exists_wordProd {gens : List M4c} (hg : ∀ c ∈ gens, ∃ g : G, ((ρ g : GL4) : M4) = c.toMat)
    (w : List ℕ) : ∃ g : G, ((ρ g : GL4) : M4) = (wordProd gens w).toMat := by
  unfold wordProd
  suffices h : ∀ A : M4c, (∃ g : G, ((ρ g : GL4) : M4) = A.toMat) →
      ∃ g : G, ((ρ g : GL4) : M4) =
        (w.foldl (fun A i => A.mul (gens.getD i M4c.one)) A).toMat from
    h _ ⟨1, by rw [map_one, Units.val_one, M4c.toMat_one]⟩
  induction w with
  | nil => exact fun A hA => hA
  | cons i w ih =>
    rintro A ⟨g, hgA⟩
    rw [List.foldl_cons]
    apply ih
    have hi : ∃ g : G, ((ρ g : GL4) : M4) = (gens.getD i M4c.one).toMat := by
      by_cases hil : i < gens.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
        exact hg _ (List.getElem_mem hil)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hil), Option.getD_none]
        exact ⟨1, by rw [map_one, Units.val_one, M4c.toMat_one]⟩
    obtain ⟨g', hg'⟩ := hi
    exact ⟨g * g', by rw [map_mul, Units.val_mul, M4c.toMat_mul, hgA, hg']⟩

theorem transitive_of_sylow (hρ : Function.Injective ρ)
    (S : Sylow 2 G) (hS : ∀ y : M4, (∃ x ∈ S, ((ρ x : GL4) : M4) = y) ↔ y ∈ listSet e0c)
    (hn : ∃ h : G, ∃ x ∈ S, h * x * h⁻¹ ∉ S) {v : Fin 4 → ZMod 2} (hv : v ≠ 0) :
    ∃ g : G, ((ρ g : GL4) : M4) *ᵥ V4c.v0.toVec = v := by
  have hinj : ∀ x y : G, ((ρ x : GL4) : M4) = ((ρ y : GL4) : M4) → x = y :=
    fun x y h => hρ (Units.ext h)
  have hmul : ∀ x y : G, ((ρ (x * y) : GL4) : M4) = ((ρ x : GL4) : M4) * ((ρ y : GL4) : M4) :=
    fun x y => by rw [map_mul, Units.val_mul]
  have hone : ((ρ 1 : GL4) : M4) = 1 := by rw [map_one, Units.val_one]
  have hE : ∀ e ∈ e0c, ∃ x ∈ S, ((ρ x : GL4) : M4) = e.toMat := fun e he =>
    (hS _).mpr ⟨e, he, rfl⟩
  have hSmat : ∀ x ∈ S, ∃ e ∈ e0c, e.toMat = ((ρ x : GL4) : M4) := fun x hx =>
    (hS _).mp ⟨x, hx, rfl⟩
  have hSsq : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨e, he, hex⟩ := hSmat x hx
    exact hinj _ _ (by rw [hmul, ← hex, ← M4c.toMat_mul, e0_mul_self e he, M4c.toMat_one, hone])
  obtain ⟨h, x, hxS, hx⟩ := hn
  have hdet : ((ρ h⁻¹ : GL4) : M4).det ≠ 0 := (Matrix.isUnits_det_units (ρ h⁻¹)).ne_zero
  obtain ⟨k, hk, hkset⟩ := exists_conjSet_eq hdet 0 (by norm_num)
  have hAinv : ((ρ h⁻¹ : GL4) : M4)⁻¹ = ((ρ h : GL4) : M4) := by
    rw [← Matrix.coe_units_inv, ← map_inv, inv_inv]
  have hconj : ∀ y : G, ((ρ (h * y * h⁻¹) : GL4) : M4) =
      ((ρ h⁻¹ : GL4) : M4)⁻¹ * ((ρ y : GL4) : M4) * ((ρ h⁻¹ : GL4) : M4) := fun y => by
    rw [hAinv, hmul, hmul]
  have hCH : ∀ c ∈ conjAt k, ∃ g : G, ((ρ g : GL4) : M4) = c.toMat := by
    intro c hc
    have hcs : c.toMat ∈ conjSet ((ρ h⁻¹ : GL4) : M4) (conjAt 0) := by
      rw [hkset]
      exact ⟨c, hc, rfl⟩
    obtain ⟨e, he, hec⟩ := hcs
    obtain ⟨s, -, hse⟩ := hE e he
    exact ⟨h * s * h⁻¹, by rw [hconj, hse, hec]⟩
  have hgens : ∀ c ∈ e0c ++ conjAt k, ∃ g : G, ((ρ g : GL4) : M4) = c.toMat := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨s, -, hs⟩ := hE c hc
      exact ⟨s, hs⟩
    · exact hCH c hc
  obtain ⟨c₀, hc₀, hc₀x⟩ : ((ρ (h * x * h⁻¹) : GL4) : M4) ∈ listSet (conjAt k) := by
    rw [← hkset]
    obtain ⟨e, he, hex⟩ := hSmat x hxS
    exact ⟨e, he, by rw [hconj, hex]⟩
  have hc₀e : c₀ ∉ e0c := fun he => by
    obtain ⟨s, hs, hse⟩ := hE c₀ he
    exact hx (hinj _ _ (hse.trans hc₀x) ▸ hs)
  have hw := conjAt_wit hk
  cases hwk : witAt k with
  | norm =>
    rw [hwk] at hw
    exact absurd (hw.1 c₀ hc₀) hc₀e
  | word w =>
    rw [hwk] at hw
    obtain ⟨h4, h2⟩ := hw
    obtain ⟨g, hg⟩ := exists_wordProd ρ hgens w
    have hg4 : g ^ 4 = 1 := hinj _ _ (by
      rw [show g ^ 4 = g * g * (g * g) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
        hmul, hmul, hg, ← M4c.toMat_mul,
        ← M4c.toMat_mul, h4, M4c.toMat_one, hone])
    exact absurd (M4c.toMat_injective (by
      rw [M4c.toMat_mul, ← hg, ← hmul, mul_self_eq_one_of_pow_four S hSsq hg4, hone,
        M4c.toMat_one])) h2
  | comm n =>
    rw [hwk] at hw
    obtain ⟨hnC, hne, hsq, hcomm⟩ := hw
    obtain ⟨g, hg⟩ := hCH _ hnC
    have hg2 : g * g = 1 :=
      hinj _ _ (by rw [hmul, hg, ← M4c.toMat_mul, hsq, M4c.toMat_one, hone])
    have hgc : ∀ s ∈ S, s * g = g * s := by
      intro s hs
      obtain ⟨e, he, hes⟩ := hSmat s hs
      exact hinj _ _ (by rw [hmul, hmul, ← hes, hg, ← M4c.toMat_mul, ← M4c.toMat_mul,
        hcomm e he])
    obtain ⟨e, he, heg⟩ := hSmat g (mem_of_comm S hg2 hgc)
    exact (hne (M4c.toMat_injective (heg.trans hg) ▸ he)).elim
  | orbit ws =>
    rw [hwk] at hw
    obtain ⟨hall, hws⟩ := hw
    rcases hall (V4c.ofVec v) (V4c.mem_all _) with h0 | ⟨p, hp, hpv⟩
    · exact absurd (by rw [← V4c.toVec_ofVec v, h0, V4c.toVec_zero]) hv
    · obtain ⟨g, hg⟩ := exists_wordProd ρ hgens p.2
      exact ⟨g, by rw [hg, ← M4c.toVec_mulVec, hws p hp, hpv, V4c.toVec_ofVec]⟩

end Transitive

end CFSG.ComponentClassification.GHarris.GL42
