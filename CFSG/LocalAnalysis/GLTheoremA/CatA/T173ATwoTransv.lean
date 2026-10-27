module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open Module
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL
  (fixSp comSp Nsub mem_Nsub mem_fixSp isCompl_fixSp_comSp)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private lemma exists_fin_ne_two {r : ℕ} (hr : 3 ≤ r) (a b : Fin r) :
    ∃ k : Fin r, k ≠ a ∧ k ≠ b := by
  have hcard : ({a, b} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h2 : ({a, b} : Finset (Fin r)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_singleton] at hk
  exact ⟨k, fun h => hk (Or.inl h), fun h => hk (Or.inr h)⟩

private lemma toLin_transvection_apply {R : Type*} [CommRing R] {M : Type*}
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [DecidableEq n]
    (v : Basis n R M) (i j : n) (c : R) (a : n) :
    Matrix.toLin v v (Matrix.transvection i j c) (v a) =
      v a + (if a = j then c • v i else 0) := by
  change Matrix.toLin v v ((1 : Matrix n n R) + Matrix.single i j c) (v a) =
    v a + (if a = j then c • v i else 0)
  rw [map_add, Matrix.toLin_one, LinearMap.add_apply,
    LinearMap.id_apply, Matrix.toLin_self]
  have hsingle : (∑ l, Matrix.single i j c l a • v l) =
      if a = j then c • v i else 0 := by
    rw [Finset.sum_eq_single i]
    · rw [Matrix.single_apply]
      by_cases h : a = j
      · simp [h]
      · simp [h, Ne.symm h]
    · intro l _ hl
      have hzero : Matrix.single i j c l a = 0 := by
        rw [Matrix.single_apply]
        simp [Ne.symm hl]
      rw [hzero, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsingle]

theorem lin_two_nsub_generate {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V} {V0 : Submodule (ZMod 2) V}
    (hF : LinTwoStdFrame E x P V0) (hr : 3 ≤ r) :
    ⨆ j, Nsub (hF.2.2.2.1 j) = ⊤ := by
  classical
  obtain ⟨-, hInt, hdim, hx3, hcom, hV0, hP⟩ := hF
  let S : Option (Fin r) → Submodule (ZMod 2) V := fun o => o.elim V0 P
  have hInt' : DirectSum.IsInternal S := hInt
  have hSnone : S none = V0 := rfl
  have hSsome : ∀ i, S (some i) = P i := fun _ => rfl
  let α : Option (Fin r) → Type := fun o =>
    match o with
    | none => Fin (Module.finrank (ZMod 2) V0)
    | some _ => Fin 2
  letI : ∀ o, Fintype (α o) := fun o => by cases o <;> infer_instance
  letI : ∀ o, DecidableEq (α o) := fun o => by cases o <;> infer_instance
  let v : ∀ o, Basis (α o) (ZMod 2) (S o) := fun o =>
    match o with
    | none => Module.finBasis (ZMod 2) V0
    | some i => Module.finBasisOfFinrankEq (ZMod 2) (P i) (hdim i)
  let b : Basis (Σ o, α o) (ZMod 2) V := hInt'.collectedBasis v
  have hb_coe : ⇑b = fun a : Σ o, α o => (v a.1 a.2 : V) :=
    DirectSum.IsInternal.collectedBasis_coe hInt' v
  have hspan : ∀ o : Option (Fin r),
      Submodule.span (ZMod 2) (Set.range (fun a : α o => b ⟨o, a⟩)) = S o := by
    intro o
    have hcomp : (fun a : α o => b ⟨o, a⟩) =
        (Subtype.val : S o → V) ∘ (v o) := by
      funext a
      exact congrFun hb_coe ⟨o, a⟩
    rw [hcomp, Set.range_comp]
    change Submodule.span (ZMod 2) (Submodule.subtype (S o) '' Set.range (v o)) = S o
    rw [Submodule.span_image, (v o).span_eq, Submodule.map_subtype_top]
  let H : Subgroup (V ≃ₗ[ZMod 2] V) := ⨆ j, Nsub (hx3 j)
  change H = ⊤
  let Pmat : Matrix (Σ o, α o) (Σ o, α o) (ZMod 2) → Prop := fun M =>
    ∃ h : V ≃ₗ[ZMod 2] V, h ∈ H ∧ (h : V →ₗ[ZMod 2] V) = Matrix.toLin b b M
  have htrans : ∀ t : Matrix.TransvectionStruct (Σ o, α o) (ZMod 2),
      Pmat t.toMatrix := by
    intro t
    obtain ⟨i, j, hij, c⟩ := t
    show Pmat (Matrix.transvection i j c)
    obtain ⟨k, hik, hjk⟩ : ∃ k : Fin r, i.1 ≠ some k ∧ j.1 ≠ some k := by
      cases hi : i.1 with
      | none =>
        cases hj : j.1 with
        | none => exact ⟨⟨0, by omega⟩, by simp [hi], by simp [hj]⟩
        | some c' =>
          obtain ⟨k, hk⟩ := exists_fin_ne_two hr c' c'
          exact ⟨k, by simp [hi], by simpa [hj] using (Ne.symm hk.1)⟩
      | some a =>
        cases hj : j.1 with
        | none =>
          obtain ⟨k, hk⟩ := exists_fin_ne_two hr a a
          exact ⟨k, by simpa [hi] using (Ne.symm hk.1), by simp [hj]⟩
        | some c' =>
          obtain ⟨k, hk⟩ := exists_fin_ne_two hr a c'
          exact ⟨k, by simpa [hi] using (Ne.symm hk.1),
            by simpa [hj] using (Ne.symm hk.2)⟩
    let f : Module.Dual (ZMod 2) V := b.coord j
    let w : V := c • b i
    have hfw : f w = 0 := by
      have hcoord : b.coord j (b i) = 0 := by
        by_cases h : i = j
        · exact absurd h hij
        · simp [Basis.coord_apply, h]
      simp only [f, w, map_smul, smul_eq_mul, hcoord]
      simp
    let T : V ≃ₗ[ZMod 2] V := LinearEquiv.transvection hfw
    have hT_apply : ∀ a, T (b a) = b a + b.coord j (b a) • (c • b i) := by
      intro a
      show LinearEquiv.transvection hfw (b a) =
        b a + b.coord j (b a) • (c • b i)
      rw [LinearEquiv.transvection.coe_apply, LinearMap.transvection.apply]
    have hT_j : T (b j) = b j + c • b i := by
      rw [hT_apply]
      have h1 : b.coord j (b j) = 1 := by simp [Basis.coord_apply]
      rw [h1, one_smul]
    have hT_other : ∀ a, a ≠ j → T (b a) = b a := by
      intro a ha
      rw [hT_apply]
      have h0 : b.coord j (b a) = 0 := by
        simp [Basis.coord_apply, Ne.symm ha]
      rw [h0, zero_smul, add_zero]
    let sIdx : Set (Σ o, α o) := {a | a.1 ≠ some k}
    let tIdx : Set (Σ o, α o) := {a | a.1 = some k}
    let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) (b '' sIdx)
    have hst : IsCompl sIdx tIdx := by
      constructor
      · rw [Set.disjoint_left]
        intro a ha hb
        exact ha hb
      · rw [codisjoint_iff]
        change sIdx ∪ tIdx = (Set.univ : Set (Σ o, α o))
        rw [Set.eq_univ_iff_forall]
        intro a
        by_cases h : a.1 = some k
        · exact Or.inr h
        · exact Or.inl h
    have hset : b '' tIdx =
        Set.range (fun a : α (some k) => b ⟨some k, a⟩) := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨o, a'⟩ := a
        simp only [tIdx, Set.mem_setOf_eq] at ha
        change o = some k at ha
        subst o
        exact ⟨a', rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨some k, a⟩, rfl, rfl⟩
    have hcompl := b.linearIndependent.isCompl_span_image b.span_eq hst
    have htop : W ⊔ S (some k) = ⊤ := by
      rw [← hspan (some k), ← hset]
      change Submodule.span (ZMod 2) (b '' sIdx) ⊔
        Submodule.span (ZMod 2) (b '' tIdx) = ⊤
      exact codisjoint_iff.mp hcompl.2
    have hWfix : W ≤ fixSp (x k) := by
      change Submodule.span (ZMod 2) (b '' sIdx) ≤ fixSp (x k)
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨o, a'⟩ := a
      have hb : b ⟨o, a'⟩ ∈ S o := hInt'.collectedBasis_mem v ⟨o, a'⟩
      cases o with
      | none =>
        rw [hSnone] at hb
        exact mem_fixSp.mpr (hV0 k (b ⟨none, a'⟩) hb)
      | some i =>
        have hik : i ≠ k := by
          intro h
          exact ha (by rw [h])
        rw [hSsome i] at hb
        exact mem_fixSp.mpr (hP k i (fun h => hik h.symm) (b ⟨some i, a'⟩) hb)
    have hfixk : fixSp (x k) = W := by
      apply le_antisymm
      · intro z hz
        have hzV : z ∈ W ⊔ S (some k) := by rw [htop]; trivial
        obtain ⟨z1, hz1, z2, hz2, hzeq⟩ := Submodule.mem_sup.mp hzV
        have hz1fix : z1 ∈ fixSp (x k) := hWfix hz1
        have hz2fix : z2 ∈ fixSp (x k) := by
          have hz2eq : z2 = z - z1 := by rw [← hzeq]; abel
          rw [hz2eq]
          exact Submodule.sub_mem _ hz hz1fix
        have hz2com : z2 ∈ comSp (x k) := by
          rw [hcom k, ← hSsome k]
          exact hz2
        have hbot : fixSp (x k) ⊓ comSp (x k) = ⊥ :=
          disjoint_iff.mp (isCompl_fixSp_comSp (hx3 k)).1
        have hz2bot : z2 ∈ (⊥ : Submodule (ZMod 2) V) := by
          have hmem : z2 ∈ fixSp (x k) ⊓ comSp (x k) :=
            Submodule.mem_inf.mpr ⟨hz2fix, hz2com⟩
          rwa [hbot] at hmem
        have hz2zero : z2 = 0 := by simpa using hz2bot
        rw [← hzeq, hz2zero, add_zero]
        exact hz1
      · exact hWfix
    have hfix : ∀ a ∈ comSp (x k), T a = a := by
      intro a ha
      have hagen : a ∈ Submodule.span (ZMod 2)
          (Set.range (fun a' : α (some k) => b ⟨some k, a'⟩)) := by
        rw [hspan (some k)]
        rw [hcom k, ← hSsome k] at ha
        exact ha
      have hgen : ∀ a' : α (some k), T (b ⟨some k, a'⟩) = b ⟨some k, a'⟩ := by
        intro a'
        apply hT_other
        intro h
        exact hjk (by rw [← h])
      have hle : Submodule.span (ZMod 2)
          (Set.range (fun a' : α (some k) => b ⟨some k, a'⟩)) ≤
          LinearMap.ker ((T : V →ₗ[ZMod 2] V) - LinearMap.id) := by
        rw [Submodule.span_le]
        rintro _ ⟨a', rfl⟩
        simp [hgen a']
      have hzero := hle hagen
      exact sub_eq_zero.mp (by simpa using hzero)
    have hmapW : W ≤ Submodule.comap (T : V →ₗ[ZMod 2] V) W := by
      change Submodule.span (ZMod 2) (b '' sIdx) ≤
        Submodule.comap (T : V →ₗ[ZMod 2] V) W
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      change T (b a) ∈ W
      by_cases htj : a = j
      · subst htj
        rw [hT_j]
        exact W.add_mem (Submodule.subset_span (Set.mem_image_of_mem b ha))
          (W.smul_mem c (Submodule.subset_span (Set.mem_image_of_mem b hik)))
      · rw [hT_other a htj]
        exact Submodule.subset_span (Set.mem_image_of_mem b ha)
    have hpres : ∀ z ∈ fixSp (x k), T z ∈ fixSp (x k) := by
      intro z hz
      rw [hfixk] at hz ⊢
      exact hmapW hz
    have hTmem : T ∈ H := by
      apply le_iSup (fun j => Nsub (hx3 j)) k
      exact mem_Nsub.mpr ⟨hfix, hpres⟩
    refine ⟨T, hTmem, ?_⟩
    apply b.ext
    intro a
    change T (b a) = Matrix.toLin b b (Matrix.transvection i j c) (b a)
    rw [toLin_transvection_apply, hT_apply a]
    congr 1
    by_cases h : a = j
    · simp [Basis.coord_apply, h]
    · simp [Basis.coord_apply, h]
  have hdiag : ∀ D : (Σ o, α o) → ZMod 2, Matrix.det (Matrix.diagonal D) ≠ 0 →
      Pmat (Matrix.diagonal D) := by
    intro D hD
    have hD1 : D = fun _ => 1 := by
      funext a
      have hprod : (∏ i, D i) ≠ 0 := by
        rwa [Matrix.det_diagonal] at hD
      have ha : D a ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) a (Finset.mem_univ a)
      have hval : (D a).val = 1 := by
        have h1 : (D a).val ≠ 0 := (ZMod.val_ne_zero (D a)).mpr ha
        have h2 : (D a).val < 2 := ZMod.val_lt (D a)
        omega
      exact ZMod.val_injective 2 (by simpa using hval)
    rw [hD1]
    exact ⟨1, H.one_mem, by rw [Matrix.diagonal_one, Matrix.toLin_one]; rfl⟩
  have hmul : ∀ A B : Matrix (Σ o, α o) (Σ o, α o) (ZMod 2),
      Matrix.det A ≠ 0 → Matrix.det B ≠ 0 → Pmat A → Pmat B → Pmat (A * B) := by
    intro A B _ _ hPA hPB
    obtain ⟨hA, hAH, hAeq⟩ := hPA
    obtain ⟨hB, hBH, hBeq⟩ := hPB
    refine ⟨hA * hB, H.mul_mem hAH hBH, ?_⟩
    rw [LinearEquiv.coe_toLinearMap_mul, hAeq, hBeq]
    apply LinearMap.ext
    intro x
    change (Matrix.toLin b b A) ((Matrix.toLin b b B) x) =
      Matrix.toLin b b (A * B) x
    rw [Matrix.toLin_mul_apply (v₁ := b) (v₂ := b) (v₃ := b)]
  rw [eq_top_iff]
  intro g _
  have hdet : Matrix.det (LinearMap.toMatrix b b (g : V →ₗ[ZMod 2] V)) ≠ 0 := by
    rw [LinearMap.det_toMatrix]
    exact (LinearEquiv.isUnit_det' g).ne_zero
  have hmain : Pmat (LinearMap.toMatrix b b (g : V →ₗ[ZMod 2] V)) :=
    Matrix.diagonal_transvection_induction_of_det_ne_zero
      (n := Σ o, α o) (𝕜 := ZMod 2) Pmat
      (LinearMap.toMatrix b b (g : V →ₗ[ZMod 2] V)) hdet hdiag htrans hmul
  obtain ⟨h, hhH, hheq⟩ := hmain
  rw [Matrix.toLin_toMatrix] at hheq
  have hh : h = g := LinearEquiv.toLinearMap_injective hheq
  rwa [hh] at hhH

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
