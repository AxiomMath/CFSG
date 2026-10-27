module

import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem card_map_eq_of_ker {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (hf : ∀ x ∈ K, f x = 1 → x = 1) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have hr : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem mem_centralizer_of_mk_mem {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1 → z = 1) {a : G} (ha : a ^ 3 = 1)
    {g : G}
    (hg : QuotientGroup.mk' Z g ∈ Subgroup.centralizer ({QuotientGroup.mk' Z a} : Set (G ⧸ Z))) :
    g ∈ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq] at hg
  set w := (g * a)⁻¹ * (a * g) with hwdef
  have hwc : ∀ x, x * w = w * x := Subgroup.mem_center_iff.1 (hZ hg)
  have e1 : g⁻¹ * a * g = a * w := by rw [hwdef]; group
  have e2 : (g⁻¹ * a * g) ^ 3 = 1 := by
    have : g⁻¹ * a * g = g⁻¹ * a * g⁻¹⁻¹ := by rw [inv_inv]
    rw [this, conj_pow, ha, mul_one, inv_inv, inv_mul_cancel]
  rw [e1, Commute.mul_pow (hwc a) 3, ha, one_mul] at e2
  have hw1 : w = 1 := hZ3 w hg e2
  rw [hw1, mul_one] at e1
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  calc g * a = g * (g⁻¹ * a * g) := by rw [e1]
    _ = a * g := by group

theorem centralizer_mk_eq {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1 → z = 1) {a : G} (ha : a ^ 3 = 1) :
    Subgroup.centralizer ({QuotientGroup.mk' Z a} : Set (G ⧸ Z)) =
      (Subgroup.centralizer ({a} : Set G)).map (QuotientGroup.mk' Z) := by
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
  constructor
  · intro hg
    exact ⟨g, mem_centralizer_of_mk_mem Z hZ hZ3 ha hg, rfl⟩
  · rintro ⟨h, hh, he⟩
    rw [← he, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 hh]

theorem mem_centralizer_of_centMod {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJ3 : 3 ∣ Nat.card ↥J) {x : G} (hx : CentMod 3 J x) :
    x ∈ Subgroup.centralizer (J : Set G) := by
  have h := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf
    Nat.prime_three hJq hJ3 (MulAut.conj x).toMonoidHom fun j hj => by
      have hc : ⁅j, x⁆ ∈ GLAPPrimeCoreOf 3 J :=
        hx.2 (Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers x))
      have e : (MulAut.conj x).toMonoidHom j * j⁻¹ = ⁅j, x⁆⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact (GLAPPrimeCoreOf 3 J).inv_mem hc
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have := h j hj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  calc j * x = x * j * x⁻¹ * x := by rw [this]
    _ = x * j := by group

section C3

variable {F : Type} [Field F]

@[expose] def c3Mat : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, -1]

theorem det_c3Mat : (c3Mat : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [c3Mat, Matrix.det_fin_two]

@[expose] def c3 : SpecialLinearGroup (Fin 2) F := ⟨c3Mat, det_c3Mat⟩

theorem coe_c3 : ((c3 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = c3Mat := rfl

theorem c3Mat_pow_three : (c3Mat : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c3Mat, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem c3_pow_three : (c3 : SpecialLinearGroup (Fin 2) F) ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_c3, c3Mat_pow_three,
    Matrix.SpecialLinearGroup.coe_one]

theorem c3_ne_one : (c3 : SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [coe_c3, c3Mat] at this

theorem eq_zero_of_c3Mat_mul {ι : Type*} (h3 : (3 : F) ≠ 0) {Q : Matrix (Fin 2) ι F}
    (hQ : c3Mat * Q = Q) : Q = 0 := by
  have h0 : ∀ j, ((c3Mat : Matrix (Fin 2) (Fin 2) F) * Q) 0 j = -Q 1 j := fun j => by
    simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ∀ j, ((c3Mat : Matrix (Fin 2) (Fin 2) F) * Q) 1 j = Q 0 j - Q 1 j := fun j => by
    simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  have hQ1 : ∀ j, Q 1 j = 0 := fun j => by
    have a : -Q 1 j = Q 0 j := (h0 j).symm.trans (congrFun (congrFun hQ 0) j)
    have b : Q 0 j - Q 1 j = Q 1 j := (h1 j).symm.trans (congrFun (congrFun hQ 1) j)
    have : (3 : F) * Q 1 j = 0 := by linear_combination -b - a
    exact (mul_eq_zero.1 this).resolve_left h3
  ext i j
  fin_cases i
  · have a : -Q 1 j = Q 0 j := (h0 j).symm.trans (congrFun (congrFun hQ 0) j)
    rw [hQ1 j, neg_zero] at a
    simpa using a.symm
  · simpa using hQ1 j

theorem eq_zero_of_mul_c3Mat {ι : Type*} (h3 : (3 : F) ≠ 0) {R : Matrix ι (Fin 2) F}
    (hR : R * c3Mat = R) : R = 0 := by
  have h0 : ∀ i, (R * (c3Mat : Matrix (Fin 2) (Fin 2) F)) i 0 = R i 1 := fun i => by
    simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ∀ i, (R * (c3Mat : Matrix (Fin 2) (Fin 2) F)) i 1 = -R i 0 - R i 1 := fun i => by
    simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  have hR0 : ∀ i, R i 0 = 0 := fun i => by
    have a : R i 1 = R i 0 := (h0 i).symm.trans (congrFun (congrFun hR i) 0)
    have b : -R i 0 - R i 1 = R i 1 := (h1 i).symm.trans (congrFun (congrFun hR i) 1)
    have : (3 : F) * R i 0 = 0 := by linear_combination -b - 2 * a
    exact (mul_eq_zero.1 this).resolve_left h3
  ext i j
  fin_cases j
  · simpa using hR0 i
  · have a : R i 1 = R i 0 := (h0 i).symm.trans (congrFun (congrFun hR i) 0)
    rw [hR0 i] at a
    simpa using a

end C3

section Blk

variable {F : Type} [Field F] (ι : Type) [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def blk :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup ι F →* SpecialLinearGroup (Fin 2 ⊕ ι) F where
  toFun p := ⟨fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) F) 0 0 (p.2 : Matrix ι ι F), by
    rw [det_fromBlocks_zero₂₁, p.1.2, p.2.2, one_mul]⟩
  map_one' := by
    apply Subtype.ext
    simp [fromBlocks_one]
  map_mul' p q := by
    apply Subtype.ext
    change fromBlocks ((p.1 * q.1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      0 0 ((p.2 * q.2 : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F) =
      fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) F) 0 0 (p.2 : Matrix ι ι F) *
        fromBlocks (q.1 : Matrix (Fin 2) (Fin 2) F) 0 0 (q.2 : Matrix ι ι F)
    simp [fromBlocks_multiply]

variable {ι}

theorem coe_blk (p : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup ι F) :
    ((blk ι p : SpecialLinearGroup (Fin 2 ⊕ ι) F) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F) =
      fromBlocks (p.1 : Matrix (Fin 2) (Fin 2) F) 0 0 (p.2 : Matrix ι ι F) :=
  rfl

theorem blk_injective : Function.Injective (blk ι (F := F)) := by
  rintro ⟨P, Y⟩ ⟨P', Y'⟩ h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2 ⊕ ι) F =>
    (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)) h
  simp only [coe_blk] at this
  obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 this
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h4)

theorem toBlocks_eq_zero_of_commute (h3 : (3 : F) ≠ 0) {g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F}
    (hg : g * fromBlocks c3Mat 0 0 1 = fromBlocks c3Mat 0 0 1 * g) :
    g.toBlocks₁₂ = 0 ∧ g.toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks g, fromBlocks_multiply, fromBlocks_multiply] at hg
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at hg
  obtain ⟨-, h2, h3', -⟩ := Matrix.fromBlocks_inj.1 hg
  exact ⟨eq_zero_of_c3Mat_mul h3 h2.symm, eq_zero_of_mul_c3Mat h3 h3'⟩

@[expose] noncomputable def blkRange : Subgroup (SpecialLinearGroup (Fin 2 ⊕ ι) F) :=
  ((blk ι).comp (MonoidHom.inr _ _)).range

theorem mem_blkRange_iff {g : SpecialLinearGroup (Fin 2 ⊕ ι) F} :
    g ∈ blkRange (F := F) (ι := ι) ↔
      (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F).toBlocks₁₁ = 1 ∧
        (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F).toBlocks₁₂ = 0 ∧
        (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F).toBlocks₂₁ = 0 := by
  constructor
  · rintro ⟨Y, rfl⟩
    simp [blkRange, coe_blk]
  · rintro ⟨h1, h2, h3⟩
    have hdet : (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F).toBlocks₂₂.det = 1 := by
      have := g.2
      rw [← fromBlocks_toBlocks (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F), h1, h2, h3,
        det_fromBlocks_zero₂₁, det_one, one_mul] at this
      exact this
    refine ⟨⟨(g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F).toBlocks₂₂, hdet⟩, Subtype.ext ?_⟩
    change fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) 0 0
      (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F).toBlocks₂₂ = _
    rw [← h1, ← h2, ← h3, fromBlocks_toBlocks]

theorem conj_mem_blkRange (h3 : (3 : F) ≠ 0) {g y : SpecialLinearGroup (Fin 2 ⊕ ι) F}
    (hg : g * blk ι (c3, 1) = blk ι (c3, 1) * g) (hy : y ∈ blkRange (F := F) (ι := ι)) :
    g * y * g⁻¹ ∈ blkRange (F := F) (ι := ι) := by
  have hgi : g⁻¹ * blk ι (c3, 1) = blk ι (c3, 1) * g⁻¹ := by
    calc g⁻¹ * blk ι (c3, 1) = g⁻¹ * (blk ι (c3, 1) * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * blk ι (c3, 1)) * g⁻¹ := by rw [hg]
      _ = blk ι (c3, 1) * g⁻¹ := by group
  have cg := congrArg (fun x : SpecialLinearGroup (Fin 2 ⊕ ι) F =>
    (x : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)) hg
  have cgi := congrArg (fun x : SpecialLinearGroup (Fin 2 ⊕ ι) F =>
    (x : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)) hgi
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blk, coe_c3,
    Matrix.SpecialLinearGroup.coe_one] at cg cgi
  obtain ⟨g12, g21⟩ := toBlocks_eq_zero_of_commute h3 cg
  obtain ⟨i12, i21⟩ := toBlocks_eq_zero_of_commute h3 cgi
  obtain ⟨y11, y12, y21⟩ := mem_blkRange_iff.1 hy
  have hgg : (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 2 ⊕ ι) F) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  set G := (g : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)
  set Gi := ((g⁻¹ : SpecialLinearGroup (Fin 2 ⊕ ι) F) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)
  set Y := (y : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) F)
  have hG : G = fromBlocks G.toBlocks₁₁ 0 0 G.toBlocks₂₂ := by
    rw [← g12, ← g21, fromBlocks_toBlocks]
  have hGi : Gi = fromBlocks Gi.toBlocks₁₁ 0 0 Gi.toBlocks₂₂ := by
    rw [← i12, ← i21, fromBlocks_toBlocks]
  have hY : Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
    rw [← y11, ← y12, ← y21, fromBlocks_toBlocks]
  have h11 : G.toBlocks₁₁ * Gi.toBlocks₁₁ = 1 := by
    have := hgg
    rw [hG, hGi, fromBlocks_multiply] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at this
    exact (Matrix.fromBlocks_inj.1 (this.trans fromBlocks_one.symm)).1
  apply mem_blkRange_iff.2
  change (G * Y * Gi).toBlocks₁₁ = 1 ∧ (G * Y * Gi).toBlocks₁₂ = 0 ∧ (G * Y * Gi).toBlocks₂₁ = 0
  rw [hG, hY, hGi]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
  exact ⟨h11, trivial, trivial⟩

end Blk

theorem eq_one_of_mem_center_of_pow_three {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hF : ∀ x : F, x ^ 3 = 1 → x = 1) {z : SpecialLinearGroup ι F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup ι F)) (hz3 : z ^ 3 = 1) : z = 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact Subtype.ext (Subsingleton.elim _ _)
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr3 : r ^ 3 = 1 := by
    have := congrArg (fun g : SpecialLinearGroup ι F => (g : Matrix ι ι F) i i) hz3
    simp only [Matrix.SpecialLinearGroup.coe_pow, ← hr, Matrix.SpecialLinearGroup.coe_one] at this
    simpa [scalar_apply, diagonal_pow] using this
  apply Subtype.ext
  change (z : Matrix ι ι F) = 1
  rw [← hr, hF r hr3, map_one]

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
