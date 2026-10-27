module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerPerfect
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n : ℕ}

section Stab

variable {p : Fin n}

theorem mat_inr_apply_of_col_inl {g : StatedSp n K}
    (hg : ∀ r, mat n K g r (Sum.inl p) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r
      (Sum.inl p)) (b : Fin n ⊕ Fin n) :
    mat n K g (Sum.inr p) b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inr p) b := by
  have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) (Sum.inl p)) b
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
    Finset.sum_eq_single (Sum.inl p)] at key
  · rw [hg, Matrix.one_apply_eq, one_mul, sgn_inl, one_mul, par_inl] at key
    rw [key, Matrix.one_apply]
    simp only [eq_comm]
  · intro c _ hc
    rw [hg, Matrix.one_apply_ne hc, zero_mul]
  · simp

theorem mat_siegDiag (p : Fin n) (c : K) :
    mat n K (siegDiag K p c) = fromBlocks 1 (single p p c) 0 1 :=
  mat_upperUnipotentSp _

theorem mat_siegDiag_one (p : Fin n) :
    mat n K (siegDiag K p 1) = 1 + single (Sum.inl p) (Sum.inr p) 1 := by
  rw [mat_siegDiag]
  ext r t
  rcases r with x | x <;> rcases t with y | y <;>
    simp [Matrix.one_apply, Matrix.single_apply, and_comm]

theorem col_row_of_commute {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : G * single (Sum.inl p) (Sum.inr p) 1 = single (Sum.inl p) (Sum.inr p) 1 * G) :
    (∀ r, G r (Sum.inl p) = if r = Sum.inl p then G (Sum.inr p) (Sum.inr p) else 0) ∧
      ∀ t, t ≠ Sum.inr p → G (Sum.inr p) t = 0 := by
  refine ⟨fun r => ?_, fun t ht => ?_⟩
  · have e := congrFun (congrFun h r) (Sum.inr p)
    rw [Matrix.mul_single_apply_same, mul_one] at e
    rw [e]
    by_cases hr : r = Sum.inl p
    · subst hr
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := hr)]
      simp [hr]
  · have e := congrFun (congrFun h (Sum.inl p)) t
    rw [Matrix.single_mul_apply_same, one_mul, Matrix.mul_single_apply_of_ne (hbj := ht)] at e
    exact e.symm

variable [CharP K 2]

theorem mem_centralizer_siegDiag_iff {g : StatedSp n K} :
    g ∈ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) ↔
      ∀ r, mat n K g r (Sum.inl p) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r
        (Sum.inl p) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (mat n K) h
    rw [map_mul, map_mul, mat_siegDiag_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, add_right_inj] at h'
    obtain ⟨hcol, hrow⟩ := col_row_of_commute h'
    set lam := mat n K g (Sum.inr p) (Sum.inr p) with hlam
    have hsq : lam * lam = 1 := by
      have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) (Sum.inl p)) (Sum.inr p)
      rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
        Finset.sum_eq_single (Sum.inl p)] at key
      · simpa [hcol] using key
      · intro c _ hc
        simp [hcol, hc]
      · simp
    have hl1 : lam = 1 := eq_one_of_mul_self_eq_one_of_charTwo hsq
    intro r
    rw [hcol, hl1, Matrix.one_apply]
  · intro hcol
    apply mat_injective
    rw [map_mul, map_mul, mat_siegDiag_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, add_right_inj]
    ext r t
    by_cases ht : t = Sum.inr p
    · subst ht
      rw [Matrix.mul_single_apply_same, mul_one, hcol]
      by_cases hr : r = Sum.inl p
      · subst hr
        rw [Matrix.single_mul_apply_same, one_mul, mat_inr_apply_of_col_inl hcol,
          Matrix.one_apply_eq, Matrix.one_apply_eq]
      · rw [Matrix.single_mul_apply_of_ne (h := hr), Matrix.one_apply_ne hr]
    · rw [Matrix.mul_single_apply_of_ne (hbj := ht)]
      by_cases hr : r = Sum.inl p
      · subst hr
        rw [Matrix.single_mul_apply_same, one_mul, mat_inr_apply_of_col_inl hcol,
          Matrix.one_apply_ne (Ne.symm ht)]
      · rw [Matrix.single_mul_apply_of_ne (h := hr)]

end Stab

section Radical

variable (K) in
@[expose] def transvRadical (p : Fin n) : Subgroup (StatedSp n K) where
  carrier := {g | (∀ r, mat n K g r (Sum.inl p) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p)) ∧
    ∀ t, t ∉ coords p → ∀ r, r ≠ Sum.inl p →
      mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t}
  one_mem' := ⟨fun r => by rw [map_one], fun t _ r _ => by rw [map_one]⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun r => ?_, fun t ht r hr => ?_⟩
    · rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single (Sum.inl p)]
      · rw [hh1, Matrix.one_apply_eq, mul_one, hg1]
      · intro u _ hu
        rw [hh1, Matrix.one_apply_ne hu, mul_zero]
      · simp
    · have htp : t ≠ Sum.inl p := fun h => ht (h ▸ inl_mem_coords p)
      rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add t (Sum.inl p) htp]
      · rw [hg1, Matrix.one_apply_ne hr, zero_mul, add_zero, hh2 t ht t htp,
          Matrix.one_apply_eq, mul_one, hg2 t ht r hr]
      · rintro u ⟨hut, hup⟩
        rw [hh2 t ht u hup, Matrix.one_apply_ne hut, mul_zero]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : mat n K g⁻¹ * mat n K g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h1 : ∀ r, mat n K g⁻¹ r (Sum.inl p) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p) := by
      intro r
      have e := congrFun (congrFun hinv r) (Sum.inl p)
      rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl p)] at e
      · rwa [hg1, Matrix.one_apply_eq, mul_one] at e
      · intro u _ hu
        rw [hg1, Matrix.one_apply_ne hu, mul_zero]
      · simp
    refine ⟨h1, fun t ht r hr => ?_⟩
    have htp : t ≠ Sum.inl p := fun h => ht (h ▸ inl_mem_coords p)
    have e := congrFun (congrFun hinv r) t
    rw [Matrix.mul_apply, Fintype.sum_eq_add t (Sum.inl p) htp] at e
    · rwa [h1, Matrix.one_apply_ne hr, zero_mul, add_zero, hg2 t ht t htp, Matrix.one_apply_eq,
        mul_one] at e
    · rintro u ⟨hut, hup⟩
      rw [hg2 t ht u hup, Matrix.one_apply_ne hut, mul_zero]

variable {p : Fin n}

theorem mem_transvRadical {g : StatedSp n K} :
    g ∈ transvRadical K p ↔ (∀ r, mat n K g r (Sum.inl p) =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p)) ∧
    ∀ t, t ∉ coords p → ∀ r, r ≠ Sum.inl p →
      mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := Iff.rfl

theorem transvRadical_le_centralizer [CharP K 2] :
    transvRadical K p ≤ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
  fun _ hg => mem_centralizer_siegDiag_iff.2 hg.1

theorem complSp_le_centralizer_siegDiag [CharP K 2] :
    complSp K p ≤ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
  fun _ hg => mem_centralizer_siegDiag_iff.2 fun r =>
    hg r (Sum.inl p) fun h => h.2 (inl_mem_coords p)

end Radical

section Compression

variable (p : Fin n)

@[expose] def compr (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.of fun r t => if r ∈ coords p ∨ t ∈ coords p then
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t else G r t

variable {p}

theorem compr_apply_of_mem (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) {r t : Fin n ⊕ Fin n}
    (h : r ∈ coords p ∨ t ∈ coords p) :
    compr p G r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
  simp [compr, h]

theorem compr_apply_of_not_mem (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    {r t : Fin n ⊕ Fin n} (hr : r ∉ coords p) (ht : t ∉ coords p) : compr p G r t = G r t := by
  simp [compr, hr, ht]

theorem compr_one : compr p (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 1 := by
  ext r t
  by_cases h : r ∈ coords p ∨ t ∈ coords p
  · rw [compr_apply_of_mem _ h]
  · push Not at h
    rw [compr_apply_of_not_mem _ h.1 h.2]

theorem compr_mul {G H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hG : ∀ r, G r (Sum.inl p) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r (Sum.inl p))
    (hH : ∀ t, H (Sum.inr p) t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inr p) t) :
    compr p (G * H) = compr p G * compr p H := by
  ext r t
  by_cases hr : r ∈ coords p
  · rw [compr_apply_of_mem _ (Or.inl hr), Matrix.mul_apply,
      Finset.sum_congr rfl fun u _ => by rw [compr_apply_of_mem G (Or.inl hr)],
      ← Matrix.mul_apply, Matrix.one_mul, compr_apply_of_mem _ (Or.inl hr)]
  by_cases ht : t ∈ coords p
  · rw [compr_apply_of_mem _ (Or.inr ht), Matrix.mul_apply,
      Finset.sum_congr rfl fun u _ => by rw [compr_apply_of_mem H (Or.inr ht)],
      ← Matrix.mul_apply, Matrix.mul_one, compr_apply_of_mem _ (Or.inr ht)]
  rw [compr_apply_of_not_mem _ hr ht, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ coords p
  · rw [compr_apply_of_mem G (Or.inr hu), Matrix.one_apply_ne (by rintro rfl; exact hr hu),
      zero_mul]
    rcases mem_coords.1 hu with rfl | rfl
    · rw [hG, Matrix.one_apply_ne (by rintro rfl; exact hr (inl_mem_coords p)), zero_mul]
    · rw [hH, Matrix.one_apply_ne (by rintro rfl; exact ht (inr_mem_coords p)), mul_zero]
  · rw [compr_apply_of_not_mem G hr hu, compr_apply_of_not_mem H hu ht]

theorem compr_symplectic {g : StatedSp n K}
    (hg : ∀ r, mat n K g r (Sum.inl p) = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r
      (Sum.inl p)) :
    (compr p (mat n K g))ᵀ * gram K n * compr p (mat n K g) = gram K n := by
  have hrow := mat_inr_apply_of_col_inl hg
  have hpar : ∀ c : Fin n ⊕ Fin n, par c ∈ coords p ↔ c ∈ coords p := by
    intro c
    rcases c with x | x <;> simp [mem_coords, par]
  ext a b
  rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
  by_cases ha : a ∈ coords p
  · rw [Finset.sum_eq_single a]
    · rw [compr_apply_of_mem _ (Or.inr ha), Matrix.one_apply_eq, one_mul,
        compr_apply_of_mem _ (Or.inl ((hpar a).2 ha)), Matrix.one_apply]
      by_cases h : b = par a
      · subst h
        simp
      · have h' : ¬ par a = b := fun h' => h h'.symm
        simp [h, h']
    · intro c _ hc
      rw [compr_apply_of_mem _ (Or.inr ha), Matrix.one_apply_ne hc, zero_mul]
    · simp
  by_cases hb : b ∈ coords p
  · rw [Finset.sum_eq_single (par b)]
    · rw [compr_apply_of_mem _ (Or.inl ((hpar b).2 hb)),
        Matrix.one_apply_ne (fun h => ha (by rw [← h]; exact (hpar b).2 hb)), zero_mul,
        ite_eq_right_iff.2]
      intro h
      exact absurd ((hpar a).1 (h ▸ hb)) ha
    · intro c _ hc
      rw [compr_apply_of_mem _ (Or.inr hb), Matrix.one_apply_ne (fun h => hc (by
        rw [← h, par_par])), mul_zero, mul_zero]
    · simp
  have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) a) b
  rw [transpose_mul_gram_mul_apply,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : c ∈ coords p
  · rw [compr_apply_of_mem _ (Or.inl hc), Matrix.one_apply_ne (by rintro rfl; exact ha hc),
      zero_mul]
    rcases mem_coords.1 hc with rfl | rfl
    · rw [par_inl, hrow, Matrix.one_apply_ne (by rintro rfl; exact hb (inr_mem_coords p)),
        mul_zero, mul_zero]
    · rw [hrow, Matrix.one_apply_ne (by rintro rfl; exact ha (inr_mem_coords p)), zero_mul]
  · rw [compr_apply_of_not_mem _ hc ha,
      compr_apply_of_not_mem _ (fun h => hc ((hpar c).1 h)) hb]

end Compression

section Decomposition

variable [CharP K 2] (p : Fin n)

variable (K) in
@[expose] noncomputable def comprHom :
    centralizer ({siegDiag K p 1} : Set (StatedSp n K)) →* StatedSp n K where
  toFun g := ofSymplecticMat (compr p (mat n K g)) (compr_symplectic
    (mem_centralizer_siegDiag_iff.1 g.2))
  map_one' := mat_injective (by
    rw [mat_ofSymplecticMat, OneMemClass.coe_one, map_one, compr_one])
  map_mul' g h := mat_injective (by
    rw [map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat, mat_ofSymplecticMat,
      Subgroup.coe_mul, map_mul]
    exact compr_mul (mem_centralizer_siegDiag_iff.1 g.2)
      (mat_inr_apply_of_col_inl (mem_centralizer_siegDiag_iff.1 h.2)))

variable {p}

theorem mat_comprHom (g : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) :
    mat n K (comprHom K p g) = compr p (mat n K g) := rfl

theorem comprHom_mem_complSp (g : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) :
    comprHom K p g ∈ complSp K p := by
  intro r t hrt
  rw [mat_comprHom, compr_apply_of_mem]
  by_contra h
  push Not at h
  exact hrt ⟨h.1, h.2⟩

theorem comprHom_of_mem_complSp {g : centralizer ({siegDiag K p 1} : Set (StatedSp n K))}
    (hg : (g : StatedSp n K) ∈ complSp K p) : comprHom K p g = g := by
  apply mat_injective
  rw [mat_comprHom]
  ext r t
  by_cases h : r ∈ coords p ∨ t ∈ coords p
  · rw [compr_apply_of_mem _ h, hg r t fun h' => by rcases h with h | h; exacts [h'.1 h, h'.2 h]]
  · push Not at h
    rw [compr_apply_of_not_mem _ h.1 h.2]

theorem mem_transvRadical_iff_comprHom_eq_one
    {g : centralizer ({siegDiag K p 1} : Set (StatedSp n K))} :
    (g : StatedSp n K) ∈ transvRadical K p ↔ comprHom K p g = 1 := by
  have hcol := mem_centralizer_siegDiag_iff.1 g.2
  have hrow := mat_inr_apply_of_col_inl hcol
  constructor
  · rintro ⟨-, h2⟩
    apply mat_injective
    rw [mat_comprHom, map_one]
    ext r t
    by_cases h : r ∈ coords p ∨ t ∈ coords p
    · rw [compr_apply_of_mem _ h]
    · push Not at h
      rw [compr_apply_of_not_mem _ h.1 h.2]
      exact h2 t h.2 r fun hr => h.1 (hr ▸ inl_mem_coords p)
  · intro h1
    refine ⟨hcol, fun t ht r hr => ?_⟩
    by_cases hrp : r ∈ coords p
    · rcases mem_coords.1 hrp with rfl | rfl
      · exact absurd rfl hr
      · exact hrow t
    · have e := congrFun (congrFun (congrArg (mat n K) h1) r) t
      rwa [mat_comprHom, map_one, compr_apply_of_not_mem _ hrp ht] at e

theorem centralizer_siegDiag_eq_sup :
    centralizer ({siegDiag K p 1} : Set (StatedSp n K)) = transvRadical K p ⊔ complSp K p := by
  refine le_antisymm (fun g hg => ?_) (sup_le transvRadical_le_centralizer
    complSp_le_centralizer_siegDiag)
  set g' : centralizer ({siegDiag K p 1} : Set (StatedSp n K)) := ⟨g, hg⟩
  set m := comprHom K p g' with hm
  have hmC : m ∈ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
    complSp_le_centralizer_siegDiag (comprHom_mem_complSp g')
  set m' : centralizer ({siegDiag K p 1} : Set (StatedSp n K)) := ⟨m, hmC⟩
  have hm' : comprHom K p m' = m := comprHom_of_mem_complSp (comprHom_mem_complSp g')
  have hq : ((g' * m'⁻¹ : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) :
      StatedSp n K) ∈ transvRadical K p := by
    rw [mem_transvRadical_iff_comprHom_eq_one, map_mul, map_inv, hm', ← hm, mul_inv_cancel]
  have e : g = ((g' * m'⁻¹ : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) :
      StatedSp n K) * m := by
    simp [g', m']
  rw [e]
  exact Subgroup.mul_mem _ (mem_sup_left hq) (mem_sup_right (comprHom_mem_complSp g'))

theorem disjoint_transvRadical_complSp : Disjoint (transvRadical K p) (complSp K p) := by
  rw [Subgroup.disjoint_def]
  intro g hq hm
  set g' : centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
    ⟨g, transvRadical_le_centralizer hq⟩
  have h1 := (mem_transvRadical_iff_comprHom_eq_one (g := g')).1 hq
  rw [comprHom_of_mem_complSp (g := g') hm] at h1
  exact h1

theorem complSp_le_normalizer_transvRadical :
    complSp K p ≤ normalizer (transvRadical K p : Set (StatedSp n K)) := by
  intro m hm
  rw [mem_normalizer_iff]
  have key : ∀ (c : StatedSp n K) (hc : c ∈ centralizer ({siegDiag K p 1} : Set (StatedSp n K)))
      {x : StatedSp n K}, x ∈ transvRadical K p → c * x * c⁻¹ ∈ transvRadical K p := by
    intro c hc x hx
    set c' : centralizer ({siegDiag K p 1} : Set (StatedSp n K)) := ⟨c, hc⟩
    set x' : centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
      ⟨x, transvRadical_le_centralizer hx⟩
    have h := (mem_transvRadical_iff_comprHom_eq_one (g := x')).1 hx
    have : ((c' * x' * c'⁻¹ : centralizer ({siegDiag K p 1} : Set (StatedSp n K))) :
        StatedSp n K) ∈ transvRadical K p := by
      rw [mem_transvRadical_iff_comprHom_eq_one, map_mul, map_mul, h, mul_one, map_inv,
        mul_inv_cancel]
    simpa [c', x'] using this
  have hmC := complSp_le_centralizer_siegDiag hm
  intro x
  refine ⟨key m hmC, fun hx => ?_⟩
  have := key m⁻¹ (Subgroup.inv_mem _ hmC) hx
  simpa [mul_assoc] using this

end Decomposition

section RootElements

variable {p j : Fin n}

theorem mat_leviTv {i k : Fin n} (hik : i ≠ k) (c : K) :
    mat n K (leviTv K hik c) = fromBlocks (transvection i k c) 0 0
      (((TauCeti.transvectionUnit hik c)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  rw [leviTv, mat_leviEmbedGL, TauCeti.coe_transvectionUnit]

theorem coe_transvectionUnit_inv_transpose {i k : Fin n} (hik : i ≠ k) (c : K) :
    (((TauCeti.transvectionUnit hik c)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      1 + single k i (-c) := by
  rw [TauCeti.transvectionUnit_inv, TauCeti.coe_transvectionUnit, transvection, transpose_add,
    transpose_one, transpose_single]

theorem mat_siegPair (i j : Fin n) (c : K) :
    mat n K (siegPair K i j c) = fromBlocks 1 (single i j c + single j i c) 0 1 :=
  mat_upperUnipotentSp _

variable (hpj : p ≠ j)
include hpj

theorem leviTv_mem_transvRadical (c : K) : leviTv K hpj c ∈ transvRadical K p := by
  refine ⟨fun r => ?_, fun t ht r hr => ?_⟩
  · rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
    rcases r with x | x
    · simp [transvection, Matrix.one_apply, hpj.symm]
    · simp
  · rw [mat_leviTv, coe_transvectionUnit_inv_transpose]
    rcases t with y | y <;> rcases r with x | x
    · have hy : y ≠ p := fun h => ht (h ▸ inl_mem_coords p)
      have hx : x ≠ p := fun h => hr (h ▸ rfl)
      simp [transvection, Matrix.one_apply, Ne.symm hx]
    · simp
    · simp
    · have hy : y ≠ p := fun h => ht (h ▸ inr_mem_coords p)
      simp [Matrix.one_apply, Ne.symm hy]

omit hpj in
theorem siegPair_mem_transvRadical (c : K) : siegPair K p j c ∈ transvRadical K p := by
  refine ⟨fun r => ?_, fun t ht r hr => ?_⟩
  · rw [mat_siegPair]
    rcases r with x | x <;> simp [Matrix.one_apply]
  · rw [mat_siegPair]
    rcases t with y | y <;> rcases r with x | x
    · simp [Matrix.one_apply]
    · simp
    · have hy : y ≠ p := fun h => ht (h ▸ inr_mem_coords p)
      have hx : x ≠ p := fun h => hr (h ▸ rfl)
      simp [Ne.symm hx, Ne.symm hy]
    · simp [Matrix.one_apply]

theorem mat_leviTv_mul_apply (c : K) (q : StatedSp n K) (t : Fin n ⊕ Fin n) :
    mat n K (leviTv K hpj c * q) (Sum.inl p) t =
      mat n K q (Sum.inl p) t + c * mat n K q (Sum.inl j) t := by
  rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add (Sum.inl p) (Sum.inl j)
    (fun h => hpj (Sum.inl_injective h))]
  · rw [mat_leviTv]
    simp [transvection, hpj, hpj.symm]
  · rintro u ⟨hu1, hu2⟩
    rw [mat_leviTv]
    rcases u with x | x
    · have hx1 : p ≠ x := fun h => hu1 (h ▸ rfl)
      have hx2 : j ≠ x := fun h => hu2 (h ▸ rfl)
      simp [transvection, hx1, hx2]
    · simp

theorem mat_siegPair_mul_apply (c : K) (q : StatedSp n K) (t : Fin n ⊕ Fin n) :
    mat n K (siegPair K p j c * q) (Sum.inl p) t =
      mat n K q (Sum.inl p) t + c * mat n K q (Sum.inr j) t := by
  rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add (Sum.inl p) (Sum.inr j) Sum.inl_ne_inr]
  · rw [mat_siegPair]
    simp [hpj.symm]
  · rintro u ⟨hu1, hu2⟩
    rw [mat_siegPair]
    rcases u with x | x
    · have hx1 : p ≠ x := fun h => hu1 (h ▸ rfl)
      simp [hx1]
    · have hx2 : j ≠ x := fun h => hu2 (h ▸ rfl)
      simp [hx2, hpj.symm]

end RootElements

section Generation

variable {p : Fin n}

theorem mat_apply_of_mem_transvRadical {q : StatedSp n K} (hq : q ∈ transvRadical K p)
    (hv : ∀ t, t ∉ coords p → mat n K q (Sum.inl p) t = 0) {t : Fin n ⊕ Fin n}
    (ht : t ∉ coords p) (r : Fin n ⊕ Fin n) :
    mat n K q r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t := by
  by_cases hr : r = Sum.inl p
  · subst hr
    rw [hv t ht, Matrix.one_apply_ne (by rintro rfl; exact ht (inl_mem_coords p))]
  · exact hq.2 t ht r hr

theorem eq_siegDiag_of_mem_transvRadical {q : StatedSp n K} (hq : q ∈ transvRadical K p)
    (hv : ∀ t, t ∉ coords p → mat n K q (Sum.inl p) t = 0) :
    q = siegDiag K p (mat n K q (Sum.inl p) (Sum.inr p)) := by
  have hcol : ∀ {t : Fin n ⊕ Fin n}, t ∉ coords p → ∀ r, mat n K q r t =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t :=
    fun ht r => mat_apply_of_mem_transvRadical hq hv ht r
  have hrow := mat_inr_apply_of_col_inl hq.1
  have hpar : ∀ c : Fin n ⊕ Fin n, par c ∈ coords p ↔ c ∈ coords p := by
    intro c
    rcases c with x | x <;> simp [mem_coords, par]
  apply mat_injective
  ext r t
  rw [mat_siegDiag]
  by_cases ht : t ∈ coords p
  · rcases mem_coords.1 ht with rfl | rfl
    · rw [hq.1]
      rcases r with x | x <;> simp [Matrix.one_apply]
    · by_cases hr : r ∈ coords p
      · rcases mem_coords.1 hr with rfl | rfl
        · simp
        · rw [hrow]
          simp
      ·
        have key := congrFun (congrFun (mat_transpose_mul_gram_mul q) (par r)) (Sum.inr p)
        rw [transpose_mul_gram_mul_apply,
          CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, par_par,
          ite_eq_right_iff.2 (fun (h : Sum.inr p = r) => absurd (h ▸ inr_mem_coords p) hr),
          Finset.sum_eq_single (par r)] at key
        · rw [hcol (fun h => hr ((hpar r).1 h)), Matrix.one_apply_eq, one_mul, par_par] at key
          have h0 := (mul_eq_zero.1 key).resolve_left (sgn_ne_zero _)
          rw [h0]
          rcases r with x | x
          · have hx : x ≠ p := fun h => hr (h ▸ inl_mem_coords p)
            simp [Ne.symm hx]
          · have hx : x ≠ p := fun h => hr (h ▸ inr_mem_coords p)
            simp [hx]
        · intro c _ hc
          rw [hcol (fun h => hr ((hpar r).1 h)), Matrix.one_apply_ne hc, zero_mul]
        · simp
  · rw [hcol ht]
    rcases r with x | x <;> rcases t with y | y
    · simp [Matrix.one_apply]
    · have hy : y ≠ p := fun h => ht (h ▸ inr_mem_coords p)
      simp [Ne.symm hy]
    · simp
    · simp [Matrix.one_apply]

theorem transvRadical_le_of_forall_mem {H : Subgroup (StatedSp n K)}
    (hD : ∀ c : K, siegDiag K p c ∈ H)
    (hL : ∀ (j : Fin n) (hpj : p ≠ j) (c : K), leviTv K hpj c ∈ H)
    (hS : ∀ (j : Fin n), p ≠ j → ∀ c : K, siegPair K p j c ∈ H) :
    transvRadical K p ≤ H := by
  classical
  have key : ∀ T : Finset (Fin n ⊕ Fin n), ∀ q ∈ transvRadical K p,
      (∀ t, t ∉ coords p → t ∉ T → mat n K q (Sum.inl p) t = 0) → q ∈ H := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro q hq hv
      rw [eq_siegDiag_of_mem_transvRadical hq fun t ht => hv t ht (Finset.notMem_empty t)]
      exact hD _
    | insert t T htT ih =>
      intro q hq hv
      by_cases htp : t ∈ coords p
      · refine ih q hq fun t' ht' hT => hv t' ht' ?_
        rw [Finset.mem_insert, not_or]
        exact ⟨fun h => ht' (h ▸ htp), hT⟩
      set c := mat n K q (Sum.inl p) t
      have hrow' : ∀ (u : Fin n ⊕ Fin n), u ≠ Sum.inl p → ∀ t', t' ∉ coords p →
          mat n K q u t' = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) u t' :=
        fun u hu t' ht' => hq.2 t' ht' u hu
      rcases t with j | j
      · have hpj : p ≠ j := fun h => htp (h ▸ inl_mem_coords p)
        have hq' : leviTv K hpj (-c) * q ∈ transvRadical K p :=
          Subgroup.mul_mem _ (leviTv_mem_transvRadical hpj _) hq
        have hmem := ih _ hq' fun t' ht' hT => by
          rw [mat_leviTv_mul_apply hpj, hrow' _ (fun h => hpj (Sum.inl_injective h).symm) t' ht']
          by_cases h : t' = Sum.inl j
          · subst h
            simp [c]
          · rw [hv t' ht' (by rw [Finset.mem_insert, not_or]; exact ⟨h, hT⟩),
              Matrix.one_apply_ne (Ne.symm h), mul_zero, add_zero]
        have e : q = (leviTv K hpj (-c))⁻¹ * (leviTv K hpj (-c) * q) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL j hpj _)) hmem
      · have hpj : p ≠ j := fun h => htp (h ▸ inr_mem_coords p)
        have hq' : siegPair K p j (-c) * q ∈ transvRadical K p :=
          Subgroup.mul_mem _ (siegPair_mem_transvRadical _) hq
        have hmem := ih _ hq' fun t' ht' hT => by
          rw [mat_siegPair_mul_apply hpj, hrow' _ Sum.inr_ne_inl t' ht']
          by_cases h : t' = Sum.inr j
          · subst h
            simp [c]
          · rw [hv t' ht' (by rw [Finset.mem_insert, not_or]; exact ⟨h, hT⟩),
              Matrix.one_apply_ne (Ne.symm h), mul_zero, add_zero]
        have e : q = (siegPair K p j (-c))⁻¹ * (siegPair K p j (-c) * q) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS j hpj _)) hmem
  exact fun q hq => key Finset.univ q hq fun t _ h => absurd (Finset.mem_univ t) h

end Generation

section TwoGroup

variable {p : Fin n}

theorem siegDiag_mul (p : Fin n) (a b : K) :
    siegDiag K p a * siegDiag K p b = siegDiag K p (a + b) := by
  rw [siegDiag, siegDiag, upperUnipotentSp_mul]
  exact upperUnipotentSp_congr _ _ (single_add _ _ _ _).symm

theorem siegDiag_zero (p : Fin n) : siegDiag K p 0 = 1 := by
  rw [siegDiag, ← upperUnipotentSp_zero (m := n) (K := K)]
  exact upperUnipotentSp_congr _ _ (single_zero _ _)

theorem mul_self_eq_siegDiag [CharP K 2] {q : StatedSp n K} (hq : q ∈ transvRadical K p) :
    q * q = siegDiag K p (mat n K (q * q) (Sum.inl p) (Sum.inr p)) := by
  refine eq_siegDiag_of_mem_transvRadical (Subgroup.mul_mem _ hq hq) fun t ht => ?_
  have htp : t ≠ Sum.inl p := fun h => ht (h ▸ inl_mem_coords p)
  rw [map_mul, Matrix.mul_apply, Fintype.sum_eq_add t (Sum.inl p) htp]
  · rw [hq.2 t ht t htp, Matrix.one_apply_eq, mul_one, hq.1, Matrix.one_apply_eq, one_mul,
      CharTwo.add_self_eq_zero]
  · rintro u ⟨hut, hup⟩
    rw [hq.2 t ht u hup, Matrix.one_apply_ne hut, mul_zero]

theorem isPGroup_transvRadical [CharP K 2] : IsPGroup 2 (transvRadical K p) := by
  intro q
  refine ⟨2, Subtype.ext ?_⟩
  have h := mul_self_eq_siegDiag q.2
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add,
    pow_two, h, siegDiag_mul, CharTwo.add_self_eq_zero, siegDiag_zero]

end TwoGroup

section Perfect

variable {m : ℕ}

omit [Field K] in
theorem exists_finset_card_four [Finite K] (hK : 4 ≤ Nat.card K) : ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
  exact ⟨s, hs⟩

theorem commutator_complSp [Finite K] (hK : 4 ≤ Nat.card K) (p : Fin (m + 1)) :
    ⁅complSp K p, complSp K p⁆ = complSp K p := by
  have : Group.IsPerfect (StatedSp m K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp m K (Or.inl (exists_finset_card_four hK))
  rw [complSp_eq_range_spEmbed, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]

theorem longRootSp2_le_complSp {n : ℕ} {p j : Fin n} (hpj : p ≠ j) :
    longRootSp2 K n j ≤ complSp K p := by
  rw [longRootSp2_eq_suppGroup]
  intro g hg r t hrt
  refine hg r t fun h => hrt ⟨fun hr => ?_, fun ht => ?_⟩
  · rcases mem_coords.1 h.1 with rfl | rfl <;> rcases mem_coords.1 hr with h' | h' <;>
      simp_all
  · rcases mem_coords.1 h.2 with rfl | rfl <;> rcases mem_coords.1 ht with h' | h' <;>
      simp_all

theorem upperUnipotentSp_mem_centralizer_siegDiag {n : ℕ} (p : Fin n)
    {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C) :
    upperUnipotentSp n K hC ∈ centralizer ({siegDiag K p 1} : Set (StatedSp n K)) :=
  mem_centralizer_singleton_iff.2 (upperUnipotentSp_commute _ _)

variable [CharP K 2]

theorem commutator_centralizer_siegDiag [Finite K] (hK : 4 ≤ Nat.card K) {p : Fin (m + 1)}
    (hm : 1 ≤ m) :
    ⁅centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)),
      centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K))⁆ =
      centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) := by
  set C := centralizer ({siegDiag K p 1} : Set (StatedSp (m + 1) K)) with hC
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK
  have hκ1 : (κ : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hκ (Units.ext h)
  have hκ2 : ((κ⁻¹ : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hκ (inv_eq_one.1 (Units.ext h))
  have hMC : complSp K p ≤ C := complSp_le_centralizer_siegDiag
  have hM : complSp K p ≤ ⁅C, C⁆ := by
    rw [← commutator_complSp hK p]
    exact commutator_mono hMC hMC
  have hh : ∀ j : Fin (m + 1), p ≠ j → rootTorusHom K (m + 1) j κ ∈ C := fun j hpj =>
    hMC (longRootSp2_le_complSp hpj (rootTorusSp_le_longRootSp2 j ⟨κ, rfl⟩))
  have hS : ∀ j : Fin (m + 1), p ≠ j → ∀ c : K, siegPair K p j c ∈ ⁅C, C⁆ := by
    intro j hpj c
    have e := commutatorElement_rootTorusHom_siegPair (k := j) hpj κ (((κ : K) - 1)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hκ1, one_mul] at e
    rw [siegPair_comm, ← e]
    exact commutator_mem_commutator (hh j hpj) (upperUnipotentSp_mem_centralizer_siegDiag p _)
  have hL : ∀ (j : Fin (m + 1)) (hpj : p ≠ j) (c : K), leviTv K hpj c ∈ ⁅C, C⁆ := by
    intro j hpj c
    have e := commutatorElement_rootTorusHom_leviTv (k := j) hpj κ
      ((((κ⁻¹ : Kˣ) : K) - 1)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hκ2, one_mul] at e
    rw [← e]
    exact commutator_mem_commutator (hh j hpj)
      (transvRadical_le_centralizer (leviTv_mem_transvRadical hpj _))
  obtain ⟨j, hpj⟩ : ∃ j : Fin (m + 1), p ≠ j := by
    by_cases h0 : p = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      rw [h0] at h
      exact absurd (congrArg Fin.val h) (by simp)
    · exact ⟨0, h0⟩
  have hD : ∀ c : K, siegDiag K p c ∈ ⁅C, C⁆ := by
    intro c
    have e := commutatorElement_leviTv_siegDiag hpj 1 c
    rw [one_mul, one_mul, one_mul] at e
    have h1 : ⁅leviTv K hpj 1, siegDiag K j c⁆ ∈ ⁅C, C⁆ :=
      commutator_mem_commutator (transvRadical_le_centralizer (leviTv_mem_transvRadical hpj 1))
        (hMC (longRootSp2_le_complSp hpj (siegDiag_mem_longRootSp2 j c)))
    rw [e] at h1
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS j hpj c)) h1
    rwa [inv_mul_cancel_left] at h2
  have hQ : transvRadical K p ≤ ⁅C, C⁆ := transvRadical_le_of_forall_mem hD hL hS
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  calc C = transvRadical K p ⊔ complSp K p := centralizer_siegDiag_eq_sup
    _ ≤ ⁅C, C⁆ := sup_le hQ hM

end Perfect

section OTwo

variable {m : ℕ} [Finite K] [CharP K 2]

omit [Finite K] in
theorem isSimpleGroup_statedSp (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m) :
    IsSimpleGroup (StatedSp m K) := by
  have : NeZero m := ⟨by omega⟩
  have : IsSimpleGroup (StatedProj (StatedSp m K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m hm (Or.inl (Or.inr hK))
  exact (MulEquiv.ofBijective _
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    ).isSimpleGroup_congr.2 this

theorem eq_bot_of_normal_of_isPGroup_complSp (hK : 4 ≤ Nat.card K) (hm : 1 ≤ m)
    {p : Fin (m + 1)} (N : Subgroup (complSp K p)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have : IsSimpleGroup (complSp K p) :=
    (complSpEquiv (K := K) p).isSimpleGroup_congr.1 (isSimpleGroup_statedSp hK hm)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  exfalso
  obtain ⟨κ, hκ⟩ := exists_units_ne_one hK
  obtain ⟨j, hpj⟩ : ∃ j : Fin (m + 1), p ≠ j := by
    by_cases h0 : p = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      rw [h0] at h
      exact absurd (congrArg Fin.val h) (by simp)
    · exact ⟨0, h0⟩
  set x : complSp K p := ⟨rootTorusHom K (m + 1) j κ,
    longRootSp2_le_complSp hpj (rootTorusSp_le_longRootSp2 j ⟨κ, rfl⟩)⟩
  have hxN : x ∈ N := h ▸ Subgroup.mem_top x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hN) ⟨x, hxN⟩
  rw [Subgroup.orderOf_mk] at hk
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    have := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hf]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, f.ne_zero⟩) odd_one
  have hdvd : orderOf x ∣ Nat.card Kˣ := by
    refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, pow_card_eq_one', map_one]
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card Kˣ := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  have h1 : rootTorusHom K (m + 1) j κ = 1 := congrArg Subtype.val hk
  exact hκ (rootTorusHom_injective j (h1.trans (map_one _).symm))

end OTwo

section SA7

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem spRep_b1_eq_siegDiag (n : ℕ) : spRep (K := K) n .b1 = siegDiag K 1 1 := by
  rw [spRep, twoCentralRep, twoCentralElt_eq_siegDiag_mul_siegPair]
  simp only [SpTwoCentral.params]
  rw [show siegPair K (1 : Fin (n + 3)) 2 0 = 1 from by
    rw [siegPair, ← upperUnipotentSp_zero (m := n + 3) (K := K)]
    exact upperUnipotentSp_congr _ _ (by rw [single_zero, single_zero, add_zero]), mul_one]

theorem perfectCore_centralizer_spRep_b1 (hK : 4 ≤ Nat.card K) (n : ℕ) :
    ∃ Q M S : Subgroup (StatedSp (n + 3) K), IsPGroup 2 Q ∧
      M ≤ normalizer (Q : Set (StatedSp (n + 3) K)) ∧ Disjoint Q M ∧
      perfectCore (centralizer ({spRep n .b1} : Set (StatedSp (n + 3) K))) = Q ⊔ M ∧
      (∀ N : Subgroup M, N.Normal → IsPGroup 2 N → N = ⊥) ∧
      spRep n .b1 ∈ perfectCore (centralizer ({spRep n .b1} : Set (StatedSp (n + 3) K))) ∧
      longRootSp2 K (n + 3) 0 ≤ S ∧ S = perfectCore M ∧
      Nonempty (S ≃* StatedSp (n + 2) K) := by
  have h10 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have hperf := commutator_centralizer_siegDiag (K := K) (m := n + 2) hK (p := 1) (by omega)
  have hMperf := commutator_complSp (K := K) (m := n + 2) hK 1
  refine ⟨transvRadical K 1, complSp K 1, complSp K 1, isPGroup_transvRadical,
    complSp_le_normalizer_transvRadical, disjoint_transvRadical_complSp, ?_,
    fun N hN hN2 => @eq_bot_of_normal_of_isPGroup_complSp K _ (n + 2) _ _ hK (by omega) 1 N hN hN2,
    spRep_mem_perfectCore_centralizer hK n .b1, longRootSp2_le_complSp (Ne.symm h10),
    (CFSG.Quasithin.perfectCore_eq_self_of_perfect hMperf).symm, ⟨(complSpEquiv 1).symm⟩⟩
  rw [spRep_b1_eq_siegDiag, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf,
    centralizer_siegDiag_eq_sup]

end SA7

end CFSG.SeitzReduction.SymplecticPilot
