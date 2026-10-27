module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitEta

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

theorem IsSupp.mul {A B : Set ι} {M N : Matrix ι ι R} (hM : IsSupp A M) (hN : IsSupp B N) :
    IsSupp (A ∪ B) (M * N) := by
  intro x y hxy
  rcases hxy with hx | hy
  · rw [Set.mem_union, not_or] at hx
    rw [hM.mul_apply_of_notMem hx.1, hN x y (Or.inl hx.2)]
  · rw [Set.mem_union, not_or] at hy
    have h : (M * N) x y = M x y := by
      rw [mul_apply]
      trans ∑ z, M x z * (1 : Matrix ι ι R) z y
      · exact Finset.sum_congr rfl fun z _ => by rw [hN z y (Or.inr hy.2)]
      · rw [← mul_apply, Matrix.mul_one]
    rw [h, hM x y (Or.inr hy.1)]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open SymplecticTorusWeyl

variable {r : ℕ} {k : Type} [Field k]

theorem isSupp_etaMat {a b : Fin r ⊕ Fin r} (g : SpecialLinearGroup (Fin 2) k) :
    IsSupp ({a, b} ∪ {a.swap, b.swap}) (etaMat a b g) := by
  rw [etaMat]
  exact (isSupp_pairMat (a := a) (b := b) (g := (g : Matrix (Fin 2) (Fin 2) k))).mul
    (isSupp_pairMat (a := a.swap) (b := b.swap)
      (g := ((sl2InvT g : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)))

theorem coordIdx_mem_of_mem_etaSupport {a b x : Fin r ⊕ Fin r}
    (hx : x ∈ ({a, b} ∪ {a.swap, b.swap} : Set (Fin r ⊕ Fin r))) :
    coordIdx x ∈ ({coordIdx a, coordIdx b} : Set (Fin r)) := by
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with (rfl | rfl) | rfl | rfl <;> simp

theorem disjoint_etaSupport {a b c d : Fin r ⊕ Fin r}
    (h : Disjoint ({coordIdx a, coordIdx b} : Set (Fin r))
      ({coordIdx c, coordIdx d} : Set (Fin r))) :
    Disjoint (({a, b} : Set (Fin r ⊕ Fin r)) ∪ {a.swap, b.swap})
      (({c, d} : Set (Fin r ⊕ Fin r)) ∪ {c.swap, d.swap}) := by
  rw [Set.disjoint_left] at h ⊢
  intro x hx hx'
  exact h (coordIdx_mem_of_mem_etaSupport hx) (coordIdx_mem_of_mem_etaSupport hx')

theorem commute_eta_of_disjoint_coordIdx {a b c d : Fin r ⊕ Fin r}
    (hab : coordIdx a ≠ coordIdx b) (hcd : coordIdx c ≠ coordIdx d)
    (h : Disjoint ({coordIdx a, coordIdx b} : Set (Fin r))
      ({coordIdx c, coordIdx d} : Set (Fin r)))
    (g g' : SpecialLinearGroup (Fin 2) k) :
    Commute (eta hab g) (eta hcd g') := by
  have hmat : Commute (etaMat a b g) (etaMat c d g') :=
    (isSupp_etaMat g).commute (isSupp_etaMat g') (disjoint_etaSupport h)
  have hGL : Commute (etaGL hab g) (etaGL hcd g') :=
    Units.ext (by simpa only [Units.val_mul, coe_etaGL] using hmat.eq)
  have hlin : Commute (etaLin hab g) (etaLin hcd g') := by
    rw [etaLin_eq, etaLin_eq]
    exact hGL.map (toLinEquiv (Fin r ⊕ Fin r) k)
  exact Subtype.ext (by simpa only [Subgroup.coe_mul, coe_eta] using hlin.eq)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
