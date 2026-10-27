module

public import Certificates.Data.E8KilledPlanes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg

theorem e8Certificate_roots_length : e8Certificate.roots.length = 240 := by decide +kernel

theorem toArray_map_range_getD {α : Type*} {n i : ℕ} (f : ℕ → α) (d : α) (hi : i < n) :
    (((List.range n).map f).toArray).getD i d = f i := by
  simp [Array.getD_eq_getD_getElem?, hi]

theorem e8PlaneRL_getD {r : ℕ} (hr : r < 240) :
    (e8PlaneRL ()).getD r [] = List.ofFn (e8Certificate.root r) :=
  toArray_map_range_getD _ _ hr

theorem e8PlaneRA_getD {r : ℕ} (hr : r < 240) :
    (e8PlaneRA ()).getD r [] = List.ofFn fun i : Fin Tag.E8.rank =>
      ∑ j, Tag.E8.symmetrizedCartan i j * e8Certificate.root r j :=
  toArray_map_range_getD _ _ hr

theorem dotL_ofFn_symmetrizedCartan (x y : Fin Tag.E8.rank → ℤ) :
    dotL (List.ofFn x) (List.ofFn fun i : Fin Tag.E8.rank =>
      ∑ j, Tag.E8.symmetrizedCartan i j * y j) = iform x y := by
  rw [dotL, sum_zipWith_ofFn_left, iform]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem e8PlaneGram_getD {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())).getD (240 * a + b) 0 =
      iform (e8Certificate.root a) (e8Certificate.root b) := by
  rw [e8PlaneGram, toArray_map_range_getD _ _ (show 240 * a + b < 57600 by omega),
    show (240 * a + b) / 240 = a by omega, show (240 * a + b) % 240 = b by omega,
    e8PlaneRL_getD ha, e8PlaneRA_getD hb, dotL_ofFn_symmetrizedCartan]


theorem e8Certificate_isRoot {r : ℕ} (hr : r < 240) : IsRoot Tag.E8 (e8Certificate.root r) :=
  RootCertificate.isRoot_root e8Certificate_check r (by rw [e8Certificate_roots_length]; exact hr)

theorem e8Certificate_exists_root {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) :
    ∃ r < 240, e8Certificate.root r = α := by
  obtain ⟨r, hr, h⟩ := RootCertificate.exists_root_eq e8Certificate_check hα
  exact ⟨r, by rwa [e8Certificate_roots_length] at hr, h⟩

theorem e8Certificate_root_single (j : Fin Tag.E8.rank) :
    e8Certificate.root j = Pi.single j 1 := by
  have h := e8Certificate_check
  simp only [RootCertificate.check, Bool.and_eq_true] at h
  obtain ⟨⟨hb, -⟩, -⟩ := h
  simp only [RootCertificate.checkBasis, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at hb
  exact RootCertificate.eq_of_ofFn_beq (hb.2 j)

theorem e8Certificate_root_inj {r r' : ℕ} (hr : r < 240) (hr' : r' < 240)
    (h : e8Certificate.root r = e8Certificate.root r') : r = r' := by
  have hn := e8Certificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq, e8Certificate_roots_length] at hn
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 hr) (List.mem_range.2 hr') (by rw [h])

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane
