module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrLink
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Alpha
public import CFSG.ClassicalInvolution.Asc77.AscT8T3
import CFSG.ClassicalInvolution.Asc77.AscT8T12Eng

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AlphaFr

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open CFSG.ClassicalInvolution.Q3.TL4

section Pair

variable {G : Type} [Group G]

theorem closure_pair_mul_left {z t : G} (hz : z * z = 1) :
    Subgroup.closure ({z * t, z} : Set G) = Subgroup.closure ({t, z} : Set G) := by
  exact CFSG.ClassicalInvolution.Asc77.T8T.closure_pair_mul_leftE hz

end Pair

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem alpha_of_triangle (hH : TightHyp51TriR r n) (hL : TightLargeHypR r n Y Rd Sd z)
    {J L : Subgroup Y} {u w : Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hLK : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hLJ : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J)
    (hu : IsUniqueInvolution J u) (hw : IsUniqueInvolution L w)
    (hind : w ∉ Subgroup.closure ({z, u} : Set Y)) :
    (∀ F : Subgroup Y, F ≤ Subgroup.closure ({z, u, w} : Set Y) → IsElemAbelian2 F 2 →
        alphaOf F = alphaOf (Subgroup.closure ({u, z} : Set Y))) ∧
      ∀ b ∈ Subgroup.closure ({z, u, w} : Set Y),
        oddCoreOf (Subgroup.centralizer ({b} : Set Y)) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hz := hd.isUniqueInvolution_core
  have hnt := noTwins_of_large hL
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨P, hF⟩ := exists_triFrame_of_commonNbr hL hJ hLK hLJ hu hw
  have hHyp : Hyp51 (Subgroup.closure ({z, u, w} : Set Y)) :=
    hH Y Rd Sd z hL ![tightCore Rd, J, L] ![z, u, w] P hF hind
  have hzu : z * u = u * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ hu
  have huz : u ≠ z := fun h => hJ.2.1 (hnt _ hK J ⟨hJ.1, z, hz, h ▸ hu⟩)
  have hDB : Subgroup.closure ({u, z} : Set Y) ≤ Subgroup.closure ({z, u, w} : Set Y) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair hu.sq hz.sq hu.ne_one hz.ne_one huz hzu.symm
  have h3 := (lemma54_odd_and_eq hHyp hDB hD).2
  exact ⟨h3, fun b hb => T8T.oddCoreOf_centralizer_le_normalizer hHyp.1 hHyp.2.1 hb h3⟩

theorem alphaOf_eq_of_link_edge (hH : TightHyp51TriR r n) (hL : TightLargeHypR r n Y Rd Sd z)
    {J L : Subgroup Y} {u w : Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hLK : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hLJ : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J)
    (hu : IsUniqueInvolution J u) (hw : IsUniqueInvolution L w) :
    alphaOf (Subgroup.closure ({w, z} : Set Y)) =
      alphaOf (Subgroup.closure ({u, z} : Set Y)) := by
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hz := hd.isUniqueInvolution_core
  have hnt := noTwins_of_large hL
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) :=
    CoreAssembly.mem_conjClass_self _
  have hzu : z * u = u * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ hu
  have hzw : z * w = w * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hLK hw
  by_cases hdeg : w ∈ Subgroup.closure ({z, u} : Set Y)
  · rcases T3CII.closure_pair_cases hz.sq hu.sq hzu hdeg with h | h | h | h
    · exact absurd h hw.ne_one
    · exact absurd (hnt _ hK L ⟨hLK.1, z, hz, h ▸ hw⟩) hLK.2.1
    · exact absurd (hnt _ hJ.1 L ⟨hLK.1, u, hu, h ▸ hw⟩) hLJ.2.1
    · rw [h, closure_pair_mul_left hz.sq]
  · obtain ⟨hbal, -⟩ := alpha_of_triangle hH hL hJ hLK hLJ hu hw hdeg
    have hle : Subgroup.closure ({w, z} : Set Y) ≤ Subgroup.closure ({z, u, w} : Set Y) := by
      apply Subgroup.closure_mono
      intro y hy
      rcases hy with rfl | rfl <;> simp
    have hwz : w ≠ z := fun h => hLK.2.1 (hnt _ hK L ⟨hLK.1, z, hz, h ▸ hw⟩)
    exact hbal _ hle
      (T7A.isElemAbelian2_closure_pair hw.sq hz.sq hw.ne_one hz.ne_one hwz hzw.symm)

theorem exists_base_triangle (hL : TightLargeHypR r n Y Rd Sd z)
    (hfr : ∃ (M : Fin 3 → Subgroup Y) (x : Fin 3 → Y) (P : Fin 3 → Subgroup Y),
      TriFrame (CoreAssembly.conjClass (tightCore Rd)) M x P ∧
        x 2 ∉ Subgroup.closure ({x 0, x 1} : Set Y)) :
    ∃ (A B : Subgroup Y) (a b : Y),
      A ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      B ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      B ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) A ∧
      IsUniqueInvolution A a ∧ IsUniqueInvolution B b ∧
      b ∉ Subgroup.closure ({z, a} : Set Y) := by
  obtain ⟨M, x, P, hF, hind⟩ := hfr
  have hd := hL.datum
  have hz := hd.isUniqueInvolution_core
  obtain ⟨h, hh⟩ := hF.mem 0
  have hh' : conjSub h (tightCore Rd) = M 0 := hh
  have hF' := triFrame_conj hd.hypOmegaGen.conjInvariant hF h⁻¹
  have hM0 : conjSub h⁻¹ (M 0) = tightCore Rd := by rw [← hh', conjSub_inv_conjSub]
  have h0 : IsUniqueInvolution (conjSub h⁻¹ (M 0)) (h⁻¹ * x 0 * h⁻¹⁻¹) := hF'.inv 0
  rw [hM0] at h0
  have hx0 : h⁻¹ * x 0 * h⁻¹⁻¹ = z := h0.eq hz
  have h01 : conjSub h⁻¹ (M 1) ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd))
      (conjSub h⁻¹ (M 0)) := hF'.nbr 0 1 (by decide)
  have h02 : conjSub h⁻¹ (M 2) ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd))
      (conjSub h⁻¹ (M 0)) := hF'.nbr 0 2 (by decide)
  rw [hM0] at h01 h02
  refine ⟨conjSub h⁻¹ (M 1), conjSub h⁻¹ (M 2), h⁻¹ * x 1 * h⁻¹⁻¹, h⁻¹ * x 2 * h⁻¹⁻¹, h01, h02,
    hF'.nbr 1 2 (by decide), hF'.inv 1, hF'.inv 2, fun hmem => hind ?_⟩
  rw [← hx0, ← T7A.conjSub_closure_pair, mem_conjSub_iff] at hmem
  simpa [mul_assoc] using hmem

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.AlphaFr
