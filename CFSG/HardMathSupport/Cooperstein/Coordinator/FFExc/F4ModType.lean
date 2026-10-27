module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModSimple
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitOffender

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem tgt_E_e0 : ∀ k < 6, tgt k 0 = 0 := by decide +kernel

theorem tgt_F_e0 : tgt 6 0 = 2 ∧ tgt 8 0 = 0 ∧ tgt 10 0 = 0 ∧ tgt 12 0 = 0 ∧ tgt 14 0 = 0 ∧
    tgt 16 0 = 0 := by decide +kernel

theorem tgt_e1 : tgt 0 1 = 1 ∧ tgt 5 1 = 0 ∧ tgt 6 1 = 0 ∧ tgt 16 1 = 0 := by decide +kernel

theorem e6root_neg_single : ∀ i : Fin Tag.E6.rank, e6root (6 + 2 * i.val) = -Pi.single i 1 := by
  decide +kernel

abbrev i1 : Ix := ⟨1, by decide⟩

theorem E_single_zero (k : ℕ) (hk : k < 72) (p : Ix) (h : tgt k p = 0) :
    e6Data.E K k (Finsupp.single p (1 : K)) = 0 := by
  ext i
  rw [coe_E k hk, Finsupp.single_eq_pi_single, Matrix.mulVec_single_one]
  simp [Em2_apply, h]

theorem endo_xm_root (k : ℕ) (hk : k < 72) (c : K) (v : Fin e6Data.d →₀ K) :
    e6Data_valid.endo K (e6Data_valid.xm K (e6root k) c) v = v + c • e6Data.E K k v := by
  have e : e6Data.rootOp K (e6root k) = e6Data.E K k :=
    MinData.rootOp_root (show k < Tag.E6.rootCertificate.roots.length from hk)
  rw [MinData.Valid.endo_xm, e]
  simp

theorem endo_xm_single (i : Fin Tag.E6.rank) (c : K) (v : Fin e6Data.d →₀ K) :
    e6Data_valid.endo K (e6Data_valid.xm K (Pi.single i 1) c) v = v + c • e6Data.E K i.val v := by
  rw [← e6root_simple i]
  exact endo_xm_root K i.val (by have := i.2; change i.val < 6 at this; omega) c v

theorem endo_xm_neg_single (i : Fin Tag.E6.rank) (c : K) (v : Fin e6Data.d →₀ K) :
    e6Data_valid.endo K (e6Data_valid.xm K (-Pi.single i 1) c) v =
      v + c • e6Data.E K (6 + 2 * i.val) v := by
  rw [← e6root_neg_single i]
  exact endo_xm_root K _ (by have := i.2; change i.val < 6 at this; omega) c v

theorem E_e0_lt (k : ℕ) (hk : k < 6) : e6Data.E K k (Finsupp.single i0 (1 : K)) = 0 :=
  E_single_zero K k (by omega) i0 (tgt_E_e0 k hk)

theorem E_e0_neg (k : ℕ) (hk : k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 14 ∨ k = 16) :
    e6Data.E K k (Finsupp.single i0 (1 : K)) = 0 := by
  have h := tgt_F_e0
  refine E_single_zero K k (by omega) i0 ?_
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem E_e0_six : e6Data.E K 6 (Finsupp.single i0 (1 : K)) = Finsupp.single i1 (1 : K) :=
  E_single (K := K) 6 (by decide) i0 i1 tgt_F_e0.1

theorem E_e1_zero : e6Data.E K 0 (Finsupp.single i1 (1 : K)) = Finsupp.single i0 (1 : K) :=
  E_single (K := K) 0 (by decide) i1 i0 tgt_e1.1

theorem E_e1_five : e6Data.E K 5 (Finsupp.single i1 (1 : K)) = 0 :=
  E_single_zero K 5 (by decide) i1 tgt_e1.2.1

theorem E_e1_six : e6Data.E K 6 (Finsupp.single i1 (1 : K)) = 0 :=
  E_single_zero K 6 (by decide) i1 tgt_e1.2.2.1

theorem E_e1_sixteen : e6Data.E K 16 (Finsupp.single i1 (1 : K)) = 0 :=
  E_single_zero K 16 (by decide) i1 tgt_e1.2.2.2

abbrev orbA : List (Fin Tag.E6.rank) := [nd0, nd5]

theorem endo_sX_e0 {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (c : K) :
    e6Data_valid.endo K (sX e6Data_valid K l c) (Finsupp.single i0 (1 : K)) =
      Finsupp.single i0 (1 : K) := by
  simp only [orbs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp [sX_pair, sX_single, endo_mul_apply, endo_xm_single, E_e0_lt]

theorem endo_sY_e0 {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (h0 : nd0 ∉ l) (c : K) :
    e6Data_valid.endo K (sY e6Data_valid K l c) (Finsupp.single i0 (1 : K)) =
      Finsupp.single i0 (1 : K) := by
  simp only [orbs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact absurd (by simp) h0
  · simp [sY_pair, endo_mul_apply, endo_xm_neg_single, E_e0_neg]
  · simp [sY_single, endo_xm_neg_single, E_e0_neg]
  · simp [sY_single, endo_xm_neg_single, E_e0_neg]

theorem endo_sY_e0_A (c : K) :
    e6Data_valid.endo K (sY e6Data_valid K orbA c) (Finsupp.single i0 (1 : K)) =
      Finsupp.single i0 (1 : K) + c • Finsupp.single i1 (1 : K) := by
  simp [orbA, sY_pair, endo_mul_apply, endo_xm_neg_single, E_e0_neg, E_e0_six]

theorem endo_sX_e1_A (c : K) :
    e6Data_valid.endo K (sX e6Data_valid K orbA c) (Finsupp.single i1 (1 : K)) =
      Finsupp.single i1 (1 : K) + c • Finsupp.single i0 (1 : K) := by
  simp [orbA, sX_pair, endo_mul_apply, endo_xm_single, E_e1_zero, E_e1_five]

theorem endo_sY_e1_A (c : K) :
    e6Data_valid.endo K (sY e6Data_valid K orbA c) (Finsupp.single i1 (1 : K)) =
      Finsupp.single i1 (1 : K) := by
  simp [orbA, sY_pair, endo_mul_apply, endo_xm_neg_single, E_e1_six, E_e1_sixteen]

@[expose] def wC (j : Fin Tag.F4.rank) (t : Kˣ) : adjointGroup Tag.F4 K :=
  ⟨weylElt Tag.F4 K j t, weylElt_mem_adjointGroup j t⟩

theorem wC_eq (j : Fin Tag.F4.rank) (t : Kˣ) :
    wC K j t = xC Tag.F4 K j t * yC Tag.F4 K j (-((t⁻¹ : Kˣ) : K)) * xC Tag.F4 K j t :=
  Subtype.ext (by
    simp only [wC, Subgroup.coe_mul, xC, yC]
    exact weylElt_eq_xUnit_mul j t)

theorem dC_eq_wC (j : Fin Tag.F4.rank) (t : Kˣ) :
    dC Tag.F4 K j t = wC K j t * wC K j (-1) :=
  Subtype.ext (by simp only [dC, wC, Subgroup.coe_mul, torusElt])

theorem f4Embed_wC (j : Fin Tag.F4.rank) (t : Kˣ) :
    f4Embed K (idF4 K) (wC K j t) =
      sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) t *
        sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) (-((t⁻¹ : Kˣ) : K)) *
        sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) t := by
  rw [wC_eq, map_mul, map_mul, f4Embed_xC, f4Embed_yC]

theorem unit_neg_inv_mul (t : Kˣ) : (-((t⁻¹ : Kˣ) : K)) * (t : K) = -1 := by
  rw [neg_mul, Units.inv_mul]

theorem endo_n_A_e0 (t : Kˣ) :
    e6Data_valid.endo K (sX e6Data_valid K orbA t * sY e6Data_valid K orbA (-((t⁻¹ : Kˣ) : K)) *
      sX e6Data_valid K orbA t) (Finsupp.single i0 (1 : K)) =
        (-((t⁻¹ : Kˣ) : K)) • Finsupp.single i1 (1 : K) := by
  have hA : orbA ∈ orbs := by decide
  simp only [endo_mul_apply, endo_sX_e0 (K := K) hA, endo_sY_e0_A, map_add, map_smul,
    endo_sX_e1_A, smul_add, smul_smul, unit_neg_inv_mul]
  module

theorem endo_n_A_e1 (t : Kˣ) :
    e6Data_valid.endo K (sX e6Data_valid K orbA t * sY e6Data_valid K orbA (-((t⁻¹ : Kˣ) : K)) *
      sX e6Data_valid K orbA t) (Finsupp.single i1 (1 : K)) =
        (t : K) • Finsupp.single i0 (1 : K) := by
  have hA : orbA ∈ orbs := by decide
  simp only [endo_mul_apply, endo_sX_e0 (K := K) hA, endo_sY_e0_A, endo_sY_e1_A, map_add,
    map_smul, endo_sX_e1_A, smul_add, smul_smul]
  have h : (t : K) * (-((t⁻¹ : Kˣ) : K)) = -1 := by rw [mul_comm, unit_neg_inv_mul]
  rw [h]
  have h' : (t : K) * ((-((t⁻¹ : Kˣ) : K)) * (t : K)) = -(t : K) := by
    rw [unit_neg_inv_mul]; ring
  rw [h']
  module

theorem endo_n_nonA_e0 {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (h0 : nd0 ∉ l) (t : K) (s : K) :
    e6Data_valid.endo K (sX e6Data_valid K l t * sY e6Data_valid K l s * sX e6Data_valid K l t)
      (Finsupp.single i0 (1 : K)) = Finsupp.single i0 (1 : K) := by
  simp only [endo_mul_apply, endo_sX_e0 (K := K) hl, endo_sY_e0 (K := K) hl h0]

theorem unit_neg_one_inv : (-(((-1 : Kˣ)⁻¹ : Kˣ) : K)) = 1 := by simp

theorem endo_dC_e0 (j : Fin Tag.F4.rank) (t : Kˣ) :
    e6Data_valid.endo K (f4Embed K (idF4 K) (dC Tag.F4 K j t)) (Finsupp.single i0 (1 : K)) =
      ((t : K) ^ (if j.val = 3 then 1 else 0)) • Finsupp.single i0 (1 : K) := by
  rw [dC_eq_wC, map_mul, f4Embed_wC, f4Embed_wC, endo_mul_apply]
  fin_cases j
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) = [nd1] := rfl
    change e6Data_valid.endo K _ (e6Data_valid.endo K _ _) = ((t : K) ^ 0) • _
    rw [h, endo_n_nonA_e0 K (l := [nd1]) (by decide) (by decide), endo_n_nonA_e0 K (l := [nd1]) (by decide) (by decide)]
    simp
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) = [nd3] := rfl
    change e6Data_valid.endo K _ (e6Data_valid.endo K _ _) = ((t : K) ^ 0) • _
    rw [h, endo_n_nonA_e0 K (l := [nd3]) (by decide) (by decide), endo_n_nonA_e0 K (l := [nd3]) (by decide) (by decide)]
    simp
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) = [nd2, nd4] := rfl
    change e6Data_valid.endo K _ (e6Data_valid.endo K _ _) = ((t : K) ^ 0) • _
    rw [h, endo_n_nonA_e0 K (l := [nd2, nd4]) (by decide) (by decide), endo_n_nonA_e0 K (l := [nd2, nd4]) (by decide) (by decide)]
    simp
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) = orbA := rfl
    change e6Data_valid.endo K _ (e6Data_valid.endo K _ _) = ((t : K) ^ 1) • _
    rw [h, endo_n_A_e0, map_smul, endo_n_A_e1]
    simp [unit_neg_one_inv]

abbrev j3 : Fin Tag.F4.rank := ⟨3, by decide⟩

theorem torus_act (j : Fin Tag.F4.rank) (t : Kˣ) :
    m26Rep K (dC Tag.F4 K j t) (y26 K) = ((t : K) ^ (if j.val = 3 then 1 else 0)) • y26 K := by
  refine jExt_injective K ?_
  rw [jExt_m26Rep, jExt_y26, map_smul, jExt_y26, endo_dC_e0]

theorem y26_mem_fixU : y26 K ∈ (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').fixU (m26Rep K) := by
  have hne := (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').fixU_ne_bot (p := 2) (m26Rep K)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨c, hc⟩ := m26Rep_fixed_smul K fun j c =>
    hx (xC Tag.F4 K j c) ((chevDatum Tag.F4 K 2 exists_weyl_neg_F4').X_le j
      (xC_mem_X (hw := exists_weyl_neg_F4') j c))
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [hc, h, zero_smul])
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

theorem m26Rep_H_scalar {h : adjointGroup Tag.F4 K}
    (hh : h ∈ (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').H) :
    ∃ c : K, m26Rep K h (y26 K) = c • y26 K := by
  have hy := y26_mem_fixU K
  have hfix : m26Rep K h (y26 K) ∈ (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').fixU (m26Rep K) := by
    intro u hu
    have h1 := (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').H_normU' h hh u hu
    have h2 := hy _ h1
    calc m26Rep K u (m26Rep K h (y26 K)) = m26Rep K (u * h) (y26 K) := by
          rw [map_mul]; rfl
      _ = m26Rep K (h * (h⁻¹ * u * h)) (y26 K) := by
          rw [show h * (h⁻¹ * u * h) = u * h by group]
      _ = m26Rep K h (m26Rep K (h⁻¹ * u * h) (y26 K)) := by
          rw [map_mul]; rfl
      _ = m26Rep K h (y26 K) := by rw [h2]
  obtain ⟨c, hc⟩ := m26Rep_fixed_smul K (x := m26Rep K h (y26 K))
    (fun j c => hfix (xC Tag.F4 K j c) ((chevDatum Tag.F4 K 2 exists_weyl_neg_F4').X_le j
        (xC_mem_X (hw := exists_weyl_neg_F4') j c)))
  exact ⟨c, hc⟩

theorem nC_eq_wC (j : Fin Tag.F4.rank) : nC Tag.F4 K j = wC K j 1 := rfl

theorem jExt_hecke_term (j : Fin Tag.F4.rank) (c : K) :
    jExt K (m26Rep K (xC Tag.F4 K j c * nC Tag.F4 K j) (y26 K)) =
      e6Data_valid.endo K
        (sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c *
          (sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) (1 : Kˣ) *
            sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j))
              (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) *
            sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) (1 : Kˣ)))
        (Finsupp.single i0 (1 : K)) := by
  rw [jExt_m26Rep, jExt_y26, nC_eq_wC, map_mul, f4Embed_xC, f4Embed_wC]

theorem hecke_term_nonA {l : List (Fin Tag.E6.rank)} (hl : l ∈ orbs) (h0 : nd0 ∉ l) (c : K) :
    e6Data_valid.endo K (sX e6Data_valid K l c *
      (sX e6Data_valid K l (1 : Kˣ) * sY e6Data_valid K l (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) *
        sX e6Data_valid K l (1 : Kˣ))) (Finsupp.single i0 (1 : K)) = Finsupp.single i0 (1 : K) := by
  rw [endo_mul_apply, endo_n_nonA_e0 K hl h0, endo_sX_e0 K hl]

theorem sum_const_e0 [Fintype K] (v : Fin e6Data.d →₀ K) : ∑ _c : K, v = 0 := by
  classical
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K, FiniteField.cast_card_eq_zero K,
    zero_smul]

theorem heckeT_m26_nonA (j : Fin Tag.F4.rank) (hj : j.val ≠ 3) :
    (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').heckeT (m26Rep K) j (y26 K) = 0 := by
  classical
  have := Fintype.ofFinite K
  rw [heckeT_chevDatum]
  refine jExt_injective K ?_
  rw [map_sum, map_zero]
  have key : ∀ c : K, jExt K (m26Rep K (xC Tag.F4 K j c * nC Tag.F4 K j) (y26 K)) =
      Finsupp.single i0 (1 : K) := by
    intro c
    rw [jExt_hecke_term]
    have hj3 : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by
      have h4 : j.val < 4 := j.2
      omega
    rcases hj3 with h | h | h
    · have hjj : j = ⟨0, by decide⟩ := Fin.ext h
      subst hjj
      have h' : TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) = [nd1] := rfl
      rw [h']; exact hecke_term_nonA K (by decide) (by decide) c
    · have hjj : j = ⟨1, by decide⟩ := Fin.ext h
      subst hjj
      have h' : TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) = [nd3] := rfl
      rw [h']; exact hecke_term_nonA K (by decide) (by decide) c
    · have hjj : j = ⟨2, by decide⟩ := Fin.ext h
      subst hjj
      have h' : TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) = [nd2, nd4] := rfl
      rw [h']; exact hecke_term_nonA K (by decide) (by decide) c
  simp only [key]
  exact sum_const_e0 K _

theorem jExt_hecke_j3 [Fintype K] :
    jExt K ((chevDatum Tag.F4 K 2 exists_weyl_neg_F4').heckeT (m26Rep K) j3 (y26 K)) =
      (∑ c : K, c) • Finsupp.single i0 (1 : K) := by
  rw [heckeT_chevDatum, map_sum]
  have h' : TwistTag.E6.orbitWord (f4FoldedIndex j3) = orbA := rfl
  have key : ∀ c : K, jExt K (m26Rep K (xC Tag.F4 K j3 c * nC Tag.F4 K j3) (y26 K)) =
      Finsupp.single i1 (1 : K) + c • Finsupp.single i0 (1 : K) := by
    intro c
    rw [jExt_hecke_term, h', endo_mul_apply, endo_n_A_e0, map_smul, endo_sX_e1_A]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hn : (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) = 1 := by
      simp only [inv_one, Units.val_one]; linear_combination (-1 : K) * h2
    rw [hn, one_smul]
  simp only [key]
  rw [Finset.sum_add_distrib, sum_const_e0, zero_add, Finset.sum_smul]

theorem heckeT_m26_j3_of_card_two (h : Nat.card K = 2) :
    (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').heckeT (m26Rep K) j3 (y26 K) ≠ 0 := by
  classical
  have := Fintype.ofFinite K
  intro h0
  have h1 := congrArg (jExt K) h0
  rw [jExt_hecke_j3, map_zero] at h1
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact h
  have hsum : ∑ c : K, c = 1 := by
    have hs : ({0, 1} : Finset K) = Finset.univ := by
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
      rw [Finset.card_univ, hcard, Finset.card_pair zero_ne_one]
    rw [← hs, Finset.sum_pair zero_ne_one, zero_add]
  rw [hsum, one_smul] at h1
  have h2 := congrArg (fun v : Fin e6Data.d →₀ K => v i0) h1
  simp at h2

theorem m26_isChevType (χ : adjointGroup Tag.F4 K → K)
    (hχ : ∀ h ∈ (chevDatum Tag.F4 K 2 exists_weyl_neg_F4').H, m26Rep K h (y26 K) = χ h • y26 K) :
    IsChevType Tag.F4 K 2 exists_weyl_neg_F4' (m26Rep K) (y26 K) χ (Finset.univ.erase j3) := by
  classical
  have hchi : ∀ (j : Fin Tag.F4.rank) (t : Kˣ),
      χ (dC Tag.F4 K j t) = (t : K) ^ (if j.val = 3 then 1 else 0) := by
    intro j t
    have h1 := hχ _ (dC_mem_H j t)
    rw [torus_act] at h1
    exact (smul_left_injective K (y26_ne_zero K) h1).symm
  refine ⟨y26_mem_fixU K, y26_ne_zero K, hχ, fun i => ?_⟩
  by_cases hi : i = j3
  · subst hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, not_true_eq_false, false_iff]
    rintro ⟨hall, hT⟩
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    by_cases h2 : Nat.card K = 2
    · exact heckeT_m26_j3_of_card_two K h2 hT
    · have hgt : 2 < Nat.card K := by omega
      have : Nontrivial Kˣ := by
        have := Fintype.ofFinite K
        rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_units]
        rw [← Nat.card_eq_fintype_card]; omega
      obtain ⟨t, ht⟩ := exists_ne (1 : Kˣ)
      have := hall t
      rw [hchi] at this
      simp at this
      exact ht this
  · have hv : i.val ≠ 3 := fun h => hi (Fin.ext h)
    rw [Finset.mem_erase]
    refine ⟨fun _ => ⟨fun t => ?_, heckeT_m26_nonA K i hv⟩, fun _ => ⟨hi, Finset.mem_univ _⟩⟩
    rw [hchi, if_neg hv, pow_zero]

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
