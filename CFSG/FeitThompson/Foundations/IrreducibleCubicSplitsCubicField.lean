module

public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.PrimeField
public import CFSG.FeitThompson.Foundations.FrobeniusNormPrimeDegree

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Polynomial

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Algebra (ZMod p) F]

theorem charP_of_algebra_zmod : CharP F p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p

theorem coe_bot_subfield_eq_range_algebraMap :
    ((⊥ : Subfield F) : Set F) = Set.range (algebraMap (ZMod p) F) := by
  rw [Subfield.bot_eq_of_zMod_algebra p]; rfl

theorem isRoot_map_pow_char {f : (ZMod p)[X]} {b : F}
    (h : (f.map (algebraMap (ZMod p) F)).IsRoot b) :
    (f.map (algebraMap (ZMod p) F)).IsRoot (b ^ p) := by
  have : CharP F p := charP_of_algebra_zmod
  have : ExpChar F p := ExpChar.prime Fact.out
  have hφ : (frobenius F p).comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) F := by
    ext c; simp [frobenius_def, ← map_pow, ZMod.pow_card]
  have key := hom_eval₂ f (algebraMap (ZMod p) F) (frobenius F p) b
  rw [hφ] at key
  simp only [frobenius_def] at key
  rw [IsRoot, eval_map] at h ⊢
  rw [← key, h, zero_pow (Fact.out : p.Prime).pos.ne']

variable {f : (ZMod p)[X]}

theorem irreducible_of_natDegree_eq_three (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) : Irreducible f :=
  irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) hnoroot

theorem dvd_X_pow_pow_sub_X (hdeg : f.natDegree = 3) (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) :
    f ∣ X ^ p ^ 3 - X := by
  have h := ((irreducible_of_natDegree_eq_three hdeg
    hnoroot).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 3)).mp (by rw [hdeg])
  rwa [Nat.card_zmod] at h

private theorem map_dvd_X_pow_pow_sub_X (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) :
    f.map (algebraMap (ZMod p) F) ∣ (X ^ p ^ 3 - X : F[X]) := by
  simpa using Polynomial.map_dvd (algebraMap (ZMod p) F) (dvd_X_pow_pow_sub_X hdeg hnoroot)

theorem splits_map (hcard : Nat.card F = p ^ 3) (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) : (f.map (algebraMap (ZMod p) F)).Splits := by
  have h := splits_X_pow_nat_card_sub_X (K := F)
  rw [hcard] at h
  exact Splits.of_dvd h
    (FiniteField.X_pow_card_pow_sub_X_ne_zero F three_ne_zero (Fact.out : p.Prime).one_lt)
    (map_dvd_X_pow_pow_sub_X hdeg hnoroot)

theorem card_roots_map_eq_three (hcard : Nat.card F = p ^ 3) (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) :
    (f.map (algebraMap (ZMod p) F)).roots.card = 3 := by
  rw [splits_iff_card_roots.mp (splits_map hcard hdeg hnoroot), natDegree_map, hdeg]

theorem nodup_roots_map (hcard : Nat.card F = p ^ 3) (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) :
    (f.map (algebraMap (ZMod p) F)).roots.Nodup := by
  have hp : p.Prime := Fact.out
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : Fintype F := Fintype.ofFinite F
  have hbig : (X ^ p ^ 3 - X : F[X]).roots = Finset.univ.val := by
    rw [show p ^ 3 = Fintype.card F by rw [← hcard, Nat.card_eq_fintype_card]]
    exact FiniteField.roots_X_pow_card_sub_X F
  exact Multiset.nodup_of_le (roots.le_of_dvd
      (FiniteField.X_pow_card_pow_sub_X_ne_zero F three_ne_zero hp.one_lt)
      (map_dvd_X_pow_pow_sub_X hdeg hnoroot))
    (by rw [hbig]; exact Finset.univ.nodup)

theorem notMem_bot_of_isRoot_map (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) {a : F}
    (ha : (f.map (algebraMap (ZMod p) F)).IsRoot a) : a ∉ (⊥ : Subfield F) := by
  intro hmem
  rw [← SetLike.mem_coe, coe_bot_subfield_eq_range_algebraMap (p := p)] at hmem
  obtain ⟨c, rfl⟩ := hmem
  refine hnoroot c ?_
  have h2 : (algebraMap (ZMod p) F) (f.eval c) = 0 := by
    rw [← eval₂_at_apply, ← eval_map]; exact ha
  exact (map_eq_zero_iff _ (algebraMap (ZMod p) F).injective).mp h2

theorem exists_root_frobenius_orbit (hcard : Nat.card F = p ^ 3) (hmon : f.Monic)
    (hdeg : f.natDegree = 3) (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) :
    ∃ a : F, a ∉ (⊥ : Subfield F) ∧ a ≠ a ^ p ∧ a ^ p ≠ a ^ p ^ 2 ∧ a ^ p ^ 2 ≠ a ∧
      (f.map (algebraMap (ZMod p) F)).roots = {a, a ^ p, a ^ p ^ 2} ∧
      f.map (algebraMap (ZMod p) F)
        = (X - C a) * (X - C (a ^ p)) * (X - C (a ^ p ^ 2)) := by
  have hp : p.Prime := Fact.out
  have : CharP F p := charP_of_algebra_zmod
  have : ExpChar F p := ExpChar.prime hp
  set g := f.map (algebraMap (ZMod p) F) with hg
  have hgmon : g.Monic := hmon.map _
  have hrc : g.roots.card = g.natDegree := splits_iff_card_roots.mp (splits_map hcard hdeg hnoroot)
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp
    (by rw [card_roots_map_eq_three hcard hdeg hnoroot]; norm_num)
  have haroot : g.IsRoot a := (mem_roots hgmon.ne_zero).mp ha
  have hr1 : g.IsRoot (a ^ p) := isRoot_map_pow_char haroot
  have hr2 : g.IsRoot (a ^ p ^ 2) := by
    have h := isRoot_map_pow_char (p := p) (F := F) (f := f) hr1
    rwa [← pow_mul, ← pow_two] at h
  have hnotmem : a ∉ (⊥ : Subfield F) := notMem_bot_of_isRoot_map hnoroot haroot
  have hane : a ≠ a ^ p := fun h =>
    hnotmem ((Subfield.mem_bot_iff_pow_eq_self F p).mpr h.symm)
  have hfrobinj : Function.Injective (fun x : F => x ^ p) := fun x y hxy =>
    frobenius_inj F p (by simpa [frobenius_def] using hxy)
  have h12 : a ^ p ≠ a ^ p ^ 2 := fun h =>
    hane (hfrobinj (by simpa [← pow_mul, ← pow_two] using h))
  have h20 : a ^ p ^ 2 ≠ a := by
    intro h
    refine hane ?_
    have h4 : (a ^ p ^ 2) ^ p = a ^ p := by rw [h]
    rwa [← pow_mul, ← pow_succ, pow_prime_pow_eq_self hp hcard] at h4
  have hroots : g.roots = {a, a ^ p, a ^ p ^ 2} := by
    refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
    · rw [Multiset.le_iff_subset (by simp [hane, h12, h20, Ne.symm])]
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (mem_roots hgmon.ne_zero).mpr haroot
      · exact (mem_roots hgmon.ne_zero).mpr hr1
      · exact (mem_roots hgmon.ne_zero).mpr hr2
    · rw [card_roots_map_eq_three hcard hdeg hnoroot]; simp
  refine ⟨a, hnotmem, hane, h12, h20, hroots, ?_⟩
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hgmon hrc
  rw [hroots] at hprod
  rw [← hprod]
  simp [Multiset.insert_eq_cons, mul_assoc]

theorem exists_rootSet_eq (hcard : Nat.card F = p ^ 3) (hmon : f.Monic) (hdeg : f.natDegree = 3)
    (hnoroot : ∀ c : ZMod p, ¬ f.IsRoot c) :
    ∃ a : F, a ∉ (⊥ : Subfield F) ∧ f.rootSet F = {a, a ^ p, a ^ p ^ 2} := by
  classical
  obtain ⟨a, hnotmem, -, -, -, hroots, -⟩ :=
    exists_root_frobenius_orbit hcard hmon hdeg hnoroot
  refine ⟨a, hnotmem, ?_⟩
  rw [rootSet_def, aroots_def, hroots]
  simp [Multiset.insert_eq_cons]

end

end CFSG.FeitThompson
