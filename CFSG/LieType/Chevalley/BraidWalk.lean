module

public import CFSG.Blueprint.ChevalleyWeyl
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootWalk

open CFSG.Blueprint.Chevalley CoxeterSystem

variable {τ : Tag} {R : Type*} [CommRing R]

theorem rootCertificate_basis_table :
    τ.rank ≤ τ.rootCertificate.roots.length ∧
      (∀ j : Fin τ.rank, τ.rootCertificate.root j = Pi.single j 1) ∧
      ∀ k < τ.rootCertificate.roots.length, ∀ i : Fin τ.rank,
        τ.rootCertificate.image k i < τ.rootCertificate.roots.length ∧
          τ.rootCertificate.root (τ.rootCertificate.image k i) =
            reflect τ i (τ.rootCertificate.root k) := by
  have h := τ.rootCertificate_check
  simp only [RootCertificate.check, RootCertificate.checkBasis, RootCertificate.checkTable,
    Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, List.mem_range,
    true_implies] at h
  exact ⟨h.1.1.1, fun j => RootCertificate.eq_of_ofFn_beq (h.1.1.2 j),
    fun k hk i => ⟨(h.2 k hk i).1, RootCertificate.eq_of_ofFn_beq (h.2 k hk i).2⟩⟩

theorem rootCertificate_image_lt {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : τ.rootCertificate.image k i < τ.rootCertificate.roots.length :=
  (rootCertificate_basis_table.2.2 k hk i).1

theorem rootCertificate_root_image {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) :
    τ.rootCertificate.root (τ.rootCertificate.image k i) =
      reflect τ i (τ.rootCertificate.root k) :=
  (rootCertificate_basis_table.2.2 k hk i).2

theorem isRoot_rootCertificate_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    IsRoot τ (τ.rootCertificate.root k) :=
  RootCertificate.isRoot_root τ.rootCertificate_check k hk

theorem rootCertificate_root_injOn {k k' : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (hk' : k' < τ.rootCertificate.roots.length)
    (h : τ.rootCertificate.root k = τ.rootCertificate.root k') : k = k' := by
  have hn := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 hk) (List.mem_range.2 hk') (by rw [h])

@[expose] def downAt (τ : Tag) (k : ℕ) (i : Fin τ.rank) : ℕ :=
  if k = i then 2 else if k = τ.rootCertificate.image i i then 0 else τ.stringData.down k i

theorem stringDown_rootCertificate_root {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : stringDown τ i (τ.rootCertificate.root k) = downAt τ k i := by
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have hi : (i : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le i.2 hr
  have hneg : τ.rootCertificate.root (τ.rootCertificate.image i i) = -Pi.single i 1 := by
    rw [rootCertificate_root_image hi, hb, reflect_single_self]
  unfold downAt
  split_ifs with h₁ h₂
  · rw [h₁, hb, stringDown_single]
  · rw [h₂, hneg, stringDown_neg_single]
  have hne : τ.rootCertificate.root k ≠ Pi.single i 1 := fun h =>
    h₁ (rootCertificate_root_injOn hk hi (h.trans (hb i).symm))
  have hne' : τ.rootCertificate.root k ≠ -Pi.single i 1 := fun h =>
    h₂ (rootCertificate_root_injOn hk (rootCertificate_image_lt hi i) (h.trans hneg.symm))
  obtain ⟨-, hS⟩ := StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk
    i hne hne'
  obtain ⟨-, hΦ⟩ := isRoot_add_smul_single_iff (isRoot_rootCertificate_root hk) i hne hne'
  have h1 := (hS _).1 ((hΦ (-(stringDown τ i (τ.rootCertificate.root k) : ℤ))).2
    ⟨le_rfl, by omega⟩)
  have h2 := (hΦ _).1 ((hS (-(τ.stringData.down k i : ℤ))).2 ⟨le_rfl, by omega⟩)
  omega

@[expose] def walk (τ : Tag) (ω : List (Fin τ.rank)) (k : ℕ) : ℕ × ℕ :=
  ω.foldr (fun i p => (τ.rootCertificate.image p.1 i, (p.2 + downAt τ p.1 i) % 2)) (k, 0)

theorem walk_nil (k : ℕ) : walk τ [] k = (k, 0) :=
  rfl

theorem walk_cons (i : Fin τ.rank) (ω : List (Fin τ.rank)) (k : ℕ) :
    walk τ (i :: ω) k = (τ.rootCertificate.image (walk τ ω k).1 i,
      ((walk τ ω k).2 + downAt τ (walk τ ω k).1 i) % 2) :=
  rfl

theorem walk_fst_lt (ω : List (Fin τ.rank)) {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    (walk τ ω k).1 < τ.rootCertificate.roots.length := by
  induction ω with
  | nil => exact hk
  | cons i ω ih => exact rootCertificate_image_lt ih i

variable (R) in
theorem prod_weylElt_rootVec_root (ω : List (Fin τ.rank)) {k : ℕ}
    (hk : k < τ.rootCertificate.roots.length) :
    (((ω.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) (rootVec τ R (τ.rootCertificate.root k)) =
      ((-1 : R) ^ (walk τ ω k).2) • rootVec τ R (τ.rootCertificate.root (walk τ ω k).1) := by
  induction ω with
  | nil => simp [walk_nil]
  | cons i ω ih =>
    have hlt := walk_fst_lt ω hk
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, map_smul,
      weylElt_rootVec i 1 (isRoot_rootCertificate_root hlt), one_zpow, Units.val_one, mul_one,
      stringDown_rootCertificate_root hlt, ← rootCertificate_root_image hlt, smul_smul,
      ← pow_add, walk_cons,
      neg_one_pow_eq_pow_mod_two (R := R) (n := (walk τ ω k).2 + downAt τ (walk τ ω k).1 i)]

variable (R) in
@[expose] noncomputable def hVecSum (c : Fin τ.rank → ℤ) : RootModule τ R :=
  ∑ j, (c j : R) • hVec τ R j

theorem hVecSum_single (k : Fin τ.rank) : hVecSum R (Pi.single k 1) = hVec τ R k := by
  simp [hVecSum, Pi.single_apply]

@[expose] def hStep (τ : Tag) (i : Fin τ.rank) (c : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  c - (∑ j, ((τ.cartan j i).natAbs : ℤ) * c j) • Pi.single i 1

theorem weylElt_hVecSum (i : Fin τ.rank) (t : Rˣ) (c : Fin τ.rank → ℤ) :
    (weylElt τ R i t : Module.End R (RootModule τ R)) (hVecSum R c) =
      hVecSum R (hStep τ i c) := by
  simp only [hVecSum, hStep, map_sum, map_smul, weylElt_hVec, smul_sub, Finset.sum_sub_distrib,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, sub_smul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Int.cast_ite, Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  congr 1
  rw [Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Int.cast_mul, Int.cast_natCast, mul_comm]

variable (R) in
theorem prod_weylElt_hVecSum (ω : List (Fin τ.rank)) (c : Fin τ.rank → ℤ) :
    (((ω.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) (hVecSum R c) =
      hVecSum R (ω.foldr (hStep τ) c) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, weylElt_hVecSum,
      List.foldr_cons]

@[expose] def braidLength (c : ℤ) : ℕ :=
  if c = 0 then 2 else if c = 1 then 3 else if c = 2 then 4 else if c = 3 then 6 else
    if c = 4 then 1 else 0

theorem coxeterOrder_eq_braidLength (c : ℤ) : TauCeti.coxeterOrder c = braidLength c := by
  unfold braidLength
  split_ifs with h₀ h₁ h₂ h₃ h₄
  · rw [h₀, TauCeti.coxeterOrder_zero]
  · rw [h₁, TauCeti.coxeterOrder_one]
  · rw [h₂, TauCeti.coxeterOrder_two]
  · rw [h₃, TauCeti.coxeterOrder_three]
  · rw [h₄, TauCeti.coxeterOrder_four]
  · exact TauCeti.coxeterOrder_eq_zero_iff.2 (by simp [h₀, h₁, h₂, h₃, h₄])

@[expose] def braidCheckPair (τ : Tag) (i j : Fin τ.rank) : Bool :=
  ((List.finRange τ.rank).all fun k =>
      List.ofFn ((alternatingWord i j (braidLength (τ.cartan i j * τ.cartan j i))).foldr
          (hStep τ) (Pi.single k 1)) ==
        List.ofFn ((alternatingWord j i (braidLength (τ.cartan i j * τ.cartan j i))).foldr
          (hStep τ) (Pi.single k 1))) &&
    (List.range τ.rootCertificate.roots.length).all fun k =>
      decide (walk τ (alternatingWord i j (braidLength (τ.cartan i j * τ.cartan j i))) k =
        walk τ (alternatingWord j i (braidLength (τ.cartan i j * τ.cartan j i))) k)

@[expose] def braidCheck (τ : Tag) : Bool :=
  (List.finRange τ.rank).all fun i => (List.finRange τ.rank).all fun j =>
    !decide (i < j) || braidCheckPair τ i j

theorem g2_braidCheck : braidCheck .G2 = true := by decide +kernel

theorem f4_braidCheck : braidCheck .F4 = true := by decide +kernel

theorem d4_braidCheck : braidCheck .D4 = true := by decide +kernel

theorem e6_braidCheck : braidCheck .E6 = true := by decide +kernel

theorem e7_braidCheck : braidCheck .E7 = true := by decide +kernel

theorem e8_braidCheck : braidCheck .E8 = true := by decide +kernel

theorem braidCheck_eq_true : ∀ τ : Tag, braidCheck τ = true
  | .G2 => g2_braidCheck
  | .F4 => f4_braidCheck
  | .D4 => d4_braidCheck
  | .E6 => e6_braidCheck
  | .E7 => e7_braidCheck
  | .E8 => e8_braidCheck

theorem braidCheckPair_of_lt {i j : Fin τ.rank} (hij : i < j) :
    (∀ k : Fin τ.rank,
      (alternatingWord i j (braidLength (τ.cartan i j * τ.cartan j i))).foldr (hStep τ)
          (Pi.single k 1) =
        (alternatingWord j i (braidLength (τ.cartan i j * τ.cartan j i))).foldr (hStep τ)
          (Pi.single k 1)) ∧
      ∀ k < τ.rootCertificate.roots.length,
        walk τ (alternatingWord i j (braidLength (τ.cartan i j * τ.cartan j i))) k =
          walk τ (alternatingWord j i (braidLength (τ.cartan i j * τ.cartan j i))) k := by
  have h := braidCheck_eq_true τ
  simp only [braidCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  have hp := (h i j).resolve_left (not_not.2 hij)
  simp only [braidCheckPair, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, List.mem_range, decide_eq_true_eq] at hp
  exact ⟨fun k => List.ofFn_injective (eq_of_beq (hp.1 k)), hp.2⟩

end CFSG.LieType.Chevalley.RootWalk
