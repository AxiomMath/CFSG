module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjType
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

@[expose] def e7Theta0 : Fin Tag.E7.rank → ℤ := ![2, 2, 3, 4, 3, 2, 1]

abbrev e7node10 : Fin Tag.E7.rank := ⟨0, by decide⟩

@[expose] def e7ThetaWords : List (List (Fin Tag.E7.rank)) :=
  ([[2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0], [3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
    [3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [4, 5, 6, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
    [5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0], [6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0],
    [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]] : List (List (Fin 7)))

theorem e7_words_check : ∀ j : Fin Tag.E7.rank,
    (e7ThetaWords.getD j []).foldr (reflect .E7) e7Theta0 = Pi.single j 1 := by
  decide +kernel

theorem e7_check_two : ∀ i : Fin Tag.E7.rank,
    List.ofFn (Pi.single i 1 + Pi.single i 1 : Fin Tag.E7.rank → ℤ) ∉ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7_check_string : ∀ k < Tag.E7.rootCount, ∀ i : Fin Tag.E7.rank,
    (Tag.rootCertificate Tag.E7).root k = Pi.single i 1 ∨
      (Tag.rootCertificate Tag.E7).root k = -Pi.single i 1 ∨
        (Tag.stringData Tag.E7).up k i + (Tag.stringData Tag.E7).down k i ≤ 1 := by
  decide +kernel

theorem e7_check_succ : ∀ k < Tag.E7.rootCount, (Tag.rootCertificate Tag.E7).root k = e7Theta0 ∨
    (∃ j : Fin Tag.E7.rank, (Tag.rootCertificate Tag.E7).root k = -Pi.single j 1) ∨
      ∃ i : Fin Tag.E7.rank, (Tag.rootCertificate Tag.E7).root k ≠ Pi.single i 1 ∧
        (Tag.rootCertificate Tag.E7).root k ≠ -Pi.single i 1 ∧
          1 ≤ (Tag.stringData Tag.E7).up k i := by
  decide +kernel

theorem adjHyp_E7 : AdjHyp .E7 e7Theta0 :=
  AdjHyp.of_checks e7_check_two e7_check_string e7_check_succ

theorem e7_theta_mem : List.ofFn e7Theta0 ∈ Tag.E7.artifactRoots := by decide +kernel

theorem e7_check_not_succ : ∀ i : Fin Tag.E7.rank,
    List.ofFn (e7Theta0 + Pi.single i 1) ∉ Tag.E7.artifactRoots := by decide +kernel

theorem e7_check_sub : List.ofFn (e7Theta0 - Pi.single e7node10 1) ∈ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7_check_ne : (∀ i : Fin Tag.E7.rank, e7Theta0 ≠ Pi.single i 1) ∧
    (∀ i : Fin Tag.E7.rank, e7Theta0 ≠ -Pi.single i 1) ∧
    (e7Theta0 - Pi.single e7node10 1 ≠ Pi.single e7node10 1) ∧
    (e7Theta0 - Pi.single e7node10 1 ≠ -Pi.single e7node10 1) := by
  decide +kernel

theorem e7_check_reflect :
    (∀ i : Fin Tag.E7.rank, i ≠ e7node10 → reflect .E7 i e7Theta0 = e7Theta0) ∧
    reflect .E7 e7node10 e7Theta0 = e7Theta0 - Pi.single e7node10 1 := by
  decide +kernel

theorem e7_check_weight : ∀ s : Fin Tag.E7.rank,
    ∑ j, Tag.E7.cartan s j * e7Theta0 j = if s = e7node10 then 1 else 0 := by
  decide +kernel

theorem adjTop_E7 : AdjTop .E7 e7Theta0 e7node10 where
  root := isRoot_iff_mem_artifactRoots.2 e7_theta_mem
  hyp := adjHyp_E7
  not_succ i := fun h => e7_check_not_succ i (isRoot_iff_mem_artifactRoots.1 h)
  ne_single := e7_check_ne.1
  ne_neg := e7_check_ne.2.1
  reflect_ne := e7_check_reflect.1
  reflect_node := e7_check_reflect.2
  root_sub := isRoot_iff_mem_artifactRoots.2 e7_check_sub
  sub_ne_single := e7_check_ne.2.2.1
  sub_ne_neg := e7_check_ne.2.2.2
  weight := e7_check_weight

@[expose] def e7A : Fin 7 → Fin 7 → ℕ :=
  ![![2, 0, 1, 0, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 0], ![1, 0, 2, 1, 0, 0, 0],
    ![0, 1, 1, 2, 1, 0, 0], ![0, 0, 0, 1, 2, 1, 0], ![0, 0, 0, 0, 1, 2, 1],
    ![0, 0, 0, 0, 0, 1, 2]]

theorem e7_natAbs_cartan : ∀ i j : Fin 7, (Tag.E7.cartan i j).natAbs = e7A i j := by
  decide +kernel

@[expose] def e7c0 : Fin Tag.E7.rank → ℕ := ![0, 1, 0, 0, 1, 0, 1]

theorem e7_c0_ker : ∀ i : Fin Tag.E7.rank, (∑ j, e7A j i * e7c0 j) % 2 = 0 := by decide +kernel

theorem cartan7_mod_two_ker {F : Type} [Field F] [CharP F 2] (x : Fin 7 → F)
    (hx : ∀ i, ∑ j, ((Tag.E7.cartan j i).natAbs : F) * x j = 0) :
    ∀ j, x j = (e7c0 j : F) * x 1 := by
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hA : ∀ i j : Fin 7, (((Tag.E7.cartan j i).natAbs : ℕ) : F) = (e7A j i : F) := by
    intro i j
    rw [e7_natAbs_cartan j i]
  have hx' : ∀ i, ∑ j, (e7A j i : F) * x j = 0 := fun i => by
    rw [← hx i]
    exact Finset.sum_congr rfl fun j _ => by rw [hA]
  have e0 := hx' 0
  have e1 := hx' 1
  have e2 := hx' 2
  have e3 := hx' 3
  have e4 := hx' 4
  have e5 := hx' 5
  have e6 := hx' 6
  simp [Fin.sum_univ_succ, e7A] at e0 e1 e2 e3 e4 e5 e6
  intro j
  fin_cases j
  · simp [e7c0]
    linear_combination e2 + e4 + e6 - (x 2 + x 3 + x 4 + x 5 + x 6) * htwo
  · simp [e7c0]
  · simp [e7c0]
    linear_combination e0 - (x 0) * htwo
  · simp [e7c0]
    linear_combination e4 + e6 - (x 4 + x 5 + x 6) * htwo
  · simp [e7c0]
    linear_combination e0 + e3 - (x 0 + x 2 + x 3 + x 1) * htwo
  · simp [e7c0]
    linear_combination e6 - (x 6) * htwo
  · simp [e7c0]
    linear_combination e0 + e3 + e5 - (x 0 + x 2 + x 3 + x 4 + x 5 + x 1) * htwo

section Mod

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] def e7Hc : RootModule .E7 K := ∑ j : Fin Tag.E7.rank, (e7c0 j : K) • hVec .E7 K j

theorem e7_c0_cartan_cast (i : Fin Tag.E7.rank) : ∑ j : Fin Tag.E7.rank, (e7c0 j : K) * ((Tag.E7.cartan j i).natAbs : K) = 0 := by
  have h : ∑ j : Fin Tag.E7.rank, (e7c0 j : K) * ((Tag.E7.cartan j i).natAbs : K) =
      ((∑ j : Fin Tag.E7.rank, e7A j i * e7c0 j : ℕ) : K) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e7_natAbs_cartan j i, mul_comm]
  rw [h, CharP.cast_eq_zero_iff K 2]
  exact Nat.dvd_of_mod_eq_zero (e7_c0_ker i)

theorem xOp_e7Hc (i : Fin Tag.E7.rank) (c : K) : xOp .E7 K i c (e7Hc K) = e7Hc K := by
  unfold e7Hc
  simp only [map_sum, map_smul, xOp_hVec_eq, smul_add, Finset.sum_add_distrib]
  have : ∑ j : Fin Tag.E7.rank, (e7c0 j : K) • (((Tag.E7.cartan j i).natAbs : K) * c) •
      rootVec .E7 K (Pi.single i 1) = 0 := by
    have key : ∑ j : Fin Tag.E7.rank, (e7c0 j : K) • (((Tag.E7.cartan j i).natAbs : K) * c) •
        rootVec .E7 K (Pi.single i 1) =
        ((∑ j : Fin Tag.E7.rank, (e7c0 j : K) * ((Tag.E7.cartan j i).natAbs : K)) * c) •
          rootVec .E7 K (Pi.single i 1) := by
      simp only [Finset.sum_mul, Finset.sum_smul, smul_smul, mul_assoc]
    rw [key, e7_c0_cartan_cast, zero_mul, zero_smul]
  rw [this, add_zero]

theorem yOp_e7Hc (i : Fin Tag.E7.rank) (c : K) : yOp .E7 K i c (e7Hc K) = e7Hc K := by
  unfold e7Hc
  simp only [map_sum, map_smul, yOp_hVec_eq, smul_add, Finset.sum_add_distrib]
  have : ∑ j : Fin Tag.E7.rank, (e7c0 j : K) • (((Tag.E7.cartan j i).natAbs : K) * c) •
      rootVec .E7 K (-Pi.single i 1) = 0 := by
    have key : ∑ j : Fin Tag.E7.rank, (e7c0 j : K) • (((Tag.E7.cartan j i).natAbs : K) * c) •
        rootVec .E7 K (-Pi.single i 1) =
        ((∑ j : Fin Tag.E7.rank, (e7c0 j : K) * ((Tag.E7.cartan j i).natAbs : K)) * c) •
          rootVec .E7 K (-Pi.single i 1) := by
      simp only [Finset.sum_mul, Finset.sum_smul, smul_smul, mul_assoc]
    rw [key, e7_c0_cartan_cast, zero_mul, zero_smul]
  rw [this, add_zero]

variable (K) in
@[expose] def hcStab : Subgroup (ModGL .E7 K) where
  carrier := {g | (g : Module.End K (RootModule .E7 K)) (e7Hc K) = e7Hc K}
  mul_mem' := fun {a b} ha hb => by
    show (a : Module.End K (RootModule .E7 K)) ((b : Module.End K (RootModule .E7 K)) (e7Hc K)) = _
    have ha' : (a : Module.End K (RootModule .E7 K)) (e7Hc K) = e7Hc K := ha
    have hb' : (b : Module.End K (RootModule .E7 K)) (e7Hc K) = e7Hc K := hb
    rw [hb', ha']
  one_mem' := rfl
  inv_mem' := fun {g} hg => by
    have hg' : (g : Module.End K (RootModule .E7 K)) (e7Hc K) = e7Hc K := hg
    show ((g⁻¹ : ModGL .E7 K) : Module.End K (RootModule .E7 K)) (e7Hc K) = _
    calc ((g⁻¹ : ModGL .E7 K) : Module.End K (RootModule .E7 K)) (e7Hc K) =
        ((g⁻¹ : ModGL .E7 K) : Module.End K (RootModule .E7 K))
          ((g : Module.End K (RootModule .E7 K)) (e7Hc K)) := by rw [hg']
      _ = e7Hc K := by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]

theorem adjointGroup_le_hcStab : adjointGroup .E7 K ≤ hcStab K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · show (g : Module.End K (RootModule .E7 K)) (e7Hc K) = e7Hc K
    rw [hg]; exact xOp_e7Hc i c
  · show (g : Module.End K (RootModule .E7 K)) (e7Hc K) = e7Hc K
    rw [hg]; exact yOp_e7Hc i c

theorem adjRep_e7Hc (g : ↥(adjointGroup .E7 K)) : adjRep .E7 K g (e7Hc K) = e7Hc K :=
  adjointGroup_le_hcStab g.2

variable (K) in
@[expose] def e7Z : Submodule K (RootModule .E7 K) := Submodule.span K {e7Hc K}

theorem e7Z_le_comap (g : ↥(adjointGroup .E7 K)) : e7Z K ≤ (e7Z K).comap (adjRep .E7 K g) := by
  refine Submodule.span_le.2 ?_
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  show adjRep .E7 K g (e7Hc K) ∈ e7Z K
  rw [adjRep_e7Hc]
  exact Submodule.subset_span rfl

variable (K) in
@[expose] def adj132 : Representation K ↥(adjointGroup .E7 K) (RootModule .E7 K ⧸ e7Z K) :=
  (adjRep .E7 K).quotient (e7Z K) e7Z_le_comap

theorem adj132_apply (g : ↥(adjointGroup .E7 K)) (v : RootModule .E7 K) :
    adj132 K g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (adjRep .E7 K g v) := rfl

@[expose] def adj132Y : RootModule .E7 K ⧸ e7Z K :=
  Submodule.Quotient.mk (rootVec .E7 K e7Theta0)

theorem coord_e7Hc_inl (k : Fin Tag.E7.rank) : (e7Hc K) (Sum.inl k) = (e7c0 k : K) := by
  unfold e7Hc
  rw [Finsupp.coe_finsetSum, Finset.sum_apply]
  simp [hVec_inl]

theorem coord_e7Z_inr {z : RootModule .E7 K} (hz : z ∈ e7Z K) (α : {v : Fin Tag.E7.rank → ℤ // IsRoot .E7 v}) :
    z (Sum.inr α) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  unfold e7Hc
  rw [Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
  have hh : ∀ j, (hVec .E7 K j : RootModule .E7 K) (Sum.inr α) = 0 := fun j => by
    unfold hVec
    simp [Finsupp.single_apply]
  simp [hh]

theorem adj132Y_ne_zero : (adj132Y : RootModule .E7 K ⧸ e7Z K) ≠ 0 := by
  intro h
  have hz := (Submodule.Quotient.mk_eq_zero _).1 h
  have := coord_e7Z_inr hz ⟨e7Theta0, adjTop_E7.root⟩
  rw [rootVec_eq_single adjTop_E7.root, Finsupp.single_eq_same] at this
  exact one_ne_zero this

end Mod

section Simple

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem xC_mem_U7 (i : Fin Tag.E7.rank) : xC .E7 K i 1 ∈ (e7Datum (K := K)).U :=
  (e7Datum (K := K)).X_le i (xC_mem_X (hw := exists_weyl_neg_E7) i 1)

theorem coord_inl_of_mem_Z {z : RootModule .E7 K} (hz : z ∈ e7Z K) :
    ∃ κ : K, ∀ k : Fin Tag.E7.rank, z (Sum.inl k) = κ * (e7c0 k : K) := by
  obtain ⟨κ, rfl⟩ := Submodule.mem_span_singleton.1 hz
  refine ⟨κ, fun k => ?_⟩
  rw [Finsupp.smul_apply, coord_e7Hc_inl, smul_eq_mul]

abbrev e7i1 : Fin Tag.E7.rank := ⟨1, by decide⟩

theorem e7_c0_i1 : e7c0 e7i1 = 1 := by decide +kernel

theorem exists_k0 : ∀ i : Fin Tag.E7.rank, ∃ k : Fin Tag.E7.rank, k ≠ i ∧ e7c0 k = 1 := by
  decide +kernel

theorem fixU_le_line132 {x : RootModule .E7 K ⧸ e7Z K}
    (hx : x ∈ (e7Datum (K := K)).fixU (adj132 K)) : ∃ c : K, x = c • adj132Y := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hD : ∀ i, Dop .E7 K i v = 0 := by
    intro i
    have h := ((e7Datum (K := K)).mem_fixU _).1 hx _ (xC_mem_U7 i)
    rw [adj132_apply, adjRep_xC] at h
    have hz : Dop .E7 K i v ∈ e7Z K := (Submodule.Quotient.eq _).1 h
    obtain ⟨κ, hκ⟩ := coord_inl_of_mem_Z hz
    obtain ⟨k0, hk0, hc0⟩ := exists_k0 i
    have h1 := hκ k0
    rw [Dop_inl adjHyp_E7 i v k0, if_neg hk0, hc0] at h1
    have hκ0 : κ = 0 := by simpa using h1.symm
    ext b
    rcases b with k | α
    · rw [hκ k, hκ0, zero_mul]; rfl
    · exact coord_e7Z_inr hz α
  have hdec := eq_decomp_of_Dop adjHyp_E7 adjTop_E7.root hD
  have hker := cartan7_mod_two_ker (fun j => v (Sum.inl j)) (cartan_cond_of_Dop adjHyp_E7 hD)
  refine ⟨coordR v e7Theta0, ?_⟩
  have hsum : ∑ j : Fin Tag.E7.rank, v (Sum.inl j) • hVec .E7 K j =
      v (Sum.inl e7i1) • e7Hc K := by
    unfold e7Hc
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hker j, smul_smul, mul_comm]
    rfl
  have hz0 : (Submodule.Quotient.mk (e7Hc K) : RootModule .E7 K ⧸ e7Z K) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span rfl)
  have : Submodule.Quotient.mk v = (coordR v e7Theta0 • Submodule.Quotient.mk (rootVec .E7 K e7Theta0) :
      RootModule .E7 K ⧸ e7Z K) := by
    conv_lhs => rw [hdec, hsum]
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, hz0,
      smul_zero, add_zero]
  exact this

instance nontrivialQuotE7 : Nontrivial (RootModule .E7 K ⧸ e7Z K) :=
  ⟨⟨adj132Y, 0, adj132Y_ne_zero⟩⟩

theorem adj132Y_mem_fixU : (adj132Y : RootModule .E7 K ⧸ e7Z K) ∈
    (e7Datum (K := K)).fixU (adj132 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    ((e7Datum (K := K)).fixU_ne_bot (p := 2) (adj132 K))
  obtain ⟨c, rfl⟩ := fixU_le_line132 hx
  have hc : c ≠ 0 := by rintro rfl; exact hx0 (zero_smul _ _)
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem orbitSpan_adj132 : orbitSpan (adj132 K) (adj132Y : RootModule .E7 K ⧸ e7Z K) = ⊤ := by
  have h := orbitSpan_adjRep (K := K) adjTop_E7.root (words := fun j => e7ThetaWords.getD j [])
    e7_words_check
  refine (Submodule.eq_top_iff').2 fun w => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hv : v ∈ spanθ (K := K) e7Theta0 := by rw [h]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, rfl⟩ := hv
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => rw [Submodule.Quotient.mk_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Submodule.Quotient.mk_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ c ha

variable (K) in
@[expose] def adjChi132 (g : ↥(adjointGroup .E7 K)) : K :=
  coordR (adjRep .E7 K g (rootVec .E7 K e7Theta0)) e7Theta0

theorem adjChi132_dC (s : Fin Tag.E7.rank) (t : Kˣ) :
    adjChi132 K (dC .E7 K s t) = ((t ^ (if s = e7node10 then (1 : ℤ) else 0) : Kˣ) : K) := by
  unfold adjChi132
  rw [adjRep_dC_theta adjTop_E7 s t, coordR_smul, coordR_rootVec adjTop_E7.root, if_pos rfl,
    mul_one]

theorem adj132_H (h : ↥(adjointGroup .E7 K)) (hh : h ∈ (e7Datum (K := K)).H) :
    adj132 K h adj132Y = adjChi132 K h • adj132Y := by
  obtain ⟨c, hc⟩ := fixU_le_line132 ((e7Datum (K := K)).act_H_mem_fixU (adj132 K) hh
    adj132Y_mem_fixU)
  have h1 : adj132 K h adj132Y = Submodule.Quotient.mk (adjRep .E7 K h (rootVec .E7 K e7Theta0)) :=
    rfl
  have h2 : adjRep .E7 K h (rootVec .E7 K e7Theta0) - c • rootVec .E7 K e7Theta0 ∈ e7Z K := by
    have e : (Submodule.Quotient.mk (adjRep .E7 K h (rootVec .E7 K e7Theta0)) :
        RootModule .E7 K ⧸ e7Z K) = Submodule.Quotient.mk (c • rootVec .E7 K e7Theta0) :=
      h1.symm.trans (hc.trans (Submodule.Quotient.mk_smul _ _ _).symm)
    exact (Submodule.Quotient.eq _).1 e
  have h3 := coord_e7Z_inr h2 ⟨e7Theta0, adjTop_E7.root⟩
  have h5 : (rootVec .E7 K e7Theta0 : RootModule .E7 K) (Sum.inr ⟨e7Theta0, adjTop_E7.root⟩) = 1 := by
    rw [rootVec_eq_single adjTop_E7.root]
    exact Finsupp.single_eq_same
  have : adjChi132 K h = c := by
    unfold adjChi132
    have h4 : coordR (adjRep .E7 K h (rootVec .E7 K e7Theta0)) e7Theta0 =
        (adjRep .E7 K h (rootVec .E7 K e7Theta0)) (Sum.inr ⟨e7Theta0, adjTop_E7.root⟩) := by
      simp [coordR, adjTop_E7.root]
    rw [h4]
    rw [Finsupp.sub_apply, Finsupp.smul_apply, h5, smul_eq_mul, mul_one] at h3
    exact sub_eq_zero.1 h3
  rw [this, hc]

theorem adj132_heckeT (s : Fin Tag.E7.rank) [Fintype K] :
    (e7Datum (K := K)).heckeT (adj132 K) s adj132Y =
      Submodule.Quotient.mk (∑ c : K, adjRep .E7 K (xC .E7 K s c * nC .E7 K s)
        (rootVec .E7 K e7Theta0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold e7Datum
  rw [heckeT_chevDatum]
  exact (map_sum (Submodule.mkQ (e7Z K)) _ _).symm

theorem adj132_isChevType :
    IsChevType .E7 K 2 exists_weyl_neg_E7 (adj132 K) adj132Y (adjChi132 K)
      (Finset.univ.erase e7node10) := by
  have := Fintype.ofFinite K
  refine ⟨adj132Y_mem_fixU, adj132Y_ne_zero, adj132_H, fun s => ?_⟩
  by_cases hs : s = e7node10
  · subst hs
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := h
    have h1' : ∀ u : Kˣ, (u : K) = 1 := fun u => by
      have := h1 u
      rwa [adjChi132_dC, if_pos rfl, zpow_one] at this
    have h3 : (e7Datum (K := K)).heckeT (adj132 K) e7node10 adj132Y =
        (∑ c : K, c) • adj132Y := by
      rw [adj132_heckeT, adj_heckeSum_node adjTop_E7]
      rfl
    have h4 : (∑ c : K, c) • (adj132Y : RootModule .E7 K ⧸ e7Z K) = 0 := h3.symm.trans h2
    rw [sum_eq_one_of_units_eq_one h1', one_smul] at h4
    exact adj132Y_ne_zero h4
  · refine ⟨fun _ => ⟨fun u => ?_, ?_⟩, fun _ => Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩⟩
    · rw [adjChi132_dC, if_neg hs, zpow_zero]
      rfl
    · have h5 : (e7Datum (K := K)).heckeT (adj132 K) s adj132Y = 0 := by
        rw [adj132_heckeT, adj_heckeSum_of_ne adjTop_E7 hs]
        rfl
      exact h5

theorem e7Hc_ne_zero : e7Hc K ≠ 0 := by
  intro h
  have := congrArg (fun v : RootModule .E7 K => v (Sum.inl e7i1)) h
  simp only [coord_e7Hc_inl, e7_c0_i1, Finsupp.zero_apply] at this
  simp at this

theorem finrank_adj132 : Module.finrank K (RootModule .E7 K ⧸ e7Z K) = 132 := by
  have h1 := Submodule.finrank_quotient_add_finrank (e7Z K)
  have h2 : Module.finrank K (e7Z K) = 1 := finrank_span_singleton e7Hc_ne_zero
  have h3 : Module.finrank K (RootModule .E7 K) = 133 := by
    rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_fin,
      Nat.card_eq_fintype_card (α := {v : Fin Tag.E7.rank → ℤ // IsRoot .E7 v}), card_isRoot]
    rfl
  omega

end Simple

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
