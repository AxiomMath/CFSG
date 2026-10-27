module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Weyl

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def spWeylGroup (k : Fin r) : Subgroup (StatedSp r K) :=
  unipotent r K ⊔ Subgroup.closure {weylRep K k}

theorem unipotent_le_spWeylGroup (k : Fin r) : unipotent r K ≤ spWeylGroup K k := le_sup_left

theorem weylRep_mem_spWeylGroup (k : Fin r) : weylRep K k ∈ spWeylGroup K k :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))

theorem rootSubgroup_neg_le_spWeylGroup (k : Fin r) :
    rootSubgroup K (-simpleRootVec r k) ≤ spWeylGroup K k := by
  have h1 := map_conj_rootSubgroup (weylRep K k) (isLinePerm_weylRep (K := K) k) (simpleRootVec r k)
  rw [epsAct_simpleRefl_simpleRootVec] at h1
  rw [← h1]
  rintro _ ⟨u, hu, rfl⟩
  have hn := weylRep_mem_spWeylGroup (K := K) k
  exact mul_mem (mul_mem hn (unipotent_le_spWeylGroup k
    (rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k) hu))) (inv_mem hn)

theorem torus_conj_mem_rootSubgroup {t : StatedSp r K} (ht : t ∈ torus r K) {α : Fin r → ℤ}
    {x : StatedSp r K} (hx : x ∈ rootSubgroup K α) : t * x * t⁻¹ ∈ rootSubgroup K α := by
  have h := (root_transport (K := K) (r := r)).2.1 t ht α
  have : (MulAut.conj t) x ∈ (rootSubgroup K α).map (MulAut.conj t).toMonoidHom := ⟨x, hx, rfl⟩
  rw [h] at this
  exact this

theorem torus_conj_weylRep_mem (k : Fin r) {t : StatedSp r K} (ht : t ∈ torus r K) :
    t * weylRep K k * t⁻¹ ∈ spWeylGroup K k := by
  have hpos : ∀ s : K, t * pairRootElt (inl_ne_simpleSnd k) s * t⁻¹ ∈ spWeylGroup K k := by
    intro s
    refine unipotent_le_spWeylGroup k (rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k)
      (torus_conj_mem_rootSubgroup ht ?_))
    rw [← rootVec_simpleSnd]
    exact pairRootElt_mem_rootSubgroup _ _
  have hneg : t * pairRootElt (inl_ne_simpleSnd k).symm (-1 : K) * t⁻¹ ∈ spWeylGroup K k := by
    refine rootSubgroup_neg_le_spWeylGroup k (torus_conj_mem_rootSubgroup ht ?_)
    rw [← rootVec_simpleSnd, neg_rootVec]
    exact pairRootElt_mem_rootSubgroup _ _
  have e : weylRep K k = pairRootElt (inl_ne_simpleSnd k) (1 : K) *
      pairRootElt (inl_ne_simpleSnd k).symm (-1 : K) * pairRootElt (inl_ne_simpleSnd k) (1 : K) := rfl
  have hconj : ∀ a b c : StatedSp r K,
      t * (a * b * c) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) * (t * c * t⁻¹) := by
    intro a b c
    group
  rw [e, hconj]
  exact mul_mem (mul_mem (hpos 1) hneg) (hpos 1)

theorem map_conj_spWeylGroup_le (k : Fin r) {t : StatedSp r K} (ht : t ∈ torus r K) :
    (spWeylGroup K k).map (MulAut.conj t).toMonoidHom ≤ spWeylGroup K k := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hU : t * u * t⁻¹ ∈ unipotent r K :=
      (Subgroup.normal_subgroupOf_iff unipotent_le_borelSubgroup).mp
        unipotent_subgroupOf_borelSubgroup_normal u t hu (torus_le_borelSubgroup ht)
    exact unipotent_le_spWeylGroup k hU
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact torus_conj_weylRep_mem k ht

theorem torus_le_normalizer_spWeylGroup (k : Fin r) :
    torus r K ≤ Subgroup.normalizer (spWeylGroup K k : Set (StatedSp r K)) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact map_conj_spWeylGroup_le k hh ⟨x, hx, rfl⟩
  · have h2 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ ∈ spWeylGroup K k :=
      map_conj_spWeylGroup_le k ((torus r K).inv_mem hh) ⟨h * x * h⁻¹, hx, rfl⟩
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [e] at h2

theorem torus_commute {a b : StatedSp r K} (ha : a ∈ torus r K) (hb : b ∈ torus r K) :
    a * b = b * a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem borelSubgroup_le_sup_torus : borelSubgroup r K ≤ unipotent r K ⊔ torus r K := by
  intro b hb
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_unipotent_mul_torus hb
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ht)

end Weyl

section Solvable

variable {r : ℕ} {K : Type} [Field K]

theorem isSolvable_borelSubgroup [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    Group.IsSolvable (borelSubgroup r K) := by
  obtain ⟨k, hk⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsPGroup 2 (unipotent r K) :=
    IsPGroup.of_card (n := k * r ^ 2) (by rw [card_unipotent, hk, pow_mul])
  have : Finite (unipotent r K) := inferInstance
  have : Group.IsSolvable (unipotent r K) := by
    have := hV.isNilpotent
    infer_instance
  have hV' : Group.IsSolvable ((unipotent r K).subgroupOf (borelSubgroup r K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe unipotent_le_borelSubgroup).toMonoidHom)
      (MulEquiv.injective _)
  refine Group.isSolvable_of_ker_le_range
    ((unipotent r K).subgroupOf (borelSubgroup r K)).subtype (diagHom r K) ?_
  rw [ker_diagHom]
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

end Solvable

section Two

variable {K : Type} [Field K]

variable (K) in
@[expose] def Q2 (j : Fin 2) : Subgroup (StatedSp 2 K) :=
  stabilizer 2 K (flag 2 K ((j : ℕ) + 1))

variable (K) in
@[expose] def H2 (j : Fin 2) : Subgroup (StatedSp 2 K) :=
  spWeylGroup K (Fin.rev j)

theorem flagStabilizer_singleton_sp (i : ℕ) :
    flagStabilizer 2 K {i} = stabilizer 2 K (flag 2 K i) := by
  ext g
  rw [mem_flagStabilizer]
  simp

theorem Q2_eq (j : Fin 2) : Q2 K j = flagStabilizer 2 K {(j : ℕ) + 1} :=
  (flagStabilizer_singleton_sp _).symm

theorem weylRep_mem_flagStabilizer_iff {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 2) (k : Fin 2) :
    weylRep K k ∈ flagStabilizer 2 K I ↔ (k : ℕ) + 1 ∉ I :=
  (subflag_generation (r := 2) (K := K) I hI).2.1 k

theorem weylRep_mem_flagStabilizer_singleton_iff {i : ℕ} (hi : i ≤ 2) (k : Fin 2) :
    weylRep K k ∈ flagStabilizer 2 K {i} ↔ (k : ℕ) + 1 ≠ i := by
  rw [weylRep_mem_flagStabilizer_iff (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    omega)]
  simp

theorem borelSubgroup_eq_flagStabilizer : borelSubgroup 2 K = flagStabilizer 2 K {1, 2} := by
  ext g
  rw [mem_borelSubgroup, mem_flagStabilizer]
  constructor
  · intro h i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    exact h i (by omega) (by omega)
  · intro h i h1 h2
    exact h i (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)

theorem weylRep_not_mem_borelSubgroup (k : Fin 2) : weylRep K k ∉ borelSubgroup 2 K := by
  have hk := k.isLt
  rw [borelSubgroup_eq_flagStabilizer, weylRep_mem_flagStabilizer_iff (fun x hx => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    omega)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_not]
  omega

theorem borelCuts_borelSubgroup : borelCuts K (borelSubgroup 2 K) = {1, 2} := by
  ext i
  constructor
  · rintro ⟨k, rfl, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have := k.isLt
    omega
  · intro hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    exact ⟨⟨i - 1, by omega⟩, by simp; omega, weylRep_not_mem_borelSubgroup _⟩

theorem mem_borelCuts_of_le_Q2 {j : Fin 2} {A : Subgroup (StatedSp 2 K)} (hAQ : A ≤ Q2 K j) :
    (j : ℕ) + 1 ∈ borelCuts K A := by
  have hj := j.isLt
  by_contra hiJ
  have hr : weylRep K j ∈ A := by
    by_contra hr
    exact hiJ ((succ_mem_borelCuts_iff A j).mpr hr)
  have := hAQ hr
  rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by omega)] at this
  exact this rfl

theorem covBy_Q2 (j : Fin 2) : borelSubgroup 2 K ⋖ Q2 K j := by
  have hj := j.isLt
  have hBQ : borelSubgroup 2 K ≤ Q2 K j := by
    rw [Q2_eq]
    exact borelSubgroup_le_flagStabilizer (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      omega)
  refine ⟨lt_of_le_of_ne hBQ fun h => ?_, fun A hBA hAQ => ?_⟩
  · have h1 : weylRep K (Fin.rev j) ∈ Q2 K j := by
      rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by omega), Fin.val_rev]
      omega
    rw [← h] at h1
    exact weylRep_not_mem_borelSubgroup _ h1
  · have hA := (borel_overgroups A hBA.le).1
    have hiJ := mem_borelCuts_of_le_Q2 hAQ.le
    have hoJ : (Fin.rev j : ℕ) + 1 ∉ borelCuts K A := by
      intro hoJ
      have hJeq : borelCuts K A = {1, 2} := by
        ext x
        constructor
        · intro hx
          have := borelCuts_le A x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          omega
        · intro hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases (by rw [Fin.val_rev]; omega : x = (j : ℕ) + 1 ∨ x = (Fin.rev j : ℕ) + 1) with
            rfl | rfl
          · exact hiJ
          · exact hoJ
      apply hBA.ne
      rw [hA, hJeq, borelSubgroup_eq_flagStabilizer]
    have hJ : borelCuts K A = {(j : ℕ) + 1} := by
      ext x
      constructor
      · intro hx
        have h12 := borelCuts_le A x hx
        rw [Set.mem_singleton_iff]
        by_contra hne
        apply hoJ
        have : x = (Fin.rev j : ℕ) + 1 := by rw [Fin.val_rev]; omega
        rw [← this]
        exact hx
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hiJ
    apply hAQ.ne
    rw [hA, hJ]
    exact (Q2_eq j).symm

theorem Q2_ne : Q2 K 0 ≠ Q2 K 1 := by
  intro h
  have h1 : weylRep K 1 ∈ Q2 K 0 := by
    rw [Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by norm_num)]
    decide
  rw [h, Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by norm_num)] at h1
  exact h1 rfl

theorem contained_in_Q2 {A : Subgroup (StatedSp 2 K)} (hVA : unipotent 2 K ≤ A) (hAt : A ≠ ⊤) :
    A ≤ Q2 K 0 ∨ A ≤ Q2 K 1 := by
  obtain ⟨hle, hiff⟩ :=
    (symplectic_unitriangular_overgroup_subflag_containment (r := 2) (K := K)).1 A hVA
  have hne : borelCuts K A ≠ ∅ := fun he => hAt (hiff.mp he)
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have h12 := borelCuts_le A i hi
  have hAi : A ≤ stabilizer 2 K (flag 2 K i) := by
    rw [← flagStabilizer_singleton_sp]
    intro g hg
    rw [mem_flagStabilizer]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mem_flagStabilizer.mp (hle hg) x hi
  rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
  · exact Or.inl hAi
  · exact Or.inr hAi

theorem Q2_le_sup (j : Fin 2) : Q2 K j ≤ torus 2 K ⊔ H2 K j := by
  have hj := j.isLt
  have hI : ∀ i ∈ ({(j : ℕ) + 1} : Set ℕ), i ≤ 2 := fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    omega
  rw [Q2_eq, (subflag_generation (r := 2) (K := K) _ hI).1, Subgroup.closure_le]
  rintro g (hg | ⟨k, hk, rfl⟩)
  · exact (sup_le (le_sup_of_le_right (unipotent_le_spWeylGroup (Fin.rev j))) le_sup_left :
      unipotent 2 K ⊔ torus 2 K ≤ torus 2 K ⊔ H2 K j) (borelSubgroup_le_sup_torus hg)
  · have hk' : k = Fin.rev j := by
      rw [Set.mem_singleton_iff] at hk
      apply Fin.ext
      rw [Fin.val_rev]
      have := k.isLt
      omega
    subst hk'
    exact Subgroup.mem_sup_right (weylRep_mem_spWeylGroup _)

theorem commutator_Q2_le (j : Fin 2) : ⁅Q2 K j, Q2 K j⁆ ≤ H2 K j :=
  (Subgroup.commutator_mono (Q2_le_sup j) (Q2_le_sup j)).trans
    (commutator_le_of_sup_normalizer (torus_le_normalizer_spWeylGroup (K := K) (Fin.rev j))
      (fun _ ha _ hb => torus_commute ha hb))

theorem H2_le_of_nonsolvable (hB : Group.IsSolvable (borelSubgroup 2 K)) (j : Fin 2)
    {A : Subgroup (StatedSp 2 K)} (hVA : unipotent 2 K ≤ A) (hAQ : A ≤ Q2 K j)
    (hAns : ¬ Group.IsSolvable A) : H2 K j ≤ A := by
  obtain ⟨hle, -⟩ := (symplectic_unitriangular_overgroup_subflag_containment (r := 2) (K := K)).1 A hVA
  have hj := j.isLt
  have hiJ := mem_borelCuts_of_le_Q2 hAQ
  have hroA : weylRep K (Fin.rev j) ∈ A := by
    by_contra hr
    have hoJ : (Fin.rev j : ℕ) + 1 ∈ borelCuts K A := (succ_mem_borelCuts_iff A _).mpr hr
    have hAB : A ≤ borelSubgroup 2 K := by
      rw [borelSubgroup_eq_flagStabilizer]
      intro g hg
      rw [mem_flagStabilizer]
      intro x hx
      have hx' : x ∈ borelCuts K A := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases (by rw [Fin.val_rev]; omega : x = (j : ℕ) + 1 ∨ x = (Fin.rev j : ℕ) + 1) with
          rfl | rfl
        · exact hiJ
        · exact hoJ
      exact mem_flagStabilizer.mp (hle hg) x hx'
    exact hAns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
      (Subgroup.inclusion_injective hAB))
  exact sup_le hVA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr hroA))

theorem symplectic_two_residualOvergroupsAt {K : Type} [Field K] [Finite K]
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))) := by
  have hB := isSolvable_borelSubgroup (r := 2) (K := K) hK
  exact residualOvergroupsAt_of_rank_two_data (π := proj 2 K) (proj_surjective (r := 2) (K := K))
    (V := unipotent 2 K) (B := borelSubgroup 2 K) (Q := Q2 K) (H := H2 K)
    (by
      rw [ker_proj, borelSubgroup_eq_flagStabilizer]
      exact spScalars_le_flagStabilizer _)
    unipotent_le_borelSubgroup
    (fun j => by
      have hj := j.isLt
      rw [Q2_eq]
      exact borelSubgroup_le_flagStabilizer (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        omega))
    Q2_ne covBy_Q2 (fun A hVA hAt => contained_in_Q2 hVA hAt) hB commutator_Q2_le
    (fun j A hVA hAQ hAns => H2_le_of_nonsolvable hB j hVA hAQ hAns)

theorem H2_le_Q2 (j : Fin 2) : H2 K j ≤ Q2 K j := by
  have hj := j.isLt
  refine sup_le ?_ ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr ?_))
  · rw [Q2_eq]
    exact unipotent_le_borelSubgroup.trans (borelSubgroup_le_flagStabilizer (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      omega))
  · rw [SetLike.mem_coe, Q2_eq, weylRep_mem_flagStabilizer_singleton_iff (by omega), Fin.val_rev]
    omega

theorem H2_normal_in_Q2 (j : Fin 2) : ((H2 K j).subgroupOf (Q2 K j)).Normal := by
  have hQ : Q2 K j ≤ Subgroup.normalizer (H2 K j : Set (StatedSp 2 K)) :=
    (Q2_le_sup j).trans (sup_le (torus_le_normalizer_spWeylGroup (K := K) (Fin.rev j))
      Subgroup.le_normalizer)
  rw [Subgroup.normal_subgroupOf_iff (H2_le_Q2 j)]
  intro h k hh hk
  exact (Subgroup.mem_normalizer_iff.mp (hQ hk) h).mp hh

end Two

end CFSG.QuasithinUnique.Setup.X7a
