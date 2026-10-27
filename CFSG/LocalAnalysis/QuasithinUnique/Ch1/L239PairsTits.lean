module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsFacts

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat
open scoped commutatorElement

@[expose] noncomputable def pJ0 : Equiv.Perm (Fin 1755) := wordIn 13 titsT [-4, -4]

@[expose] noncomputable def pJ1 : Equiv.Perm (Fin 1755) := wordIn 13 titsT [-4, 3, 3]

@[expose] noncomputable def pJ2 : Equiv.Perm (Fin 1755) := wordIn 13 titsT [3, 4, 3]

@[expose] noncomputable def pK0 : Equiv.Perm (Fin 1755) := wordIn 13 titsT [13]

theorem rep_aJ0 : Rep 1755 aJ0 pJ0 := rep_wordArr_titsT (by decide)

theorem rep_aJ1 : Rep 1755 aJ1 pJ1 := rep_wordArr_titsT (by decide)

theorem rep_aJ2 : Rep 1755 aJ2 pJ2 := rep_wordArr_titsT (by decide)

theorem rep_aK0 : Rep 1755 aK0 pK0 := rep_wordArr_titsT (by decide)

theorem pJ0_mem_J : pJ0 ∈ titsJ :=
  Subgroup.subset_closure (show pJ0 ∈ {g | ∃ w ∈ titsJWords, wordIn 13 titsT w = g} from
    ⟨[-4, -4], by simp [titsJWords], rfl⟩)

theorem pJ1_mem_J : pJ1 ∈ titsJ :=
  Subgroup.subset_closure (show pJ1 ∈ {g | ∃ w ∈ titsJWords, wordIn 13 titsT w = g} from
    ⟨[-4, 3, 3], by simp [titsJWords], rfl⟩)

theorem pJ2_mem_J : pJ2 ∈ titsJ :=
  Subgroup.subset_closure (show pJ2 ∈ {g | ∃ w ∈ titsJWords, wordIn 13 titsT w = g} from
    ⟨[3, 4, 3], by simp [titsJWords], rfl⟩)

theorem pJ0_mem_K : pJ0 ∈ titsK :=
  Subgroup.subset_closure (show pJ0 ∈ {g | ∃ w ∈ titsKWords, wordIn 13 titsT w = g} from
    ⟨[-4, -4], by simp [titsKWords], rfl⟩)

theorem pK0_mem_K : pK0 ∈ titsK :=
  Subgroup.subset_closure (show pK0 ∈ {g | ∃ w ∈ titsKWords, wordIn 13 titsT w = g} from
    ⟨[13], by simp [titsKWords], rfl⟩)

theorem tcomm_mem_commutator {A : Subgroup (Equiv.Perm (Fin 1755))} {x y : Equiv.Perm (Fin 1755)}
    (hx : x ∈ A) (hy : y ∈ A) : tcomm x y ∈ ⁅A, A⁆ := by
  have h := Subgroup.commutator_mem_commutator (inv_mem hx) (inv_mem hy)
  simpa [tcomm, commutatorElement_def] using h

theorem inv_aJ0
    : isInvA 1755 aJ0 (invCand 1755 aJ0) = true := titsPairs_check.1

theorem inv_aK0
    : isInvA 1755 aK0 (invCand 1755 aK0) = true := titsPairs_check.2.2.2.1

theorem inv_aJy
    : isInvA 1755 aJy (invCand 1755 aJy) = true := titsPairs_check.2.2.2.2.1

theorem inv_aKy1
    : isInvA 1755 aKy1 (invCand 1755 aKy1) = true := titsPairs_check.2.2.2.2.2.1

theorem inv_aKy2 : isInvA 1755 aKy2 (invCand 1755 aKy2) = true :=
  titsPairs_check.2.2.2.2.2.2.1

theorem inv_aKy3 : isInvA 1755 aKy3 (invCand 1755 aKy3) = true :=
  titsPairs_check.2.2.2.2.2.2.2.1

theorem noncomm_J
    : eqA 1755 (compA 1755 aJ0 aJ1) (compA 1755 aJ1 aJ0) = false :=
  titsPairs_check.2.2.2.2.2.2.2.2.1

theorem noncomm_K
    : eqA 1755 (compA 1755 aK0 aJ0) (compA 1755 aJ0 aK0) = false :=
  titsPairs_check.2.2.2.2.2.2.2.2.2.1

theorem rep_aJy : Rep 1755 aJy (pJ2 * pJ0 * pJ2) :=
  rep_compA (rep_compA rep_aJ2 rep_aJ0) rep_aJ2

theorem rep_aKy1 :
    Rep 1755 aKy1 (pJ0 * pK0 * pK0 * pJ0⁻¹) :=
  rep_compA (rep_compA (rep_compA rep_aJ0 rep_aK0) rep_aK0) (rep_inv_of_isInvA rep_aJ0 inv_aJ0)

theorem rep_aKy2 :
    Rep 1755 aKy2 (pJ0⁻¹ * pK0 * pK0 * pJ0) :=
  rep_compA (rep_compA (rep_compA (rep_inv_of_isInvA rep_aJ0 inv_aJ0) rep_aK0) rep_aK0) rep_aJ0

theorem rep_aKy3
    : Rep 1755 aKy3 (pJ0 * pJ0 * pK0 * pK0 * pJ0 * pJ0) :=
  rep_compA (rep_compA (rep_compA (rep_compA (rep_compA rep_aJ0 rep_aJ0) rep_aK0) rep_aK0)
    rep_aJ0) rep_aJ0

theorem rep_aJc :
    Rep 1755 aJc (tcomm pJ0 (pJ2 * pJ0 * pJ2)) :=
  rep_commArr rep_aJ0 rep_aJy inv_aJ0 inv_aJy

theorem rep_aKc1
    : Rep 1755 aKc1 (tcomm pK0 (pJ0 * pK0 * pK0 * pJ0⁻¹)) :=
  rep_commArr rep_aK0 rep_aKy1 inv_aK0 inv_aKy1

theorem rep_aKc2
    : Rep 1755 aKc2 (tcomm pK0 (pJ0⁻¹ * pK0 * pK0 * pJ0)) :=
  rep_commArr rep_aK0 rep_aKy2 inv_aK0 inv_aKy2

theorem rep_aKc3
    : Rep 1755 aKc3 (tcomm pK0 (pJ0 * pJ0 * pK0 * pK0 * pJ0 * pJ0)) :=
  rep_commArr rep_aK0 rep_aKy3 inv_aK0 inv_aKy3

theorem center_J_le_commutator
    :
    titsJ ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) ≤ ⁅titsJ, titsJ⁆ := by
  intro g hg
  have hgH : g ∈ titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
    ⟨titsJ_le_titsH hg.1, hg.2⟩
  have hg' : g ∈ ((titsH ⊓ Subgroup.centralizer (titsJ : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) := hgH
  rw [titsCHJ_eq] at hg'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg'
  obtain ⟨hinv, -, -, -⟩ := titsCHJ_facts hc
  have hr := (rep_permOfArr hinv).1
  have h := List.all_eq_true.1 titsPairs_check.2.2.2.2.2.2.2.2.2.2.1 c hc
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [eq_of_eqA hr rep_idA h]
    exact one_mem _
  · rw [eq_of_eqA hr rep_aJc h]
    exact tcomm_mem_commutator pJ0_mem_J
      (mul_mem (mul_mem pJ2_mem_J pJ0_mem_J) pJ2_mem_J)

theorem center_K_le_commutator
    :
    titsK ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) ≤ ⁅titsK, titsK⁆ := by
  intro g hg
  have hgN : g ∈ titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :=
    ⟨titsK_le_titsN hg.1, hg.2⟩
  have hg' : g ∈ ((titsN ⊓ Subgroup.centralizer (titsK : Set (Equiv.Perm (Fin 1755))) :
      Subgroup (Equiv.Perm (Fin 1755))) : Set (Equiv.Perm (Fin 1755))) := hgN
  rw [titsCNK_eq] at hg'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg'
  obtain ⟨hinv, -, -, -⟩ := titsCNK_facts hc
  have hr := (rep_permOfArr hinv).1
  have h := List.all_eq_true.1 titsPairs_check.2.2.2.2.2.2.2.2.2.2.2 c hc
  simp only [Bool.or_eq_true] at h
  have hk0 : pK0 ∈ titsK := pK0_mem_K
  have hj0 : pJ0 ∈ titsK := pJ0_mem_K
  rcases h with ((h | h) | h) | h
  · rw [eq_of_eqA hr rep_idA h]
    exact one_mem _
  · rw [eq_of_eqA hr rep_aKc1 h]
    exact tcomm_mem_commutator hk0
      (mul_mem (mul_mem (mul_mem hj0 hk0) hk0) (inv_mem hj0))
  · rw [eq_of_eqA hr rep_aKc2 h]
    exact tcomm_mem_commutator hk0
      (mul_mem (mul_mem (mul_mem (inv_mem hj0) hk0) hk0) hj0)
  · rw [eq_of_eqA hr rep_aKc3 h]
    exact tcomm_mem_commutator hk0
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hj0 hj0) hk0) hk0) hj0) hj0)

theorem exists_noncomm_J
    : ∃ x ∈ titsJ, ∃ y ∈ titsJ, x * y ≠ y * x := by
  refine ⟨pJ0, pJ0_mem_J, pJ1, pJ1_mem_J, fun h => ?_⟩
  have := (eqA_iff (rep_compA rep_aJ0 rep_aJ1) (rep_compA rep_aJ1 rep_aJ0)).2 h
  rw [noncomm_J] at this
  exact Bool.false_ne_true this

theorem exists_noncomm_K
    : ∃ x ∈ titsK, ∃ y ∈ titsK, x * y ≠ y * x := by
  refine ⟨pK0, pK0_mem_K, pJ0, pJ0_mem_K, fun h => ?_⟩
  have := (eqA_iff (rep_compA rep_aK0 rep_aJ0) (rep_compA rep_aJ0 rep_aK0)).2 h
  rw [noncomm_K] at this
  exact Bool.false_ne_true this

theorem solvable_titsH
    : Group.IsSolvable titsH := by
  have h := solvable_titsPointStab
  let e : titsPointStab ≃* titsH :=
    (titsPointStab.equivMapOfInjective titsD.subtype titsD.subtype_injective).trans
      (MulEquiv.subgroupCongr titsH_eq_stab.symm)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem solvable_titsN
    : Group.IsSolvable titsN := by
  have h := solvable_titsLineStab
  let e : titsLineStab ≃* titsN :=
    (titsLineStab.equivMapOfInjective titsD.subtype titsD.subtype_injective).trans
      (MulEquiv.subgroupCongr titsN_eq_stab.symm)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

open CFSG.QuasithinUnique.Vol2Native.L239.Lie in
theorem parabolicFacts_titsH
    : ParabolicFacts titsH titsJ := by
  obtain ⟨-, -, -, -, hJ2, -, hJn, -, -, -, hCJ, -⟩ := AT_Tits_intrinsic_local_pair
  exact
    { le := titsJ_le_titsH
      normalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1 hJn
      pGroup := hJ2
      selfCentralizing := hCJ
      center_le := center_J_le_commutator
      nonabelian := exists_noncomm_J
      levi := Or.inl (by
        rw [(CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot titsH).1 solvable_titsH]
        exact bot_le) }

open CFSG.QuasithinUnique.Vol2Native.L239.Lie in
theorem parabolicFacts_titsN
    : ParabolicFacts titsN titsK := by
  obtain ⟨-, -, -, -, -, hK2, -, hKn, -, -, -, hCK⟩ := AT_Tits_intrinsic_local_pair
  exact
    { le := titsK_le_titsN
      normalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer titsK_le_titsN).1 hKn
      pGroup := hK2
      selfCentralizing := hCK
      center_le := center_K_le_commutator
      nonabelian := exists_noncomm_K
      levi := Or.inl (by
        rw [(CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot titsN).1 solvable_titsN]
        exact bot_le) }

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs
