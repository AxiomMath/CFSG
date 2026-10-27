module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core

public section

noncomputable section

open scoped BigOperators

namespace CFSG.Semidihedral.NormalInductionConstituent

open CFSG Section1

universe u

attribute [local instance] Fintype.ofFinite

variable {L : Type u} [Group L] [Finite L]

@[expose] def originalConjugate (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (t : L) : ClassFunction H :=
  conjugateOnNormal H theta t⁻¹

omit [Finite L] in
theorem originalConjugate_apply (H : Subgroup L) [hH : H.Normal]
    (theta : ClassFunction H) (t : L) (h : H) :
    originalConjugate H theta t h =
      theta ⟨t⁻¹ * (h : L) * t, by simpa using hH.conj_mem (h : L) h.2 t⁻¹⟩ := by
  simp [originalConjugate, conjugateOnNormal]

@[expose] def originalConjugacyOrbit (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) : Finset (ClassFunction H) := by
  classical
  exact Finset.univ.image (originalConjugate H theta)

theorem mem_originalConjugacyOrbit (H : Subgroup L) [H.Normal]
    (theta phi : ClassFunction H) :
    phi ∈ originalConjugacyOrbit H theta ↔
      ∃ t : L, originalConjugate H theta t = phi := by
  classical
  simp [originalConjugacyOrbit]

@[expose] def originalOrbitSum (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) : ClassFunction H :=
  ∑ phi ∈ originalConjugacyOrbit H theta, phi

theorem originalOrbitSum_apply (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (h : H) :
    originalOrbitSum H theta h = ∑ phi ∈ originalConjugacyOrbit H theta, phi h := by
  simp [originalOrbitSum]

theorem originalConjugate_irreducible (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta) (t : L) :
    IsIrreducibleCharacterOnGroup (originalConjugate H theta t) := by
  rcases htheta with ⟨n, rho, hirr, rfl⟩
  let : Representation.IsIrreducible rho := hirr
  rw [originalConjugate, ← representationCharacter_conjugateRepresentation H rho t⁻¹]
  exact isIrreducibleCharacterOnGroup_of_representation
    (conjugateRepresentation H rho t⁻¹)
    (irreducible_conjugateRepresentation H rho t⁻¹)

theorem orbit_member_irreducible (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta)
    (phi : ClassFunction H) (hphi : phi ∈ originalConjugacyOrbit H theta) :
    IsIrreducibleCharacterOnGroup phi := by
  rcases (mem_originalConjugacyOrbit H theta phi).mp hphi with ⟨t, rfl⟩
  exact originalConjugate_irreducible H theta htheta t

theorem originalOrbitSum_isClassFunction (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta) :
    IsClassFunction (originalOrbitSum H theta) := by
  intro x g
  simp only [originalOrbitSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro phi hphi
  exact isBookIrreducibleCharacter_isClassFunction phi
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
      (orbit_member_irreducible H theta htheta phi hphi)) x g

theorem restriction_inner_originalConjugate (H : Subgroup L) [H.Normal]
    (chi : ClassFunction L) (hchi : IsClassFunction chi)
    (theta : ClassFunction H) (t : L) :
    scalarProduct H (subgroupRestriction H chi) (originalConjugate H theta t) =
      scalarProduct H (subgroupRestriction H chi) theta := by
  let e : H ≃* H := conjugateSubgroupMulEquiv H t
  have hinvariant : classFunctionLinearEquivOfMulEquiv e
      (subgroupRestriction H chi) = subgroupRestriction H chi := by
    ext h
    change chi (t⁻¹ * (h : L) * t) = chi (h : L)
    simpa [mul_assoc] using hchi t⁻¹ (h : L)
  have h := scalarProduct_classFunctionLinearEquivOfMulEquiv e
    (subgroupRestriction H chi) theta
  rw [hinvariant] at h
  have htheta : classFunctionLinearEquivOfMulEquiv e theta =
      originalConjugate H theta t := by
    ext k
    simp [e, classFunctionLinearEquivOfMulEquiv, conjugateSubgroupMulEquiv,
      originalConjugate, conjugateOnNormal]
  rw [htheta] at h
  exact h

theorem induction_inner_eq_nat (H : Subgroup L)
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsCharacter theta) (hchi : IsCharacter chi) :
    ∃ m : ℕ, scalarProduct L (inducedCF H theta) chi = (m : ℂ) :=
  scalarProduct_character_character_eq_nat (inducedCF H theta) chi
    (isCharacter_inducedCF_of_isCharacter H theta htheta) hchi

theorem restriction_inner_eq_induction_inner (H : Subgroup L)
    (phi : ClassFunction H) (chi : ClassFunction L)
    (hphi : IsCharacter phi) (hchi : IsCharacter chi) :
    scalarProduct H (subgroupRestriction H chi) phi =
      scalarProduct L (inducedCF H phi) chi := by
  rw [← inducedClassFunction_frobenius_right H phi chi
    (isCharacter_isClassFunction chi hchi)]
  rcases induction_inner_eq_nat H phi chi hphi hchi with ⟨m, hm⟩
  rw [← scalarProduct_star_swap chi (inducedCF H phi), hm]
  simp

theorem orthogonal_character_occurrence
    (f g chi : ClassFunction L) (hf : IsCharacter f) (hg : IsCharacter g)
    (hchi : IsBookIrreducibleCharacter chi)
    (hgf : scalarProduct L g f = 0) (hm : scalarProduct L f chi ≠ 0) :
    scalarProduct L g chi = 0 := by
  classical
  have hfne : f ≠ 0 := by
    intro hzero
    apply hm
    simp [hzero, scalarProduct]
  rcases exists_positive_irreducible_decomposition_of_character f hf hfne with
    ⟨ι, hι, hdec, e, psi, i0, he, hpsi, hdistinct, hdecomp⟩
  let : Fintype ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : DecidableEq ι := hdec
  have hex : ∃ i : ι, psi i = chi := by
    by_contra hnone
    apply hm
    rw [hdecomp, scalarProduct_weightedFamilySum_left]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : psi i ≠ chi := fun h => hnone ⟨i, h⟩
    rw [scalarProduct_isBookIrreducible_ne (psi i) chi (hpsi i) hchi hne, mul_zero]
  rcases hex with ⟨i, hi⟩
  have hnat : ∀ j : ι, ∃ n : ℕ, scalarProduct L g (psi j) = (n : ℂ) :=
    fun j => scalarProduct_character_character_eq_nat g (psi j) hg (hpsi j).1
  choose n hn using hnat
  have hsum : (∑ j : ι, (e j : ℂ) * (n j : ℂ)) = 0 := by
    rw [hdecomp, scalarProduct_weightedFamilySum_right] at hgf
    simpa [hn] using hgf
  have hsumNat : ∑ j : ι, e j * n j = 0 := by
    exact_mod_cast hsum
  have hterm : e i * n i = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      e i * n i ≤ ∑ j : ι, e j * n j :=
        Finset.single_le_sum (f := fun j => e j * n j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = 0 := hsumNat
  have hni : n i = 0 :=
    (Nat.mul_eq_zero.mp hterm).resolve_left (Nat.ne_of_gt (he i))
  rw [← hi, hn i, hni]
  simp

theorem induced_inner_eq_zero_of_not_mem_orbit (H : Subgroup L) [H.Normal]
    (theta phi : ClassFunction H)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hphi : IsIrreducibleCharacterOnGroup phi)
    (hnot : phi ∉ originalConjugacyOrbit H theta) :
    scalarProduct L (inducedCF H phi) (inducedCF H theta) = 0 := by
  rcases htheta with ⟨n, thetaRep, hthetaRep, rfl⟩
  rcases hphi with ⟨k, phiRep, hphiRep, hphi⟩
  apply proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
    H phi phiRep thetaRep hphi hphiRep hthetaRep
  intro i
  refine Quotient.inductionOn i ?_
  intro t heq
  apply hnot
  apply (mem_originalConjugacyOrbit H thetaRep.character phi).mpr
  exact ⟨t⁻¹, by simpa [originalConjugate, conjugateOrbitConj, conjugateOrbitFiber] using heq.symm⟩

theorem restriction_inner_eq_zero_of_not_mem_orbit (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (hm : scalarProduct L (inducedCF H theta) chi ≠ 0)
    (phi : ClassFunction H) (hphi : IsIrreducibleCharacterOnGroup phi)
    (hnot : phi ∉ originalConjugacyOrbit H theta) :
    scalarProduct H (subgroupRestriction H chi) phi = 0 := by
  have hthetaChar := isCharacter_of_isIrreducibleCharacterOnGroup htheta
  have hphiChar := isCharacter_of_isIrreducibleCharacterOnGroup hphi
  have hchiChar := isCharacter_of_isIrreducibleCharacterOnGroup hchi
  rw [restriction_inner_eq_induction_inner H phi chi hphiChar hchiChar]
  exact orthogonal_character_occurrence (inducedCF H theta) (inducedCF H phi) chi
    (isCharacter_inducedCF_of_isCharacter H theta hthetaChar)
    (isCharacter_inducedCF_of_isCharacter H phi hphiChar)
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi)
    (induced_inner_eq_zero_of_not_mem_orbit H theta phi htheta hphi hnot) hm

private theorem scalarProduct_finset_sum_left {X I : Type*} [Finite X]
    (s : Finset I) (f : I → ClassFunction X) (psi : ClassFunction X) :
    scalarProduct X (∑ i ∈ s, f i) psi = ∑ i ∈ s, scalarProduct X (f i) psi := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [scalarProduct]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, scalarProduct_add_left, ih]

theorem originalOrbitSum_inner (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta)
    (phi : ClassFunction H) (hphi : IsIrreducibleCharacterOnGroup phi) :
    scalarProduct H (originalOrbitSum H theta) phi =
      if phi ∈ originalConjugacyOrbit H theta then 1 else 0 := by
  classical
  rw [originalOrbitSum, scalarProduct_finset_sum_left]
  have horth : ∀ psi ∈ originalConjugacyOrbit H theta,
      scalarProduct H psi phi = if psi = phi then 1 else 0 := by
    intro psi hpsi
    by_cases heq : psi = phi
    · subst psi
      simpa [IsIrreducibleCharacter] using
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hphi).2
    · simp only [ite_eq_right heq]
      exact scalarProduct_isBookIrreducible_ne psi phi
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
          (orbit_member_irreducible H theta htheta psi hpsi))
        (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hphi) heq
  calc
    (∑ psi ∈ originalConjugacyOrbit H theta, scalarProduct H psi phi) =
        ∑ psi ∈ originalConjugacyOrbit H theta, if psi = phi then 1 else 0 :=
      Finset.sum_congr rfl horth
    _ = if phi ∈ originalConjugacyOrbit H theta then 1 else 0 := by
      by_cases hmem : phi ∈ originalConjugacyOrbit H theta
      · simp [hmem]
      · simp [hmem]
  all_goals split_ifs <;> rfl

theorem restriction_inner_on_orbit (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (phi : ClassFunction H) (hphi : phi ∈ originalConjugacyOrbit H theta) :
    scalarProduct H (subgroupRestriction H chi) phi =
      scalarProduct L (inducedCF H theta) chi := by
  rcases (mem_originalConjugacyOrbit H theta phi).mp hphi with ⟨t, rfl⟩
  rw [restriction_inner_originalConjugate H chi
    (isBookIrreducibleCharacter_isClassFunction chi
      (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi)) theta t]
  exact restriction_inner_eq_induction_inner H theta chi
    (isCharacter_of_isIrreducibleCharacterOnGroup htheta)
    (isCharacter_of_isIrreducibleCharacterOnGroup hchi)

theorem homogeneous_restriction_of_nonzero_occurrence (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (hm : scalarProduct L (inducedCF H theta) chi ≠ 0) :
    subgroupRestriction H chi =
      scalarProduct L (inducedCF H theta) chi • originalOrbitSum H theta := by
  classical
  have hchiClass := isBookIrreducibleCharacter_isClassFunction chi
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi)
  have hfClass := subgroupRestriction_isClassFunction_of_isClassFunction H chi hchiClass
  have hgClass := isClassFunction_smul
    (scalarProduct L (inducedCF H theta) chi) (originalOrbitSum H theta)
    (originalOrbitSum_isClassFunction H theta htheta)
  apply classFunction_eq_of_inner_irreducible _ _ hfClass hgClass
  intro xi hxi
  rw [representation_inner_toConjClassFunction_right,
    representation_inner_toConjClassFunction_right]
  have hphi := isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
    (ofConjClassFunction xi)
    (isBookIrreducibleCharacter_of_representation_irreducible xi hxi)
  rw [scalarProduct_smul_left, originalOrbitSum_inner H theta htheta _ hphi]
  by_cases hmem : ofConjClassFunction xi ∈ originalConjugacyOrbit H theta
  · rw [ite_eq_left hmem, mul_one]
    exact restriction_inner_on_orbit H theta chi htheta hchi _ hmem
  · rw [ite_eq_right hmem, mul_zero]
    exact restriction_inner_eq_zero_of_not_mem_orbit H theta chi htheta hchi hm
      _ hphi hmem

theorem positive_multiplicity_homogeneous_restriction (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (hm : 0 < (scalarProduct L (inducedCF H theta) chi).re) :
    ∃ m : ℕ, 0 < m ∧ scalarProduct L (inducedCF H theta) chi = (m : ℂ) ∧
      subgroupRestriction H chi = (m : ℂ) • originalOrbitSum H theta := by
  rcases induction_inner_eq_nat H theta chi
    (isCharacter_of_isIrreducibleCharacterOnGroup htheta)
    (isCharacter_of_isIrreducibleCharacterOnGroup hchi) with ⟨m, hmNat⟩
  have hmpos : 0 < m := by
    rw [hmNat] at hm
    exact_mod_cast hm
  have hmne : scalarProduct L (inducedCF H theta) chi ≠ 0 := by
    rw [hmNat]
    exact_mod_cast (Nat.ne_of_gt hmpos)
  refine ⟨m, hmpos, hmNat, ?_⟩
  simpa only [hmNat] using
    homogeneous_restriction_of_nonzero_occurrence H theta chi htheta hchi hmne

theorem multiplicity_one_equal_restrictions_degrees (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta)
    (chi₁ chi₂ : ClassFunction L)
    (hchi₁ : IsIrreducibleCharacterOnGroup chi₁)
    (hchi₂ : IsIrreducibleCharacterOnGroup chi₂)
    (hm₁ : scalarProduct L (inducedCF H theta) chi₁ = 1)
    (hm₂ : scalarProduct L (inducedCF H theta) chi₂ = 1) :
    subgroupRestriction H chi₁ = subgroupRestriction H chi₂ ∧
      degree chi₁ = degree chi₂ := by
  have hres₁ := homogeneous_restriction_of_nonzero_occurrence
    H theta chi₁ htheta hchi₁ (by rw [hm₁]; exact one_ne_zero)
  have hres₂ := homogeneous_restriction_of_nonzero_occurrence
    H theta chi₂ htheta hchi₂ (by rw [hm₂]; exact one_ne_zero)
  rw [hm₁, one_smul] at hres₁
  rw [hm₂, one_smul] at hres₂
  have hres := hres₁.trans hres₂.symm
  refine ⟨hres, ?_⟩
  exact congrFun hres (1 : H)

theorem irreducible_difference_virtual (chi₁ chi₂ : ClassFunction L)
    (hchi₁ : IsIrreducibleCharacterOnGroup chi₁)
    (hchi₂ : IsIrreducibleCharacterOnGroup chi₂) :
    Theory.Character.IsVirtualCharacter (chi₁ - chi₂) := by
  rcases hchi₁ with ⟨n₁, rho₁, hirr₁, heq₁⟩
  rcases hchi₂ with ⟨n₂, rho₂, hirr₂, heq₂⟩
  let data : Fin 2 → Σ n : ℕ, Representation ℂ L (Fin n → ℂ) :=
    Fin.cases ⟨n₁, rho₁⟩ (fun _ => ⟨n₂, rho₂⟩)
  refine ⟨2, (fun i => if i = 0 then (1 : ℤ) else -1),
    (fun i => (data i).1), (fun i => (data i).2), ?_⟩
  ext g
  have hdataOne : data (1 : Fin 2) = ⟨n₂, rho₂⟩ := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl]
    exact Fin.cases_succ (0 : Fin 1)
  simp only [Theory.Character.virtualCharacterOfRepresentations, Fin.sum_univ_two]
  have hcharOne : (data (1 : Fin 2)).2.character g = rho₂.character g :=
    congrArg (fun p : Σ n : ℕ, Representation ℂ L (Fin n → ℂ) => p.2.character g)
      hdataOne
  rw [hcharOne]
  simp [data, heq₁, heq₂, sub_eq_add_neg]
  all_goals rfl

theorem difference_support_of_equal_restrictions (H : Subgroup L)
    (chi₁ chi₂ : ClassFunction L)
    (hchi₁ : IsIrreducibleCharacterOnGroup chi₁)
    (hchi₂ : IsIrreducibleCharacterOnGroup chi₂)
    (hres : subgroupRestriction H chi₁ = subgroupRestriction H chi₂)
    (A : Set L) (hA : A ⊆ ({1} : Set L)ᶜ)
    (hsupp₁ : Theory.Character.supportedOn chi₁ ({1} ∪ A))
    (hsupp₂ : Theory.Character.supportedOn chi₂ ({1} ∪ A)) :
    Theory.Character.IsVirtualCharacter (chi₁ - chi₂) ∧
      degree (chi₁ - chi₂) = 0 ∧
      Theory.Character.supportedOn (chi₁ - chi₂) (A \ (H : Set L)) := by
  have hsupp : Theory.Character.supportedOn (chi₁ - chi₂) (A \ (H : Set L)) := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact sub_eq_zero.mpr (congrFun hres (⟨z, hzH⟩ : H))
    · have hzA : z ∉ A := fun hzA => hz ⟨hzA, hzH⟩
      have hzOne : z ≠ 1 := by
        intro heq
        apply hzH
        simp [heq]
      have hout : z ∉ ({1} ∪ A : Set L) := by simp [hzOne, hzA]
      change chi₁ z - chi₂ z = 0
      rw [hsupp₁ z hout, hsupp₂ z hout, sub_self]
  refine ⟨irreducible_difference_virtual chi₁ chi₂ hchi₁ hchi₂, ?_, hsupp⟩
  apply hsupp (1 : L)
  intro h
  exact hA h.1 (by simp)

theorem multiplicity_one_constituent_consequences (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta)
    (chi₁ chi₂ : ClassFunction L)
    (hchi₁ : IsIrreducibleCharacterOnGroup chi₁)
    (hchi₂ : IsIrreducibleCharacterOnGroup chi₂)
    (hm₁ : scalarProduct L (inducedCF H theta) chi₁ = 1)
    (hm₂ : scalarProduct L (inducedCF H theta) chi₂ = 1) :
    subgroupRestriction H chi₁ = subgroupRestriction H chi₂ ∧
      degree chi₁ = degree chi₂ ∧
      ∀ A : Set L, A ⊆ ({1} : Set L)ᶜ →
        Theory.Character.supportedOn chi₁ ({1} ∪ A) →
        Theory.Character.supportedOn chi₂ ({1} ∪ A) →
        Theory.Character.IsVirtualCharacter (chi₁ - chi₂) ∧
          degree (chi₁ - chi₂) = 0 ∧
          Theory.Character.supportedOn (chi₁ - chi₂) (A \ (H : Set L)) := by
  rcases multiplicity_one_equal_restrictions_degrees H theta htheta chi₁ chi₂
    hchi₁ hchi₂ hm₁ hm₂ with ⟨hres, hdegree⟩
  refine ⟨hres, hdegree, ?_⟩
  intro A hA hsupp₁ hsupp₂
  exact difference_support_of_equal_restrictions H chi₁ chi₂ hchi₁ hchi₂ hres
    A hA hsupp₁ hsupp₂

theorem normal_induction_constituent_homogeneous_restriction
    (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (m : ℂ) (hm : m = scalarProduct L (inducedCF H theta) chi)
    (hmpos : 0 < m.re) :
    (∃ n : ℕ, 0 < n ∧ m = (n : ℂ)) ∧
      subgroupRestriction H chi = m • originalOrbitSum H theta ∧
      ∀ chi₁ chi₂ : ClassFunction L,
        IsIrreducibleCharacterOnGroup chi₁ →
        IsIrreducibleCharacterOnGroup chi₂ →
        scalarProduct L (inducedCF H theta) chi₁ = 1 →
        scalarProduct L (inducedCF H theta) chi₂ = 1 →
        subgroupRestriction H chi₁ = subgroupRestriction H chi₂ ∧
          degree chi₁ = degree chi₂ ∧
          ∀ A : Set L, A ⊆ ({1} : Set L)ᶜ →
            Theory.Character.supportedOn chi₁ ({1} ∪ A) →
            Theory.Character.supportedOn chi₂ ({1} ∪ A) →
            Theory.Character.IsVirtualCharacter (chi₁ - chi₂) ∧
              degree (chi₁ - chi₂) = 0 ∧
              Theory.Character.supportedOn (chi₁ - chi₂) (A \ (H : Set L)) := by
  subst m
  rcases positive_multiplicity_homogeneous_restriction H theta chi htheta hchi hmpos with
    ⟨n, hn, hmNat, hres⟩
  refine ⟨⟨n, hn, hmNat⟩, ?_, ?_⟩
  · simpa only [hmNat] using hres
  · intro chi₁ chi₂ hchi₁ hchi₂ hm₁ hm₂
    exact multiplicity_one_constituent_consequences H theta htheta chi₁ chi₂
      hchi₁ hchi₂ hm₁ hm₂

theorem orbit_member_degree (H : Subgroup L) [H.Normal]
    (theta phi : ClassFunction H) (hphi : phi ∈ originalConjugacyOrbit H theta) :
    degree phi = degree theta := by
  rcases (mem_originalConjugacyOrbit H theta phi).mp hphi with ⟨t, rfl⟩
  exact degree_conjugateOnNormal H theta t⁻¹

theorem originalOrbitSum_degree (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) :
    degree (originalOrbitSum H theta) =
      ((originalConjugacyOrbit H theta).card : ℂ) * degree theta := by
  rw [degree, originalOrbitSum_apply]
  rw [Finset.sum_eq_card_nsmul (fun phi hphi =>
    show phi (1 : H) = degree theta from orbit_member_degree H theta phi hphi)]
  simp [nsmul_eq_mul]

theorem originalConjugacyOrbit_nonempty (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) : (originalConjugacyOrbit H theta).Nonempty := by
  refine ⟨theta, (mem_originalConjugacyOrbit H theta theta).mpr ⟨1, ?_⟩⟩
  simpa [originalConjugate] using conjugateOnNormal_one H theta

theorem constituent_degree_ratio (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (m : ℕ) (hm : scalarProduct L (inducedCF H theta) chi = (m : ℂ))
    (hmpos : 0 < m) :
    degree chi = ((m * (originalConjugacyOrbit H theta).card : ℕ) : ℂ) * degree theta := by
  have hne : scalarProduct L (inducedCF H theta) chi ≠ 0 := by
    rw [hm]
    exact_mod_cast (Nat.ne_of_gt hmpos)
  have hres := homogeneous_restriction_of_nonzero_occurrence H theta chi htheta hchi hne
  have hdegree := congrFun hres (1 : H)
  change degree chi = scalarProduct L (inducedCF H theta) chi *
    degree (originalOrbitSum H theta) at hdegree
  rw [hm, originalOrbitSum_degree] at hdegree
  simpa only [Nat.cast_mul, mul_assoc] using hdegree

theorem exists_irreducible_positive_degree_multiple (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (htheta : IsIrreducibleCharacterOnGroup theta) :
    ∃ chi : ClassFunction L, IsIrreducibleCharacterOnGroup chi ∧
      ∃ m a : ℕ, 0 < m ∧ 0 < a ∧
        scalarProduct L (inducedCF H theta) chi = (m : ℂ) ∧
        degree chi = (a : ℂ) * degree theta := by
  classical
  have hthetaBook := isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup htheta
  have hindChar := isCharacter_inducedCF_of_isCharacter H theta hthetaBook.1
  have hindNe : inducedCF H theta ≠ 0 := by
    intro hzero
    have hdegree : degree (inducedCF H theta) = (H.index : ℂ) * degree theta :=
      degree_inducedClassFunction H theta
    rw [hzero] at hdegree
    have hidx : (H.index : ℂ) ≠ 0 := by
      exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := H))
    have hthetaNe := degree_ne_zero_of_isBookIrreducibleCharacter theta hthetaBook
    exact (mul_ne_zero hidx hthetaNe) hdegree.symm
  rcases exists_positive_irreducible_decomposition_of_character
    (inducedCF H theta) hindChar hindNe with
    ⟨ι, hι, hdec, e, psi, i0, he, hpsi, hdistinct, hdecomp⟩
  let : Fintype ι := hι
  let : DecidableEq ι := hdec
  have horth := scalarProduct_isBookIrreducible_family psi hpsi hdistinct
  have hm : scalarProduct L (inducedCF H theta) (psi i0) = (e i0 : ℂ) :=
    proposition_1_7_multiplicity_from_decomposition e psi (inducedCF H theta)
      horth hdecomp i0
  have hchi := isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter (psi i0) (hpsi i0)
  refine ⟨psi i0, hchi, e i0, e i0 * (originalConjugacyOrbit H theta).card,
    he i0, ?_, hm, ?_⟩
  · exact Nat.mul_pos (he i0) (Finset.card_pos.mpr (originalConjugacyOrbit_nonempty H theta))
  · exact constituent_degree_ratio H theta (psi i0) htheta hchi (e i0) hm (he i0)

theorem irreducible_degree_eq_positive_nat (chi : ClassFunction L)
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    ∃ d : ℕ, 0 < d ∧ degree chi = (d : ℂ) := by
  have hbook := isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi
  rcases degree_nat_dvd_card_of_isBookIrreducibleCharacter chi hbook with ⟨d, hd, hdiv⟩
  refine ⟨d, ?_, hd⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  apply degree_ne_zero_of_isBookIrreducibleCharacter chi hbook
  simp [hd, hzero]

theorem occurrence_degree_bound (f chi : ClassFunction L)
    (hf : IsCharacter f) (hchi : IsBookIrreducibleCharacter chi)
    (dF dChi m : ℕ) (hdF : degree f = (dF : ℂ)) (hdChi : degree chi = (dChi : ℂ))
    (hm : scalarProduct L f chi = (m : ℂ)) (hmpos : 0 < m) :
    m * dChi ≤ dF := by
  classical
  have hfne : f ≠ 0 := by
    intro hzero
    have h : (m : ℂ) = 0 := by simpa [hzero, scalarProduct] using hm.symm
    have hmzero : m = 0 := by exact_mod_cast h
    omega
  rcases exists_positive_irreducible_decomposition_of_character f hf hfne with
    ⟨ι, hι, hdec, e, psi, i0, he, hpsi, hdistinct, hdecomp⟩
  let : Fintype ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  let : DecidableEq ι := hdec
  have hex : ∃ i : ι, psi i = chi := by
    by_contra hnone
    have hzero : scalarProduct L f chi = 0 := by
      rw [hdecomp, scalarProduct_weightedFamilySum_left]
      apply Finset.sum_eq_zero
      intro i hi
      rw [scalarProduct_isBookIrreducible_ne (psi i) chi (hpsi i) hchi
        (fun h => hnone ⟨i, h⟩), mul_zero]
    have hmzero : m = 0 := by exact_mod_cast (hm.symm.trans hzero)
    omega
  rcases hex with ⟨i, hi⟩
  have horth := scalarProduct_isBookIrreducible_family psi hpsi hdistinct
  have hei : e i = m := by
    have hco := proposition_1_7_multiplicity_from_decomposition e psi f horth hdecomp i
    rw [hi, hm] at hco
    exact_mod_cast hco.symm
  have hdegrees : ∀ j : ι, ∃ d : ℕ, degree (psi j) = (d : ℂ) := by
    intro j
    rcases degree_nat_dvd_card_of_isBookIrreducibleCharacter (psi j) (hpsi j) with
      ⟨d, hd, hdiv⟩
    exact ⟨d, hd⟩
  choose d hd using hdegrees
  have hdi : d i = dChi := by
    have h := hd i
    rw [hi, hdChi] at h
    exact_mod_cast h.symm
  have hsumC : (dF : ℂ) = ∑ j : ι, (e j : ℂ) * (d j : ℂ) := by
    rw [← hdF, hdecomp]
    change (∑ j : ι, (e j : ℂ) * psi j 1) = _
    apply Finset.sum_congr rfl
    intro j hj
    rw [show psi j 1 = (d j : ℂ) from hd j]
  have hsumNat : dF = ∑ j : ι, e j * d j := by exact_mod_cast hsumC
  have hterm : e i * d i ≤ ∑ j : ι, e j * d j :=
    Finset.single_le_sum (f := fun j => e j * d j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa only [hei, hdi, ← hsumNat] using hterm

theorem multiplicity_sq_mul_orbit_card_le_index (H : Subgroup L) [H.Normal]
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (m : ℕ) (hm : scalarProduct L (inducedCF H theta) chi = (m : ℂ))
    (hmpos : 0 < m) :
    m ^ 2 * (originalConjugacyOrbit H theta).card ≤ H.index := by
  rcases irreducible_degree_eq_positive_nat theta htheta with ⟨dTheta, hdThetaPos, hdTheta⟩
  rcases irreducible_degree_eq_positive_nat chi hchi with ⟨dChi, hdChiPos, hdChi⟩
  have hdegreeInd : degree (inducedCF H theta) = ((H.index * dTheta : ℕ) : ℂ) := by
    rw [degree_inducedClassFunction, hdTheta, Nat.cast_mul]
  have hbound := occurrence_degree_bound (inducedCF H theta) chi
    (isCharacter_inducedCF_of_isCharacter H theta
      (isCharacter_of_isIrreducibleCharacterOnGroup htheta))
    (isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi)
    (H.index * dTheta) dChi m hdegreeInd hdChi hm hmpos
  have hdegreeChi := constituent_degree_ratio H theta chi htheta hchi m hm hmpos
  rw [hdChi, hdTheta] at hdegreeChi
  have hratio : dChi = (m * (originalConjugacyOrbit H theta).card) * dTheta := by
    exact_mod_cast hdegreeChi
  rw [hratio] at hbound
  apply Nat.le_of_mul_le_mul_right (c := dTheta) _ hdThetaPos
  simpa only [pow_two, mul_assoc] using hbound

theorem index_two_constituent_multiplicity_degree (H : Subgroup L) [H.Normal]
    (hindex : H.index = 2)
    (theta : ClassFunction H) (chi : ClassFunction L)
    (htheta : IsIrreducibleCharacterOnGroup theta)
    (hchi : IsIrreducibleCharacterOnGroup chi)
    (hm : 0 < (scalarProduct L (inducedCF H theta) chi).re) :
    scalarProduct L (inducedCF H theta) chi = 1 ∧
      subgroupRestriction H chi = originalOrbitSum H theta ∧
      ((originalConjugacyOrbit H theta).card = 1 ∨
        (originalConjugacyOrbit H theta).card = 2) ∧
      (degree chi = degree theta ∨ degree chi = (2 : ℂ) * degree theta) := by
  rcases positive_multiplicity_homogeneous_restriction H theta chi htheta hchi hm with
    ⟨m, hmpos, hmNat, hres⟩
  have hsq := multiplicity_sq_mul_orbit_card_le_index H theta chi htheta hchi m hmNat hmpos
  rw [hindex] at hsq
  have horbitpos := Finset.card_pos.mpr (originalConjugacyOrbit_nonempty H theta)
  have hmle : m ^ 2 ≤ 2 := by
    calc
      m ^ 2 ≤ m ^ 2 * (originalConjugacyOrbit H theta).card :=
        Nat.le_mul_of_pos_right _ horbitpos
      _ ≤ 2 := hsq
  have hmone : m = 1 := by nlinarith
  have horbitle : (originalConjugacyOrbit H theta).card ≤ 2 := by simpa [hmone] using hsq
  have horbit : (originalConjugacyOrbit H theta).card = 1 ∨
      (originalConjugacyOrbit H theta).card = 2 := by omega
  have hdegree := constituent_degree_ratio H theta chi htheta hchi m hmNat hmpos
  refine ⟨by simpa [hmone] using hmNat, by simpa [hmone] using hres, horbit, ?_⟩
  rcases horbit with horbit | horbit
  · left
    simpa [hmone, horbit] using hdegree
  · right
    simpa [hmone, horbit] using hdegree

theorem restriction_isCharacter (H : Subgroup L) (chi : ClassFunction L)
    (hchi : IsCharacter chi) : IsCharacter (subgroupRestriction H chi) := by
  rcases hchi with ⟨V, hadd, hmodule, hfinite, rho, rfl⟩
  refine ⟨V, hadd, hmodule, hfinite, rho.comp H.subtype, ?_⟩
  rfl

theorem exists_irreducible_restriction_constituent (H : Subgroup L)
    (chi : ClassFunction L) (hchi : IsIrreducibleCharacterOnGroup chi) :
    ∃ theta : ClassFunction H, IsIrreducibleCharacterOnGroup theta ∧
      ∃ m : ℕ, 0 < m ∧ scalarProduct L (inducedCF H theta) chi = (m : ℂ) := by
  have hbook := isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hchi
  have hresChar := restriction_isCharacter H chi hbook.1
  have hresNe : subgroupRestriction H chi ≠ 0 := by
    intro hzero
    have hdegree : degree chi = 0 := congrFun hzero (1 : H)
    exact degree_ne_zero_of_isBookIrreducibleCharacter chi hbook hdegree
  rcases exists_positive_irreducible_decomposition_of_character
    (subgroupRestriction H chi) hresChar hresNe with
    ⟨ι, hι, hdec, e, psi, i0, he, hpsi, hdistinct, hdecomp⟩
  let : Fintype ι := hι
  let : DecidableEq ι := hdec
  refine ⟨psi i0,
    isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter (psi i0) (hpsi i0),
    e i0, he i0, ?_⟩
  rw [← restriction_inner_eq_induction_inner H (psi i0) chi (hpsi i0).1 hbook.1]
  exact proposition_1_7_multiplicity_from_decomposition e psi (subgroupRestriction H chi)
    (scalarProduct_isBookIrreducible_family psi hpsi hdistinct) hdecomp i0

theorem index_two_irreducible_restriction (H : Subgroup L) [H.Normal]
    (hindex : H.index = 2)
    (chi : ClassFunction L) (hchi : IsIrreducibleCharacterOnGroup chi) :
    ∃ theta : ClassFunction H, IsIrreducibleCharacterOnGroup theta ∧
      scalarProduct L (inducedCF H theta) chi = 1 ∧
      subgroupRestriction H chi = originalOrbitSum H theta ∧
      ((originalConjugacyOrbit H theta).card = 1 ∨
        (originalConjugacyOrbit H theta).card = 2) ∧
      (degree chi = degree theta ∨ degree chi = (2 : ℂ) * degree theta) := by
  rcases exists_irreducible_restriction_constituent H chi hchi with
    ⟨theta, htheta, m, hmpos, hm⟩
  refine ⟨theta, htheta, ?_⟩
  apply index_two_constituent_multiplicity_degree H hindex theta chi htheta hchi
  rw [hm]
  exact_mod_cast hmpos

end CFSG.Semidihedral.NormalInductionConstituent
