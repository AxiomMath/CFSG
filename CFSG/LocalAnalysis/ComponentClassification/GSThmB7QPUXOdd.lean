module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUXEven
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClQuot
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerGraphHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaField
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieChar

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace QPUJ.Odd

theorem fixedSubgroup_conj {G : Type*} [Group G] (t : G) :
    fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set G) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change t * x * t⁻¹ = x ↔ x * t = t * x
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

theorem inf_center_eq_bot {M : Type} [Group M] [Finite M] (hZ2 : IsPGroup 2 (center M))
    {J : Subgroup M} {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f) [Group.IsPerfect ↥J] :
    J ⊓ center M = ⊥ := by
  have := QPUJ.Even.isSimpleGroup_of_lieModel_psl_two h5 hJLie
  have : Group.IsPerfect (↥J ⧸ pPrimeCore 2 ↥J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hZq : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := Seven.center_eq_bot_of_isPerfect
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzJ, hzZ⟩ := mem_inf.mp hz
  set z' : ↥J := ⟨z, hzJ⟩
  have hz'c : QuotientGroup.mk' (pPrimeCore 2 ↥J) z' ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
    rw [mem_center_iff]
    intro u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_center_iff.mp hzZ w)
  rw [hZq, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hz'c
  have hR : IsPGroup 2 ((center M).subgroupOf J) := hZ2.comap_subtype
  have h1 : z' ∈ (center M).subgroupOf J ⊓ pPrimeCore 2 ↥J := mem_inf.mpr ⟨hzZ, hz'c⟩
  rw [OddQuot.inf_pPrimeCore_eq_bot hR, mem_bot] at h1
  exact mem_bot.mpr (congrArg Subtype.val h1)

theorem pPrimeCore_eq_center {J : Type} [Group J] (hJ : IsQuasisimple J)
    [IsSimpleGroup (J ⧸ pPrimeCore 2 J)] : pPrimeCore 2 J = center J := by
  have : Group.IsPerfect J := hJ.1
  apply le_antisymm
  · rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hJ (pPrimeCore 2 J) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : J ⧸ pPrimeCore 2 J)
      induction x using QuotientGroup.induction_on with
      | H x =>
        apply hx
        rw [QuotientGroup.eq_one_iff, h]
        exact mem_top x
  · intro z hz
    have : Group.IsPerfect (J ⧸ pPrimeCore 2 J) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hZq : center (J ⧸ pPrimeCore 2 J) = ⊥ := Seven.center_eq_bot_of_isPerfect
    have hzc : QuotientGroup.mk' (pPrimeCore 2 J) z ∈ center (J ⧸ pPrimeCore 2 J) := by
      rw [mem_center_iff]
      intro u
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 J) u
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz w]
    rw [hZq, mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hzc
    exact hzc

open CatLeaf CatLeafProof in
theorem family_facts {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {τ : StatedLieTag} {n r e : ℕ} (hr2 : r ≠ 2)
    (hM : StatedClassicalModel S τ n r e) :
    Blueprint.LieModel S τ n r e ∧ CatLeaf.FixedTwoComponentsQuasisimple S ∧
      CatLeafProof.GLS3OddFamilyInput τ := by
  cases τ
  case PSL =>
    refine ⟨Or.inl ⟨by decide, hM⟩, ?_, gls3OddFamilyInput_PSL_holds⟩
    by_cases hn : 3 ≤ n
    · exact fixedTwoComponentsQuasisimple_psl hr2 hn hM
    · have hn2 : n = 2 := by have := hM.1.2.2.1; omega
      subst hn2
      exact fixedTwoComponentsQuasisimple_psl_two hna hr2 hM
  case PSU =>
    exact ⟨Or.inl ⟨by decide, hM⟩, fixedTwoComponentsQuasisimple_psu hr2 hM,
      gls3OddFamilyInput_PSU_holds⟩
  case PSp =>
    exact ⟨Or.inl ⟨by decide, hM⟩, fixedTwoComponentsQuasisimple_psp hr2 hM,
      gls3OddFamilyInput_PSp_holds⟩
  case POmegaOdd =>
    exact ⟨Or.inl ⟨by decide, hM⟩, fixedTwoComponentsQuasisimple_orthogonal (Or.inl rfl) hr2 hM,
      gls3OddFamilyInput_POmegaOdd oddOmegaOddLinearInput_holds oddOmegaOddFieldInput_holds⟩
  case POmegaPlus =>
    exact ⟨Or.inl ⟨by decide, hM⟩,
      fixedTwoComponentsQuasisimple_orthogonal (Or.inr (Or.inl rfl)) hr2 hM,
      gls3OddFamilyInput_POmegaPlus oddOmegaPlusLinearInput_holds oddOmegaPlusFieldInput_holds⟩
  case POmegaMinus =>
    exact ⟨Or.inl ⟨by decide, hM⟩,
      fixedTwoComponentsQuasisimple_orthogonal (Or.inr (Or.inr rfl)) hr2 hM,
      gls3OddFamilyInput_POmegaMinus oddOmegaMinusLinearInput_holds oddOmegaMinusFieldInput_holds⟩
  all_goals exact hM.2.elim

theorem exists_mul_ne_quot {M : Type} [Group M] (hq : IsQuasisimple M) :
    ∃ a b : M ⧸ center M, a * b ≠ b * a := by
  have : IsSimpleGroup (M ⧸ center M) := hq.2.1
  have : Group.IsPerfect M := hq.1
  have : Group.IsPerfect (M ⧸ center M) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hZS : center (M ⧸ center M) = ⊥ := Seven.center_eq_bot_of_isPerfect
  by_contra h
  have hcomm : ∀ a b : M ⧸ center M, a * b = b * a := fun a b =>
    Classical.byContradiction fun hab => h ⟨a, b, hab⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : M ⧸ center M)
  have hxZ : x ∈ center (M ⧸ center M) := mem_center_iff.mpr fun g => hcomm g x
  rw [hZS] at hxZ
  exact hx (mem_bot.mp hxZ)

section Certified


theorem false_of_config {M : Type} [Group M] [Finite M] {p' f' p f : ℕ}
    (hc : QPUJConfig M p' f' p f) {τ : StatedLieTag} {n r e : ℕ} (hr : r ≠ p') (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible τ n r e) (hLie : Blueprint.LieModel (M ⧸ center M) τ n r e)
    (hB : CatLeaf.FixedTwoComponentsQuasisimple (M ⧸ center M))
    (hG : CatLeafProof.GLS3OddFamilyInput τ) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hZ2, -, -, -, -, hp, hp2, -, h5, hpp, -, -, -, t, J, -, -, -, -, -, -, -, ht2, htZ,
    hJC, hJpc, hJLie, -, -, -⟩ := hc
  have : IsSimpleGroup (M ⧸ center M) := hq.2.1
  have : Group.IsPerfect M := hq.1
  have : Group.IsPerfect (M ⧸ center M) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hZS : center (M ⧸ center M) = ⊥ := Seven.center_eq_bot_of_isPerfect
  obtain ⟨tb, htb⟩ : ∃ tb : M ⧸ center M, tb = t := ⟨_, rfl⟩
  have ht1 : tb ≠ 1 := by
    intro h1
    apply htZ
    rw [htb, QuotientGroup.eq_one_iff] at h1
    exact h1
  have htt : tb * tb = 1 := by
    rw [htb, ← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
  have hα2 : MulAut.conj tb * MulAut.conj tb = 1 := by rw [← map_mul, htt, map_one]
  have hα1 : MulAut.conj tb ≠ 1 := by
    intro h
    apply ht1
    have hcen : tb ∈ center (M ⧸ center M) := by
      rw [mem_center_iff]
      intro g
      have hg : tb * g * tb⁻¹ = g := by
        have := congrArg (fun β : MulAut (M ⧸ center M) => β g) h
        exact this
      calc g * tb = tb * g * tb⁻¹ * tb := by rw [hg]
        _ = tb * g := by group
    rw [hZS] at hcen
    exact mem_bot.mp hcen
  have hαo : orderOf (MulAut.conj tb) = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨hJbC, hJbpc⟩ := QPUCl.isPComponent_map_centralizer t hJC hJpc
  rw [← htb, ← fixedSubgroup_conj tb] at hJbC hJbpc
  have hKq := hB (MulAut.conj tb) hα2 hα1 _ hJbpc
  obtain ⟨-, -, hKs, -⟩ := hJbpc
  rcases hG (M ⧸ center M) n r e hadm.1 hr2 hadm hLie (MulAut.conj tb) hαo _ ⟨hKq, hKs⟩ with
    hK | ⟨-, -, hαr, -⟩
  swap
  · exact hαr ⟨tb, rfl⟩
  have : Group.IsPerfect ↥J := B5a.isPerfect_of_isPComponent_subgroupOf hJC hJpc
  have hJZ : J ⊓ center M = ⊥ := inf_center_eq_bot hZ2 h5 hJLie
  have hinj : Function.Injective ((QuotientGroup.mk' (center M)).subgroupMap J) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (center M) (x : M) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (x : M) ∈ J ⊓ center M := mem_inf.mpr ⟨x.2, h1⟩
    rw [hJZ, mem_bot] at h2
    exact Subtype.ext h2
  let eK := (MulEquiv.ofBijective ((QuotientGroup.mk' (center M)).subgroupMap J) ⟨hinj,
    (QuotientGroup.mk' (center M)).subgroupMap_surjective J⟩).trans (subgroupOfEquivOfLe hJbC).symm
  have hJq : IsQuasisimple ↥J := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eK).mpr hKq
  have := QPUJ.Even.isSimpleGroup_of_lieModel_psl_two h5 hJLie
  have hX : Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_center hJq)) hJLie
  obtain ⟨τ', n', f'', -, hL⟩ := CatLeafProof.oddLieCentralQuotient_of_mulEquiv eK hK
  exact hr ((HarrisLit.L35.char_eq_of_pslTwo hp hp2 h5 hr2 hX hL).trans hpp)

end Certified

end QPUJ.Odd

section Certified


theorem cfQPUJCrossCharOdd_holds : CFQPUJCrossCharOdd := by
  intro M _ _ p' f' p f hc ⟨τ, n, r, e, hr, hr2, hM⟩
  have : IsSimpleGroup (M ⧸ center M) := hc.1.2.1
  obtain ⟨hLie, hB, hG⟩ := QPUJ.Odd.family_facts (QPUJ.Odd.exists_mul_ne_quot hc.1) hr2 hM
  exact QPUJ.Odd.false_of_config hc hr hr2 hM.1 hLie hB hG

theorem cfQPUJCrossChar_holds : CFQPUJCrossChar :=
  cfQPUJCrossChar_of_odd cfQPUJCrossCharOdd_holds

end Certified

end CFSG.ComponentClassification.GSThmB
