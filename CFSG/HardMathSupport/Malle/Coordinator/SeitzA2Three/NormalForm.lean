module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.NormalFormAux
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Assembly
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.FieldReplace

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open
open CFSG.HardMathSupport.Foote.ModuleExclusions (fixF mem_fixF SplitData)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
  (mem_of_zpow_mem_of_pow_three card_sup_of_commute_disjoint sc scal mem_sc_iff scal_mem_sc
    torusThree heisenbergThree monomGL)
open CFSG.HardMathSupport.Foote.ModuleExclusions (natCard_eq_pow_three three_dvd_sub_one_of_pow_three)

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Finite F]

theorem three_ne_zero_of_dvd (h3 : 3 ∣ Nat.card F - 1) : (3 : F) ≠ 0 := by
  intro h
  have hd : ringChar F ∣ 3 := ringChar.dvd (by exact_mod_cast h)
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact CFSG.HardMathSupport.Foote.ModuleExclusions.ringChar_ne_three h3 h1

noncomputable abbrev ιU (σ : F ≃+* F) : (fixF σ)ˣ →* Fˣ := Units.map (fixF σ).subtype.toMonoidHom

theorem liftGL_diagGL (σ : F ≃+* F) (a b c : (fixF σ)ˣ) :
    liftGL σ (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL (fixF σ) a b c) =
      CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL F (ιU σ a) (ιU σ b)
        (ιU σ c) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftGL, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL,
      ιU]

theorem liftGL_diagGL_foote (σ : F ≃+* F) (a b c : (fixF σ)ˣ) :
    liftGL σ (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL (fixF σ) a b c) =
      CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL ![ιU σ a, ιU σ b, ιU σ c] := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftGL, CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL,
      CFSG.HardMathSupport.Foote.ModuleExclusions.diagGL, ιU]

theorem liftGL_monomGL (σ : F ≃+* F) (lam : (fixF σ)ˣ) :
    liftGL σ (monomGL (fixF σ) lam) = monomGL F (ιU σ lam) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftGL, monomGL, ιU]

theorem map_conj_sup_zpowers {G : Type*} [Group G] (f : G) (A : Subgroup G) (c₀ : G)
    (hc : Commute c₀ f) :
    (Subgroup.zpowers f ⊔ A).map (MulAut.conj c₀).toMonoidHom =
      Subgroup.zpowers f ⊔ A.map (MulAut.conj c₀).toMonoidHom := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hc.eq]
  group


set_option maxHeartbeats 1000000 in
theorem a2Three_cube_normal_form (h3 : 3 ∣ Nat.card F - 1)
    {B : Subgroup (MulAut (projectiveSL 3 F))} (hB : IsElemAbelian 3 B) (hc : Nat.card B = 3 ^ 3) :
    ∃ (α : MulAut (projectiveSL 3 F)) (σ : F ≃+* F), orderOf σ = 3 ∧
      ((∃ A : Subgroup (MulAut (projectiveSL 3 F)),
          SplitData σ A (B.map (MulAut.conj α).toMonoidHom)) ∨
       (∃ lam ω : Fˣ, σ lam = lam ∧ IsPrimitiveRoot (ω : F) 3 ∧
          B.map (MulAut.conj α).toMonoidHom = heisCube σ lam ω)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h30 : (3 : F) ≠ 0 := three_ne_zero_of_dvd h3
  have hout : ¬ B ≤ linearAutGroup 3 F := by
    intro hle
    have := CFSG.RankThree.PartTwo.Sec4.card_inf_linearAutGroup_three_le h30 hB
    rw [inf_of_le_left hle, hc] at this
    norm_num at this
  obtain ⟨g, σ, hσ, hB'eq, hcent⟩ := fieldCube_standardForm_noinn B hB hout
  set c : MulAut (projectiveSL 3 F) := conjAut 3 F g with hcdef
  set B' : Subgroup (MulAut (projectiveSL 3 F)) := B.map (MulAut.conj c).toMonoidHom with hB'
  have hB'e : IsElemAbelian 3 B' := CFSG.SectionRank.isElemAbelian_map hB _
  have hB'c : Nat.card B' = 3 ^ 3 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj c).injective, hc]
  set A : Subgroup (MulAut (projectiveSL 3 F)) := B' ⊓ linearAutGroup 3 F with hA
  set f : MulAut (projectiveSL 3 F) := fieldAut 3 F σ with hf
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hf3 : f ^ 3 = 1 := by rw [hf, ← map_pow, hσ3, map_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  have hfnl : f ∉ linearAutGroup 3 F := fun hm =>
    hσ1 ((CFSG.RankThree.PartTwo.KFacts.fieldAut_mem_linearAutGroup_iff (by norm_num)).1 hm)
  have hf1 : f ≠ 1 := fun h1 => hfnl (h1 ▸ one_mem _)
  have hfA : ∀ a ∈ A, Commute a f := by
    intro a ha
    have := (Subgroup.mem_centralizer_iff.1 (hcent ha)) f (Set.mem_singleton f)
    exact this.symm
  have hof : orderOf f = 3 := orderOf_eq_prime hf3 hf1
  have hAc : Nat.card A = 9 := by
    have hdisj : Disjoint (Subgroup.zpowers f) A := by
      rw [Subgroup.disjoint_def]
      intro x hxf hxA
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxf
      by_cases h3k : (3 : ℤ) ∣ k
      · exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hof]; exact_mod_cast h3k)
      · exact absurd (mem_of_zpow_mem_of_pow_three hf3 h3k hxA.2) hfnl
    have hcomm : ∀ h ∈ Subgroup.zpowers f, ∀ k ∈ A, Commute h k := by
      intro h hh k hk
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact ((hfA k hk).symm).zpow_left i
    have := card_sup_of_commute_disjoint _ _ hcomm hdisj
    rw [← hB'eq, hB'c, Nat.card_zpowers, hof] at this
    omega
  set φ0 : GL (Fin 3) (fixF σ) →* MulAut (projectiveSL 3 F) :=
    (conjAut 3 F).comp (liftGL σ) with hφ0
  set At : Subgroup (GL (Fin 3) (fixF σ)) := A.comap φ0 with hAt
  have hφ0comm : ∀ M, Commute (φ0 M) f := fun M => (fieldAut_mul_conjAut_lift σ M).symm
  have hAsurj : ∀ a ∈ A, ∃ M ∈ At, φ0 M = a := by
    intro a ha
    obtain ⟨M, hM⟩ := exists_liftGL_of_commute hσ ha.2 (hfA a ha).symm.eq
    refine ⟨M, ?_, hM.symm⟩
    show φ0 M ∈ A
    rw [show φ0 M = a from hM.symm]
    exact ha
  have hAt_ker : ∀ x, φ0 x = 1 ↔ x ∈ sc (fixF σ) := conjAut_liftGL_eq_one_iff σ
  have hAt_sc : sc (fixF σ) ≤ At := by
    intro x hx
    show φ0 x ∈ A
    rw [(hAt_ker x).2 hx]
    exact A.one_mem
  have hAt_cube : ∀ x ∈ At, x ^ 3 ∈ sc (fixF σ) := by
    intro x hx
    rw [← hAt_ker, map_pow]
    exact hB'e.2 _ (hx : φ0 x ∈ A).1
  have hAt_comm' : ∀ x ∈ At, ∀ y ∈ At, x * y * x⁻¹ * y⁻¹ ∈ sc (fixF σ) := by
    intro x hx y hy
    rw [← hAt_ker]
    simp only [map_mul, map_inv]
    have := hB'e.1.is_comm.comm ⟨φ0 x, (hx : φ0 x ∈ A).1⟩ ⟨φ0 y, (hy : φ0 y ∈ A).1⟩
    have h' : φ0 x * φ0 y = φ0 y * φ0 x := congrArg Subtype.val this
    rw [h']
    group
  have hAt_rank : Nat.card (At ⧸ (sc (fixF σ)).subgroupOf At) = 9 := by
    let ψ : At →* A := (φ0.comp At.subtype).codRestrict A (fun x => x.2)
    have hψs : Function.Surjective ψ := by
      rintro ⟨a, ha⟩
      obtain ⟨M, hM, rfl⟩ := hAsurj a ha
      exact ⟨⟨M, hM⟩, rfl⟩
    have hker : ψ.ker = (sc (fixF σ)).subgroupOf At := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      rw [← hAt_ker]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    have hN : ((sc (fixF σ)).subgroupOf At).Normal := by rw [← hker]; infer_instance
    rw [← hAc]
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).toEquiv.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv)
  have hh3 : 3 ∣ Nat.card (fixF σ) - 1 := by
    have h1 := natCard_eq_pow_three hσ
    rw [h1] at h3
    exact three_dvd_sub_one_of_pow_three Nat.card_pos h3
  have hAmap : At.map φ0 = A := by
    ext a
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact hM
    · intro ha
      obtain ⟨M, hM, rfl⟩ := hAsurj a ha
      exact ⟨M, hM, rfl⟩
  have key : ∀ g₀ : GL (Fin 3) (fixF σ),
      B.map (MulAut.conj (φ0 g₀ * c)).toMonoidHom =
        Subgroup.zpowers f ⊔ (At.map (MulAut.conj g₀).toMonoidHom).map φ0 := by
    intro g₀
    have e1 : B.map (MulAut.conj (φ0 g₀ * c)).toMonoidHom =
        B'.map (MulAut.conj (φ0 g₀)).toMonoidHom := by
      rw [hB', Subgroup.map_map]
      congr 1
    have e2 : B'.map (MulAut.conj (φ0 g₀)).toMonoidHom =
        Subgroup.zpowers f ⊔ A.map (MulAut.conj (φ0 g₀)).toMonoidHom := by
      rw [hB'eq]
      exact map_conj_sup_zpowers f A _ (hφ0comm g₀)
    have e3 : A.map (MulAut.conj (φ0 g₀)).toMonoidHom = (At.map (MulAut.conj g₀).toMonoidHom).map φ0 := by
      rw [← hAmap, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    rw [e1, e2, e3]
  have hN : ∀ g₀ : GL (Fin 3) (fixF σ), ∀ N ∈ At.map (MulAut.conj g₀).toMonoidHom,
      ∃ M ∈ At, N = g₀ * M * g₀⁻¹ := by
    rintro g₀ N ⟨M, hM, rfl⟩
    exact ⟨M, hM, by simp [MulAut.conj_apply]⟩
  rcases pgl3_rank_two_classify_any hh3 At hAt_sc hAt_cube hAt_comm' hAt_rank with
    ⟨g₀, hg₀⟩ | ⟨g₀, lam, ω, hω, hH⟩
  · refine ⟨φ0 g₀ * c, σ, hσ, Or.inl ⟨(At.map (MulAut.conj g₀).toMonoidHom).map φ0, ?_⟩⟩
    rw [key g₀]
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨N, hNm, rfl⟩
      obtain ⟨M, hM, rfl⟩ := hN g₀ N hNm
      rw [← map_pow, show (g₀ * M * g₀⁻¹) ^ 3 = g₀ * M ^ 3 * g₀⁻¹ from conj_pow]
      have := (hAt_ker (M ^ 3)).2 (hAt_cube M hM)
      simp [map_mul, map_inv, this]
    · rintro _ ⟨N, hNm, rfl⟩
      obtain ⟨a, b, c', -, -, hd⟩ := hg₀ hNm
      refine ⟨![ιU σ a, ιU σ b, ιU σ c'], ?_⟩
      rw [← liftGL_diagGL_foote]
      rw [hd]
      rfl
    · intro x hx
      refine exists_pow_mul_of_mem_sup hf3 (A := (At.map (MulAut.conj g₀).toMonoidHom).map φ0) ?_ x hx
      rintro _ ⟨N, hNm, rfl⟩
      exact hφ0comm N
  · refine ⟨φ0 g₀ * c, σ, hσ, Or.inr ⟨ιU σ lam, ιU σ ω, ?_, ?_, ?_⟩⟩
    · exact mem_fixF.1 (lam : fixF σ).2
    · simpa [ιU] using hω.map_of_injective (f := (fixF σ).subtype) Subtype.val_injective
    · rw [key g₀, hH, heisenbergThree, MonoidHom.map_closure, heisCube]
      have hd : φ0 (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL (fixF σ) 1 ω (ω ^ 2)) =
          conjAut 3 F (CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL F 1
            (ιU σ ω) (ιU σ ω ^ 2)) := by
        rw [hφ0, MonoidHom.comp_apply, liftGL_diagGL]
        simp [ιU]
      have hm : φ0 (monomGL (fixF σ) lam) = conjAut 3 F (monomGL F (ιU σ lam)) := by
        rw [hφ0, MonoidHom.comp_apply, liftGL_monomGL]
      rw [← hd, ← hm]
      congr 1
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨x, hx | hx, rfl⟩
        · have : φ0 x = 1 := (hAt_ker x).2 hx
          rw [this]
          exact one_mem _
        · rcases hx with rfl | rfl
          · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
          · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · refine sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_))
          (Subgroup.zpowers_le.2 (Subgroup.subset_closure ?_))
        · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
        · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩

theorem a2ThreeNormalForm_holds : A2ThreeNormalForm :=
  fun _ _ _ h3 _ hB hc => a2Three_cube_normal_form h3 hB hc

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
