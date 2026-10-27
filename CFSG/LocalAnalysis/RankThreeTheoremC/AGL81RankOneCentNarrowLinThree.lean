module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenNarrow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowCriteria

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Model

variable {F : Type} [Field F] [Finite F]

private theorem transvection_pow_char (p : ℕ) [CharP F p] {i j : Fin 3} (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ^ p = 1 := by
  have h : ∀ n : ℕ, SpecialLinearGroup.transvection hij c ^ n =
      SpecialLinearGroup.transvection hij ((n : F) * c) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add]
      congr 1
      push_cast
      ring
  rw [h, CharP.cast_eq_zero, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem centralizer_proj_transvection_le_narrowGamma (p : ℕ) [Fact p.Prime] [CharP F p]
    {i j : Fin 3} (hij : i < j) (hij02 : ¬ (i = 0 ∧ j = 2)) :
    centralizer ({proj 3 F (SpecialLinearGroup.transvection hij.ne (1 : F))} :
        Set (projectiveSL 3 F)) ≤
      narrowGamma p (projUnitriangular 3 F) := by
  have hp : p.Prime := Fact.out
  have h02 : (0 : Fin 3) < 2 := by decide
  set x := proj 3 F (SpecialLinearGroup.transvection hij.ne (1 : F)) with hx
  set z := proj 3 F (SpecialLinearGroup.transvection h02.ne (1 : F)) with hz
  have hxU : x ∈ projUnitriangular 3 F := mem_map_of_mem _ (transvection_mem_unitriangular hij 1)
  have hzU : z ∈ projUnitriangular 3 F := mem_map_of_mem _ (transvection_mem_unitriangular h02 1)
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, transvection_pow_char p, map_one]
  have hzp : z ^ p = 1 := by rw [hz, ← map_pow, transvection_pow_char p, map_one]
  have hx1 : x ≠ 1 := by
    rw [hx, Ne, proj_eq_one_iff, scalars_eq_center, SpecialLinearGroup.transvection_mem_center_iff]
    exact one_ne_zero
  have hxz : Commute x z := by
    refine Commute.map (SpecialLinearGroup.commute_transvection hij.ne h02.ne ?_ ?_ 1 1) _
    · exact (by decide : ∀ a b : Fin 3, a < b → b ≠ 0) i j hij
    · exact (by decide : ∀ a b : Fin 3, a < b → (2 : Fin 3) ≠ a) i j hij
  have hzx : z ∉ zpowers x := by
    intro hzx
    have hle : zpowers x ≤ (SpecialLinearGroup.transvectionHom (n := Fin 3) (A := F)
        hij.ne).range.map (proj 3 F) :=
      zpowers_le.mpr (mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, by simp⟩))
    obtain ⟨g, hg, hgz⟩ := hle hzx
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [SpecialLinearGroup.transvectionHom_apply] at hgz
    have heq := proj_injOn_unitriangular 3 (transvection_mem_unitriangular hij _)
      (transvection_mem_unitriangular h02 1) hgz
    have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 2)
      heq
    simp [SpecialLinearGroup.transvection_coe, hij02] at h'
  have hE : IsElemAbelian p (closure ({x, z} : Set (projectiveSL 3 F))) :=
    IsElemAbelian.closure_of_commute
      (by rintro a (rfl | rfl) b (rfl | rfl); exacts [rfl, hxz.eq, hxz.eq.symm, rfl])
      (by rintro a (rfl | rfl); exacts [hxp, hzp])
  have hEc := CFSG.HardMathSupport.Dickson.I271.card_closure_pair_sq hxz hxp hzp hx1 hzx
  refine centralizer_le_narrowGamma hxU (orderOf_eq_prime hxp hx1) ?_
  refine CFSG.SectionRank.le_pRank hp.one_lt (le_inf ?_ ?_) hE hEc
  · rw [closure_le]
    rintro a (rfl | rfl)
    exacts [hxU, hzU]
  · rw [closure_le]
    rintro a (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact mem_centralizer_singleton_iff.mpr hxz.eq.symm

theorem narrowGamma_projUnitriangular_eq_top (p : ℕ) [Fact p.Prime] [CharP F p] :
    narrowGamma p (projUnitriangular 3 F) = ⊤ := by
  set Γ := narrowGamma p (projUnitriangular 3 F)
  have h01 : (0 : Fin 3) < 1 := by decide
  have h12 : (1 : Fin 3) < 2 := by decide
  have hC₁ := centralizer_proj_transvection_le_narrowGamma (F := F) p h01 (by decide)
  have hC₂ := centralizer_proj_transvection_le_narrowGamma (F := F) p h12 (by decide)
  have hX₁ : ∀ {k l : Fin 3} (hkl : k ≠ l), l ≠ 0 → (1 : Fin 3) ≠ k → ∀ t : F,
      proj 3 F (SpecialLinearGroup.transvection hkl t) ∈ Γ := fun hkl hl hk t =>
    hC₁ (mem_centralizer_singleton_iff.mpr
      ((SpecialLinearGroup.commute_transvection hkl h01.ne hl hk t 1).map (proj 3 F)).eq)
  have hX₂ : ∀ {k l : Fin 3} (hkl : k ≠ l), l ≠ 1 → (2 : Fin 3) ≠ k → ∀ t : F,
      proj 3 F (SpecialLinearGroup.transvection hkl t) ∈ Γ := fun hkl hl hk t =>
    hC₂ (mem_centralizer_singleton_iff.mpr
      ((SpecialLinearGroup.commute_transvection hkl h12.ne hl hk t 1).map (proj 3 F)).eq)
  have hX₂₀ : ∀ t : F,
      proj 3 F (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t) ∈ Γ := by
    intro t
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    have h := SpecialLinearGroup.commutatorElement_transvection h21 h10
      (show (2 : Fin 3) ≠ 0 by decide) t (1 : F)
    rw [mul_one] at h
    rw [← h, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    have ha := hX₁ h21 (by decide) (by decide) t
    have hb := hX₂ h10 (by decide) (by decide) 1
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)) (Γ.inv_mem hb)
  have hall : ∀ {k l : Fin 3} (hkl : k ≠ l) (t : F),
      proj 3 F (SpecialLinearGroup.transvection hkl t) ∈ Γ := by
    intro k l hkl t
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact hX₂₀ t
      | exact hX₁ hkl (by decide) (by decide) t
      | exact hX₂ hkl (by decide) (by decide) t
  have hH : Γ.comap (proj 3 F) = ⊤ := by
    rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      closure_le]
    rintro _ ⟨t, rfl⟩
    exact hall t.hij t.c
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := proj_surjective 3 F y
  have hg : g ∈ Γ.comap (proj 3 F) := by
    rw [hH]
    exact mem_top g
  exact hg

end Model

theorem narrowGamma_eq_top_linThree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow p K) : narrowGamma p (T : Subgroup K) = ⊤ := by
  obtain ⟨q, rfl, -, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  change x = _ at hdq
  subst hdq
  haveI : Fact q.p.Prime := ⟨hp⟩
  obtain ⟨f⟩ := hK
  let e : TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩ ≃*
      projectiveSL 3 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField q.p q.exponent))
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := GaloisField q.p q.exponent) q.p (n := 3)
    (by norm_num)
  refine narrowGamma_eq_top_of_sylow hp (e.symm.trans f.symm) S ?_ T
  rw [hS]
  exact narrowGamma_projUnitriangular_eq_top q.p

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
