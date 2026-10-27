module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.Reduction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem card_le_three_of_isCyclic_pow_three (H : Type) [Group H] [IsCyclic H] [Finite H]
    (h : ∀ x : H, x ^ 3 = 1) : Nat.card H ≤ 3 := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hc := IsCyclic.card_pow_eq_one_le (α := H) (n := 3) (by norm_num)
  simp only [h, Finset.filter_true_of_mem, Finset.mem_univ, implies_true] at hc
  rw [Nat.card_eq_fintype_card]
  simpa using hc

theorem ker_comp_congr_eq {S C G : Type} [Group S] [Group C] [Group G] (e : S ≃* C)
    (Θ : MulAut C →* G) (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) :
    (Θ.comp (MulAut.congr e).toMonoidHom).ker = (MulAut.conj : S →* MulAut S).range := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have h1 : Θ (MulAut.congr e x) = 1 ↔
      MulAut.congr e x ∈ (MulAut.conj : C →* MulAut C).range := by
    rw [← hker, MonoidHom.mem_ker]
  rw [h1, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    apply (MulAut.congr e).injective
    rw [← hc]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · rintro ⟨s, rfl⟩
    refine ⟨e s, ?_⟩
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem card_le_three_mul_inf_inner_of_hom {S G : Type} [Group S] [Group G] [IsCyclic G]
    (Θ : MulAut S →* G) (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ innerAutS S) := by
  by_cases hfin : Finite E
  swap
  · haveI : Infinite E := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  let f : E →* G := Θ.comp E.subtype
  have hmem : ∀ x : MulAut S, Θ x = 1 ↔ x ∈ innerAutS S := fun x => by
    rw [← MonoidHom.mem_ker, hker]
    rfl
  have hK : f.ker.map E.subtype = E ⊓ innerAutS S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hmem _).1 hy⟩
    · rintro ⟨hxE, hxI⟩
      exact ⟨⟨x, hxE⟩, (hmem x).2 hxI, rfl⟩
  have hKc : Nat.card ↥(E ⊓ innerAutS S) = Nat.card f.ker := by
    rw [← hK, Subgroup.card_map_of_injective E.subtype_injective]
  have hL : Nat.card E = Nat.card (E ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hQ : Nat.card (E ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hR : Nat.card f.range ≤ 3 := by
    haveI : Finite f.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective f)
    refine card_le_three_of_isCyclic_pow_three f.range fun x => ?_
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp x.2
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hE.2 _ y.2)
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hy, ← map_pow, hy3, map_one]
  rw [hL, hQ, hKc]
  exact Nat.mul_le_mul_right _ hR

theorem isoLie_trialityD4_of_catalogIs {S : Type} [Group S] (hS : catalogIs S isTD4Any) :
    ∃ q : TauCeti.PrimePower, IsoLie S (TauCeti.LieTypeIndex.trialityD4 q) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨d, hv⟩ | s
  · simp [isTD4Any, onLie] at hi
  · simp [isTD4Any, onLie] at hi
  · cases d <;> first | exact ⟨_, hv, ⟨e⟩⟩ | simp [isTD4Any, onLie] at hi
  · simp [isTD4Any, onLie] at hi

section TriD4Out


theorem exists_cyclic_hom_of_isoLie_trialityD4 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hS : IsoLie S (TauCeti.LieTypeIndex.trialityD4 q)) :
    ∃ (K : Type) (_ : Field K) (Θ : MulAut S →* (K ≃+* K)),
      IsCyclic (K ≃+* K) ∧ Θ.ker = (MulAut.conj : S →* MulAut S).range := by
  by_cases hq2 : q.p = 2
  · obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.CTP.exists_trialityD4_model hq2 hS
    obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
      CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form q.exponent_pos X hX σ hσ
    exact ⟨X, inferInstance, Θ.comp (MulAut.congr e).toMonoidHom, hcyc,
      ker_comp_congr_eq e Θ hker⟩
  · obtain ⟨X, _, _, σ, hX, hσ, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Seitz.TrialityOdd.exists_trialityD4_model_odd hq2 hS
    obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
      CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form q.prime_p hq2
        q.exponent_pos X hX σ hσ
    exact ⟨X, inferInstance, Θ.comp (MulAut.congr e).toMonoidHom, hcyc,
      ker_comp_congr_eq e Θ hker⟩

theorem I2023FactOutCyclic_holds : I2023FactOutCyclic := by
  intro S _ _ hS E hE
  obtain ⟨q, hq⟩ := isoLie_trialityD4_of_catalogIs hS
  obtain ⟨K, _, Θ, hcyc, hker⟩ := exists_cyclic_hom_of_isoLie_trialityD4 q hq
  haveI : IsCyclic (K ≃+* K) := hcyc
  exact card_le_three_mul_inf_inner_of_hom Θ hker hE

end TriD4Out

end CFSG.LocalAnalysis.GLTheoremA.I2023
