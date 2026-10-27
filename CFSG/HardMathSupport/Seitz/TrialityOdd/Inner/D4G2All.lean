module

public import CFSG.RankThree.PartTwo.KFacts.K71D4G2Group

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Chevalley.RootWalk CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (vecBEq vecBEq_iff)

@[expose] def d4IntertwinerCheckAll (y : Bool) (I : List (Fin Tag.D4.rank)) (j : Fin Tag.G2.rank) :
    Bool :=
  (List.range (dim Tag.G2)).all fun p => (List.range 7).all fun n =>
    normalize (d4OrbitLhs y I n p) == normalize (d4OrbitRhs y j n p)

theorem d4IntertwinerCheckAll_x0 :
    d4IntertwinerCheckAll false [⟨2, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem d4IntertwinerCheckAll_x1 :
    d4IntertwinerCheckAll false [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] ⟨1, by decide⟩ =
      true := by
  decide +kernel

theorem d4IntertwinerCheckAll_y0 :
    d4IntertwinerCheckAll true [⟨2, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem d4IntertwinerCheckAll_y1 :
    d4IntertwinerCheckAll true [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] ⟨1, by decide⟩ =
      true := by
  decide +kernel

theorem d4_coeffOp_comp_of_checkAll_single (K : Type) [CommRing K] {y : Bool}
    {i : Fin Tag.D4.rank} {j : Fin Tag.G2.rank} (h : d4IntertwinerCheckAll y [i] j = true) {n : ℕ}
    (hn : n < 4) :
    coeffOp Tag.D4 K y i n ∘ₗ g2ToD4Module K = g2ToD4Module K ∘ₗ coeffOp Tag.G2 K y j n := by
  simp only [d4IntertwinerCheckAll, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_G2 K fun p hp => ?_
  have e := vecOf_eq_of_normalize_eq (τ := Tag.D4) (R := K) (h p hp n (by omega))
  simp only [d4OrbitLhs, d4OrbitRhs, hn, ↓reduceIte] at e
  rw [LinearMap.comp_apply, LinearMap.comp_apply, g2ToD4Module_posVec K hp,
    (coeffOp_vecOf simpleRow_D4_all d4_allValid K y i hn (validVec_g2ToD4Pos p)).1, e,
    g2ToD4Module_coeffOp K y j hn hp]

theorem d4_coeffOp_comp_of_checkAll_triple (K : Type) [CommRing K] {y : Bool}
    {i i' i'' : Fin Tag.D4.rank} {j : Fin Tag.G2.rank}
    (h : d4IntertwinerCheckAll y [i, i', i''] j = true) {n : ℕ} (hn : n < 7) :
    ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3, (if k + l ≤ n ∧ n - (k + l) < 3 then
      (coeffOp Tag.D4 K y i k * coeffOp Tag.D4 K y i' l * coeffOp Tag.D4 K y i'' (n - (k + l))) ∘ₗ
        g2ToD4Module K else 0) =
      if n < 4 then g2ToD4Module K ∘ₗ coeffOp Tag.G2 K y j n else 0 := by
  simp only [d4IntertwinerCheckAll, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_G2 K fun p hp => ?_
  have e := vecOf_eq_of_normalize_eq (τ := Tag.D4) (R := K) (h p hp n hn)
  simp only [d4OrbitLhs, d4OrbitRhs] at e
  have hflat : vecOf Tag.D4 K ((List.range 3).flatMap fun k => (List.range 3).flatMap fun l =>
      if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k (coeffVec .D4 y i' l
        (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) =
      ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3, vecOf Tag.D4 K
        (if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k (coeffVec .D4 y i' l
          (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) := by
    rw [vecOf_flatMap_range]
    exact Finset.sum_congr rfl fun k _ => vecOf_flatMap_range 3 _
  rw [hflat] at e
  rw [LinearMap.sum_apply]
  have hL : ∀ k ∈ Finset.range 3, ∀ l ∈ Finset.range 3,
      (if k + l ≤ n ∧ n - (k + l) < 3 then (coeffOp Tag.D4 K y i k * coeffOp Tag.D4 K y i' l *
        coeffOp Tag.D4 K y i'' (n - (k + l))) ∘ₗ g2ToD4Module K else 0) (posVec Tag.G2 K p) =
      vecOf Tag.D4 K (if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k
        (coeffVec .D4 y i' l (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) := by
    intro k hk l hl
    by_cases hc : k + l ≤ n ∧ n - (k + l) < 3
    · rw [ite_eq_left hc, ite_eq_left hc]
      have hk4 : k < 4 := by have := Finset.mem_range.1 hk; omega
      have hl4 : l < 4 := by have := Finset.mem_range.1 hl; omega
      obtain ⟨e1, hv1⟩ := coeffOp_vecOf (k := n - (k + l)) simpleRow_D4_all d4_allValid K y i''
        (by omega) (validVec_g2ToD4Pos p)
      obtain ⟨e2, hv2⟩ := coeffOp_vecOf simpleRow_D4_all d4_allValid K y i' hl4 hv1
      rw [LinearMap.comp_apply, Module.End.mul_apply, Module.End.mul_apply,
        g2ToD4Module_posVec K hp, e1, e2,
        (coeffOp_vecOf simpleRow_D4_all d4_allValid K y i hk4 hv2).1]
    · rw [ite_eq_right hc, ite_eq_right hc]
      simp
  have hsum : ∑ k ∈ Finset.range 3, (∑ l ∈ Finset.range 3,
      (if k + l ≤ n ∧ n - (k + l) < 3 then (coeffOp Tag.D4 K y i k * coeffOp Tag.D4 K y i' l *
        coeffOp Tag.D4 K y i'' (n - (k + l))) ∘ₗ g2ToD4Module K else 0)) (posVec Tag.G2 K p) =
      ∑ k ∈ Finset.range 3, ∑ l ∈ Finset.range 3, vecOf Tag.D4 K
        (if k + l ≤ n ∧ n - (k + l) < 3 then coeffVec .D4 y i k (coeffVec .D4 y i' l
          (coeffVec .D4 y i'' (n - (k + l)) (g2ToD4Pos p))) else []) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun l hl => hL k hk l hl
  rw [hsum, e]
  split_ifs with hn4
  · rw [LinearMap.comp_apply, g2ToD4Module_coeffOp K y j hn4 hp]
  · simp


theorem g2OrbitX_comp_g2ToD4ModuleAll (R : Type) [CommRing R]
    (j : Fin Tag.G2.rank) (c : R) :
    g2OrbitX R j c ∘ₗ g2ToD4Module R = g2ToD4Module R ∘ₗ xOp Tag.G2 R j c := by
  fin_cases j
  · show [xOp Tag.D4 R ⟨2, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => d4_coeffOp_comp_of_checkAll_single R d4IntertwinerCheckAll_x0 hn) c
  · show [xOp Tag.D4 R ⟨0, by decide⟩ c, xOp Tag.D4 R ⟨1, by decide⟩ c,
      xOp Tag.D4 R ⟨3, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_cons, List.prod_cons, List.prod_singleton, ← mul_assoc, xOp_D4_eq_sum,
      xOp_D4_eq_sum, xOp_D4_eq_sum, xOp_eq_sum_xCoeff]
    exact triple_poly_comp R _ _ _ _ _
      (fun n hn => d4_coeffOp_comp_of_checkAll_triple R d4IntertwinerCheckAll_x1 hn) c

theorem g2OrbitY_comp_g2ToD4ModuleAll (R : Type) [CommRing R]
    (j : Fin Tag.G2.rank) (c : R) :
    g2OrbitY R j c ∘ₗ g2ToD4Module R = g2ToD4Module R ∘ₗ yOp Tag.G2 R j c := by
  fin_cases j
  · show [yOp Tag.D4 R ⟨2, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => d4_coeffOp_comp_of_checkAll_single R d4IntertwinerCheckAll_y0 hn) c
  · show [yOp Tag.D4 R ⟨0, by decide⟩ c, yOp Tag.D4 R ⟨1, by decide⟩ c,
      yOp Tag.D4 R ⟨3, by decide⟩ c].prod ∘ₗ g2ToD4Module R = _
    rw [List.prod_cons, List.prod_cons, List.prod_singleton, ← mul_assoc, yOp_D4_eq_sum,
      yOp_D4_eq_sum, yOp_D4_eq_sum, yOp_eq_sum_yCoeff]
    exact triple_poly_comp R _ _ _ _ _
      (fun n hn => d4_coeffOp_comp_of_checkAll_triple R d4IntertwinerCheckAll_y1 hn) c


variable {K : Type} [Field K]

theorem d4FixedToG2_g2OrbitXUnitAll (j : Fin Tag.G2.rank) (c : K) :
    d4FixedToG2 K ⟨g2OrbitXUnit K j c, g2OrbitXUnit_mem j c⟩ = xUnit Tag.G2 K j c := by
  refine Units.ext ?_
  rw [coe_d4FixedToG2, coe_xUnit, d4RestrictEnd]
  change d4ToG2Module K ∘ₗ d4EndHom K (g2OrbitXUnit K j c) ∘ₗ g2ToD4Module K = _
  rw [d4EndHom_g2OrbitXUnit, g2OrbitX_comp_g2ToD4ModuleAll K j c, ← LinearMap.comp_assoc,
    d4ToG2Module_comp_g2ToD4Module, LinearMap.id_comp]

theorem d4FixedToG2_g2OrbitYUnitAll (j : Fin Tag.G2.rank) (c : K) :
    d4FixedToG2 K ⟨g2OrbitYUnit K j c, g2OrbitYUnit_mem j c⟩ = yUnit Tag.G2 K j c := by
  refine Units.ext ?_
  rw [coe_d4FixedToG2, coe_yUnit, d4RestrictEnd]
  change d4ToG2Module K ∘ₗ d4EndHom K (g2OrbitYUnit K j c) ∘ₗ g2ToD4Module K = _
  rw [d4EndHom_g2OrbitYUnit, g2OrbitY_comp_g2ToD4ModuleAll K j c, ← LinearMap.comp_assoc,
    d4ToG2Module_comp_g2ToD4Module, LinearMap.id_comp]


theorem d4FixedToG2_mem_adjointGroupAll
    (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    d4FixedToG2 K g ∈ adjointGroup Tag.G2 K := by
  set H := (adjointGroup Tag.G2 K).comap (d4FixedToG2 K)
  have hle : twistedFixedGroup TwistTag.D4 K (RingHom.id K) ≤
      H.map (twistedFixedGroup TwistTag.D4 K (RingHom.id K)).subtype := by
    conv_lhs => rw [d4_twistedFixedGroup_id_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, c, rfl | rfl⟩
    · refine ⟨⟨_, g2OrbitXUnit_mem j c⟩, ?_, rfl⟩
      change d4FixedToG2 K ⟨_, g2OrbitXUnit_mem j c⟩ ∈ adjointGroup Tag.G2 K
      rw [d4FixedToG2_g2OrbitXUnitAll ]
      exact xUnit_mem_adjointGroup j c
    · refine ⟨⟨_, g2OrbitYUnit_mem j c⟩, ?_, rfl⟩
      change d4FixedToG2 K ⟨_, g2OrbitYUnit_mem j c⟩ ∈ adjointGroup Tag.G2 K
      rw [d4FixedToG2_g2OrbitYUnitAll ]
      exact yUnit_mem_adjointGroup j c
  obtain ⟨h, hh, hgh⟩ := hle g.2
  rw [show g = h from Subtype.ext hgh.symm]
  exact hh

theorem adjointGroup_le_range_d4FixedToG2All :
    adjointGroup Tag.G2 K ≤ (d4FixedToG2 K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨j, c, hg | hg⟩
  · rw [show g = xUnit Tag.G2 K j c from Units.ext hg]
    exact ⟨_, d4FixedToG2_g2OrbitXUnitAll j c⟩
  · rw [show g = yUnit Tag.G2 K j c from Units.ext hg]
    exact ⟨_, d4FixedToG2_g2OrbitYUnitAll j c⟩

variable (K) in
@[expose] def d4FixedToG2GroupAll :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) →* adjointGroup Tag.G2 K :=
  (d4FixedToG2 K).codRestrict _ (d4FixedToG2_mem_adjointGroupAll )

theorem d4FixedToG2Group_surjectiveAll :
    Function.Surjective (d4FixedToG2GroupAll K ) := fun g => by
  obtain ⟨x, hx⟩ := adjointGroup_le_range_d4FixedToG2All g.2
  exact ⟨x, Subtype.ext hx⟩


theorem d4FixedToG2Group_injective_of_three_leAll
    (hK3 : (3 : ℕ∞) ≤ ENat.card K) : Function.Injective (d4FixedToG2GroupAll K ) := by
  have hC0 : graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom ≤
      twistedFixedGroup TwistTag.D4 K (RingHom.id K) := graphFixedRootGroup_le _ _ _
  set ψ := (d4FixedToG2GroupAll K ).comp (Subgroup.inclusion hC0)
  have hΓ : ∀ g : twistedFixedGroup TwistTag.D4 K (RingHom.id K),
      (g : ModGL TwistTag.D4.tag K) ∈
        graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom := fun g =>
    (d4_twistedFixedGroup_id_eq_graphFixedRootGroup K).le g.2
  have hψ : Function.Surjective ψ := fun x => by
    obtain ⟨g, rfl⟩ := d4FixedToG2Group_surjectiveAll x
    exact ⟨⟨g, hΓ g⟩, rfl⟩
  have hker : ψ.ker = ⊥ := by
    by_contra hne
    have hM : ¬ ψ.ker ≤ Subgroup.center
        (graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom) := by
      rw [center_graphFixedRootGroup_eq_bot (σ := (RingEquiv.refl K).toRingHom)
        (RingEquiv.refl K).surjective]
      exact fun h => hne (le_bot_iff.1 h)
    have := fixed_noncentral_normal_solvable_quotient TwistTag.D4 K (RingEquiv.refl K) ψ.ker hM
    have : Group.IsSolvable (adjointGroup Tag.G2 K) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).surjective
    have := nontrivial_adjointGroup_G2 (K := K)
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (adjointGroup Tag.G2 K)
    rw [generated_group_perfect_away_from_two Tag.G2 K hK3] at hlt
    exact lt_irrefl _ hlt
  intro g g' hgg'
  have hinj := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  have h : (⟨g, hΓ g⟩ : graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom) =
      ⟨g', hΓ g'⟩ := hinj hgg'
  have h' := congrArg (fun x : graphFixedRootGroup TwistTag.D4 K (RingEquiv.refl K).toRingHom =>
    (x : ModGL TwistTag.D4.tag K)) h
  exact Subtype.ext h'


variable (K) in
@[expose] def d4FixedG2EquivAll (hK3 : (3 : ℕ∞) ≤ ENat.card K) :
    twistedFixedGroup TwistTag.D4 K (RingHom.id K) ≃* adjointGroup Tag.G2 K :=
  MulEquiv.ofBijective (d4FixedToG2GroupAll K )
    ⟨d4FixedToG2Group_injective_of_three_leAll hK3, d4FixedToG2Group_surjectiveAll ⟩

theorem coe_d4FixedG2EquivAll (hK3 : (3 : ℕ∞) ≤ ENat.card K)
    (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) :
    (d4FixedG2EquivAll K hK3 g : ModGL Tag.G2 K) = d4FixedToG2 K g :=
  rfl

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
