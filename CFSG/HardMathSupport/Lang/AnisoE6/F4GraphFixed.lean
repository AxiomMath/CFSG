module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Chevalley.RootWalk

@[expose] def intertwinerCheckZ (y : Bool) (I : List (Fin Tag.E6.rank)) (j : Fin Tag.F4.rank) :
    Bool :=
  (List.range (dim Tag.F4)).all fun p => (List.range 7).all fun n =>
    normalize (orbitLhs y I n p) == normalize (orbitRhs y j n p)

theorem intertwinerCheckZ_x0 :
    intertwinerCheckZ false [⟨1, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem intertwinerCheckZ_x1 :
    intertwinerCheckZ false [⟨3, by decide⟩] ⟨1, by decide⟩ = true := by decide +kernel

theorem intertwinerCheckZ_x2 :
    intertwinerCheckZ false [⟨2, by decide⟩, ⟨4, by decide⟩] ⟨2, by decide⟩ = true := by
  decide +kernel

theorem intertwinerCheckZ_x3 :
    intertwinerCheckZ false [⟨0, by decide⟩, ⟨5, by decide⟩] ⟨3, by decide⟩ = true := by
  decide +kernel

theorem intertwinerCheckZ_y0 :
    intertwinerCheckZ true [⟨1, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem intertwinerCheckZ_y1 :
    intertwinerCheckZ true [⟨3, by decide⟩] ⟨1, by decide⟩ = true := by decide +kernel

theorem intertwinerCheckZ_y2 :
    intertwinerCheckZ true [⟨2, by decide⟩, ⟨4, by decide⟩] ⟨2, by decide⟩ = true := by
  decide +kernel

theorem intertwinerCheckZ_y3 :
    intertwinerCheckZ true [⟨0, by decide⟩, ⟨5, by decide⟩] ⟨3, by decide⟩ = true := by
  decide +kernel

theorem vecOf_eq_of_normalize_eq {τ : Tag} {R : Type*}
    [CommRing R] {v w : List (ℕ × ℤ)} (h : normalize v = normalize w) : vecOf τ R v = vecOf τ R w := by
  rw [← vecOf_normalize v, h, vecOf_normalize]

section Coeff

set_option linter.unusedSectionVars false


theorem coeffOp_comp_of_checkZ_single (K : Type) [CommRing K] {y : Bool}
    {i : Fin Tag.E6.rank} {j : Fin Tag.F4.rank} (h : intertwinerCheckZ y [i] j = true) {n : ℕ}
    (hn : n < 4) :
    coeffOp Tag.E6 K y i n ∘ₗ f4ToE6Module K = f4ToE6Module K ∘ₗ coeffOp Tag.F4 K y j n := by
  simp only [intertwinerCheckZ, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_F4 K fun p hp => ?_
  have e := vecOf_eq_of_normalize_eq (τ := Tag.E6) (R := K) (h p hp n (by omega))
  simp only [orbitLhs, orbitRhs, hn, ↓reduceIte] at e
  rw [LinearMap.comp_apply, LinearMap.comp_apply, f4ToE6Module_posVec K hp,
    (coeffOp_vecOf simpleRow_E6 e6_allValid K y i hn (validVec_f4ToE6Pos p)).1, e,
    f4ToE6Module_coeffOp K y j hn hp]

theorem coeffOp_comp_of_checkZ_pair (K : Type) [CommRing K] {y : Bool}
    {i i' : Fin Tag.E6.rank} {j : Fin Tag.F4.rank} (h : intertwinerCheckZ y [i, i'] j = true)
    {n : ℕ} (hn : n < 7) :
    ∑ k ∈ Finset.range 4, (if k ≤ n ∧ n - k < 4 then
      (coeffOp Tag.E6 K y i k * coeffOp Tag.E6 K y i' (n - k)) ∘ₗ f4ToE6Module K else 0) =
      if n < 4 then f4ToE6Module K ∘ₗ coeffOp Tag.F4 K y j n else 0 := by
  simp only [intertwinerCheckZ, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_F4 K fun p hp => ?_
  have e := vecOf_eq_of_normalize_eq (τ := Tag.E6) (R := K) (h p hp n hn)
  simp only [orbitLhs, orbitRhs, vecOf_flatMap_range] at e
  rw [LinearMap.sum_apply]
  have hL : ∀ k ∈ Finset.range 4,
      (if k ≤ n ∧ n - k < 4 then (coeffOp Tag.E6 K y i k * coeffOp Tag.E6 K y i' (n - k)) ∘ₗ
        f4ToE6Module K else 0) (posVec Tag.F4 K p) =
      vecOf Tag.E6 K (if k ≤ n ∧ n - k < 4 then
        coeffVec .E6 y i k (coeffVec .E6 y i' (n - k) (f4ToE6Pos p)) else []) := by
    intro k hk
    split_ifs with hc
    · have hk4 : k < 4 := Finset.mem_range.1 hk
      obtain ⟨e1, hv1⟩ := coeffOp_vecOf simpleRow_E6 e6_allValid K y i' hc.2
        (validVec_f4ToE6Pos p)
      rw [LinearMap.comp_apply, Module.End.mul_apply, f4ToE6Module_posVec K hp, e1,
        (coeffOp_vecOf simpleRow_E6 e6_allValid K y i hk4 hv1).1]
    · simp
  rw [Finset.sum_congr rfl hL, e]
  split_ifs with hn4
  · rw [LinearMap.comp_apply, f4ToE6Module_coeffOp K y j hn4 hp]
  · simp

theorem f4OrbitX_comp_f4ToE6Module_all (R : Type) [CommRing R] (j : Fin Tag.F4.rank) (c : R) :
    f4OrbitX R j c ∘ₗ f4ToE6Module R = f4ToE6Module R ∘ₗ xOp Tag.F4 R j c := by
  fin_cases j
  · show [xOp Tag.E6 R ⟨1, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_single R intertwinerCheckZ_x0 hn) c
  · show [xOp Tag.E6 R ⟨3, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_single R intertwinerCheckZ_x1 hn) c
  · show [xOp Tag.E6 R ⟨2, by decide⟩ c, xOp Tag.E6 R ⟨4, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff,
      xOp_eq_sum_xCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_pair R intertwinerCheckZ_x2 hn) c
  · show [xOp Tag.E6 R ⟨0, by decide⟩ c, xOp Tag.E6 R ⟨5, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff,
      xOp_eq_sum_xCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_pair R intertwinerCheckZ_x3 hn) c

theorem f4OrbitY_comp_f4ToE6Module_all (R : Type) [CommRing R] (j : Fin Tag.F4.rank) (c : R) :
    f4OrbitY R j c ∘ₗ f4ToE6Module R = f4ToE6Module R ∘ₗ yOp Tag.F4 R j c := by
  fin_cases j
  · show [yOp Tag.E6 R ⟨1, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_single R intertwinerCheckZ_y0 hn) c
  · show [yOp Tag.E6 R ⟨3, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_single R intertwinerCheckZ_y1 hn) c
  · show [yOp Tag.E6 R ⟨2, by decide⟩ c, yOp Tag.E6 R ⟨4, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff,
      yOp_eq_sum_yCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_pair R intertwinerCheckZ_y2 hn) c
  · show [yOp Tag.E6 R ⟨0, by decide⟩ c, yOp Tag.E6 R ⟨5, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff,
      yOp_eq_sum_yCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_checkZ_pair R intertwinerCheckZ_y3 hn) c

variable {K : Type} [Field K]

theorem e6FixedToF4_f4OrbitXUnit_all (j : Fin Tag.F4.rank) (c : K) :
    e6FixedToF4 K ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩ = xUnit Tag.F4 K j c := by
  refine Units.ext ?_
  rw [coe_e6FixedToF4, coe_xUnit, e6RestrictEnd]
  change e6ToF4Module K ∘ₗ e6EndHom K (f4OrbitXUnit K j c) ∘ₗ f4ToE6Module K = _
  rw [e6EndHom_f4OrbitXUnit, f4OrbitX_comp_f4ToE6Module_all K j c, ← LinearMap.comp_assoc,
    e6ToF4Module_comp_f4ToE6Module, LinearMap.id_comp]

theorem e6FixedToF4_f4OrbitYUnit_all (j : Fin Tag.F4.rank) (c : K) :
    e6FixedToF4 K ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩ = yUnit Tag.F4 K j c := by
  refine Units.ext ?_
  rw [coe_e6FixedToF4, coe_yUnit, e6RestrictEnd]
  change e6ToF4Module K ∘ₗ e6EndHom K (f4OrbitYUnit K j c) ∘ₗ f4ToE6Module K = _
  rw [e6EndHom_f4OrbitYUnit, f4OrbitY_comp_f4ToE6Module_all K j c, ← LinearMap.comp_assoc,
    e6ToF4Module_comp_f4ToE6Module, LinearMap.id_comp]

theorem adjointGroup_le_range_e6FixedToF4_all :
    adjointGroup Tag.F4 K ≤ (e6FixedToF4 K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨j, c, hg | hg⟩
  · rw [show g = xUnit Tag.F4 K j c from Units.ext hg]
    exact ⟨_, e6FixedToF4_f4OrbitXUnit_all j c⟩
  · rw [show g = yUnit Tag.F4 K j c from Units.ext hg]
    exact ⟨_, e6FixedToF4_f4OrbitYUnit_all j c⟩

theorem e6FixedToF4_mem_adjointGroup_all
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    e6FixedToF4 K g ∈ adjointGroup Tag.F4 K := by
  set H := (adjointGroup Tag.F4 K).comap (e6FixedToF4 K)
  have hle : twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≤
      H.map (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).subtype := by
    conv_lhs => rw [twistedFixedGroup_id_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, c, rfl | rfl⟩
    · refine ⟨⟨_, f4OrbitXUnit_mem j c⟩, ?_, rfl⟩
      change e6FixedToF4 K ⟨_, f4OrbitXUnit_mem j c⟩ ∈ adjointGroup Tag.F4 K
      rw [e6FixedToF4_f4OrbitXUnit_all]
      exact xUnit_mem_adjointGroup j c
    · refine ⟨⟨_, f4OrbitYUnit_mem j c⟩, ?_, rfl⟩
      change e6FixedToF4 K ⟨_, f4OrbitYUnit_mem j c⟩ ∈ adjointGroup Tag.F4 K
      rw [e6FixedToF4_f4OrbitYUnit_all]
      exact yUnit_mem_adjointGroup j c
  obtain ⟨h, hh, hgh⟩ := hle g.2
  rw [show g = h from Subtype.ext hgh.symm]
  exact hh

variable (K) in
@[expose] def e6FixedToF4GroupAll :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) →* adjointGroup Tag.F4 K :=
  (e6FixedToF4 K).codRestrict _ e6FixedToF4_mem_adjointGroup_all

theorem e6FixedToF4GroupAll_surjective :
    Function.Surjective (e6FixedToF4GroupAll K) := fun g => by
  obtain ⟨x, hx⟩ := adjointGroup_le_range_e6FixedToF4_all g.2
  exact ⟨x, Subtype.ext hx⟩

theorem e6FixedToF4GroupAll_injective :
    Function.Injective (e6FixedToF4GroupAll K) := by
  have hC0 : graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom ≤
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := graphFixedRootGroup_le _ _ _
  set ψ := (e6FixedToF4GroupAll K).comp (Subgroup.inclusion hC0)
  have hΓ : ∀ g : twistedFixedGroup TwistTag.E6 K (RingHom.id K),
      (g : ModGL TwistTag.E6.tag K) ∈
        graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom := fun g =>
    (e6_twistedFixedGroup_id_eq_graphFixedRootGroup K).le g.2
  have hψ : Function.Surjective ψ := fun x => by
    obtain ⟨g, rfl⟩ := e6FixedToF4GroupAll_surjective x
    exact ⟨⟨g, hΓ g⟩, rfl⟩
  have hker : ψ.ker = ⊥ := by
    by_contra hne
    have hM : ¬ ψ.ker ≤ Subgroup.center
        (graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom) := by
      rw [center_graphFixedRootGroup_eq_bot (σ := (RingEquiv.refl K).toRingHom)
        (RingEquiv.refl K).surjective]
      exact fun h => hne (le_bot_iff.1 h)
    have := fixed_noncentral_normal_solvable_quotient TwistTag.E6 K (RingEquiv.refl K) ψ.ker hM
    have : Group.IsSolvable (adjointGroup Tag.F4 K) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toMonoidHom)
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).surjective
    have := nontrivial_adjointGroup_F4 (K := K)
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (adjointGroup Tag.F4 K)
    rw [single_edge_perfect Tag.F4 K (Or.inl rfl)] at hlt
    exact lt_irrefl _ hlt
  intro g g' hgg'
  have hinj := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  have h : (⟨g, hΓ g⟩ : graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom) =
      ⟨g', hΓ g'⟩ := hinj hgg'
  have h' := congrArg (fun x : graphFixedRootGroup TwistTag.E6 K (RingEquiv.refl K).toRingHom =>
    (x : ModGL TwistTag.E6.tag K)) h
  exact Subtype.ext h'

variable (K) in
@[expose] def e6FixedF4EquivAll :
    twistedFixedGroup TwistTag.E6 K (RingHom.id K) ≃* adjointGroup Tag.F4 K :=
  MulEquiv.ofBijective (e6FixedToF4GroupAll K)
    ⟨e6FixedToF4GroupAll_injective, e6FixedToF4GroupAll_surjective⟩

theorem coe_e6FixedF4EquivAll (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    (e6FixedF4EquivAll K g : ModGL Tag.F4 K) = e6FixedToF4 K g :=
  rfl

end Coeff

end CFSG.HardMathSupport.Lang.AnisoE6
