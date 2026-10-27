module

public import CFSG.CharacterTheory.Semidihedral.Principal.RationalOddCharacter
public import CFSG.CharacterTheory.Semidihedral.Principal.CosetConstantHalfDegree
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

namespace QuaternionSixteen

theorem regular_character_apply {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q] (q : Q) :
    (Representation.ofMulAction ℂ Q Q).character q = if q = 1 then (Nat.card Q : ℂ) else 0 := by
  classical
  let sigma : Equiv.Perm Q := MulAction.toPerm q
  let T : MonoidAlgebra ℂ Q ≃ₗ[ℂ] MonoidAlgebra ℂ Q :=
    MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ sigma
  have hT : ∀ x, T (MonoidAlgebra.basis Q ℂ x) = MonoidAlgebra.basis Q ℂ (sigma x) := by
    intro x
    simp [T]
  have hmap : (Representation.ofMulAction ℂ Q Q q) = T.toLinearMap := by
    apply (MonoidAlgebra.basis Q ℂ).ext
    intro x
    simp [T, sigma]
  change LinearMap.trace ℂ (MonoidAlgebra ℂ Q) (Representation.ofMulAction ℂ Q Q q) = _
  rw [hmap, CFSG.Theory.Character.trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis
    (MonoidAlgebra.basis Q ℂ) sigma T hT]
  by_cases hq : q = 1
  · rw [ite_eq_left hq]
    have : Function.fixedPoints sigma = Set.univ := by
      ext x
      simp [sigma, hq, Function.IsFixedPt]
    rw [this, Set.ncard_univ]
  · rw [ite_eq_right hq]
    have : Function.fixedPoints sigma = ∅ := by
      ext x
      simp only [Function.mem_fixedPoints, Function.IsFixedPt, sigma, MulAction.toPerm_apply,
        smul_eq_mul, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hq (by simpa using h)
    rw [this, Set.ncard_empty, Nat.cast_zero]

theorem trace_restrict_eq_trace_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (S : Submodule ℂ V) (T P : Module.End ℂ V)
    (hT : ∀ v ∈ S, T v ∈ S) (hP : LinearMap.IsProj S P) :
    LinearMap.trace ℂ S (T.restrict hT) = LinearMap.trace ℂ V (T.comp P) := by
  let retract := P.codRestrict S hP.map_mem
  have hres : ((T.restrict hT).comp retract).comp S.subtype = T.restrict hT := by
    ext v
    exact congrArg T (hP.map_id v.val v.property)
  have hamb : S.subtype.comp ((T.restrict hT).comp retract) = T.comp P := by
    ext v
    rfl
  rw [← hres, LinearMap.trace_comp_comm', hamb]

variable {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]

@[expose] noncomputable def twist (ρ : Representation ℂ G W) (N : Subgroup G) (χ : N →* ℂˣ) :
    Representation ℂ N W where
  toFun n := ((χ n : ℂ))⁻¹ • ρ n
  map_one' := by simp
  map_mul' m n := by
    simp only [map_mul, Subgroup.coe_mul, Units.val_mul, mul_inv]
    rw [smul_mul_smul_comm]

theorem twist_apply (ρ : Representation ℂ G W) (N : Subgroup G) (χ : N →* ℂˣ) (n : N) :
    twist ρ N χ n = ((χ n : ℂ))⁻¹ • ρ n := rfl

theorem mem_isotypic_iff {ρ : Representation ℂ G W} {N : Subgroup G} {χ : N →* ℂˣ} {v : W} :
    v ∈ (⨅ n : N, Module.End.eigenspace (ρ n) (χ n : ℂ)) ↔ ∀ n : N, ρ n v = (χ n : ℂ) • v := by
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem isotypic_eq_invariants (ρ : Representation ℂ G W) (N : Subgroup G) (χ : N →* ℂˣ) :
    (⨅ n : N, Module.End.eigenspace (ρ n) (χ n : ℂ)) = (twist ρ N χ).invariants := by
  ext v
  rw [mem_isotypic_iff, Representation.mem_invariants]
  refine forall_congr' fun n => ?_
  rw [twist_apply, LinearMap.smul_apply]
  have h0 : (χ n : ℂ) ≠ 0 := (χ n).ne_zero
  constructor
  · intro h
    rw [h, smul_smul, inv_mul_cancel₀ h0, one_smul]
  · intro h
    calc ρ n v = (χ n : ℂ) • ((χ n : ℂ)⁻¹ • ρ n v) := by
          rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
      _ = (χ n : ℂ) • v := by rw [h]

theorem mapsTo_isotypic (ρ : Representation ℂ G W) (N : Subgroup G) (χ : N →* ℂˣ) {g : G}
    (hg : ∀ n ∈ N, g * n = n * g) :
    ∀ v ∈ (⨅ n : N, Module.End.eigenspace (ρ n) (χ n : ℂ)),
      ρ g v ∈ (⨅ n : N, Module.End.eigenspace (ρ n) (χ n : ℂ)) := by
  intro v hv
  rw [mem_isotypic_iff] at hv ⊢
  intro n
  rw [← Module.End.mul_apply, ← map_mul, ← hg n n.2, map_mul, Module.End.mul_apply, hv n,
    map_smul]

theorem trace_restrict_isotypic [FiniteDimensional ℂ W] (ρ : Representation ℂ G W)
    (N : Subgroup G) [Fintype N] (χ : N →* ℂˣ) {g : G} (hg : ∀ n ∈ N, g * n = n * g) :
    LinearMap.trace ℂ ↥(⨅ n : N, Module.End.eigenspace (ρ n) (χ n : ℂ))
        ((ρ g).restrict (mapsTo_isotypic ρ N χ hg)) =
      (Nat.card N : ℂ)⁻¹ * ∑ n : N, ρ.character (g * n) * ((χ n : ℂ))⁻¹ := by
  let : Invertible (Fintype.card N : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have hproj : LinearMap.IsProj (⨅ n : N, Module.End.eigenspace (ρ n) (χ n : ℂ))
      (twist ρ N χ).averageMap := by
    rw [isotypic_eq_invariants]
    exact Representation.isProj_averageMap _
  rw [trace_restrict_eq_trace_comp _ (ρ g) _ _ hproj]
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_of, twist_apply]
  rw [LinearMap.comp_smul, ← Module.End.mul_eq_comp, Finset.mul_sum, map_smul, map_sum,
    smul_eq_mul, invOf_eq_inv, Fintype.card_eq_nat_card]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm, Representation.character, map_mul ρ]

theorem multiplicity_dvd_of_coset_constant {H W : Type} [Group H] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W) (Q N : Subgroup H)
    [Fintype Q] [Fintype N] (hcomm : ∀ q ∈ Q, ∀ n ∈ N, q * n = n * q)
    (hconst : ∀ q ∈ Q, q ≠ 1 → ∀ n ∈ N, ρ.character (q * n) = ρ.character q)
    (μ : BlocksIrr N) (hμ : (μ : N → ℂ) ≠ 1) :
    ∃ k : ℕ, BlocksInnerProduct (fun n : N => ρ.character n) μ = ((Nat.card Q * k : ℕ) : ℂ) := by
  obtain ⟨U, _, _, _, σ, -, hσμ⟩ := μ.property
  have hNpos : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hQpos : (Nat.card Q : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum0 : ∑ n : N, σ.character n = 0 := by
    have h := blocksInnerProduct_irreducible_principal μ
    rw [ite_eq_right hμ] at h
    unfold BlocksInnerProduct at h
    simp only [Pi.one_apply, map_one, mul_one] at h
    rw [← hσμ] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hNpos)
  let φ : Q × N →* H := Q.subtype.noncommCoprod N.subtype (fun q n => hcomm q q.2 n n.2)
  let ρ' : Representation ℂ (Q × N) W := ρ.comp φ
  let σ' : Representation ℂ (Q × N) U := σ.comp (MonoidHom.snd Q N)
  let : Invertible (Nat.card (Q × N) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank σ' ρ'
  have hsum : ∑ x : Q × N, ρ'.character x * σ'.character x⁻¹ =
      (Nat.card N : ℂ) * BlocksInnerProduct (fun n : N => ρ.character n) μ := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (1 : Q)]
    · unfold BlocksInnerProduct
      rw [mul_inv_cancel_left₀ hNpos]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← hσμ, CFSG.Theory.Representation.representation_character_inv_eq_star_character]
      change ρ.character ((1 : H) * n) * _ = _
      rw [one_mul]
      rfl
    · intro q _ hq
      have hq' : (q : H) ≠ 1 := fun h' => hq (Subtype.ext h')
      calc ∑ n : N, ρ'.character (q, n) * σ'.character (q, n)⁻¹
          = ∑ n : N, ρ.character q * σ.character n⁻¹ := by
            refine Finset.sum_congr rfl fun n _ => ?_
            change ρ.character (q * n) * σ.character n⁻¹ = _
            rw [hconst q q.2 hq' n n.2]
        _ = ρ.character q * ∑ n : N, σ.character n := by
            rw [← Finset.mul_sum]
            congr 1
            exact Equiv.sum_comp (Equiv.inv N) (fun n => σ.character n)
        _ = 0 := by rw [hsum0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, Nat.card_prod] at h
  refine ⟨Module.finrank ℂ (σ'.IntertwiningMap ρ'), ?_⟩
  push_cast at h ⊢
  rw [← h]
  field_simp

theorem principal_multiplicity_ge {H W : Type} [Group H] [Finite H] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W) (N : Subgroup H)
    [Fintype N] {t : H} (htN : ∀ n ∈ N, t * n = n * t)
    (hconst : ∀ n ∈ N, ρ.character (t * n) = ρ.character t) :
    ∃ m : ℕ, BlocksInnerProduct (fun n : N => ρ.character n) 1 = m ∧
      ‖ρ.character t‖ ≤ m := by
  have hNpos : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1N : ∀ n ∈ N, (1 : H) * n = n * 1 := fun n _ => by rw [one_mul, mul_one]
  have hdim := trace_restrict_isotypic ρ N 1 h1N
  have htr := trace_restrict_isotypic ρ N 1 htN
  refine ⟨Module.finrank ℂ ↥(⨅ n : N, Module.End.eigenspace (ρ n) ((1 : N →* ℂˣ) n : ℂ)),
    ?_, ?_⟩
  · have h1 : (ρ 1).restrict (mapsTo_isotypic ρ N 1 h1N) = 1 := by
      ext v
      simp [LinearMap.restrict_apply]
    rw [h1, LinearMap.trace_one] at hdim
    rw [hdim]
    unfold BlocksInnerProduct
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  · have ht : LinearMap.trace ℂ ↥(⨅ n : N, Module.End.eigenspace (ρ n) ((1 : N →* ℂˣ) n : ℂ))
        ((ρ t).restrict (mapsTo_isotypic ρ N 1 htN)) = ρ.character t := by
      rw [htr]
      simp only [MonoidHom.one_apply, Units.val_one, inv_one, mul_one]
      rw [Finset.sum_congr rfl fun (n : N) _ => hconst n n.2, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_eq_nat_card, inv_mul_cancel_left₀ hNpos]
    rw [← ht]
    refine CFSG.Semidihedral.Principal.EigenCalculus.norm_trace_le_finrank
      (orderOf_pos t).ne' ?_
    rw [Module.End.pow_restrict]
    ext v
    change (ρ t ^ orderOf t) (v : W) = v
    rw [← map_pow, pow_orderOf_eq_one, map_one, Module.End.one_apply]

theorem exists_conj_blocksIrr {A : Type} [Group A] [Finite A] (μ : BlocksIrr A) :
    ∃ μbar : BlocksIrr A, ∀ a, (μbar : A → ℂ) a = star ((μ : A → ℂ) a) := by
  obtain ⟨U, _, _, _, σ, hσ, hσμ⟩ := μ.property
  refine ⟨⟨σ.dual.character, Module.Dual ℂ U, inferInstance, inferInstance, inferInstance,
    σ.dual, CFSG.Section1.representation_dual_irreducible_of σ hσ, rfl⟩, fun a => ?_⟩
  change σ.dual.character a = _
  rw [← CFSG.Section1.conjugateCharacter_representationCharacter_eq_dual, hσμ]
  rfl

theorem conj_blocksIrr_ne {A : Type} [Group A] [Finite A] (hodd : Odd (Nat.card A))
    (μ μbar : BlocksIrr A) (hμ : (μ : A → ℂ) ≠ 1)
    (hbar : ∀ a, (μbar : A → ℂ) a = star ((μ : A → ℂ) a)) : μbar ≠ μ := by
  obtain ⟨U, _, _, _, σ, hσ, hσμ⟩ := μ.property
  intro h
  have hfix : σ.character = CFSG.Section1.conjugateCharacter σ.character := by
    funext a
    have := congrArg (fun χ : BlocksIrr A => (χ : A → ℂ) a) h
    simp only [hbar] at this
    rw [hσμ]
    exact this.symm
  refine CFSG.Section1.proposition_1_1 hodd σ hσ (fun hprin => hμ ?_) hfix
  rw [← hσμ, hprin]
  rfl

theorem blocksInnerProduct_conj_of_real {A : Type} [Group A] [Fintype A] (f : A → ℂ)
    (hf : ∀ a, starRingEnd ℂ (f a) = f a) (μ μbar : A → ℂ) (hbar : ∀ a, μbar a = star (μ a)) :
    BlocksInnerProduct f μbar = starRingEnd ℂ (BlocksInnerProduct f μ) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hf a, hbar a]
  simp only [starRingEnd_apply, star_star]

theorem card_eq_three_of_rational {A : Type*} [Group A] [Finite A] (hodd : Odd (Nat.card A))
    (hne : Nat.card A ≠ 1) (ψ : A →* ℂˣ) (hψ : Function.Injective ψ)
    (hrat : ∀ a, ∃ r : ℚ, (ψ a : ℂ) + (ψ a : ℂ)⁻¹ = r) : IsCyclic A ∧ Nat.card A = 3 := by
  have hinj : Function.Injective ((Units.coeHom ℂ).comp ψ) := fun a b h => hψ (Units.ext h)
  have hcyc : IsCyclic A := isCyclic_of_injective_ringHom _ hinj
  refine ⟨hcyc, ?_⟩
  obtain ⟨x, hx⟩ := hcyc.exists_generator
  have hord : orderOf x = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hx
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hζord : orderOf ((Units.coeHom ℂ).comp ψ x) = Nat.card A := by
    rw [← hord]
    exact orderOf_injective _ hinj x
  have hζ : IsPrimitiveRoot ((ψ x : ℂˣ) : ℂ) (Nat.card A) := hζord ▸ IsPrimitiveRoot.orderOf _
  set ζ : ℂ := (ψ x : ℂ) with hζdef
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'
  have hint : IsIntegral ℤ (ζ + ζ⁻¹) := (hζ.isIntegral hpos).add (hζ.inv.isIntegral hpos)
  obtain ⟨k, hk⟩ := (IsIntegral.exists_int_iff_exists_rat hint).mp (hrat x)
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hpos.ne'
  have hk2 : |(k : ℝ)| ≤ 2 := by
    have h1 : ‖ζ + ζ⁻¹‖ ≤ 2 := by
      calc ‖ζ + ζ⁻¹‖ ≤ ‖ζ‖ + ‖ζ⁻¹‖ := norm_add_le _ _
        _ = 2 := by rw [norm_inv, hnorm]; norm_num
    rw [hk, Complex.norm_intCast] at h1
    exact h1
  rw [abs_le] at hk2
  have hk2a : -2 ≤ k := by exact_mod_cast hk2.1
  have hk2b : k ≤ 2 := by exact_mod_cast hk2.2
  have hquad : ζ ^ 2 - k * ζ + 1 = 0 := by
    have h : ζ * (ζ + ζ⁻¹) = ζ ^ 2 + 1 := by field_simp
    rw [hk] at h
    linear_combination -h
  have h12 : ζ ^ 12 = 1 := by
    interval_cases k
    · have h : (ζ + 1) ^ 2 = 0 := by linear_combination hquad
      have h' : ζ = -1 := by linear_combination pow_eq_zero_iff two_ne_zero |>.mp h
      rw [h']
      norm_num
    · linear_combination (ζ - 1) * (ζ ^ 9 + ζ ^ 6 + ζ ^ 3 + 1) * hquad
    · linear_combination (ζ ^ 10 - ζ ^ 8 + ζ ^ 6 - ζ ^ 4 + ζ ^ 2 - 1) * hquad
    · linear_combination (ζ ^ 3 - 1) * (ζ + 1) * (ζ ^ 6 + 1) * hquad
    · have h : (ζ - 1) ^ 2 = 0 := by linear_combination hquad
      have h' : ζ = 1 := by linear_combination pow_eq_zero_iff two_ne_zero |>.mp h
      rw [h']
      norm_num
  have hdvd : Nat.card A ∣ 12 := hζ.dvd_of_pow_eq_one 12 h12
  have hle : Nat.card A ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨j, hj⟩ := hodd
  set m := Nat.card A with hm
  interval_cases m <;> omega

theorem exists_hom_of_finrank_eq_one {A U : Type*} [Group A] [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : Representation ℂ A U) (h : Module.finrank ℂ U = 1) :
    ∃ ψ : A →* ℂˣ, ∀ a, (ψ a : ℂ) = σ.character a := by
  let f : A →* ℂ :=
    { toFun := σ.character
      map_one' := by rw [Representation.char_one, h, Nat.cast_one]
      map_mul' := fun x y => by
        change LinearMap.trace ℂ U (σ (x * y)) =
          LinearMap.trace ℂ U (σ x) * LinearMap.trace ℂ U (σ y)
        rw [map_mul, CFSG.Semidihedral.Principal.RationalOddCharacter.trace_mul_of_finrank_eq_one
          h] }
  exact ⟨f.toHomUnits, fun a => rfl⟩

theorem star_hom_eq_inv {A : Type*} [Group A] [Finite A] (ν : A →* ℂˣ) (a : A) :
    star (ν a : ℂ) = (ν a : ℂ)⁻¹ := by
  have hpow : (ν a : ℂ) ^ orderOf a = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hnorm := Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos a).ne'
  rw [Complex.inv_eq_conj hnorm]
  rfl

end QuaternionSixteen

open QuaternionSixteen

theorem quaternion_coset_constant_rational_odd_sixteen_bound {H W : Type} [Group H] [Finite H]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ H W)
    (Q : Subgroup H) (e : QuaternionGroup 2 ≃* Q) {t : H}
    (ht : ((e (QuaternionGroup.a 2) : Q) : H) = t)
    (N : Subgroup H) [Fintype N] (hNQ : N ≤ Subgroup.centralizer Q) (hNodd : Odd (Nat.card N))
    (hfaith : ∀ n ∈ N, ρ n = 1 → n = 1) (hrat : ∀ n ∈ N, ∃ q : ℚ, ρ.character n = q)
    (hconst : ∀ q ∈ Q, q ≠ 1 → ∀ n ∈ N, ρ.character (q * n) = ρ.character q)
    (hbound : (Module.finrank ℂ W : ℝ) - ‖ρ.character t‖ ≤ 16) :
    (N = ⊥ ∨ (IsCyclic N ∧ Nat.card N = 3)) ∧
    (N ≠ ⊥ → (Module.finrank ℂ W : ℝ) - ‖ρ.character t‖ = 16 ∧
      ∃ ψ : N →* ℂˣ, Function.Injective ψ ∧ Function.Injective (ψ⁻¹ : N →* ℂˣ) ∧ ψ ≠ ψ⁻¹ ∧
        (∀ n : N, ρ.character n = (‖ρ.character t‖ : ℂ) + 8 * (ψ n : ℂ) + 8 * (ψ⁻¹ n : ℂ)) ∧
        (fun n => (ψ n : ℂ)) ∈ BlocksIrr N ∧ (fun n => (ψ⁻¹ n : ℂ)) ∈ BlocksIrr N ∧
        BlocksInnerProduct (fun n : N => ρ.character n) (fun n => (ψ n : ℂ)) = 8 ∧
        BlocksInnerProduct (fun n : N => ρ.character n) (fun n => (ψ⁻¹ n : ℂ)) = 8 ∧
        (∀ μ ∈ BlocksIrr N, μ ≠ 1 → BlocksInnerProduct (fun n : N => ρ.character n) μ ≠ 0 →
          μ = (fun n => (ψ n : ℂ)) ∨ μ = (fun n => (ψ⁻¹ n : ℂ))) ∧
        ∀ ν ∈ ({ψ, ψ⁻¹} : Set (N →* ℂˣ)),
          ∃ hE : ∀ q : Q, (⨅ n : N, Module.End.eigenspace (ρ n) (ν n : ℂ)) ≤
              (⨅ n : N, Module.End.eigenspace (ρ n) (ν n : ℂ)).comap ((ρ.comp Q.subtype) q),
            (Representation.subrepresentation (ρ.comp Q.subtype) _ hE).character =
              (Representation.ofMulAction ℂ Q Q).character) := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hQcard : Nat.card Q = 8 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have htQ : t ∈ Q := ht ▸ (e (QuaternionGroup.a 2)).2
  have hcomm : ∀ q ∈ Q, ∀ n ∈ N, q * n = n * q := fun q hq n hn =>
    Subgroup.mem_centralizer_iff.mp (hNQ hn) q hq
  have ht1 : t ≠ 1 := by
    rw [← ht]
    intro h
    have h' : e (QuaternionGroup.a 2) = e 1 := by
      rw [map_one]
      exact Subtype.ext h
    exact absurd (e.injective h') (by decide)
  have hNpos : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hθ1 : ρ.character 1 = Module.finrank ℂ W := Representation.char_one ρ
  have hθV : (fun n : N => ρ.character n) ∈ BlocksVChar N := by
    rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
    exact character_mem_virtualCharacters
      ({ vector := W, representation := ρ.comp N.subtype } : FiniteComplexRepresentation N)
  obtain ⟨c, hc, -⟩ := blocksVChar_exists_unique_expansion hθV
  have hcoeff : ∀ μ : BlocksIrr N,
      BlocksInnerProduct (fun n : N => ρ.character n) μ = c μ := fun μ => by
    rw [← hc]
    exact blocksInnerProduct_expansion_coefficient c μ
  have hval : ∀ n : N, ρ.character n = ∑ ν ∈ c.support, (c ν : ℂ) * (ν : N → ℂ) n := by
    intro n
    have h := congrArg (fun f : N → ℂ => f n) hc
    simp only [blocksCharacterExpansion_apply] at h
    exact h.symm
  choose d hdpos hdval using fun μ : BlocksIrr N => blocksIrr_degree_eq_natCast μ
  let p : BlocksIrr N := ⟨1, principal_mem_blocksIrr N⟩
  have hdp : d p = 1 := by
    have h : ((d p : ℕ) : ℂ) = 1 := by
      rw [← hdval p]
      rfl
    exact_mod_cast h
  obtain ⟨m₁, hm₁, htm₁⟩ := principal_multiplicity_ge ρ N (fun n hn => hcomm t htQ n hn)
    (fun n hn => hconst t htQ ht1 n hn)
  have hcp : c p = m₁ := by
    have h : (c p : ℂ) = m₁ := by
      rw [← hcoeff p]
      exact hm₁
    exact_mod_cast h
  have hmult : ∀ μ : BlocksIrr N, (μ : N → ℂ) ≠ 1 → ∃ k : ℕ, c μ = 8 * k := by
    intro μ hμ
    obtain ⟨k, hk⟩ := multiplicity_dvd_of_coset_constant ρ Q N hcomm hconst μ hμ
    refine ⟨k, ?_⟩
    rw [hcoeff, hQcard] at hk
    exact_mod_cast hk
  have hnonneg : ∀ μ : BlocksIrr N, 0 ≤ c μ := by
    intro μ
    by_cases hμ : (μ : N → ℂ) = 1
    · have : μ = p := Subtype.ext hμ
      rw [this, hcp]
      positivity
    · obtain ⟨k, hk⟩ := hmult μ hμ
      rw [hk]
      positivity
  have hdeg : (Module.finrank ℂ W : ℤ) = ∑ ν ∈ c.support, c ν * (d ν : ℤ) := by
    have h' : ((Module.finrank ℂ W : ℤ) : ℂ) =
        ((∑ ν ∈ c.support, c ν * (d ν : ℤ) : ℤ) : ℂ) := by
      rw [Int.cast_natCast, ← hθ1]
      have h1 := hval 1
      rw [OneMemClass.coe_one] at h1
      rw [h1]
      push_cast
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hdval ν]
    exact_mod_cast h'
  have hle : ∀ U : Finset (BlocksIrr N),
      ∑ ν ∈ U, c ν * (d ν : ℤ) ≤ Module.finrank ℂ W := by
    intro U
    rw [hdeg]
    calc ∑ ν ∈ U, c ν * (d ν : ℤ) ≤ ∑ ν ∈ U ∪ c.support, c ν * (d ν : ℤ) :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            fun ν _ _ => mul_nonneg (hnonneg ν) (by positivity)
      _ = ∑ ν ∈ c.support, c ν * (d ν : ℤ) :=
          (Finset.sum_subset Finset.subset_union_right fun ν _ hν => by
            rw [Finsupp.notMem_support_iff.mp hν, zero_mul]).symm
  have hreal : ∀ n : N, starRingEnd ℂ (ρ.character n) = ρ.character n := by
    intro n
    obtain ⟨q, hq⟩ := hrat n n.2
    rw [hq]
    exact map_ratCast _ q
  rcases eq_or_ne N ⊥ with hNbot | hNbot
  · exact ⟨Or.inl hNbot, fun h => absurd hNbot h⟩
  obtain ⟨μ, hμS, hμ1⟩ : ∃ μ ∈ c.support, (μ : N → ℂ) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hNbot
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    have hn1 : ρ.character n = ρ.character 1 := by
      have h1 := hval 1
      have hn' : ρ.character n = ∑ ν ∈ c.support, (c ν : ℂ) * (ν : N → ℂ) ⟨n, hn⟩ :=
        hval ⟨n, hn⟩
      rw [OneMemClass.coe_one] at h1
      rw [hn', h1]
      refine Finset.sum_congr rfl fun ν hν => ?_
      rw [hcon ν hν]
      rfl
    refine hfaith n hn (CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank (ρ n)
      (orderOf_pos n).ne' ?_ ?_)
    · rw [← map_pow, pow_orderOf_eq_one, map_one]
    · change ρ.character n = _
      rw [hn1, hθ1]
  obtain ⟨μbar, hbar⟩ := exists_conj_blocksIrr μ
  have hbarne : μbar ≠ μ := conj_blocksIrr_ne hNodd μ μbar hμ1 hbar
  have hbar1 : (μbar : N → ℂ) ≠ 1 := by
    intro h
    apply hμ1
    funext n
    have h' := hbar n
    rw [h, Pi.one_apply] at h'
    have h'' := congrArg star h'
    rw [star_star, star_one] at h''
    exact h''.symm
  have hcbar : c μbar = c μ := by
    have h := blocksInnerProduct_conj_of_real (fun n : N => ρ.character n) hreal μ μbar hbar
    rw [hcoeff, hcoeff, map_intCast] at h
    exact_mod_cast h
  have hdbar : d μbar = d μ := by
    have h : ((d μbar : ℕ) : ℂ) = d μ := by
      rw [← hdval, hbar, hdval]
      simp
    exact_mod_cast h
  obtain ⟨k, hk⟩ := hmult μ hμ1
  have hk1 : 1 ≤ k := by
    have : c μ ≠ 0 := Finsupp.mem_support_iff.mp hμS
    rw [hk] at this
    omega
  have hpμ : p ≠ μ := fun h => hμ1 (by rw [← h])
  have hpμbar : p ≠ μbar := fun h => hbar1 (by rw [← h])
  have hsum3 := hle {p, μ, μbar}
  rw [Finset.sum_insert (by simp [hpμ, hpμbar]), Finset.sum_pair hbarne.symm, hcbar, hdbar,
    hdp, hk, hcp] at hsum3
  push_cast at hsum3
  have hR : (m₁ : ℝ) + 16 * ((k * d μ : ℕ) : ℝ) ≤ Module.finrank ℂ W := by
    have h : (m₁ : ℤ) + 16 * ((k * d μ : ℕ) : ℤ) ≤ Module.finrank ℂ W := by
      push_cast
      linarith
    exact_mod_cast h
  have hkd : k * d μ = 1 := by
    have h : ((k * d μ : ℕ) : ℝ) ≤ 1 := by linarith
    have h' : k * d μ ≤ 1 := by exact_mod_cast h
    have h'' : 1 ≤ k * d μ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (hdpos μ).ne')
    omega
  obtain ⟨hk', hdμ⟩ := mul_eq_one.mp hkd
  rw [hkd] at hR
  push_cast at hR
  have h16 : (Module.finrank ℂ W : ℝ) - ‖ρ.character t‖ = 16 := by linarith
  have hm₁eq : (m₁ : ℝ) = ‖ρ.character t‖ := by linarith
  have hother : ∀ ν : BlocksIrr N, ν ≠ p → ν ≠ μ → ν ≠ μbar → c ν = 0 := by
    intro ν hνp hνμ hνbar
    by_contra hν0
    have hcν : 1 ≤ c ν := by
      have := hnonneg ν
      omega
    have hdν : (1 : ℤ) ≤ d ν := by exact_mod_cast hdpos ν
    have hsum4 := hle {ν, p, μ, μbar}
    rw [Finset.sum_insert (by simp [hνp, hνμ, hνbar]), Finset.sum_insert (by simp [hpμ, hpμbar]),
      Finset.sum_pair hbarne.symm, hcbar, hdbar, hdp, hk, hcp, hk', hdμ] at hsum4
    push_cast at hsum4
    have hcd : 1 ≤ c ν * d ν := one_le_mul_of_one_le_of_one_le hcν hdν
    have h17 : (m₁ : ℤ) + 17 ≤ Module.finrank ℂ W := by linarith
    have hR' : (m₁ : ℝ) + 17 ≤ Module.finrank ℂ W := by exact_mod_cast h17
    linarith
  have hS : c.support ⊆ {p, μ, μbar} := by
    intro ν hν
    by_contra hνT
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hνT
    exact Finsupp.mem_support_iff.mp hν (hother ν hνT.1 hνT.2.1 hνT.2.2)
  have hform : ∀ n : N,
      ρ.character n = (m₁ : ℂ) + 8 * (μ : N → ℂ) n + 8 * (μbar : N → ℂ) n := by
    intro n
    rw [hval n, Finset.sum_subset hS (fun ν _ hν => by
      rw [Finsupp.notMem_support_iff.mp hν, Int.cast_zero, zero_mul]),
      Finset.sum_insert (by simp [hpμ, hpμbar]), Finset.sum_pair hbarne.symm, hcbar, hk, hcp, hk']
    have hpn : (p : N → ℂ) n = 1 := rfl
    rw [hpn]
    push_cast
    ring
  obtain ⟨U, _, _, _, σ, -, hσμ⟩ := μ.property
  have hU : Module.finrank ℂ U = 1 := by
    have h : (Module.finrank ℂ U : ℂ) = 1 := by
      rw [← Representation.char_one σ, hσμ, hdval μ, hdμ, Nat.cast_one]
    exact_mod_cast h
  obtain ⟨ψ, hψ⟩ := exists_hom_of_finrank_eq_one σ hU
  have hμψ : (μ : N → ℂ) = fun n => (ψ n : ℂ) := by
    funext n
    rw [hψ n, hσμ]
  have hμbarψ : (μbar : N → ℂ) = fun n => (ψ⁻¹ n : ℂ) := by
    funext n
    rw [hbar n, ← hσμ,
      ← CFSG.Theory.Representation.representation_character_inv_eq_star_character, ← hψ,
      map_inv, MonoidHom.inv_apply]
  have hψinv : ∀ n : N, (ψ⁻¹ n : ℂ) = (ψ n : ℂ)⁻¹ := fun n => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hform' : ∀ n : N, ρ.character n = (m₁ : ℂ) + 8 * (ψ n : ℂ) + 8 * (ψ⁻¹ n : ℂ) := by
    intro n
    rw [hform n, hμψ, hμbarψ]
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hθn : ρ.character n = ρ.character 1 := by
      have h1 := hform' 1
      rw [OneMemClass.coe_one] at h1
      rw [hform' n, h1, hψinv, hψinv, hn, map_one ψ]
    have hρn : ρ n = 1 := CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank (ρ n)
      (orderOf_pos (n : H)).ne' (by rw [← map_pow, pow_orderOf_eq_one, map_one])
      (by
        change ρ.character n = _
        rw [hθn, hθ1])
    exact Subtype.ext (hfaith n n.2 hρn)
  have hψinvinj : Function.Injective (ψ⁻¹ : N →* ℂˣ) := by
    intro a b h
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply] at h
    exact hψinj (inv_injective h)
  have hψne : ψ ≠ ψ⁻¹ := by
    intro h
    apply hbarne
    apply Subtype.ext
    rw [hμbarψ, hμψ, ← h]
  have hψ1 : ψ ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    apply hn
    apply hψinj
    rw [h, MonoidHom.one_apply, map_one]
  have hψinv1 : ψ⁻¹ ≠ 1 := by
    intro h
    apply hψ1
    refine MonoidHom.ext fun n => ?_
    have h' := DFunLike.congr_fun h n
    rw [MonoidHom.inv_apply, MonoidHom.one_apply, inv_eq_one] at h'
    rw [h', MonoidHom.one_apply]
  have hcard3 := card_eq_three_of_rational hNodd (fun h => hNbot (Subgroup.card_eq_one.mp h)) ψ
    hψinj (fun n => by
      obtain ⟨q, hq⟩ := hrat n n.2
      refine ⟨(q - m₁) / 8, ?_⟩
      push_cast
      rw [← hq, hform' n, hψinv n]
      ring)
  have hmulψ : BlocksInnerProduct (fun n : N => ρ.character n) (fun n => (ψ n : ℂ)) = 8 := by
    rw [← hμψ, hcoeff, hk, hk']
    norm_num
  have hmulψinv :
      BlocksInnerProduct (fun n : N => ρ.character n) (fun n => (ψ⁻¹ n : ℂ)) = 8 := by
    rw [← hμbarψ, hcoeff, hcbar, hk, hk']
    norm_num
  have hconstit : ∀ ν ∈ BlocksIrr N, ν ≠ 1 →
      BlocksInnerProduct (fun n : N => ρ.character n) ν ≠ 0 →
      ν = (fun n => (ψ n : ℂ)) ∨ ν = (fun n => (ψ⁻¹ n : ℂ)) := by
    intro ν hν hν1 hν0
    rw [← hμψ, ← hμbarψ]
    by_contra hcon
    push Not at hcon
    exact hν0 ((hcoeff ⟨ν, hν⟩).trans (by
      rw [hother ⟨ν, hν⟩ (fun h => hν1 (congrArg Subtype.val h))
        (fun h => hcon.1 (congrArg Subtype.val h)) (fun h => hcon.2 (congrArg Subtype.val h)),
        Int.cast_zero]))
  have hreg : ∀ ν : N →* ℂˣ, ν ≠ 1 →
      BlocksInnerProduct (fun n : N => ρ.character n) (fun n => (ν n : ℂ)) = 8 →
      ∃ hE : ∀ q : Q, (⨅ n : N, Module.End.eigenspace (ρ n) (ν n : ℂ)) ≤
          (⨅ n : N, Module.End.eigenspace (ρ n) (ν n : ℂ)).comap ((ρ.comp Q.subtype) q),
        (Representation.subrepresentation (ρ.comp Q.subtype) _ hE).character =
          (Representation.ofMulAction ℂ Q Q).character := by
    intro ν hν1 hν8
    refine ⟨fun q v hv => mapsTo_isotypic ρ N ν (fun n hn => hcomm q q.2 n hn) v hv, ?_⟩
    funext q
    change LinearMap.trace ℂ _
      ((ρ q).restrict (mapsTo_isotypic ρ N ν (fun n hn => hcomm q q.2 n hn))) = _
    rw [trace_restrict_isotypic ρ N ν (fun n hn => hcomm q q.2 n hn), regular_character_apply,
      hQcard]
    by_cases hq : q = 1
    · rw [ite_eq_left hq, Nat.cast_ofNat, ← hν8]
      subst hq
      unfold BlocksInnerProduct
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [OneMemClass.coe_one, one_mul, starRingEnd_apply, star_hom_eq_inv]
    · rw [ite_eq_right hq]
      have hq' : (q : H) ≠ 1 := fun h => hq (Subtype.ext h)
      have hterm : ∀ n : N, ρ.character (q * n) * ((ν n : ℂ))⁻¹ =
          ρ.character q * ((ν n : ℂ))⁻¹ := fun n => by rw [hconst q q.2 hq' n n.2]
      have hne : (Units.coeHom ℂ).comp ν⁻¹ ≠ 1 := by
        intro h
        apply hν1
        ext n
        have h' := DFunLike.congr_fun h n
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply,
          MonoidHom.one_apply] at h'
        rw [Units.val_inv_eq_inv_val, inv_eq_one] at h'
        simpa using h'
      have hsum := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp ν⁻¹) hne
      simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val] at hsum
      rw [Finset.sum_congr rfl fun n _ => hterm n, ← Finset.mul_sum, hsum, mul_zero, mul_zero]
  refine ⟨Or.inr hcard3, fun _ => ⟨h16, ψ, hψinj, hψinvinj, hψne, fun n => ?_, ?_, ?_, hmulψ,
    hmulψinv, hconstit, fun ν hν => ?_⟩⟩
  · rw [hform' n]
    have h : (m₁ : ℂ) = (‖ρ.character t‖ : ℂ) := by
      rw [← hm₁eq]
      norm_cast
    rw [h]
  · rw [← hμψ]
    exact μ.property
  · rw [← hμbarψ]
    exact μbar.property
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hν
    rcases hν with rfl | rfl
    · exact hreg _ hψ1 hmulψ
    · exact hreg _ hψinv1 hmulψinv

end CFSG.Semidihedral.Principal
