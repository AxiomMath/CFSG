module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis

public section

open scoped BigOperators Classical

namespace CFSG.SmallDefect

open CFSG.Section1

@[expose] noncomputable def fsIndicator {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, χ (g * g)

section Representation

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

private noncomputable def repIndicator : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character (g⁻¹ * g⁻¹)

private noncomputable abbrev flipMap : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
  (LinearMap.BilinForm.flipHom : LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap

private theorem repIndicator_eq_trace :
    repIndicator ρ =
      LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
        (flipMap.comp (Representation.averageMap (Representation.linHom ρ ρ.dual))) := by
  let rhoh : Representation ℂ G (LinearMap.BilinForm ℂ V) := Representation.linHom ρ ρ.dual
  have hcomp_smul :
      (flipMap (V := V)).comp (((Nat.card G : ℂ)⁻¹ : ℂ) • ∑ g : G, rhoh g) =
        (((Nat.card G : ℂ)⁻¹ : ℂ) • ∑ g : G, (flipMap (V := V)).comp (rhoh g)) := by
    ext x
    simp [LinearMap.comp_apply]
  symm
  rw [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
  simp [Representation.asAlgebraHom_def]
  rw [← Nat.card_eq_fintype_card]
  rw [hcomp_smul, map_smul, map_sum]
  unfold repIndicator
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _
  exact representation_trace_flip_linHom_dual_eq_character_inv_mul_inv ρ g

private noncomputable def invariantFlip :
    Representation.invariants (Representation.linHom ρ ρ.dual) →ₗ[ℂ]
      Representation.invariants (Representation.linHom ρ ρ.dual) :=
  (flipMap (V := V)).restrict (by
    intro x hx
    rw [Representation.mem_invariants] at hx ⊢
    intro g
    calc Representation.linHom ρ ρ.dual g (flipMap x) =
          flipMap (Representation.linHom ρ ρ.dual g x) := by
          have hcomm := congrArg
            (fun f : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V => f x)
            (representation_flip_linHom_dual_comm ρ g)
          simpa using hcomm.symm
      _ = flipMap x := by rw [hx g])

private theorem trace_flip_average_eq :
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
        ((flipMap (V := V)).comp
          (Representation.averageMap (Representation.linHom ρ ρ.dual))) =
      LinearMap.trace ℂ (Representation.invariants (Representation.linHom ρ ρ.dual))
        (invariantFlip ρ) := by
  let rhoh : Representation ℂ G (LinearMap.BilinForm ℂ V) := Representation.linHom ρ ρ.dual
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) := Representation.invariants rhoh
  let avg : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    Representation.averageMap rhoh
  let : Module.Free ℂ p := Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ p)
  let : Module.Finite ℂ p := Module.Finite.of_basis (Module.Basis.ofVectorSpace ℂ p)
  have havgProj : LinearMap.IsProj p avg := by
    simpa [p, avg, rhoh] using (Representation.isProj_averageMap rhoh)
  let flipP : p →ₗ[ℂ] p := invariantFlip ρ
  let avgToP : LinearMap.BilinForm ℂ V →ₗ[ℂ] p := havgProj.codRestrict
  let inclFlip : p →ₗ[ℂ] LinearMap.BilinForm ℂ V := p.subtype.comp flipP
  have hfactor : (flipMap (V := V)).comp avg = inclFlip.comp avgToP := by
    ext x
    rfl
  have hcod : avgToP.comp p.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact havgProj.codRestrict_apply_cod x
  change LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) ((flipMap (V := V)).comp avg) =
    LinearMap.trace ℂ p flipP
  rw [hfactor]
  calc LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (inclFlip.comp avgToP) =
        LinearMap.trace ℂ p (avgToP.comp inclFlip) := by
        simpa [LinearMap.comp_assoc] using
          (LinearMap.trace_comp_comm' (R := ℂ) (M := LinearMap.BilinForm ℂ V)
            (N := p) avgToP inclFlip)
    _ = LinearMap.trace ℂ p ((avgToP.comp p.subtype).comp flipP) := by
        rw [LinearMap.comp_assoc]
    _ = LinearMap.trace ℂ p (LinearMap.id.comp flipP) := by rw [hcod]
    _ = LinearMap.trace ℂ p flipP := by simp

private theorem repIndicator_eq_zero (hirr : Representation.IsIrreducible ρ)
    (hnot : ρ.character ≠ conjugateCharacter ρ.character) : repIndicator ρ = 0 := by
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) :=
    Representation.invariants (Representation.linHom ρ ρ.dual)
  have hdualirr : Representation.IsIrreducible ρ.dual := representation_dual_irreducible_of ρ hirr
  have hhomzero : ∀ f : Representation.IntertwiningMap ρ ρ.dual, f = 0 := by
    intro f
    let : Representation.IsIrreducible ρ := hirr
    let : Representation.IsIrreducible ρ.dual := hdualirr
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hbij | hzero
    · let e : ρ.Equiv ρ.dual := f.ofBijective hbij
      exfalso
      apply hnot
      calc ρ.character = ρ.dual.character := Representation.char_iso e
        _ = conjugateCharacter ρ.character :=
          (conjugateCharacter_representationCharacter_eq_dual ρ).symm
    · exact hzero
  have hsub : Subsingleton (Representation.IntertwiningMap ρ ρ.dual) :=
    ⟨fun f g => (hhomzero f).trans (hhomzero g).symm⟩
  have hpfin : Module.finrank ℂ p = 0 := by
    calc Module.finrank ℂ p = Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) := by
          simpa using
            (Representation.invariantsEquivIntertwiningMap (ρ := ρ) (σ := ρ.dual)).finrank_eq
      _ = 0 := Module.finrank_zero_of_subsingleton
  have hpzero (x : p) : x = 0 := (finrank_zero_iff_forall_zero.mp hpfin) x
  have : Subsingleton p := ⟨fun x y => (hpzero x).trans (hpzero y).symm⟩
  rw [repIndicator_eq_trace, trace_flip_average_eq]
  have hflipzero : invariantFlip ρ = 0 := Subsingleton.elim _ _
  rw [hflipzero]
  simp

private theorem repIndicator_of_fixed (hirr : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    repIndicator ρ ^ 2 = 1 ∧
      ∃ x ∈ Representation.invariants (Representation.linHom ρ ρ.dual), x ≠ 0 ∧
        LinearMap.BilinForm.flip x = repIndicator ρ • x := by
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) :=
    Representation.invariants (Representation.linHom ρ ρ.dual)
  let flipP : p →ₗ[ℂ] p := invariantFlip ρ
  let : Module.Free ℂ p := Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ p)
  let : Module.Finite ℂ p := Module.Finite.of_basis (Module.Basis.ofVectorSpace ℂ p)
  have hpfin : Module.finrank ℂ p = 1 := by
    simpa [p] using
      representation_linHom_dual_invariants_finrank_eq_one_of_fixed_conjugate ρ hirr hfixed
  have hp_nonzero : ∃ x : p, x ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hsub : Subsingleton p := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    have hfinzero : Module.finrank ℂ p = 0 :=
      @Module.finrank_zero_of_subsingleton ℂ p _ _ _ _ hsub
    omega
  rcases hp_nonzero with ⟨x, hx⟩
  have hspan := (finrank_eq_one_iff_of_nonzero' (K := ℂ) (V := p) x hx).mp hpfin
  rcases hspan (flipP x) with ⟨c, hc⟩
  let b : Module.Basis Unit ℂ p := FiniteDimensional.basisSingleton Unit hpfin x hx
  have htrace_eq_c : LinearMap.trace ℂ p flipP = c := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    have hxrepr_ne : (Module.basisUnique Unit hpfin).repr x PUnit.unit ≠ 0 := by
      exact mt (Module.basisUnique_repr_eq_zero_iff (ι := Unit) (h := hpfin)
        (v := x) (i := PUnit.unit)).mp hx
    have hrepr : (Module.basisUnique Unit hpfin).repr (flipP x) PUnit.unit =
        c * (Module.basisUnique Unit hpfin).repr x PUnit.unit := by
      simpa using (congrArg
        (fun y : p => (Module.basisUnique Unit hpfin).repr y PUnit.unit) hc).symm
    simp [LinearMap.toMatrix_apply, b, FiniteDimensional.basisSingleton_apply, hrepr,
      hxrepr_ne]
  have hinv : ∀ y : p, flipP (flipP y) = y := by
    intro y
    apply Subtype.ext
    ext u v
    rfl
  have hcsq : c ^ 2 = 1 := by
    apply smul_left_injective (M := p) ℂ hx
    calc (c ^ 2) • x = c • (c • x) := by rw [pow_two, mul_smul]
      _ = c • flipP x := congrArg (fun y : p => c • y) hc
      _ = flipP (c • x) := by simp
      _ = flipP (flipP x) := congrArg flipP hc
      _ = x := hinv x
      _ = (1 : ℂ) • x := by simp
  have hind : repIndicator ρ = c := by
    rw [repIndicator_eq_trace, trace_flip_average_eq, show invariantFlip ρ = flipP from rfl,
      htrace_eq_c]
  refine ⟨by rw [hind, hcsq], x, x.2, fun h => hx (Subtype.ext h), ?_⟩
  rw [hind]
  have := congrArg Subtype.val hc
  exact this.symm

omit [Fintype G] in
private theorem nondegenerate_of_invariant (hirr : Representation.IsIrreducible ρ)
    {x : LinearMap.BilinForm ℂ V}
    (hx : x ∈ Representation.invariants (Representation.linHom ρ ρ.dual))
    (hx0 : x ≠ 0) : x.Nondegenerate := by
  let f : Representation.IntertwiningMap ρ ρ.dual :=
    (Representation.invariantsEquivIntertwiningMap (ρ := ρ) (σ := ρ.dual)) ⟨x, hx⟩
  have hf : (f : V →ₗ[ℂ] Module.Dual ℂ V) = x := rfl
  let : Representation.IsIrreducible ρ := hirr
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hinj | hzero
  · apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro m hm
    apply hinj
    change (f : V →ₗ[ℂ] Module.Dual ℂ V) m = (f : V →ₗ[ℂ] Module.Dual ℂ V) 0
    rw [hf, map_zero]
    ext n
    exact hm n
  · exfalso
    apply hx0
    rw [← hf, hzero]
    rfl

private theorem even_finrank_of_skew {x : LinearMap.BilinForm ℂ V} (hnd : x.Nondegenerate)
    (hskew : LinearMap.BilinForm.flip x = (-1 : ℂ) • x) : Even (Module.finrank ℂ V) := by
  let b := Module.finBasis ℂ V
  set M := LinearMap.BilinForm.toMatrix b x with hM
  have hdet : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  have hT : M.transpose = -M := by
    have h := congrArg (LinearMap.BilinForm.toMatrix b) hskew
    rw [map_smul, neg_one_smul] at h
    rw [hM, ← h]
    ext i j
    simp [LinearMap.BilinForm.flip_apply]
  have hpow : (-1 : ℂ) ^ (Module.finrank ℂ V) = 1 := by
    have h := congrArg Matrix.det hT
    rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h
    have h' : M.det * ((-1) ^ Module.finrank ℂ V - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hdet
    · exact sub_eq_zero.mp h0
  rcases Nat.even_or_odd (Module.finrank ℂ V) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hpow
    norm_num at hpow

end Representation

variable {G : Type} [Group G] [Fintype G]

private theorem fsIndicator_eq_repIndicator {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    fsIndicator ρ.character = repIndicator ρ := by
  unfold fsIndicator repIndicator
  congr 1
  exact (Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp).symm

theorem fsIndicator_spec {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    (fsIndicator χ = 0 ∨ fsIndicator χ = 1 ∨ fsIndicator χ = -1) ∧
      (fsIndicator χ = 0 ↔ starRingEnd ℂ ∘ χ ≠ χ) ∧
      (fsIndicator χ = -1 → ∃ n : ℕ, χ 1 = 2 * n) := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  rw [fsIndicator_eq_repIndicator]
  have hconj : (starRingEnd ℂ ∘ ρ.character = ρ.character) ↔
      ρ.character = conjugateCharacter ρ.character := by
    constructor
    · intro h
      funext g
      exact (congrFun h g).symm
    · intro h
      funext g
      exact (congrFun h g).symm
  by_cases hfixed : ρ.character = conjugateCharacter ρ.character
  · obtain ⟨hsq, x, hx, hx0, hflip⟩ := repIndicator_of_fixed ρ hirr hfixed
    have hne : repIndicator ρ ≠ 0 := by
      intro h
      rw [h] at hsq
      norm_num at hsq
    refine ⟨?_, ⟨fun h => absurd h hne, fun h => absurd (hconj.mpr hfixed) h⟩, ?_⟩
    · rcases sq_eq_one_iff.mp hsq with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · intro hneg
      rw [hneg] at hflip
      have hev := even_finrank_of_skew (nondegenerate_of_invariant ρ hirr hx hx0) hflip
      obtain ⟨k, hk⟩ := hev
      refine ⟨k, ?_⟩
      rw [Representation.char_one, hk]
      push_cast
      ring
  · have hzero := repIndicator_eq_zero ρ hirr hfixed
    refine ⟨Or.inl hzero, ⟨fun _ h => hfixed (hconj.mp h), fun _ => hzero⟩, ?_⟩
    intro hneg
    rw [hzero] at hneg
    norm_num at hneg

theorem card_sq_eq_sum_fsIndicator (y : G) :
    (((Finset.univ.filter fun x : G => x * x = y).card : ℕ) : ℂ) =
      ∑ χ ∈ (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite G).toFinset,
        fsIndicator χ * χ y := by
  set F : G → ℂ := fun y => (((Finset.univ.filter fun x : G => x * x = y).card : ℕ) : ℂ)
    with hF
  have hFclass : BlocksIsClassFunction F := by
    intro z g
    simp only [hF]
    congr 1
    refine Finset.card_nbij' (fun x => g⁻¹ * x * g) (fun x => g * x * g⁻¹) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, hx]
      group
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx]
    · intro x _
      group
    · intro x _
      group
  have hexp := congrFun ((irreducible_character_basis G).2.2.2 F hFclass) y
  rw [Finset.sum_apply] at hexp
  simp only [Pi.smul_apply, smul_eq_mul] at hexp
  change F y = _
  rw [hexp]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Set.Finite.mem_toFinset] at hχ
  congr 1
  have hreal : starRingEnd ℂ (fsIndicator χ) = fsIndicator χ := by
    rcases (fsIndicator_spec hχ).1 with h | h | h <;> rw [h] <;> simp
  rw [← hreal]
  unfold BlocksInnerProduct fsIndicator
  rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum]
  congr 1
  simp only [hF]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := fun x : G => x * x) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2],
    Finset.sum_const, nsmul_eq_mul]

end CFSG.SmallDefect
