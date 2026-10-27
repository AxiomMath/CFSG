module

public import CFSG.CharacterTheory.Wreathed.AbelianQuotientTwists
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralSectionQuotientBasis
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

section Decomposition

variable {K : Type} [Group K] [Fintype K]

theorem exists_blocksIrr_sum {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ K W) :
    ∃ (m : ℕ) (μ : Fin m → BlocksIrr K), σ.character = ∑ j, (μ j : K → ℂ) := by
  obtain ⟨m, summand, hirr, hsum⟩ := finiteComplexRepresentation_exists_irreducible_character_sum
    ({ vector := W, representation := σ } : FiniteComplexRepresentation.{0, 0} K)
  have hmem : ∀ j, (summand j).character ∈ BlocksIrr K := by
    intro j
    rw [blocksIrr_eq_irreducible_characters]
    exact ⟨summand j, hirr j, rfl⟩
  refine ⟨m, fun j => ⟨(summand j).character, hmem j⟩, ?_⟩
  funext g
  rw [Finset.sum_apply]
  exact hsum g

theorem blocksInnerProduct_sum_blocksIrr_left {m : ℕ} (μ : Fin m → BlocksIrr K) {ξ : K → ℂ}
    (hξ : ξ ∈ BlocksIrr K) :
    BlocksInnerProduct (∑ j, (μ j : K → ℂ)) ξ =
      ((Finset.univ.filter fun j => (μ j : K → ℂ) = ξ).card : ℂ) := by
  have hsum : BlocksInnerProduct (∑ j, (μ j : K → ℂ)) ξ =
      ∑ j, BlocksInnerProduct (μ j : K → ℂ) ξ := by
    unfold BlocksInnerProduct
    simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp_rw [blocksInnerProduct_of_mem_blocksIrr (μ _).2 hξ]
  rw [Finset.sum_boole]

theorem blocksInnerProduct_sum_blocksIrr_right {m : ℕ} (μ : Fin m → BlocksIrr K) {ξ : K → ℂ}
    (hξ : ξ ∈ BlocksIrr K) :
    BlocksInnerProduct ξ (∑ j, (μ j : K → ℂ)) =
      ((Finset.univ.filter fun j => ξ = (μ j : K → ℂ)).card : ℂ) := by
  have hsum : BlocksInnerProduct ξ (∑ j, (μ j : K → ℂ)) =
      ∑ j, BlocksInnerProduct ξ (μ j : K → ℂ) := by
    unfold BlocksInnerProduct
    simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp_rw [blocksInnerProduct_of_mem_blocksIrr hξ (μ _).2]
  rw [Finset.sum_boole]

theorem blocksInnerProduct_finset_sum_left {ι : Type*} (s : Finset ι) (f : ι → K → ℂ)
    (g : K → ℂ) :
    BlocksInnerProduct (∑ i ∈ s, f i) g = ∑ i ∈ s, BlocksInnerProduct (f i) g := by
  unfold BlocksInnerProduct
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem blocksInnerProduct_sum_blocksIrr_self {m : ℕ} (μ : Fin m → BlocksIrr K) :
    BlocksInnerProduct (∑ j, (μ j : K → ℂ)) (∑ j, (μ j : K → ℂ)) =
      ((∑ l, (Finset.univ.filter fun k => (μ k : K → ℂ) = μ l).card : ℕ) : ℂ) := by
  have hsum : BlocksInnerProduct (∑ j, (μ j : K → ℂ)) (∑ j, (μ j : K → ℂ)) =
      ∑ l, BlocksInnerProduct (∑ j, (μ j : K → ℂ)) (μ l : K → ℂ) := by
    unfold BlocksInnerProduct
    simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp_rw [blocksInnerProduct_sum_blocksIrr_left μ (μ _).2]
  push_cast
  rfl

theorem card_le_sum_card_filter {m : ℕ} (μ : Fin m → BlocksIrr K) :
    m ≤ ∑ l, (Finset.univ.filter fun k => (μ k : K → ℂ) = μ l).card := by
  calc m = ∑ _l : Fin m, 1 := by simp
    _ ≤ ∑ l, (Finset.univ.filter fun k => (μ k : K → ℂ) = μ l).card := by
      apply Finset.sum_le_sum
      intro l _
      exact Finset.card_pos.mpr ⟨l, by simp⟩

theorem exists_natCast_blocksInnerProduct_restrict {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ K W) (P : Subgroup K) {ξ : P → ℂ}
    (hξ : ξ ∈ BlocksIrr P) :
    ∃ c : ℕ, BlocksInnerProduct (fun p : P => σ.character p) ξ = c := by
  obtain ⟨m, μ, hμ⟩ := exists_blocksIrr_sum (σ.comp P.subtype)
  have hres : (fun p : P => σ.character p) =
      Representation.character (σ.comp P.subtype) := rfl
  rw [hres, hμ, blocksInnerProduct_sum_blocksIrr_left μ hξ]
  exact ⟨_, rfl⟩

end Decomposition

section IrreducibleCriteria

theorem isIrreducible_of_equiv {K W W' : Type*} [Group K] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {τ : Representation ℂ K W'} {σ : Representation ℂ K W}
    (e : Representation.Equiv τ σ) (hτ : τ.IsIrreducible) : σ.IsIrreducible := by
  have hcomm : ∀ (g : K) (v : W'), e (τ g v) = σ g (e v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining τ σ e.toIntertwiningMap g v
  have hcomm' : ∀ (g : K) (w : W), e.toLinearEquiv.symm (σ g w) =
      τ g (e.toLinearEquiv.symm w) := by
    intro g w
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h := hcomm g (e.toLinearEquiv.symm w)
    change e.toLinearEquiv (τ g (e.toLinearEquiv.symm w)) = σ g
      (e.toLinearEquiv (e.toLinearEquiv.symm w)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let iso : Subrepresentation σ ≃o Subrepresentation τ :=
    { toFun := fun S => ⟨S.toSubmodule.comap e.toLinearEquiv.toLinearMap, fun g v hv => by
        simp only [Submodule.mem_comap] at hv ⊢
        change e.toLinearEquiv (τ g v) ∈ S.toSubmodule
        have h := hcomm g v
        change e.toLinearEquiv (τ g v) = σ g (e.toLinearEquiv v) at h
        rw [h]
        exact S.apply_mem_toSubmodule g hv⟩
      invFun := fun T => ⟨T.toSubmodule.comap e.toLinearEquiv.symm.toLinearMap, fun g w hw => by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
        rw [hcomm']
        exact T.apply_mem_toSubmodule g hw⟩
      left_inv := fun S => by
        apply Subrepresentation.ext
        ext w
        change e.toLinearEquiv (e.toLinearEquiv.symm w) ∈ S.toSubmodule ↔ w ∈ S.toSubmodule
        rw [LinearEquiv.apply_symm_apply]
      right_inv := fun T => by
        apply Subrepresentation.ext
        ext v
        change e.toLinearEquiv.symm (e.toLinearEquiv v) ∈ T.toSubmodule ↔ v ∈ T.toSubmodule
        rw [LinearEquiv.symm_apply_apply]
      map_rel_iff' := by
        intro S S'
        change S.toSubmodule.comap e.toLinearEquiv.toLinearMap ≤
            S'.toSubmodule.comap e.toLinearEquiv.toLinearMap ↔ S.toSubmodule ≤ S'.toSubmodule
        exact Submodule.comap_le_comap_iff_of_surjective e.toLinearEquiv.surjective }
  let : IsSimpleOrder (Subrepresentation τ) := hτ
  exact (OrderIso.isSimpleOrder_iff iso).mpr inferInstance

theorem isIrreducible_of_character_mem_blocksIrr {K W : Type} [Group K] [Fintype K]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ K W)
    (hσ : σ.character ∈ BlocksIrr K) : σ.IsIrreducible := by
  obtain ⟨W', i₁, i₂, i₃, τ, hτ, hchar⟩ := hσ
  let : τ.IsIrreducible := hτ
  let : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hdim := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  have hττ := Representation.char_orthonormal τ τ
  rw [ite_eq_left ⟨Representation.Equiv.refl τ⟩] at hττ
  rw [← hchar, hττ] at hdim
  obtain ⟨f, hf⟩ : ∃ f : Representation.IntertwiningMap τ σ, f ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    have : Subsingleton (Representation.IntertwiningMap τ σ) :=
      ⟨fun a b => (h a).trans (h b).symm⟩
    rw [Module.finrank_zero_of_subsingleton] at hdim
    norm_num at hdim
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hfin : Module.finrank ℂ W' = Module.finrank ℂ W := by
    have h1 := congrFun hchar 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := f.toLinearMap)).mp hinj
  exact isIrreducible_of_equiv (f.ofBijective ⟨hinj, hsurj⟩) hτ

end IrreducibleCriteria

section Inertia

variable {H : Type*} [Group H] (N : Subgroup H) [N.Normal]

@[expose] def conjugateNormalCharacter (θ : N → ℂ) (h : H) : N → ℂ :=
  fun n => θ ⟨h⁻¹ * n * h, Subgroup.Normal.conj_mem' inferInstance _ n.2 h⟩

theorem conjugateNormalCharacter_apply (θ : N → ℂ) (h : H) (n : N) :
    conjugateNormalCharacter N θ h n =
      θ ⟨h⁻¹ * n * h, Subgroup.Normal.conj_mem' inferInstance _ n.2 h⟩ := rfl

omit [N.Normal] in
private theorem apply_eq_of_coe_eq (θ : N → ℂ) {x y : N} (h : (x : H) = y) : θ x = θ y := by
  rw [Subtype.ext h]

theorem conjugateNormalCharacter_one (θ : N → ℂ) : conjugateNormalCharacter N θ 1 = θ := by
  funext n
  rw [conjugateNormalCharacter_apply]
  exact apply_eq_of_coe_eq N θ (by simp)

theorem conjugateNormalCharacter_mul (θ : N → ℂ) (a b : H) :
    conjugateNormalCharacter N θ (a * b) =
      conjugateNormalCharacter N (conjugateNormalCharacter N θ b) a := by
  funext n
  rw [conjugateNormalCharacter_apply, conjugateNormalCharacter_apply,
    conjugateNormalCharacter_apply]
  exact apply_eq_of_coe_eq N θ (by simp only; group)

@[expose] def characterInertiaSubgroup (θ : N → ℂ) : Subgroup H where
  carrier := {h | conjugateNormalCharacter N θ h = θ}
  one_mem' := conjugateNormalCharacter_one N θ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [conjugateNormalCharacter_mul, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h1 := conjugateNormalCharacter_mul N θ a⁻¹ a
    rw [inv_mul_cancel, conjugateNormalCharacter_one, ha] at h1
    exact h1.symm

theorem mem_characterInertiaSubgroup_iff (θ : N → ℂ) (h : H) :
    h ∈ characterInertiaSubgroup N θ ↔ conjugateNormalCharacter N θ h = θ := Iff.rfl

theorem le_characterInertiaSubgroup {θ : N → ℂ} (hθ : BlocksIsClassFunction θ) :
    N ≤ characterInertiaSubgroup N θ := by
  intro h hh
  rw [mem_characterInertiaSubgroup_iff]
  funext n
  rw [conjugateNormalCharacter_apply]
  have h1 := hθ n ⟨h, hh⟩⁻¹
  rw [← h1]
  exact apply_eq_of_coe_eq N θ (by simp)

theorem conjugateNormalCharacter_mul_of_mem (θ : N → ℂ) (h : H) {i : H}
    (hi : i ∈ characterInertiaSubgroup N θ) :
    conjugateNormalCharacter N θ (h * i) = conjugateNormalCharacter N θ h := by
  rw [conjugateNormalCharacter_mul, (mem_characterInertiaSubgroup_iff N θ i).mp hi]

theorem conjugateNormalCharacter_eq_iff (θ : N → ℂ) (h k : H) :
    conjugateNormalCharacter N θ h = conjugateNormalCharacter N θ k ↔
      (h : H ⧸ characterInertiaSubgroup N θ) = (k : H ⧸ characterInertiaSubgroup N θ) := by
  rw [QuotientGroup.eq, mem_characterInertiaSubgroup_iff]
  constructor
  · intro heq
    rw [conjugateNormalCharacter_mul, ← heq, ← conjugateNormalCharacter_mul, inv_mul_cancel,
      conjugateNormalCharacter_one]
  · intro heq
    have h2 := conjugateNormalCharacter_mul_of_mem N θ h
      (i := h⁻¹ * k) ((mem_characterInertiaSubgroup_iff N θ _).mpr heq)
    rw [mul_inv_cancel_left] at h2
    exact h2.symm

@[expose] def normalConj (h : H) : N →* N where
  toFun n := ⟨h⁻¹ * n * h, Subgroup.Normal.conj_mem' inferInstance _ n.2 h⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem normalConj_surjective (h : H) : Function.Surjective (normalConj N h) := by
  intro n
  refine ⟨⟨h * n * h⁻¹, Subgroup.Normal.conj_mem inferInstance _ n.2 h⟩, ?_⟩
  apply Subtype.ext
  change h⁻¹ * (h * n * h⁻¹) * h = n
  group

theorem conjugateNormalCharacter_eq_comp (θ : N → ℂ) (h : H) :
    conjugateNormalCharacter N θ h = θ ∘ normalConj N h := rfl

end Inertia

section CosetSums

variable {H : Type*} [Group H] [Fintype H] (I : Subgroup H)

theorem sum_eq_card_mul_sum_of_leftCoset_reps (C : Finset H)
    (hC : ∀ q : H ⧸ I, ∃! h, h ∈ C ∧ (h : H ⧸ I) = q) (F : H → ℂ)
    (hF : ∀ h, ∀ i ∈ I, F (h * i) = F h) :
    ∑ c : H, F c = (Nat.card I : ℂ) * ∑ h ∈ C, F h := by
  let e : C × I → H := fun x => (x.1 : H) * x.2
  have hrep : ∀ h ∈ C, ∀ k ∈ C, (h : H ⧸ I) = (k : H ⧸ I) → h = k := by
    intro h hh k hk hhk
    obtain ⟨r, -, hr⟩ := hC (h : H ⧸ I)
    exact (hr h ⟨hh, rfl⟩).trans (hr k ⟨hk, hhk.symm⟩).symm
  have hbij : Function.Bijective e := by
    constructor
    · rintro ⟨⟨h, hh⟩, ⟨i, hi⟩⟩ ⟨⟨k, hk⟩, ⟨j, hj⟩⟩ heq
      simp only [e] at heq
      have hhk : (h : H ⧸ I) = (k : H ⧸ I) := by
        rw [QuotientGroup.eq]
        have : h⁻¹ * k = i * j⁻¹ := by
          rw [show k = h * i * j⁻¹ by rw [heq]; group]
          group
        rw [this]
        exact I.mul_mem hi (I.inv_mem hj)
      have hkh := hrep h hh k hk hhk
      subst hkh
      have hij : i = j := mul_left_cancel heq
      subst hij
      rfl
    · intro c
      obtain ⟨h, ⟨hh, hq⟩, -⟩ := hC (c : H ⧸ I)
      have hmem : h⁻¹ * c ∈ I := QuotientGroup.eq.mp hq
      exact ⟨(⟨h, hh⟩, ⟨h⁻¹ * c, hmem⟩), by simp [e]⟩
  rw [← Fintype.sum_bijective e hbij (fun x => F (e x)) F (fun _ => rfl)]
  simp only [e, Fintype.sum_prod_type]
  have hinner : ∀ x : C, ∑ y : I, F ((x : H) * y) = (Nat.card I : ℂ) * F x := by
    intro x
    rw [Finset.sum_congr rfl fun (y : I) _ => hF x (y : H) y.2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp_rw [hinner]
  rw [← Finset.mul_sum, Finset.sum_coe_sort C (fun h => F h)]

theorem exists_leftCoset_reps [DecidableEq H] :
    ∃ C : Finset H, ∀ q : H ⧸ I, ∃! h, h ∈ C ∧ (h : H ⧸ I) = q := by
  refine ⟨Finset.univ.image (fun q : H ⧸ I => q.out), fun q => ⟨q.out, ⟨?_, ?_⟩, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  · exact QuotientGroup.out_eq' q
  · rintro h ⟨hh, rfl⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hh
    rw [QuotientGroup.out_eq']

end CosetSums

section Main

variable {H : Type} [Group H] [Fintype H] (N : Subgroup H) [N.Normal]

omit [Fintype H] [N.Normal] in
private theorem comp_blocksIrr {K L : Type} [Group K] [Group L] (f : K →* L)
    (hf : Function.Surjective f) {χ : L → ℂ} (hχ : χ ∈ BlocksIrr L) : χ ∘ f ∈ BlocksIrr K := by
  obtain ⟨W, i₁, i₂, i₃, τ, hτ, rfl⟩ := hχ
  exact ⟨W, i₁, i₂, i₃, τ.comp f, CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective f hf τ hτ,
    rfl⟩

omit [Fintype H] [N.Normal] in
private theorem classFunction_of_mem_blocksIrr {K : Type} [Group K] {χ : K → ℂ}
    (hχ : χ ∈ BlocksIrr K) : BlocksIsClassFunction χ := by
  obtain ⟨W, _, _, _, σ, _, rfl⟩ := hχ
  intro g h
  exact Representation.char_conj σ g h

omit [Fintype H] in
theorem conjugateNormalCharacter_mem_blocksIrr {θ : N → ℂ} (hθ : θ ∈ BlocksIrr N) (h : H) :
    conjugateNormalCharacter N θ h ∈ BlocksIrr N := by
  rw [conjugateNormalCharacter_eq_comp]
  exact comp_blocksIrr _ (normalConj_surjective N h) hθ

omit [Fintype H] [N.Normal] in
theorem mem_blocksIrr_of_norm_one {K W : Type} [Group K] [Fintype K] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ K W)
    (h : BlocksInnerProduct τ.character τ.character = 1) : τ.character ∈ BlocksIrr K := by
  obtain ⟨m, μ, hμ⟩ := exists_blocksIrr_sum τ
  rw [hμ] at h ⊢
  rw [blocksInnerProduct_sum_blocksIrr_self] at h
  have hsum : ∑ l, (Finset.univ.filter fun k => (μ k : K → ℂ) = μ l).card = 1 := by
    exact_mod_cast h
  have hm := card_le_sum_card_filter μ
  rw [hsum] at hm
  rcases m with _ | _ | m
  · simp at hsum
  · rw [Fin.sum_univ_one]
    exact (μ 0).2
  · omega

omit [Fintype H] [N.Normal] in
theorem one_le_norm_of_character_ne_zero {K W : Type} [Group K] [Fintype K] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ K W) (hτ : τ.character ≠ 0) :
    ∃ c : ℕ, 1 ≤ c ∧ BlocksInnerProduct τ.character τ.character = c := by
  obtain ⟨m, μ, hμ⟩ := exists_blocksIrr_sum τ
  rw [hμ, blocksInnerProduct_sum_blocksIrr_self]
  refine ⟨_, ?_, rfl⟩
  have hm := card_le_sum_card_filter μ
  rcases m with _ | m
  · exfalso
    apply hτ
    rw [hμ]
    simp
  · omega

omit [N.Normal] in
theorem exists_representation_inducedFunction (I : Subgroup H) {ψ : I → ℂ}
    (hψ : ψ ∈ BlocksIrr I) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (τ : Representation ℂ H W), τ.character = inducedFunction I ψ := by
  rw [blocksIrr_eq_irreducible_characters] at hψ
  obtain ⟨data, -, rfl⟩ := hψ
  let D := coinducedFiniteComplexRepresentation I data
  exact ⟨D.vector, inferInstance, inferInstance, inferInstance, D.representation,
    funext fun g => coinducedFiniteComplexRepresentation_character I data g⟩

omit [N.Normal] in
theorem inducedFunction_norm_one_of_restrict (I : Subgroup H) (P : Subgroup I) {θ' : P → ℂ}
    (hθ' : θ' ∈ BlocksIrr P) {ψ ψ' : I → ℂ} (hψ : ψ ∈ BlocksIrr I) (hψ' : ψ' ∈ BlocksIrr I)
    (hψres : (fun p : P => ψ p) = θ') (hψ'res : (fun p : P => ψ' p) = θ')
    (hone : BlocksInnerProduct (fun p : P => inducedFunction I ψ' ((p : I) : H)) θ' = 1) :
    BlocksInnerProduct (inducedFunction I ψ') (inducedFunction I ψ') = 1 ∧
      (ψ ≠ ψ' → BlocksInnerProduct (inducedFunction I ψ) (inducedFunction I ψ') = 0) := by
  obtain ⟨W, i₁, i₂, i₃, τ, hτ⟩ := exists_representation_inducedFunction I hψ'
  obtain ⟨m, ν, hν⟩ := exists_blocksIrr_sum (τ.comp I.subtype)
  have hΦ : (fun x : I => inducedFunction I ψ' x) = ∑ j, (ν j : I → ℂ) := by
    rw [← hν, ← hτ]
    rfl
  have hc : ∀ j, ∃ c : ℕ, BlocksInnerProduct (fun p : P => (ν j : I → ℂ) p) θ' = c := by
    intro j
    obtain ⟨Wj, _, _, _, τj, -, hτj⟩ := (ν j).2
    rw [← hτj]
    exact exists_natCast_blocksInnerProduct_restrict τj P hθ'
  choose c hcj using hc
  have hsum : ∑ j, c j = 1 := by
    have h1 := hone
    have hfun : (fun p : P => inducedFunction I ψ' ((p : I) : H)) =
        ∑ j, (fun p : P => (ν j : I → ℂ) p) := by
      funext p
      have := congrFun hΦ (p : I)
      simp only [Finset.sum_apply] at this ⊢
      exact this
    rw [hfun, blocksInnerProduct_finset_sum_left] at h1
    simp_rw [hcj] at h1
    exact_mod_cast h1
  have hc1 : ∀ j, ((ν j : I → ℂ) = ψ ∨ (ν j : I → ℂ) = ψ') → 1 ≤ c j := by
    intro j hj
    have hθθ : BlocksInnerProduct θ' θ' = 1 := by
      rw [blocksInnerProduct_of_mem_blocksIrr hθ' hθ', ite_eq_left rfl]
    have h1 : BlocksInnerProduct (fun p : P => (ν j : I → ℂ) p) θ' = 1 := by
      rcases hj with hj | hj <;> rw [hj]
      · rw [hψres, hθθ]
      · rw [hψ'res, hθθ]
    rw [hcj] at h1
    have : c j = 1 := by exact_mod_cast h1
    omega
  have hclass : BlocksIsClassFunction (inducedFunction I ψ') :=
    fun g h => inducedFunction_conjugate I ψ' g h
  have hfrob : ∀ χ : I → ℂ, χ ∈ BlocksIrr I →
      BlocksInnerProduct (inducedFunction I χ) (inducedFunction I ψ') =
        ((Finset.univ.filter fun j => χ = (ν j : I → ℂ)).card : ℂ) := by
    intro χ hχ
    rw [blocksInnerProduct_inducedFunction_left I χ _ hclass, hΦ,
      blocksInnerProduct_sum_blocksIrr_right ν hχ]
  have hcount : ∀ S : Finset (Fin m), (∀ j ∈ S, 1 ≤ c j) → S.card ≤ 1 := by
    intro S hS
    calc S.card = ∑ _j ∈ S, 1 := by simp
      _ ≤ ∑ j ∈ S, c j := Finset.sum_le_sum hS
      _ ≤ ∑ j, c j := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = 1 := hsum
  have hA := hcount (Finset.univ.filter fun j => ψ' = (ν j : I → ℂ)) (fun j hj =>
    hc1 j (Or.inr (Finset.mem_filter.mp hj).2.symm))
  have hne : inducedFunction I ψ' ≠ 0 := by
    intro h0
    have h1 := congrFun h0 1
    obtain ⟨Wψ, _, _, _, τψ, hτψ, hτψc⟩ := hψ'
    have hdeg := irreducible_character_degree_ne_zero
      ({ vector := Wψ, representation := τψ } : FiniteComplexRepresentation I) hτψ
    unfold inducedFunction at h1
    have hterm : ∀ x : H, (if hmember : x⁻¹ * 1 * x ∈ I then ψ' ⟨x⁻¹ * 1 * x, hmember⟩ else 0) =
        ψ' 1 := by
      intro x
      have hmem : x⁻¹ * 1 * x ∈ I := by simp [I.one_mem]
      rw [dite_eq_left hmem]
      congr 1
      apply Subtype.ext
      simp
    simp_rw [hterm] at h1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hτψc] at h1
    simp only [Pi.zero_apply, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero] at h1
    rcases h1 with h1 | h1 | h1
    · exact Nat.card_pos.ne' h1
    · exact (Fintype.card_ne_zero) h1
    · exact hdeg h1
  obtain ⟨n0, hn0, hnorm⟩ := one_le_norm_of_character_ne_zero τ (by rw [hτ]; exact hne)
  rw [hτ] at hnorm
  have hnorm' := hfrob ψ' hψ'
  rw [hnorm] at hnorm'
  have hn0' : n0 = (Finset.univ.filter fun j => ψ' = (ν j : I → ℂ)).card := by
    exact_mod_cast hnorm'
  have hcard1 : (Finset.univ.filter fun j => ψ' = (ν j : I → ℂ)).card = 1 := by omega
  refine ⟨by rw [hnorm, hn0', hcard1]; simp, fun hneq => ?_⟩
  rw [hfrob ψ hψ]
  have hB := hcount ((Finset.univ.filter fun j => ψ = (ν j : I → ℂ)) ∪
    (Finset.univ.filter fun j => ψ' = (ν j : I → ℂ))) (fun j hj => by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hc1 j (Or.inl (Finset.mem_filter.mp hj).2.symm)
      · exact hc1 j (Or.inr (Finset.mem_filter.mp hj).2.symm))
  rw [Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun j _ h1 h2 =>
    hneq (h1.trans h2.symm)), hcard1] at hB
  have h0 : (Finset.univ.filter fun j => ψ = (ν j : I → ℂ)).card = 0 := by omega
  rw [h0]
  simp

theorem inducedFunction_restrict_eq_sum_conjugate (I : Subgroup H) (hNI : N ≤ I) (θ : N → ℂ)
    (hIθ : ∀ i ∈ I, conjugateNormalCharacter N θ i = θ) (ψ : I → ℂ)
    (hψ : ∀ (x : I) (hx : (x : H) ∈ N), ψ x = θ ⟨x, hx⟩) (C : Finset H)
    (hC : ∀ q : H ⧸ I, ∃! h, h ∈ C ∧ (h : H ⧸ I) = q) :
    (fun n : N => inducedFunction I ψ n) = ∑ h ∈ C, conjugateNormalCharacter N θ h := by
  funext n
  rw [Finset.sum_apply]
  unfold inducedFunction
  have hterm : ∀ c : H, (if hmember : c⁻¹ * (n : H) * c ∈ I then
      ψ ⟨c⁻¹ * n * c, hmember⟩ else 0) = conjugateNormalCharacter N θ c n := by
    intro c
    have hN : c⁻¹ * (n : H) * c ∈ N := Subgroup.Normal.conj_mem' inferInstance _ n.2 c
    rw [dite_eq_left (hNI hN), hψ _ hN]
    rfl
  simp_rw [hterm]
  rw [sum_eq_card_mul_sum_of_leftCoset_reps I C hC (fun c => conjugateNormalCharacter N θ c n)
    (fun h i hi => by rw [conjugateNormalCharacter_mul, hIθ i hi])]
  have hI0 : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

abbrev InertiaQuotient (θ : N → ℂ) : Type :=
  characterInertiaSubgroup N θ ⧸ N.subgroupOf (characterInertiaSubgroup N θ)

@[expose] noncomputable def inertiaInducedCharacter {θ : N → ℂ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (characterInertiaSubgroup N θ) V)
    (σ : InertiaQuotient N θ →* ℂˣ) : H → ℂ :=
  inducedFunction (characterInertiaSubgroup N θ)
    (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ)

theorem abelian_inertia_extension_induction_character_family {θ : N → ℂ}
    (hθ : θ ∈ BlocksIrr N) [IsMulCommutative (InertiaQuotient N θ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (characterInertiaSubgroup N θ) V)
    (hρ : ∀ (x : characterInertiaSubgroup N θ) (hx : (x : H) ∈ N), ρ.character x = θ ⟨x, hx⟩) :
    (∀ σ : InertiaQuotient N θ →* ℂˣ, inertiaInducedCharacter N ρ σ ∈ BlocksIrr H ∧
      inertiaInducedCharacter N ρ σ 1 = ((characterInertiaSubgroup N θ).index : ℂ) * θ 1) ∧
    Function.Injective (inertiaInducedCharacter N ρ) ∧
    (∀ ξ ∈ BlocksIrr H, 0 < BlocksInnerProduct (fun n : N => ξ n) θ ↔
      ∃ σ : InertiaQuotient N θ →* ℂˣ, ξ = inertiaInducedCharacter N ρ σ) ∧
    (∀ C : Finset H, (∀ q : H ⧸ characterInertiaSubgroup N θ,
        ∃! h, h ∈ C ∧ (h : H ⧸ characterInertiaSubgroup N θ) = q) →
      (∀ σ : InertiaQuotient N θ →* ℂˣ,
        (fun n : N => inertiaInducedCharacter N ρ σ n) =
          ∑ h ∈ C, conjugateNormalCharacter N θ h) ∧
      (∀ h ∈ C, ∀ k ∈ C, h ≠ k →
        conjugateNormalCharacter N θ h ≠ conjugateNormalCharacter N θ k) ∧
      (∀ h ∈ C, conjugateNormalCharacter N θ h ∈ BlocksIrr N) ∧
      ∀ σ : InertiaQuotient N θ →* ℂˣ, ∀ h ∈ C,
        BlocksInnerProduct (fun n : N => inertiaInducedCharacter N ρ σ n)
          (conjugateNormalCharacter N θ h) = 1) ∧
    ((characterInertiaSubgroup N θ).Normal → ∀ σ : InertiaQuotient N θ →* ℂˣ,
      ∀ g ∉ characterInertiaSubgroup N θ, inertiaInducedCharacter N ρ σ g = 0) := by
  unfold inertiaInducedCharacter
  have hNI : N ≤ characterInertiaSubgroup N θ :=
    le_characterInertiaSubgroup N (classFunction_of_mem_blocksIrr hθ)
  let e : N.subgroupOf (characterInertiaSubgroup N θ) ≃* N := Subgroup.subgroupOfEquivOfLe hNI
  have hθ' : (fun n : N.subgroupOf (characterInertiaSubgroup N θ) => ρ.character n) = θ ∘ e := by
    funext n
    exact hρ n n.2
  have hθ'irr : (fun n : N.subgroupOf (characterInertiaSubgroup N θ) => ρ.character n) ∈
      BlocksIrr (N.subgroupOf (characterInertiaSubgroup N θ)) := by
    rw [hθ']
    exact comp_blocksIrr e.toMonoidHom e.surjective hθ
  have hρN' :
      Representation.IsIrreducible (ρ.comp (N.subgroupOf (characterInertiaSubgroup N θ)).subtype) :=
    isIrreducible_of_character_mem_blocksIrr _ hθ'irr
  obtain ⟨hψirr, hψinj, hψiff, -⟩ :=
    irreducible_extension_abelian_quotient_character_twists _ ρ hρN'
  have hIθ : ∀ i ∈ characterInertiaSubgroup N θ, conjugateNormalCharacter N θ i = θ :=
    fun i hi => hi
  have hψN : ∀ (σ : InertiaQuotient N θ →* ℂˣ)
      (x : characterInertiaSubgroup N θ) (hx : (x : H) ∈ N),
      quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ x = θ ⟨x, hx⟩ := by
    intro σ x hx
    have h1 : (x : InertiaQuotient N θ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    simp [quotientTwist, h1, hρ x hx]
  have hψres : ∀ σ : InertiaQuotient N θ →* ℂˣ,
      (fun n : N.subgroupOf (characterInertiaSubgroup N θ) =>
        quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ n) =
        fun n : N.subgroupOf (characterInertiaSubgroup N θ) => ρ.character n := by
    intro σ
    funext n
    rw [hψN σ n n.2, hρ n n.2]
  have hres := fun C hC σ => inducedFunction_restrict_eq_sum_conjugate N
    (characterInertiaSubgroup N θ)
    hNI θ hIθ _ (hψN σ) C hC
  have hdist : ∀ C : Finset H, (∀ q : H ⧸ characterInertiaSubgroup N θ,
      ∃! h, h ∈ C ∧ (h : H ⧸ characterInertiaSubgroup N θ) = q) →
      ∀ h ∈ C, ∀ k ∈ C, h ≠ k →
        conjugateNormalCharacter N θ h ≠ conjugateNormalCharacter N θ k := by
    intro C hC h hh k hk hne heq
    have hq := (conjugateNormalCharacter_eq_iff N θ h k).mp heq
    obtain ⟨r, -, hr⟩ := hC (h : H ⧸ characterInertiaSubgroup N θ)
    exact hne ((hr h ⟨hh, rfl⟩).trans (hr k ⟨hk, hq.symm⟩).symm)
  have hmult : ∀ C : Finset H, (∀ q : H ⧸ characterInertiaSubgroup N θ,
      ∃! h, h ∈ C ∧ (h : H ⧸ characterInertiaSubgroup N θ) = q) →
      ∀ σ : InertiaQuotient N θ →* ℂˣ, ∀ h ∈ C,
      BlocksInnerProduct (fun n : N => inducedFunction (characterInertiaSubgroup N θ)
        (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) n)
        (conjugateNormalCharacter N θ h) = 1 := by
    intro C hC σ h hh
    rw [hres C hC σ, blocksInnerProduct_finset_sum_left]
    simp_rw [blocksInnerProduct_of_mem_blocksIrr (conjugateNormalCharacter_mem_blocksIrr N hθ _)
      (conjugateNormalCharacter_mem_blocksIrr N hθ h)]
    rw [Finset.sum_congr rfl fun k hk => if_congr
      (show (conjugateNormalCharacter N θ k = conjugateNormalCharacter N θ h) ↔ k = h from
        ⟨fun heq => by_contra fun hne => hdist C hC k hk h hh hne heq, fun heq => heq ▸ rfl⟩)
      rfl rfl]
    rw [Finset.sum_ite_eq' C h (fun _ => (1 : ℂ)), ite_eq_left hh]
  obtain ⟨C₀, hC₀⟩ := exists_leftCoset_reps (characterInertiaSubgroup N θ)
  have hθpair : ∀ σ : InertiaQuotient N θ →* ℂˣ,
      BlocksInnerProduct (fun n : N => inducedFunction (characterInertiaSubgroup N θ)
        (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) n) θ = 1 := by
    intro σ
    obtain ⟨h₀, ⟨hh₀, hq₀⟩, -⟩ := hC₀ (1 : H)
    have hθh₀ : conjugateNormalCharacter N θ h₀ = θ := by
      have h1 := (conjugateNormalCharacter_eq_iff N θ h₀ 1).mpr hq₀
      rwa [conjugateNormalCharacter_one] at h1
    have h2 := hmult C₀ hC₀ σ h₀ hh₀
    rwa [hθh₀] at h2
  have htransport : ∀ f g : N → ℂ, BlocksInnerProduct (f ∘ e) (g ∘ e) = BlocksInnerProduct f g :=
    fun f g => blocksInnerProduct_comp_surjective e.toMonoidHom e.surjective f g
  have hpairs : ∀ σ σ' : InertiaQuotient N θ →* ℂˣ,
      BlocksInnerProduct (inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ'))
        (inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ')) = 1 ∧
      (σ ≠ σ' → BlocksInnerProduct (inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ))
        (inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ')) = 0) := by
    intro σ σ'
    have hone : BlocksInnerProduct (fun p : N.subgroupOf (characterInertiaSubgroup N θ) =>
        inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ')
          ((p : _) : H))
        (fun n : N.subgroupOf (characterInertiaSubgroup N θ) => ρ.character n) = 1 := by
      rw [hθ']
      have h := htransport (fun n : N => inducedFunction (characterInertiaSubgroup N θ)
        (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ') n) θ
      rw [hθpair σ'] at h
      exact h
    obtain ⟨h1, h2⟩ := inducedFunction_norm_one_of_restrict (characterInertiaSubgroup N θ)
      (N.subgroupOf (characterInertiaSubgroup N θ)) hθ'irr (hψirr σ) (hψirr σ') (hψres σ) (hψres σ')
      hone
    exact ⟨h1, fun hne => h2 (fun heq => hne (hψinj heq))⟩
  have hirr : ∀ σ : InertiaQuotient N θ →* ℂˣ,
      inducedFunction (characterInertiaSubgroup N θ)
        (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) ∈
          BlocksIrr H := by
    intro σ
    obtain ⟨W, i₁, i₂, i₃, τ, hτ⟩ := exists_representation_inducedFunction
      (characterInertiaSubgroup N θ) (hψirr σ)
    rw [← hτ]
    apply mem_blocksIrr_of_norm_one
    rw [hτ]
    exact (hpairs σ σ).1
  have hinj : Function.Injective
      (fun σ : InertiaQuotient N θ →* ℂˣ =>
        inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ)) := by
    intro σ σ' heq
    by_contra hne
    have h0 := (hpairs σ σ').2 hne
    simp only at heq
    rw [heq, (hpairs σ σ').1] at h0
    exact one_ne_zero h0
  have hdeg : ∀ σ : InertiaQuotient N θ →* ℂˣ,
      inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) 1 =
        ((characterInertiaSubgroup N θ).index : ℂ) * θ 1 := by
    intro σ
    unfold inducedFunction
    have hterm : ∀ c : H, (if hmember : c⁻¹ * 1 * c ∈ characterInertiaSubgroup N θ then
        quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ
          ⟨c⁻¹ * 1 * c, hmember⟩ else 0) = θ 1 := by
      intro c
      have hmem : c⁻¹ * 1 * c ∈ N := by simp [N.one_mem]
      rw [dite_eq_left (hNI hmem), hψN σ _ hmem]
      congr 1
      apply Subtype.ext
      simp
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      ← (characterInertiaSubgroup N θ).index_mul_card, Nat.cast_mul]
    have hI0 : (Nat.card (characterInertiaSubgroup N θ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  have hiff : ∀ ξ ∈ BlocksIrr H, 0 < BlocksInnerProduct (fun n : N => ξ n) θ ↔
      ∃ σ : InertiaQuotient N θ →* ℂˣ,
        ξ = inducedFunction (characterInertiaSubgroup N θ)
          (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) := by
    intro ξ hξ
    constructor
    · intro hpos
      obtain ⟨W, i₁, i₂, i₃, τ, -, hτ⟩ := id hξ
      obtain ⟨m, ν, hν⟩ := exists_blocksIrr_sum (τ.comp (characterInertiaSubgroup N θ).subtype)
      have hξI : (fun x : characterInertiaSubgroup N θ => ξ x) =
          ∑ j, (ν j : characterInertiaSubgroup N θ → ℂ) := by
        rw [← hν, ← hτ]
        rfl
      have hc : ∀ j, ∃ c : ℕ, BlocksInnerProduct
          (fun p : N.subgroupOf (characterInertiaSubgroup N θ) =>
            (ν j : characterInertiaSubgroup N θ → ℂ) (p : characterInertiaSubgroup N θ))
          (fun n : N.subgroupOf (characterInertiaSubgroup N θ) => ρ.character n) = c := by
        intro j
        obtain ⟨Wj, _, _, _, τj, -, hτj⟩ := (ν j).2
        rw [← hτj]
        exact exists_natCast_blocksInnerProduct_restrict τj _ hθ'irr
      choose c hcj using hc
      have htotal : BlocksInnerProduct (fun n : N => ξ n) θ = ((∑ j, c j : ℕ) : ℂ) := by
        rw [← htransport, ← hθ']
        have hfun : ((fun n : N => ξ n) ∘ e) =
            ∑ j, (fun p : N.subgroupOf (characterInertiaSubgroup N θ) =>
            (ν j : characterInertiaSubgroup N θ → ℂ) (p : characterInertiaSubgroup N θ)) := by
          funext p
          have := congrFun hξI (p : characterInertiaSubgroup N θ)
          simp only [Finset.sum_apply, Function.comp_apply] at this ⊢
          exact this
        rw [hfun, blocksInnerProduct_finset_sum_left]
        simp_rw [hcj]
        push_cast
        rfl
      obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
        by_contra hnone
        simp only [ne_eq, not_exists, not_not] at hnone
        rw [htotal, Finset.sum_eq_zero fun j _ => hnone j] at hpos
        simp at hpos
      have hjpos : 0 < BlocksInnerProduct
          (fun p : N.subgroupOf (characterInertiaSubgroup N θ) =>
            (ν j : characterInertiaSubgroup N θ → ℂ) (p : characterInertiaSubgroup N θ))
          (fun n : N.subgroupOf (characterInertiaSubgroup N θ) => ρ.character n) := by
        rw [hcj]
        exact_mod_cast Nat.pos_of_ne_zero hj
      obtain ⟨σ, hσ⟩ := (hψiff (ν j) (ν j).2).mp hjpos
      refine ⟨σ, ?_⟩
      have hξclass : BlocksIsClassFunction ξ := by
        rw [← hτ]
        intro g h
        exact Representation.char_conj τ g h
      have hfrob := blocksInnerProduct_inducedFunction_left (characterInertiaSubgroup N θ)
        (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) ξ hξclass
      rw [hξI, blocksInnerProduct_sum_blocksIrr_right ν (hψirr σ)] at hfrob
      have hmem : (Finset.univ.filter fun k =>
          quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ =
            (ν k : _ → ℂ)).Nonempty := ⟨j, by simp [hσ]⟩
      rw [blocksInnerProduct_of_mem_blocksIrr (hirr σ) hξ] at hfrob
      by_contra hne
      rw [ite_eq_right (fun h => hne h.symm)] at hfrob
      have := Finset.card_pos.mpr hmem
      have h0 : ((Finset.univ.filter fun k =>
          quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ =
            (ν k : _ → ℂ)).card : ℂ) = 0 := hfrob.symm
      norm_cast at h0
      omega
    · rintro ⟨σ, rfl⟩
      rw [hθpair σ]
      exact zero_lt_one
  have hvanish : (characterInertiaSubgroup N θ).Normal →
      ∀ σ : InertiaQuotient N θ →* ℂˣ,
      ∀ g ∉ characterInertiaSubgroup N θ, inducedFunction (characterInertiaSubgroup N θ)
        (quotientTwist (N.subgroupOf (characterInertiaSubgroup N θ)) ρ.character σ) g = 0 := by
    intro hInormal σ g hg
    unfold inducedFunction
    rw [Finset.sum_eq_zero, mul_zero]
    intro c _
    rw [dite_eq_right]
    intro hmem
    apply hg
    have := hInormal.conj_mem _ hmem c
    simpa [mul_assoc] using this
  refine ⟨fun σ => ⟨hirr σ, hdeg σ⟩, hinj, hiff, fun C hC => ⟨fun σ => hres C hC σ,
    hdist C hC, fun h _ => conjugateNormalCharacter_mem_blocksIrr N hθ h, hmult C hC⟩, hvanish⟩

end Main

end CFSG.Wreathed
