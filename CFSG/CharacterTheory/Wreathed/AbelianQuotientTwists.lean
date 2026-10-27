module

public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCharacterFamily

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

section Restriction

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_comp_subtype (ρ : Representation ℂ G V) (N : Subgroup G)
    (h : Representation.IsIrreducible (ρ.comp N.subtype)) : ρ.IsIrreducible := by
  let : IsSimpleOrder (Subrepresentation (ρ.comp N.subtype)) := h
  let toN : Subrepresentation ρ → Subrepresentation (ρ.comp N.subtype) := fun W =>
    ⟨W.toSubmodule, fun n v hv => W.apply_mem_toSubmodule n hv⟩
  have htoN : ∀ W, (toN W).toSubmodule = W.toSubmodule := fun _ => rfl
  change IsSimpleOrder (Subrepresentation ρ)
  have hnontrivial : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hequal
    have hb : (⊥ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊤ := bot_ne_top
    apply hb
    apply Subrepresentation.ext
    have := congrArg Subrepresentation.toSubmodule hequal
    exact this
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro W
  rcases eq_bot_or_eq_top (toN W) with hW | hW
  · left
    apply Subrepresentation.ext
    have := congrArg Subrepresentation.toSubmodule hW
    exact this
  · right
    apply Subrepresentation.ext
    have := congrArg Subrepresentation.toSubmodule hW
    exact this

end Restriction

section Twists

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

@[expose] def quotientTwist (χ : G → ℂ) (lam : G ⧸ N →* ℂˣ) : G → ℂ :=
  fun g => χ g * (lam (g : G ⧸ N) : ℂ)

@[expose] noncomputable def inflatedLinearRepresentation (lam : G ⧸ N →* ℂˣ) :
    Representation ℂ G ℂ :=
  scalarHomRepresentation ((Units.coeHom ℂ).comp (lam.comp (QuotientGroup.mk' N)))

@[expose] noncomputable def quotientTwistRepresentation {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (lam : G ⧸ N →* ℂˣ) : Representation ℂ G V where
  toFun g := (lam (g : G ⧸ N) : ℂ) • ρ g
  map_one' := by simp
  map_mul' x y := by
    ext v
    simp only [QuotientGroup.mk_mul, map_mul, Units.val_mul, LinearMap.smul_apply,
      Module.End.mul_apply, map_smul, smul_smul, mul_comm]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem quotientTwistRepresentation_apply (ρ : Representation ℂ G V) (lam : G ⧸ N →* ℂˣ)
    (g : G) : quotientTwistRepresentation N ρ lam g = (lam (g : G ⧸ N) : ℂ) • ρ g := rfl

theorem quotientTwistRepresentation_comp_subtype (ρ : Representation ℂ G V)
    (lam : G ⧸ N →* ℂˣ) :
    (quotientTwistRepresentation N ρ lam).comp N.subtype = ρ.comp N.subtype := by
  ext n v
  have h1 : ((n : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr n.2
  simp [quotientTwistRepresentation_apply, h1]

theorem quotientTwistRepresentation_character [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (lam : G ⧸ N →* ℂˣ) :
    (quotientTwistRepresentation N ρ lam).character = quotientTwist N ρ.character lam := by
  funext g
  change LinearMap.trace ℂ V ((lam (g : G ⧸ N) : ℂ) • ρ g) = _
  rw [map_smul, smul_eq_mul, quotientTwist, mul_comm]
  rfl

theorem tprod_inflatedLinearRepresentation_character [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (lam : G ⧸ N →* ℂˣ) :
    (Representation.tprod ρ (inflatedLinearRepresentation N lam)).character =
      quotientTwist N ρ.character lam := by
  rw [Representation.char_tensor, inflatedLinearRepresentation, scalarHomRepresentation_character]
  rfl

theorem quotientTwistRepresentation_isIrreducible (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible (ρ.comp N.subtype)) (lam : G ⧸ N →* ℂˣ) :
    (quotientTwistRepresentation N ρ lam).IsIrreducible := by
  apply isIrreducible_of_comp_subtype _ N
  rw [quotientTwistRepresentation_comp_subtype]
  exact hρ

theorem nontrivial_of_isIrreducible {H W : Type*} [Group H] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ H W) (hσ : σ.IsIrreducible) : Nontrivial W := by
  let : IsSimpleOrder (Subrepresentation σ) := hσ
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
  apply Subrepresentation.ext
  exact Subsingleton.elim _ _

theorem quotientTwist_injective [Fintype G] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible (ρ.comp N.subtype)) :
    Function.Injective (quotientTwist N ρ.character) := by
  intro lam mu h
  set A := quotientTwistRepresentation N ρ lam with hAdef
  set B := quotientTwistRepresentation N ρ mu with hBdef
  have hA : A.IsIrreducible := quotientTwistRepresentation_isIrreducible N ρ hρ lam
  have hB : B.IsIrreducible := quotientTwistRepresentation_isIrreducible N ρ hρ mu
  have hchar : A.character = B.character := by
    rw [hAdef, hBdef, quotientTwistRepresentation_character, quotientTwistRepresentation_character,
      h]
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hBA := Representation.char_orthonormal A B
  have hAA := Representation.char_orthonormal A A
  have hequiv : Nonempty (Representation.Equiv B A) := by
    by_contra hnot
    have hrefl : Nonempty (Representation.Equiv A A) := ⟨Representation.Equiv.refl A⟩
    rw [ite_eq_right hnot] at hBA
    rw [ite_eq_left hrefl] at hAA
    rw [← hchar] at hBA
    rw [hAA] at hBA
    norm_num at hBA
  obtain ⟨φ⟩ := hequiv
  have hNcomm : ∀ (n : N) (v : V), φ (ρ n v) = ρ n (φ v) := by
    intro n v
    have h1 := Representation.IntertwiningMap.isIntertwining B A φ.toIntertwiningMap (n : G) v
    have hB1 : B n = ρ n := by
      have := congrArg (fun f => f n) (quotientTwistRepresentation_comp_subtype N ρ mu)
      simpa [hBdef] using this
    have hA1 : A n = ρ n := by
      have := congrArg (fun f => f n) (quotientTwistRepresentation_comp_subtype N ρ lam)
      simpa [hAdef] using this
    rw [hB1, hA1] at h1
    exact h1
  let T : Representation.IntertwiningMap (ρ.comp N.subtype) (ρ.comp N.subtype) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ φ.toLinearEquiv.toLinearMap
      (fun n v => hNcomm n v)
  let : Representation.IsIrreducible (ρ.comp N.subtype) := hρ
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ.comp N.subtype)).2 T
  have hφ : ∀ v, φ v = c • v := by
    intro v
    have h1 := congrArg (fun f : Representation.IntertwiningMap (ρ.comp N.subtype)
      (ρ.comp N.subtype) => f v) hc
    simp only [Representation.IntertwiningMap.algebraMap_apply] at h1
    exact h1.symm.trans (by simp)
  have : Nontrivial V := nontrivial_of_isIrreducible A hA
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : φ v = 0 := by rw [hφ, zero_smul]
    exact hv (φ.toLinearEquiv.injective (h0.trans (map_zero _).symm))
  have hval : ∀ g : G, (lam (g : G ⧸ N) : ℂ) = (mu (g : G ⧸ N) : ℂ) := by
    intro g
    have h1 := Representation.IntertwiningMap.isIntertwining B A φ.toIntertwiningMap g v
    change φ (B g v) = A g (φ v) at h1
    rw [hφ, hφ, hBdef, hAdef, quotientTwistRepresentation_apply,
      quotientTwistRepresentation_apply] at h1
    simp only [LinearMap.smul_apply, map_smul, smul_smul] at h1
    have hgv : ρ g v ≠ 0 := by
      intro h0
      apply hv
      have := congrArg (ρ g⁻¹) h0
      simpa [← Module.End.mul_apply, ← map_mul] using this
    have h3 := smul_left_injective ℂ hgv h1
    have h4 : c * ((mu (g : G ⧸ N) : ℂ) - (lam (g : G ⧸ N) : ℂ)) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 hc0
    · exact (sub_eq_zero.mp h5).symm
  apply MonoidHom.ext
  intro q
  apply Units.ext
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact hval g

end Twists

section Regular

theorem sum_basis_character_of_isMulCommutative {Q : Type} [Group Q] [Fintype Q]
    [IsMulCommutative Q] (basis : FiniteIrreducibleCharacterBasis Q) (x : Q) :
    ∑ ℓ, (basis.representation ℓ).character x = if x = 1 then (Nat.card Q : ℂ) else 0 := by
  have hdeg : ∀ ℓ, (basis.representation ℓ).character 1 = 1 := by
    intro ℓ
    let : (basis.representation ℓ).representation.IsIrreducible := basis.irreducible ℓ
    rw [FiniteComplexRepresentation.character, Representation.char_one,
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (basis.representation ℓ).representation]
    simp
  set f : Q → ℂ := fun y => if y = 1 then (Nat.card Q : ℂ) else 0 with hf
  have hclass : ∀ e c : Q, f (c * e * c⁻¹) = f e := by
    intro e c
    simp only [hf]
    congr 1
    apply propext
    constructor
    · intro h
      have := congrArg (fun z => c⁻¹ * z * c) h
      simpa [mul_assoc] using this
    · rintro rfl
      simp
  have hrec := finiteIrreducibleCharacterBasis_reconstruction basis f hclass x
  have hpair : ∀ ℓ, characterPairing f (basis.representation ℓ).character = 1 := by
    intro ℓ
    unfold characterPairing
    rw [Finset.sum_eq_single 1]
    · simp only [hf, ↓reduceIte, inv_one, hdeg, mul_one]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    · intro y _ hy
      simp [hf, hy]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [hpair, one_mul] at hrec
  exact hrec.symm

end Regular

section Main

variable {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]

theorem inducedFunction_one_apply (g : G) :
    inducedFunction N (1 : N → ℂ) g = if g ∈ N then (Nat.card (G ⧸ N) : ℂ) else 0 := by
  unfold inducedFunction
  have hconj : ∀ c : G, c⁻¹ * g * c ∈ N ↔ g ∈ N := by
    intro c
    constructor
    · intro h
      have := Subgroup.Normal.conj_mem inferInstance _ h c
      simpa [mul_assoc] using this
    · intro h
      have := Subgroup.Normal.conj_mem inferInstance _ h c⁻¹
      simpa [mul_assoc] using this
  have hterm : ∀ c : G, (if hmember : c⁻¹ * g * c ∈ N then (1 : N → ℂ) ⟨_, hmember⟩ else 0) =
      if g ∈ N then 1 else 0 := by
    intro c
    by_cases hg : g ∈ N
    · rw [dite_eq_left ((hconj c).mpr hg), ite_eq_left hg]
      rfl
    · rw [dite_eq_right (fun h => hg ((hconj c).mp h)), ite_eq_right hg]
  simp_rw [hterm]
  have hcard : (Nat.card G : ℂ) = (Nat.card (G ⧸ N) : ℂ) * (Nat.card N : ℂ) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.cast_mul]
  have hN0 : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  by_cases hg : g ∈ N
  · simp only [ite_eq_left hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hcard]
    field_simp
  · simp [hg]

omit [Fintype G] [N.Normal] in
private theorem bip_sum_left {K : Type} [Group K] [Fintype K] {ι : Type*} (s : Finset ι)
    (f : ι → K → ℂ) (g : K → ℂ) :
    BlocksInnerProduct (∑ i ∈ s, f i) g = ∑ i ∈ s, BlocksInnerProduct (f i) g := by
  unfold BlocksInnerProduct
  simp only [Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [Fintype G] [N.Normal] in
private theorem bip_comm {K : Type} [Group K] [Fintype K] (f g : K → ℂ) :
    BlocksInnerProduct f g = starRingEnd ℂ (BlocksInnerProduct g f) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

omit [Fintype G] [N.Normal] in
private theorem blocksIrr_classFunction {K : Type} [Group K] {χ : K → ℂ}
    (hχ : χ ∈ BlocksIrr K) : BlocksIsClassFunction χ := by
  obtain ⟨W, _, _, _, σ, _, rfl⟩ := hχ
  intro g h
  exact Representation.char_conj σ g h

theorem irreducible_extension_abelian_quotient_character_twists [IsMulCommutative (G ⧸ N)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : Representation.IsIrreducible (ρ.comp N.subtype)) :
    (∀ lam : G ⧸ N →* ℂˣ, quotientTwist N ρ.character lam ∈ BlocksIrr G) ∧
    Function.Injective (quotientTwist N ρ.character) ∧
    (∀ η ∈ BlocksIrr G,
      0 < BlocksInnerProduct (fun n : N => η n) (fun n : N => ρ.character n) ↔
        ∃ lam : G ⧸ N →* ℂˣ, η = quotientTwist N ρ.character lam) ∧
    ∀ η ∈ BlocksIrr G,
      0 < BlocksInnerProduct (fun n : N => η n) (fun n : N => ρ.character n) →
      (fun n : N => η n) = (fun n : N => ρ.character n) ∧ η 1 = Module.finrank ℂ V ∧
      ∃! lam : G ⧸ N →* ℂˣ,
        η = (Representation.tprod ρ (inflatedLinearRepresentation N lam)).character := by
  have hmem : ∀ lam, quotientTwist N ρ.character lam ∈ BlocksIrr G := fun lam =>
    ⟨V, inferInstance, inferInstance, inferInstance, quotientTwistRepresentation N ρ lam,
      quotientTwistRepresentation_isIrreducible N ρ hρ lam,
      quotientTwistRepresentation_character N ρ lam⟩
  have hinj := quotientTwist_injective N ρ hρ
  set θ : N → ℂ := fun n => ρ.character n with hθdef
  have hθirr : θ ∈ BlocksIrr N := ⟨V, inferInstance, inferInstance, inferInstance,
    ρ.comp N.subtype, hρ, rfl⟩
  have hθθ : BlocksInnerProduct θ θ = 1 := by
    rw [blocksInnerProduct_of_mem_blocksIrr hθirr hθirr, ite_eq_left rfl]
  have hres : ∀ lam, (fun n : N => quotientTwist N ρ.character lam n) = θ := by
    intro lam
    funext n
    have h1 : ((n : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr n.2
    simp [quotientTwist, h1, hθdef]
  obtain ⟨basisQ⟩ := finiteIrreducibleCharacterBasis_exists (G := G ⧸ N)
  have hdeg : ∀ ℓ, (basisQ.representation ℓ).character 1 = 1 := by
    intro ℓ
    let : (basisQ.representation ℓ).representation.IsIrreducible := basisQ.irreducible ℓ
    rw [FiniteComplexRepresentation.character, Representation.char_one,
      Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (basisQ.representation ℓ).representation]
    simp
  let lamℓ : basisQ.index → (G ⧸ N →* ℂˣ) := fun ℓ =>
    degreeOneCharacterUnits (basisQ.representation ℓ) (hdeg ℓ)
  have hInd : inducedFunction N θ = ∑ ℓ, quotientTwist N ρ.character (lamℓ ℓ) := by
    have hproj := blocks_induction_projection_formula N (1 : N → ℂ) ρ.character
      (fun g h => Representation.char_conj ρ g h)
    have h1 : inducedFunction N θ = ρ.character * inducedFunction N 1 := by
      rw [hproj]
      congr 1
      funext h
      simp [hθdef]
    rw [h1]
    funext g
    rw [Pi.mul_apply, inducedFunction_one_apply, Finset.sum_apply]
    simp only [quotientTwist, lamℓ, degreeOneCharacterUnits_val]
    rw [← Finset.mul_sum, sum_basis_character_of_isMulCommutative]
    congr 1
    simp only [QuotientGroup.eq_one_iff]
  have hpair : ∀ η ∈ BlocksIrr G, BlocksInnerProduct (fun n : N => η n) θ =
      ∑ ℓ, if quotientTwist N ρ.character (lamℓ ℓ) = η then 1 else 0 := by
    intro η hη
    rw [bip_comm, ← blocksInnerProduct_inducedFunction_left N θ η (blocksIrr_classFunction hη),
      hInd, bip_sum_left]
    simp_rw [blocksInnerProduct_of_mem_blocksIrr (hmem _) hη]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs <;> simp
  have hiff : ∀ η ∈ BlocksIrr G, 0 < BlocksInnerProduct (fun n : N => η n) θ ↔
      ∃ lam : G ⧸ N →* ℂˣ, η = quotientTwist N ρ.character lam := by
    intro η hη
    constructor
    · intro hpos
      by_contra hnone
      simp only [not_exists] at hnone
      rw [hpair η hη, Finset.sum_eq_zero fun ℓ _ =>
        ite_eq_right (fun h => hnone (lamℓ ℓ) h.symm)] at hpos
      exact lt_irrefl _ hpos
    · rintro ⟨lam, rfl⟩
      rw [hres lam, hθθ]
      exact zero_lt_one
  refine ⟨hmem, hinj, hiff, fun η hη hpos => ?_⟩
  obtain ⟨lam, rfl⟩ := (hiff η hη).mp hpos
  refine ⟨hres lam, ?_, ⟨lam, ?_, fun mu hmu => ?_⟩⟩
  · simp only [quotientTwist, QuotientGroup.mk_one, map_one, Units.val_one, mul_one]
    exact Representation.char_one ρ
  · dsimp only
    rw [tprod_inflatedLinearRepresentation_character]
  · dsimp only at hmu
    rw [tprod_inflatedLinearRepresentation_character] at hmu
    exact (hinj hmu).symm

end Main

end CFSG.Wreathed
