module

public import CFSG.LieType.Simplicity.ReeLarge

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  ReeTag

section CharTwo

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

variable (K) in
theorem nrep_simple_mul_self
    (i : Fin τ.rank) :
    nrep τ K (simple τ i) * nrep τ K (simple τ i) = 1 := by
  rw [nrep_simple_eq]
  apply Subtype.ext
  change weylElt τ K i 1 * weylElt τ K i 1 = 1
  rw [weylElt_one_mul_self, show (-1 : Kˣ) = 1 from Units.ext (CharTwo.neg_eq 1), torusElt_one]

variable (K) in
theorem nrep_simple_mul_charTwo
    (i : Fin τ.rank) (w : WeylGroup τ) :
    nrep τ K (simple τ i * w) = nrep τ K (simple τ i) * nrep τ K w := by
  rcases (coxeterSystem τ).length_simple_mul w i with h | h
  · exact nrep_mul K (by rw [h, CoxeterSystem.length_simple, add_comm])
  · have hw : simple τ i * (simple τ i * w) = w := by
      rw [← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
    have h2 : nrep τ K w = nrep τ K (simple τ i) * nrep τ K (simple τ i * w) := by
      conv_lhs => rw [← hw]
      exact nrep_mul K (by rw [hw, CoxeterSystem.length_simple, ← h, add_comm])
    rw [h2, ← mul_assoc, nrep_simple_mul_self, one_mul]

variable (K) in
theorem nrep_mul_charTwo
    (v w : WeylGroup τ) : nrep τ K (v * w) = nrep τ K v * nrep τ K w := by
  induction v using (coxeterSystem τ).simple_induction_left with
  | one => rw [one_mul, nrep_one, one_mul]
  | mul_simple_left v i ih =>
    rw [mul_assoc, nrep_simple_mul_charTwo, ih, nrep_simple_mul_charTwo, mul_assoc]

variable (τ K) in
@[expose] noncomputable def nrepHom
    : WeylGroup τ →* adjointGroup τ K where
  toFun := nrep τ K
  map_one' := nrep_one
  map_mul' := nrep_mul_charTwo K

@[simp] theorem nrepHom_apply
    (w : WeylGroup τ) : nrepHom τ K w = nrep τ K w :=
  rfl

variable (K) in
theorem nrep_inv
    (w : WeylGroup τ) : nrep τ K w⁻¹ = (nrep τ K w)⁻¹ :=
  map_inv (nrepHom τ K) w

end CharTwo

section Cells

variable {τ : Tag} {K : Type} [Field K] [Finite K]

variable (τ K) in
theorem nrep_injective
    : Function.Injective (nrep τ K) := by
  intro w w' h
  have e : (⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ : monomialGroup τ K) =
      ⟨nrep τ K w', nrep_mem_monomialGroup τ K w'⟩ := Subtype.ext h
  rw [← weylHom_nrep τ K w, ← weylHom_nrep τ K w', e]

theorem eq_one_of_mul_nrep_mul_eq_one
    {w : WeylGroup τ} {b₁ b₂ : adjointGroup τ K}
    (hb₁ : b₁ ∈ (nativeData τ K).B) (hb₂ : b₂ ∈ (nativeData τ K).B)
    (h : b₁ * nrep τ K w * b₂ = 1) : w = 1 := by
  have e := nativeData_weylHom_eq_of_mul_eq ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ 1 hb₁ hb₂
    (one_mem _) (one_mem _) (by rw [h, OneMemClass.coe_one, mul_one, mul_one])
  rwa [weylHom_nrep, map_one] at e

end Cells

section F4Weyl

theorem relWords_mul_length : ∀ i : Fin ReeTag.F4.tag.rank, ∀ ω ∈ relWords ReeTag.F4,
    ∃ ω' ∈ relWords ReeTag.F4, (∀ k : Fin ReeTag.F4.tag.rank,
      (ReeTag.F4.reeOrbitWord i ++ ω).foldr (reflect ReeTag.F4.tag) (Pi.single k 1) =
        ω'.foldr (reflect ReeTag.F4.tag) (Pi.single k 1)) ∧
      (ω'.length = (ReeTag.F4.reeOrbitWord i).length + ω.length ∨
        ω.length = (ReeTag.F4.reeOrbitWord i).length + ω'.length) := by
  decide +kernel

theorem length_blockElt_mul_or
    (i : Fin ReeTag.F4.tag.rank) {w : WeylGroup ReeTag.F4.tag}
    (hw : w ∈ ReeTag.F4.relWeylRee) :
    (coxeterSystem ReeTag.F4.tag).length (ReeTag.F4.blockElt i * w) =
        (coxeterSystem ReeTag.F4.tag).length (ReeTag.F4.blockElt i) +
          (coxeterSystem ReeTag.F4.tag).length w ∨
      (coxeterSystem ReeTag.F4.tag).length w =
        (coxeterSystem ReeTag.F4.tag).length (ReeTag.F4.blockElt i) +
          (coxeterSystem ReeTag.F4.tag).length (ReeTag.F4.blockElt i * w) := by
  obtain ⟨ω, hω, rfl⟩ := exists_mem_relWords hw
  obtain ⟨ω', hω', hact, hlen⟩ := relWords_mul_length i ω hω
  have he : ReeTag.F4.blockElt i * (coxeterSystem ReeTag.F4.tag).wordProd ω =
      (coxeterSystem ReeTag.F4.tag).wordProd ω' := ext_single fun k => by
    rw [blockElt, ← CoxeterSystem.wordProd_append, CFSG.LieType.Ree.wordProd_smul,
      CFSG.LieType.Ree.wordProd_smul]
    exact hact k
  rw [he, (isReduced_of_mem_relWords hω).eq, (isReduced_of_mem_relWords hω').eq, blockElt,
    (isReduced_reeOrbitWord ReeTag.F4 i).eq]
  exact hlen

theorem blockElt_mul_blockElt_pow_eight :
    (ReeTag.F4.blockElt (0 : Fin 4) * ReeTag.F4.blockElt (1 : Fin 4)) ^ 8 = 1 := by
  refine ext_single fun k => ?_
  simp only [pow_succ, pow_zero, one_mul, mul_smul, CFSG.LieType.Ree.wordProd_smul, one_smul]
  revert k
  decide +kernel

theorem blockElt_zero_ne_blockElt_one :
    ReeTag.F4.blockElt (0 : Fin 4) ≠ ReeTag.F4.blockElt (1 : Fin 4) := by
  intro h
  have := congrArg (fun w : WeylGroup ReeTag.F4.tag =>
    w • (Pi.single (0 : Fin 4) 1 : Fin ReeTag.F4.tag.rank → ℤ)) h
  simp only [CFSG.LieType.Ree.wordProd_smul] at this
  revert this
  decide +kernel

@[expose] def blockIdx : Fin 2 → Fin ReeTag.F4.tag.rank :=
  ![(0 : Fin 4), (1 : Fin 4)]

@[simp] theorem blockIdx_zero : blockIdx 0 = (0 : Fin 4) :=
  rfl

@[simp] theorem blockIdx_one : blockIdx 1 = (1 : Fin 4) :=
  rfl

@[expose] noncomputable def blockGen
    (i : Fin 2) : ReeTag.F4.relWeylRee :=
  ⟨ReeTag.F4.blockElt (blockIdx i), reeOrbitWord_mem ReeTag.F4 (blockIdx i)⟩

@[simp] theorem coe_blockGen
    (i : Fin 2) :
    (blockGen i : WeylGroup ReeTag.F4.tag) = ReeTag.F4.blockElt (blockIdx i) :=
  rfl

theorem blockGen_zero :
    blockGen 0 = ⟨ReeTag.F4.blockElt (0 : Fin 4), reeOrbitWord_mem ReeTag.F4 (0 : Fin 4)⟩ :=
  rfl

theorem blockGen_one :
    blockGen 1 = ⟨ReeTag.F4.blockElt (1 : Fin 4), reeOrbitWord_mem ReeTag.F4 (1 : Fin 4)⟩ :=
  rfl

theorem blockGen_mul_self
    (i : Fin 2) : blockGen i * blockGen i = 1 :=
  Subtype.ext (ReeTag.F4.blockElt_mul_self (blockIdx i))

theorem blockGen_ne_one
    (i : Fin 2) : blockGen i ≠ 1 := fun h =>
  blockElt_ne_one ReeTag.F4 (blockIdx i) (congrArg Subtype.val h)

theorem blockGen_zero_ne_blockGen_one
    : blockGen 0 ≠ blockGen 1 := fun h =>
  blockElt_zero_ne_blockElt_one (congrArg Subtype.val h)

theorem blockGen_mul_pow_eight
    : (blockGen 0 * blockGen 1) ^ 8 = 1 :=
  Subtype.ext blockElt_mul_blockElt_pow_eight

theorem length_blockGen_mul_or
    (i : Fin 2) (w : ReeTag.F4.relWeylRee) :
    (coxeterSystem ReeTag.F4.tag).length ((blockGen i * w : ReeTag.F4.relWeylRee) :
        WeylGroup ReeTag.F4.tag) =
        (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
          (coxeterSystem ReeTag.F4.tag).length (w : WeylGroup ReeTag.F4.tag) ∨
      (coxeterSystem ReeTag.F4.tag).length (w : WeylGroup ReeTag.F4.tag) =
        (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
          (coxeterSystem ReeTag.F4.tag).length ((blockGen i * w : ReeTag.F4.relWeylRee) :
            WeylGroup ReeTag.F4.tag) :=
  length_blockElt_mul_or (blockIdx i) w.2

theorem length_blockGen_mul_or_mul
    (i : Fin 2) (w : ReeTag.F4.relWeylRee) :
    (coxeterSystem ReeTag.F4.tag).length ((blockGen i * w : ReeTag.F4.relWeylRee) :
        WeylGroup ReeTag.F4.tag) =
        (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
          (coxeterSystem ReeTag.F4.tag).length (w : WeylGroup ReeTag.F4.tag) ∨
      (coxeterSystem ReeTag.F4.tag).length ((blockGen i * (blockGen i * w) :
          ReeTag.F4.relWeylRee) : WeylGroup ReeTag.F4.tag) =
        (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
          (coxeterSystem ReeTag.F4.tag).length ((blockGen i * w : ReeTag.F4.relWeylRee) :
            WeylGroup ReeTag.F4.tag) := by
  rw [← mul_assoc, blockGen_mul_self, one_mul]
  exact length_blockGen_mul_or i w

theorem closure_range_blockGen
    : Subgroup.closure (Set.range blockGen) = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  have hle : Subgroup.closure (Set.range ReeTag.F4.blockElt) ≤
      (Subgroup.closure (Set.range blockGen)).map ReeTag.F4.relWeylRee.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hcases : ∀ k : Fin 4, (k = 0 ∨ k = 3) ∨ (k = 1 ∨ k = 2) := by decide
    rcases hcases k with (rfl | rfl) | (rfl | rfl)
    · exact ⟨blockGen 0, Subgroup.subset_closure ⟨0, rfl⟩, rfl⟩
    · exact ⟨blockGen 0, Subgroup.subset_closure ⟨0, rfl⟩, rfl⟩
    · exact ⟨blockGen 1, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
    · exact ⟨blockGen 1, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
  obtain ⟨c, hc, hcw⟩ := hle (ReeTag.F4.mem_closure_blockElt _ w rfl
    ((mem_relWeylRee ReeTag.F4).1 w.2))
  rwa [Subtype.ext hcw] at hc

end F4Weyl

section F4Fixed

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

variable (K a) in
@[expose] noncomputable def relNrepHom
    : ReeTag.F4.relWeylRee →* reeFixed ReeTag.F4 K a where
  toFun w := nrepFixed ReeTag.F4 K a w.2
  map_one' := Subtype.ext nrep_one
  map_mul' v w := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact Subtype.ext (nrep_mul_charTwo K (v : WeylGroup ReeTag.F4.tag) w)

theorem relNrepHom_apply
    (w : ReeTag.F4.relWeylRee) :
    relNrepHom K a w = nrepFixed ReeTag.F4 K a w.2 :=
  rfl

@[simp] theorem coe_relNrepHom
    (w : ReeTag.F4.relWeylRee) :
    (relNrepHom K a w : adjointGroup ReeTag.F4.tag K) = nrep ReeTag.F4.tag K w :=
  rfl

theorem relNrepHom_injective
    : Function.Injective (relNrepHom K a) := fun _ _ h =>
  Subtype.ext (nrep_injective _ K (congrArg Subtype.val h))

theorem relNrepHom_blockGen_mul_self
    (i : Fin 2) :
    relNrepHom K a (blockGen i) * relNrepHom K a (blockGen i) = 1 := by
  rw [← map_mul, blockGen_mul_self, map_one]

theorem relNrepHom_blockGen_mul_pow_eight :
    (relNrepHom K a (blockGen 0) * relNrepHom K a (blockGen 1)) ^ 8 = 1 := by
  rw [← map_mul, ← map_pow, blockGen_mul_pow_eight, map_one]

theorem eq_one_of_mul_relNrepHom_mul_eq_one
    (w : ReeTag.F4.relWeylRee)
    {b₁ b₂ : reeFixed ReeTag.F4 K a} (hb₁ : b₁ ∈ reeBorelPart ReeTag.F4 K a)
    (hb₂ : b₂ ∈ reeBorelPart ReeTag.F4 K a) (h : b₁ * relNrepHom K a w * b₂ = 1) : w = 1 := by
  have h' : (b₁ : adjointGroup ReeTag.F4.tag K) * nrep ReeTag.F4.tag K w * b₂ = 1 :=
    congrArg Subtype.val h
  exact Subtype.ext (eq_one_of_mul_nrep_mul_eq_one hb₁ hb₂ h')

variable (K a) in
theorem closure_reeBorelPart_union_blockGen :
    Subgroup.closure ((reeBorelPart ReeTag.F4 K a : Set (reeFixed ReeTag.F4 K a)) ∪
      Set.range fun i => relNrepHom K a (blockGen i)) = ⊤ := by
  refine eq_top_of_reeBorelPart_le (fun b hb => Subgroup.subset_closure (.inl hb)) fun k => ?_
  have hcases : ∀ k : Fin 4, (k = 0 ∨ k = 3) ∨ (k = 1 ∨ k = 2) := by decide
  rcases hcases k with (rfl | rfl) | (rfl | rfl)
  · exact Subgroup.subset_closure (.inr ⟨0, rfl⟩)
  · exact Subgroup.subset_closure (.inr ⟨0, rfl⟩)
  · exact Subgroup.subset_closure (.inr ⟨1, rfl⟩)
  · exact Subgroup.subset_closure (.inr ⟨1, rfl⟩)

end F4Fixed

end CFSG.SectionRank.LargeRee
