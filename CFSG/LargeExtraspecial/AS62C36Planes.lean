module

public import CFSG.LargeExtraspecial.AS62O4b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace AS62

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

private theorem exists_ne_zero_polar_eq_zero {U : Submodule (ZMod 2) V}
    (hU : finrank (ZMod 2) U = 2) (a : V) : ∃ u ∈ U, u ≠ 0 ∧ polar q a u = 0 := by
  let f : U →ₗ[ZMod 2] ZMod 2 := (q.polarBilin a).comp U.subtype
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [hU, finrank_self]; omega)
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨u, u.2, fun h => hu0 (Subtype.ext h), ?_⟩
  simpa [f, polarBilin_apply_apply] using hu

omit [FiniteDimensional (ZMod 2) V] in
private theorem span_inf_span_eq_bot {a b : V} (hab : a ≠ b) :
    (ZMod 2 ∙ a) ⊓ (ZMod 2 ∙ b) = ⊥ :=
  disjoint_iff.mp (Submodule.disjoint_span_singleton.mpr fun h => by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    rcases zmod2_cases c with rfl | rfl
    · rw [← hc, zero_smul]
    · rw [one_smul] at hc
      exact absurd hc hab)

omit [FiniteDimensional (ZMod 2) V] in
private theorem finrank_sup_span_eq_two {a b : V} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    finrank (ZMod 2) ↥((ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ b)) = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ZMod 2 ∙ a) (ZMod 2 ∙ b)
  rw [span_inf_span_eq_bot hab, finrank_bot, finrank_span_singleton ha0,
    finrank_span_singleton hb0] at h
  omega

omit [FiniteDimensional (ZMod 2) V] in
private theorem eq_or_eq_of_mem_sup_span {a b x : V} (hx : x ∈ (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ b)) :
    x = 0 ∨ x = a ∨ x = b ∨ x = a + b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
  rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;> simp

omit [FiniteDimensional (ZMod 2) V] in
private theorem span_pair_singular {a b : V} (ha : q a = 0) (hb : q b = 0)
    (hab : polar q a b = 0) {x : V} (hx : x ∈ (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ b)) : q x = 0 := by
  rcases eq_or_eq_of_mem_sup_span hx with rfl | rfl | rfl | rfl
  · exact map_zero q
  · exact ha
  · exact hb
  · rw [map_add_eq, ha, hb, hab, add_zero, add_zero]

theorem ncard_tsPlane_inf_eq_bot_le_two (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {ℓ : Submodule (ZMod 2) V} (hℓ : finrank (ZMod 2) ℓ = 2)
    (hqℓ : ∀ v ∈ ℓ, q v = 0) :
    {U : Submodule (ZMod 2) V | finrank (ZMod 2) U = 2 ∧ (∀ v ∈ U, q v = 0) ∧ U ⊓ ℓ = ⊥}.ncard
      ≤ 2 := by
  obtain ⟨a, haℓ, ha0⟩ : ∃ a ∈ ℓ, a ≠ 0 := by
    refine (Submodule.ne_bot_iff _).mp fun h => ?_
    rw [h, finrank_bot] at hℓ
    omega
  obtain ⟨P, hP2, hPq, haP, hPℓ, -⟩ := exists_tsPlane_ne hq ha0 hℓ hqℓ haℓ
  obtain ⟨b, hbP, hbℓ⟩ : ∃ b ∈ P, b ∉ ℓ := by
    by_contra! hle
    exact hPℓ (Submodule.eq_of_le_of_finrank_eq hle (by rw [hP2, hℓ]))
  have hab : a ≠ b := fun h => hbℓ (h ▸ haℓ)
  have hb0 : b ≠ 0 := fun h => hbℓ (h ▸ ℓ.zero_mem)
  have habP : a + b ∈ P := P.add_mem haP hbP
  have habℓ : a + b ∉ ℓ := fun h => hbℓ (by simpa using ℓ.sub_mem h haℓ)
  have hab0 : a + b ≠ 0 := fun h => habℓ (h ▸ ℓ.zero_mem)
  obtain ⟨W₁, hW₁2, hW₁q, hbW₁, hW₁P, -⟩ := exists_tsPlane_ne hq hb0 hP2 hPq hbP
  obtain ⟨W₂, hW₂2, hW₂q, habW₂, hW₂P, -⟩ := exists_tsPlane_ne hq hab0 hP2 hPq habP
  refine (Set.ncard_le_ncard (t := {W₁, W₂}) ?_ (Set.toFinite _)).trans
    ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  rintro U ⟨hU2, hUq, hUℓ⟩
  have hnotU : ∀ x ∈ ℓ, x ≠ 0 → x ∉ U := fun x hxℓ hx0 hxU => hx0 (by
    simpa [hUℓ] using (Submodule.mem_inf.mpr ⟨hxU, hxℓ⟩ : x ∈ U ⊓ ℓ))
  obtain ⟨u, huU, hu0, hau⟩ := exists_ne_zero_polar_eq_zero hU2 a
  have huℓ : u ∉ ℓ := fun h => hnotU u h hu0 huU
  have hau' : a ≠ u := fun h => huℓ (h ▸ haℓ)
  have haS : a ∈ (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ u) :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self a)
  have huS : u ∈ (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ u) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
  have huP : u ∈ P := by
    rcases eq_or_eq_of_tsPlane hV hq ha0 (finrank_sup_span_eq_two ha0 hu0 hau') hℓ hP2
      (fun x hx => span_pair_singular (hqℓ a haℓ) (hUq u huU) hau hx) hqℓ hPq haS haℓ haP
      (Ne.symm hPℓ) with h | h
    · exact absurd (h ▸ huS) huℓ
    · exact h ▸ huS
  have hu : u = b ∨ u = a + b := by
    rcases eq_or_eq_of_mem_sup_span
      ((sup_span_eq_of_ne hP2 haP hbP ha0 hb0 hab).symm ▸ huP) with h | h | h | h
    · exact absurd h hu0
    · exact absurd (h ▸ haℓ) huℓ
    · exact Or.inl h
    · exact Or.inr h
  have hUP : U ≠ P := fun h => hnotU a haℓ ha0 (h ▸ haP)
  rcases hu with rfl | rfl
  · exact Or.inl ((eq_or_eq_of_tsPlane hV hq hu0 hU2 hP2 hW₁2 hUq hPq hW₁q huU huP hbW₁
      (Ne.symm hW₁P)).resolve_left hUP)
  · exact Or.inr ((eq_or_eq_of_tsPlane hV hq hu0 hU2 hP2 hW₂2 hUq hPq hW₂q huU huP habW₂
      (Ne.symm hW₂P)).resolve_left hUP)

theorem card_le_twelve_of_map_eq (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {ℓ : Submodule (ZMod 2) V} (hℓ : finrank (ZMod 2) ℓ = 2)
    (hqℓ : ∀ v ∈ ℓ, q v = 0) (X : Subgroup (V ≃ₗ[ZMod 2] V))
    (hXO : X ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hX : ∀ σ ∈ X, ℓ.map (σ : V →ₗ[ZMod 2] V) = ℓ) : Nat.card X ≤ 12 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hmem : ∀ σ ∈ X, ∀ x ∈ ℓ, σ x ∈ ℓ := fun σ hσ x hx => by
    have h : σ x ∈ ℓ.map (σ : V →ₗ[ZMod 2] V) := Submodule.mem_map_of_mem hx
    rwa [hX σ hσ] at h
  let _ : MulAction X ↥((ℓ : Set V) \ {0}) :=
    { smul := fun σ x => ⟨(σ : V ≃ₗ[ZMod 2] V) x, hmem σ σ.2 x x.2.1, fun h =>
        x.2.2 (((σ : V ≃ₗ[ZMod 2] V).map_eq_zero_iff).mp h)⟩
      one_smul := fun x => rfl
      mul_smul := fun σ τ x => rfl }
  have hT : Nat.card ↥((ℓ : Set V) \ {0}) = 3 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem
      (show (0 : V) ∈ (ℓ : Set V) from ℓ.zero_mem), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hℓ]
    norm_num
  set φ := MulAction.toPermHom X ↥((ℓ : Set V) \ {0})
  have hker : Nat.card φ.ker ≤ 2 := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective (K := φ.ker)]
    refine card_le_two_of_fix_tsPlane hV hq hℓ hqℓ ?_ ?_
    · rintro _ ⟨σ, -, rfl⟩
      exact hXO σ.2
    · rintro _ ⟨σ, hσ, rfl⟩ u hu
      by_cases hu0 : u = 0
      · rw [hu0, map_zero]
      · exact congrArg Subtype.val (Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hσ) ⟨u, hu, hu0⟩)
  have hrange : Nat.card φ.range ≤ 6 := by
    calc Nat.card φ.range ≤ Nat.card (Equiv.Perm ↥((ℓ : Set V) \ {0})) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 6 := by rw [Nat.card_perm, hT]; rfl
  calc Nat.card X = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index _).symm
    _ = Nat.card φ.ker * Nat.card φ.range := by rw [Subgroup.index_ker]
    _ ≤ 2 * 6 := Nat.mul_le_mul hker hrange
    _ = 12 := by norm_num

end Quadratic

end AS62

end CFSG.LargeExtraspecial
