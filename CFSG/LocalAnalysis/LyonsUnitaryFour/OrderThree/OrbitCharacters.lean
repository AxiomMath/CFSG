module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.NormalizerAction

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem exists_orbit_representatives_three {X : Type*} [Finite X] (σ : Equiv.Perm X)
    (h3 : σ ^ 3 = 1) (hfix : ∀ x, σ x ≠ x) :
    ∃ (k : ℕ) (rep : Fin k → X),
      Function.Bijective (fun p : Fin k × Fin 3 => (σ ^ (p.2 : ℕ)) (rep p.1)) := by
  classical
  let H := Subgroup.zpowers σ
  let Ω := MulAction.orbitRel.Quotient H X
  have : Finite Ω := Quotient.finite _
  let e : Fin (Nat.card Ω) ≃ Ω := (Finite.equivFin Ω).symm
  have hfix2 : ∀ x, (σ ^ 2) x ≠ x := by
    intro x hx
    apply hfix x
    calc σ x = σ ((σ ^ 2) x) := by rw [hx]
      _ = (σ ^ 3) x := by rw [pow_succ' σ 2]; rfl
      _ = x := by rw [h3]; rfl
  have hsmul : ∀ (g : H) (x : X), g • x = (g : Equiv.Perm X) x := fun _ _ => rfl
  refine ⟨Nat.card Ω, fun i => (e i).out, ?_, ?_⟩
  · rintro ⟨i, a⟩ ⟨i', b⟩ hab
    simp only at hab
    have horb : (e i).out ∈ MulAction.orbit H (e i').out := by
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨(σ ^ (a : ℕ))⁻¹ * σ ^ (b : ℕ), Subgroup.mul_mem _ (Subgroup.inv_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _)) (Subgroup.pow_mem _
          (Subgroup.mem_zpowers σ) _)⟩, ?_⟩
      rw [hsmul]
      change ((σ ^ (a : ℕ))⁻¹ * σ ^ (b : ℕ)) ((e i').out) = (e i).out
      rw [Equiv.Perm.mul_apply, ← hab]
      simp
    have hii : e i = e i' := by
      rw [← Quotient.out_eq (e i), ← Quotient.out_eq (e i')]
      exact Quotient.sound (MulAction.orbitRel_apply.mpr horb)
    have hi : i = i' := e.injective hii
    subst hi
    refine Prod.ext rfl ?_
    set x := (e i).out
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd (by simpa using hab.symm) (hfix x)
    · exact absurd (by simpa using hab.symm) (hfix2 x)
    · exact absurd (by simpa using hab) (hfix x)
    · rfl
    · exfalso
      apply hfix x
      apply σ.injective
      have : σ (σ x) = σ x := by simpa [pow_two] using hab.symm
      exact this
    · exact absurd (by simpa using hab) (hfix2 x)
    · exfalso
      apply hfix x
      apply σ.injective
      have : σ (σ x) = σ x := by simpa [pow_two] using hab
      exact this
    · rfl
  · intro y
    let ω : Ω := Quotient.mk _ y
    have hout : (e (e.symm ω)).out ∈ MulAction.orbit H y := by
      rw [Equiv.apply_symm_apply]
      exact MulAction.orbitRel_apply.mp (Quotient.exact (Quotient.out_eq ω))
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hout
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (g⁻¹).property
    have hy : y = (σ ^ z) ((e (e.symm ω)).out) := by
      rw [hz, ← hsmul, ← hg, inv_smul_smul]
    have h3' : σ ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, h3]
    have hz3 : σ ^ z = σ ^ (z % 3) := zpow_eq_zpow_emod z h3'
    have hnn : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
    have hlt : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
    refine ⟨⟨e.symm ω, ⟨(z % 3).toNat, by omega⟩⟩, ?_⟩
    simp only
    rw [hy, hz3]
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]

variable {G : Type} [Group G]

theorem conjugateCharacter_one_fun (S : Subgroup G) (m : G)
    (hm : m ∈ Subgroup.normalizer (S : Set G)) : conjugateCharacter S m 1 = 1 := by
  funext x
  rw [conjugateCharacter_apply hm]
  rfl

theorem blocksIrr_conj {S : Type} [Group S] {θ : S → ℂ} (hθ : θ ∈ CFSG.BlocksIrr S) (c x : S) :
    θ (c * x * c⁻¹) = θ x := by
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
  exact Representation.char_conj ρ x c

@[expose] noncomputable def conjugatePerm {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (P : (S → ℂ) → Prop)
    (hP : ∀ θ, P θ → P (conjugateCharacter S n θ))
    (hP' : ∀ θ, P θ → P (conjugateCharacter S n⁻¹ θ)) : Equiv.Perm {θ : S → ℂ // P θ} where
  toFun θ := ⟨conjugateCharacter S n θ.val, hP _ θ.property⟩
  invFun θ := ⟨conjugateCharacter S n⁻¹ θ.val, hP' _ θ.property⟩
  left_inv θ := Subtype.ext (by
    change conjugateCharacter S n⁻¹ (conjugateCharacter S n θ.val) = θ.val
    rw [conjugateCharacter_mul (inv_mem hn) hn, inv_mul_cancel, conjugateCharacter_one])
  right_inv θ := Subtype.ext (by
    change conjugateCharacter S n (conjugateCharacter S n⁻¹ θ.val) = θ.val
    rw [conjugateCharacter_mul hn (inv_mem hn), mul_inv_cancel, conjugateCharacter_one])

theorem conjugatePerm_pow_val {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (P : (S → ℂ) → Prop)
    (hP : ∀ θ, P θ → P (conjugateCharacter S n θ))
    (hP' : ∀ θ, P θ → P (conjugateCharacter S n⁻¹ θ)) (k : ℕ) (θ : {θ : S → ℂ // P θ}) :
    ((conjugatePerm hn P hP hP' ^ k) θ).val = conjugateCharacter S (n ^ k) θ.val := by
  induction k with
  | zero => rw [pow_zero, pow_zero, conjugateCharacter_one]; rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change conjugateCharacter S n ((conjugatePerm hn P hP hP' ^ k) θ).val = _
    rw [ih, conjugateCharacter_pow hn]

theorem order_three_orbit_partition [Finite G] {S : Subgroup G} (hshape : UnitaryFourSylowShape S)
    {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G)) (h3 : n ^ 3 ∈ innerActing S)
    (hfix : ∀ z ∈ (Subgroup.center S).map S.subtype, z ≠ 1 → n * z * n⁻¹ ≠ z) :
    ∃ (lam : Fin 5 → S → ℂ) (ψ : S → ℂ),
      (∀ i, lam i ∈ CFSG.BlocksIrr S ∧ lam i 1 = 1 ∧ lam i ≠ 1) ∧
      ψ ∈ CFSG.BlocksIrr S ∧ ψ 1 = 4 ∧
      (∀ (i i' : Fin 5) (a b : Fin 3), conjugateCharacter S (n ^ (a : ℕ)) (lam i) =
        conjugateCharacter S (n ^ (b : ℕ)) (lam i') → i = i' ∧ a = b) ∧
      (∀ a b : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ =
        conjugateCharacter S (n ^ (b : ℕ)) ψ → a = b) ∧
      (∀ χ ∈ CFSG.BlocksIrr S, χ ≠ 1 →
        (∃ (i : Fin 5) (a : Fin 3), χ = conjugateCharacter S (n ^ (a : ℕ)) (lam i)) ∨
          ∃ a : Fin 3, χ = conjugateCharacter S (n ^ (a : ℕ)) ψ) := by
  classical
  let := Fintype.ofFinite S
  have hninv : n⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem hn
  obtain ⟨-, -, hlin16, -, -, hover, hcases, hirr19, -, -⟩ := hshape.character_table
  have hdeg : ∀ χ ∈ CFSG.BlocksIrr S, χ 1 = 1 ∨ χ 1 = 4 := by
    intro χ hχ
    rcases hcases χ hχ with h1 | ⟨l, hl1, hl⟩
    · exact Or.inl h1
    · exact Or.inr (hover l hl1 χ hχ hl).1
  have hφ := normalizerConj_fixedPointFree hn hfix
  let PL : (S → ℂ) → Prop := fun θ => θ ∈ CFSG.BlocksIrr S ∧ θ 1 = 1 ∧ θ ≠ 1
  let PD : (S → ℂ) → Prop := fun θ => θ ∈ CFSG.BlocksIrr S ∧ θ 1 = 4
  have hPL : ∀ m ∈ Subgroup.normalizer (S : Set G), ∀ θ, PL θ → PL (conjugateCharacter S m θ) := by
    rintro m hm θ ⟨hθ, h1, hne⟩
    refine ⟨conjugateCharacter_mem_blocksIrr hm hθ, by rw [conjugateCharacter_apply_one hm, h1],
      fun h => hne ?_⟩
    have := congrArg (conjugateCharacter S m⁻¹) h
    rwa [conjugateCharacter_mul (inv_mem hm) hm, inv_mul_cancel, conjugateCharacter_one,
      conjugateCharacter_one_fun S _ (inv_mem hm)] at this
  have hPD : ∀ m ∈ Subgroup.normalizer (S : Set G), ∀ θ, PD θ → PD (conjugateCharacter S m θ) := by
    rintro m hm θ ⟨hθ, h4⟩
    exact ⟨conjugateCharacter_mem_blocksIrr hm hθ, by rw [conjugateCharacter_apply_one hm, h4]⟩
  let σL := conjugatePerm hn PL (hPL n hn) (hPL n⁻¹ hninv)
  let σD := conjugatePerm hn PD (hPD n hn) (hPD n⁻¹ hninv)
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := S)
  have hfinIrr : (CFSG.BlocksIrr S).Finite := by
    rw [blocksIrr_eq_range_basis basis]
    exact Set.finite_range _
  have := hfinIrr.to_subtype
  have : Finite {θ : S → ℂ // PL θ} :=
    Finite.of_injective (fun θ => (⟨θ.val, θ.property.1⟩ : CFSG.BlocksIrr S))
      (fun a b h => Subtype.ext (congrArg (fun t : CFSG.BlocksIrr S => (t : S → ℂ)) h))
  have : Finite {θ : S → ℂ // PD θ} :=
    Finite.of_injective (fun θ => (⟨θ.val, θ.property.1⟩ : CFSG.BlocksIrr S))
      (fun a b h => Subtype.ext (congrArg (fun t : CFSG.BlocksIrr S => (t : S → ℂ)) h))
  have hone : (1 : S → ℂ) ∈ {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1} := by
    refine ⟨?_, rfl⟩
    have h := inflateSign_mem_blocksIrr (Subgroup.center S) 1
    have h1 : (inflateSign (Subgroup.center S) 1 : S → ℂ) = 1 := by
      funext x
      simp [inflateSign_apply]
    rwa [h1] at h
  have hcardL : Nat.card {θ : S → ℂ // PL θ} = 15 := by
    have he : {θ : S → ℂ // PL θ} ≃ ↥({χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1} \ {1}) :=
      Equiv.subtypeEquivRight (fun θ => by
        simp only [PL, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        tauto)
    rw [Nat.card_congr he, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hone, hlin16]
  have hcardD : Nat.card {θ : S → ℂ // PD θ} = 3 := by
    have he : {θ : S → ℂ // PD θ} ≃
        ↥(CFSG.BlocksIrr S \ {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1}) :=
      Equiv.subtypeEquivRight (fun θ => by
        simp only [PD, Set.mem_sdiff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hθ, h4⟩
          exact ⟨hθ, fun ⟨_, h1⟩ => by rw [h4] at h1; norm_num at h1⟩
        · rintro ⟨hθ, hn1⟩
          rcases hdeg θ hθ with h1 | h4
          · exact absurd ⟨hθ, h1⟩ hn1
          · exact ⟨hθ, h4⟩)
    rw [Nat.card_congr he, Nat.card_coe_set_eq,
      Set.ncard_sdiff (fun χ hχ => hχ.1) (hfinIrr.subset fun χ hχ => hχ.1), hirr19, hlin16]
  have hcube : ∀ θ ∈ CFSG.BlocksIrr S, conjugateCharacter S (n ^ 3) θ = θ :=
    fun θ hθ => conjugateCharacter_innerActing h3 θ (blocksIrr_conj hθ)
  have hσL3 : σL ^ 3 = 1 := by
    ext θ : 1
    apply Subtype.ext
    rw [conjugatePerm_pow_val, hcube _ θ.property.1]
    rfl
  have hσD3 : σD ^ 3 = 1 := by
    ext θ : 1
    apply Subtype.ext
    rw [conjugatePerm_pow_val, hcube _ θ.property.1]
    rfl
  have hσLfix : ∀ θ, σL θ ≠ θ := by
    intro θ h
    have h' := congrArg Subtype.val h
    change conjugateCharacter S n θ.val = θ.val at h'
    rw [conjugateCharacter_eq_comp hn] at h'
    exact hshape.linear_comp_ne (normalizerConj S hn) hφ θ.property.1 θ.property.2.1
      θ.property.2.2 h'
  have hσDfix : ∀ θ, σD θ ≠ θ := by
    intro θ h
    have h' := congrArg Subtype.val h
    change conjugateCharacter S n θ.val = θ.val at h'
    rw [conjugateCharacter_eq_comp hn] at h'
    exact hshape.degree_four_comp_ne (normalizerConj S hn) hφ θ.property.1 θ.property.2 h'
  obtain ⟨kL, repL, hbijL⟩ := exists_orbit_representatives_three σL hσL3 hσLfix
  obtain ⟨kD, repD, hbijD⟩ := exists_orbit_representatives_three σD hσD3 hσDfix
  have hkL : kL = 5 := by
    have h := Nat.card_eq_of_bijective _ hbijL
    rw [hcardL, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin] at h
    omega
  have hkD : kD = 1 := by
    have h := Nat.card_eq_of_bijective _ hbijD
    rw [hcardD, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin] at h
    omega
  subst hkL hkD
  refine ⟨fun i => (repL i).val, (repD 0).val, fun i => (repL i).property,
    (repD 0).property.1, (repD 0).property.2, ?_, ?_, ?_⟩
  · intro i i' a b h
    have h' : (σL ^ (a : ℕ)) (repL i) = (σL ^ (b : ℕ)) (repL i') := by
      apply Subtype.ext
      rw [conjugatePerm_pow_val, conjugatePerm_pow_val]
      exact h
    have := hbijL.1 (a₁ := (i, a)) (a₂ := (i', b)) h'
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · intro a b h
    have h' : (σD ^ (a : ℕ)) (repD 0) = (σD ^ (b : ℕ)) (repD 0) := by
      apply Subtype.ext
      rw [conjugatePerm_pow_val, conjugatePerm_pow_val]
      exact h
    have := hbijD.1 (a₁ := (0, a)) (a₂ := (0, b)) h'
    exact congrArg Prod.snd this
  · intro χ hχ hne
    rcases hdeg χ hχ with h1 | h4
    · left
      obtain ⟨⟨i, a⟩, hia⟩ := hbijL.2 ⟨χ, hχ, h1, hne⟩
      refine ⟨i, a, ?_⟩
      have := congrArg Subtype.val hia
      simp only at this
      rw [conjugatePerm_pow_val] at this
      exact this.symm
    · right
      obtain ⟨⟨i, a⟩, hia⟩ := hbijD.2 ⟨χ, hχ, h4⟩
      refine ⟨a, ?_⟩
      have := congrArg Subtype.val hia
      simp only at this
      rw [conjugatePerm_pow_val, Subsingleton.elim i 0] at this
      exact this.symm

end CFSG.LyonsUnitaryFour
