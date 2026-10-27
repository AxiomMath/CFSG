module

public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PSL2Natural.BasicSharp
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3

public section

namespace CFSG.Holt

open MulAction
open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

namespace PSL2Natural

variable {F : Type*} [Field F]

private theorem sl2_smul_vec (A : SL(2, F)) (x y : F) :
    A • (![x, y] : Fin 2 → F) =
      ![A.val 0 0 * x + A.val 0 1 * y, A.val 1 0 * x + A.val 1 1 * y] := by
  ext i
  fin_cases i <;>
    simp [show A • (![x, y] : Fin 2 → F) = A.val *ᵥ ![x, y] from rfl, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

private def pInf : ℙ F (Fin 2 → F) := Projectivization.mk F ![1, 0] (by simp)

private def pAff (y : F) : ℙ F (Fin 2 → F) := Projectivization.mk F ![y, 1] (by simp)

private theorem eq_pInf_or_eq_pAff (p : ℙ F (Fin 2 → F)) : p = pInf ∨ ∃ y : F, p = pAff y := by
  induction p using Projectivization.ind with
  | h v hv =>
    by_cases h1 : v 1 = 0
    · left
      have h0 : v 0 ≠ 0 := fun h0 => hv (by ext i; fin_cases i <;> simp [h0, h1])
      rw [pInf, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (v 0) h0, ?_⟩
      ext i; fin_cases i <;> simp [Units.smul_def, h1]
    · right
      refine ⟨v 0 / v 1, ?_⟩
      rw [pAff, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (v 1) h1, ?_⟩
      ext i; fin_cases i <;> simp [Units.smul_def, mul_div_cancel₀ _ h1]

private theorem toPGL_surjective [Finite F] [CharP F 2] :
    Function.Surjective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) := by
  refine Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => ?_
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (r : F)
  have hc0 : c ≠ 0 := fun h => r.ne_zero (by rw [hc, h, mul_zero])
  exact ⟨Units.mk0 c hc0, Units.ext (by simp [hc, pow_two])⟩

private theorem toPGL_smul (h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (x : ℙ F (Fin 2 → F)) : Matrix.ProjectiveSpecialLinearGroup.toPGL h • x = h • x := by
  induction h using QuotientGroup.induction_on with
  | _ A => rfl

theorem isSharplyThreeTransitive (F : Type*) [Field F] [Finite F] [CharP F 2] :
    IsSharplyThreeTransitive (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
      (ℙ F (Fin 2 → F)) := by
  obtain ⟨-, rho, -, -, -, -, hrho, -, -, hsharp, -⟩ :=
    CFSG.BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a F
  have hnat : ∀ (g : Matrix.ProjGenLinGroup (Fin 2) F) (x : ℙ F (Fin 2 → F)),
      rho g x = g • x := by
    intro g x
    rcases Matrix.ProjGenLinGroup.mk_surjective g with ⟨A, rfl⟩
    exact hrho _ _ A rfl
  refine ⟨fun hab hac hbc ha'b' ha'c' hb'c' => ?_, fun {g a b c} hab hac hbc ha hb hc => ?_⟩
  · obtain ⟨g, ⟨hga, hgb, hgc⟩, -⟩ := hsharp _ _ _ _ _ _ hab hac hbc ha'b' ha'c' hb'c'
    obtain ⟨h, rfl⟩ := toPGL_surjective g
    rw [hnat, toPGL_smul] at hga hgb hgc
    exact ⟨h, hga, hgb, hgc⟩
  · obtain ⟨k, -, hk⟩ := hsharp _ _ _ _ _ _ hab hac hbc hab hac hbc
    have h1 := hk (Matrix.ProjectiveSpecialLinearGroup.toPGL g)
      ⟨by rw [hnat, toPGL_smul, ha], by rw [hnat, toPGL_smul, hb], by rw [hnat, toPGL_smul, hc]⟩
    have h2 := hk 1 ⟨by rw [map_one, Equiv.Perm.one_apply], by rw [map_one, Equiv.Perm.one_apply],
      by rw [map_one, Equiv.Perm.one_apply]⟩
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (by rw [h1, map_one, h2])

private def sl2Unip (x : F) : SL(2, F) := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem sl2Unip_add (x y : F) : sl2Unip (x + y) = sl2Unip x * sl2Unip y := by
  apply Subtype.ext
  change (!![1, x + y; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] * !![1, y; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private def unipHom : Multiplicative F →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F where
  toFun x := (sl2Unip x.toAdd : SL(2, F))
  map_one' := by
    rw [toAdd_one, show sl2Unip (0 : F) = 1 from Subtype.ext (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [sl2Unip])]
    rfl
  map_mul' x y := by
    rw [toAdd_mul, sl2Unip_add]
    rfl

private theorem unipHom_smul_pInf (x : Multiplicative F) :
    unipHom x • (pInf : ℙ F (Fin 2 → F)) = pInf := by
  change sl2Unip x.toAdd • Projectivization.mk F (![1, 0] : Fin 2 → F) _ = _
  rw [Projectivization.smul_mk, pInf, Projectivization.mk_eq_mk_iff]
  exact ⟨1, by rw [one_smul, sl2_smul_vec]; simp [sl2Unip]⟩

private theorem unipHom_smul_pAff (x : Multiplicative F) (y : F) :
    unipHom x • (pAff y : ℙ F (Fin 2 → F)) = pAff (y + x.toAdd) := by
  change sl2Unip x.toAdd • Projectivization.mk F (![y, 1] : Fin 2 → F) _ = _
  rw [Projectivization.smul_mk, pAff, Projectivization.mk_eq_mk_iff]
  exact ⟨1, by rw [one_smul, sl2_smul_vec]; simp [sl2Unip]⟩

private theorem unipHom_sq [CharP F 2] (x : Multiplicative F) : unipHom x ^ 2 = 1 := by
  rw [← map_pow, pow_two, show x * x = 1 from CharTwo.add_self_eq_zero (R := F) x.toAdd,
    map_one]

theorem exists_unipotent [CharP F 2] :
    ∃ (a₀ : ℙ F (Fin 2 → F)) (U : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)),
      (∀ u ∈ U, u • a₀ = a₀ ∧ u ^ 2 = 1) ∧ ∀ b c, b ≠ a₀ → c ≠ a₀ → ∃ u ∈ U, u • b = c := by
  refine ⟨pInf, unipHom.range, ?_, fun b c hb hc => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨unipHom_smul_pInf x, unipHom_sq x⟩
  · obtain hb' | ⟨y, rfl⟩ := eq_pInf_or_eq_pAff b
    · exact absurd hb' hb
    obtain hc' | ⟨y', rfl⟩ := eq_pInf_or_eq_pAff c
    · exact absurd hc' hc
    refine ⟨unipHom (Multiplicative.ofAdd (y' - y)), ⟨_, rfl⟩, ?_⟩
    rw [unipHom_smul_pAff, toAdd_ofAdd, add_sub_cancel]

theorem card_projectiveLine [Finite F] :
    Nat.card (ℙ F (Fin 2 → F)) = Nat.card F + 1 :=
  Projectivization.card_of_finrank_two F _ (Module.finrank_fin_fun F)

theorem even_card [Finite F] [CharP F 2] : Even (Nat.card F) := by
  have := Fintype.ofFinite F
  rw [Nat.even_iff, ← Fintype.card_eq_nat_card]
  exact FiniteField.even_card_of_char_two (ringChar.eq F 2)

end PSL2Natural

namespace IsNaturalPSL2

variable {Δ : Type*} {K : Subgroup (Equiv.Perm Δ)} {n : ℕ}

theorem map_permCongrHom (hK : IsNaturalPSL2 K n) {Δ' : Type*} (e : Δ ≃ Δ') :
    IsNaturalPSL2 (K.map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) n := by
  obtain ⟨φ, ψ, hψ⟩ := hK
  refine ⟨φ.trans (e.permCongrHom.subgroupMap K), ψ.trans e, fun g p => ?_⟩
  simp only [MulEquiv.trans_apply, MulEquiv.coe_subgroupMap_apply, Equiv.trans_apply, hψ,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem finite (hK : IsNaturalPSL2 K n) : Finite Δ := by
  obtain ⟨-, ψ, -⟩ := hK
  exact Finite.of_equiv _ ψ

theorem card_eq (hK : IsNaturalPSL2 K n) : Nat.card Δ = Nat.card (GaloisField 2 n) + 1 := by
  obtain ⟨-, ψ, -⟩ := hK
  rw [← Nat.card_congr ψ, PSL2Natural.card_projectiveLine]

theorem card_eq_two_pow_add_one (hK : IsNaturalPSL2 K n) (hn : n ≠ 0) :
    Nat.card Δ = 2 ^ n + 1 := by
  rw [hK.card_eq, GaloisField.card 2 n hn]

theorem odd_card (hK : IsNaturalPSL2 K n) : Odd (Nat.card Δ) := by
  rw [hK.card_eq]
  exact PSL2Natural.even_card.add_one

theorem three_le_card (hK : IsNaturalPSL2 K n) : 3 ≤ Nat.card Δ := by
  rw [hK.card_eq]
  have := Finite.one_lt_card (α := GaloisField 2 n)
  have := PSL2Natural.even_card (F := GaloisField 2 n)
  obtain ⟨k, hk⟩ := this
  omega

theorem isSharplyThreeTransitive (hK : IsNaturalPSL2 K n) : IsSharplyThreeTransitive K Δ := by
  obtain ⟨φ, ψ, hψ⟩ := hK
  exact (PSL2Natural.isSharplyThreeTransitive (GaloisField 2 n)).of_equivariant φ ψ hψ

theorem isPretransitive (hK : IsNaturalPSL2 K n) : IsPretransitive K Δ :=
  have := hK.finite
  hK.isSharplyThreeTransitive.isPretransitive hK.three_le_card

theorem stabilizer_inf_inf_eq_bot (hK : IsNaturalPSL2 K n) {a b c : Δ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : stabilizer K a ⊓ stabilizer K b ⊓ stabilizer K c = ⊥ :=
  hK.isSharplyThreeTransitive.stabilizer_inf_inf_eq_bot hab hac hbc

private theorem exists_unipotent (hK : IsNaturalPSL2 K n) :
    ∃ (a₀ : Δ) (U : Subgroup K), (∀ u ∈ U, u • a₀ = a₀ ∧ u ^ 2 = 1) ∧
      ∀ b c, b ≠ a₀ → c ≠ a₀ → ∃ u ∈ U, u • b = c := by
  obtain ⟨φ, ψ, hψ⟩ := hK
  obtain ⟨a₀, U, hU1, hU2⟩ := PSL2Natural.exists_unipotent (F := GaloisField 2 n)
  refine ⟨ψ a₀, U.map (φ : _ →* K), ?_, fun b c hb hc => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · change ((φ v : K) : Equiv.Perm Δ) (ψ a₀) = ψ a₀
      rw [← hψ, (hU1 v hv).1]
    · rw [← map_pow, (hU1 v hv).2, map_one]
  · have hb' : ψ.symm b ≠ a₀ := fun e => hb (by rw [← e, Equiv.apply_symm_apply])
    have hc' : ψ.symm c ≠ a₀ := fun e => hc (by rw [← e, Equiv.apply_symm_apply])
    obtain ⟨v, hv, hvc⟩ := hU2 _ _ hb' hc'
    refine ⟨φ v, ⟨v, hv, rfl⟩, ?_⟩
    have h := hψ v (ψ.symm b)
    rw [hvc, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm

theorem mem_unipotentRadical_iff (hK : IsNaturalPSL2 K n) {a : Δ} {g : K} :
    g ∈ unipotentRadical K a ↔ g • a = a ∧ g ^ 2 = 1 :=
  have := hK.finite
  hK.isSharplyThreeTransitive.mem_unipotentRadical_iff hK.odd_card hK.three_le_card
    hK.exists_unipotent

theorem isMulCommutative_unipotentRadical (hK : IsNaturalPSL2 K n) {a : Δ} :
    IsMulCommutative ↥(unipotentRadical K a) :=
  IsSharplyThreeTransitive.isMulCommutative_unipotentRadical fun _ =>
    hK.mem_unipotentRadical_iff

theorem existsUnique_unipotentRadical_smul_eq (hK : IsNaturalPSL2 K n) {a b c : Δ} (hb : b ≠ a)
    (hc : c ≠ a) : ∃! u : ↥(unipotentRadical K a), u • b = c :=
  have := hK.finite
  hK.isSharplyThreeTransitive.existsUnique_unipotentRadical_smul_eq hK.odd_card
    (fun _ => hK.mem_unipotentRadical_iff) hb hc

theorem card_unipotentRadical (hK : IsNaturalPSL2 K n) {a : Δ} :
    Nat.card ↥(unipotentRadical K a) = Nat.card (GaloisField 2 n) := by
  have := hK.finite
  rw [hK.isSharplyThreeTransitive.card_unipotentRadical hK.odd_card hK.three_le_card
    (fun _ => hK.mem_unipotentRadical_iff), hK.card_eq, Nat.add_sub_cancel]

theorem card_unipotentRadical_eq_two_pow (hK : IsNaturalPSL2 K n) (hn : n ≠ 0) {a : Δ} :
    Nat.card ↥(unipotentRadical K a) = 2 ^ n := by
  rw [hK.card_unipotentRadical, GaloisField.card 2 n hn]

theorem range_toPermHom (n : ℕ) :
    IsNaturalPSL2 (MulAction.toPermHom (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 n)) (ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n))).range n :=
  ⟨MonoidHom.ofInjective MulAction.toPerm_injective, Equiv.refl _, fun _ _ => rfl⟩

end IsNaturalPSL2

end CFSG.Holt
