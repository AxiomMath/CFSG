module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local
import CFSG.RankThree.PartTwo.KFacts.L34Automizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Transport

variable {G H : Type} [Group G] [Group H]

private theorem mem_normalizer_map (e : G ≃* H) {E : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    e n ∈ Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup H) : Set H) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.mem_map_of_mem _ hn

private theorem twoLocal_map (e : G ≃* H) (h : LThreeFourTwoLocal G) : LThreeFourTwoLocal H := by
  obtain ⟨E, hE, y, hy, hy5, x, hx, hxy⟩ := h
  refine ⟨E.map e.toMonoidHom, hE.map _, e y, mem_normalizer_map e hy, ?_, e x,
    Subgroup.mem_map_of_mem _ hx, ?_⟩
  · rw [← hy5]
    exact orderOf_injective e.toMonoidHom e.injective y
  · rw [← map_mul, ← map_mul]
    exact fun h => hxy (e.injective h)

private theorem threeLocal_map (e : G ≃* H) (h : LThreeFourThreeLocal G) :
    LThreeFourThreeLocal H := by
  obtain ⟨E, hE, hc, a, ha, b, hb, hab⟩ := h
  refine ⟨E.map e.toMonoidHom, hE.map _, Subgroup.map_isMulCommutative _ _, e a,
    mem_normalizer_map e ha, e b, mem_normalizer_map e hb, ?_⟩
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ : ∃ g ∈ ({a, b, a * b} : Set G), e g = g' := by
    rcases hg' with rfl | rfl | rfl
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨a * b, Or.inr (Or.inr rfl), map_mul e a b⟩
  obtain ⟨h4, x, hx, hx2⟩ := hab g hg
  refine ⟨?_, e x, Subgroup.mem_map_of_mem _ hx, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, ← map_inv, ← map_mul, ← map_mul, h4 y hy]
  · rw [← map_pow, ← map_inv, ← map_mul, ← map_mul]
    exact fun h => hx2 (e.injective h)

end Transport

section TwoLocal

variable {k : Type} [Field k]

private def uM (a b : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, a; 0, 1, b; 0, 0, 1]

private def uSL (a b : k) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨uM a b, by simp [uM, Matrix.det_fin_three]⟩

private theorem uSL_add (a b c d : k) : uSL (a + c) (b + d) = uSL a b * uSL c d := by
  apply Subtype.ext
  change uM (a + c) (b + d) = uM a b * uM c d
  simp only [uM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

private theorem uSL_zero : uSL (0 : k) 0 = 1 := by
  apply Subtype.ext
  change uM (0 : k) 0 = 1
  rw [Matrix.one_fin_three]
  rfl

private noncomputable def uHom : Multiplicative (k × k) →* projectiveSL 3 k where
  toFun p := proj 3 k (uSL (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2)
  map_one' := by simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, uSL_zero, map_one]
  map_mul' p q := by simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, uSL_add, map_mul]

private def fiveM (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, 0; 1, ω, 0; 0, 0, 1]

private def fiveSL [CharP k 2] (ω : k) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨fiveM ω, by simp only [fiveM, Matrix.det_fin_three]; simp [CharTwo.neg_eq]⟩

private theorem fiveSL_mul_uSL [CharP k 2] (ω a b : k) :
    fiveSL ω * uSL a b = uSL b (a + ω * b) * fiveSL ω := by
  apply Subtype.ext
  change fiveM ω * uM a b = uM b (a + ω * b) * fiveM ω
  simp only [fiveM, uM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem fiveSL_pow_five [CharP k 2] {ω : k} (hω : ω * ω + ω + 1 = 0) :
    fiveSL ω ^ 5 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change fiveM ω ^ 5 = 1
  have h2 : fiveM ω ^ 2 = !![1, ω, 0; ω, ω, 0; 0, 0, 1] := by
    rw [sq]
    simp only [fiveM, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> grind
  have h4 : fiveM ω ^ 4 = !![ω, 1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [show fiveM ω ^ 4 = fiveM ω ^ 2 * fiveM ω ^ 2 by rw [← pow_add], h2]
    simp only [Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> grind
  rw [pow_succ, h4]
  simp only [fiveM, Matrix.mul_fin_three, Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> grind

private theorem proj_fiveSL_ne_one [CharP k 2] (ω : k) : proj 3 k (fiveSL ω) ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  have h01 := congrFun (congrFun hc 0) 1
  change fiveM ω 0 1 = _ at h01
  simp [fiveM, Matrix.scalar_apply] at h01

private theorem proj_uSL_one_one_ne_one : proj 3 k (uSL (1 : k) 1) ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
  have h02 := congrFun (congrFun hc 0) 2
  change uM (1 : k) 1 0 2 = _ at h02
  simp [uM, Matrix.scalar_apply] at h02

private theorem conj_uHom [CharP k 2] (ω a b : k) :
    proj 3 k (fiveSL ω) * uHom (Multiplicative.ofAdd (a, b)) * (proj 3 k (fiveSL ω))⁻¹ =
      uHom (Multiplicative.ofAdd (b, a + ω * b)) := by
  rw [mul_inv_eq_iff_eq_mul]
  change proj 3 k (fiveSL ω) * proj 3 k (uSL a b) =
    proj 3 k (uSL b (a + ω * b)) * proj 3 k (fiveSL ω)
  rw [← map_mul, ← map_mul, fiveSL_mul_uSL]

private theorem isPGroup_range_uHom [CharP k 2] :
    IsPGroup 2 (uHom : Multiplicative (k × k) →* projectiveSL 3 k).range := by
  rintro ⟨_, p, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change uHom p ^ 2 = 1
  obtain ⟨⟨a, b⟩, rfl⟩ := Multiplicative.ofAdd.surjective p
  rw [sq, ← map_mul, ← ofAdd_add, Prod.mk_add_mk, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]

private theorem mem_normalizer_range_uHom [CharP k 2] (ω : k) :
    proj 3 k (fiveSL ω) ∈ Subgroup.normalizer
      ((uHom : Multiplicative (k × k) →* projectiveSL 3 k).range : Set (projectiveSL 3 k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := Multiplicative.ofAdd.surjective p
    exact ⟨_, (conj_uHom ω a b).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨⟨c, d⟩, rfl⟩ := Multiplicative.ofAdd.surjective p
    refine ⟨Multiplicative.ofAdd (ω * c + d, c), ?_⟩
    have h1 := conj_uHom ω (ω * c + d) c
    rw [show ω * c + d + ω * c = d by
      rw [add_comm (ω * c) d, add_assoc, CharTwo.add_self_eq_zero, add_zero], hp] at h1
    exact mul_left_cancel (mul_right_cancel h1)

private theorem twoLocal_projectiveSL (hk : Nat.card k = 4) :
    LThreeFourTwoLocal (projectiveSL 3 k) := by
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨u, hu⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_units_ne_one hk
  have hω := CFSG.RankThree.PartTwo.KFacts.L34.val_mul_self_add hk hu
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨uHom.range, isPGroup_range_uHom, proj 3 k (fiveSL (u : k)),
    mem_normalizer_range_uHom _, orderOf_eq_prime ?_ (proj_fiveSL_ne_one _),
    uHom (Multiplicative.ofAdd (1, 0)), ⟨_, rfl⟩, fun h => proj_uSL_one_one_ne_one (k := k) ?_⟩
  · rw [← map_pow, fiveSL_pow_five hω, map_one]
  · have h1 := conj_uHom (u : k) 1 0
    rw [mul_zero, add_zero, h, mul_inv_cancel_right] at h1
    have e1 : Multiplicative.ofAdd ((1 : k), (1 : k)) =
        Multiplicative.ofAdd ((0 : k), (1 : k)) * Multiplicative.ofAdd ((1 : k), (0 : k)) := by
      rw [← ofAdd_add, Prod.mk_add_mk, zero_add, add_zero]
    have e2 : Multiplicative.ofAdd ((1 : k), (0 : k)) * Multiplicative.ofAdd ((1 : k), (0 : k)) =
        1 := by
      rw [← ofAdd_add, Prod.mk_add_mk, CharTwo.add_self_eq_zero, add_zero, Prod.mk_zero_zero,
        ofAdd_zero]
    change uHom (Multiplicative.ofAdd ((1 : k), (1 : k))) = 1
    rw [e1, map_mul, ← h1, ← map_mul, e2, map_one]

end TwoLocal

section ThreeLocal

open CFSG.RankThree.Asc83Table

private theorem conj_pow_of_rhoE {L : Type*} [Group L] (E : E9Basis L)
    (x : Subgroup.normalizer (Subgroup.closure (Set.range E.vec) : Set L))
    {M : Matrix (Fin 2) (Fin 2) (ZMod 3)}
    (hM : ((E.rhoE x : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = M) (h4 : M ^ 4 = 1)
    (h2 : M ^ 2 ≠ 1) :
    (∀ e ∈ Subgroup.closure (Set.range E.vec), (x : L) ^ 4 * e * ((x : L) ^ 4)⁻¹ = e) ∧
      ∃ e ∈ Subgroup.closure (Set.range E.vec), (x : L) ^ 2 * e * ((x : L) ^ 2)⁻¹ ≠ e := by
  have hker : ∀ n : ℕ, M ^ n = 1 ↔
      ∀ e ∈ Subgroup.closure (Set.range E.vec), e * (x : L) ^ n = (x : L) ^ n * e := by
    intro n
    have h1 : M ^ n = 1 ↔ x ^ n ∈ (rho E.equiv).ker := by
      rw [MonoidHom.mem_ker, map_pow, ← Units.val_eq_one, Units.val_pow_eq_pow_val]
      change M ^ n = 1 ↔ ((E.rhoE x : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ n = 1
      rw [hM]
    rw [h1, ker_rho, Subgroup.mem_subgroupOf, Subgroup.coe_pow, Subgroup.mem_centralizer_iff]
    rfl
  refine ⟨fun e he => ?_, ?_⟩
  · rw [← (hker 4).1 h4 e he, mul_inv_cancel_right]
  · by_contra hcon
    refine h2 ((hker 2).2 fun e he => ?_)
    have h : (x : L) ^ 2 * e * ((x : L) ^ 2)⁻¹ = e := by
      by_contra hne
      exact hcon ⟨e, he, hne⟩
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm

open CFSG.RankThree.PartTwo.KFacts.L34 in
private theorem threeLocal_projectiveSL {k : Type} [Field k] (hk : Nat.card k = 4) :
    LThreeFourThreeLocal (projectiveSL 3 k) := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set E := eZeroBasis hk hu
  have ha3 : aP u ^ 3 = 1 := pow_three_of_mem_eZero hk aP_mem_eZero
  have hf₁ : fP hk hu * E.a * (fP hk hu)⁻¹ = E.a ^ 0 * E.b ^ 1 := by
    change fP hk hu * aP u * (fP hk hu)⁻¹ = aP u ^ 0 * bP ^ 1
    rw [fP_conj_aP hk hu]
    simp
  have hf₂ : fP hk hu * E.b * (fP hk hu)⁻¹ = E.a ^ 2 * E.b ^ 0 := by
    change fP hk hu * bP * (fP hk hu)⁻¹ = aP u ^ 2 * bP ^ 0
    rw [fP_conj_bP hk hu, sq_eq_inv_of_pow_three ha3]
    simp
  have hg₁ : (fP hk hu)⁻¹ * jP hk hu * E.a * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ =
      E.a ^ 1 * E.b ^ 1 := by
    change (fP hk hu)⁻¹ * jP hk hu * aP u * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ = aP u ^ 1 * bP ^ 1
    rw [fP_inv_jP_conj_aP hk hu]
    simp
  have hg₂ : (fP hk hu)⁻¹ * jP hk hu * E.b * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ =
      E.a ^ 1 * E.b ^ 2 := by
    change (fP hk hu)⁻¹ * jP hk hu * bP * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ = aP u ^ 1 * bP ^ 2
    rw [fP_inv_jP_conj_bP hk hu, pow_one]
  have hf := E.mem_normalizer_of_conj 0 2 1 0 hf₁ hf₂
  have hg := E.mem_normalizer_of_conj 1 1 1 2 hg₁ hg₂
  have hρf := E.rhoE_apply_of_conj hf 0 2 1 0 hf₁ hf₂
  have hρg := E.rhoE_apply_of_conj hg 1 1 1 2 hg₁ hg₂
  refine ⟨Subgroup.closure (Set.range E.vec), IsPGroup.of_card E.card_range,
    Subgroup.isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact E.vec_comm i j),
    fP hk hu, hf, (fP hk hu)⁻¹ * jP hk hu, hg, ?_⟩
  rintro g (rfl | rfl | rfl)
  · exact conj_pow_of_rhoE E ⟨_, hf⟩ hρf (by decide) (by decide)
  · exact conj_pow_of_rhoE E ⟨_, hg⟩ hρg (by decide) (by decide)
  · have hρ : ((E.rhoE (⟨_, hf⟩ * ⟨_, hg⟩) : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        ((E.rhoE ⟨_, hf⟩ : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
          ((E.rhoE ⟨_, hg⟩ : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      rw [map_mul, Units.val_mul]
    rw [hρf, hρg] at hρ
    exact conj_pow_of_rhoE E _ hρ (by decide) (by decide)

end ThreeLocal

private theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem lThreeFourTwoLocal_of {K : Type} [Group K] (hK : CFSG.AGLEmbedding.IsLinThreeFour K) :
    LThreeFourTwoLocal K := by
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  exact twoLocal_map e.symm (twoLocal_projectiveSL card_galoisField_two_two)

theorem lThreeFourThreeLocal_of {K : Type} [Group K]
    (hK : CFSG.AGLEmbedding.IsLinThreeFour K) : LThreeFourThreeLocal K := by
  obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  exact threeLocal_map e.symm (threeLocal_projectiveSL card_galoisField_two_two)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
