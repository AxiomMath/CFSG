module

public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LocalAnalysis.ComponentInitial

theorem card_cube_SL23 : Nat.card {y : SL23 // y ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide

section SLThree

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_one_or_eq_neg_one (hK : Nat.card K = 3) (c : K) :
    c = 0 ∨ c = 1 ∨ c = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : (1 : K) ≠ -1 := fun h => one_ne_zero (by linear_combination three_eq_zero hK - h)
  have hcard : ({0, 1, -1} : Finset K).card = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Finset.card_eq_three.2 ⟨0, 1, -1, zero_ne_one, by simp, h1, rfl⟩
  have h := (Finset.eq_univ_of_card _ hcard) ▸ Finset.mem_univ c
  simpa using h

theorem closure_upper_lower_one_eq_top (hK : Nat.card K = 3) :
    Subgroup.closure ({sl2Upper K 1, sl2Lower K 1} : Set (Matrix.SpecialLinearGroup (Fin 2) K)) =
      ⊤ := by
  set C := Subgroup.closure ({sl2Upper K 1, sl2Lower K 1} :
    Set (Matrix.SpecialLinearGroup (Fin 2) K))
  rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
  have key : ∀ f : K → Matrix.SpecialLinearGroup (Fin 2) K, (∀ a b, f a * f b = f (a + b)) →
      f 0 = 1 → f 1 ∈ C → ∀ c, f c ∈ C := by
    intro f hf h0 h1 c
    rcases eq_zero_or_eq_one_or_eq_neg_one hK c with rfl | rfl | rfl
    · rw [h0]
      exact one_mem _
    · exact h1
    · have e : f (-1) = (f 1)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [hf, neg_add_cancel, h0])
      rw [e]
      exact inv_mem h1
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact key _ sl2Upper_mul sl2Upper_zero (Subgroup.subset_closure (Or.inl rfl)) c
  · exact key _ sl2Lower_mul sl2Lower_zero (Subgroup.subset_closure (Or.inr rfl)) c

theorem map_mem_centralizer_of_isQuasisimple {G S : Type*} [Group G] [Group S] [Finite S]
    (hS : CFSG.IsQuasisimple S) (hZ : Nat.card (Subgroup.center S) * 81 < Nat.card S)
    (hK : Nat.card K = 3) {L : Subgroup G} (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (ψ : S →* G) (hψ : ∀ s, ψ s ∈ Subgroup.normalizer (L : Set G)) (s : S) :
    ψ s ∈ Subgroup.centralizer (L : Set G) := by
  classical
  set N := (Subgroup.centralizer (L : Set G)).comap ψ with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hn ⊢
    intro l hl
    have hl' : (ψ g)⁻¹ * l * ψ g ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.1 (hψ g⁻¹) l).1 hl
      simpa [map_inv] using h
    have h := hn _ hl'
    simp only [map_mul, map_inv]
    calc l * (ψ g * ψ n * (ψ g)⁻¹) = ψ g * (((ψ g)⁻¹ * l * ψ g) * ψ n) * (ψ g)⁻¹ := by group
      _ = ψ g * (ψ n * ((ψ g)⁻¹ * l * ψ g)) * (ψ g)⁻¹ := by rw [h]
      _ = ψ g * ψ n * (ψ g)⁻¹ * l := by group
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hS hNn with htop | hcen
  · have h : s ∈ N := htop ▸ Subgroup.mem_top s
    exact h
  exfalso
  set a : L := eL.symm (sl2Upper K 1) with ha
  set b : L := eL.symm (sl2Lower K 1) with hb
  have hcl : Subgroup.closure ({a, b} : Set L) = ⊤ := by
    have h := congrArg (Subgroup.map eL.symm.toMonoidHom) (closure_upper_lower_one_eq_top hK)
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ eL.symm.surjective,
      Set.image_pair] at h
    exact h
  have hgen : ∀ g : G, g * a = a * g → g * b = b * g →
      g ∈ Subgroup.centralizer (L : Set G) := by
    intro g hga hgb
    have hle : Subgroup.closure ({a, b} : Set L) ≤
        (Subgroup.centralizer ({g} : Set G)).subgroupOf L := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl) <;>
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      · exact hga.symm
      · exact hgb.symm
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hle (hcl ▸ Subgroup.mem_top (⟨l, hl⟩ : L))
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  have hE : Nat.card {y : L // y ^ 3 = 1} = 9 := by
    rw [← card_cube_SL23]
    refine Nat.card_congr (Equiv.subtypeEquiv (eL.trans (slEquivSL23 hK)).toEquiv fun y => ?_)
    rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow,
      MulEquivClass.map_eq_one_iff]
  have hconj : ∀ (t : S) (y : L), ψ t * y * (ψ t)⁻¹ ∈ L := fun t y =>
    (Subgroup.mem_normalizer_iff.1 (hψ t) y).1 y.2
  have hcube : ∀ (t : S) (y : L), y ^ 3 = 1 →
      (⟨ψ t * y * (ψ t)⁻¹, hconj t y⟩ : L) ^ 3 = 1 := by
    intro t y hy
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, conj_pow]
    have hy' : (y : G) ^ 3 = 1 := by rw [← SubgroupClass.coe_pow, hy]; rfl
    rw [hy', mul_one, mul_inv_cancel]
    rfl
  have hu3 : ∀ y : Matrix.SpecialLinearGroup (Fin 2) K, y = sl2Upper K 1 ∨ y = sl2Lower K 1 →
      y ^ 3 = 1 := by
    have h3 : (1 : K) + (1 + 1) = 0 := by linear_combination three_eq_zero hK
    rintro y (rfl | rfl)
    · rw [pow_three, sl2Upper_mul, sl2Upper_mul, h3, sl2Upper_zero]
    · rw [pow_three, sl2Lower_mul, sl2Lower_mul, h3, sl2Lower_zero]
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hu3 _ (Or.inl rfl), map_one]
  have hb3 : b ^ 3 = 1 := by rw [hb, ← map_pow, hu3 _ (Or.inr rfl), map_one]
  let F : S → {y : L // y ^ 3 = 1} × {y : L // y ^ 3 = 1} := fun t =>
    (⟨⟨ψ t * a * (ψ t)⁻¹, hconj t a⟩, hcube t a ha3⟩,
      ⟨⟨ψ t * b * (ψ t)⁻¹, hconj t b⟩, hcube t b hb3⟩)
  have hconj_eq : ∀ (t t' : S) (y : G), ψ t * y * (ψ t)⁻¹ = ψ t' * y * (ψ t')⁻¹ ↔
      ((ψ t)⁻¹ * ψ t') * y = y * ((ψ t)⁻¹ * ψ t') := by
    intro t t' y
    constructor
    · intro h
      calc (ψ t)⁻¹ * ψ t' * y = (ψ t)⁻¹ * (ψ t' * y * (ψ t')⁻¹) * ψ t' := by group
        _ = (ψ t)⁻¹ * (ψ t * y * (ψ t)⁻¹) * ψ t' := by rw [h]
        _ = y * ((ψ t)⁻¹ * ψ t') := by group
    · intro h
      calc ψ t * y * (ψ t)⁻¹ = ψ t * (y * ((ψ t)⁻¹ * ψ t')) * (ψ t')⁻¹ := by group
        _ = ψ t * ((ψ t)⁻¹ * ψ t' * y) * (ψ t')⁻¹ := by rw [h]
        _ = ψ t' * y * (ψ t')⁻¹ := by group
  have hFN : ∀ t t' : S, F t = F t' ↔ t⁻¹ * t' ∈ N := by
    intro t t'
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq]
    rw [hconj_eq, hconj_eq, hN, Subgroup.mem_comap, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      exact hgen _ h1 h2
    · intro h
      rw [Subgroup.mem_centralizer_iff] at h
      exact ⟨(h a a.2).symm, (h b b.2).symm⟩
  let F' : S ⧸ N → {y : L // y ^ 3 = 1} × {y : L // y ^ 3 = 1} :=
    Quotient.lift F fun t t' h => (hFN t t').2 (QuotientGroup.leftRel_apply.1 h)
  have hF' : Function.Injective F' := by
    intro q q'
    induction q using QuotientGroup.induction_on with | H t => ?_
    induction q' using QuotientGroup.induction_on with | H t' => ?_
    intro h
    exact QuotientGroup.eq.2 ((hFN t t').1 h)
  have : Finite L := Finite.of_equiv _ eL.symm.toEquiv
  have h1 := Nat.card_le_card_of_injective F' hF'
  rw [Nat.card_prod, hE] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have h3 := Subgroup.card_le_of_le hcen
  have h4 := Nat.mul_le_mul h1 h3
  omega

end SLThree

section Commute

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

theorem one_add_smul_mul_one_add_smul (c d : k) (E F : A) :
    (1 + c • E) * (1 + d • F) = 1 + c • E + d • F + (c * d) • (E * F) := by
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm]
  abel

theorem commute_of_forall_commute_one_add_smul_mul (θ : k →+* k) (h2 : (2 : k) ≠ 0) {ω : k}
    (hω : θ ω ≠ ω) {X E F : A} (h : ∀ c : k, Commute X ((1 + c • E) * (1 + θ c • F))) :
    Commute X E ∧ Commute X F := by
  set D : A →ₗ[k] A := LinearMap.mulLeft k X - LinearMap.mulRight k X with hD
  have hDc : ∀ Y : A, Commute X Y ↔ D Y = 0 := fun Y => by
    rw [hD, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, sub_eq_zero]
    rfl
  have key : ∀ c : k, c • D E + θ c • D F + (c * θ c) • D (E * F) = 0 := by
    intro c
    have h' := (hDc _).1 (h c)
    rw [one_add_smul_mul_one_add_smul, map_add, map_add, map_add, map_smul, map_smul, map_smul,
      (hDc 1).1 (Commute.one_right X), zero_add] at h'
    exact h'
  have hneg : ∀ c : k, c • D E + θ c • D F = 0 := by
    intro c
    have h1 := key c
    have h2' := key (-c)
    rw [map_neg, neg_mul, mul_neg, neg_neg, neg_smul, neg_smul] at h2'
    have h3 : (2 : k) • (c • D E + θ c • D F) = 0 := by
      rw [two_smul]
      calc c • D E + θ c • D F + (c • D E + θ c • D F) =
          (c • D E + θ c • D F + (c * θ c) • D (E * F)) -
            (-(c • D E) + -(θ c • D F) + (c * θ c) • D (E * F)) := by abel
        _ = 0 := by rw [h1, h2', sub_zero]
    rcases smul_eq_zero.1 h3 with h | h
    · exact absurd h h2
    · exact h
  have h1 := hneg 1
  rw [map_one, one_smul, one_smul] at h1
  have hω' := hneg ω
  have hF : D F = -D E := eq_neg_of_add_eq_zero_right h1
  rw [hF, smul_neg, ← sub_eq_add_neg, ← sub_smul] at hω'
  have hE : D E = 0 := by
    rcases smul_eq_zero.1 hω' with h | h
    · exact absurd (sub_eq_zero.1 h).symm hω
    · exact h
  refine ⟨(hDc E).2 hE, (hDc F).2 ?_⟩
  rw [hF, hE, neg_zero]

end Commute

end CFSG.LieType.HighestRoot
