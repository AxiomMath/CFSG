module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry

namespace EvenCatalog

section Transvection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}

theorem isometryGroup_ext {g h : isometryGroup B}
    (H : ∀ x, (g : V ≃ₗ[K] V) x = (h : V ≃ₗ[K] V) x) : g = h :=
  Subtype.ext (LinearEquiv.ext H)

theorem isometryGroup_mul_apply (g h : isometryGroup B) (x : V) :
    ((g * h : isometryGroup B) : V ≃ₗ[K] V) x = (g : V ≃ₗ[K] V) ((h : V ≃ₗ[K] V) x) :=
  rfl

theorem isometryGroup_one_apply (x : V) : ((1 : isometryGroup B) : V ≃ₗ[K] V) x = x :=
  rfl

theorem isometryGroup_apply_apply (g : isometryGroup B) (x y : V) :
    B ((g : V ≃ₗ[K] V) x) ((g : V ≃ₗ[K] V) y) = B x y :=
  (mem_isometryGroup_iff B g).mp g.2 x y

theorem flip_apply_eq (a x : V) : B.flip a x = B x a :=
  rfl

theorem flip_apply_self_eq_zero (hB : B.IsAlt) (a : V) : B.flip a a = 0 :=
  hB.self_eq_zero a

@[expose] def binaryTransvection (hB : B.IsAlt) (a : V) : isometryGroup B :=
  ⟨LinearEquiv.transvection (f := B.flip a) (v := a) (flip_apply_self_eq_zero hB a), by
    rw [mem_isometryGroup_iff]
    intro x y
    simp only [LinearEquiv.transvection.apply, flip_apply_eq, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero a]
    rw [← hB.neg_eq y a]
    ring⟩

theorem binaryTransvection_apply (hB : B.IsAlt) (a x : V) :
    ((binaryTransvection hB a : isometryGroup B) : V ≃ₗ[K] V) x = x + B x a • a :=
  rfl

theorem mul_binaryTransvection (hB : B.IsAlt) (g : isometryGroup B) (a : V) :
    g * binaryTransvection hB a = binaryTransvection hB ((g : V ≃ₗ[K] V) a) * g :=
  isometryGroup_ext fun x => by
    rw [isometryGroup_mul_apply, isometryGroup_mul_apply, binaryTransvection_apply,
      binaryTransvection_apply, map_add, map_smul, isometryGroup_apply_apply]

theorem conj_binaryTransvection (hB : B.IsAlt) (g : isometryGroup B) (a : V) :
    g * binaryTransvection hB a * g⁻¹ = binaryTransvection hB ((g : V ≃ₗ[K] V) a) := by
  rw [mul_binaryTransvection, mul_inv_cancel_right]

theorem binaryTransvection_commute (hB : B.IsAlt) {a b : V} (hab : B a b = 0) :
    binaryTransvection hB a * binaryTransvection hB b =
      binaryTransvection hB b * binaryTransvection hB a :=
  isometryGroup_ext fun x => by
    have hba : B b a = 0 := by rw [← hB.neg_eq a b, hab, neg_zero]
    rw [isometryGroup_mul_apply, isometryGroup_mul_apply, binaryTransvection_apply,
      binaryTransvection_apply, binaryTransvection_apply, binaryTransvection_apply]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab,
      hba, mul_zero, add_zero]
    abel

theorem eq_of_binaryTransvection_eq (hB : B.IsAlt) (hK : ∀ k : K, k = 0 ∨ k = 1)
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0) {a b : V} (ha : a ≠ 0)
    (h : binaryTransvection hB a = binaryTransvection hB b) : a = b := by
  obtain ⟨x, hx⟩ : ∃ x, B x a ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha (hBn a hc)
  have hx1 : B x a = 1 := (hK _).resolve_left hx
  have h' := congrArg (fun g : isometryGroup B => (g : V ≃ₗ[K] V) x) h
  simp only [binaryTransvection_apply, hx1, one_smul, add_right_inj] at h'
  rcases hK (B x b) with h0 | h1
  · rw [h0, zero_smul] at h'
    exact absurd h' ha
  · rwa [h1, one_smul] at h'

variable [CharP K 2]

theorem binaryTransvection_mul_self (hB : B.IsAlt) (a : V) :
    binaryTransvection hB a * binaryTransvection hB a = 1 :=
  isometryGroup_ext fun x => by
    rw [isometryGroup_mul_apply, binaryTransvection_apply, binaryTransvection_apply,
      isometryGroup_one_apply]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero a, mul_zero, add_zero]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem binaryTransvection_inv (hB : B.IsAlt) (a : V) :
    (binaryTransvection hB a)⁻¹ = binaryTransvection hB a :=
  inv_eq_of_mul_eq_one_right (binaryTransvection_mul_self hB a)

theorem eq_bot_of_normal_of_odd_card (hK : ∀ k : K, k = 0 ∨ k = 1) (hB : B.IsAlt)
    (hBn : ∀ a : V, (∀ x, B x a = 0) → a = 0)
    (hperp : ∀ a b : V, ∃ c : V, c ≠ 0 ∧ B a c = 0 ∧ B b c = 0)
    {Q : Subgroup (isometryGroup B)} (hQ : Q.Normal) (hodd : Odd (Nat.card Q)) : Q = ⊥ := by
  set τ := binaryTransvection hB
  have hnoinv : ∀ w ∈ Q, w * w = 1 → w = 1 := by
    intro w hw hww
    by_contra hw1
    have h2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
    have h3 := Subgroup.orderOf_dvd_natCard Q hw
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  have hpair : ∀ a b : V, a ≠ 0 → a ≠ b → B a b = 0 → τ b * τ a ∈ Q → False := by
    intro a b ha hab hBab hmem
    have hsq : τ b * τ a * (τ b * τ a) = 1 := by
      calc τ b * τ a * (τ b * τ a) = τ b * (τ a * τ b) * τ a := by group
        _ = τ b * (τ b * τ a) * τ a := by rw [binaryTransvection_commute hB hBab]
        _ = (τ b * τ b) * (τ a * τ a) := by group
        _ = 1 := by rw [binaryTransvection_mul_self, binaryTransvection_mul_self, one_mul]
    have h1 := hnoinv _ hmem hsq
    have h2 : τ b = τ a := by
      have h3 := eq_inv_of_mul_eq_one_left h1
      rwa [binaryTransvection_inv] at h3
    exact hab (eq_of_binaryTransvection_eq hB hK hBn ha h2.symm)
  rw [eq_bot_iff]
  intro q hq
  rw [Subgroup.mem_bot]
  by_contra hq1
  obtain ⟨a, ha⟩ : ∃ a, (q : V ≃ₗ[K] V) a ≠ a := by
    by_contra h
    push Not at h
    exact hq1 (isometryGroup_ext h)
  set b := (q : V ≃ₗ[K] V) a with hbdef
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (map_zero _)
  have hu : τ b * τ a ∈ Q := by
    have h1 : τ a * q⁻¹ * (τ a)⁻¹ ∈ Q := hQ.conj_mem _ (inv_mem hq) _
    have h2 := mul_mem hq h1
    rwa [show q * (τ a * q⁻¹ * (τ a)⁻¹) = q * τ a * q⁻¹ * (τ a)⁻¹ by group,
      conj_binaryTransvection, binaryTransvection_inv] at h2
  rcases hK (B a b) with hab | hab
  · exact hpair a b ha0 (Ne.symm ha) hab hu
  · obtain ⟨c, hc0, hac, hbc⟩ := hperp a b
    have hbb := hB.self_eq_zero b
    set g := τ (b + c) * τ b with hgdef
    have hga : (g : V ≃ₗ[K] V) a = a + c := by
      rw [hgdef, isometryGroup_mul_apply, binaryTransvection_apply, binaryTransvection_apply, hab,
        one_smul]
      have h1 : B (a + b) (b + c) = 1 := by
        simp only [map_add, LinearMap.add_apply, hab, hac, hbb, hbc, add_zero]
      rw [h1, one_smul, show a + b + (b + c) = a + c + (b + b) by abel, ← two_smul K b,
        CharTwo.two_eq_zero, zero_smul, add_zero]
    have hgb : (g : V ≃ₗ[K] V) b = b := by
      rw [hgdef, isometryGroup_mul_apply, binaryTransvection_apply, binaryTransvection_apply, hbb,
        zero_smul, add_zero]
      have h1 : B b (b + c) = 0 := by rw [map_add, hbb, hbc, add_zero]
      rw [h1, zero_smul, add_zero]
    have hconj : g * (τ b * τ a) * g⁻¹ ∈ Q := hQ.conj_mem _ hu g
    rw [show g * (τ b * τ a) * g⁻¹ = (g * τ b * g⁻¹) * (g * τ a * g⁻¹) by group,
      conj_binaryTransvection, conj_binaryTransvection, hga, hgb] at hconj
    have hw : (τ b * τ (a + c))⁻¹ * (τ b * τ a) ∈ Q := mul_mem (inv_mem hconj) hu
    rw [mul_inv_rev, binaryTransvection_inv, binaryTransvection_inv,
      show τ (a + c) * τ b * (τ b * τ a) = τ (a + c) * (τ b * τ b) * τ a by group,
      binaryTransvection_mul_self, mul_one] at hw
    refine hpair a (a + c) ha0 (fun h => hc0 ?_) ?_ hw
    · have h1 : a + c = a + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h1
    · rw [map_add, hB.self_eq_zero a, hac, add_zero]

end Transvection

theorem eq_zero_or_eq_one_of_card_eq_two {K : Type*} [Field K] (hK : Nat.card K = 2) (k : K) :
    k = 0 ∨ k = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have huniv : ({0, 1} : Finset K) = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK])
  have hk : k ∈ ({0, 1} : Finset K) := huniv ▸ Finset.mem_univ k
  simpa using hk

theorem oddCore_statedSp_eq_bot_of_card_eq_two {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    (hK : Nat.card K = 2) : CFSG.oddCore (StatedSp r K) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : CharP K 2 := finite_field_prime_power_characteristic (k := 1) Nat.prime_two le_rfl
    (by rw [hK, pow_one])
  set B := pairedSympForm K r
  have hB : B.IsAlt := SymplecticFlag.pairedSympForm_isAlt
  have hBn : ∀ a, (∀ x, B x a = 0) → a = 0 := fun a h =>
    SymplecticFlag.pairedSympForm_nondegenerate.2 a h
  have hperp : ∀ a b : Fin r ⊕ Fin r → K, ∃ c, c ≠ 0 ∧ B a c = 0 ∧ B b c = 0 := by
    intro a b
    have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := (B a).prod (B b)) (by
      rw [Module.finrank_prod, Module.finrank_self, SymplecticFlag.finrank_standard]
      omega)
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
    rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hc
    exact ⟨c, hc0, hc.1, hc.2⟩
  let e := CatalogueBSymplecticB.statedSpIsometryEquiv (r := r) (K := K)
  have : Finite (isometryGroup B) := Finite.of_equiv _ e.toEquiv
  have hQ := eq_bot_of_normal_of_odd_card (eq_zero_or_eq_one_of_card_eq_two hK) hB hBn hperp
    (Q := CFSG.oddCore (isometryGroup B)) inferInstance odd_card_oddCore
  exact oddCore_eq_bot_of_mulEquiv e.symm hQ

end EvenCatalog

open EvenCatalog

theorem even_symplectic_odd_core_including_field_two_rank_two {r f : ℕ} (hr : 2 ≤ r)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) :
    CFSG.oddCore (StatedSp r K) = ⊥ ∧ CFSG.oddCore (StatedProj (StatedSp r K)) = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  have hbij := (UnitaryHigher.even_symplectic_semilinear_normal_form (r := r) hf hK).1
  let e : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
  rcases Nat.lt_or_ge f 2 with hf2 | hf2
  ·
    have hK2 : Nat.card K = 2 := by rw [hK, show f = 1 by omega, pow_one]
    have hS := oddCore_statedSp_eq_bot_of_card_eq_two hr hK2
    exact ⟨hS, oddCore_eq_bot_of_mulEquiv e hS⟩
  ·
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have : IsSimpleGroup (StatedProj (StatedSp r K)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega)
        (Or.inl (Or.inr h4))
    have hcard := (SymplecticFlag.symplectic_higher_order_and_Sylow 2 (2 ^ f) hK
      (r := r) (by omega)).1
    have heven : Even (Nat.card (StatedProj (StatedSp r K))) := by
      rw [← Nat.card_congr e.toEquiv, hcard]
      refine Even.mul_right ?_ _
      rw [Nat.even_pow]
      refine ⟨?_, by positivity⟩
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    have hP := oddCore_eq_bot_of_isSimpleGroup heven
    exact ⟨oddCore_eq_bot_of_mulEquiv e.symm hP, hP⟩

end CFSG.ComponentClassification.UnbalancedCatalog
