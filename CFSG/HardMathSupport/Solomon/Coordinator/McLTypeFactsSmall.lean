module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsBasic
public import CFSG.LargeExtraspecial.S10Model
public import CFSG.CharacterTheory.Burnside
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LargeExtraspecial.S10

theorem mcltf_preserves_part {α : Type*} (S P : Set α) (E : α → α → Prop) (f : α → α)
    (hfS : ∀ x ∈ S, f x ∈ S) (hE : ∀ x ∈ S, ∀ y ∈ S, (E (f x) (f y) ↔ E x y))
    (hEP : ∀ x ∈ S, ∀ y ∈ S, (E x y ↔ (x ∈ P ↔ y ∈ P))) (hf3 : ∀ x, f (f (f x)) = x) :
    ∀ x ∈ S, x ∈ P → f x ∈ P := by
  intro x hxS hxP
  by_contra hfx
  have hswap : ∀ y ∈ S, (f y ∈ P ↔ y ∉ P) := by
    intro y hyS
    have h1 := hEP x hxS y hyS
    have h2 := hEP (f x) (hfS x hxS) (f y) (hfS y hyS)
    have h3 := hE x hxS y hyS
    by_cases hy : y ∈ P <;> by_cases hfy : f y ∈ P <;> simp_all
  have h1 : f (f x) ∈ P := (hswap (f x) (hfS x hxS)).mpr hfx
  have h2 : f (f (f x)) ∉ P :=
    fun h => ((hswap (f (f x)) (hfS _ (hfS x hxS))).mp h) h1
  exact h2 ((hf3 x).symm ▸ hxP)

section SLTwoTwo

local notation "SL22" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

@[expose] def mcltf_s₁ : SL22 := ⟨!![0, 1; 1, 0], by decide⟩

@[expose] def mcltf_s₂ : SL22 := ⟨!![1, 1; 0, 1], by decide⟩

theorem mcltf_card_SL22 : Nat.card SL22 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem mcltf_SL22_inv_cases : ∀ x : SL22, x * x = 1 → x ≠ 1 →
    x = mcltf_s₁ ∨ x = mcltf_s₂ ∨ x = mcltf_s₁ * mcltf_s₂ * mcltf_s₁ := by
  decide +kernel

theorem mcltf_SL22_conj : ∀ x y : SL22, x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → x ≠ y →
    ∃ g : SL22, g * mcltf_s₁ = x * g ∧ g * mcltf_s₂ = y * g := by
  decide +kernel

theorem mcltf_SL22_cent : ∀ z : SL22, (∀ x : SL22, x * x = 1 → x ≠ 1 → z * x = x * z) → z = 1 := by
  decide +kernel

theorem mcltf_isSolvable_SL22 : Group.IsSolvable SL22 := by
  have hcard : Fintype.card SL22 = 2 ^ 1 * 3 ^ 1 := by decide +kernel
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) hcard

theorem mcltf_eq_conj_of_mul_eq {G : Type*} [Group G] {g a b : G} (h : g * a = b * g) :
    b = g * a * g⁻¹ := by
  rw [h, mul_inv_cancel_right]

theorem mcltf_SL22_aut (φ : MulAut SL22) : ∃ g : SL22, φ = MulAut.conj g := by
  have hinv : ∀ x : SL22, x * x = 1 → x ≠ 1 → φ x * φ x = 1 ∧ φ x ≠ 1 := fun x h1 h2 =>
    ⟨by rw [← map_mul, h1, map_one], fun h => h2 (φ.injective (by rw [h, map_one]))⟩
  have h₁ : mcltf_s₁ * mcltf_s₁ = 1 := by decide +kernel
  have h₂ : mcltf_s₂ * mcltf_s₂ = 1 := by decide +kernel
  have h₁' : mcltf_s₁ ≠ 1 := by decide +kernel
  have h₂' : mcltf_s₂ ≠ 1 := by decide +kernel
  have h₁₂ : mcltf_s₁ ≠ mcltf_s₂ := by decide +kernel
  obtain ⟨g, hg₁, hg₂⟩ := mcltf_SL22_conj (φ mcltf_s₁) (φ mcltf_s₂) (hinv _ h₁ h₁').1
    (hinv _ h₁ h₁').2 (hinv _ h₂ h₂').1 (hinv _ h₂ h₂').2 (φ.injective.ne h₁₂)
  refine ⟨g, mcltf_eq_conj_of_eqOn {x | x * x = 1 ∧ x ≠ 1} ?_ ?_ φ g ?_⟩
  · rintro k x ⟨hx1, hx2⟩
    refine ⟨by rw [show k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ by group, hx1]; group,
      fun h => hx2 ?_⟩
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · exact fun z hz => mcltf_SL22_cent z fun x h1 h2 => hz x ⟨h1, h2⟩
  · rintro x ⟨hx1, hx2⟩
    have e₁ := mcltf_eq_conj_of_mul_eq hg₁
    have e₂ := mcltf_eq_conj_of_mul_eq hg₂
    rcases mcltf_SL22_inv_cases x hx1 hx2 with rfl | rfl | rfl
    · exact e₁
    · exact e₂
    · rw [map_mul, map_mul, e₁, e₂]
      group

theorem mcltf_facts_SL22 : mcltf_Facts SL22 := by
  refine mcltf_facts_of_solvable mcltf_isSolvable_SL22 (fun φ _ => mcltf_SL22_aut φ) ?_ ?_
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    exact Subgroup.mem_bot.mpr (mcltf_SL22_cent z fun x _ _ => (hz x).symm)
  · intro q hq hqd
    rw [mcltf_card_SL22, show (6 : ℕ) = 2 * 3 by norm_num] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)

end SLTwoTwo

section Model

theorem mcltf_mult2_cases : ∀ k : Multiplicative (ZMod 2), k = 1 ∨ k = Multiplicative.ofAdd 1 := by
  decide

theorem mcltf_gen_mul_gen :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by
  decide

@[expose] def mcltf_hom2 {H : Type*} [Group H] (h : H) (hh : h * h = 1) :
    Multiplicative (ZMod 2) →* H where
  toFun k := if k = 1 then 1 else h
  map_one' := by simp
  map_mul' a b := by
    rcases mcltf_mult2_cases a with rfl | rfl <;> rcases mcltf_mult2_cases b with rfl | rfl <;>
      simp [mcltf_gen_mul_gen, hh]

theorem mcltf_hom2_gen {H : Type*} [Group H] (h : H) (hh : h * h = 1) :
    mcltf_hom2 h hh (Multiplicative.ofAdd 1) = h := by
  simp [mcltf_hom2]

theorem mcltf_prodComm_mul_self :
    (MulEquiv.prodComm : MulAut Gm) * MulEquiv.prodComm = 1 := by
  ext x <;> rfl

@[expose] def mcltf_swapHom : Multiplicative (ZMod 2) →* MulAut Gm :=
  mcltf_hom2 MulEquiv.prodComm mcltf_prodComm_mul_self

abbrev mcltf_OPlus4 : Type := Gm ⋊[mcltf_swapHom] Multiplicative (ZMod 2)

instance : Fintype mcltf_OPlus4 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

@[expose, instance_reducible] def mcltf_OPlus4DecEq : DecidableEq mcltf_OPlus4 :=
  SemidirectProduct.equivProd.decidableEq

attribute [local instance high] mcltf_OPlus4DecEq

@[expose] def mcltf_IsA (x : mcltf_OPlus4) : Prop :=
  x.right = 1 ∧ x.left.2 = 1 ∧ x.left.1 ≠ 1 ∧ x.left.1 * x.left.1 = 1

@[expose] def mcltf_IsB (x : mcltf_OPlus4) : Prop :=
  x.right = 1 ∧ x.left.1 = 1 ∧ x.left.2 ≠ 1 ∧ x.left.2 * x.left.2 = 1

@[expose] def mcltf_IsT₁ (x : mcltf_OPlus4) : Prop := mcltf_IsA x ∨ mcltf_IsB x

@[expose] def mcltf_IsT₂ (x : mcltf_OPlus4) : Prop := x.right ≠ 1 ∧ x * x = 1

@[expose] def mcltf_IsT (x : mcltf_OPlus4) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ ∃ y : mcltf_OPlus4, y * y * y = 1 ∧ y ≠ 1 ∧ x * y = y * x

instance : DecidablePred mcltf_IsA := fun x => by unfold mcltf_IsA; infer_instance
instance : DecidablePred mcltf_IsB := fun x => by unfold mcltf_IsB; infer_instance
instance : DecidablePred mcltf_IsT₁ := fun x => by unfold mcltf_IsT₁; infer_instance
instance : DecidablePred mcltf_IsT₂ := fun x => by unfold mcltf_IsT₂; infer_instance
instance : DecidablePred mcltf_IsT := fun x => by unfold mcltf_IsT; infer_instance

@[expose] def mcltf_pair (s t : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : mcltf_OPlus4 :=
  ⟨(s, t), 1⟩

theorem mcltf_card_OPlus4 : Nat.card mcltf_OPlus4 = 72 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem mcltf_IsT_iff : ∀ x : mcltf_OPlus4, mcltf_IsT x ↔ mcltf_IsT₁ x ∨ mcltf_IsT₂ x := by
  decide +kernel

theorem mcltf_order_four_iff : ∀ x y : mcltf_OPlus4, mcltf_IsT x → mcltf_IsT y →
    (¬ ((x * y) * (x * y) * (x * y) * (x * y) = 1 ∧ (x * y) * (x * y) ≠ 1) ↔
      (mcltf_IsT₁ x ↔ mcltf_IsT₁ y)) := by
  decide +kernel

theorem mcltf_commute_iff : ∀ x y : mcltf_OPlus4, mcltf_IsT₁ x → mcltf_IsT₁ y →
    ((x = y ∨ x * y ≠ y * x) ↔ (mcltf_IsA x ↔ mcltf_IsA y)) := by
  decide +kernel

theorem mcltf_IsA_iff_not_IsB : ∀ x : mcltf_OPlus4, mcltf_IsT₁ x →
    (mcltf_IsA x ↔ ¬ mcltf_IsB x) := by
  decide +kernel

theorem mcltf_IsA_eq : ∀ x : mcltf_OPlus4, mcltf_IsA x → x = mcltf_pair x.left.1 1 := by
  decide +kernel

theorem mcltf_IsB_eq : ∀ x : mcltf_OPlus4, mcltf_IsB x → x = mcltf_pair 1 x.left.2 := by
  decide +kernel

theorem mcltf_IsA_cases : ∀ x : mcltf_OPlus4, mcltf_IsA x →
    x = mcltf_pair mcltf_s₁ 1 ∨ x = mcltf_pair mcltf_s₂ 1 ∨
      x = mcltf_pair mcltf_s₁ 1 * mcltf_pair mcltf_s₂ 1 * mcltf_pair mcltf_s₁ 1 := by
  decide +kernel

theorem mcltf_IsB_cases : ∀ x : mcltf_OPlus4, mcltf_IsB x →
    x = mcltf_pair 1 mcltf_s₁ ∨ x = mcltf_pair 1 mcltf_s₂ ∨
      x = mcltf_pair 1 mcltf_s₁ * mcltf_pair 1 mcltf_s₂ * mcltf_pair 1 mcltf_s₁ := by
  decide +kernel

theorem mcltf_IsA_pair : mcltf_IsA (mcltf_pair mcltf_s₁ 1) ∧ mcltf_IsA (mcltf_pair mcltf_s₂ 1) ∧
    mcltf_IsB (mcltf_pair 1 mcltf_s₁) ∧ mcltf_IsB (mcltf_pair 1 mcltf_s₂) := by
  decide +kernel

theorem mcltf_OPlus4_conj : ∀ s t u v : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    s * s = 1 → s ≠ 1 → t * t = 1 → t ≠ 1 → s ≠ t →
    u * u = 1 → u ≠ 1 → v * v = 1 → v ≠ 1 → u ≠ v →
    ∃ g : mcltf_OPlus4, g * mcltf_pair mcltf_s₁ 1 = mcltf_pair s 1 * g ∧
      g * mcltf_pair mcltf_s₂ 1 = mcltf_pair t 1 * g ∧
      g * mcltf_pair 1 mcltf_s₁ = mcltf_pair 1 u * g ∧
      g * mcltf_pair 1 mcltf_s₂ = mcltf_pair 1 v * g := by
  decide +kernel

theorem mcltf_IsT₁_conj : ∀ g x : mcltf_OPlus4, mcltf_IsT₁ x →
    ∃ y : mcltf_OPlus4, mcltf_IsT₁ y ∧ g * x = y * g := by
  decide +kernel

theorem mcltf_IsT₁_cent : ∀ z : mcltf_OPlus4, (∀ x : mcltf_OPlus4, mcltf_IsT₁ x → z * x = x * z) →
    z = 1 := by
  decide +kernel

theorem mcltf_OPlus4_aut_halves (φ : MulAut mcltf_OPlus4) (hφ : φ ^ 3 = 1) :
    (∀ x, mcltf_IsA x → mcltf_IsA (φ x)) ∧ (∀ x, mcltf_IsB x → mcltf_IsB (φ x)) := by
  have hf3 : ∀ x, φ (φ (φ x)) = x := fun x => by
    have := congrArg (fun ψ : MulAut mcltf_OPlus4 => ψ x) hφ
    simpa [pow_succ, MulAut.mul_apply] using this
  have hne : ∀ x : mcltf_OPlus4, x ≠ 1 → φ x ≠ 1 := fun x hx h =>
    hx (φ.injective (by rw [h, map_one]))
  have hT : ∀ x, mcltf_IsT x → mcltf_IsT (φ x) := by
    rintro x ⟨h1, h2, y, hy1, hy2, hxy⟩
    exact ⟨by rw [← map_mul, h1, map_one], hne x h2, φ y,
      by rw [← map_mul, ← map_mul, hy1, map_one], hne y hy2, by rw [← map_mul, ← map_mul, hxy]⟩
  have hT₁ : ∀ x, mcltf_IsT₁ x → mcltf_IsT₁ (φ x) := by
    have key := mcltf_preserves_part {x | mcltf_IsT x} {x | mcltf_IsT₁ x}
      (fun x y => ¬ ((x * y) * (x * y) * (x * y) * (x * y) = 1 ∧ (x * y) * (x * y) ≠ 1)) φ
      (fun x hx => hT x hx) (fun x _ y _ => by
        simp only [← map_mul, ne_eq, MulEquiv.map_eq_one_iff])
      (fun x hx y hy => mcltf_order_four_iff x y hx hy) hf3
    exact fun x hx => key x ((mcltf_IsT_iff x).mpr (Or.inl hx)) hx
  have hE : ∀ x ∈ {x | mcltf_IsT₁ x}, ∀ y ∈ {x | mcltf_IsT₁ x},
      ((φ x = φ y ∨ φ x * φ y ≠ φ y * φ x) ↔ (x = y ∨ x * y ≠ y * x)) := fun x _ y _ => by
    rw [φ.injective.eq_iff, ← map_mul, ← map_mul, φ.injective.ne_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact mcltf_preserves_part {x | mcltf_IsT₁ x} {x | mcltf_IsA x}
      (fun x y => x = y ∨ x * y ≠ y * x) φ (fun x hx => hT₁ x hx) hE
      (fun x hx y hy => mcltf_commute_iff x y hx hy) hf3 x (Or.inl hx) hx
  · exact mcltf_preserves_part {x | mcltf_IsT₁ x} {x | mcltf_IsB x}
      (fun x y => x = y ∨ x * y ≠ y * x) φ (fun x hx => hT₁ x hx) hE
      (fun x hx y hy => by
        rw [mcltf_commute_iff x y hx hy, mcltf_IsA_iff_not_IsB x hx, mcltf_IsA_iff_not_IsB y hy]
        exact not_iff_not) hf3 x (Or.inr hx) hx

theorem mcltf_OPlus4_aut (φ : MulAut mcltf_OPlus4) (hφ : φ ^ 3 = 1) :
    ∃ g : mcltf_OPlus4, φ = MulAut.conj g := by
  obtain ⟨hA, hB⟩ := mcltf_OPlus4_aut_halves φ hφ
  obtain ⟨hA₁, hA₂, hB₁, hB₂⟩ := mcltf_IsA_pair
  have ha₁ := hA _ hA₁
  have ha₂ := hA _ hA₂
  have hb₁ := hB _ hB₁
  have hb₂ := hB _ hB₂
  have e₁ := mcltf_IsA_eq _ ha₁
  have e₂ := mcltf_IsA_eq _ ha₂
  have e₃ := mcltf_IsB_eq _ hb₁
  have e₄ := mcltf_IsB_eq _ hb₂
  have hne₁₂ : (φ (mcltf_pair mcltf_s₁ 1)).left.1 ≠ (φ (mcltf_pair mcltf_s₂ 1)).left.1 := by
    intro h
    have : φ (mcltf_pair mcltf_s₁ 1) = φ (mcltf_pair mcltf_s₂ 1) := by rw [e₁, e₂, h]
    exact absurd (φ.injective this) (by decide +kernel)
  have hne₃₄ : (φ (mcltf_pair 1 mcltf_s₁)).left.2 ≠ (φ (mcltf_pair 1 mcltf_s₂)).left.2 := by
    intro h
    have : φ (mcltf_pair 1 mcltf_s₁) = φ (mcltf_pair 1 mcltf_s₂) := by rw [e₃, e₄, h]
    exact absurd (φ.injective this) (by decide +kernel)
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := mcltf_OPlus4_conj _ _ _ _ ha₁.2.2.2 ha₁.2.2.1
    ha₂.2.2.2 ha₂.2.2.1 hne₁₂ hb₁.2.2.2 hb₁.2.2.1 hb₂.2.2.2 hb₂.2.2.1 hne₃₄
  rw [← e₁] at hg₁
  rw [← e₂] at hg₂
  rw [← e₃] at hg₃
  rw [← e₄] at hg₄
  have c₁ := mcltf_eq_conj_of_mul_eq hg₁
  have c₂ := mcltf_eq_conj_of_mul_eq hg₂
  have c₃ := mcltf_eq_conj_of_mul_eq hg₃
  have c₄ := mcltf_eq_conj_of_mul_eq hg₄
  refine ⟨g, mcltf_eq_conj_of_eqOn {x | mcltf_IsT₁ x} ?_ ?_ φ g ?_⟩
  · intro k x hx
    obtain ⟨y, hy, hky⟩ := mcltf_IsT₁_conj k x hx
    rw [show k * x * k⁻¹ = y by rw [hky]; group]
    exact hy
  · exact fun z hz => mcltf_IsT₁_cent z hz
  · rintro x (hx | hx)
    · rcases mcltf_IsA_cases x hx with rfl | rfl | rfl
      · exact c₁
      · exact c₂
      · rw [map_mul, map_mul, c₁, c₂]
        group
    · rcases mcltf_IsB_cases x hx with rfl | rfl | rfl
      · exact c₃
      · exact c₄
      · rw [map_mul, map_mul, c₃, c₄]
        group

theorem mcltf_facts_OPlus4 : mcltf_Facts mcltf_OPlus4 := by
  have hsol : Group.IsSolvable mcltf_OPlus4 := by
    have hcard : Fintype.card mcltf_OPlus4 = 2 ^ 3 * 3 ^ 2 := by decide +kernel
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) hcard
  refine mcltf_facts_of_solvable hsol mcltf_OPlus4_aut ?_ ?_
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    exact Subgroup.mem_bot.mpr (mcltf_IsT₁_cent z fun x _ => (hz x).symm)
  · intro q hq hqd
    rw [mcltf_card_OPlus4, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h))

end Model

section Iso

@[expose] def mcltf_tau : M2 ≃ₗ[ZMod 2] M2 :=
  Matrix.transposeLinearEquiv (Fin 2) (Fin 2) (ZMod 2) (ZMod 2)

theorem mcltf_tau_apply (m : M2) : mcltf_tau m = m.transpose :=
  rfl

theorem mcltf_tau_mem : mcltf_tau ∈ TauCeti.QuadraticMap.orthogonalGroup q₀ :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun m => by
    rw [q₀_apply, q₀_apply, mcltf_tau_apply]
    simp only [qf, Matrix.transpose_apply]
    ring

theorem mcltf_tau_mul_tau : mcltf_tau * mcltf_tau = 1 :=
  LinearEquiv.ext fun m => Matrix.transpose_transpose m

@[expose] noncomputable def mcltf_tauHom :
    Multiplicative (ZMod 2) →* TauCeti.QuadraticMap.orthogonalGroup q₀ :=
  mcltf_hom2 ⟨mcltf_tau, mcltf_tau_mem⟩ (Subtype.ext mcltf_tau_mul_tau)

@[expose] noncomputable def mcltf_rhoHom : Gm →* TauCeti.QuadraticMap.orthogonalGroup q₀ :=
  ρ₀.codRestrict _ ρ₀_mem_orthogonalGroup

theorem mcltf_compat (k : Multiplicative (ZMod 2)) :
    mcltf_rhoHom.comp (mcltf_swapHom k).toMonoidHom =
      (MulAut.conj (mcltf_tauHom k)).toMonoidHom.comp mcltf_rhoHom := by
  rcases mcltf_mult2_cases k with rfl | rfl
  · ext γ m
    simp
  · have hinv : (mcltf_tau)⁻¹ = mcltf_tau := inv_eq_of_mul_eq_one_right mcltf_tau_mul_tau
    ext γ m : 3
    simp only [mcltf_swapHom, mcltf_tauHom, mcltf_hom2_gen, mcltf_rhoHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.coe_prodComm, MonoidHom.codRestrict_apply,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, ρ₀_apply,
      hinv, mcltf_tau_apply, act, Prod.fst_swap, Prod.snd_swap, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]

@[expose] noncomputable def mcltf_OPlus4Hom :
    mcltf_OPlus4 →* TauCeti.QuadraticMap.orthogonalGroup q₀ :=
  SemidirectProduct.lift mcltf_rhoHom mcltf_tauHom mcltf_compat

theorem mcltf_act_ne_transpose : ∀ γ : Gm, ∃ m : M2, act γ m ≠ m.transpose := by
  decide +kernel

theorem mcltf_OPlus4Hom_injective : Function.Injective mcltf_OPlus4Hom := by
  rw [injective_iff_map_eq_one]
  rintro ⟨γ, k⟩ h
  change mcltf_rhoHom γ * mcltf_tauHom k = 1 at h
  rcases mcltf_mult2_cases k with rfl | rfl
  · rw [map_one, mul_one] at h
    have hγ : γ = 1 := ρ₀_injective (congrArg Subtype.val (h.trans mcltf_rhoHom.map_one.symm))
    subst hγ
    rfl
  · exfalso
    rw [mcltf_tauHom, mcltf_hom2_gen] at h
    have h' : mcltf_rhoHom γ = ⟨mcltf_tau, mcltf_tau_mem⟩ := by
      have h3 : (⟨mcltf_tau, mcltf_tau_mem⟩ : TauCeti.QuadraticMap.orthogonalGroup q₀) *
          ⟨mcltf_tau, mcltf_tau_mem⟩ = 1 := Subtype.ext mcltf_tau_mul_tau
      calc mcltf_rhoHom γ = mcltf_rhoHom γ * (⟨mcltf_tau, mcltf_tau_mem⟩ *
            ⟨mcltf_tau, mcltf_tau_mem⟩) := by rw [h3, mul_one]
        _ = ⟨mcltf_tau, mcltf_tau_mem⟩ := by rw [← mul_assoc, h, one_mul]
    obtain ⟨m, hm⟩ := mcltf_act_ne_transpose γ
    apply hm
    have := congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup q₀ =>
      (x : M2 ≃ₗ[ZMod 2] M2) m) h'
    simpa [mcltf_rhoHom, mcltf_tau_apply] using this

@[expose] noncomputable def mcltf_OPlus4Equiv :
    mcltf_OPlus4 ≃* TauCeti.QuadraticMap.orthogonalGroup q₀ :=
  MulEquiv.ofBijective mcltf_OPlus4Hom ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨mcltf_OPlus4Hom_injective, by rw [mcltf_card_OPlus4, card_orthogonalGroup_q₀]⟩)

theorem mcltf_facts_orthogonalGroup_q₀ :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup q₀) :=
  mcltf_facts_of_mulEquiv mcltf_OPlus4Equiv.symm mcltf_facts_OPlus4

@[expose] noncomputable def mcltf_plusIsometry :
    (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)).IsometryEquiv q₀ :=
  { plusEquiv with map_app' := q₀_plusEquiv }

theorem mcltf_facts_orthogonalGroup_quadPlus_two :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2))) :=
  mcltf_facts_of_mulEquiv (TauCeti.QuadraticMap.orthogonalGroupCongr mcltf_plusIsometry)
    mcltf_facts_orthogonalGroup_q₀

end Iso

end CFSG.HardMathSupport.Solomon.Coordinator
