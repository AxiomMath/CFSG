module

public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.SectionRank

open CFSG.Open
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem commutatorElement_mul_central_left {a : P} (ha : a ∈ Subgroup.center P) (x y : P) :
    ⁅x * a, y⁆ = ⁅x, y⁆ := by
  have h := (Subgroup.mem_center_iff.1 ha y).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc x * a * y * (x * a)⁻¹ * y⁻¹ = x * (a * y) * a⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * a) * a⁻¹ * x⁻¹ * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_central_right {b : P} (hb : b ∈ Subgroup.center P) (x y : P) :
    ⁅x, y * b⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_central_left hb, commutatorElement_inv]

@[expose] def zmodPowHom {p : ℕ} [NeZero p] (g : P) (hg : g ^ p = 1) :
    Multiplicative (ZMod p) →* P where
  toFun k := g ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    change g ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val = _
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem zmodPowHom_apply {p : ℕ} [NeZero p] (g : P) (hg : g ^ p = 1) (k : Multiplicative (ZMod p)) :
    zmodPowHom g hg k = g ^ (Multiplicative.toAdd k).val := rfl

@[expose] def piToMultiplicative (ι G : Type*) [AddGroup G] :
    (ι → Multiplicative G) →* Multiplicative (ι → G) where
  toFun f := Multiplicative.ofAdd fun i => Multiplicative.toAdd (f i)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem piToMultiplicative_injective (ι G : Type*) [AddGroup G] :
    Function.Injective (piToMultiplicative ι G) := fun f g h => by
  funext i
  have := congrFun (congrArg Multiplicative.toAdd h) i
  exact Multiplicative.toAdd.injective this

theorem piToMultiplicative_surjective (ι G : Type*) [AddGroup G] :
    Function.Surjective (piToMultiplicative ι G) := fun v =>
  ⟨fun i => Multiplicative.ofAdd (Multiplicative.toAdd v i), rfl⟩

variable {p : ℕ} [hp : Fact p.Prime]

theorem three_sign_lines_central_splitting (hp2 : p ≠ 2) (A : Subgroup P) [A.Normal]
    (hAZ : A ≤ Subgroup.center P) (θ : P ⧸ A ≃* Multiplicative (Fin 3 → ZMod p))
    (α β : P ≃* P) (hαA : ∀ a ∈ A, α a = a) (hβA : ∀ a ∈ A, β a = a)
    (hα : ∀ x : P, Multiplicative.toAdd (θ (α x : P ⧸ A)) =
      ![1, -1, -1] * Multiplicative.toAdd (θ (x : P ⧸ A)))
    (hβ : ∀ x : P, Multiplicative.toAdd (θ (β x : P ⧸ A)) =
      ![-1, -1, 1] * Multiplicative.toAdd (θ (x : P ⧸ A))) :
    ∃ E : Subgroup P, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ A ⊔ E = ⊤ ∧ A ⊓ E = ⊥ := by
  have hp' := hp.out
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp'.odd_of_ne_two hp2)
  set τ : P →* Multiplicative (Fin 3 → ZMod p) := θ.toMonoidHom.comp (QuotientGroup.mk' A)
    with hτdef
  have hτ : ∀ x, τ x = θ (x : P ⧸ A) := fun _ => rfl
  have hker : ∀ x, τ x = 1 ↔ x ∈ A := fun x => by
    rw [hτ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hτeq : ∀ x y, τ x = τ y → x⁻¹ * y ∈ A := fun x y h =>
    (hker _).1 (by rw [map_mul, map_inv, h]; exact inv_mul_cancel _)
  have hcen : ∀ a ∈ A, ∀ g : P, Commute a g := fun a ha g =>
    (Subgroup.mem_center_iff.1 (hAZ ha) g).symm
  have hcommA : ∀ x y : P, ⁅x, y⁆ ∈ A := fun x y => by
    rw [← hker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hpA : ∀ x : P, x ^ p ∈ A := fun x => by
    rw [← hker, map_pow]
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, toAdd_one,
      Pi.zero_apply]
  have hc : ∀ x y z : P, Commute ⁅x, y⁆ z := fun x y z => hcen _ (hcommA x y) z
  have hcp : ∀ x y : P, ⁅x, y⁆ ^ p = 1 := fun x y => by
    rw [← commutatorElement_pow_left_of_central hc, commutatorElement_def,
      (hcen _ (hpA x) y).eq]
    group
  set e : Fin 3 → Multiplicative (Fin 3 → ZMod p) := fun i =>
    Multiplicative.ofAdd (Pi.single i 1) with he
  have hτsurj : Function.Surjective τ := fun v => by
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (θ.symm v)
    exact ⟨q, by rw [hτ, hq, MulEquiv.apply_symm_apply]⟩
  choose g hg using fun i => hτsurj (e i)
  have hsign : ∀ (σ : P ≃* P) (s : Fin 3 → ZMod p),
      (∀ x : P, Multiplicative.toAdd (θ (σ x : P ⧸ A)) =
        s * Multiplicative.toAdd (θ (x : P ⧸ A))) → ∀ i,
      (s i = 1 → (g i)⁻¹ * σ (g i) ∈ A) ∧ (s i + 1 = 0 → g i * σ (g i) ∈ A) := by
    intro σ s hσ i
    have h1 : Multiplicative.toAdd (τ (σ (g i))) = Pi.single i (s i) := by
      rw [hτ, hσ, ← hτ, hg i]
      funext j
      by_cases hj : j = i
      · subst hj; simp [he]
      · simp [he, hj]
    refine ⟨fun hs => hτeq _ _ ?_, fun hs => ?_⟩
    · apply Multiplicative.toAdd.injective
      rw [h1, hg i, hs]
      rfl
    · have h2 : τ (g i * σ (g i)) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [map_mul, toAdd_mul, h1, hg i, toAdd_one]
        change (Pi.single i 1 + Pi.single i (s i) : Fin 3 → ZMod p) = 0
        rw [← Pi.single_add, add_comm, hs, Pi.single_zero]
      exact (hker _).1 h2
  have hsep : ∀ (σ : P ≃* P) (hσA : ∀ a ∈ A, σ a = a) (i j : Fin 3),
      (g i)⁻¹ * σ (g i) ∈ A → g j * σ (g j) ∈ A → Commute (g i) (g j) := by
    intro σ hσA i j hi hj
    set a := (g i)⁻¹ * σ (g i)
    set b := g j * σ (g j)
    have hσi : σ (g i) = g i * a := by simp [a]
    have hσj : σ (g j) = (g j)⁻¹ * b := by simp [b]
    have hfix := hσA _ (hcommA (g i) (g j))
    rw [map_commutatorElement, hσi, hσj, commutatorElement_mul_central_left (hAZ hi),
      commutatorElement_mul_central_right (hAZ hj)] at hfix
    have hinv : ⁅g i, (g j)⁻¹⁆ = ⁅g i, g j⁆⁻¹ := by
      have := commutatorElement_mul_right_of_central hc (g i) (g j)⁻¹ (g j)
      rw [inv_mul_cancel, commutatorElement_one_right] at this
      exact eq_inv_of_mul_eq_one_left this.symm
    rw [hinv] at hfix
    set c := ⁅g i, g j⁆
    have hc2 : c ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← hfix]
      exact inv_mul_cancel c
    have hc1 : c = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
      have := hcp (g i) (g j)
      rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at this
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at hc1
    exact hc1
  have hneg1 : (![1, -1, -1] : Fin 3 → ZMod p) 1 + 1 = 0 := neg_add_cancel _
  have hneg2 : (![1, -1, -1] : Fin 3 → ZMod p) 2 + 1 = 0 := neg_add_cancel _
  have hneg0' : (![-1, -1, 1] : Fin 3 → ZMod p) 0 + 1 = 0 := neg_add_cancel _
  have hneg1' : (![-1, -1, 1] : Fin 3 → ZMod p) 1 + 1 = 0 := neg_add_cancel _
  obtain ⟨hα0, -⟩ := hsign α ![1, -1, -1] hα 0
  obtain ⟨-, hα1⟩ := hsign α ![1, -1, -1] hα 1
  obtain ⟨-, hα2⟩ := hsign α ![1, -1, -1] hα 2
  obtain ⟨-, hβ0⟩ := hsign β ![-1, -1, 1] hβ 0
  obtain ⟨-, hβ1⟩ := hsign β ![-1, -1, 1] hβ 1
  obtain ⟨hβ2, -⟩ := hsign β ![-1, -1, 1] hβ 2
  have c01 := hsep α hαA 0 1 (hα0 rfl) (hα1 hneg1)
  have c02 := hsep α hαA 0 2 (hα0 rfl) (hα2 hneg2)
  have c21 := hsep β hβA 2 1 (hβ2 rfl) (hβ1 hneg1')
  have hadj : ∀ (σ : P ≃* P) (hσA : ∀ a ∈ A, σ a = a) (i : Fin 3), g i * σ (g i) ∈ A →
      ∃ d ∈ A, (g i * d⁻¹) ^ p = 1 := by
    intro σ hσA i hi
    set a := g i * σ (g i)
    have hσi : σ (g i) = (g i)⁻¹ * a := by simp [a]
    set c := g i ^ p
    have hcA : c ∈ A := hpA (g i)
    have hfix := hσA c hcA
    rw [map_pow, hσi, (hcen a hi _).symm.mul_pow, inv_pow] at hfix
    have hcc : c * c = a ^ p := by
      calc c * c = c * (c⁻¹ * a ^ p) := by rw [hfix]
        _ = a ^ p := mul_inv_cancel_left c _
    refine ⟨a ^ ((p + 1) / 2) * c⁻¹, A.mul_mem (A.pow_mem hi _) (A.inv_mem hcA), ?_⟩
    have hdA : a ^ ((p + 1) / 2) * c⁻¹ ∈ A := A.mul_mem (A.pow_mem hi _) (A.inv_mem hcA)
    have hac : Commute (a ^ ((p + 1) / 2)) c⁻¹ := ((hcen a hi c).pow_left _).inv_right
    have hdp : (a ^ ((p + 1) / 2) * c⁻¹) ^ p = c := by
      rw [hac.mul_pow, ← pow_mul, mul_comm, pow_mul, ← hcc, inv_pow]
      have hcomm : Commute c c := Commute.refl c
      rw [hcomm.mul_pow, ← pow_add]
      have : (p + 1) / 2 + (p + 1) / 2 = p + 1 := by omega
      rw [this, pow_succ, ((Commute.refl c).pow_left p).eq, mul_inv_cancel_right]
    rw [(hcen _ (A.inv_mem hdA) (g i)).symm.mul_pow, inv_pow, hdp, mul_inv_cancel]
  obtain ⟨d0, hd0, hg0⟩ := hadj β hβA 0 (hβ0 hneg0')
  obtain ⟨d1, hd1, hg1⟩ := hadj α hαA 1 (hα1 hneg1)
  obtain ⟨d2, hd2, hg2⟩ := hadj α hαA 2 (hα2 hneg2)
  set d : Fin 3 → P := ![d0, d1, d2]
  have hd : ∀ i, d i ∈ A := fun i => by fin_cases i <;> assumption
  set g' : Fin 3 → P := fun i => g i * (d i)⁻¹ with hg'def
  have hg'p : ∀ i, g' i ^ p = 1 := fun i => by fin_cases i <;> assumption
  have hτg' : ∀ i, τ (g' i) = e i := fun i => by
    rw [hg'def, map_mul, (hker _).2 (A.inv_mem (hd i)), mul_one, hg i]
  have hcomm' : ∀ i j, Commute (g' i) (g' j) := by
    have hbase : ∀ i j, Commute (g i) (g j) := by
      intro i j
      fin_cases i <;> fin_cases j
      all_goals first
        | exact Commute.refl _
        | assumption
        | exact Commute.symm (by assumption)
    intro i j
    exact ((hbase i j).mul_right (hcen _ (A.inv_mem (hd j)) (g i)).symm).mul_left
      (hcen _ (A.inv_mem (hd i)) _)
  have : NeZero p := ⟨hp'.ne_zero⟩
  let ψ : Fin 3 → Multiplicative (ZMod p) →* P := fun i => zmodPowHom (g' i) (hg'p i)
  have hψcomm : Pairwise fun i j => ∀ (x y : Multiplicative (ZMod p)), Commute (ψ i x) (ψ j y) :=
    fun i j _ x y => (hcomm' i j).pow_pow _ _
  let Ψ : (Fin 3 → Multiplicative (ZMod p)) →* P := MonoidHom.noncommPiCoprod ψ hψcomm
  have hτΨ : τ.comp Ψ = piToMultiplicative (Fin 3) (ZMod p) := by
    refine MonoidHom.functions_ext _ _ _ fun i x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_mulSingle]
    change τ (g' i ^ (Multiplicative.toAdd x).val) = _
    rw [map_pow, hτg']
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow]
    funext j
    by_cases hj : j = i
    · subst hj
      simp [he, piToMultiplicative]
    · simp [he, piToMultiplicative, hj]
  have hΨinj : Function.Injective Ψ := fun f f' h => piToMultiplicative_injective _ _ (by
    have h' := congrArg τ h
    rwa [← MonoidHom.comp_apply τ Ψ, ← MonoidHom.comp_apply τ Ψ, hτΨ] at h')
  refine ⟨Ψ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : P) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have hxp : x ^ p = 1 := by
      funext i
      apply Multiplicative.toAdd.injective
      rw [Pi.pow_apply, toAdd_pow, Pi.one_apply, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero,
        zero_mul]
    rw [← map_pow, hxp, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv, Nat.card_pi, Finset.prod_const,
      Finset.card_univ,
      Fintype.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · rw [eq_top_iff]
    intro x _
    obtain ⟨f, hf⟩ := piToMultiplicative_surjective (Fin 3) (ZMod p) (τ x)
    have h1 : τ (Ψ f) = τ x := by rw [← MonoidHom.comp_apply, hτΨ, hf]
    have hx : Ψ f * ((Ψ f)⁻¹ * x) ∈ Ψ.range ⊔ A :=
      Subgroup.mul_mem_sup ⟨f, rfl⟩ (hτeq _ _ h1)
    rw [mul_inv_cancel_left, sup_comm] at hx
    exact hx
  · rw [eq_bot_iff]
    rintro x ⟨hxA, ⟨f, rfl⟩⟩
    have h1 : τ (Ψ f) = 1 := (hker _).2 hxA
    rw [← MonoidHom.comp_apply, hτΨ] at h1
    have hf : f = 1 := piToMultiplicative_injective _ _ (by rw [h1, map_one])
    rw [hf, map_one]
    exact one_mem _

end CFSG.SectionRank
