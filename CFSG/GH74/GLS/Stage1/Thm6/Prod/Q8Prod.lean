module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem q8_sq : ∀ q : QuaternionGroup 2, q * q = 1 ∨ q * q = QuaternionGroup.a 2 := by decide

theorem q8_comm : ∀ x y : QuaternionGroup 2,
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = QuaternionGroup.a 2 := by decide

theorem q8_center : ∀ x : QuaternionGroup 2, (∀ y, y * x = x * y) →
    x = 1 ∨ x = QuaternionGroup.a 2 := by decide

theorem q8_a2_central : ∀ y : QuaternionGroup 2, y * QuaternionGroup.a 2 = QuaternionGroup.a 2 * y := by
  decide

theorem q8_a2_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem q8_a2_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide

section Q8

variable {Γ : Type*} [Group Γ]

structure Q8Like (A : Subgroup Γ) (c : Γ) : Prop where
  mem : c ∈ A
  ne : c ≠ 1
  sq_c : c * c = 1
  central : ∀ y ∈ A, y * c = c * y
  sq : ∀ x ∈ A, x * x = 1 ∨ x * x = c
  comm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = c
  center : ∀ x ∈ A, (∀ y ∈ A, y * x = x * y) → x = 1 ∨ x = c

theorem q8Like_of_equiv {A : Subgroup Γ} (φ : ↥A ≃* QuaternionGroup 2) :
    ∃ c : Γ, Q8Like A c := by
  let c : ↥A := φ.symm (QuaternionGroup.a 2)
  refine ⟨(c : Γ), ?_⟩
  have hφ : ∀ x : ↥A, φ x = QuaternionGroup.a 2 ↔ x = c := fun x => (φ.eq_symm_apply).symm
  refine ⟨c.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have : c = 1 := Subtype.ext h
    apply q8_a2_ne
    have := congrArg φ this
    simpa [c] using this
  · have : c * c = 1 := by
      apply φ.injective
      rw [map_mul, map_one]
      simp only [c, MulEquiv.apply_symm_apply]
      exact q8_a2_sq
    exact congrArg Subtype.val this
  · intro y hy
    have : (⟨y, hy⟩ : ↥A) * c = c * ⟨y, hy⟩ := by
      apply φ.injective
      rw [map_mul, map_mul]
      simp only [c, MulEquiv.apply_symm_apply]
      exact q8_a2_central _
    exact congrArg Subtype.val this
  · intro x hx
    have key := q8_sq (φ ⟨x, hx⟩)
    rcases key with h | h
    · left
      have : (⟨x, hx⟩ : ↥A) * ⟨x, hx⟩ = 1 := by
        apply φ.injective; rw [map_mul, map_one]; exact h
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥A) * ⟨x, hx⟩ = c := by
        apply φ.injective; rw [map_mul]; simpa [c] using h
      exact congrArg Subtype.val this
  · intro x hx y hy
    have key := q8_comm (φ ⟨x, hx⟩) (φ ⟨y, hy⟩)
    rcases key with h | h
    · left
      have : (⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ * (⟨y, hy⟩)⁻¹ = 1 := by
        apply φ.injective; simp only [map_mul, map_inv, map_one]; exact h
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ * (⟨x, hx⟩)⁻¹ * (⟨y, hy⟩)⁻¹ = c := by
        apply φ.injective; simp only [map_mul, map_inv]; simpa [c] using h
      exact congrArg Subtype.val this
  · intro x hx hxc
    have key := q8_center (φ ⟨x, hx⟩) (fun q => by
      obtain ⟨y, rfl⟩ := φ.surjective q
      have := hxc y.1 y.2
      have h2 : y * ⟨x, hx⟩ = ⟨x, hx⟩ * y := Subtype.ext this
      rw [← map_mul, ← map_mul, h2])
    rcases key with h | h
    · left
      have : (⟨x, hx⟩ : ↥A) = 1 := by apply φ.injective; rw [map_one]; exact h
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥A) = c := by apply φ.injective; simpa [c] using h
      exact congrArg Subtype.val this

theorem card_sup_mul_card_inf {A B : Subgroup Γ} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  let φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hrange : φ.range = A ⊔ B := by
    simp only [φ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype]
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨(k.1.1 : Γ), k.1.1.2, ?_⟩
        invFun := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1⁻¹, B.inv_mem x.2.2⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hk := k.2
      rw [MonoidHom.mem_ker] at hk
      have : (k.1.1 : Γ) * (k.1.2 : Γ) = 1 := by simpa [φ] using hk
      have h2 : (k.1.1 : Γ) = (k.1.2 : Γ)⁻¹ := eq_inv_of_mul_eq_one_left this
      rw [h2]; exact B.inv_mem k.1.2.2
    · simp [φ]
    · rintro ⟨⟨a, b⟩, hk⟩
      rw [MonoidHom.mem_ker] at hk
      have : (a : Γ) * (b : Γ) = 1 := by simpa [φ] using hk
      have h2 : (a : Γ) = (b : Γ)⁻¹ := eq_inv_of_mul_eq_one_left this
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [h2]
    · intro x; rfl
  have := Subgroup.card_ker_mul_card_range φ
  rw [hrange, hker] at this
  rw [mul_comm, this, Nat.card_prod]

theorem q8Like_inf {A B : Subgroup Γ} {cA cB : Γ} (hA : Q8Like A cA) (hB : Q8Like B cB)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : Nat.card ↥(A ⊓ B) = 2) :
    cA = cB ∧ ∀ x ∈ A ⊓ B, x = 1 ∨ x = cA := by
  have hAB : ∀ x ∈ A ⊓ B, x = 1 ∨ x = cA := fun x hx =>
    hA.center x hx.1 (fun y hy => hc y hy x hx.2)
  have hAB' : ∀ x ∈ A ⊓ B, x = 1 ∨ x = cB := fun x hx =>
    hB.center x hx.2 (fun y hy => (hc x hx.1 y hy).symm)
  have hne : A ⊓ B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hi
    omega
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hw' : (w : Γ) ∈ A ⊓ B := w.2
  have hw1' : (w : Γ) ≠ 1 := fun e => hw1 (Subtype.ext e)
  have e1 : (w : Γ) = cA := (hAB _ hw').resolve_left hw1'
  have e2 : (w : Γ) = cB := (hAB' _ hw').resolve_left hw1'
  exact ⟨e1.symm.trans e2, hAB⟩

theorem isExtraspecial_sup_q8 [Finite Γ] {A B : Subgroup Γ} {cA cB : Γ} (hA : Q8Like A cA) (hB : Q8Like B cB)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : Nat.card ↥(A ⊓ B) = 2) (hA8 : Nat.card ↥A = 8) :
    CFSG.IsExtraspecial 2 ↥(A ⊔ B) := by
  obtain ⟨hcc, hAB⟩ := q8Like_inf hA hB hc hi
  subst hcc
  have hprod : ∀ y ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, y = a * b := fun y hy =>
    Sec12.mem_sup_of_commute hc hy
  have hcY : cA ∈ A ⊔ B := Subgroup.mem_sup_left hA.mem
  have hZ : ∀ y : ↥(A ⊔ B), y ∈ Subgroup.center ↥(A ⊔ B) ↔ (y : Γ) = 1 ∨ (y : Γ) = cA := by
    intro y
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, hyab⟩ := hprod y y.2
      have hya : a ∈ A := ha
      have h1 : ∀ a' ∈ A, a' * a = a * a' := by
        intro a' ha'
        have := hy ⟨a', Subgroup.mem_sup_left ha'⟩
        have e := congrArg Subtype.val this
        simp only [Subgroup.coe_mul, hyab] at e
        have e2 : a' * (a * b) = (a * b) * a' := by simpa using e
        have e3 : a' * a * b = a * a' * b := by
          calc a' * a * b = a' * (a * b) := by rw [mul_assoc]
            _ = (a * b) * a' := e2
            _ = a * (b * a') := by rw [mul_assoc]
            _ = a * (a' * b) := by rw [← hc a' ha' b hb]
            _ = a * a' * b := by rw [mul_assoc]
        exact mul_right_cancel e3
      have h2 : ∀ b' ∈ B, b' * b = b * b' := by
        intro b' hb'
        have := hy ⟨b', Subgroup.mem_sup_right hb'⟩
        have e := congrArg Subtype.val this
        simp only [Subgroup.coe_mul, hyab] at e
        have e2 : b' * (a * b) = (a * b) * b' := by simpa using e
        have e3 : a * (b' * b) = a * (b * b') := by
          calc a * (b' * b) = (b' * a) * b := by rw [← hc a ha b' hb', mul_assoc]
            _ = b' * (a * b) := by rw [mul_assoc]
            _ = (a * b) * b' := e2
            _ = a * (b * b') := by rw [mul_assoc]
        exact mul_left_cancel e3
      have ha' := hA.center a hya h1
      have hb' := hB.center b hb h2
      have hcc : cA * cA = 1 := hA.sq_c
      rw [hyab]
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp [hcc]
    · intro hy y'
      have hcen : ∀ g : ↥(A ⊔ B), g * ⟨cA, hcY⟩ = ⟨cA, hcY⟩ * g := by
        intro g
        obtain ⟨a, ha, b, hb, hgab⟩ := hprod g g.2
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hgab]
        calc a * b * cA = a * (b * cA) := by rw [mul_assoc]
          _ = a * (cA * b) := by rw [hB.central b hb]
          _ = (a * cA) * b := by rw [mul_assoc]
          _ = (cA * a) * b := by rw [hA.central a ha]
          _ = cA * (a * b) := by rw [mul_assoc]
      rcases hy with h | h
      · have : y = 1 := Subtype.ext h
        rw [this]; simp
      · have : y = ⟨cA, hcY⟩ := Subtype.ext h
        rw [this]; exact hcen y'
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  let ψ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hψ : ∀ (a : ↥A) (b : ↥B), ψ (a, b) = (a : Γ) * (b : Γ) := fun a b => rfl
  have hrange : ψ.range = A ⊔ B := by
    simp only [ψ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype]
  have hsq_mem : ∀ x ∈ ({1, cA} : Set Γ), ∀ y ∈ ({1, cA} : Set Γ), x * y ∈ ({1, cA} : Set Γ) := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    have hcc : cA * cA = 1 := hA.sq_c
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hcc]
  have hel : ∀ y : ↥(A ⊔ B), ∃ p : ↥A × ↥B, ψ p = (y : Γ) := by
    intro y
    have : (y : Γ) ∈ ψ.range := by rw [hrange]; exact y.2
    exact this
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨⟨cA, hcY⟩, (hZ _).2 (Or.inr rfl)⟩, ?_, ?_⟩
    · intro h
      have := congrArg (fun w : ↥(Subgroup.center ↥(A ⊔ B)) => ((w : ↥(A ⊔ B)) : Γ)) h
      simp only [OneMemClass.coe_one] at this
      exact hA.ne this.symm
    · ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hw := (hZ w).1 w.2
      rcases hw with h | h
      · left; exact Subtype.ext (Subtype.ext h)
      · right; exact Subtype.ext (Subtype.ext h)
  ·
    have hcom : ∀ x y : ↥(A ⊔ B), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥(A ⊔ B) := by
      intro x y
      obtain ⟨⟨a₁, b₁⟩, h1⟩ := hel x
      obtain ⟨⟨a₂, b₂⟩, h2⟩ := hel y
      rw [hZ]
      have e : ((x * y * x⁻¹ * y⁻¹ : ↥(A ⊔ B)) : Γ) = ψ ((a₁, b₁) * (a₂, b₂) * (a₁, b₁)⁻¹ * (a₂, b₂)⁻¹) := by
        simp only [map_mul, map_inv, h1, h2, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      have e2 : ((a₁, b₁) * (a₂, b₂) * (a₁, b₁)⁻¹ * (a₂, b₂)⁻¹ : ↥A × ↥B) =
          (a₁ * a₂ * a₁⁻¹ * a₂⁻¹, b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by
        exact Prod.ext (by simp) (by simp)
      rw [e2, hψ]
      have hxa := hA.comm a₁ a₁.2 a₂ a₂.2
      have hxb := hB.comm b₁ b₁.2 b₂ b₂.2
      have := hsq_mem _ (by simpa using hxa) _ (by
        simpa using (show ((b₁ * b₂ * b₁⁻¹ * b₂⁻¹ : ↥B) : Γ) ∈ ({1, cA} : Set Γ) by simpa using hxb))
      simpa using this
    refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have := hcom y⁻¹ x⁻¹
          simpa [mul_assoc] using this
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hZ]
        obtain ⟨⟨a, b⟩, h1⟩ := hel y
        have e : ((y ^ 2 : ↥(A ⊔ B)) : Γ) = ψ ((a, b) ^ 2) := by
          rw [map_pow, h1]; simp
        rw [e, pow_two, Prod.mul_def, hψ]
        have h1' := hA.sq a a.2
        have h2' := hB.sq b b.2
        have := hsq_mem _ (by simpa using h1') _ (by
          simpa using (show ((b * b : ↥B) : Γ) ∈ ({1, cA} : Set Γ) by simpa using h2'))
        simpa using this
  ·
    have hlt : ∃ a ∈ A, a ≠ 1 ∧ a ≠ cA := by
      by_contra hcon
      push Not at hcon
      have hle : A ≤ zpowers cA := by
        intro a ha
        by_cases h1 : a = 1
        · rw [h1]; exact Subgroup.one_mem _
        · rw [hcon a ha h1]; exact Subgroup.mem_zpowers _
      have h2 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hA.sq_c) hA.ne, hA8] at h2
      omega
    obtain ⟨a, ha, ha1, hac⟩ := hlt
    refine ⟨⟨QuotientGroup.mk ⟨a, Subgroup.mem_sup_left ha⟩, 1, ?_⟩⟩
    intro h
    have h' : (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(A ⊔ B)) ∈ Subgroup.center ↥(A ⊔ B) :=
      (QuotientGroup.eq_one_iff _).1 h
    rcases (hZ _).1 h' with h1 | h1
    · exact ha1 h1
    · exact hac h1


end Q8

theorem card_stab_le_two {U : Type*} [Group U] [Finite U] (hc : Nat.card U = 4) (z : U) (hz1 : z ≠ 1) :
    Nat.card {σ : MulAut U // σ z = z} ≤ 2 := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hT : Fintype.card {u : U // u ≠ 1 ∧ u ≠ z} = 2 := by
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun u : U => u ≠ 1 ∧ u ≠ z) = Finset.univ \ {1, z} := by
      ext u; simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hc, Finset.card_pair (Ne.symm hz1)]
  let φ : {σ : MulAut U // σ z = z} → Equiv.Perm {u : U // u ≠ 1 ∧ u ≠ z} := fun σ =>
    Equiv.subtypeEquiv σ.1.toEquiv (fun u => by
      show (u ≠ 1 ∧ u ≠ z) ↔ (σ.1 u ≠ 1 ∧ σ.1 u ≠ z)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun e => h1 ?_, fun e => h2 ?_⟩
        · exact σ.1.injective (by rw [e, map_one])
        · exact σ.1.injective (e.trans σ.2.symm)
      · rintro ⟨h1, h2⟩
        refine ⟨fun e => h1 ?_, fun e => h2 ?_⟩
        · rw [e, map_one]
        · rw [e]; exact σ.2)
  have hφ : Function.Injective φ := by
    intro σ σ' h
    apply Subtype.ext
    ext u
    by_cases hu1 : u = 1
    · simp [hu1]
    by_cases huz : u = z
    · rw [huz, σ.2, σ'.2]
    · have := congrArg (fun p => ((p ⟨u, hu1, huz⟩ : {u : U // u ≠ 1 ∧ u ≠ z}) : U)) h
      simpa [φ] using this
  calc Nat.card {σ : MulAut U // σ z = z} ≤ Nat.card (Equiv.Perm {u : U // u ≠ 1 ∧ u ≠ z}) :=
        Nat.card_le_card_of_injective φ hφ
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hT]; rfl

theorem exists_move_of_autOrd {G : Type} [Group G] [Finite G] {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) {z : G} (hz : z ∈ U) (hz1 : z ≠ 1)
    (hA : AutOrd (⊤ : Subgroup G) U = 6) :
    ∃ g ∈ normalizer (U : Set G), g * z * g⁻¹ ≠ z := by
  by_contra hall
  push Not at hall
  let α := U.normalizerMonoidHom
  have hcard : Nat.card α.range = 6 := by
    rw [← hA]
    unfold AutOrd
    rw [inf_top_eq, inf_top_eq, ← Subgroup.index_ker, Subgroup.normalizerMonoidHom_ker]
    rfl
  have hfix : ∀ σ ∈ α.range, σ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    rintro _ ⟨g, rfl⟩
    apply Subtype.ext
    show (g : G) * z * (g : G)⁻¹ = z
    exact hall g g.2
  have hinj : Function.Injective (fun σ : ↥α.range =>
      (⟨σ.1, hfix σ.1 σ.2⟩ : {σ : MulAut ↥U // σ ⟨z, hz⟩ = ⟨z, hz⟩})) := by
    intro σ σ' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hle := Nat.card_le_card_of_injective _ hinj
  have h2 := card_stab_le_two hU.2 ⟨z, hz⟩ (fun e => hz1 (congrArg Subtype.val e))
  omega


end CFSG.GH74.GLS.Stage1.Thm6.Prod
