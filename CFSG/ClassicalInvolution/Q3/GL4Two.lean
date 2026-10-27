module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.ClassicalInvolution.Q3.GL4Two

open Module

theorem natCard_generalLinearGroup {N : Type*} [AddCommGroup N] [Module (ZMod 2) N] [Finite N] :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) N) =
      ∏ i : Fin (finrank (ZMod 2) N), (2 ^ finrank (ZMod 2) N - 2 ^ (i : ℕ)) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) N rfl
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field,
    ZMod.card]

theorem prod_dvd_of_le_four {n : ℕ} (hn : n ≤ 4) :
    ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) ∣ 20160 := by
  interval_cases n <;> decide +kernel

theorem prod_dvd_of_le_two {n : ℕ} (hn : n ≤ 2) : ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) ∣ 6 := by
  interval_cases n <;> decide +kernel

theorem le_two_of_three_pow_dvd {k m : ℕ} (hm : ¬ 27 ∣ m) (h : 3 ^ k ∣ m) : k ≤ 2 := by
  by_contra hk
  have : 3 ^ 3 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
  exact hm (by simpa using this.trans h)

theorem le_one_of_three_pow_dvd {k m : ℕ} (hm : ¬ 9 ∣ m) (h : 3 ^ k ∣ m) : k ≤ 1 := by
  by_contra hk
  have : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
  exact hm (by simpa using this.trans h)

theorem natCard_dvd_prod_of_displaced {V P : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [Group P] (hP : IsPGroup 3 P) (ρ : Representation (ZMod 2) P V)
    (hρ : Function.Injective ρ) {a b : P} (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    (N : Submodule (ZMod 2) V) (ha : ∀ x, ρ a x - x ∈ N) (hb : ∀ x, ρ b x - x ∈ N) :
    Nat.card P ∣ ∏ i : Fin (finrank (ZMod 2) N), (2 ^ finrank (ZMod 2) N - 2 ^ (i : ℕ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hρinv : ∀ g x, ρ g (ρ g⁻¹ x) = x := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2x : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hK : ∀ t : P, ∀ x, ρ t x - x ∈ N := by
    intro t
    have ht : t ∈ Subgroup.closure ({a, b} : Set P) := by rw [hgen]; exact Subgroup.mem_top t
    refine Subgroup.closure_induction (p := fun t _ => ∀ x, ρ t x - x ∈ N) ?_ ?_ ?_ ?_ ht
    · intro g hg x
      rcases hg with rfl | hg
      · exact ha x
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hb x
    · intro x
      simp
    · intro g h _ _ hg hh x
      have := N.add_mem (hg (ρ h x)) (hh x)
      rw [map_mul, Module.End.mul_apply]
      convert this using 1
      abel
    · intro g _ hg x
      have := N.neg_mem (hg (ρ g⁻¹ x))
      rw [hρinv] at this
      convert this using 1
      abel
  have hinv : ∀ g, N ≤ N.comap (ρ g) := fun g x hx => by
    have h := N.add_mem hx (hK g x)
    simpa using h
  let ρN : Representation (ZMod 2) P N := ρ.subrepresentation N hinv
  have hinj : Function.Injective ρN.asGroupHom := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have ht' : ∀ x ∈ N, ρ t x = x := fun x hx => by
      have := congrArg (fun u => (u.val ⟨x, hx⟩ : N).val) ht
      simpa [ρN, Representation.asGroupHom_apply] using this
    have h2 : ρ (t ^ 2) = 1 := by
      ext x
      have h1 := ht' _ (hK t x)
      rw [map_sub] at h1
      rw [pow_two, map_mul, Module.End.mul_apply, Module.End.one_apply]
      calc ρ t (ρ t x) = (ρ t (ρ t x) - ρ t x) + ρ t x := by abel
        _ = (ρ t x - x) + ρ t x := by rw [h1]
        _ = (ρ t x + ρ t x) - x := by abel
        _ = -x := by rw [h2x, zero_sub]
        _ = x := neg_eq_of_add_eq_zero_right (h2x x)
    have ht2 : t ^ 2 = 1 := hρ (h2.trans (map_one ρ).symm)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP t
    have hd : 3 ^ k ∣ 2 := hk ▸ orderOf_dvd_of_pow_eq_one ht2
    have hk0 : k = 0 := by
      by_contra hne
      have := Nat.le_of_dvd (by norm_num) hd
      have h3 : 3 ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
      omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  have hfin : Finite N := Subtype.finite
  rw [← natCard_generalLinearGroup (N := N)]
  exact Subgroup.card_dvd_of_injective _ hinj

theorem natCard_dvd_prod_of_displaced_group {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ x y : A, x * y = y * x) (hexp : ∀ x : A, x ^ 2 = 1) {P : Type*} [Group P]
    (hP : IsPGroup 3 P) (φ : P →* MulAut A) (hφ : Function.Injective φ) {a b : P}
    (hgen : Subgroup.closure ({a, b} : Set P) = ⊤) (S : Finset A)
    (ha : ∀ x, φ a x * x⁻¹ ∈ Subgroup.closure (S : Set A))
    (hb : ∀ x, φ b x * x⁻¹ ∈ Subgroup.closure (S : Set A)) :
    ∃ n ≤ S.card, Nat.card P ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  classical
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (fun x => by
    have h := hexp (Additive.toMul x)
    calc (2 : ℕ) • x = Additive.ofMul (Additive.toMul x ^ 2) := rfl
      _ = 0 := by rw [h]; rfl)
  have : Finite (Additive A) := inferInstanceAs (Finite A)
  let ρ : Representation (ZMod 2) P (Additive A) :=
    { toFun := fun g => (MonoidHom.toAdditive (φ g).toMonoidHom).toZModLinearMap 2
      map_one' := by
        ext x
        change Additive.ofMul (φ 1 (Additive.toMul x)) = x
        rw [map_one]; rfl
      map_mul' := fun g h => by
        ext x
        change Additive.ofMul (φ (g * h) (Additive.toMul x)) =
          Additive.ofMul (φ g (φ h (Additive.toMul x)))
        rw [map_mul]; rfl }
  have hρ : ∀ g x, ρ g (Additive.ofMul x) = Additive.ofMul (φ g x) := fun g x => rfl
  let N : Submodule (ZMod 2) (Additive A) :=
    Submodule.span (ZMod 2)
      ((S.map ⟨Additive.ofMul, Additive.ofMul.injective⟩ : Finset (Additive A)) :
        Set (Additive A))
  have hN : finrank (ZMod 2) N ≤ S.card :=
    (finrank_span_finset_le_card _).trans (by simp)
  have hmem : ∀ g ∈ Subgroup.closure (S : Set A), Additive.ofMul g ∈ N := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => Additive.ofMul g ∈ N) ?_ ?_ ?_ ?_ hg
    · intro x hx
      exact Submodule.subset_span (by simpa using hx)
    · exact N.zero_mem
    · intro x y _ _ hx hy
      exact N.add_mem hx hy
    · intro x _ hx
      exact N.neg_mem hx
  have hdisp : ∀ g : P, (∀ x, φ g x * x⁻¹ ∈ Subgroup.closure (S : Set A)) →
      ∀ x : Additive A, ρ g x - x ∈ N := fun g hg x => by
    have := hmem _ (hg (Additive.toMul x))
    have e : ρ g x - x = Additive.ofMul (φ g (Additive.toMul x) * (Additive.toMul x)⁻¹) := by
      rw [← div_eq_mul_inv, ofMul_div]
      exact congrArg (· - x) (hρ g (Additive.toMul x))
    rw [e]
    exact this
  have hρinj : Function.Injective ρ := by
    intro g h hgh
    apply hφ
    ext y
    exact Additive.ofMul.injective (by rw [← hρ, ← hρ, hgh])
  exact ⟨finrank (ZMod 2) N, hN, natCard_dvd_prod_of_displaced hP ρ hρinj hgen N
    (hdisp a ha) (hdisp b hb)⟩

theorem mul_comm_of_displaced {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ x y : A, x * y = y * x) (hexp : ∀ x : A, x ^ 2 = 1) {P : Type*} [Group P]
    (hP : IsPGroup 3 P) (φ : P →* MulAut A) (hφ : Function.Injective φ) (a b : P)
    (S : Finset A) (hS : S.card ≤ 4) (ha : ∀ x, φ a x * x⁻¹ ∈ Subgroup.closure (S : Set A))
    (hb : ∀ x, φ b x * x⁻¹ ∈ Subgroup.closure (S : Set A)) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup P := Subgroup.closure ({a, b} : Set P) with hT
  have haT : a ∈ T := Subgroup.subset_closure (by simp)
  have hbT : b ∈ T := Subgroup.subset_closure (by simp)
  have hgen : Subgroup.closure ({⟨a, haT⟩, ⟨b, hbT⟩} : Set T) = ⊤ := by
    have := Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set P))
    convert this using 2
    ext x
    simp [Subtype.ext_iff]
  have hfin : Finite (MulAut A) :=
    Finite.of_injective (fun f : MulAut A => f.toEquiv) fun f g h => MulEquiv.ext (fun x =>
      congrArg (fun e : A ≃ A => e x) h)
  have hφT : Function.Injective (φ.comp T.subtype) := hφ.comp T.subtype_injective
  have : Finite T := Finite.of_injective _ hφT
  obtain ⟨n, hn, hdvd⟩ := natCard_dvd_prod_of_displaced_group hcomm hexp (hP.to_subgroup T)
    (φ.comp T.subtype) hφT hgen S ha hb
  have h20 : Nat.card T ∣ 20160 :=
    hdvd.trans (prod_dvd_of_le_four (hn.trans hS))
  obtain ⟨k, hk⟩ := (hP.to_subgroup T).exists_card_eq
  have hk2 : k ≤ 2 := le_two_of_three_pow_dvd (m := 20160) (by norm_num) (hk ▸ h20)
  have h9 : Nat.card T ∣ 9 := by
    rw [hk]
    exact (Nat.pow_dvd_pow 3 hk2).trans (by norm_num)
  have hcomm' : ∀ x y : T, x * y = y * x := by
    interval_cases k
    · have : Subsingleton T := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      intro x y; exact Subsingleton.elim _ _
    · have : IsCyclic T := isCyclic_of_prime_card (p := 3) (by simpa using hk)
      intro x y; exact (IsCyclic.commGroup (α := T)).mul_comm x y
    · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hk
      intro x y; exact mul_comm' x y
  exact congrArg Subtype.val (hcomm' ⟨a, haT⟩ ⟨b, hbT⟩)

theorem mem_zpowers_of_displaced {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ x y : A, x * y = y * x) (hexp : ∀ x : A, x ^ 2 = 1) {P : Type*} [Group P]
    (hP : IsPGroup 3 P) (φ : P →* MulAut A) (hφ : Function.Injective φ) {a b : P}
    (S : Finset A) (hS : S.card ≤ 2) (ha : ∀ x, φ a x * x⁻¹ ∈ Subgroup.closure (S : Set A))
    (hb : ∀ x, φ b x * x⁻¹ ∈ Subgroup.closure (S : Set A)) (ha1 : a ≠ 1) :
    b ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup P := Subgroup.closure ({a, b} : Set P) with hT
  have haT : a ∈ T := Subgroup.subset_closure (by simp)
  have hbT : b ∈ T := Subgroup.subset_closure (by simp)
  have hgen : Subgroup.closure ({⟨a, haT⟩, ⟨b, hbT⟩} : Set T) = ⊤ := by
    have := Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set P))
    convert this using 2
    ext x
    simp [Subtype.ext_iff]
  have hfin : Finite (MulAut A) :=
    Finite.of_injective (fun f : MulAut A => f.toEquiv) fun f g h => MulEquiv.ext (fun x =>
      congrArg (fun e : A ≃ A => e x) h)
  have hφT : Function.Injective (φ.comp T.subtype) := hφ.comp T.subtype_injective
  have : Finite T := Finite.of_injective _ hφT
  obtain ⟨n, hn, hdvd⟩ := natCard_dvd_prod_of_displaced_group hcomm hexp (hP.to_subgroup T)
    (φ.comp T.subtype) hφT hgen S ha hb
  have h6 : Nat.card T ∣ 6 := hdvd.trans (prod_dvd_of_le_two (hn.trans hS))
  obtain ⟨k, hk⟩ := (hP.to_subgroup T).exists_card_eq
  have hk1 : k ≤ 1 := le_one_of_three_pow_dvd (m := 6) (by norm_num) (hk ▸ h6)
  have ha' : (⟨a, haT⟩ : T) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hcard3 : Nat.card T = 3 := by
    interval_cases k
    · exfalso
      have : Subsingleton T := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact ha' (Subsingleton.elim _ _)
    · simpa using hk
  have hord : orderOf (⟨a, haT⟩ : T) = 3 := by
    have hd : orderOf (⟨a, haT⟩ : T) ∣ 3 := hcard3 ▸ orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha'
    · exact h
  have htop : Subgroup.zpowers (⟨a, haT⟩ : T) = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hord, hcard3]
  have hb' : (⟨b, hbT⟩ : T) ∈ Subgroup.zpowers (⟨a, haT⟩ : T) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb'
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  have := congrArg Subtype.val hm
  simpa using this

end CFSG.ClassicalInvolution.Q3.GL4Two
