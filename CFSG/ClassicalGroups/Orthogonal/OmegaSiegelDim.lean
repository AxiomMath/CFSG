module

public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
public import CFSG.HardMathSupport.Kantor79.LongRoot
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

@[expose] def OmegaSiegelDimStatement : Prop :=
  ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2] (K : Type) [Field K] [Finite K] [CharP K 2],
    Nat.card K' = Nat.card K → 4 ≤ Nat.card K →
  ∀ (N : Type) [AddCommGroup N] [Module K' N] [FiniteDimensional K' N] (QN : QuadraticForm K' N),
    (polarBilin QN).Nondegenerate → ∀ m : ℕ, finrank K' N = 2 * m → 3 ≤ m →
  ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Qf : QuadraticForm K V),
    (∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) →
  ∀ ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V), Function.Injective ρ →
    (∀ g v, Qf (ρ g v) = Qf v) →
    (∃ t₀ : ↥(elementaryGroup QN), IsOrthA2 QN (t₀ : N ≃ₗ[K'] N) ∧ IsLongRootElement Qf (ρ t₀)) →
    (∀ v : V, (∀ g, ρ g v = v) → v = 0) → commutatorSpace ρ.range = ⊤ →
    finrank K V = 2 * m ∨ (m = 3 ∧ finrank K V = 8)

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Qf : QuadraticForm K V}
  {X : Type} [Group X]

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem polar_map_of_isometry (g : V ≃ₗ[K] V) (hg : ∀ v, Qf (g v) = Qf v) (x y : V) :
    polar Qf (g x) (g y) = polar Qf x y := by
  simp only [polar, ← map_add, hg]

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem nondegenerate_of_forall (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) :
    (polarBilin Qf).Nondegenerate :=
  ⟨fun x hx => hnd x fun y => hx y, fun y hy => hnd y fun x => by rw [polar_comm]; exact hy x⟩

omit [CharP K 2] in
private theorem isCoprime_two_sub {a b : ℤ} (ha : 2 ∣ a) (hb : b = 1 ∨ b = -1) :
    IsCoprime (2 : ℤ) (a - b) := by
  obtain ⟨t, rfl⟩ := ha
  rcases hb with rfl | rfl
  · exact ⟨1 - t, 1, by ring⟩
  · exact ⟨-t, 1, by ring⟩

theorem two_mul_le_finrank_of_pow_dvd_card (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : X →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    {m : ℕ} (hm : 2 ≤ m) (hX : Nat.card K ^ (m * (m - 1)) ∣ Nat.card X) :
    2 * m ≤ finrank K V := by
  have hnd' := nondegenerate_of_forall hnd
  have hdvd : Nat.card X ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qf) := by
    have hle : ρ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Qf := by
      rintro _ ⟨g, rfl⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hρQ g)
    rw [Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have hq : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨e, he1, he⟩ : ∃ e : ℕ, 1 ≤ e ∧ Nat.card K = 2 ^ e := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hm1 : 2 ≤ m * (m - 1) := by
    calc 2 = 2 * 1 := rfl
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Qf hnd'
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · exfalso
    have hsub : Subsingleton V := Module.finrank_zero_iff.1 (by omega)
    have : Subsingleton (V ≃ₗ[K] V) :=
      ⟨fun a b => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
    have : Subsingleton X := hρ.subsingleton
    rw [Nat.card_of_subsingleton (1 : X)] at hX
    have h1 := Nat.dvd_one.1 hX
    have := Nat.one_lt_pow (by omega : m * (m - 1) ≠ 0) hq
    omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hdim : finrank K V = 2 * (k' + 1) := by omega
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ((ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Qf) ∨
        (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Qf)) := by
    by_cases h : CFSG.GroupTheory.WeirSylow.IsPlusType Qf
    · exact ⟨1, Or.inl rfl, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨-1, Or.inr rfl, Or.inr ⟨rfl, h⟩⟩
  have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd' hdim hε
  have hX' : (Nat.card K : ℤ) ^ (m * (m - 1)) ∣
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Qf) : ℤ) := by
    have := hX.trans hdvd
    exact_mod_cast this
  rw [hcard] at hX'
  have hq2 : (2 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast (show 2 ≤ Nat.card K from hq)
  have hqe : (Nat.card K : ℤ) = 2 ^ e := by rw [he]; push_cast; rfl
  set q : ℤ := (Nat.card K : ℤ) with hqdef
  have h2q : (2 : ℤ) ∣ q := by rw [hqe]; exact dvd_pow_self 2 (by omega)
  have hA : IsCoprime (2 : ℤ) (q ^ (k' + 1) - ε) :=
    isCoprime_two_sub (dvd_pow h2q (Nat.succ_ne_zero _)) hε1
  have hP : IsCoprime (2 : ℤ) (∏ i ∈ Finset.Icc 1 k', ((q ^ 2) ^ i - 1)) :=
    IsCoprime.prod_right fun i hi => by
      have hi1 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
      exact isCoprime_two_sub (dvd_pow (dvd_pow h2q two_ne_zero) hi1) (Or.inl rfl)
  have hc : ∀ {z : ℤ}, IsCoprime (2 : ℤ) z → IsCoprime (q ^ (m * (m - 1))) z := fun {z} h => by
    rw [hqe, ← pow_mul]
    exact h.pow_left
  have hdiv : q ^ (m * (m - 1)) ∣ 2 * q ^ (k' * (k' + 1)) :=
    (hc hA).dvd_of_dvd_mul_right ((hc hP).dvd_of_dvd_mul_right hX')
  by_contra hlt
  have hkm : k' + 2 ≤ m := by omega
  have hge : k' * (k' + 1) + 2 ≤ m * (m - 1) := by
    have h1 : (k' + 2) * (k' + 1) ≤ m * (m - 1) := Nat.mul_le_mul hkm (by omega)
    have h2 : (k' + 2) * (k' + 1) = k' * (k' + 1) + 2 * (k' + 1) := by ring
    omega
  have h3 : q ^ (k' * (k' + 1) + 2) ∣ 2 * q ^ (k' * (k' + 1)) := (pow_dvd_pow q hge).trans hdiv
  rw [pow_add, mul_comm (2 : ℤ)] at h3
  have h4 : q ^ 2 ∣ 2 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by omega))).1 h3
  have h5 := Int.le_of_dvd (by norm_num) h4
  nlinarith

private theorem coprime_pow_sub_one (q j : ℕ) (hq : 1 ≤ q) (hj : 1 ≤ j) :
    Nat.Coprime q (q ^ j - 1) := by
  have h : q ^ j - 1 + 1 = q ^ j := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  have h1 : Nat.gcd q (q ^ j - 1) ∣ q ^ j - 1 + 1 := by
    rw [h]
    exact (Nat.gcd_dvd_left _ _).trans (dvd_pow_self q (by omega))
  exact Nat.dvd_one.1 ((Nat.dvd_add_right (Nat.gcd_dvd_right _ _)).1 h1)

omit [CharP K 2] [Finite K] in
private theorem card_dvd_card_GL {R : Type} [AddCommGroup R] [Module K R] [FiniteDimensional K R]
    (ρ : X →* (R ≃ₗ[K] R)) (hρ : Function.Injective ρ) :
    Nat.card X ∣ Nat.card (Matrix.GeneralLinearGroup (Fin (finrank K R)) K) := by
  classical
  let b : Module.Basis (Fin (finrank K R)) K R := Module.finBasis K R
  let e : R ≃ₗ[K] (Fin (finrank K R) → K) := b.equivFun
  have h1 : Nat.card (R ≃ₗ[K] R) =
      Nat.card ((Fin (finrank K R) → K) ≃ₗ[K] (Fin (finrank K R) → K)) :=
    Nat.card_congr
      { toFun := fun u => (e.symm.trans u).trans e
        invFun := fun v => (e.trans v).trans e.symm
        left_inv := fun u => by ext x; simp
        right_inv := fun v => by ext x; simp }
  have h2 : Nat.card ((Fin (finrank K R) → K) ≃ₗ[K] (Fin (finrank K R) → K)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin (finrank K R)) K) :=
    Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin (finrank K R) → K))).toEquiv.symm)
  rw [← h2, ← h1, Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

omit [CharP K 2] in
theorem false_of_pow_dvd_card_of_finrank_le {R : Type} [AddCommGroup R] [Module K R]
    [FiniteDimensional K R] (ρ : X →* (R ≃ₗ[K] R)) (hρ : Function.Injective ρ) {m : ℕ}
    (hm : 2 ≤ m) (hX : Nat.card K ^ (m * (m - 1)) ∣ Nat.card X) (hR : finrank K R ≤ m) :
    False := by
  have hGL := card_dvd_card_GL ρ hρ
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field] at hGL
  rw [Nat.card_eq_fintype_card] at hX
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K with hqdef
  set r := finrank K R with hrdef
  have hprod : ∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) =
      q ^ (∑ i : Fin r, (i : ℕ)) * ∏ i : Fin r, (q ^ (r - i) - 1) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [hprod] at hGL
  have hcop : Nat.Coprime q (∏ i : Fin r, (q ^ (r - i) - 1)) :=
    Nat.Coprime.prod_right fun i _ => coprime_pow_sub_one q (r - i) hq.le (by have := i.2; omega)
  have hdvd : q ^ (m * (m - 1)) ∣ q ^ (∑ i : Fin r, (i : ℕ)) :=
    (hcop.pow_left _).dvd_of_dvd_mul_right (hX.trans hGL)
  have hle := (Nat.pow_dvd_pow_iff_le_right hq).1 hdvd
  have hS : ∑ i : Fin r, (i : ℕ) = ∑ i ∈ Finset.range r, i :=
    Fin.sum_univ_eq_sum_range (fun i => i) r
  have hsum := Finset.sum_range_id_mul_two r
  have h1 : r * (r - 1) ≤ m * (m - 1) := Nat.mul_le_mul hR (Nat.sub_le_sub_right hR 1)
  have h2 : 2 ≤ m * (m - 1) := by
    calc 2 = 2 * 1 := rfl
      _ ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
  omega

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem exists_restrict_action (ρ : X →* (V ≃ₗ[K] V)) (U : Submodule K V)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    ∃ ρU : X →* (U ≃ₗ[K] U), ∀ g (u : U), ((ρU g u : U) : V) = ρ g u := by
  have hmap : ∀ g, Submodule.map ((ρ g : V ≃ₗ[K] V) : V →ₗ[K] V) U = U := by
    intro g
    refine le_antisymm ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact hU g u hu
    · intro u hu
      refine ⟨ρ g⁻¹ u, hU g⁻¹ u hu, ?_⟩
      change ρ g (ρ g⁻¹ u) = u
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  refine ⟨{ toFun := fun g => LinearEquiv.ofSubmodules (ρ g) U U (hmap g)
            map_one' := ?_
            map_mul' := ?_ }, fun g u => rfl⟩
  · refine LinearEquiv.ext fun u => Subtype.ext ?_
    simp
  · intro g h
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    simp

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem injective_of_isSimpleGroup [IsSimpleGroup X] (ρ : X →* (V ≃ₗ[K] V))
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0) {U : Submodule K V} (hU0 : U ≠ ⊥)
    {ρU : X →* (U ≃ₗ[K] U)} (hρU : ∀ g (u : U), ((ρU g u : U) : V) = ρ g u) :
    Function.Injective ρU := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρU.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff ρU).1 h
  · exfalso
    refine hU0 ((Submodule.eq_bot_iff _).2 fun u hu => hC u fun g => ?_)
    have hg : g ∈ ρU.ker := h ▸ Subgroup.mem_top g
    have := hρU g ⟨u, hu⟩
    rw [MonoidHom.mem_ker.1 hg] at this
    simpa using this.symm

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem polar_comp_subtype (U : Submodule K V) (x y : U) :
    polar (Qf.comp U.subtype) x y = polar Qf (x : V) (y : V) := by
  simp [polar, QuadraticMap.comp_apply]

theorem eq_bot_or_eq_top_of_pow_dvd_card [IsSimpleGroup X]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    (ρ : X →* (V ≃ₗ[K] V)) (hρQ : ∀ g v, Qf (ρ g v) = Qf v)
    (hC : ∀ v : V, (∀ g, ρ g v = v) → v = 0) {m : ℕ} (hm : 2 ≤ m)
    (hX : Nat.card K ^ (m * (m - 1)) ∣ Nat.card X) (hV : finrank K V = 2 * m)
    (W : Submodule K V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  have hnd' := nondegenerate_of_forall hnd
  obtain ⟨U, ⟨hU0, hUW, hUinv⟩, hmin⟩ := IsArtinian.set_has_minimal
    {U : Submodule K V | U ≠ ⊥ ∧ U ≤ W ∧ ∀ g, ∀ u ∈ U, ρ g u ∈ U} ⟨W, hW0, le_rfl, hW⟩
  have hρinv : ∀ g (v : V), ρ g (ρ g⁻¹ v) = v := fun g v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  set Up : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Qf) U with hUp
  have hUp_inv : ∀ g, ∀ x ∈ Up, ρ g x ∈ Up := by
    intro g x hx
    rw [hUp, LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro n hn
    have h1 := hx (ρ g⁻¹ n) (hUinv g⁻¹ n hn)
    have h2 := polar_map_of_isometry (ρ g) (hρQ g) (ρ g⁻¹ n) x
    rw [hρinv, ← polarBilin_apply_apply, ← polarBilin_apply_apply] at h2
    exact h2.trans h1
  have hR_inv : ∀ g, ∀ x ∈ U ⊓ Up, ρ g x ∈ U ⊓ Up := fun g x hx =>
    ⟨hUinv g x hx.1, hUp_inv g x hx.2⟩
  have hRU : U ⊓ Up = ⊥ ∨ U ⊓ Up = U := by
    by_cases hR : U ⊓ Up = ⊥
    · exact Or.inl hR
    · refine Or.inr ?_
      by_contra hne
      exact hmin (U ⊓ Up) ⟨hR, inf_le_left.trans hUW, hR_inv⟩ (lt_of_le_of_ne inf_le_left hne)
  obtain ⟨ρU, hρU⟩ := exists_restrict_action ρ U hUinv
  have hinj : Function.Injective ρU := injective_of_isSimpleGroup ρ hC hU0 hρU
  have hUtop : U ≠ ⊤ := fun h => hW1 (top_le_iff.1 (h ▸ hUW))
  rcases hRU with hR | hR
  · have hndU : ∀ x : U, (∀ y : U, polar (Qf.comp U.subtype) x y = 0) → x = 0 := by
      intro x hx
      have hxUp : (x : V) ∈ Up := by
        rw [hUp, LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        rw [polarBilin_apply_apply, polar_comm]
        have := hx ⟨n, hn⟩
        rwa [polar_comp_subtype] at this
      have hxR : (x : V) ∈ U ⊓ Up := ⟨x.2, hxUp⟩
      rw [hR] at hxR
      exact Subtype.ext ((Submodule.mem_bot K).1 hxR)
    have hρQU : ∀ g (u : U), (Qf.comp U.subtype) (ρU g u) = (Qf.comp U.subtype) u := by
      intro g u
      simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, hρU, hρQ]
    have h1 := two_mul_le_finrank_of_pow_dvd_card hndU ρU hinj hρQU hm hX
    have h2 : finrank K U < finrank K V := Submodule.finrank_lt hUtop
    omega
  · have hle : U ≤ Up := inf_eq_left.1 hR
    have h1 : finrank K Up = finrank K V - finrank K U :=
      LinearMap.BilinForm.finrank_orthogonal hnd' U
    have h2 := Submodule.finrank_mono hle
    have h3 := Submodule.finrank_le U
    exact false_of_pow_dvd_card_of_finrank_le ρU hinj hm hX (by omega)

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
