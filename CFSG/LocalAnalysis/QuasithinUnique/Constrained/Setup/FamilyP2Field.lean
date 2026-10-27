module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Binary

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module

section Ops

variable {K : Type} [Field K]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def Uop (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E)) (a : K) : Module.End (ZMod 2) E :=
  ((U (Multiplicative.ofAdd a) : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E)

theorem Uop_add (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E)) (a b : K) :
    Uop U (a + b) = Uop U a * Uop U b := by
  ext x
  simp only [Uop, ofAdd_add, map_mul, Module.End.mul_apply, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]

theorem Uop_zero (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E)) : Uop U 0 = 1 := by
  ext x
  simp [Uop]

theorem Uop_comm (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E)) (a b : K) :
    Uop U a * Uop U b = Uop U b * Uop U a := by
  rw [← Uop_add, ← Uop_add, add_comm]

theorem End_add_self (x : Module.End (ZMod 2) E) : x + x = 0 := by
  ext e
  simp [add_self_eq_zero_of_zmod_two]

theorem End_nsmul_odd {n : ℕ} (hn : Odd n) (x : Module.End (ZMod 2) E) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_comm, add_nsmul, one_nsmul, mul_comm, mul_nsmul, two_nsmul, End_add_self, add_zero]

end Ops

section Lines

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def fpMap (p : ℕ) (K : Type) [Field K] [CharP K p] : ZMod p →+* K :=
  ZMod.castHom (dvd_refl p) K

theorem fpMap_injective (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    Function.Injective (fpMap p K) := (fpMap p K).injective

@[expose] def eL (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E)) (b : K) : Module.End (ZMod 2) E :=
  ∑ l : ZMod p, Uop U (fpMap p K l * b)

@[expose] def eU (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E)) : Module.End (ZMod 2) E :=
  ∑ a : K, Uop U a

variable (hK : Fintype.card K = p ^ 2) (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E))

theorem hp_odd (hp5 : 5 ≤ p) : Odd p :=
  hpf.out.odd_of_ne_two (by omega)

theorem Uop_mul_eU (a : K) : Uop U a * eU U = eU U := by
  unfold eU
  rw [Finset.mul_sum]
  simp only [← Uop_add]
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => rfl

theorem eU_mul_Uop (a : K) : eU U * Uop U a = eU U := by
  unfold eU
  rw [Finset.sum_mul]
  simp only [← Uop_add]
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ fun b => rfl

theorem eL_mul_eU (hp5 : 5 ≤ p) (b : K) : eL U b * eU U = eU U := by
  unfold eL
  rw [Finset.sum_mul]
  simp only [Uop_mul_eU]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  exact End_nsmul_odd (hp_odd hp5) _

theorem eU_mul_eL (hp5 : 5 ≤ p) (b : K) : eU U * eL U b = eU U := by
  unfold eL
  rw [Finset.mul_sum]
  simp only [eU_mul_Uop]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  exact End_nsmul_odd (hp_odd hp5) _

include hK in
omit [CharP K p] in
theorem eU_mul_eU (hp5 : 5 ≤ p) : eU U * eU U = eU U := by
  change (∑ a : K, Uop U a) * eU U = eU U
  rw [Finset.sum_mul]
  simp only [Uop_mul_eU]
  rw [Finset.sum_const, Finset.card_univ, hK]
  exact End_nsmul_odd ((hp_odd hp5).pow) _

omit [Fintype K] in
theorem eL_mul_eL_self (hp5 : 5 ≤ p) (b : K) : eL U b * eL U b = eL U b := by
  unfold eL
  rw [Finset.sum_mul_sum]
  simp only [← Uop_add, ← add_mul, ← map_add]
  have h : ∀ l : ZMod p, ∑ m : ZMod p, Uop U (fpMap p K (l + m) * b) =
      ∑ m : ZMod p, Uop U (fpMap p K m * b) := fun l =>
    Fintype.sum_equiv (Equiv.addLeft l) _ _ fun m => rfl
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  exact End_nsmul_odd (hp_odd hp5) _

include hK in
theorem eL_mul_eL_of_ne (b b' : K) (hb : b ≠ 0) (hb' : ∀ l : ZMod p, b' ≠ fpMap p K l * b) :
    eL U b * eL U b' = eU U := by
  unfold eL
  rw [Finset.sum_mul_sum]
  simp only [← Uop_add]
  let f : ZMod p × ZMod p → K := fun lm => fpMap p K lm.1 * b + fpMap p K lm.2 * b'
  have hinj : Function.Injective f := by
    rintro ⟨l, m⟩ ⟨l', m'⟩ h
    simp only [f] at h
    have h1 : fpMap p K (l - l') * b = fpMap p K (m' - m) * b' := by
      rw [map_sub, map_sub]
      linear_combination h
    by_cases hm : m' - m = 0
    · have hmm : m' = m := sub_eq_zero.1 hm
      rw [hm, map_zero, zero_mul] at h1
      have h2 : fpMap p K (l - l') = 0 := (mul_eq_zero.1 h1).resolve_right hb
      have h3 : l - l' = 0 := fpMap_injective p K (h2.trans (map_zero _).symm)
      rw [hmm, sub_eq_zero.1 h3]
    · exfalso
      have hne : fpMap p K (m' - m) ≠ 0 := fun h0 =>
        hm (fpMap_injective p K (h0.trans (map_zero _).symm))
      apply hb' ((l - l') / (m' - m))
      rw [map_div₀]
      field_simp
      linear_combination -h1
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hinj, by rw [Fintype.card_prod, ZMod.card, hK, sq]⟩
  rw [← Fintype.sum_prod_type (f := fun lm : ZMod p × ZMod p => Uop U (f lm))]
  exact Fintype.sum_equiv (Equiv.ofBijective f hbij) _ _ fun _ => rfl

@[expose] def Eb (b : K) : Module.End (ZMod 2) E := eL U b + eU U

omit [Fintype K] in
theorem Uop_mul_eL (a b : K) : Uop U a * eL U b = eL U b * Uop U a := by
  unfold eL
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => Uop_comm U _ _

include hK in
theorem Eb_mul_Eb (hp5 : 5 ≤ p) (b : K) : Eb U b * Eb U b = Eb U b := by
  unfold Eb
  rw [add_mul, mul_add, mul_add, eL_mul_eL_self U hp5, eL_mul_eU U hp5, eU_mul_eL U hp5,
    eU_mul_eU hK U hp5]
  calc eL U b + eU U + (eU U + eU U) = eL U b + (eU U + eU U) + eU U := by abel
    _ = eL U b + eU U := by rw [End_add_self, add_zero]

include hK in
theorem Eb_mul_Eb_of_ne (hp5 : 5 ≤ p) (b b' : K) (hb : b ≠ 0)
    (hb' : ∀ l : ZMod p, b' ≠ fpMap p K l * b) : Eb U b * Eb U b' = 0 := by
  unfold Eb
  rw [add_mul, mul_add, mul_add, eL_mul_eL_of_ne hK U b b' hb hb', eL_mul_eU U hp5,
    eU_mul_eL U hp5, eU_mul_eU hK U hp5]
  calc eU U + eU U + (eU U + eU U) = (eU U + eU U) + (eU U + eU U) := by abel
    _ = 0 := End_add_self _

include hK in
theorem Eb_mul_eU (hp5 : 5 ≤ p) (b : K) : Eb U b * eU U = 0 := by
  unfold Eb
  rw [add_mul, eL_mul_eU U hp5, eU_mul_eU hK U hp5, End_add_self]

include hK in
theorem eU_mul_Eb (hp5 : 5 ≤ p) (b : K) : eU U * Eb U b = 0 := by
  unfold Eb
  rw [mul_add, eU_mul_eL U hp5, eU_mul_eU hK U hp5, End_add_self]

omit [Fintype K] in
theorem eL_smul (m : ZMod p) (hm : m ≠ 0) (b : K) : eL U (fpMap p K m * b) = eL U b := by
  unfold eL
  refine Fintype.sum_equiv (Equiv.mulLeft₀ m hm) _ _ fun l => ?_
  show _ = Uop U (fpMap p K (m * l) * b)
  rw [map_mul]
  congr 1
  ring

theorem Eb_smul (m : ZMod p) (hm : m ≠ 0) (b : K) : Eb U (fpMap p K m * b) = Eb U b := by
  unfold Eb
  rw [eL_smul U m hm]

omit [Fintype K] in
theorem mul_eL_of_intertwine (φ : Module.End (ZMod 2) E) (f : K → K)
    (hφ : ∀ a, φ * Uop U a = Uop U (f a) * φ) (b b' : K)
    (hf : ∀ l : ZMod p, f (fpMap p K l * b) = fpMap p K l * b') :
    φ * eL U b = eL U b' * φ := by
  unfold eL
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by rw [hφ, hf]

theorem mul_eU_of_intertwine (φ : Module.End (ZMod 2) E) (f : K → K)
    (hf : Function.Bijective f) (hφ : ∀ a, φ * Uop U a = Uop U (f a) * φ) :
    φ * eU U = eU U * φ := by
  unfold eU
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [hφ]
  exact Fintype.sum_bijective f hf _ _ fun a => rfl

theorem mul_Eb_of_intertwine (φ : Module.End (ZMod 2) E) (f : K → K)
    (hf : Function.Bijective f) (hφ : ∀ a, φ * Uop U a = Uop U (f a) * φ) (b b' : K)
    (hfb : ∀ l : ZMod p, f (fpMap p K l * b) = fpMap p K l * b') :
    φ * Eb U b = Eb U b' * φ := by
  unfold Eb
  rw [mul_add, add_mul, mul_eL_of_intertwine U φ f hφ b b' hfb,
    mul_eU_of_intertwine U φ f hf hφ]

omit [Fintype K] in
theorem op_intertwine {φ : E ≃ₗ[ZMod 2] E} (a a' : K)
    (h : φ * U (Multiplicative.ofAdd a) * φ⁻¹ = U (Multiplicative.ofAdd a')) :
    (φ : Module.End (ZMod 2) E) * Uop U a = Uop U a' * (φ : Module.End (ZMod 2) E) := by
  have h' : φ * U (Multiplicative.ofAdd a) = U (Multiplicative.ofAdd a') * φ := by
    rw [← h]; group
  ext x
  have := congrArg (fun ψ : E ≃ₗ[ZMod 2] E => ψ x) h'
  simpa [Uop] using this

theorem torus_mul_Eb {T : E ≃ₗ[ZMod 2] E} {c : K} (hc : c ≠ 0)
    (hT : ∀ a : K, T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)))
    (b : K) :
    (T : Module.End (ZMod 2) E) * Eb U b = Eb U (c ^ 2 * b) * (T : Module.End (ZMod 2) E) :=
  mul_Eb_of_intertwine U _ (fun a => c ^ 2 * a)
    (Equiv.mulLeft₀ (c ^ 2) (pow_ne_zero 2 hc)).bijective
    (fun a => op_intertwine U a _ (hT a)) b _
    (fun l => by simp only [← mul_assoc, mul_comm (c ^ 2) (fpMap p K l)])

theorem frob_mul_Eb {τ : E ≃ₗ[ZMod 2] E}
    (hτ : ∀ a : K, τ * U (Multiplicative.ofAdd a) * τ⁻¹ = U (Multiplicative.ofAdd (a ^ p)))
    (b : K) :
    (τ : Module.End (ZMod 2) E) * Eb U b = Eb U (b ^ p) * (τ : Module.End (ZMod 2) E) :=
  mul_Eb_of_intertwine U _ (fun a => a ^ p)
    (Finite.injective_iff_bijective.1 (frobenius_inj K p))
    (fun a => op_intertwine U a _ (hτ a)) b _
    (fun l => by
      rw [mul_pow, ← map_pow, ZMod.pow_card])

omit hpf [CharP K p] in
theorem orderOf_gen (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) : orderOf g = p ^ 2 - 1 := by
  classical
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hK]

omit hpf [CharP K p] in
theorem gen_pow_card_sub_one (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) : (g : K) ^ (p ^ 2 - 1) = 1 := by
  have h := pow_orderOf_eq_one g
  rw [orderOf_gen hK hg] at h
  have := congrArg Units.val h
  simpa using this

theorem gen_pow_succ_mem (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) :
    ∃ m : ZMod p, m ≠ 0 ∧ fpMap p K m = (g : K) ^ (p + 1) := by
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hpf.out.pos
  have hx : ((g : K) ^ (p + 1)) ^ p = (g : K) ^ (p + 1) := by
    rw [← pow_mul]
    have h2 : (p + 1) * p = (p ^ 2 - 1) + (p + 1) := by
      zify [hp1]
      ring
    rw [h2, pow_add, gen_pow_card_sub_one hK hg, one_mul]
  have hmem : (g : K) ^ (p + 1) ∈ (⊥ : Subfield K) :=
    (Subfield.mem_bot_iff_pow_eq_self K p).2 hx
  rw [← ZMod.fieldRange_castHom_eq_bot p] at hmem
  obtain ⟨m, hm⟩ := RingHom.mem_fieldRange.1 hmem
  refine ⟨m, ?_, hm⟩
  rintro rfl
  rw [map_zero] at hm
  exact pow_ne_zero _ g.ne_zero hm.symm

@[expose] def Bl (g : Kˣ) (j : ℕ) : Module.End (ZMod 2) E := Eb U ((g : K) ^ j)

theorem Bl_add_period (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (j k : ℕ) :
    Bl U g (j + (p + 1) * k) = Bl U g j := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm0, hm⟩ := gen_pow_succ_mem hK hg
    have h1 : (g : K) ^ (j + (p + 1) * (k + 1)) =
        fpMap p K m * (g : K) ^ (j + (p + 1) * k) := by
      rw [hm, ← pow_add]
      congr 1
      ring
    unfold Bl at ih ⊢
    rw [h1, Eb_smul U m hm0, ih]

theorem Bl_mod (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (j : ℕ) :
    Bl U g j = Bl U g (j % (p + 1)) := by
  conv_lhs => rw [← Nat.mod_add_div j (p + 1)]
  exact Bl_add_period U hK hg _ _

theorem Bl_eq_of_modEq (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {j j' : ℕ} (h : j ≡ j' [MOD p + 1]) :
    Bl U g j = Bl U g j' := by
  rw [Bl_mod U hK hg j, Bl_mod U hK hg j']
  exact congrArg (Bl U g) h

theorem not_mem_line_of_not_modEq (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {j j' : ℕ} (h : ¬ j ≡ j' [MOD p + 1]) (l : ZMod p) :
    (g : K) ^ j' ≠ fpMap p K l * (g : K) ^ j := by
  intro hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl
    exact pow_ne_zero _ g.ne_zero hl
  have h1 : (g : K) ^ (j' * (p - 1)) = (g : K) ^ (j * (p - 1)) := by
    rw [pow_mul, pow_mul, hl, mul_pow, ← map_pow, ZMod.pow_card_sub_one_eq_one hl0, map_one,
      one_mul]
  have h2 : g ^ (j' * (p - 1)) = g ^ (j * (p - 1)) := Units.ext (by simpa using h1)
  have h3 := pow_eq_pow_iff_modEq.1 h2
  have hp1 : 1 ≤ p := hpf.out.one_lt.le
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hpf.out.pos
    zify [hp1, this]
    ring
  rw [orderOf_gen hK hg, hsq] at h3
  have hne : p - 1 ≠ 0 := by have := hpf.out.one_lt; omega
  exact h (Nat.ModEq.mul_right_cancel' hne h3).symm

theorem Bl_mul_Bl_of_modEq (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (hp5 : 5 ≤ p) {j j' : ℕ} (h : j ≡ j' [MOD p + 1]) :
    Bl U g j * Bl U g j' = Bl U g j := by
  rw [← Bl_eq_of_modEq U hK hg h]
  exact Eb_mul_Eb hK U hp5 _

theorem Bl_mul_Bl_of_not_modEq (hK : Fintype.card K = p ^ 2) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (hp5 : 5 ≤ p) {j j' : ℕ}
    (h : ¬ j ≡ j' [MOD p + 1]) : Bl U g j * Bl U g j' = 0 :=
  Eb_mul_Eb_of_ne hK U hp5 _ _ (pow_ne_zero _ g.ne_zero) (not_mem_line_of_not_modEq hK hg h)

theorem torus_mul_Bl {g : Kˣ} {T : E ≃ₗ[ZMod 2] E} {k : ℕ}
    (hT : ∀ a : K, T * U (Multiplicative.ofAdd a) * T⁻¹ =
      U (Multiplicative.ofAdd (((g : K) ^ k) ^ 2 * a))) (j : ℕ) :
    (T : Module.End (ZMod 2) E) * Bl U g j = Bl U g (j + 2 * k) * (T : Module.End (ZMod 2) E) := by
  have h := torus_mul_Eb U (pow_ne_zero k g.ne_zero) hT ((g : K) ^ j)
  unfold Bl
  rw [h, ← pow_mul, ← pow_add]
  congr 3
  ring

theorem frob_mul_Bl {g : Kˣ} {τ : E ≃ₗ[ZMod 2] E}
    (hτ : ∀ a : K, τ * U (Multiplicative.ofAdd a) * τ⁻¹ = U (Multiplicative.ofAdd (a ^ p)))
    (j : ℕ) :
    (τ : Module.End (ZMod 2) E) * Bl U g j = Bl U g (j * p) * (τ : Module.End (ZMod 2) E) := by
  have h := frob_mul_Eb U hτ ((g : K) ^ j)
  unfold Bl
  rw [h, ← pow_mul]

theorem End_nsmul_even {n : ℕ} (hn : Even n) (x : Module.End (ZMod 2) E) : n • x = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul]
  exact End_add_self _

theorem sum_Bl (hK : Fintype.card K = p ^ 2) {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    (hp5 : 5 ≤ p) : eU U + ∑ j ∈ Finset.range (p + 1), Bl U g j = 1 := by
  classical
  have hev : Even (p + 1) := (hp_odd hp5).add_one
  have hN : ∑ j ∈ Finset.range (p + 1), Bl U g j =
      ∑ j ∈ Finset.range (p + 1), eL U ((g : K) ^ j) := by
    unfold Bl Eb
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, End_nsmul_even hev, add_zero]
  have hsplit : ∀ j : ℕ, eL U ((g : K) ^ j) = 1 +
      ∑ l ∈ (Finset.univ : Finset (ZMod p)).erase 0, Uop U (fpMap p K l * (g : K) ^ j) := by
    intro j
    unfold eL
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), map_zero, zero_mul, Uop_zero]
  have hS : ∑ j ∈ Finset.range (p + 1), ∑ l ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      Uop U (fpMap p K l * (g : K) ^ j) = ∑ a ∈ (Finset.univ : Finset K).erase 0, Uop U a := by
    rw [← Finset.sum_product']
    refine Finset.sum_bij (fun x _ => fpMap p K x.2 * (g : K) ^ x.1) ?_ ?_ ?_ ?_
    · rintro ⟨j, l⟩ hx
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_erase, Finset.mem_univ,
        and_true] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact mul_ne_zero ((map_ne_zero _).2 hx.2) (pow_ne_zero _ g.ne_zero)
    · rintro ⟨j, l⟩ hx ⟨j', l'⟩ hx' h
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_erase, Finset.mem_univ,
        and_true] at hx hx'
      have h' : fpMap p K l * (g : K) ^ j = fpMap p K l' * (g : K) ^ j' := h
      have hjj : j = j' := by
        by_contra hne
        have hmod : ¬ j ≡ j' [MOD p + 1] := fun hm => hne (by
          have hm' := hm
          unfold Nat.ModEq at hm'
          rwa [Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hx'.1] at hm')
        have hl'0 : fpMap p K l' ≠ 0 := (map_ne_zero _).2 hx'.2
        apply not_mem_line_of_not_modEq hK hg hmod (l / l')
        rw [map_div₀]
        field_simp
        linear_combination -h'
      subst hjj
      have hl : fpMap p K l = fpMap p K l' := mul_right_cancel₀ (pow_ne_zero _ g.ne_zero) h'
      exact Prod.ext rfl (fpMap_injective p K hl)
    · intro b hb
      have hb0 : b ≠ 0 := (Finset.mem_erase.1 hb).1
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (g : K) ^ m = b := by
        have h1 := hg (Units.mk0 b hb0)
        rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at h1
        obtain ⟨m, hm⟩ := h1
        exact ⟨m, by simpa using congrArg Units.val hm⟩
      obtain ⟨m₀, hm₀0, hm₀⟩ := gen_pow_succ_mem hK hg
      refine ⟨(m % (p + 1), m₀ ^ (m / (p + 1))), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range, Finset.mem_erase, Finset.mem_univ,
          and_true]
        exact ⟨Nat.mod_lt _ (Nat.succ_pos p), pow_ne_zero _ hm₀0⟩
      · show fpMap p K (m₀ ^ (m / (p + 1))) * (g : K) ^ (m % (p + 1)) = b
        rw [map_pow, hm₀, ← pow_mul, ← pow_add, ← hm]
        congr 1
        have := Nat.mod_add_div m (p + 1)
        omega
    · intro x _
      rfl
  have hT : eU U = 1 + ∑ a ∈ (Finset.univ : Finset K).erase 0, Uop U a := by
    unfold eU
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), Uop_zero]
  rw [hN]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, End_nsmul_even hev, zero_add,
    hS, hT, add_assoc, End_add_self, add_zero]

end Lines

section Rank

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

theorem finrank_le_range_of_injOn (f : E →ₗ[ZMod 2] E) (N : Submodule (ZMod 2) E)
    (h : ∀ x ∈ N, f x = 0 → x = 0) :
    finrank (ZMod 2) N ≤ finrank (ZMod 2) (LinearMap.range f) := by
  have hinj : Function.Injective (f.domRestrict N) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (h x x.2 hx)
  calc finrank (ZMod 2) N = finrank (ZMod 2) (LinearMap.range (f.domRestrict N)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ finrank (ZMod 2) (LinearMap.range f) :=
        Submodule.finrank_mono (LinearMap.range_domRestrict_le_range f N)

omit [Module.Finite (ZMod 2) E] in
theorem eq_zero_of_swapped_fixed (τ : E ≃ₗ[ZMod 2] E) {P P' : Module.End (ZMod 2) E}
    (hPP : P * P = P) (hτ : (τ : Module.End (ZMod 2) E) * P = P' * (τ : Module.End (ZMod 2) E))
    (hPP' : P' * P = 0) {x : E} (hx : x ∈ LinearMap.range P) (hfix : τ x = x) : x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have hP2 : P (P y) = P y := by simpa using LinearMap.congr_fun hPP y
  have h2 : P' (P y) = P y := by
    calc P' (P y) = P' (τ (P y)) := by rw [hfix]
      _ = τ (P (P y)) := (LinearMap.congr_fun hτ (P y)).symm
      _ = τ (P y) := by rw [hP2]
      _ = P y := hfix
  have h3 : P' (P y) = 0 := by simpa using LinearMap.congr_fun hPP' y
  exact h2.symm.trans h3

omit [Module.Finite (ZMod 2) E] in
theorem exists_moved_of_swapped (τ : E ≃ₗ[ZMod 2] E) {P P' : Module.End (ZMod 2) E}
    (hP : P ≠ 0) (hPP : P * P = P)
    (hτ : (τ : Module.End (ZMod 2) E) * P = P' * (τ : Module.End (ZMod 2) E))
    (hPP' : P' * P = 0) : ∃ m ∈ LinearMap.range P, τ m ≠ m := by
  by_contra hcon
  push Not at hcon
  apply hP
  ext y
  exact eq_zero_of_swapped_fixed τ hPP hτ hPP' ⟨y, rfl⟩ (hcon _ ⟨y, rfl⟩)

theorem finrank_le_rank_of_swapped (τ : E ≃ₗ[ZMod 2] E) {P P' : Module.End (ZMod 2) E}
    (hPP : P * P = P) (hτ : (τ : Module.End (ZMod 2) E) * P = P' * (τ : Module.End (ZMod 2) E))
    (hPP' : P' * P = 0) :
    finrank (ZMod 2) (LinearMap.range P) ≤
      finrank (ZMod 2) (LinearMap.range ((τ : E →ₗ[ZMod 2] E) - LinearMap.id)) := by
  apply finrank_le_range_of_injOn
  intro x hx hx0
  exact eq_zero_of_swapped_fixed τ hPP hτ hPP' hx (by simpa [sub_eq_zero] using hx0)

theorem finrank_succ_le_rank_of_swapped (τ : E ≃ₗ[ZMod 2] E) {P P' Q : Module.End (ZMod 2) E}
    (hPP : P * P = P) (hτ : (τ : Module.End (ZMod 2) E) * P = P' * (τ : Module.End (ZMod 2) E))
    (hPP' : P' * P = 0) (hPQ : P * Q = 0) (hP'Q : P' * Q = 0) {m : E}
    (hm : m ∈ LinearMap.range Q) (hτm : τ m ≠ m) :
    finrank (ZMod 2) (LinearMap.range P) + 1 ≤
      finrank (ZMod 2) (LinearMap.range ((τ : E →ₗ[ZMod 2] E) - LinearMap.id)) := by
  obtain ⟨z, rfl⟩ := hm
  set mQ := Q z with hmQ
  have hPm : P mQ = 0 := by simpa using LinearMap.congr_fun hPQ z
  have hP'm : P' mQ = 0 := by simpa using LinearMap.congr_fun hP'Q z
  have hm0 : mQ ≠ 0 := fun h => hτm (by rw [h, map_zero])
  have hbin : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  set N : Submodule (ZMod 2) E := LinearMap.range P ⊔ Submodule.span (ZMod 2) {mQ} with hN
  have hinj : ∀ x ∈ N, ((τ : E →ₗ[ZMod 2] E) - (LinearMap.id : E →ₗ[ZMod 2] E)) x = 0 →
      x = 0 := by
    intro x hx hx0
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨y', rfl⟩ := hy
    have hfix : τ (P y' + c • mQ) = P y' + c • mQ := by simpa [sub_eq_zero] using hx0
    have hP'x : P' (P y' + c • mQ) = 0 := by
      rw [map_add, map_smul, hP'm, smul_zero, add_zero]
      simpa using LinearMap.congr_fun hPP' y'
    have h1 : τ (P (P y' + c • mQ)) = 0 := by
      have h := LinearMap.congr_fun hτ (P y' + c • mQ)
      have h' : τ (P (P y' + c • mQ)) = P' (τ (P y' + c • mQ)) := h
      rw [h', hfix, hP'x]
    have h2 : P (P y' + c • mQ) = 0 := (τ.map_eq_zero_iff).1 h1
    have hP2 : P (P y') = P y' := by simpa using LinearMap.congr_fun hPP y'
    have h3 : P y' = 0 := by
      rw [map_add, map_smul, hPm, smul_zero, add_zero, hP2] at h2
      exact h2
    rw [h3, zero_add] at hfix ⊢
    rcases hbin c with rfl | rfl
    · simp
    · exfalso
      apply hτm
      simpa using hfix
  have hdisj : Disjoint (LinearMap.range P) (Submodule.span (ZMod 2) {mQ}) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx'
    rcases hbin c with rfl | rfl
    · simp
    · exfalso
      obtain ⟨y, hy⟩ := hx
      have hPy : P (P y) = P y := by simpa using LinearMap.congr_fun hPP y
      rw [one_smul] at hy
      have : P mQ = mQ := by rw [← hy, hPy]
      exact hm0 (this.symm.trans hPm)
  have hdim : finrank (ZMod 2) N = finrank (ZMod 2) (LinearMap.range P) + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P)
      (Submodule.span (ZMod 2) {mQ})
    rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton hm0] at h
    rw [hN]
    omega
  rw [← hdim]
  exact finrank_le_range_of_injOn _ N hinj

end Rank

section Dim

theorem prime_dvd_card_GL_small {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : n ≤ 3)
    (h : p ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ))) : n = 3 ∧ p = 7 := by
  interval_cases n
  · simp at h
    omega
  · simp at h
    omega
  · simp [Fin.prod_univ_succ] at h
    have h6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) h
    interval_cases p <;> first | (norm_num at hp; done) | norm_num at h
  · refine ⟨rfl, ?_⟩
    simp [Fin.prod_univ_succ] at h
    have h168 : p ∣ 7 * 24 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).1 h168 with h7 | h24
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h7
    · have h24' : p ≤ 24 := Nat.le_of_dvd (by norm_num) h24
      interval_cases p <;> first | (norm_num at hp; done) | norm_num at h24

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [CharP K p]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

theorem prime_dvd_card_aut_of_action (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E))
    (M : Submodule (ZMod 2) E) (hM : ∀ a : K, ∀ m ∈ M, U (Multiplicative.ofAdd a) m ∈ M)
    (hnz : ∃ a : K, ∃ m ∈ M, U (Multiplicative.ofAdd a) m ≠ m) :
    p ∣ ∏ i : Fin (finrank (ZMod 2) M), (2 ^ finrank (ZMod 2) M - 2 ^ (i : ℕ)) := by
  obtain ⟨a, m, hmM, hm⟩ := hnz
  have hMx : ∀ x : Multiplicative K, ∀ m ∈ M, U x m ∈ M := fun x m hm =>
    hM (Multiplicative.toAdd x) m hm
  have hmap : ∀ x : Multiplicative K, M.map (U x : E →ₗ[ZMod 2] E) = M := by
    intro x
    refine le_antisymm ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact hMx x m hm
    · intro m hm
      refine ⟨U x⁻¹ m, hMx _ m hm, ?_⟩
      show U x (U x⁻¹ m) = m
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  let Φ : Multiplicative K →* (M ≃ₗ[ZMod 2] M) :=
    { toFun := fun x => LinearEquiv.ofSubmodules (U x) M M (hmap x)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro x y
        ext m
        simp }
  have hpow : Φ (Multiplicative.ofAdd a) ^ p = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero,
      map_one]
  have hne : Φ (Multiplicative.ofAdd a) ≠ 1 := by
    intro h
    apply hm
    have := congrArg (fun f : M ≃ₗ[ZMod 2] M => (f ⟨m, hmM⟩ : E)) h
    simpa [Φ] using this
  have hord : orderOf (Φ (Multiplicative.ofAdd a)) = p := orderOf_eq_prime hpow hne
  have h1 := orderOf_dvd_natCard (Φ (Multiplicative.ofAdd a))
  rw [hord, card_automorphisms_binary rfl] at h1
  exact h1

end Dim

section BlockDim

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
variable (hK : Fintype.card K = p ^ 2) (U : Multiplicative K →* (E ≃ₗ[ZMod 2] E))

omit [Module.Finite (ZMod 2) E] in
theorem nsmul_odd_vec {n : ℕ} (hn : Odd n) (m : E) : n • m = m := by
  have h := LinearMap.congr_fun (End_nsmul_odd hn (1 : Module.End (ZMod 2) E)) m
  simpa using h

omit [Module.Finite (ZMod 2) E] in
theorem Uop_mul_Eb (a b : K) : Uop U a * Eb U b = Eb U b * Uop U a := by
  unfold Eb
  rw [mul_add, add_mul, Uop_mul_eL, Uop_mul_eU, eU_mul_Uop]

include hK in
omit [Module.Finite (ZMod 2) E] in
theorem exists_moved_vector (hp5 : 5 ≤ p) (b : K) (hb : Eb U b ≠ 0) :
    ∃ a : K, ∃ m ∈ LinearMap.range (Eb U b), Uop U a m ≠ m := by
  by_contra hcon
  push Not at hcon
  apply hb
  ext x
  have hmem : Eb U b x ∈ LinearMap.range (Eb U b) := ⟨x, rfl⟩
  have h1 : eU U (Eb U b x) = Eb U b x := by
    unfold eU
    rw [LinearMap.sum_apply]
    simp only [hcon _ _ hmem]
    rw [Finset.sum_const, Finset.card_univ, hK]
    exact nsmul_odd_vec ((hp_odd hp5).pow) _
  have h2 : Eb U b (eU U (Eb U b x)) = 0 := by
    have := LinearMap.congr_fun (Eb_mul_eU hK U hp5 b) (Eb U b x)
    simpa using this
  rw [h1] at h2
  have h3 : Eb U b (Eb U b x) = Eb U b x := by
    simpa using LinearMap.congr_fun (Eb_mul_Eb hK U hp5 b) x
  simpa [h3] using h2

include hK in
theorem block_dim (hp5 : 5 ≤ p) {b : K} (hb : Eb U b ≠ 0) :
    3 ≤ finrank (ZMod 2) (LinearMap.range (Eb U b)) ∧
      (p ≠ 7 → 4 ≤ finrank (ZMod 2) (LinearMap.range (Eb U b))) := by
  obtain ⟨a, m, hmM, hm⟩ := exists_moved_vector hK U hp5 b hb
  have hM : ∀ a : K, ∀ m ∈ LinearMap.range (Eb U b),
      U (Multiplicative.ofAdd a) m ∈ LinearMap.range (Eb U b) := by
    rintro a _ ⟨y, rfl⟩
    refine ⟨Uop U a y, ?_⟩
    have := LinearMap.congr_fun (Uop_mul_Eb U a b) y
    exact this.symm
  have h := prime_dvd_card_aut_of_action U (LinearMap.range (Eb U b)) hM ⟨a, m, hmM, hm⟩
  refine ⟨?_, fun hp7 => ?_⟩
  · by_contra hlt
    push Not at hlt
    have := prime_dvd_card_GL_small hpf.out hp5 (by omega) h
    omega
  · by_contra hlt
    push Not at hlt
    have := prime_dvd_card_GL_small hpf.out hp5 (by omega) h
    exact hp7 this.2

include hK in
omit [Module.Finite (ZMod 2) E] in
theorem exists_nonzero_Bl {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (hp5 : 5 ≤ p)
    (hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1) : ∃ j, Bl U g j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := sum_Bl U hK hg hp5
  rw [Finset.sum_eq_zero fun j _ => hcon j, add_zero] at h
  apply hU1 1 one_ne_zero
  have h1 : Uop U 1 = 1 := by
    have := Uop_mul_eU U (1 : K)
    rwa [h, mul_one] at this
  ext x
  have := LinearMap.congr_fun h1 x
  simpa [Uop] using this

omit [Module.Finite (ZMod 2) E] in
theorem Bl_ne_zero_add {g : Kˣ} {T : E ≃ₗ[ZMod 2] E} {k : ℕ}
    (hT : ∀ a : K, T * U (Multiplicative.ofAdd a) * T⁻¹ =
      U (Multiplicative.ofAdd (((g : K) ^ k) ^ 2 * a)))
    {j : ℕ} (hj : Bl U g j ≠ 0) : Bl U g (j + 2 * k) ≠ 0 := by
  intro h0
  apply hj
  have h := torus_mul_Bl U hT j
  rw [h0, zero_mul] at h
  ext x
  have h2 : T (Bl U g j x) = 0 := by simpa using LinearMap.congr_fun h x
  simpa using (T.map_eq_zero_iff).1 h2

include hK in
omit [Module.Finite (ZMod 2) E] in
theorem exists_moved_nonzero {g : Kˣ} (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (hp5 : 5 ≤ p)
    (hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1)
    (hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a))) :
    ∃ j, Bl U g j ≠ 0 ∧ ¬ (p + 1) ∣ 2 * j := by
  obtain ⟨j₀, hj₀⟩ := exists_nonzero_Bl hK U hg hp5 hU1
  by_cases h : (p + 1) ∣ 2 * j₀
  · refine ⟨j₀ + 2 * 1, ?_, ?_⟩
    · obtain ⟨T, hT'⟩ := hT ((g : K) ^ 1) (pow_ne_zero _ g.ne_zero)
      exact Bl_ne_zero_add U hT' hj₀
    · intro hd
      have h2 : 2 * (j₀ + 2 * 1) = 2 * j₀ + 4 := by ring
      rw [h2] at hd
      have h4 : (p + 1) ∣ 4 := (Nat.dvd_add_right h).1 hd
      have := Nat.le_of_dvd (by norm_num) h4
      omega
  · exact ⟨j₀, hj₀, h⟩

omit hpf [Fintype K] [CharP K p] [Module.Finite (ZMod 2) E] in
theorem not_modEq_frob {j : ℕ} (hj : ¬ (p + 1) ∣ 2 * j) : ¬ (j * p) ≡ j [MOD p + 1] := by
  intro h
  apply hj
  have h1 : j * p + j ≡ j + j [MOD p + 1] := Nat.ModEq.add_right j h
  have h2 : j * p + j ≡ 0 [MOD p + 1] := by
    have : j * p + j = (p + 1) * j := by ring
    rw [this]
    exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
  have h3 : j + j ≡ 0 [MOD p + 1] := h1.symm.trans h2
  rw [← two_mul] at h3
  exact (Nat.modEq_zero_iff_dvd).1 h3

omit hpf [Fintype K] [Module.Finite (ZMod 2) E] in
theorem two_ne_zero_of_charP {R : Type*} [Ring R] [CharP R p] (hp5 : 5 ≤ p) : (2 : R) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : R) = 0 := by exact_mod_cast h
  have h2 := (CharP.cast_eq_zero_iff R p 2).1 h'
  have := Nat.le_of_dvd two_pos h2
  omega

include hK in
omit [Module.Finite (ZMod 2) E] in
theorem exists_moved_in_fixed_line (hp5 : 5 ≤ p) {τ : E ≃ₗ[ZMod 2] E}
    (hτ : ∀ a : K, τ * U (Multiplicative.ofAdd a) * τ⁻¹ = U (Multiplicative.ofAdd (a ^ p)))
    (hne : Eb U 1 ≠ 0) : ∃ m ∈ LinearMap.range (Eb U 1), τ m ≠ m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ : ∃ x : K, x ^ p ≠ x := by
    by_contra hall
    push Not at hall
    have hbot : ∀ y : K, y ∈ (⊥ : Subfield K) := fun y =>
      (Subfield.mem_bot_iff_pow_eq_self K p).2 (hall y)
    have h1 : Nat.card (⊥ : Subfield K) = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hbot)
    rw [Subfield.card_bot K p, Nat.card_eq_fintype_card, hK] at h1
    have h2 := hpf.out.one_lt
    nlinarith
  have hxp2 : (x ^ p) ^ p = x := by
    rw [← pow_mul, ← sq, ← hK]
    exact FiniteField.pow_card x
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω = x - x ^ p := ⟨_, rfl⟩
  have hω0 : ω ≠ 0 := fun h => hx (sub_eq_zero.1 (hω ▸ h)).symm
  have hωp : ω ^ p = -ω := by
    rw [hω, sub_pow_char, hxp2, neg_sub]
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_charP hp5
  have h2Z : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP hp5
  have hωF : ∀ l : ZMod p, ω ≠ fpMap p K l := by
    intro l hl
    have h1 : ω ^ p = ω := by rw [hl, ← map_pow, ZMod.pow_card]
    rw [hωp] at h1
    have h3 : (2 : K) * ω = 0 := by linear_combination -h1
    exact hω0 ((mul_eq_zero.1 h3).resolve_left h2K)
  have hbω : ∀ l : ZMod p, (1 : K) ≠ fpMap p K l * ω := by
    intro l hl
    exact hωF l⁻¹ (by rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right hl.symm)
  apply hne
  ext y
  show Eb U 1 y = 0
  generalize hm : Eb U 1 y = m
  have hmem : m ∈ LinearMap.range (Eb U 1) := ⟨y, hm⟩
  have hUm : ∀ a : K, Uop U a m ∈ LinearMap.range (Eb U 1) := fun a =>
    ⟨Uop U a y, by
      have := LinearMap.congr_fun (Uop_mul_Eb U a 1) y
      rw [← hm]
      exact this.symm⟩
  have hUτ : ∀ l : ZMod p, Uop U (fpMap p K l * ω) m = Uop U (-(fpMap p K l * ω)) m := by
    intro l
    have h1 : τ (Uop U (fpMap p K l * ω) m) = Uop U ((fpMap p K l * ω) ^ p) (τ m) :=
      LinearMap.congr_fun (op_intertwine U (fpMap p K l * ω) _ (hτ _)) m
    rw [hcon (Uop U (fpMap p K l * ω) m) (hUm _), hcon m hmem, mul_pow, ← map_pow,
      ZMod.pow_card, hωp] at h1
    rw [h1]
    have h4 : fpMap p K l * -ω = -(fpMap p K l * ω) := by ring
    rw [h4]
  have hUfix : ∀ l' : ZMod p, Uop U (fpMap p K l' * ω) m = m := by
    intro l'
    obtain ⟨l, hl⟩ : ∃ l : ZMod p, l = l' / 2 := ⟨_, rfl⟩
    have hll : l + l = l' := by
      rw [hl]
      field_simp
      norm_num
    obtain ⟨a, ha⟩ : ∃ a : K, a = fpMap p K l * ω := ⟨_, rfl⟩
    have hfl : fpMap p K l' * ω = a + a := by
      rw [← hll, map_add, ha]
      ring
    have h1 := hUτ l
    rw [← ha] at h1
    calc Uop U (fpMap p K l' * ω) m = Uop U (a + a) m := by rw [hfl]
      _ = Uop U a (Uop U a m) := by rw [Uop_add]; rfl
      _ = Uop U a (Uop U (-a) m) := by rw [← h1]
      _ = Uop U (a + -a) m := by rw [Uop_add]; rfl
      _ = m := by rw [add_neg_cancel, Uop_zero]; rfl
  have heL : eL U ω m = m := by
    unfold eL
    rw [LinearMap.sum_apply]
    simp only [hUfix]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    exact nsmul_odd_vec (hp_odd hp5) m
  have hz : eL U ω m = 0 := by
    have h1 : eL U ω * Eb U 1 = 0 := by
      unfold Eb
      rw [mul_add, eL_mul_eL_of_ne hK U ω 1 hω0 hbω, eL_mul_eU U hp5]
      exact End_add_self _
    rw [← hm]
    simpa using LinearMap.congr_fun h1 y
  exact heL.symm.trans hz

include hK in
theorem rank_ge_four (hp5 : 5 ≤ p) (hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1)
    (hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)))
    {τ : E ≃ₗ[ZMod 2] E}
    (hτ : ∀ a : K, τ * U (Multiplicative.ofAdd a) * τ⁻¹ = U (Multiplicative.ofAdd (a ^ p))) :
    4 ≤ finrank (ZMod 2) (LinearMap.range ((τ : E →ₗ[ZMod 2] E) - LinearMap.id)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨j, hj, hjm⟩ := exists_moved_nonzero hK U hg hp5 hU1 hT
  have hP : Bl U g j * Bl U g j = Bl U g j :=
    Bl_mul_Bl_of_modEq U hK hg hp5 (Nat.ModEq.refl j)
  have hP' : Bl U g (j * p) * Bl U g j = 0 :=
    Bl_mul_Bl_of_not_modEq U hK hg hp5 (not_modEq_frob hjm)
  have hτP : (τ : Module.End (ZMod 2) E) * Bl U g j =
      Bl U g (j * p) * (τ : Module.End (ZMod 2) E) := frob_mul_Bl U hτ j
  have hrk := finrank_le_rank_of_swapped τ hP hτP hP'
  obtain ⟨hn3, hn4⟩ := block_dim hK U hp5 (b := (g : K) ^ j) hj
  have hn3' : 3 ≤ finrank (ZMod 2) (LinearMap.range (Bl U g j)) := hn3
  by_cases hp7 : p = 7
  · have h8 : p + 1 = 8 := by omega
    have hjm8 : ¬ 8 ∣ 2 * j := by rw [← h8]; exact hjm
    have hex : ∃ k : ℕ, (j + 2 * k) % 8 ≠ j % 8 ∧ (j * 7) % 8 ≠ (j + 2 * k) % 8 ∧
        (j + 2 * k) % 8 ≠ 4 := by
      have h : j % 8 = 1 ∨ j % 8 = 2 ∨ j % 8 = 3 ∨ j % 8 = 5 ∨ j % 8 = 6 ∨ j % 8 = 7 := by
        omega
      rcases h with h | h | h | h | h | h
      · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨3, by omega, by omega, by omega⟩
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨2, by omega, by omega, by omega⟩
    obtain ⟨k, hk1, hk2, hk3⟩ := hex
    obtain ⟨T, hT'⟩ := hT ((g : K) ^ k) (pow_ne_zero _ g.ne_zero)
    have hq0 : Bl U g (j + 2 * k) ≠ 0 := Bl_ne_zero_add U hT' hj
    have hmodiff : ∀ a b : ℕ, a % 8 ≠ b % 8 → ¬ a ≡ b [MOD p + 1] := by
      intro a b hab h
      apply hab
      rw [h8] at h
      exact h
    have hPQ : Bl U g j * Bl U g (j + 2 * k) = 0 :=
      Bl_mul_Bl_of_not_modEq U hK hg hp5 (hmodiff _ _ hk1.symm)
    have hP'Q : Bl U g (j * p) * Bl U g (j + 2 * k) = 0 := by
      refine Bl_mul_Bl_of_not_modEq U hK hg hp5 (hmodiff _ _ ?_)
      rw [hp7]
      exact hk2
    have hm : ∃ m ∈ LinearMap.range (Bl U g (j + 2 * k)), τ m ≠ m := by
      by_cases hqf : 8 ∣ 2 * (j + 2 * k)
      · have hq8 : (j + 2 * k) % 8 = 0 := by omega
        have hmod0 : (j + 2 * k) ≡ 0 [MOD p + 1] := by
          rw [h8]
          exact hq8
        have hBl0 : Bl U g (j + 2 * k) = Eb U 1 := by
          rw [Bl_eq_of_modEq U hK hg hmod0]
          simp [Bl]
        rw [hBl0] at hq0 ⊢
        exact exists_moved_in_fixed_line hK U hp5 hτ hq0
      · have hqm : ¬ (p + 1) ∣ 2 * (j + 2 * k) := by
          rw [h8]
          exact hqf
        have hQ : Bl U g (j + 2 * k) * Bl U g (j + 2 * k) = Bl U g (j + 2 * k) :=
          Bl_mul_Bl_of_modEq U hK hg hp5 (Nat.ModEq.refl _)
        have hQ' : Bl U g ((j + 2 * k) * p) * Bl U g (j + 2 * k) = 0 :=
          Bl_mul_Bl_of_not_modEq U hK hg hp5 (not_modEq_frob hqm)
        exact exists_moved_of_swapped τ hq0 hQ (frob_mul_Bl U hτ (j + 2 * k)) hQ'
    obtain ⟨m, hmQ, hτm⟩ := hm
    have := finrank_succ_le_rank_of_swapped τ hP hτP hP' hPQ hP'Q hmQ hτm
    omega
  · have hn4' : 4 ≤ finrank (ZMod 2) (LinearMap.range (Bl U g j)) := hn4 hp7
    exact hn4'.trans hrk

end BlockDim

end CFSG.QuasithinUnique.Setup.Family
