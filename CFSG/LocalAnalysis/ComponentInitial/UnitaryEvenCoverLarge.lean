module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverLargePairing

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement Pointwise

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 0}

omit [CharP K 2] in
theorem ker_eq_bot_of_lifts_even [Finite E] [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) (hr : 1 ≤ r) (M₀ : Subgroup E)
    (hM₀N : M₀ ≤ preN θ) (hM₀inj : ∀ y ∈ M₀, θ y = 1 → y = 1)
    (hM₀surj : ∀ {B : Matrix (Fin r) (Fin r) K}, IsHerm h B → ∃ y ∈ M₀, IsN θ B y)
    (Y : Subgroup E) (hYinj : ∀ y ∈ Y, θ y = 1 → y = 1)
    (hYsurj : ∀ A : SpecialLinearGroup (Fin r) K, ∃ y ∈ Y, θ y = leviHom h r A)
    (hnorm : ∀ A ∈ LinearFlag.unitriangular r K, ∀ u ∈ Y, θ u = leviHom h r A →
      ∀ y, y ∈ M₀ ↔ u * y * u⁻¹ ∈ M₀) :
    θ.ker = ⊥ := by
  set Ut := Y ⊓ ((LinearFlag.unitriangular r K).map (leviHom h r)).comap θ with hUt
  have hUtN : Ut ≤ Subgroup.normalizer (M₀ : Set E) := by
    intro u hu
    obtain ⟨A, hA, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    rw [Subgroup.mem_normalizer_iff]
    exact hnorm A hA u (Subgroup.mem_inf.mp hu).1 hAu.symm
  set P₀ := M₀ ⊔ Ut with hP₀
  have hP₀mul : (P₀ : Set E) = (M₀ : Set E) * (Ut : Set E) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M₀ Ut hUtN
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hθz
    rw [← SetLike.mem_coe, hP₀mul, Set.mem_mul] at hz
    obtain ⟨m, hm, u, hu, rfl⟩ := hz
    obtain ⟨B, hB, hmB⟩ := mem_preN.mp (hM₀N hm)
    obtain ⟨A, hA, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    have : CharP K 2 := h.charP
    have h1 : hypProj h r 0 (nElt hB) * hypProj h r 0 (lHom h r (slHom h r A)) = 1 := by
      rw [← hmB]
      change θ m * leviHom h r A = 1
      rw [hAu, ← map_mul, hθz]
    have hA1 := eq_one_of_hypProj_nElt_mul_lHom hr hB hA h1
    have hθu : θ u = 1 := by rw [← hAu, hA1, map_one]
    have hθm : θ m = 1 := by rwa [map_mul, hθu, mul_one] at hθz
    rw [hM₀inj m hm hθm, hYinj u (Subgroup.mem_inf.mp hu).1 hθu, one_mul]
  obtain ⟨-, -, -, -, ⟨S, hS⟩, -, -⟩ := unitary_order_and_Sylow h hr (Nat.zero_le 1)
  have hSle : (S : Subgroup (hypPSU h r 0)) ≤ P₀.map θ := by
    intro s hs
    rw [hS] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨A, hA, B, hB, rfl⟩ := exists_lHom_mul_nElt_of_mem hg
    obtain ⟨y, hy, hyA⟩ := hYsurj A
    obtain ⟨m, hm, hmB⟩ := hM₀surj hB
    have hyU : y ∈ Ut := ⟨hy, ⟨A, hA, hyA.symm⟩⟩
    refine ⟨y * m, mul_mem (Subgroup.mem_sup_right hyU) (Subgroup.mem_sup_left hm), ?_⟩
    obtain ⟨hB', hmB'⟩ := hmB
    rw [map_mul, hyA, hmB', map_mul]
    rfl
  exact LinearCover.ker_eq_bot_of_sylow_le_map θ hθ hC h2 S P₀ hSle hinj

omit [CharP K 2] in
theorem eq_one_of_conj_mul_inv_of_odd (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker)
    {g₀ : E} {m : ℕ} (hm : Odd m) (hg₀m : θ (g₀ ^ m) = 1) {y : E}
    (hy : θ (g₀ * y * g₀⁻¹ * y⁻¹) = 1) : g₀ * y * g₀⁻¹ * y⁻¹ = 1 := by
  have hconj : g₀ * y * g₀⁻¹ = (g₀ * y * g₀⁻¹ * y⁻¹) * y := by group
  generalize hxdef : g₀ * y * g₀⁻¹ * y⁻¹ = x at hy hconj ⊢
  have hcx : ∀ g : E, g * x = x * g := fun g => Subgroup.mem_center_iff.mp (hC hy) g
  have hk : ∀ k : ℕ, g₀ ^ k * y * (g₀ ^ k)⁻¹ = x ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g₀ ^ (k + 1) * y * (g₀ ^ (k + 1))⁻¹ = g₀ * (g₀ ^ k * y * (g₀ ^ k)⁻¹) * g₀⁻¹ := by
            group
        _ = g₀ * (x ^ k * y) * g₀⁻¹ := by rw [ih]
        _ = x ^ k * (g₀ * y * g₀⁻¹) := by
            rw [show g₀ * (x ^ k * y) * g₀⁻¹ = (g₀ * x ^ k) * y * g₀⁻¹ by group,
              (Commute.pow_right (hcx g₀) k).eq]
            group
        _ = x ^ (k + 1) * y := by rw [hconj, pow_succ, mul_assoc]
  have hgmc : ∀ g : E, g * g₀ ^ m = g₀ ^ m * g := fun g =>
    Subgroup.mem_center_iff.mp (hC hg₀m) g
  have hxm : x ^ m = 1 := by
    have h' := hk m
    rw [← hgmc y, mul_inv_cancel_right] at h'
    exact mul_eq_right.mp h'.symm
  obtain ⟨n, hn⟩ := h2 ⟨x, hy⟩
  have hn' : x ^ 2 ^ n = 1 := by
    simpa using congrArg (fun w : θ.ker => (w : E)) hn
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  have hord : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one hxm)
  exact orderOf_eq_one_iff.mp hord

omit [CharP K 2] in
@[expose] def radComplementE (g₀ : E) (hg₀M : ∀ y ∈ preN θ, g₀ * y * g₀⁻¹ ∈ preN θ)
    (hM : ∀ x ∈ preN θ, ∀ y ∈ preN θ, x * y = y * x) : Subgroup E where
  carrier := {x | ∃ y ∈ preN θ, x = g₀ * y * g₀⁻¹ * y⁻¹}
  one_mem' := ⟨1, one_mem _, by group⟩
  mul_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨y * y', mul_mem hy hy', ?_⟩
    have h1 := hM (g₀ * y' * g₀⁻¹) (hg₀M y' hy') y⁻¹ (inv_mem hy)
    have h2 := hM y hy y' hy'
    calc g₀ * y * g₀⁻¹ * y⁻¹ * (g₀ * y' * g₀⁻¹ * y'⁻¹)
        = g₀ * y * g₀⁻¹ * (y⁻¹ * (g₀ * y' * g₀⁻¹)) * y'⁻¹ := by group
      _ = g₀ * y * g₀⁻¹ * ((g₀ * y' * g₀⁻¹) * y⁻¹) * y'⁻¹ := by rw [h1]
      _ = g₀ * (y * y') * g₀⁻¹ * (y' * y)⁻¹ := by group
      _ = g₀ * (y * y') * g₀⁻¹ * (y * y')⁻¹ := by rw [h2]
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y⁻¹, inv_mem hy, ?_⟩
    have h1 := hM y hy (g₀ * y⁻¹ * g₀⁻¹) (hg₀M y⁻¹ (inv_mem hy))
    calc (g₀ * y * g₀⁻¹ * y⁻¹)⁻¹ = y * (g₀ * y⁻¹ * g₀⁻¹) := by group
      _ = g₀ * y⁻¹ * g₀⁻¹ * y := h1
      _ = g₀ * y⁻¹ * g₀⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]

omit [CharP K 2] in
theorem torusF_const_congr {s : Kˣ} (hs : h.bar (s : K) = s) (B : Matrix (Fin r) (Fin r) K) :
    (((torusF (fun _ => s) (fun _ => hs) : detFixed h r) : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K) * B *
      ((((torusF (fun _ => s) (fun _ => hs) : detFixed h r) : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = ((s : K) ^ 2) • B := by
  rw [coe_torusF, diagonal_map (map_zero _), diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul, hs]
  ring

omit [CharP K 2] in
theorem lHom_torusF_const_commute {s : Kˣ} (hs : h.bar (s : K) = s)
    (A : SpecialLinearGroup (Fin r) K) :
    lHom h r (torusF (fun _ => s) (fun _ => hs)) * lHom h r (slHom h r A) =
      lHom h r (slHom h r A) * lHom h r (torusF (fun _ => s) (fun _ => hs)) := by
  rw [← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext (Units.ext ?_)
  change (diagonal fun _ => (s : K)) * (A : Matrix (Fin r) (Fin r) K) =
    (A : Matrix (Fin r) (Fin r) K) * diagonal fun _ => (s : K)
  ext i j
  rw [diagonal_mul, mul_diagonal, mul_comm]

variable (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem ker_eq_bot_large [Finite E] [Group.IsPerfect E] (hf : 2 ≤ f) (hr : 2 ≤ r)
    (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ := by
  have := h.finite
  obtain ⟨hperf, hYinj⟩ := exists_levi_split_large hf hr hθ hC h2
  set R := (leviHom h r).range with hR
  set H := R.comap θ with hH
  set Y := ⁅H, H⁆ with hY
  have hYsurj : ∀ A : SpecialLinearGroup (Fin r) K, ∃ y ∈ Y, θ y = leviHom h r A := fun A => by
    have hA : leviHom h r A ∈ Y.map θ := by
      rw [hY, SymplecticSixCover.map_derivedComap hθ R]
      exact ⟨A, rfl⟩
    obtain ⟨y, hy, hyA⟩ := hA
    exact ⟨y, hy, hyA⟩
  have hM : ∀ x ∈ preN θ, ∀ y ∈ preN θ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_preN_large hθ hC hf hr h2 hx hy
  obtain ⟨s, hs, hs1⟩ := exists_fixed_unit (h := h) hf
  set A₀ : detFixed h r := torusF (fun _ => s) (fun _ => hs) with hA₀
  obtain ⟨g₀, hg₀⟩ := hθ (hypProj h r 0 (lHom h r A₀))
  have hg₀M : ∀ y ∈ preN θ, g₀ * y * g₀⁻¹ ∈ preN θ := fun y hy => by
    obtain ⟨B, hB⟩ := mem_preN.mp hy
    exact (hB.conj A₀ hg₀).mem
  set Vt := radComplementE g₀ hg₀M hM with hVt
  have hVtN : Vt ≤ preN θ := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (hg₀M y hy) (inv_mem hy)
  have := Fintype.ofFinite K
  have hm : Odd (Nat.card Kˣ) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' n.ne_zero).mpr even_two) odd_one
  have hg₀m : θ (g₀ ^ Nat.card Kˣ) = 1 := by
    rw [map_pow, hg₀, ← map_pow, ← map_pow]
    have : A₀ ^ Nat.card Kˣ = 1 := by
      refine Subtype.ext (Units.ext ?_)
      change ((((A₀ : detFixed h r) : GL (Fin r) K) ^ Nat.card Kˣ : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K) = 1
      rw [Units.val_pow_eq_pow_val, hA₀, coe_torusF, diagonal_pow, ← diagonal_one]
      congr 1
      funext i
      rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]
    rw [this, map_one, map_one]
  have hVtinj : ∀ x ∈ Vt, θ x = 1 → x = 1 := by
    rintro _ ⟨y, -, rfl⟩ hx
    exact eq_one_of_conj_mul_inv_of_odd hC h2 hm hg₀m hx
  have hVtsurj : ∀ {B : Matrix (Fin r) (Fin r) K}, IsHerm h B → ∃ y ∈ Vt, IsN θ B y := by
    intro B hB
    have hs2 : (s : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (sq_ne_one_of_ne_one' hs1)
    set c := ((s : K) ^ 2 - 1)⁻¹ with hc
    have hcF : h.bar c = c := by rw [hc, map_inv₀, map_sub, map_pow, hs, map_one]
    have hB' : IsHerm h (c • B) := by
      unfold IsHerm at hB ⊢
      have e : ((c • B).map h.bar)ᵀ = c • (B.map h.bar)ᵀ := by
        ext i j
        simp only [transpose_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcF]
      rw [e, ← smul_add, hB, smul_zero]
    obtain ⟨y, hy⟩ := exists_isN hθ hB'
    refine ⟨_, ⟨y, hy.mem, rfl⟩, ((hy.conj A₀ hg₀).mul hy.inv).congr ?_⟩
    rw [torusF_const_congr hs, smul_smul, ← sub_eq_add_neg, ← sub_smul,
      show (s : K) ^ 2 * c - c = 1 by rw [← sub_one_mul, hc, mul_inv_cancel₀ hs2], one_smul]
  have hg₀H : ∀ x ∈ H, θ (g₀ * x * g₀⁻¹) = θ x := by
    rintro x ⟨A, hA⟩
    rw [map_mul, map_mul, map_inv, ← hA, hg₀]
    change hypProj h r 0 (lHom h r A₀) * hypProj h r 0 (lHom h r (slHom h r A)) *
      (hypProj h r 0 (lHom h r A₀))⁻¹ = hypProj h r 0 (lHom h r (slHom h r A))
    rw [← map_mul, ← map_inv, ← map_mul, lHom_torusF_const_commute hs, mul_inv_cancel_right]
  have hg₀Y : ∀ u ∈ Y, g₀ * u * g₀⁻¹ ∈ Y := by
    intro u hu
    have h1 : H.map (MulAut.conj g₀).toMonoidHom ≤ H := by
      rintro _ ⟨x, hx, rfl⟩
      change θ (g₀ * x * g₀⁻¹) ∈ R
      rw [hg₀H x hx]
      exact hx
    have h2' : Y.map (MulAut.conj g₀).toMonoidHom ≤ Y := by
      rw [hY, Subgroup.map_commutator]
      exact Subgroup.commutator_mono h1 h1
    exact h2' ⟨u, hu, rfl⟩
  have hcomm : ∀ u ∈ Y, g₀ * u = u * g₀ := by
    intro u hu
    have hmem : g₀ * u * g₀⁻¹ * u⁻¹ ∈ Y := mul_mem (hg₀Y u hu) (inv_mem hu)
    have hθu : θ u ∈ R := Subgroup.mem_comap.1 (Subgroup.commutator_le_self H hu)
    have h1 : θ (g₀ * u * g₀⁻¹ * u⁻¹) = 1 := by
      rw [map_mul, hg₀H u hθu, map_inv, mul_inv_cancel]
    have h' := hYinj _ hmem h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
    exact h'
  have hYVt : ∀ u ∈ Y, ∀ x ∈ Vt, u * x * u⁻¹ ∈ Vt := by
    rintro u hu _ ⟨y, hy, rfl⟩
    have hc := hcomm u hu
    have hc' : u⁻¹ * g₀⁻¹ = g₀⁻¹ * u⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hc]
    have hθu : θ u ∈ R := Subgroup.mem_comap.1 (Subgroup.commutator_le_self H hu)
    obtain ⟨A, hA⟩ := hθu
    have huy : u * y * u⁻¹ ∈ preN θ := by
      obtain ⟨B, hB⟩ := mem_preN.mp hy
      exact (hB.conj (slHom h r A) hA.symm).mem
    refine ⟨u * y * u⁻¹, huy, ?_⟩
    calc u * (g₀ * y * g₀⁻¹ * y⁻¹) * u⁻¹ = (u * g₀) * y * g₀⁻¹ * y⁻¹ * u⁻¹ := by group
      _ = (g₀ * u) * y * g₀⁻¹ * y⁻¹ * u⁻¹ := by rw [hc]
      _ = g₀ * u * y * (u⁻¹ * g₀⁻¹) * u * y⁻¹ * u⁻¹ := by
          rw [hc']
          group
      _ = g₀ * (u * y * u⁻¹) * g₀⁻¹ * (u * y * u⁻¹)⁻¹ := by group
  refine ker_eq_bot_of_lifts_even hθ hC h2 (by omega) Vt hVtN hVtinj hVtsurj Y hYinj hYsurj
    fun A _ u hu _ y => ⟨fun hy => hYVt u hu y hy, fun hy => ?_⟩
  have := hYVt u⁻¹ (inv_mem hu) _ hy
  rwa [show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group] at this

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ClassicalGroups.UnitaryFlag

theorem even_even_dimensional_unitary_catalog_perfect_central_two_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {r f : ℕ} (hr : 2 ≤ r) (hf : 2 ≤ f) (hJ : CFSG.Blueprint.LieModel J .PSU (2 * r) 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hcard, ← pow_mul,
      mul_comm]⟩
    have := h.charP
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 0) h
    let φ : hypPSU h r 0 ≃* J := (hypPSUEquivStatedProj h hR (by omega)).trans e.symm
    set η' : E →* hypPSU h r 0 := φ.symm.toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact φ.symm.map_eq_one_iff
    have hbot := UnitaryEvenCover.ker_eq_bot_large (φ.symm.surjective.comp hη) (hker ▸ hC) hf
      hr (hker ▸ h2)
    rw [hker] at hbot
    exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
