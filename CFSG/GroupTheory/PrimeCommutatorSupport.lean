module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import Mathlib.Data.Nat.Factors

public section

open scoped Pointwise

namespace CFSG.SolvableHall

universe u v

variable {P : Type v} {A : Type u} [Group P] [Group A] [MulDistribMulAction P A]

theorem mul_smul_inv_eq_iff (u : P) (a b : A) :
    a * (u • a)⁻¹ = b * (u • b)⁻¹ ↔ u • (a⁻¹ * b) = a⁻¹ * b := by
  rw [smul_mul', smul_inv']
  constructor
  · intro h
    calc (u • a)⁻¹ * u • b = a⁻¹ * (a * (u • a)⁻¹) * (u • b) := by group
      _ = a⁻¹ * (b * (u • b)⁻¹) * (u • b) := by rw [h]
      _ = a⁻¹ * b := by group
  · intro h
    calc a * (u • a)⁻¹ = a * ((u • a)⁻¹ * u • b) * (u • b)⁻¹ := by group
      _ = a * (a⁻¹ * b) * (u • b)⁻¹ := by rw [h]
      _ = b * (u • b)⁻¹ := by group

theorem card_image_mul_smul_inv [Finite A] (u : P) (K : Subgroup A) (C : Subgroup A)
    (hC : ∀ x : A, x ∈ C ↔ u • x = x) :
    Nat.card ((fun a : A => a * (u • a)⁻¹) '' (K : Set A)) = C.relIndex K := by
  classical
  let f : K → (fun a : A => a * (u • a)⁻¹) '' (K : Set A) := fun k =>
    ⟨(k : A) * (u • (k : A))⁻¹, ⟨k, k.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hfib : ∀ a b : K, f a = f b ↔ a⁻¹ * b ∈ C.subgroupOf K := by
    intro a b
    rw [Subgroup.mem_subgroupOf, hC]
    exact Subtype.ext_iff.trans (mul_smul_inv_eq_iff u (a : A) (b : A))
  rw [Subgroup.relIndex, Subgroup.index]
  symm
  calc Nat.card (K ⧸ C.subgroupOf K)
      = Nat.card (Quotient (Setoid.ker f)) :=
        Nat.card_congr (Quotient.congrRight fun a b => by
          rw [Setoid.ker_def, hfib]
          exact QuotientGroup.leftRel_apply)
    _ = _ := Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)

theorem solvable_prime_commutator_prime_support [Finite A] {p : ℕ} [Fact p.Prime] (u : P)
    (hgen : ∀ v : P, v ∈ Subgroup.zpowers u) (hu : orderOf u = p) (hA : Group.IsSolvable A)
    (hp : ¬ p ∣ Nat.card A) :
    let C := fixedPointSubgroup P A
    let T : Set A := Set.range fun a : A => a⁻¹ * (u • a)
    let J := commutatorAction (A := P) (G := A)
    J.Normal ∧ (∀ v : P, ∀ x ∈ J, v • x ∈ J) ∧ J = Subgroup.closure T ∧
      (J : Set A) * (C : Set A) = Set.univ ∧ Nat.card T = C.index ∧
      Nat.card J = C.index * Nat.card (J ⊓ C : Subgroup A) ∧
      (∀ r : ℕ, r.Prime → (r ∣ Nat.card J ↔ r ∣ C.index)) ∧
      (Nat.Coprime (Nat.card C) C.index → J ⊓ C = ⊥ ∧ J ⊔ C = ⊤) := by
  classical
  intro C T J
  have hpp : p.Prime := Fact.out
  have hP : Subgroup.zpowers u = ⊤ := eq_top_iff.mpr fun v _ => hgen v
  have hcardP : Nat.card P = p := by
    rw [← Subgroup.card_top (G := P), ← hP, Nat.card_zpowers, hu]
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcardP]; exact hpp.ne_zero)
  have hcop : Nat.Coprime (Nat.card P) (Nat.card A) := by
    rw [hcardP]
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mpr hp
  obtain ⟨hJn, hJinv⟩ := commutatorAction_normal_and_invariant (A := P) (G := A)
  have hfixu : ∀ x : A, x ∈ C ↔ u • x = x := by
    intro x
    constructor
    · intro hx
      exact hx u
    · intro hx v
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen v)
      exact MulAction.mem_fixedBy_zpow (α := A) hx k
  have hT : T = (fun a : A => a * (u • a)⁻¹) '' ((⊤ : Subgroup A) : Set A) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a⁻¹, Subgroup.mem_top _, ?_⟩
      simp only [smul_inv', inv_inv]
    · rintro ⟨a, -, rfl⟩
      refine ⟨a⁻¹, ?_⟩
      simp only [smul_inv', inv_inv]
  have hJT : J = Subgroup.closure T := by
    change commutatorAction (A := P) (G := A) = Subgroup.closure T
    rw [commutatorAction_eq_closure]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨v, a, rfl⟩
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, u ^ n = v := by
        have hv := hgen v
        rw [← mem_powers_iff_mem_zpowers] at hv
        exact hv
      induction n generalizing a with
      | zero => simp
      | succ n ih =>
        have h1 : a⁻¹ * (u ^ (n + 1) • a) =
            (a⁻¹ * (u ^ n • a)) * ((u ^ n • a)⁻¹ * (u • (u ^ n • a))) := by
          rw [pow_succ', mul_smul]
          group
        rw [h1]
        exact Subgroup.mul_mem _ (ih a) (Subgroup.subset_closure ⟨u ^ n • a, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact Subgroup.subset_closure ⟨u, a, rfl⟩
  have hsup : C ⊔ J = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hA hcop
  have hsup' : J ⊔ C = ⊤ := by rw [sup_comm]; exact hsup
  have hmul : (J : Set A) * (C : Set A) = Set.univ := by
    rw [← Subgroup.normal_mul, hsup', Subgroup.coe_top]
  have hcardT : Nat.card T = C.index := by
    rw [hT, card_image_mul_smul_inv u ⊤ C hfixu, Subgroup.relIndex_top_right]
  have hcardJ : Nat.card J = C.index * Nat.card (J ⊓ C : Subgroup A) := by
    have h1 : J.relIndex (C ⊔ J) = J.relIndex C := Subgroup.relIndex_sup_right C J
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 := J.card_mul_index
    have h3 := Subgroup.relIndex_mul_card (H := J) (K := C)
    have h4 := C.card_mul_index
    have hpos : 0 < J.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card J * J.index = Nat.card A := h2
      _ = Nat.card C * C.index := h4.symm
      _ = C.index * Nat.card (J ⊓ C : Subgroup A) * J.index := by
        rw [← h3, h1]
        ring
  have hsupport : ∀ r : ℕ, r.Prime → (r ∣ Nat.card J ↔ r ∣ C.index) := by
    intro r hr
    constructor
    · intro hrJ
      by_contra hrC
      have : Fact r.Prime := ⟨hr⟩
      obtain ⟨B, hBhall, hBinv, -⟩ := coprime_invariant_hall_containment
        (IsPGroup.of_card (n := 1) (by rw [hcardP, pow_one])) hp hA
        {q : Nat.Primes | (q : ℕ) ≠ r} ⊥
        (fun q hq => by
          rw [Subgroup.card_bot] at hq
          exact absurd (Nat.le_of_dvd one_pos hq) (not_le.mpr q.2.one_lt))
        (fun a x hx => by rw [Subgroup.mem_bot] at hx ⊢; rw [hx, smul_one])
      have hrB : ¬ r ∣ Nat.card B := fun h => hBhall.p_in_pi_of_p_dvd_card ⟨r, hr⟩ h rfl
      obtain ⟨k, hidx⟩ : ∃ k : ℕ, B.index = r ^ k :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
          (fun {q} hq hqd => by
            by_contra hqr
            exact hBhall.p_in_pi_of_p_dvd_index ⟨q, hq⟩ hqd hqr)⟩
      have hBC : B.index ≤ (B ⊓ C).relIndex C := by
        have hdvdA : B.index ∣ Nat.card C * C.index := by
          rw [C.card_mul_index]
          exact Subgroup.index_dvd_card B
        have hcopC : Nat.Coprime B.index C.index := by
          rw [hidx]
          exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrC)
        have hdvdC : B.index ∣ Nat.card C := hcopC.dvd_of_dvd_mul_right hdvdA
        have hsplit : Nat.card C = Nat.card (B ⊓ C : Subgroup A) * (B ⊓ C).relIndex C := by
          have h := Subgroup.relIndex_mul_card (H := B ⊓ C) (K := C)
          rw [inf_assoc, inf_idem] at h
          rw [mul_comm]
          exact h.symm
        have hcopBC : Nat.Coprime B.index (Nat.card (B ⊓ C : Subgroup A)) := by
          rw [hidx]
          refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hr).mpr fun h => hrB ?_)
          exact h.trans (Subgroup.card_dvd_of_le inf_le_left)
        rw [hsplit] at hdvdC
        have hpos : 0 < (B ⊓ C).relIndex C := by
          have h := Subgroup.relIndex_mul_card (H := B ⊓ C) (K := C)
          rcases Nat.eq_zero_or_pos ((B ⊓ C).relIndex C) with h0 | h0
          · rw [h0, zero_mul] at h
            exact absurd h.symm Nat.card_pos.ne'
          · exact h0
        exact Nat.le_of_dvd hpos (hcopBC.dvd_of_dvd_mul_left hdvdC)
      have hidxB : C.index ≤ C.relIndex B := by
        have h1 := Subgroup.relIndex_mul_index (H := B ⊓ C) (K := B) inf_le_left
        have h2 := Subgroup.relIndex_mul_index (H := B ⊓ C) (K := C) inf_le_right
        have hBpos : 0 < B.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        have h3 : (B ⊓ C).relIndex B = C.relIndex B := by
          rw [inf_comm, Subgroup.inf_relIndex_right]
        rw [← h3]
        have : C.index * B.index ≤ (B ⊓ C).relIndex B * B.index := by
          rw [h1, ← h2, mul_comm]
          exact Nat.mul_le_mul_right _ hBC
        exact Nat.le_of_mul_le_mul_right this hBpos
      set TB := (fun a : A => a * (u • a)⁻¹) '' (B : Set A) with hTB
      have hTBT : TB ⊆ T := by
        rw [hT]
        exact Set.image_mono (fun x _ => Subgroup.mem_top x)
      have hTBB : TB ⊆ B := by
        rintro _ ⟨b, hb, rfl⟩
        exact B.mul_mem hb (B.inv_mem (hBinv u b hb))
      have hcardTB : Nat.card TB = C.relIndex B := card_image_mul_smul_inv u B C hfixu
      have hTeq : TB = T := by
        apply Set.eq_of_subset_of_ncard_le hTBT _ (Set.toFinite T)
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardT, hcardTB]
        exact hidxB
      have hJB : J ≤ B := by
        rw [hJT, Subgroup.closure_le, ← hTeq]
        exact hTBB
      exact hrB (hrJ.trans (Subgroup.card_dvd_of_le hJB))
    · intro hrC
      rw [hcardJ]
      exact Dvd.dvd.mul_right hrC _
  refine ⟨hJn, fun v x hx => (hJinv.invariant v x).1 hx, hJT, hmul, hcardT, hcardJ, hsupport, ?_⟩
  intro hHall
  refine ⟨?_, hsup'⟩
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have hrJ : r ∣ Nat.card J := hrd.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hrC : r ∣ Nat.card C := hrd.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hrI : r ∣ C.index := (hsupport r hr).mp hrJ
  have h1 : r ∣ Nat.gcd (Nat.card C) C.index := Nat.dvd_gcd hrC hrI
  rw [hHall.gcd_eq_one] at h1
  exact hr.not_dvd_one h1

end CFSG.SolvableHall
