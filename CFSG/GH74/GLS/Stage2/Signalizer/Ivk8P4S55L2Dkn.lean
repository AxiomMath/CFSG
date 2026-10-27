module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2DickMain
public import CFSG.Dihedral.Glauberman.DicksonMaxCases

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick

open Subgroup CFSG CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups

theorem dickson_orders {J : Type} [Group J] {F F' : Type}
    [Field F] [Finite F] [Field F'] [Finite F'] {r f p : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r ≠ p) (hF : Nat.card F = r ^ f)
    (hF' : (∃ n : ℕ, 1 ≤ n ∧ Nat.card F' = p ^ n) ∨ (p = 3 ∧ Nat.card F' = 5))
    (ι : J →* PSL2MatrixGroup F) (ψ : J →* PSL2MatrixGroup F') (hψ : Function.Surjective ψ)
    (hker : ι.ker ≤ ψ.ker) {y₁ y₂ : J} (hgen : Subgroup.closure ({y₁, y₂} : Set J) = ⊤)
    (h₁ : ι y₁ ^ p = 1) (h₂ : ι y₂ ^ p = 1)
    (hnoR : ∀ E : Subgroup (PSL2MatrixGroup F), IsPGroup r ↥E →
      (∀ x ∈ E, ι y₁ * x * (ι y₁)⁻¹ ∈ E) → E = ⊥) :
    (∀ x : J, ι x ^ 2 = 1 ∨ ι x ^ 3 = 1 ∨ ι x ^ 5 = 1) ∧
      ((∃ x : J, ι x ^ 5 = 1 ∧ ι x ≠ 1) → Nat.card F' = 5) := by
  classical
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  have hS' : ∀ s ∈ ({y₁, y₂} : Set J), ∃ n : ℕ, Odd n ∧ ι s ^ n = 1 := by
    intro s hs
    rcases hs with rfl | hs
    · exact ⟨p, hodd_p, h₁⟩
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨p, hodd_p, h₂⟩
  have hnc := psl2_not_comm F'
  have hQcard : Nat.card (PSL2MatrixGroup F') = Nat.card F' * (Nat.card F' ^ 2 - 1) / 2 :=
    card_psl2_F' hp hp2 hF'
  have hF'2 : 2 ≤ Nat.card F' := Finite.one_lt_card
  have hmem : ∀ x : J, ι x ∈ ι.range := fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩
  rcases dickson_psl2_subgroup_list hF ι.range with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, hm1, -, -, -, E, C, hEn, hEel, hEcard, -⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    refine Q_comm_of_range_comm ι ψ hψ hker (fun x y => ?_) a b
    have := hel.toIsMulCommutative.is_comm.comm (⟨ι x, hmem x⟩ : ι.range) ⟨ι y, hmem y⟩
    exact congrArg Subtype.val this
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    refine Q_comm_of_range_comm ι ψ hψ hker (fun x y => ?_) a b
    have := (IsCyclic.commGroup (α := ι.range)).mul_comm (⟨ι x, hmem x⟩ : ι.range) ⟨ι y, hmem y⟩
    exact congrArg Subtype.val this
  ·
    exact (false_of_exp_two_hom ι e (dihSign z) mult_zmod_two_sq (dihSign_nontrivial z) hgen
      hS').elim
  ·
    refine ⟨fun x => ?_, fun ⟨x, h5, hne⟩ => ?_⟩
    · rcases MaxCases.pow_of_mulEquiv_alternatingFour e (hmem x) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exfalso
      refine no_five_of_orders ι (fun x => ?_) ⟨x, h5, hne⟩
      exact MaxCases.pow_of_mulEquiv_alternatingFour e (hmem x)
  ·
    exact (false_of_exp_two_hom ι e Equiv.Perm.sign (fun g => Int.units_sq g)
      perm_sign_nontrivial hgen hS').elim
  ·
    refine ⟨fun x => MaxCases.pow_of_mulEquiv_alternatingFive e (hmem x), fun _ => ?_⟩
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup ι.range := e.isSimpleGroup
    have h1 := Q_card_of_simple ι ψ hψ hker this hnc
    have h60 : Nat.card ι.range = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [h60, hQcard] at h1
    exact eq_of_psl_card hF'2 (by norm_num) (h1.symm.trans (by norm_num))
  ·
    exfalso
    have hEp : IsPGroup r ↥E := IsElementaryAbelian.isPGroup r E
    set E' : Subgroup (PSL2MatrixGroup F) := E.map ι.range.subtype with hE'
    have hE'p : IsPGroup r ↥E' :=
      hEp.of_equiv (E.equivMapOfInjective ι.range.subtype ι.range.subtype_injective)
    have hnorm : ∀ x ∈ E', ι y₁ * x * (ι y₁)⁻¹ ∈ E' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(⟨ι y₁, hmem y₁⟩ : ι.range) * x * (⟨ι y₁, hmem y₁⟩ : ι.range)⁻¹,
        hEn.conj_mem x hx _, rfl⟩
    have hbot := hnoR E' hE'p hnorm
    have hE1 : E = ⊥ := by
      rw [hE'] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective E ι.range.subtype_injective).mp hbot
    have hc1 : Nat.card E = 1 := by rw [hE1]; simp
    rw [hEcard] at hc1
    have hrpos : 1 < r := hr.out.one_lt
    have : r ^ m ≠ 1 := (Nat.one_lt_pow (by omega) hrpos).ne'
    exact this hc1
  ·
    have hf0 : f ≠ 0 := by
      rintro rfl
      have : Nat.card F = 1 := by simpa using hF
      exact absurd this (Finite.one_lt_card (α := F)).ne'
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf0 (Nat.eq_zero_of_zero_dvd hmf)
    have hK : Nat.card (GaloisField r m) = r ^ m := GaloisField.card r m hm0
    have hz : ∀ z : PSL2MatrixGroup (GaloisField r m), z ^ r = 1 ∨
        z ^ ((r ^ m - 1) / Nat.gcd (r ^ m - 1) 2) = 1 ∨
        z ^ ((r ^ m + 1) / Nat.gcd (r ^ m - 1) 2) = 1 := by
      intro z
      rcases psl2_orderOf_dvd hK z with h | h | h
      · exact Or.inl (orderOf_dvd_iff_pow_eq_one.mp h)
      · rw [hK] at h
        exact Or.inr (Or.inl (orderOf_dvd_iff_pow_eq_one.mp h))
      · rw [hK] at h
        exact Or.inr (Or.inr (orderOf_dvd_iff_pow_eq_one.mp h))
    have hpowe : ∀ (x : J) (k : ℕ), (e ⟨ι x, hmem x⟩) ^ k = 1 → ι x ^ k = 1 := by
      intro x k h
      have h1 : (⟨ι x, hmem x⟩ : ι.range) ^ k = 1 := by
        rw [← map_pow] at h
        exact e.injective (by rw [h, map_one])
      simpa using congrArg Subtype.val h1
    have hrm_odd : Odd (r ^ m) := (hr.out.odd_of_ne_two hr2).pow
    have hrm3 : 3 ≤ r ^ m := by
      have h3 : 3 ≤ r := by
        have := hr.out.two_le
        have := hr.out.odd_of_ne_two hr2
        obtain ⟨k, hk⟩ := this
        omega
      exact h3.trans (Nat.le_self_pow hm0 r)
    by_cases hs3 : r ^ m = 3
    ·
      have hrr : r = 3 := by
        have : r ∣ 3 := hs3 ▸ dvd_pow_self r hm0
        exact (Nat.prime_dvd_prime_iff_eq hr.out (by norm_num)).mp this
      have hord : ∀ x : J, ι x ^ 2 = 1 ∨ ι x ^ 3 = 1 := by
        intro x
        rcases hz (e ⟨ι x, hmem x⟩) with h | h | h
        · have h' := hpowe x r h
          rw [hrr] at h'
          exact Or.inr h'
        · have h' := hpowe x _ h
          have hk2 : (r ^ m - 1) / Nat.gcd (r ^ m - 1) 2 = 1 := by rw [hs3]; norm_num
          rw [hk2, pow_one] at h'
          exact Or.inl (by rw [h', one_pow])
        · have h' := hpowe x _ h
          have hk2 : (r ^ m + 1) / Nat.gcd (r ^ m - 1) 2 = 2 := by rw [hs3]; norm_num
          rw [hk2] at h'
          exact Or.inl h'
      exact ⟨fun x => (hord x).elim Or.inl fun h => Or.inr (Or.inl h),
        fun hx => (no_five_of_orders ι hord hx).elim⟩
    ·
      have hs5 : 5 ≤ r ^ m := by
        obtain ⟨k, hk⟩ := hrm_odd
        omega
      have : IsSimpleGroup (PSL2MatrixGroup (GaloisField r m)) :=
        BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hK]; omega))
          (Or.inr (by rw [hK]; omega))
      have : IsSimpleGroup ι.range := e.isSimpleGroup
      have h1 := Q_card_of_simple ι ψ hψ hker this hnc
      rw [Nat.card_congr e.toEquiv, MaxUp.card_psl2_odd hK hr2, hQcard] at h1
      have hq : Nat.card F' = r ^ m := eq_of_psl_card hF'2 (by omega) h1.symm
      have h5 : r ^ m = 5 := by
        rcases hF' with ⟨n, -, hn⟩ | ⟨-, h5⟩
        · exfalso
          have : r ∣ p ^ n := by rw [← hn, hq]; exact dvd_pow_self r hm0
          exact hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp).mp (hr.out.dvd_of_dvd_pow this))
        · rw [← hq, h5]
      have hrr : r = 5 := by
        have : r ∣ 5 := h5 ▸ dvd_pow_self r hm0
        exact (Nat.prime_dvd_prime_iff_eq hr.out (by norm_num)).mp this
      refine ⟨fun x => ?_, fun _ => by rw [hq, h5]⟩
      rcases hz (e ⟨ι x, hmem x⟩) with h | h | h
      · have h' := hpowe x r h
        rw [hrr] at h'
        exact Or.inr (Or.inr h')
      · have h' := hpowe x _ h
        have hk2 : (r ^ m - 1) / Nat.gcd (r ^ m - 1) 2 = 2 := by rw [h5]; norm_num
        rw [hk2] at h'
        exact Or.inl h'
      · have h' := hpowe x _ h
        have hk2 : (r ^ m + 1) / Nat.gcd (r ^ m - 1) 2 = 3 := by rw [h5]; norm_num
        rw [hk2] at h'
        exact Or.inr (Or.inl h')
  ·
    exfalso
    have hchar : ringChar (GaloisField r m) ≠ 2 := by
      rw [ringChar.eq (GaloisField r m) r]
      exact hr2
    exact (false_of_exp_two_hom ι e (pglSq (GaloisField r m)) sqrQuot_sq
      (pglSq_nontrivial _ hchar) hgen hS').elim

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick
