module

public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeFrattini
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeOrbit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralTypeCenter

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

open Subgroup
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism quotientAutomorphism_apply)

theorem eq_seven_of_prime_dvd_168 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h : r ∣ 168) : r = 7 := by
  have h168 : (168 : ℕ) = 2 * 2 * 2 * (3 * 7) := by norm_num
  rw [h168] at h
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3; omega
      · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h2; omega
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h2

theorem apply_mem_of_pow_apply_mem {W : Type} [Group W] {σ : MulAut W} (h7 : σ ^ 7 = 1)
    {P : Set W} {k : ℕ} (hk0 : 0 < k) (hk7 : k < 7) (hP : ∀ x ∈ P, (σ ^ k) x ∈ P) :
    ∀ x ∈ P, σ x ∈ P := by
  have hm : ∀ k < 7, 0 < k → ∃ m < 7, k * m % 7 = 1 := by decide
  obtain ⟨m, -, hmk⟩ := hm k hk7 hk0
  have hdiv : k * m = 7 * (k * m / 7) + 1 := by
    have := Nat.div_add_mod (k * m) 7
    omega
  have hσ : σ = (σ ^ k) ^ m := by
    rw [← pow_mul, hdiv, pow_succ, pow_mul, h7, one_pow, one_mul]
  have hiter : ∀ n : ℕ, ∀ x ∈ P, ((σ ^ k) ^ n) x ∈ P := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', MulAut.mul_apply]
      exact hP _ (ih x hx)
  intro x hx
  rw [hσ]
  exact hiter m x hx

theorem centralizes_of_frattini_bounds {A : Type} [Group A] [Finite A] (R : Subgroup A)
    (hR : IsPGroup 2 R) {g : A} (hgN : g ∈ Subgroup.normalizer (R : Set A)) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hord : orderOf g = r)
    (hV8 : Nat.card (↥R ⧸ frattini ↥R) ≤ 8)
    (hV4 : (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → Nat.card (↥R ⧸ frattini ↥R) ≤ 4)
    (hM : Nat.card (↥R ⧸ frattini ↥R) = 8 →
      ∃ M : Subgroup A, M ≤ R ∧ (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ M.relIndex R = 2) :
    ∀ y ∈ R, g * y = y * g := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd_r : Odd r := hr.odd_of_ne_two (by omega)
  obtain ⟨-, hcomm, hpow, -, d, hcard, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hR
  have hcomm' : ∀ a b : ↥R ⧸ frattini ↥R, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  by_contra hcon
  push Not at hcon
  obtain ⟨y0, hy0R, hy0⟩ := hcon
  set τ : MulAut ↥R := R.normalizerMonoidHom ⟨g, hgN⟩ with hτdef
  have hτapp : ∀ x : ↥R, ((τ x : ↥R) : A) = g * x * g⁻¹ := fun x => by
    simp [hτdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hτr : τ ^ r = 1 := by
    have hgr : (⟨g, hgN⟩ : normalizer (R : Set A)) ^ r = 1 := by
      apply Subtype.ext
      simpa [hord] using pow_orderOf_eq_one g
    rw [hτdef, ← map_pow, hgr, map_one]
  have hτne : τ ≠ 1 := by
    intro h1
    apply hy0
    have h2 := hτapp ⟨y0, hy0R⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 : g * y0 * g⁻¹ = y0 := h2.symm
    calc g * y0 = (g * y0 * g⁻¹) * g := by simp
      _ = y0 * g := by rw [h3]
  set σ : MulAut (↥R ⧸ frattini ↥R) := quotientAutomorphism (frattini ↥R) τ with hσdef
  have hσr : σ ^ r = 1 := by rw [hσdef, ← map_pow, hτr, map_one]
  have hσne : σ ≠ 1 := by
    intro hσ1
    have hker : τ ∈ (quotientAutomorphism (frattini ↥R)).ker := by
      rw [MonoidHom.mem_ker]
      exact hσ1
    have hPker := CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup
      2 hR
    have hodd : Odd (orderOf τ) :=
      Odd.of_dvd_nat hodd_r (orderOf_dvd_of_pow_eq_one hτr)
    exact hτne
      (CFSG.Assembly.Dichotomy.CentralizerContainment.eq_one_of_mem_of_odd_orderOf hPker hker hodd)
  have hσord : orderOf σ = r := by
    haveI := Fact.mk hr
    exact orderOf_eq_prime hσr hσne
  have hrdvd : r ∣ Nat.card (MulAut (↥R ⧸ frattini ↥R)) := hσord ▸ orderOf_dvd_natCard σ
  have hd3 : d ≤ 3 := by
    by_contra hd
    have h16 : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h16
    rw [hcard] at hV8
    omega
  rcases Nat.lt_or_ge d 3 with hd2 | hd3'
  ·
    have h6 := card_mulAut_dvd_six hcomm' hpow hcard (by omega)
    have hr6 : r ∣ 6 := dvd_trans hrdvd h6
    have hle := Nat.le_of_dvd (by norm_num) hr6
    interval_cases r
    · exact absurd hr6 (by norm_num)
    · exact absurd hr (by norm_num)
  · have hd : d = 3 := by omega
    subst hd
    have hcard8 : Nat.card (↥R ⧸ frattini ↥R) = 8 := by rw [hcard]; norm_num
    have hAut168 : Nat.card (MulAut (↥R ⧸ frattini ↥R)) = 168 :=
      card_mulAut_eq_168 hcomm' hpow hcard
    have hr7 : r = 7 := eq_seven_of_prime_dvd_168 hr hr5 (hAut168 ▸ hrdvd)
    subst hr7
    have hσ7 : σ ^ 7 = 1 := hσr
    obtain ⟨M, hMR, hMab, hMidx⟩ := hM hcard8
    set M'' : Subgroup ↥R := M.subgroupOf R with hM''def
    have hM''idx : M''.index = 2 := hMidx
    have hM''ab : ∀ a ∈ M'', ∀ b ∈ M'', a * b = b * a := by
      intro a ha b hb
      apply Subtype.ext
      exact hMab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
    have hM''cop : IsCoatom M'' :=
      Subgroup.isCoatom_of_index_prime (by rw [hM''idx]; exact Nat.prime_two)
    have hΦM : frattini ↥R ≤ M'' := frattini_le_coatom hM''cop
    have hRnonab : ¬ ∀ a b : ↥R, a * b = b * a := fun h => by
      have h4 := hV4 (fun a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩))
      omega
    by_cases hinv : ∀ x : ↥R, x ∈ M'' → τ x ∈ M''
    ·
      set K : Subgroup (↥R ⧸ frattini ↥R) := M''.map (QuotientGroup.mk' (frattini ↥R)) with hK
      have hmapidx : (M''.map (QuotientGroup.mk' (frattini ↥R))).index = M''.index :=
        Subgroup.index_map_eq M'' (QuotientGroup.mk'_surjective _)
          (by rw [QuotientGroup.ker_mk']; exact hΦM)
      have hKidx : K.index = 2 := by
        rw [hK, hmapidx, hM''idx]
      have hKcard : Nat.card K = 4 := by
        have h := Subgroup.card_mul_index K
        rw [hKidx, hcard8] at h
        omega
      have hKne : ∃ v ∈ K, v ≠ 1 := by
        by_contra hc
        push Not at hc
        have hMΦ : M'' ≤ frattini ↥R := fun x hx => by
          have hmem : (QuotientGroup.mk' (frattini ↥R) x : ↥R ⧸ frattini ↥R) ∈ K :=
            Subgroup.mem_map_of_mem _ hx
          exact (QuotientGroup.eq_one_iff x).mp (hc _ hmem)
        have hdiv := Subgroup.index_dvd_of_le hMΦ
        rw [hM''idx] at hdiv
        have h8 : (frattini ↥R).index = 8 := hcard8
        rw [h8] at hdiv
        norm_num at hdiv
      have hKinv : ∀ v ∈ (K : Set (↥R ⧸ frattini ↥R)), σ v ∈ (K : Set (↥R ⧸ frattini ↥R)) := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
        rw [SetLike.mem_coe, hσdef, quotientAutomorphism_apply]
        exact Subgroup.mem_map_of_mem _ (hinv x hx)
      have h7le := card_invariant_ge_seven hcard8 hσ7 hσne hKinv hKne
      have hKcoe : Nat.card (K : Set (↥R ⧸ frattini ↥R)) = Nat.card K := rfl
      omega
    ·
      push Not at hinv
      obtain ⟨x₀, hx₀, hτx₀⟩ := hinv
      have hpowmod : ∀ n : ℕ, τ ^ n = τ ^ (n % 7) := by
        intro n
        conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, hτr, one_pow, one_mul]
      let N : Fin 4 → Subgroup ↥R := fun k => M''.map (MulEquiv.toMonoidHom (τ ^ (k : ℕ)))
      have hNidx : ∀ k, (N k).index = 2 := fun k => by
        show (M''.map (MulEquiv.toMonoidHom (τ ^ (k : ℕ)))).index = 2
        exact (Subgroup.index_map_equiv (H := M'') (τ ^ (k : ℕ) : ↥R ≃* ↥R)).trans hM''idx
      have hNab : ∀ k, ∀ a ∈ N k, ∀ b ∈ N k, a * b = b * a := by
        intro k a ha b hb
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
        rw [← map_mul, ← map_mul, hM''ab x hx y hy]
      have hNinj : Function.Injective N := by
        intro j k hjk
        by_contra hjk'
        have hjk'' : (j : ℕ) ≠ (k : ℕ) := fun h => hjk' (Fin.ext h)
        have hjk4 : (j : ℕ) < 4 := j.isLt
        have hkk4 : (k : ℕ) < 4 := k.isLt
        have hmap : ∀ x ∈ M'', (τ ^ (7 - (k : ℕ) + (j : ℕ))) x ∈ M'' := by
          intro x hx
          have hxj : (τ ^ (j : ℕ)) x ∈ N j :=
            Subgroup.mem_map_of_mem (MulEquiv.toMonoidHom (τ ^ (j : ℕ))) hx
          rw [hjk] at hxj
          obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hxj
          have hyeq' : (τ ^ (k : ℕ)) y = (τ ^ (j : ℕ)) x := hyeq
          have hcancel : (τ ^ (7 - (k : ℕ))) ((τ ^ (k : ℕ)) y) = y := by
            rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel (show (k : ℕ) ≤ 7 by omega),
              hτr, MulAut.one_apply]
          have hy_eq : (τ ^ (7 - (k : ℕ) + (j : ℕ))) x = y := by
            rw [← hcancel, hyeq', ← MulAut.mul_apply, ← pow_add]
          rw [hy_eq]
          exact hy
        have hm0 : 0 < (7 - (k : ℕ) + (j : ℕ)) % 7 := by omega
        have hm7 : (7 - (k : ℕ) + (j : ℕ)) % 7 < 7 := Nat.mod_lt _ (by norm_num)
        have hP' : ∀ x ∈ M'', (τ ^ ((7 - (k : ℕ) + (j : ℕ)) % 7)) x ∈ M'' := by
          intro x hx
          rw [← hpowmod]
          exact hmap x hx
        exact hτx₀ (apply_mem_of_pow_apply_mem (P := (M'' : Set ↥R)) hτr hm0 hm7 hP' x₀ hx₀)
      exact hRnonab (commutative_of_four_abelian_index_two N hNab hNidx hNinj)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType
