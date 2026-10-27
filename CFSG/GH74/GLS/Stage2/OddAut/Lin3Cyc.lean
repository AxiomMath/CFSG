module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Basic
public import CFSG.GroupTheory.WeirSylow.GL

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open CFSG.GroupTheory.WeirSylow Matrix

section Sigma

theorem isCyclic_wreathTower_zero (p a : ℕ) (n : ℕ) (hn : n = 0) :
    IsCyclic (wreathTower p (Multiplicative (ZMod (p ^ a))) n) := by
  subst hn
  exact inferInstanceAs (IsCyclic (Multiplicative (ZMod (p ^ a))))

theorem isCyclic_sigmaModel_of_div_eq_one {p e a N : ℕ} (hp : 1 < p) (h : N / e = 1) :
    IsCyclic (sigmaModel p e a N) := by
  have hD : Nat.digits p (N / e) = [1] := by rw [h]; exact Nat.digits_of_lt p 1 one_ne_zero hp
  have hall : ∀ x ∈ Nat.digits p (N / e), x = 1 := by rw [hD]; simp
  have hlen : (Nat.digits p (N / e)).length = 1 := by rw [hD]; rfl
  have : Unique (Fin (Nat.digits p (N / e)).length) := by
    rw [hlen]; exact inferInstanceAs (Unique (Fin 1))
  let e1 := MulEquiv.piUnique (fun i : Fin (Nat.digits p (N / e)).length =>
    Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) ↑i)
  have hd : (Nat.digits p (N / e))[(default : Fin (Nat.digits p (N / e)).length)] = 1 :=
    hall _ (List.getElem_mem _)
  have : Unique (Fin (Nat.digits p (N / e))[(default : Fin (Nat.digits p (N / e)).length)]) := by
    rw [hd]; exact inferInstanceAs (Unique (Fin 1))
  let e2 := MulEquiv.funUnique
    (Fin (Nat.digits p (N / e))[(default : Fin (Nat.digits p (N / e)).length)])
    (wreathTower p (Multiplicative (ZMod (p ^ a))) ↑(default : Fin (Nat.digits p (N / e)).length))
  have hdef : ((default : Fin (Nat.digits p (N / e)).length) : ℕ) = 0 := by
    have := (default : Fin (Nat.digits p (N / e)).length).isLt
    omega
  have hcyc := isCyclic_wreathTower_zero p a _ hdef
  exact (MulEquiv.isCyclic (e1.trans e2)).mpr hcyc

theorem isCyclic_sigmaModel_of_div_eq_zero {p e a N : ℕ} (h : N / e = 0) :
    IsCyclic (sigmaModel p e a N) := by
  have hlen : (Nat.digits p (N / e)).length = 0 := by rw [h]; simp
  have : IsEmpty (Fin (Nat.digits p (N / e)).length) := by
    rw [hlen]; infer_instance
  have : Subsingleton (sigmaModel p e a N) :=
    inferInstanceAs (Subsingleton ((i : Fin (Nat.digits p (N / e)).length) →
      Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) ↑i))
  exact isCyclic_of_subsingleton

theorem isCyclic_sigmaModel_of_div_le_one {p e a N : ℕ} (hp : 1 < p) (h : N / e ≤ 1) :
    IsCyclic (sigmaModel p e a N) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · exact isCyclic_sigmaModel_of_div_eq_zero h0
  · exact isCyclic_sigmaModel_of_div_eq_one hp h1

end Sigma

section Sylow

variable {K : Type} [Field K] [Fintype K]

theorem isCyclic_sylow_gl3 {r : ℕ} [Fact r.Prime] (hr2 : Odd r) (hrK : ¬ r ∣ Fintype.card K)
    (hrK1 : ¬ r ∣ Fintype.card K - 1) (P : Sylow r (GL (Fin 3) K)) : IsCyclic P := by
  obtain ⟨φ⟩ := sylow_GL hr2 K hrK 3 P
  set e := orderOf (Fintype.card K : ZMod r) with he
  have he1 : e ≠ 1 := by
    intro h1
    rw [he, orderOf_eq_one_iff, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h1
    apply hrK1
    have hq : 1 ≤ Fintype.card K := Fintype.card_pos
    exact (Nat.modEq_iff_dvd' hq).mp h1.symm
  have hdiv : 3 / e ≤ 1 := by
    by_cases he0 : e = 0
    · simp [he0]
    · have h2 : 2 ≤ e := by omega
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
  exact (MulEquiv.isCyclic φ).mpr (isCyclic_sigmaModel_of_div_le_one (Fact.out : r.Prime).one_lt hdiv)

end Sylow

section Main

variable {K : Type} [Field K] [Finite K]

theorem mem_closure_pair_pow {G : Type*} [Group G] {a b : G} (hab : a * b = b * a) {r : ℕ}
    (hr : 0 < r) (ha : a ^ r = 1) (hb : b ^ r = 1) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ i j : ℕ, x = a ^ i * b ^ j := by
  have hc : Commute a b := hab
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    refine ⟨i + k, j + l, ?_⟩
    have h1 : b ^ j * a ^ k = a ^ k * b ^ j := (Commute.pow_pow hc k j).eq.symm
    rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ j), h1]
    group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨(r - 1) * i, (r - 1) * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have h1 : b ^ j * a ^ ((r - 1) * i) = a ^ ((r - 1) * i) * b ^ j :=
      (Commute.pow_pow hc ((r - 1) * i) j).eq.symm
    have e1 : i + (r - 1) * i = r * i := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp; ring
    have e2 : j + (r - 1) * j = r * j := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp; ring
    calc a ^ i * b ^ j * (a ^ ((r - 1) * i) * b ^ ((r - 1) * j))
        = a ^ i * (b ^ j * a ^ ((r - 1) * i)) * b ^ ((r - 1) * j) := by group
      _ = a ^ i * (a ^ ((r - 1) * i) * b ^ j) * b ^ ((r - 1) * j) := by rw [h1]
      _ = a ^ (i + (r - 1) * i) * b ^ (j + (r - 1) * j) := by rw [pow_add, pow_add]; group
      _ = 1 := by rw [e1, e2, pow_mul, pow_mul, ha, hb]; simp

theorem eq_of_dvd_add_sub {r i i' : ℕ} (hi : i < r) (hi' : i' < r) (h : r ∣ i + (r - i')) :
    i = i' := by
  obtain ⟨k, hk⟩ := h
  have h1 : r * k < r * 2 := by omega
  have h2 : k < 2 := Nat.lt_of_mul_lt_mul_left h1
  have h3 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have : k = 1 := by omega
  subst this
  omega

theorem comm_pow_mul {G : Type*} [Group G] {a b : G} (hab : a * b = b * a) (m n p q : ℕ) :
    a ^ m * b ^ n * (a ^ p * b ^ q) = a ^ (m + p) * b ^ (n + q) := by
  have hc : Commute a b := hab
  have h1 : b ^ n * a ^ p = a ^ p * b ^ n := (Commute.pow_pow hc p n).eq.symm
  rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ n), h1]
  group

theorem lin3_false_of_not_dvd {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : ¬ r ∣ Nat.card K)
    (hrK1 : ¬ r ∣ Nat.card K - 1) (a b : GL (Fin 3) K) (ua ub : Kˣ)
    (ha : a ^ r = GeneralLinearGroup.scalar (Fin 3) ua) (hb : b ^ r = GeneralLinearGroup.scalar (Fin 3) ub)
    (hab : a * b = b * a)
    (hind : ∀ i j : ℕ, (∃ u : Kˣ, a ^ i * b ^ j = GeneralLinearGroup.scalar (Fin 3) u) →
      r ∣ i ∧ r ∣ j) : False := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hr0 : 0 < r := hr.pos
  have hcop : Nat.Coprime (Nat.card Kˣ) r := by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 hrK1).symm
  obtain ⟨γa, hγa⟩ := (powCoprime hcop).surjective ua⁻¹
  obtain ⟨γb, hγb⟩ := (powCoprime hcop).surjective ub⁻¹
  have hγa' : γa ^ r = ua⁻¹ := hγa
  have hγb' : γb ^ r = ub⁻¹ := hγb
  set a' : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) γa * a with ha'def
  set b' : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) γb * b with hb'def
  have hab' : a' * b' = b' * a' := by
    have hc : Commute a b := hab
    have h1 : Commute a (GeneralLinearGroup.scalar (Fin 3) γb * b) :=
      (scalar_commute γb a).symm.mul_right hc
    exact (((scalar_commute γa _).mul_left h1)).eq
  have ha' : a' ^ r = 1 := by
    rw [ha'def, (scalar_commute γa a).mul_pow r, ha, ← map_pow, ← map_mul, hγa', inv_mul_cancel,
      map_one]
  have hb' : b' ^ r = 1 := by
    rw [hb'def, (scalar_commute γb b).mul_pow r, hb, ← map_pow, ← map_mul, hγb', inv_mul_cancel,
      map_one]
  have hind' : ∀ i j : ℕ, a' ^ i * b' ^ j = 1 → r ∣ i ∧ r ∣ j := by
    intro i j h
    apply hind
    refine ⟨(γa ^ i * γb ^ j)⁻¹, ?_⟩
    have e1 : a' ^ i * b' ^ j =
        GeneralLinearGroup.scalar (Fin 3) (γa ^ i * γb ^ j) * (a ^ i * b ^ j) := by
      rw [ha'def, hb'def, (scalar_commute γa a).mul_pow i, (scalar_commute γb b).mul_pow j,
        map_mul, map_pow, map_pow]
      calc GeneralLinearGroup.scalar (Fin 3) γa ^ i * a ^ i *
            (GeneralLinearGroup.scalar (Fin 3) γb ^ j * b ^ j)
          = GeneralLinearGroup.scalar (Fin 3) γa ^ i * (a ^ i * GeneralLinearGroup.scalar (Fin 3) γb ^ j) *
            b ^ j := by group
        _ = GeneralLinearGroup.scalar (Fin 3) γa ^ i * (GeneralLinearGroup.scalar (Fin 3) γb ^ j * a ^ i) *
            b ^ j := by
          rw [← (Commute.pow_pow (scalar_commute γb a) j i).eq]
        _ = _ := by group
    rw [e1] at h
    have h3 := eq_inv_of_mul_eq_one_right h
    rw [h3, ← map_inv]
  set H : Subgroup (GL (Fin 3) K) := Subgroup.closure {a', b'} with hH
  have hHr : ∀ x : H, x ^ r = 1 := by
    intro ⟨x, hx⟩
    obtain ⟨i, j, rfl⟩ := mem_closure_pair_pow hab' hr0 ha' hb' hx
    apply Subtype.ext
    show (a' ^ i * b' ^ j) ^ r = 1
    rw [(Commute.pow_pow (show Commute a' b' from hab') i j).mul_pow, ← pow_mul, ← pow_mul,
      mul_comm i r, mul_comm j r, pow_mul, pow_mul, ha', hb', one_pow, one_pow, mul_one]
  have hHp : IsPGroup r H := fun x => ⟨1, by simpa using hHr x⟩
  obtain ⟨P, hP⟩ := hHp.exists_le_sylow
  have hcyc : IsCyclic P :=
    isCyclic_sylow_gl3 hodd (by rwa [← Nat.card_eq_fintype_card])
      (by rwa [← Nat.card_eq_fintype_card]) P
  have hmem : ∀ i j : ℕ, a' ^ i * b' ^ j ∈ (P : Subgroup (GL (Fin 3) K)) := fun i j =>
    hP (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
  let Φ : Fin r × Fin r → {x : ↥(P : Subgroup (GL (Fin 3) K)) // x ^ r = 1} := fun ij =>
    ⟨⟨a' ^ (ij.1 : ℕ) * b' ^ (ij.2 : ℕ), hmem _ _⟩, by
      apply Subtype.ext
      show (a' ^ (ij.1 : ℕ) * b' ^ (ij.2 : ℕ)) ^ r = 1
      rw [(Commute.pow_pow (show Commute a' b' from hab') _ _).mul_pow, ← pow_mul, ← pow_mul,
        mul_comm (ij.1 : ℕ) r, mul_comm (ij.2 : ℕ) r, pow_mul, pow_mul, ha', hb', one_pow, one_pow,
        mul_one]⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : a' ^ (i : ℕ) * b' ^ (j : ℕ) = a' ^ (i' : ℕ) * b' ^ (j' : ℕ) :=
      congrArg (fun x => ((x.1 : ↥(P : Subgroup (GL (Fin 3) K))) : GL (Fin 3) K)) h
    have h2 : a' ^ ((i : ℕ) + (r - i')) * b' ^ ((j : ℕ) + (r - j')) = 1 := by
      rw [← comm_pow_mul hab', h1, comm_pow_mul hab']
      have e1 : (i' : ℕ) + (r - i') = r := by omega
      have e2 : (j' : ℕ) + (r - j') = r := by omega
      rw [e1, e2, ha', hb', mul_one]
    obtain ⟨d1, d2⟩ := hind' _ _ h2
    have := eq_of_dvd_add_sub i.isLt i'.isLt d1
    have := eq_of_dvd_add_sub j.isLt j'.isLt d2
    ext <;> simp_all
  have hcard := Fintype.card_le_of_injective Φ hΦ
  have hle := IsCyclic.card_pow_eq_one_le (α := ↥(P : Subgroup (GL (Fin 3) K))) (n := r) hr0
  rw [Fintype.card_subtype] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have : r * r ≤ r := hcard.trans hle
  have h3 : 3 ≤ r := by
    have := hr.two_le
    omega
  nlinarith

end Main

end CFSG.GH74.GLS.Stage2.OddAut
