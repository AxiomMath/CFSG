module

public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin

@[expose] def CenterExp (K : Type*) [Group K] (k : ℕ) : Prop :=
  ∀ z ∈ Subgroup.center K, z ^ (2 ^ k) = 1

theorem CenterExp.isPGroup {K : Type*} [Group K] {k : ℕ} (h : CenterExp K k) :
    IsPGroup 2 (Subgroup.center K) := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : K) ^ (2 ^ k) = 1 := h g g.2
  have : g ^ (2 ^ k) = 1 := Subtype.ext hg
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one this)
  exact ⟨i, hi⟩

theorem CenterExp.of_mulEquiv {K K' : Type*} [Group K] [Group K'] {k : ℕ} (e : K ≃* K')
    (h : CenterExp K' k) : CenterExp K k := by
  intro z hz
  have hz' : e z ∈ Subgroup.center K' := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  apply e.injective
  rw [map_pow, h _ hz', map_one]

theorem pow_eq_one_of_mem_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Finite F] {k : ℕ} (hk : Nat.card F = 2 ^ k + 1) {g : GL ι F}
    (hg : g ∈ StatedScalars ι F) : g ^ (2 ^ k) = 1 := by
  obtain ⟨u, rfl⟩ := hg
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [← map_pow]
  have hu : u ^ (2 ^ k) = 1 := by
    have h1 : u ^ Fintype.card Fˣ = 1 := pow_card_eq_one
    rwa [Fintype.card_units, Fintype.card_eq_nat_card, hk, Nat.add_sub_cancel] at h1
  rw [hu, map_one]

theorem centerExp_specialLinear (m k : ℕ) (F : Type) [Field F] [Finite F]
    (hk : Nat.card F = 2 ^ k + 1) :
    CenterExp (Matrix.SpecialLinearGroup (Fin (m + 1)) F) k := by
  intro z hz
  obtain ⟨r, hr, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (Nat.succ_ne_zero m)] at hr
    exact zero_ne_one hr
  have : Fintype F := Fintype.ofFinite F
  have hrk : r ^ (2 ^ k) = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [Fintype.card_eq_nat_card, hk, Nat.add_sub_cancel] at h1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hz', ← map_pow, hrk, map_one]
  rfl

theorem centerExp_statedSp (n k : ℕ) (F : Type) [Field F] [Finite F]
    (hk : Nat.card F = 2 ^ k + 1) : CenterExp (StatedSp n F) k := by
  intro z hz
  rw [Symplectic.center_eq n F] at hz
  exact Subtype.ext (by
    simpa using pow_eq_one_of_mem_statedScalars hk (Subgroup.mem_subgroupOf.mp hz))

theorem centerExp_unitary {F : Type} [Field F] [Finite F] {p f n k : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n) (hnq : (n, p ^ f) ≠ (3, 2))
    (hk : Nat.card F = 2 ^ k + 1) :
    CenterExp (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F p f) n) k := by
  refine CenterExp.of_mulEquiv (Unitary.equivStatedSU hF n) ?_
  intro z hz
  rw [(Unitary.isQuasisimple_statedSU_of_card hF hn hnq).2] at hz
  exact Subtype.ext (by
    simpa using pow_eq_one_of_mem_statedScalars hk (Subgroup.mem_subgroupOf.mp hz))

theorem centerExp_spin {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K] [Finite K]
    (Q : QuadraticForm K (σ → K)) {k : ℕ} (hk : Nat.card K = 2 ^ k + 1)
    (hcen : Subgroup.center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q))
    (hker : ∀ x ∈ (spinMatrix Q).ker, x ^ 2 = 1) : CenterExp (spinGroup Q) (k + 1) := by
  intro z hz
  have h1 : (spinMatrix Q z) ^ (2 ^ k) = 1 :=
    pow_eq_one_of_mem_statedScalars hk (Subgroup.mem_comap.mp (hcen hz))
  have h2 : z ^ (2 ^ k) ∈ (spinMatrix Q).ker := by
    rw [MonoidHom.mem_ker, map_pow, h1]
  rw [pow_succ, pow_mul]
  exact hker _ h2

theorem sq_eq_one_of_ker {K : Type} [Field K] {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q : QuadraticForm K (σ → K)}
    (hker : ∀ x : spinGroup Q, x ∈ (spinMatrix Q).ker ↔
      x = 1 ∨ (x : CliffordAlgebra Q) = -1) :
    ∀ x ∈ (spinMatrix Q).ker, x ^ 2 = 1 := by
  intro x hx
  rcases (hker x).1 hx with rfl | h
  · exact one_pow _
  · apply Subtype.ext
    show (x : CliffordAlgebra Q) ^ 2 = 1
    rw [h, neg_one_sq]

theorem centerExp_spinOdd {n k : ℕ} {F : Type} [Field F] [Finite F] (hn : 3 ≤ n)
    (hk : Nat.card F = 2 ^ k + 1) (h2 : (2 : F) ≠ 0) :
    CenterExp (spinGroup (quadOdd n F)) (k + 1) := by
  refine centerExp_spin _ hk ?_ (sq_eq_one_of_ker (mem_ker_spinMatrix_quadOdd_iff h2))
  rw [← (spinToStatedProj_quadOdd h2 hn).2.1, (spinToStatedProj_quadOdd h2 hn).2.2]

theorem centerExp_spinPlus {n k : ℕ} {F : Type} [Field F] [Finite F] (hn : 3 ≤ n)
    (hk : Nat.card F = 2 ^ k + 1) : CenterExp (spinGroup (quadPlus n F)) (k + 1) := by
  refine centerExp_spin _ hk ?_ (sq_eq_one_of_ker mem_ker_spinMatrix_quadPlus_iff)
  rw [← (spinToStatedProj_quadPlus (K := F) hn).2.1, (spinToStatedProj_quadPlus (K := F) hn).2.2]

theorem centerExp_spinMinus {n k : ℕ} {F : Type} [Field F] [Finite F] {b c : F} (hn : 4 ≤ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hk : Nat.card F = 2 ^ k + 1) :
    CenterExp (spinGroup (quadMinus n F b c)) (k + 1) := by
  refine centerExp_spin _ hk ?_ (sq_eq_one_of_ker (mem_ker_spinMatrix_quadMinus_iff hirr))
  rw [← (spinToStatedProj_quadMinus hn hirr).2.1, (spinToStatedProj_quadMinus hn hirr).2.2]

theorem centerExp_of_eq {t : StatedLieTag} {n p f : ℕ} {hp : p.Prime} {U : LieUniversal} {k : ℕ}
    (h : modelUniv t n p f hp = U) (hU : CenterExp U.K k) :
    CenterExp (modelUniv t n p f hp).K k := by
  subst h
  exact hU

section Models

variable {p f : ℕ} [hpf : Fact p.Prime]

theorem centerExp_model_PSL {n k : ℕ} (hn : 1 ≤ n) (hk : Nat.card (GaloisField p f) = 2 ^ k + 1) :
    CenterExp (modelUniv .PSL n p f hpf.out).K k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact centerExp_specialLinear m k (GaloisField p f) hk

theorem centerExp_model_PSp {n k : ℕ} (hk : Nat.card (GaloisField p f) = 2 ^ k + 1) :
    CenterExp (modelUniv .PSp n p f hpf.out).K k :=
  centerExp_statedSp n k (GaloisField p f) hk

theorem centerExp_model_PSU {n k : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) (hnq : (n, p ^ f) ≠ (3, 2))
    (hk : Nat.card (GaloisField p (2 * f)) = 2 ^ k + 1) :
    CenterExp (modelUniv .PSU n p f hpf.out).K k := by
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  refine centerExp_of_eq (U := ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
    (GaloisField p (2 * f)) p f) n, Unitary.rootDatum hF n⟩) ?_ ?_
  · simp only [modelUniv, lieUniversal, hf, ↓reduceDIte]
  · exact centerExp_unitary hF hn hnq hk

private theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : GaloisField p f) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)

theorem centerExp_model_POmegaOdd {n k : ℕ} (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (hk : Nat.card (GaloisField p f) = 2 ^ k + 1) :
    CenterExp (modelUniv .POmegaOdd n p f hpf.out).K (k + 1) :=
  centerExp_spinOdd hn hk (two_ne_zero_of_ne_two hp2)

theorem centerExp_model_POmegaPlus {n k : ℕ} (hn : 3 ≤ n)
    (hk : Nat.card (GaloisField p f) = 2 ^ k + 1) :
    CenterExp (modelUniv .POmegaPlus n p f hpf.out).K (k + 1) := by
  refine centerExp_of_eq (U := ⟨spinGroup (quadPlus n (GaloisField p f)),
    plusDatum n (GaloisField p f) hn⟩) ?_ ?_
  · simp only [modelUniv, lieUniversal, hn, ↓reduceDIte]
  · exact centerExp_spinPlus hn hk

theorem centerExp_model_POmegaMinus {n k : ℕ} (hn : 4 ≤ n)
    (hk : Nat.card (GaloisField p f) = 2 ^ k + 1) :
    CenterExp (modelUniv .POmegaMinus n p f hpf.out).K (k + 1) :=
  centerExp_spinMinus hn (minusCoeffs_irr p f) hk

end Models

end CFSG.ClassicalInvolution.Q3
