module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Regular
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Torus
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCycle

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.AGLEmbedding.LinearThreeKit CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

theorem exists_monomial {S S' r : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) {d x : Fin 3 → K} (hd : Function.Injective d)
    (hS : ∀ i, S *ᵥ b i = d i • b i) (hS' : ∀ i, S' *ᵥ b i = x i • b i)
    (hrS : S' * r = r * S) (hrinj : ∀ v, r *ᵥ v = 0 → v = 0) :
    ∃ (π : Equiv.Perm (Fin 3)) (γ : Fin 3 → K), (∀ j, γ j ≠ 0) ∧
      ∀ j, r *ᵥ b j = γ j • b (π j) := by
  have hcoef : ∀ j, ∃ γ : Fin 3 → K, ∑ l, γ l • b l = r *ᵥ b j ∧
      ∀ l, γ l * (x l - d j) = 0 := fun j => by
    obtain ⟨γ, hγ⟩ := exists_sum_smul_eq hb (r *ᵥ b j)
    refine ⟨γ, hγ, coeff_mul_sub_eq_zero hb hS' ?_⟩
    rw [hγ, Matrix.mulVec_mulVec, hrS, ← Matrix.mulVec_mulVec, hS, Matrix.mulVec_smul]
  choose γ hγ hγx using hcoef
  have hne : ∀ j, ∃ l, γ j l ≠ 0 := fun j => by
    by_contra hall
    push Not at hall
    have : r *ᵥ b j = 0 := by
      rw [← (hγ j)]; exact Finset.sum_eq_zero fun l _ => by rw [hall l, zero_smul]
    exact hb.ne_zero j (hrinj _ this)
  choose p hp using hne
  have hpx : ∀ j, x (p j) = d j := fun j =>
    sub_eq_zero.mp ((mul_eq_zero.mp (hγx j (p j))).resolve_left (hp j))
  have hpinj : Function.Injective p := fun j j' h => hd (by rw [← hpx j, ← hpx j', h])
  have hpsurj : Function.Surjective p := Finite.injective_iff_surjective.mp hpinj
  let π : Equiv.Perm (Fin 3) := Equiv.ofBijective p ⟨hpinj, hpsurj⟩
  refine ⟨π, fun j => γ j (p j), fun j => hp j, fun j => ?_⟩
  rw [← hγ j, Finset.sum_eq_single (p j)]
  · rfl
  · intro l _ hl
    by_cases hz : γ j l = 0
    · rw [hz, zero_smul]
    · exfalso
      obtain ⟨j', rfl⟩ := hpsurj l
      have h1 := (mul_eq_zero.mp (hγx j (p j'))).resolve_left hz
      have : d j' = d j := by rw [← hpx j']; exact sub_eq_zero.mp h1
      exact hl (by rw [hd this])
  · intro h; exact absurd (Finset.mem_univ _) h

theorem perm_three_cycle (π : Equiv.Perm (Fin 3)) (h3 : π ^ 3 = 1) (h1 : π ≠ 1) :
    (π 0 = 1 ∧ π 1 = 2 ∧ π 2 = 0) ∨ (π 0 = 2 ∧ π 1 = 0 ∧ π 2 = 1) := by
  revert π; decide

theorem mem_scalars_of_commute_monomial {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {s : SpecialLinearGroup (Fin 3) K} {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2) {c : ℕ} {hc : 0 < c}
    {r d : SpecialLinearGroup (Fin 3) K}
    (hrs : r * s * r⁻¹ ∈ diagSub b c hc) (hrk : ∃ k : ℕ, r ^ 3 ^ k = 1)
    (hrdiag : ¬ ∃ x : Fin 3 → K, ∀ i, (r : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = x i • b i)
    (hd : d ∈ diagSub b c hc) (hcomm : r * d = d * r) : d ∈ scalars 3 K := by
  obtain ⟨x, -, hx⟩ := hrs
  obtain ⟨δ, hδc, hδ⟩ := hd
  obtain ⟨k, hk⟩ := hrk
  let dd : Fin 3 → K := ![1, ω, ω ^ 2]
  have hdd : Function.Injective dd := cubeRoots_injective hω1 hω3
  have hS : ∀ i, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = dd i • b i := by
    refine forall_fin_three ?_ ?_ ?_
    · show _ = (1 : K) • b 0
      rw [one_smul]; exact hb0
    · exact hb1
    · exact hb2
  have hrS : ((r * s * r⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (r : Matrix (Fin 3) (Fin 3) K) = (r : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K) := by
    have h : r * s * r⁻¹ * r = r * s := by group
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
    simpa only [SpecialLinearGroup.coe_mul] using this
  have hrinj : ∀ v, (r : Matrix (Fin 3) (Fin 3) K) *ᵥ v = 0 → v = 0 := fun v hv => by
    have := inv_mulVec_mulVec r v
    rw [hv, Matrix.mulVec_zero] at this
    exact this.symm
  obtain ⟨π, γ, hγ, hπ⟩ := exists_monomial hb hdd hS hx hrS hrinj
  have hrpow : ∀ (n : ℕ) (j : Fin 3), ∃ c : K, c ≠ 0 ∧
      (r : Matrix (Fin 3) (Fin 3) K) ^ n *ᵥ b j = c • b ((π ^ n) j) := by
    intro n
    induction n with
    | zero => intro j; exact ⟨1, one_ne_zero, by simp⟩
    | succ n ih =>
      intro j
      obtain ⟨c, hc0, hc⟩ := ih j
      refine ⟨c * γ ((π ^ n) j), mul_ne_zero hc0 (hγ _), ?_⟩
      rw [pow_succ', ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hπ, smul_smul, pow_succ',
        Equiv.Perm.mul_apply]
  have hπN : π ^ 3 ^ k = 1 := by
    refine Equiv.ext fun j => ?_
    obtain ⟨c, hc0, hc⟩ := hrpow (3 ^ k) j
    have hk' : (r : Matrix (Fin 3) (Fin 3) K) ^ 3 ^ k = 1 := coe_pow_eq_one hk
    rw [hk', Matrix.one_mulVec] at hc
    by_contra hne
    have hne' : (π ^ 3 ^ k) j ≠ j := fun h => hne (by rw [h]; rfl)
    have hli := Fintype.linearIndependent_iff.mp hb (Pi.single j 1 - Pi.single ((π ^ 3 ^ k) j) c)
      (by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
        simp [Pi.single_apply, hc])
    have := hli j
    simp [Ne.symm hne'] at this
  have hπ3 : π ^ 3 = 1 := by
    have h1 : orderOf π ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hπN
    have h6 : orderOf π ∣ 6 := by
      have := orderOf_dvd_natCard π
      rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at this
    obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have hj1 : j ≤ 1 := by
      by_contra hj2
      push Not at hj2
      rw [hord] at h6
      have : 3 ^ 2 ∣ 6 := dvd_trans (pow_dvd_pow 3 hj2) h6
      omega
    have : orderOf π ∣ 3 := by
      rw [hord]; interval_cases j <;> simp
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hπ1 : π ≠ 1 := fun h => hrdiag ⟨fun j => γ j, fun j => by rw [hπ, h]; rfl⟩
  have hδπ : ∀ j, δ (π j) = δ j := fun j => by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ b j)
      (congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hcomm)
    simp only [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hδ, Matrix.mulVec_smul, hπ,
      smul_smul] at h
    have h' := smul_left_injective K (hb.ne_zero (π j)) h
    exact mul_left_cancel₀ (hγ j) (by rw [← h', mul_comm])
  have hδ0 : ∀ i, δ i ≠ 0 := fun i h0 => by
    have := hδc i
    rw [h0, zero_pow hc.ne'] at this
    exact zero_ne_one this
  have hconst : δ 1 = δ 0 ∧ δ 2 = δ 0 := by
    rcases perm_three_cycle π hπ3 hπ1 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · have a0 := hδπ 0
      have a1 := hδπ 1
      rw [h0] at a0
      rw [h1] at a1
      exact ⟨a0, a1.trans a0⟩
    · have a0 := hδπ 0
      have a1 := hδπ 1
      rw [h0] at a0
      rw [h1] at a1
      exact ⟨a1.symm, a0⟩
  have hdsc : (d : Matrix (Fin 3) (Fin 3) K) = (δ 0) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    refine eq_of_mulVec_eq hb fun i => ?_
    rw [hδ i, Matrix.smul_mulVec, Matrix.one_mulVec]
    congr 1
    fin_cases i
    · rfl
    · exact hconst.1
    · exact hconst.2
  have hcube : δ 0 ^ 3 = 1 := by
    have := d.2
    rw [hdsc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
    exact this
  refine ⟨Units.mk0 (δ 0) (hδ0 0), by ext; simpa using hcube, ?_⟩
  rw [hdsc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  rfl


theorem mem_diagSub_of_comm {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    {s g : SpecialLinearGroup (Fin 3) K} {r : Fin 3 → K} (hr : Function.Injective r)
    (hs : ∀ i, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = r i • b i) (hgs : g * s = s * g)
    {c : ℕ} (hc : 0 < c) (hgc : g ^ c = 1) : g ∈ diagSub b c hc := by
  have hcomm : (g : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K) =
      (s : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun h : SpecialLinearGroup (Fin 3) K => (h : Matrix (Fin 3) (Fin 3) K)) hgs
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  have hex := fun i => exists_mulVec_eq_smul_of_commute hb hs hr hcomm i
  choose a ha using hex
  refine ⟨a, fun i => ?_, ha⟩
  have h1 := pow_mulVec_of_mulVec_eq_smul (ha i) c
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) ^ c = 1 := by
    have := congrArg (fun h : SpecialLinearGroup (Fin 3) K => (h : Matrix (Fin 3) (Fin 3) K)) hgc
    simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] using this
  rw [h2, Matrix.one_mulVec] at h1
  exact (smul_left_injective K (hb.ne_zero i) ((one_smul K (b i)).trans h1)).symm

end CFSG.HardMathSupport.Curtis.Coordinator
