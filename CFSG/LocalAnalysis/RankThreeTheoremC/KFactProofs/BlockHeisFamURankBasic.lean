module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem heisU_false_of_injective {L A : Type*} [Group L] [Group A] (hrk : OddRankLeThree L)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hcomm : ∀ x y : A, x * y = y * x)
    (hA : ∀ x : A, x ^ r = 1) (hcard : r ^ 4 ≤ Nat.card A) (ψ : A →* L)
    (hψ : Function.Injective ψ) : False := by
  have hc : IsMulCommutative ψ.range := ⟨⟨fun a b => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : L) * (b : L) = (b : L) * (a : L)
    rw [← hx, ← hy, ← map_mul, ← map_mul, hcomm]⟩⟩
  have hexp : ∀ x ∈ ψ.range, x ^ r = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, hA x, map_one]
  have h1 := hrk r hr hr2 ψ.range hc hexp
  rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at h1
  have h2 : r ^ 3 < r ^ 4 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  omega

theorem heisU_diagGL_mem_statedSU {K : Type} [Field K] {n q : ℕ} (hq : q ≠ 0) (u : Fin n → Kˣ)
    (hu : ∀ i, (u i) ^ (q + 1) = 1) (hprod : ∏ i, u i = 1) :
    diagGL n u ∈ StatedSU n q K := by
  have hdet : ((diagGL n u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [det_diagGL, ← Units.coe_prod, hprod, Units.val_one]
  have hunit : (((diagGL n u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map (· ^ q)).transpose *
      ((diagGL n u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [coe_diagGL, Matrix.diagonal_map (f := fun x : K => x ^ q) (zero_pow hq),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg Units.val (hu i)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [← pow_succ]
    exact this
  unfold StatedSU
  exact Subgroup.subset_closure ⟨hdet, hunit⟩

theorem heisU_diagGL_mem_scalars {K : Type} [Field K] {n : ℕ} {u : Fin n → Kˣ}
    (h : diagGL n u ∈ StatedScalars (Fin n) K) : ∃ s : Kˣ, ∀ i, u i = s := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun i => ?_⟩
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i) hs
  simp [coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar] at this
  exact Units.ext this.symm

def heisUVec {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) : Fin (5 + m) → G :=
  Fin.append (![c 0, c 1, c 2, c 3, (c 0 * c 1 * c 2 * c 3)⁻¹] : Fin 5 → G) (fun _ => 1)

theorem heisUVec_mul {G : Type*} [CommGroup G] (m : ℕ) (c c' : Fin 4 → G) :
    heisUVec m (c * c') = heisUVec m c * heisUVec m c' := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [heisUVec, mul_comm, mul_left_comm, mul_assoc, mul_inv]
  · simp [heisUVec]

theorem prod_heisUVec {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) :
    ∏ i, heisUVec m c i = 1 := by
  rw [Fin.prod_univ_add]
  simp [heisUVec, Fin.prod_univ_five]

theorem heisUVec_castAdd {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) (j : Fin 4) :
    heisUVec m c (Fin.castAdd m j.castSucc) = c j := by
  fin_cases j <;> simp [heisUVec]

theorem heisUVec_natAdd {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) (j : Fin m) :
    heisUVec m c (Fin.natAdd 5 j) = 1 := by
  simp [heisUVec]

theorem heisU_exists_torus {K : Type} [Field K] {n q r : ℕ} (hn : 5 ≤ n) (hq : q ≠ 0)
    (hr : r.Prime) {ζ : Kˣ} (hζ : orderOf ζ = r) (hζq : ζ ^ (q + 1) = 1) :
    ∃ ψ : (Fin 4 → Subgroup.zpowers ζ) →* StatedSU n q K, Function.Injective ψ ∧
      ((6 ≤ n ∨ ¬ r ∣ n) → ∀ c, (ψ c : GL (Fin n) K) ∈ StatedScalars (Fin n) K → c = 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
  set Z : Subgroup Kˣ := Subgroup.zpowers ζ with hZdef
  have hZcard : Nat.card Z = r := by rw [hZdef, Nat.card_zpowers, hζ]
  have hZpow : ∀ x : Z, x ^ r = 1 := fun x => by rw [← hZcard]; exact pow_card_eq_one'
  have hZq : ∀ x : Z, (x : Kˣ) ^ (q + 1) = 1 := fun x => by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_of_mem_zpowers x.2).trans (orderOf_dvd_of_pow_eq_one hζq)
  let u : (Fin 4 → Z) → Fin (5 + m) → Kˣ := fun c i => ((heisUVec (G := Z) m c i : Z) : Kˣ)
  have hu_mem : ∀ c : Fin 4 → Z, diagGL (5 + m) (u c) ∈ StatedSU (5 + m) q K := by
    intro c
    refine heisU_diagGL_mem_statedSU hq _ (fun i => hZq _) ?_
    have h2 := congrArg (fun z : Z => (z : Kˣ)) (prod_heisUVec m c)
    simpa [u] using h2
  let ψ : (Fin 4 → Z) →* StatedSU (5 + m) q K :=
    MonoidHom.mk' (fun c => ⟨diagGL (5 + m) (u c), hu_mem c⟩) (fun c c' => by
      apply Subtype.ext
      show diagGL (5 + m) (u (c * c')) = diagGL (5 + m) (u c) * diagGL (5 + m) (u c')
      rw [← map_mul]
      congr 1
      funext i
      simp [u, heisUVec_mul])
  have hψ : ∀ c, ((ψ c : StatedSU (5 + m) q K) : GL (Fin (5 + m)) K) = diagGL (5 + m) (u c) :=
    fun _ => rfl
  refine ⟨ψ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro c hc
    funext j
    have h1 := congrArg (fun g : StatedSU (5 + m) q K =>
      ((g : GL (Fin (5 + m)) K) : Matrix (Fin (5 + m)) (Fin (5 + m)) K)
        (Fin.castAdd m j.castSucc) (Fin.castAdd m j.castSucc)) hc
    simp only [hψ, coe_diagGL, Matrix.diagonal_apply_eq, OneMemClass.coe_one, Units.val_one,
      Matrix.one_apply_eq, u, heisUVec_castAdd] at h1
    exact Subtype.ext (Units.ext h1)
  · intro hnr c hc
    rw [hψ] at hc
    obtain ⟨s, hs⟩ := heisU_diagGL_mem_scalars hc
    have hsZ : s ∈ Z := hs (Fin.castAdd m 0) ▸ (heisUVec m c (Fin.castAdd m 0)).2
    have hall : ∀ i, heisUVec m c i = ⟨s, hsZ⟩ := fun i => Subtype.ext (hs i)
    have hs1 : (⟨s, hsZ⟩ : Z) = 1 := by
      rcases hnr with h6 | hnd
      · have := hall (Fin.natAdd 5 ⟨0, by omega⟩)
        rw [heisUVec_natAdd] at this
        exact this.symm
      · have h3 : (⟨s, hsZ⟩ : Z) ^ (5 + m) = 1 := by
          have := prod_heisUVec m c
          simpa [hall, Finset.prod_const] using this
        have h4 : (⟨s, hsZ⟩ : Z) ^ r = 1 := hZpow _
        have hcop : Nat.Coprime r (5 + m) := (Nat.Prime.coprime_iff_not_dvd hr).2 hnd
        have h5 : (⟨s, hsZ⟩ : Z) ^ r.gcd (5 + m) = 1 := pow_gcd_eq_one.2 ⟨h4, h3⟩
        rwa [hcop.gcd_eq_one, pow_one] at h5
    funext j
    have := hall (Fin.castAdd m j.castSucc)
    rw [heisUVec_castAdd, hs1] at this
    simpa using this

theorem heisU_torus_data {K : Type} [Field K] {r : ℕ} {ζ : Kˣ} (hζ : orderOf ζ = r) :
    (∀ c : Fin 4 → Subgroup.zpowers ζ, c ^ r = 1) ∧
      Nat.card (Fin 4 → Subgroup.zpowers ζ) = r ^ 4 := by
  have hZcard : Nat.card (Subgroup.zpowers ζ) = r := by rw [Nat.card_zpowers, hζ]
  refine ⟨fun c => ?_, ?_⟩
  · funext i
    rw [Pi.pow_apply, Pi.one_apply, ← hZcard]
    exact pow_card_eq_one'
  · rw [Nat.card_pi, hZcard]
    simp

theorem heisU_exists_prime_dvd {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) (hf : f ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 5 ∧ r ∣ 2 ^ f + 1 := by
  by_contra hcon
  push Not at hcon
  have hf0 : f ≠ 0 := by
    rintro rfl
    norm_num at h5
  have hodd : ¬ 2 ∣ 2 ^ f + 1 := by
    rw [Nat.dvd_add_right (dvd_pow_self 2 hf0)]
    norm_num
  obtain ⟨k, hk⟩ : ∃ k, f = 2 * k := by
    rcases Nat.even_or_odd f with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k, by omega⟩
    · exfalso
      have h4 : 4 ^ k % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      have h3 : 3 ∣ 2 ^ f + 1 := by
        rw [hk, pow_succ, pow_mul]
        norm_num
        omega
      exact hcon 3 Nat.prime_three (by norm_num) (by norm_num) h3
  have hk2 : 2 ≤ k := by omega
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f + 1 → d = 5 := by
    intro d hd hdvd
    by_contra hd5
    exact hcon d hd (by rintro rfl; exact hodd hdvd) hd5 hdvd
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by positivity) hall
  set a := (2 ^ f + 1).primeFactorsList.length
  have h8 : (2 ^ f + 1) % 8 = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [hk, pow_mul, pow_add]
    norm_num
    omega
  rcases Nat.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  ·
    have h25 : 25 ^ b % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h3 : (2 ^ f + 1) % 3 = 1 := by
      rw [hpow, hb, ← two_mul, pow_mul]
      exact h25
    have h2 : 2 ^ f % 3 = 0 := by omega
    have : 3 ∣ 2 ^ f := Nat.dvd_of_mod_eq_zero h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow this)
    omega
  ·
    have h25 : 25 ^ b % 8 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h5' : 5 ^ a % 8 = 5 := by
      rw [hb, pow_succ, pow_mul]
      norm_num
      omega
    rw [hpow] at h8
    omega

theorem heisU_eq_one_of_pow_eq_one {G L : Type*} [Group G] [Group L] [Finite G] (ρ : G →* L)
    {r : ℕ} (hr : r.Prime) (hker : ¬ r ∣ Nat.card ρ.ker) {x : G} (hx : x ^ r = 1)
    (hρx : ρ x = 1) : x = 1 := by
  have hord : orderOf (⟨x, hρx⟩ : ρ.ker) ∣ Nat.card ρ.ker := orderOf_dvd_natCard _
  have hord' : orderOf (⟨x, hρx⟩ : ρ.ker) ∣ r :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx))
  rcases (Nat.dvd_prime hr).1 hord' with h1 | h1
  · exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ hord) hker

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
