module

public import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.SectionRank.OddCover CFSG.StandardType CFSG.StandardType.TableBUE

theorem exists_eq_of_pow_three_eq {K : Type} [Field K] (u v : Fin 3 → K) {c c' : K}
    (hu : ∀ r, u r ^ 3 = c) (hv : ∀ r, v r ^ 3 = c')
    (huv : ∀ k : ℕ, ¬ ∀ r s, v r * u r ^ k = v s * u s ^ k) :
    ∃ r s, r ≠ s ∧ (u r = u s ∨ v r = v s) := by
  by_contra hcon
  push Not at hcon
  have hu_inj : Function.Injective u := fun r s hrs => by
    by_contra hne
    exact (hcon r s hne).1 hrs
  have hv_inj : Function.Injective v := fun r s hrs => by
    by_contra hne
    exact (hcon r s hne).2 hrs
  have hc0 : c ≠ 0 := by
    intro hc
    have h0 : u 0 = 0 :=
      (pow_eq_zero_iff (n := 3) (by norm_num)).mp (by rw [hu 0, hc])
    have h1 : u 1 = 0 :=
      (pow_eq_zero_iff (n := 3) (by norm_num)).mp (by rw [hu 1, hc])
    exact (by decide : (0 : Fin 3) ≠ 1) (hu_inj (h0.trans h1.symm))
  have hc'0 : c' ≠ 0 := by
    intro hc
    have h0 : v 0 = 0 :=
      (pow_eq_zero_iff (n := 3) (by norm_num)).mp (by rw [hv 0, hc])
    have h1 : v 1 = 0 :=
      (pow_eq_zero_iff (n := 3) (by norm_num)).mp (by rw [hv 1, hc])
    exact (by decide : (0 : Fin 3) ≠ 1) (hv_inj (h0.trans h1.symm))
  have hu0 : u 0 ≠ 0 := fun h => hc0 (by rw [← hu 0, h]; exact zero_pow (by norm_num))
  have hv0 : v 0 ≠ 0 := fun h => hc'0 (by rw [← hv 0, h]; exact zero_pow (by norm_num))
  set ζ : K := u 1 / u 0 with hζ
  set η : K := u 2 / u 0 with hη
  set ξ : K := v 1 / v 0 with hξ
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζ, div_pow, hu 1, hu 0, div_self hc0]
  have hη3 : η ^ 3 = 1 := by
    rw [hη, div_pow, hu 2, hu 0, div_self hc0]
  have hξ3 : ξ ^ 3 = 1 := by
    rw [hξ, div_pow, hv 1, hv 0, div_self hc'0]
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h1 : u 1 = u 0 := by
      rw [hζ] at h
      rwa [div_eq_one_iff_eq hu0] at h
    exact (hcon 0 1 (by decide)).1 h1.symm
  have hη1 : η ≠ 1 := by
    intro h
    have h2 : u 2 = u 0 := by
      rw [hη] at h
      rwa [div_eq_one_iff_eq hu0] at h
    exact (hcon 0 2 (by decide)).1 h2.symm
  have hξ1 : ξ ≠ 1 := by
    intro h
    have h1 : v 1 = v 0 := by
      rw [hξ] at h
      rwa [div_eq_one_iff_eq hv0] at h
    exact (hcon 0 1 (by decide)).2 h1.symm
  have hζquad : ζ ^ 2 + ζ + 1 = 0 := by
    have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ1)
  have hηquad : η ^ 2 + η + 1 = 0 := by
    have h : (η - 1) * (η ^ 2 + η + 1) = 0 := by linear_combination hη3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hη1)
  have hξquad : ξ ^ 2 + ξ + 1 = 0 := by
    have h : (ξ - 1) * (ξ ^ 2 + ξ + 1) = 0 := by linear_combination hξ3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hξ1)
  have hu1 : u 1 = u 0 * ζ := by
    rw [hζ, mul_comm, div_mul_cancel₀ _ hu0]
  have hu2pre : u 2 = u 0 * η := by
    rw [hη, mul_comm, div_mul_cancel₀ _ hu0]
  have hv1 : v 1 = v 0 * ξ := by
    rw [hξ, mul_comm, div_mul_cancel₀ _ hv0]
  set θ : K := v 2 / v 0 with hθ
  have hθ3 : θ ^ 3 = 1 := by
    rw [hθ, div_pow, hv 2, hv 0, div_self hc'0]
  have hθ1 : θ ≠ 1 := by
    intro h
    have h2 : v 2 = v 0 := by
      rw [hθ] at h
      rwa [div_eq_one_iff_eq hv0] at h
    exact (hcon 0 2 (by decide)).2 h2.symm
  have hθquad : θ ^ 2 + θ + 1 = 0 := by
    have h : (θ - 1) * (θ ^ 2 + θ + 1) = 0 := by linear_combination hθ3
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hθ1)
  have hv2pre : v 2 = v 0 * θ := by
    rw [hθ, mul_comm, div_mul_cancel₀ _ hv0]
  have hθne : θ ≠ ξ := by
    intro h
    refine (hcon 1 2 (by decide)).2 ?_
    rw [hv1, hv2pre, h]
  have hθ_eq : θ = ξ ^ 2 := by
    have h : (θ - ξ) * (θ - ξ ^ 2) = 0 := by
      linear_combination hθquad + hξ3 - θ * hξquad
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hθne))
  have hv2 : v 2 = v 0 * ξ ^ 2 := by rw [hv2pre, hθ_eq]
  have hηne : η ≠ ζ := by
    intro h
    refine (hcon 1 2 (by decide)).1 ?_
    rw [hu1, hu2pre, h]
  have hη_eq : η = ζ ^ 2 := by
    have h : (η - ζ) * (η - ζ ^ 2) = 0 := by
      linear_combination hηquad + hζ3 - η * hζquad
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hηne))
  have hu2 : u 2 = u 0 * ζ ^ 2 := by rw [hu2pre, hη_eq]
  have hξ_eq : ξ = ζ ∨ ξ = ζ ^ 2 := by
    have h : (ξ - ζ) * (ξ - ζ ^ 2) = 0 := by
      linear_combination hξquad + hζ3 - ξ * hζquad
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hu_eq : ∀ r : Fin 3, u r = u 0 * ζ ^ (r : ℕ) := by
    intro r
    fin_cases r <;> simp [hu1, hu2]
  have hv_eq : ∀ r : Fin 3, v r = v 0 * ξ ^ (r : ℕ) := by
    intro r
    fin_cases r <;> simp [hv1, hv2]
  have hpow3 : ∀ a : ℕ, (ζ ^ a) ^ 3 = 1 := by
    intro a
    rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
  rcases hξ_eq with hξζ | hξζ2
  · refine huv 2 ?_
    intro r s
    have hprod : ∀ t : Fin 3, v t * u t ^ 2 = v 0 * u 0 ^ 2 := by
      intro t
      rw [hu_eq t, hv_eq t, hξζ]
      calc v 0 * ζ ^ (t : ℕ) * (u 0 * ζ ^ (t : ℕ)) ^ 2
          = v 0 * u 0 ^ 2 * (ζ ^ (t : ℕ)) ^ 3 := by ring
        _ = v 0 * u 0 ^ 2 := by rw [hpow3 t, mul_one]
    rw [hprod r, hprod s]
  · refine huv 1 ?_
    intro r s
    have hpow : ∀ t : Fin 3, (ζ ^ 2) ^ (t : ℕ) = (ζ ^ (t : ℕ)) ^ 2 := by
      intro t
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hprod : ∀ t : Fin 3, v t * u t ^ 1 = v 0 * u 0 ^ 1 := by
      intro t
      rw [hu_eq t, hv_eq t, hξζ2, hpow t]
      simp only [pow_one]
      calc v 0 * (ζ ^ (t : ℕ)) ^ 2 * (u 0 * ζ ^ (t : ℕ))
          = v 0 * u 0 * (ζ ^ (t : ℕ)) ^ 3 := by ring
        _ = v 0 * u 0 := by rw [hpow3 t, mul_one]
    rw [hprod r, hprod s]

theorem not_isSolvable_centralizer_of_isDiag {f : ℕ} {E : Type} [Field E]
    (h : UnitaryFieldData 2 f E) (hf : 2 ≤ f) {P M : GL (Fin 3) E}
    (hP : P ∈ primeFormUnitary h (idGram E 3)) {r s : Fin 3} (hrs : r ≠ s)
    (hdiag : (((P⁻¹ * M * P : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)).IsDiag)
    (heq : ((P⁻¹ * M * P : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) r r =
      ((P⁻¹ * M * P : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) s s) :
    ¬ Group.IsSolvable ↥(unitarySU 2 f E 3 ⊓ Subgroup.centralizer {M}) := by
  classical
  have hSU : unitarySU 2 f E 3 = gramSU h (idGram E 3) := unitarySU_eq_gramSU h 3
  let t : GL (Fin 3) E := P⁻¹ * M * P
  let u : Fin 3 → E := fun c => ((t : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) c c
  have ht : ((t : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal u :=
    (hdiag.diagonal_diag).symm
  have hdet : ((t : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det ≠ 0 := by
    refine Matrix.det_ne_zero_of_right_inverse (B := ((t⁻¹ : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E)) ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hu0 : ∀ c, u c ≠ 0 := by
    have hprod : (∏ c : Fin 3, u c) ≠ 0 := by
      rw [ht] at hdet
      simpa [Matrix.det_diagonal] using hdet
    exact fun c => (Finset.prod_ne_zero_iff.mp hprod) c (Finset.mem_univ c)
  let τ : Fin 3 → Eˣ := fun c => Units.mk0 (u c) (hu0 c)
  have htτ : diagHom 3 τ = t := by
    apply Units.ext
    rw [coe_diagHom, ht]
    rfl
  let S : Finset (Fin 3) := {r, s}
  have hScard : S.card = 2 := Finset.card_pair hrs
  have hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j := by
    intro i hi j hj
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exact Units.ext heq
    · exact Units.ext heq.symm
    · rfl
  let H : Subgroup (GL (Fin 3) E) := unitarySU 2 f E 3
  let B : Subgroup ↥H := blockSU (K := E) (n := f) S
  let ψ : ↥H →* GL (Fin 3) E := (MulAut.conj P).toMonoidHom.comp H.subtype
  let K : Subgroup (GL (Fin 3) E) := B.map ψ
  have hBq : CFSG.IsQuasisimple ↥B :=
    CFSG.StandardType.SURepair.isQuasisimple_blockSU_two (n := 3) h hf hScard
  have hBns : ¬ Group.IsSolvable ↥B := by
    haveI : Nontrivial ↥B := by
      obtain ⟨-, -, a, b, hab⟩ := hBq
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      have hs : ∀ x y : ↥B ⧸ Subgroup.center ↥B, x = y := fun x y => by
        obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
        rw [Subsingleton.elim x' y']
      exact hab (by rw [hs a b])
    haveI : Group.IsPerfect ↥B := hBq.1
    exact Group.IsPerfect.not_isSolvable ↥B
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    exact Subtype.ext ((MulAut.conj P).injective hxy)
  have hKns : ¬ Group.IsSolvable ↥K := by
    intro hKsol
    have hBsol : Group.IsSolvable ↥B :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective B ψ hψinj).toMonoidHom)
        (Subgroup.equivMapOfInjective B ψ hψinj).injective
    exact hBns hBsol
  have hKle : K ≤ H ⊓ Subgroup.centralizer ({M} : Set (GL (Fin 3) E)) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    constructor
    · have hb' : ((b : GL (Fin 3) E)) ∈ gramSU h (idGram E 3) := by
        rw [← hSU]
        exact b.2
      have hconj : P * (b : GL (Fin 3) E) * P⁻¹ ∈ gramSU h (idGram E 3) :=
        conj_mem_gramSU h (idGram E 3) hP hb'
      have hconj' : P * (b : GL (Fin 3) E) * P⁻¹ ∈ unitarySU 2 f E 3 := by
        rw [hSU]
        exact hconj
      simpa [ψ, MulAut.conj_apply] using hconj'
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hbblock : IsBlockOn S ((b : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) :=
        (mem_blockSU).mp hb
      have hbt : (b : GL (Fin 3) E) * t = t * (b : GL (Fin 3) E) := by
        have hcomm := diagHom_mul_comm_of_isBlockOn hτ hbblock
        rw [htτ] at hcomm
        exact hcomm.symm
      have hMt : M = P * t * P⁻¹ := by
        simp only [t]
        group
      have hxeq : (ψ b : GL (Fin 3) E) = P * (b : GL (Fin 3) E) * P⁻¹ := by
        show (MulAut.conj P) (b : GL (Fin 3) E) = P * (b : GL (Fin 3) E) * P⁻¹
        rw [MulAut.conj_apply]
      rw [hxeq, hMt]
      calc P * (b : GL (Fin 3) E) * P⁻¹ * (P * t * P⁻¹)
          = P * ((b : GL (Fin 3) E) * t) * P⁻¹ := by group
        _ = P * (t * (b : GL (Fin 3) E)) * P⁻¹ := by rw [hbt]
        _ = P * t * P⁻¹ * (P * (b : GL (Fin 3) E) * P⁻¹) := by group
  intro hsol
  have hKsol : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKle)
      (Subgroup.inclusion_injective hKle)
  exact hKns hKsol

theorem not_isSolvable_and_of_unitary_three {f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E) (hf : 2 ≤ f)
    (h3 : 3 ∣ 2 ^ f + 1)
    {M₁ M₂ : GL (Fin 3) E}
    (hu₁ : M₁ ∈ primeFormUnitary h (idGram E 3))
    (hu₂ : M₂ ∈ primeFormUnitary h (idGram E 3))
    (h₁ : M₁ ^ 3 = 1) (h₂ : M₂ ^ 3 = 1) (hc : Commute M₁ M₂)
    (hk : ∀ k : ℕ, ∃ g ∈ CFSG.Open.StatedSU 3 (2 ^ f) E,
      g * (M₂ * M₁ ^ k) ≠ (M₂ * M₁ ^ k) * g) :
    ¬ (Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (2 ^ f) E ⊓
        Subgroup.centralizer {M₁}) ∧
      Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (2 ^ f) E ⊓
        Subgroup.centralizer {M₂})) := by
  classical
  haveI : Finite E := h.finite
  have hEU : ∀ x ∈ ({M₁, M₂} : Set (GL (Fin 3) E)), x ∈ primeFormUnitary h (idGram E 3) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu₁
    · exact hu₂
  have hEc : ∀ x ∈ ({M₁, M₂} : Set (GL (Fin 3) E)),
      ∀ y ∈ ({M₁, M₂} : Set (GL (Fin 3) E)), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · simpa using hc.eq
    · simpa using hc.eq.symm
    · rfl
  have hE3 : ∀ x ∈ ({M₁, M₂} : Set (GL (Fin 3) E)), x ^ 3 = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨P, hPmem, hPdiag⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
      (n := 3) h h3 ({M₁, M₂} : Set (GL (Fin 3) E)) hEU hEc hE3
  let Pg : GL (Fin 3) E := P
  let t₁ : GL (Fin 3) E := Pg⁻¹ * M₁ * Pg
  let t₂ : GL (Fin 3) E := Pg⁻¹ * M₂ * Pg
  have hD₁ : ((t₁ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).IsDiag :=
    hPdiag M₁ (by simp)
  have hD₂ : ((t₂ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).IsDiag :=
    hPdiag M₂ (by simp)
  let u₁ : Fin 3 → E := fun c => ((t₁ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) c c
  let u₂ : Fin 3 → E := fun c => ((t₂ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) c c
  have ht₁ : ((t₁ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal u₁ :=
    (hD₁.diagonal_diag).symm
  have ht₂ : ((t₂ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal u₂ :=
    (hD₂.diagonal_diag).symm
  have ht₁3 : t₁ ^ 3 = 1 := by
    have hconj : t₁ ^ 3 = Pg⁻¹ * M₁ ^ 3 * Pg := by
      rw [show t₁ = (MulAut.conj Pg⁻¹) M₁ by
        rw [MulAut.conj_apply]
        rfl]
      rw [← map_pow]
      simp [MulAut.conj_apply]
    rw [hconj, h₁, mul_one, inv_mul_cancel]
  have ht₂3 : t₂ ^ 3 = 1 := by
    have hconj : t₂ ^ 3 = Pg⁻¹ * M₂ ^ 3 * Pg := by
      rw [show t₂ = (MulAut.conj Pg⁻¹) M₂ by
        rw [MulAut.conj_apply]
        rfl]
      rw [← map_pow]
      simp [MulAut.conj_apply]
    rw [hconj, h₂, mul_one, inv_mul_cancel]
  have hu₁3 : ∀ c, u₁ c ^ 3 = 1 := by
    intro c
    have h := congrArg (fun M : GL (Fin 3) E => (M : Matrix (Fin 3) (Fin 3) E)) ht₁3
    simp only [Units.val_pow_eq_pow_val, Units.val_one, ht₁, Matrix.diagonal_pow,
      Pi.pow_apply] at h
    have h1 : Matrix.diagonal (fun c => u₁ c ^ 3) = Matrix.diagonal (fun _ => (1 : E)) := by
      rw [Matrix.diagonal_one]
      exact h
    exact (Matrix.diagonal_eq_diagonal_iff.mp h1) c
  have hu₂3 : ∀ c, u₂ c ^ 3 = 1 := by
    intro c
    have h := congrArg (fun M : GL (Fin 3) E => (M : Matrix (Fin 3) (Fin 3) E)) ht₂3
    simp only [Units.val_pow_eq_pow_val, Units.val_one, ht₂, Matrix.diagonal_pow,
      Pi.pow_apply] at h
    have h1 : Matrix.diagonal (fun c => u₂ c ^ 3) = Matrix.diagonal (fun _ => (1 : E)) := by
      rw [Matrix.diagonal_one]
      exact h
    exact (Matrix.diagonal_eq_diagonal_iff.mp h1) c
  have huv : ∀ k : ℕ, ¬ ∀ r s, u₂ r * u₁ r ^ k = u₂ s * u₁ s ^ k := by
    intro k hconst
    obtain ⟨g, hg, hgne⟩ := hk k
    apply hgne
    let cst : E := u₂ 0 * u₁ 0 ^ k
    have hprod : ((t₂ * t₁ ^ k : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
        Matrix.diagonal (fun r => u₂ r * u₁ r ^ k) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, ht₂, ht₁, Matrix.diagonal_pow,
        Matrix.diagonal_mul_diagonal]
      rfl
    have hconj : ((Pg⁻¹ * (M₂ * M₁ ^ k) * Pg : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) = Matrix.diagonal (fun _ => cst) := by
      have heqlGL : Pg⁻¹ * (M₂ * M₁ ^ k) * Pg = t₂ * t₁ ^ k := by
        have h1 : t₁ = (MulAut.conj Pg⁻¹) M₁ := by
          rw [MulAut.conj_apply]
          rfl
        have h2 : t₂ = (MulAut.conj Pg⁻¹) M₂ := by
          rw [MulAut.conj_apply]
          rfl
        rw [h1, h2, ← map_pow, ← map_mul, MulAut.conj_apply, inv_inv]
      have heql : ((Pg⁻¹ * (M₂ * M₁ ^ k) * Pg : GL (Fin 3) E) :
          Matrix (Fin 3) (Fin 3) E) = ((t₂ * t₁ ^ k : GL (Fin 3) E) :
            Matrix (Fin 3) (Fin 3) E) :=
        congrArg (fun M : GL (Fin 3) E => (M : Matrix (Fin 3) (Fin 3) E)) heqlGL
      rw [heql, hprod, Matrix.diagonal_eq_diagonal_iff]
      intro r
      exact hconst r 0
    have hMmat : ((M₂ * M₁ ^ k : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
        Matrix.diagonal (fun _ => cst) := by
      have hMGL : M₂ * M₁ ^ k = Pg * (Pg⁻¹ * (M₂ * M₁ ^ k) * Pg) * Pg⁻¹ := by group
      calc ((M₂ * M₁ ^ k : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)
          = ((Pg * (Pg⁻¹ * (M₂ * M₁ ^ k) * Pg) * Pg⁻¹ : GL (Fin 3) E) :
              Matrix (Fin 3) (Fin 3) E) :=
            congrArg (fun M : GL (Fin 3) E => (M : Matrix (Fin 3) (Fin 3) E)) hMGL
        _ = (Pg : Matrix (Fin 3) (Fin 3) E) *
              ((Pg⁻¹ * (M₂ * M₁ ^ k) * Pg : GL (Fin 3) E) :
                Matrix (Fin 3) (Fin 3) E) *
              ((Pg⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
            simp only [Units.val_mul]
        _ = (Pg : Matrix (Fin 3) (Fin 3) E) * Matrix.diagonal (fun _ => cst) *
              ((Pg⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
            rw [hconj]
        _ = Matrix.diagonal (fun _ => cst) := by
            rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hcomm : g * (M₂ * M₁ ^ k) = (M₂ * M₁ ^ k) * g := by
      apply Units.ext
      change (g : Matrix (Fin 3) (Fin 3) E) * ((M₂ * M₁ ^ k : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) = ((M₂ * M₁ ^ k : GL (Fin 3) E) :
          Matrix (Fin 3) (Fin 3) E) * (g : Matrix (Fin 3) (Fin 3) E)
      rw [hMmat, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul]
    exact hcomm
  obtain ⟨r, s, hrs, hcase⟩ :=
    exists_eq_of_pow_three_eq u₁ u₂ (c := 1) (c' := 1) hu₁3 hu₂3 huv
  rcases hcase with heq | heq
  · have hC := not_isSolvable_centralizer_of_isDiag (h := h) (hf := hf) (P := P) (M := M₁)
      (r := r) (s := s) hPmem hrs (by simpa [Pg, t₁] using hD₁)
      (by simpa [Pg, t₁, u₁] using heq)
    exact fun ⟨hsol, _⟩ => hC hsol
  · have hC := not_isSolvable_centralizer_of_isDiag (h := h) (hf := hf) (P := P) (M := M₂)
      (r := r) (s := s) hPmem hrs (by simpa [Pg, t₂] using hD₂)
      (by simpa [Pg, t₂, u₂] using heq)
    exact fun ⟨_, hsol⟩ => hC hsol

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
