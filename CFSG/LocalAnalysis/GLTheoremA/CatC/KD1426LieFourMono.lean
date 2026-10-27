module

public import CFSG.GroupTheory.ZpowersInvolution
public import CFSG.ClassicalInvolution.Models.LinearFrames.Signs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalInvolution.Models

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

noncomputable def diagFour (K : Type) [Field K] : Subgroup (GL (Fin 3) K) :=
  ((Subgroup.zpowers (-1 : Kˣ)).prod (Subgroup.zpowers (-1 : Kˣ))).map torusHom

theorem mem_diagFour {t : GL (Fin 3) K} :
    t ∈ diagFour K ↔ ∃ a ∈ Subgroup.zpowers (-1 : Kˣ), ∃ b ∈ Subgroup.zpowers (-1 : Kˣ),
      torusHom (a, b) = t := by
  rw [diagFour, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨a, hab.1, b, hab.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

private theorem neg_one_ne_one_units (hK : PiField π p f K) (hp : 5 ≤ p) :
    (-1 : Kˣ) ≠ 1 := by
  haveI : Fact (2 < p) := ⟨by omega⟩
  haveI : CharP K p := hK.charP
  intro h
  exact CharP.neg_one_ne_one (R := K) p (congrArg Units.val h)

private theorem eq_one_or_neg_one_of_mem_zpowers_neg_one {a : Kˣ}
    (ha : a ∈ Subgroup.zpowers (-1 : Kˣ)) : a = 1 ∨ a = -1 := by
  have h2 : a ^ 2 = 1 :=
    CFSG.sq_eq_one_of_mem_zpowers (by simp : (-1 : Kˣ) ^ 2 = 1) ha
  have h' : (a : K) = 1 ∨ (a : K) = -1 :=
    sq_eq_one_iff.mp (by simpa using congrArg Units.val h2)
  rcases h' with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

private theorem mem_zpowers_neg_one_of_sq_eq_one {a : Kˣ} (ha : a ^ 2 = 1) :
    a ∈ Subgroup.zpowers (-1 : Kˣ) := by
  have ha' : (a : K) = 1 ∨ (a : K) = -1 :=
    sq_eq_one_iff.mp (by simpa using congrArg Units.val ha)
  rcases ha' with h | h
  · rw [show a = 1 from Units.ext h]
    exact Subgroup.one_mem _
  · rw [show a = -1 from Units.ext h]
    exact Subgroup.mem_zpowers (-1)

theorem even_qSubPi (hK : PiField π p f K) (hp : 5 ≤ p) : Even (qSubPi π (p ^ f)) := by
  have hpodd : Odd p := hK.prime.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hpodd.pow (n := f)
  cases π
  · change Even (p ^ f + 1)
    exact ⟨k + 1, by omega⟩
  · change Even (p ^ f - 1)
    exact ⟨k, by omega⟩

theorem mem_rootsOfUnity_qSubPi_of_sq_eq_one (hK : PiField π p f K) (hp : 5 ≤ p) {a : Kˣ}
    (ha : a ^ 2 = 1) : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  rw [mem_rootsOfUnity]
  obtain ⟨m, hm⟩ := even_qSubPi hK hp
  rw [hm, show m + m = 2 * m by ring, pow_mul, ha, one_pow]

theorem diagFour_le_slPi (hK : PiField π p f K) (hp : 5 ≤ p) :
    diagFour (K := K) ≤ slPi π 3 (p ^ f) K := by
  intro t ht
  rw [mem_diagFour] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  exact torusHom_mem_slPi hK
    (mem_rootsOfUnity_qSubPi_of_sq_eq_one hK hp
      (CFSG.sq_eq_one_of_mem_zpowers (by simp : (-1 : Kˣ) ^ 2 = 1) ha))
    (mem_rootsOfUnity_qSubPi_of_sq_eq_one hK hp
      (CFSG.sq_eq_one_of_mem_zpowers (by simp : (-1 : Kˣ) ^ 2 = 1) hb))

theorem diagFour_sq {t : GL (Fin 3) K} (ht : t ∈ diagFour K) : t ^ 2 = 1 := by
  rw [mem_diagFour] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  rw [← map_pow]
  change torusHom (a ^ 2, b ^ 2) = 1
  rw [show a ^ 2 = 1 from
      CFSG.sq_eq_one_of_mem_zpowers (by simp : (-1 : Kˣ) ^ 2 = 1) ha,
    show b ^ 2 = 1 from
      CFSG.sq_eq_one_of_mem_zpowers (by simp : (-1 : Kˣ) ^ 2 = 1) hb]
  exact map_one torusHom

theorem card_diagFour (hK : PiField π p f K) (hp : 5 ≤ p) :
    Nat.card (diagFour (K := K)) = 4 := by
  have hneg : (-1 : Kˣ) ≠ 1 := neg_one_ne_one_units hK hp
  have h2 : (-1 : Kˣ) ^ 2 = 1 := by
    apply Units.ext
    simp
  have hord : orderOf (-1 : Kˣ) = 2 := orderOf_eq_prime h2 hneg
  have hcard : Nat.card (Subgroup.zpowers (-1 : Kˣ)) = 2 := by
    rw [Nat.card_zpowers, hord]
  rw [diagFour, Subgroup.card_map_of_injective torusHom_injective]
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hcard]

theorem diagFour_inf_zPi (hK : PiField π p f K) (hp : 5 ≤ p) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagFour (K := K) ⊓ zPi π 3 (p ^ f) K = ⊥ := by
  haveI : Fact (2 < p) := ⟨by omega⟩
  haveI : CharP K p := hK.charP
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨ht4, htZ⟩ := Subgroup.mem_inf.mp ht
  have htSL : t ∈ slPi π 3 (p ^ f) K := diagFour_le_slPi hK hp ht4
  have hdet : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    ((mem_slPi_iff hπ).mp htSL).2
  have ht2 : t ^ 2 = 1 := diagFour_sq ht4
  obtain ⟨ξ, hξ, hξt⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 htZ
  have hξ2 : ξ ^ 2 = 1 := by
    apply scalar_injective_three
    rw [map_pow, map_one, hξt, ht2]
  rw [Subgroup.mem_bot]
  have hξ' : (ξ : K) = 1 ∨ (ξ : K) = -1 :=
    sq_eq_one_iff.mp (by simpa using congrArg Units.val hξ2)
  rcases hξ' with h | h
  · rw [← hξt, show ξ = 1 from Units.ext h, map_one]
  · exfalso
    have hdet' := hdet
    rw [← hξt, show ξ = -1 from Units.ext h, det_scalar_three] at hdet'
    norm_num at hdet'
    exact (CharP.neg_one_ne_one (R := K) p) hdet'



theorem mem_diagFour_of_diagonal_pm_one {d : Fin 3 → K}
    {t : GL (Fin 3) K} (ht : (t : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hd : ∀ i, d i = 1 ∨ d i = -1) (hprod : d 0 * d 1 * d 2 = 1) :
    t ∈ diagFour (K := K) := by
  have h0 : d 0 ≠ 0 := by rcases hd 0 with h | h <;> simp [h]
  have h1 : d 1 ≠ 0 := by rcases hd 1 with h | h <;> simp [h]
  set a : Kˣ := Units.mk0 (d 0) h0 with ha
  set b : Kˣ := Units.mk0 (d 1) h1 with hb
  have ha2 : a ^ 2 = 1 := by
    apply Units.ext
    rcases hd 0 with h | h <;> simp [a, h]
  have hb2 : b ^ 2 = 1 := by
    apply Units.ext
    rcases hd 1 with h | h <;> simp [b, h]
  have hza : a ∈ Subgroup.zpowers (-1 : Kˣ) := mem_zpowers_neg_one_of_sq_eq_one ha2
  have hzb : b ∈ Subgroup.zpowers (-1 : Kˣ) := mem_zpowers_neg_one_of_sq_eq_one hb2
  have hd2 : d 2 = ((a : K) * (b : K))⁻¹ := by
    have h : ((a : K) * (b : K)) * d 2 = 1 := by
      rw [← hprod]; simp [a, b]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)
  have heq : torusHom (a, b) = diagonal d := by
    rw [coe_torusHom]
    congr 1
    funext i
    fin_cases i <;> simp [a, b, hd2]
  have ht' : t = torusHom (a, b) := Units.ext (by rw [ht, ← heq])
  rw [ht']
  exact mem_diagFour.mpr ⟨a, hza, b, hzb, rfl⟩

theorem diagFour_normalized {c : GL (Fin 3) K}
    {σ : Equiv.Perm (Fin 3)}
    (hmono : IsMonomialFor (c : Matrix (Fin 3) (Fin 3) K) σ)
    {t : GL (Fin 3) K} (ht : t ∈ diagFour (K := K)) :
    c * t * c⁻¹ ∈ diagFour (K := K) := by
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := mem_diagFour.mp ht
  set d : Fin 3 → K := ![(a₀ : K), (b₀ : K), (((a₀ * b₀)⁻¹ : Kˣ) : K)] with hddef
  have hpm : ∀ i, d i = 1 ∨ d i = -1 := by
    intro i
    have ha₀u : a₀ = 1 ∨ a₀ = -1 := eq_one_or_neg_one_of_mem_zpowers_neg_one ha₀
    have hb₀u : b₀ = 1 ∨ b₀ = -1 := eq_one_or_neg_one_of_mem_zpowers_neg_one hb₀
    fin_cases i
    · simpa [d] using ha₀u
    · simpa [d] using hb₀u
    · rcases ha₀u with h | h <;> rcases hb₀u with h' | h' <;> simp [d, h, h']
  have hprod : d 0 * d 1 * d 2 = 1 := by
    simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_inv_eq_inv_val, Units.val_mul]
    exact mul_inv_cancel₀ (mul_ne_zero a₀.ne_zero b₀.ne_zero)
  have hconv : ((c * torusHom (a₀, b₀) * c⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => d (σ.symm i)) := by
    rw [Units.val_mul, Units.val_mul, coe_torusHom, ← hddef]
    exact hmono.mul_diagonal_mul_inv (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) d
  apply mem_diagFour_of_diagonal_pm_one (d := fun i => d (σ.symm i))
    (t := c * torusHom (a₀, b₀) * c⁻¹) hconv
  · intro i; exact hpm (σ.symm i)
  · have hperm : (∏ i : Fin 3, d (σ.symm i)) = ∏ i : Fin 3, d i :=
      Fintype.prod_equiv σ.symm (fun i : Fin 3 => d (σ.symm i)) d (fun i => rfl)
    simpa [Fin.prod_univ_three] using hperm.trans (by simpa [Fin.prod_univ_three] using hprod)

theorem const_of_invariant_threeCycle {d : Fin 3 → K} {σ : Equiv.Perm (Fin 3)}
    (hσ3 : σ ^ 3 = 1) (hσne : σ ≠ 1) (hinv : ∀ i, d i = d (σ.symm i)) :
    ∀ i, d i = d 0 := by
  set τ : Equiv.Perm (Fin 3) := σ.symm with hτdef
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef]
    have e : (Equiv.symm σ : Equiv.Perm (Fin 3)) = σ⁻¹ := rfl
    rw [e, show (σ⁻¹ : Equiv.Perm (Fin 3)) ^ 3 = (σ ^ 3)⁻¹ by rw [← inv_pow], hσ3,
      inv_one]
  have hτne : τ ≠ 1 := by
    intro h
    rw [hτdef] at h
    apply hσne
    have h' := congrArg Equiv.symm h
    rw [show (Equiv.symm (1 : Equiv.Perm (Fin 3))) = 1 from rfl] at h'
    exact h'
  have hord : orderOf τ = 3 := by
    have hdvd : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hτne
    · exact h
  have hcyc : τ.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hord]; exact Nat.prime_three) (by rw [hord]; norm_num)
  have hsupp : τ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    rw [← hcyc.orderOf, hord]
  have hiter : ∀ k : ℕ, d ((τ ^ k) (0 : Fin 3)) = d 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact (hinv ((τ ^ k) (0 : Fin 3))).symm.trans ih
  intro j
  have hsupp0 : τ (0 : Fin 3) ≠ (0 : Fin 3) :=
    Equiv.Perm.mem_support.mp (by rw [hsupp]; exact Finset.mem_univ (0 : Fin 3))
  have hsuppj : τ j ≠ j :=
    Equiv.Perm.mem_support.mp (by rw [hsupp]; exact Finset.mem_univ j)
  obtain ⟨k, hk⟩ := hcyc.exists_pow_eq hsupp0 hsuppj
  rw [← hk]
  exact hiter k

theorem fixedPointFree_of_threeCycle (hK : PiField π p f K) (hp : 5 ≤ p) {c : GL (Fin 3) K}
    {σ : Equiv.Perm (Fin 3)}
    (hmono : IsMonomialFor (c : Matrix (Fin 3) (Fin 3) K) σ)
    (hσ3 : σ ^ 3 = 1) (hσne : σ ≠ 1) {t : GL (Fin 3) K} (ht : t ∈ diagFour (K := K))
    (hfix : c * t * c⁻¹ = t) : t = 1 := by
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := mem_diagFour.mp ht
  set d : Fin 3 → K := ![(a₀ : K), (b₀ : K), (((a₀ * b₀)⁻¹ : Kˣ) : K)] with hddef
  have hconv : ((c * torusHom (a₀, b₀) * c⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => d (σ.symm i)) := by
    rw [Units.val_mul, Units.val_mul, coe_torusHom, ← hddef]
    exact hmono.mul_diagonal_mul_inv (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) d
  have hdiag : diagonal (fun i => d (σ.symm i)) = diagonal d := by
    rw [← hconv, hfix, coe_torusHom, ← hddef]
  have hinv : ∀ i, d i = d (σ.symm i) := by
    intro i
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i i) hdiag
    simpa using h.symm
  have hconst := const_of_invariant_threeCycle hσ3 hσne hinv
  have hprod : d 0 * d 1 * d 2 = 1 := by
    simp only [d, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Units.val_inv_eq_inv_val, Units.val_mul]
    exact mul_inv_cancel₀ (mul_ne_zero a₀.ne_zero b₀.ne_zero)
  have ha₀u : a₀ = 1 ∨ a₀ = -1 := eq_one_or_neg_one_of_mem_zpowers_neg_one ha₀
  have hd0pm : d 0 = 1 ∨ d 0 = -1 := by
    rcases ha₀u with h | h
    · exact Or.inl (by simpa [d] using congrArg Units.val h)
    · exact Or.inr (by simpa [d] using congrArg Units.val h)
  have h1 : d 1 = d 0 := hconst 1
  have h2 : d 2 = d 0 := hconst 2
  have hcube : d 0 * d 0 * d 0 = 1 := by simpa [h1, h2] using hprod
  have hd0 : d 0 = 1 := by
    rcases hd0pm with h | h
    · exact h
    · exfalso
      rw [h] at hcube
      norm_num at hcube
      haveI : Fact (2 < p) := ⟨by omega⟩
      haveI : CharP K p := hK.charP
      exact CharP.neg_one_ne_one (R := K) p hcube
  have hdall : d = fun _ => (1 : K) := by
    funext i
    rw [hconst i, hd0]
  have hmat : ((torusHom (a₀, b₀) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [coe_torusHom]
  apply Units.ext
  rw [Units.val_one, hmat, hdall]
  simp [Matrix.diagonal_one]

theorem isMonomial_of_conj_diagTau {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {c : GL (Fin 3) K} {ξ : Kˣ}
    (h : c * diagTau hτ * c⁻¹ = GeneralLinearGroup.scalar (Fin 3) ξ * diagTau hτ) :
    ∃ σ : Equiv.Perm (Fin 3), IsMonomialFor (c : Matrix (Fin 3) (Fin 3) K) σ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro hh
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, hh, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro hh
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← hh, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hlam : Function.Injective (![τ, τ ^ 2, 1] : Fin 3 → K) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hij ⊢ <;>
      first
        | rfl
        | exact absurd hij hτ1
        | exact absurd hij.symm hτ1
        | exact absurd hij hτ2
        | exact absurd hij.symm hτ2
        | exact absurd hij hττ2
        | exact absurd hij.symm hττ2
  have hmat := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Units.val_mul, Units.val_inv_eq_inv_val] at hmat
  have h2 : (c : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
      (GeneralLinearGroup.scalar (Fin 3) ξ : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![τ, τ ^ 2, 1] * (c : Matrix (Fin 3) (Fin 3) K) := by
    have h1 :=
      congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M * (c : Matrix (Fin 3) (Fin 3) K)) hmat
    simp only [mul_assoc] at h1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] at h1
    simpa only [coe_diagTau_eq_diagonal, mul_assoc] using h1
  have hentry : ∀ i j, (c : Matrix (Fin 3) (Fin 3) K) i j *
      (![τ, τ ^ 2, 1] j - (ξ : K) * ![τ, τ ^ 2, 1] i) = 0 := by
    intro i j
    have h1 : (c : Matrix (Fin 3) (Fin 3) K) i j * ![τ, τ ^ 2, 1] j =
        (ξ : K) * ![τ, τ ^ 2, 1] i * (c : Matrix (Fin 3) (Fin 3) K) i j := by
      simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Pi.smul_apply]
        using congrFun (congrFun h2 i) j
    calc (c : Matrix (Fin 3) (Fin 3) K) i j * (![τ, τ ^ 2, 1] j - (ξ : K) * ![τ, τ ^ 2, 1] i)
        = (c : Matrix (Fin 3) (Fin 3) K) i j * ![τ, τ ^ 2, 1] j -
            (c : Matrix (Fin 3) (Fin 3) K) i j * ((ξ : K) * ![τ, τ ^ 2, 1] i) := by ring
      _ = (ξ : K) * ![τ, τ ^ 2, 1] i * (c : Matrix (Fin 3) (Fin 3) K) i j -
            (ξ : K) * ![τ, τ ^ 2, 1] i * (c : Matrix (Fin 3) (Fin 3) K) i j := by rw [h1]; ring
      _ = 0 := by ring
  have hinj : Function.Injective fun v : Fin 3 → K => (c : Matrix (Fin 3) (Fin 3) K) *ᵥ v :=
    Matrix.mulVec_injective_of_isUnit c.isUnit
  have hex : ∀ j, ∃ i, (c : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    have hzero : (c : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1 = 0 := by
      rw [Matrix.mulVec_single_one]
      ext i
      simpa using hcon i
    have h1 := hinj (hzero.trans (Matrix.mulVec_zero _).symm)
    have h2 := congrFun h1 j
    simp at h2
  choose σ hσ using hex
  have hσuniq : ∀ j i, (c : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 → i = σ j := by
    intro j i hi
    by_contra hne
    have h1 : (![τ, τ ^ 2, 1] j : K) = (ξ : K) * ![τ, τ ^ 2, 1] i := by
      have := hentry i j
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hi)
    have h2 : (![τ, τ ^ 2, 1] j : K) = (ξ : K) * ![τ, τ ^ 2, 1] (σ j) := by
      have := hentry (σ j) j
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (hσ j))
    have h3 : (![τ, τ ^ 2, 1] i : K) = ![τ, τ ^ 2, 1] (σ j) := by
      apply mul_left_cancel₀ ξ.ne_zero
      exact h1.symm.trans h2
    exact hne (hlam h3)
  have hcol : ∀ j, (c : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1 =
      (c : Matrix (Fin 3) (Fin 3) K) (σ j) j • Pi.single (σ j) 1 := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext i
    by_cases hi : i = σ j
    · subst hi; simp
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
      by_contra hz
      exact hi (hσuniq j i hz)
  have hσinj : Function.Injective σ := by
    intro j j' h
    by_contra hne
    have h2 : (c : Matrix (Fin 3) (Fin 3) K) (σ j) j' ≠ 0 := by
      rw [h]; exact hσ j'
    let v : Fin 3 → K := Pi.single j 1 -
      ((c : Matrix (Fin 3) (Fin 3) K) (σ j) j /
        (c : Matrix (Fin 3) (Fin 3) K) (σ j) j') • Pi.single j' 1
    have hv : v ≠ 0 := by
      intro hv0
      have := congrFun hv0 j
      simp [v, hne] at this
    have hMv : (c : Matrix (Fin 3) (Fin 3) K) *ᵥ v = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hcol j, hcol j', h, smul_smul,
        div_mul_cancel₀ _ (hσ j'), sub_self]
    exact hv (hinj (hMv.trans (Matrix.mulVec_zero _).symm))
  have hσbij : Function.Bijective σ :=
    ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩
  let σe : Equiv.Perm (Fin 3) := Equiv.ofBijective σ hσbij
  refine ⟨σe, fun j => ⟨(c : Matrix (Fin 3) (Fin 3) K) (σ j) j, hσ j, ?_⟩⟩
  rw [Matrix.mulVec_single_one]
  funext i
  by_cases hij : i = σe j
  · subst hij
    simp [σe]
  · have hne : i ≠ σ j := by simpa [σe] using hij
    have hzero : (c : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
      by_contra hz
      exact hne (hσuniq j i hz)
    simp [Pi.single_eq_of_ne hij, hzero]
