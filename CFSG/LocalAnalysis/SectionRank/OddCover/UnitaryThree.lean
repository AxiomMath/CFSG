module

public import CFSG.LocalAnalysis.SectionRank.OddCover.LinearThree

public section

namespace CFSG.SectionRank.OddCover

open scoped commutatorElement

section Data

variable {S : Type*} [Group S]

@[expose] def CubicSylowData (p : ℕ) (x y h : S) : Prop :=
  (∃ Q : Sylow p S, (Q : Subgroup S) = Subgroup.closure ({x, y} : Set S)) ∧
  Nat.card (Subgroup.closure ({x, y} : Set S)) = p ^ 3 ∧
  (∀ g ∈ Subgroup.closure ({x, y} : Set S), g ^ p = 1) ∧
  orderOf ⁅x, y⁆ = p ∧
  (∀ g ∈ Subgroup.closure ({x, y} : Set S),
    (∀ q ∈ Subgroup.closure ({x, y} : Set S), Commute g q) ↔ g ∈ Subgroup.zpowers ⁅x, y⁆) ∧
  (∀ g ∈ Subgroup.closure ({x, y} : Set S), ∀ q ∈ Subgroup.closure ({x, y} : Set S),
    ⁅g, q⁆ ∈ Subgroup.zpowers ⁅x, y⁆) ∧
  h ∈ Subgroup.normalizer (Subgroup.closure ({x, y} : Set S) : Set S) ∧
  h * x * h⁻¹ = x ^ (p - 1) ∧ h * y * h⁻¹ = y ^ (p - 1) ∧ h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆

theorem commute_map_iff {S' : Type*} [Group S'] (e : S ≃* S') {a b : S} :
    Commute (e a) (e b) ↔ Commute a b :=
  ⟨fun h => by simpa using h.map e.symm, fun h => h.map e⟩

theorem CubicSylowData.map [Finite S] {S' : Type*} [Group S'] {p : ℕ} [Fact p.Prime]
    {x y h : S} (e : S ≃* S') (hd : CubicSylowData p x y h) :
    CubicSylowData p (e x) (e y) (e h) := by
  obtain ⟨⟨Q, hQ⟩, hcard, hexp, hord, hcen, hcomm, hnorm, hhx, hhy, hhz⟩ := hd
  have hcl : Subgroup.closure ({e x, e y} : Set S') =
      (Subgroup.closure ({x, y} : Set S)).map e.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hmem : ∀ g : S', g ∈ Subgroup.closure ({e x, e y} : Set S') ↔
      e.symm g ∈ Subgroup.closure ({x, y} : Set S) := fun g => by
    rw [hcl, Subgroup.mem_map_equiv]
  have hz : ⁅e x, e y⁆ = e ⁅x, y⁆ := (map_commutatorElement e x y).symm
  have hzmem : ∀ g : S', g ∈ Subgroup.zpowers ⁅e x, e y⁆ ↔
      e.symm g ∈ Subgroup.zpowers ⁅x, y⁆ := fun g => by
    rw [hz, show e ⁅x, y⁆ = e.toMonoidHom ⁅x, y⁆ from rfl, ← MonoidHom.map_zpowers,
      Subgroup.mem_map_equiv]
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨⟨Q.mapSurjective hsurj, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective hsurj Q, hQ, hcl]
  · rw [hcl, Subgroup.card_map_of_injective e.injective]
    exact hcard
  · intro g hg
    have h1 := hexp _ ((hmem g).1 hg)
    calc g ^ p = e (e.symm g ^ p) := by rw [map_pow, MulEquiv.apply_symm_apply]
      _ = 1 := by rw [h1, map_one]
  · rw [hz]
    exact (orderOf_injective e.toMonoidHom e.injective _).trans hord
  · intro g hg
    rw [hzmem, ← hcen _ ((hmem g).1 hg)]
    constructor
    · intro H q hq
      have := H (e q) ((hmem _).2 (by rwa [MulEquiv.symm_apply_apply]))
      rwa [← commute_map_iff e, MulEquiv.apply_symm_apply]
    · intro H q hq
      have := H (e.symm q) ((hmem q).1 hq)
      rwa [← commute_map_iff e, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  · intro g hg q hq
    rw [hzmem, map_commutatorElement]
    exact hcomm _ ((hmem g).1 hg) _ ((hmem q).1 hq)
  · rw [Subgroup.mem_normalizer_iff] at hnorm ⊢
    intro g
    have h2 : e.symm (e h * g * (e h)⁻¹) = h * e.symm g * h⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact (hmem g).trans ((hnorm (e.symm g)).trans (by rw [← h2]; exact (hmem _).symm))
  · rw [← map_inv, ← map_mul, ← map_mul, hhx, map_pow]
  · rw [← map_inv, ← map_mul, ← map_mul, hhy, map_pow]
  · rw [hz, ← map_inv, ← map_mul, ← map_mul, hhz]

theorem center_eq_zpowers_of_card_eq_cube {p : ℕ} [hp : Fact p.Prime] {Q : Subgroup S}
    (hQ : Nat.card Q = p ^ 3) {z : S} (hzQ : z ∈ Q) (hz : orderOf z = p)
    (hzc : ∀ q ∈ Q, Commute z q) {a b : S} (ha : a ∈ Q) (hb : b ∈ Q) (hab : ¬ Commute a b) :
    (∀ g ∈ Q, (∀ q ∈ Q, Commute g q) ↔ g ∈ Subgroup.zpowers z) ∧
      (∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁆ ∈ Subgroup.zpowers z) := by
  have hp' := hp.out
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact (pow_pos hp'.pos 3).ne')
  set N : Subgroup Q := (Subgroup.zpowers z).subgroupOf Q with hNdef
  have hzle : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le.2 hzQ
  have hNcard : Nat.card N = p := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, Nat.card_zpowers, hz]
  have hNc : N ≤ Subgroup.center Q := by
    intro q hq
    rw [hNdef, Subgroup.mem_subgroupOf] at hq
    obtain ⟨j, hj⟩ := hq
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hj]
    exact ((hzc g g.2).zpow_left j).symm.eq
  have : N.Normal := Subgroup.normal_of_le_center hNc
  have hquot : Nat.card (Q ⧸ N) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hQ, hNcard, show p ^ 3 = p ^ 2 * p by ring] at h
    exact (Nat.eq_of_mul_eq_mul_right hp'.pos h).symm
  have hcomm : IsMulCommutative (Q ⧸ N) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot
  have hcom : ∀ g ∈ Q, ∀ q ∈ Q, ⁅g, q⁆ ∈ Subgroup.zpowers z := by
    intro g hg q hq
    have h1 : QuotientGroup.mk' N ⁅(⟨g, hg⟩ : Q), ⟨q, hq⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.is_comm.comm _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf] at h1
    exact h1
  refine ⟨fun g hg => ⟨fun hgc => ?_, fun hgz q hq => ?_⟩, hcom⟩
  · by_contra hgz
    have hlt : N < Subgroup.center Q := by
      refine lt_of_le_of_ne hNc fun hNeq => hgz ?_
      have hgZ : (⟨g, hg⟩ : Q) ∈ Subgroup.center Q := by
        rw [Subgroup.mem_center_iff]
        intro q
        exact Subtype.ext (hgc q q.2).symm.eq
      rw [← hNeq, hNdef, Subgroup.mem_subgroupOf] at hgZ
      exact hgZ
    have hcard_lt := Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card (Subgroup.center Q) ∣ p ^ 3 := hQ ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp').1 hdvd
    rw [hNcard, hkc] at hcard_lt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have := hp'.two_le
      interval_cases k
      · rw [pow_zero] at hcard_lt
        omega
      · rw [pow_one] at hcard_lt
        omega
    have hcyc : IsCyclic (Q ⧸ Subgroup.center Q) := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
      rw [hQ, hkc] at h
      interval_cases k
      · apply isCyclic_of_prime_card (p := p)
        rw [show p ^ 3 = p * p ^ 2 by ring] at h
        exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp'.pos 2) h).symm
      · have h1 : Nat.card (Q ⧸ Subgroup.center Q) = 1 := by
          have := Nat.eq_of_mul_eq_mul_right (pow_pos hp'.pos 3)
            (show 1 * p ^ 3 = Nat.card (Q ⧸ Subgroup.center Q) * p ^ 3 by rw [← h, one_mul])
          exact this.symm
        have : Subsingleton (Q ⧸ Subgroup.center Q) :=
          (Nat.card_eq_one_iff_unique.1 h1).1
        infer_instance
    have hQc := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center Q)) (by rw [QuotientGroup.ker_mk'])
    exact hab (congrArg Subtype.val (hQc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · obtain ⟨j, rfl⟩ := hgz
    exact (hzc q hq).zpow_left j

theorem not_pow_four_dvd_of_sylow [Finite S] {p : ℕ} [hp : Fact p.Prime] (Q : Sylow p S)
    (hQ : Nat.card (Q : Subgroup S) = p ^ 3) : ¬ p ^ 4 ∣ Nat.card S := by
  intro h4
  have h := Sylow.card_eq_multiplicity Q
  rw [hQ] at h
  have h3 := Nat.pow_right_injective hp.out.two_le h
  have h4' := (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h4
  omega

theorem CubicSylowData.sylow_kernel_eq_bot [Finite S] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {x y h : S} (hd : CubicSylowData p x y h) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (Cp : Sylow p π.ker) : (Cp : Subgroup π.ker) = ⊥ := by
  obtain ⟨⟨Q, hQ⟩, hcard, hexp, hord, hcen, -, -, hhx, hhy, hhz⟩ := hd
  have hxQ : x ∈ Subgroup.closure ({x, y} : Set S) := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Subgroup.closure ({x, y} : Set S) := Subgroup.subset_closure (by simp)
  have hzQ : ⁅x, y⁆ ∈ Subgroup.closure ({x, y} : Set S) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxQ hyQ)
      (Subgroup.inv_mem _ hxQ)) (Subgroup.inv_mem _ hyQ)
  have hzc := (hcen _ hzQ).2 (Subgroup.mem_zpowers _)
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact hp.out.one_lt.ne hord
  exact cubic_extraspecial_sylow_central_kernel π hπ hC (hexp x hxQ) (hexp y hyQ) hz1
    (hzc x hxQ) (hzc y hyQ) hcard (not_pow_four_dvd_of_sylow Q (by rw [hQ, hcard]))
    (a := p - 1) (b := 0) (c := 0) (d := p - 1) (k := 0) (l := 0) (μ := 1)
    (by rw [hhx, pow_zero, pow_zero, mul_one, mul_one])
    (by rw [hhy, pow_zero, pow_zero, one_mul, mul_one]) (by rw [hhz, pow_one])
    (det_ne_zero_of_neg_one hp.out.one_lt.le (not_dvd_four_of_odd hp2)) Cp

theorem isMulCommutative_of_card_eq_pow_le_two {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
    {k : ℕ} (hk : k ≤ 2) (h : Nat.card G = p ^ k) : IsMulCommutative G := by
  interval_cases k
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 (by rw [h, pow_zero])).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : IsCyclic G := isCyclic_of_prime_card (p := p) (by rw [h, pow_one])
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq h

theorem conj_mem_closure_pair {x y h : S} (hx : h * x * h⁻¹ ∈ Subgroup.closure ({x, y} : Set S))
    (hy : h * y * h⁻¹ ∈ Subgroup.closure ({x, y} : Set S)) {g : S}
    (hg : g ∈ Subgroup.closure ({x, y} : Set S)) :
    h * g * h⁻¹ ∈ Subgroup.closure ({x, y} : Set S) := by
  induction hg using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with rfl | rfl
    · exact hx
    · exact hy
  | one => simp
  | mul q r _ _ hq hr =>
    rw [show h * (q * r) * h⁻¹ = (h * q * h⁻¹) * (h * r * h⁻¹) by group]
    exact Subgroup.mul_mem _ hq hr
  | inv q _ hq =>
    rw [show h * q⁻¹ * h⁻¹ = (h * q * h⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hq

theorem commute_of_mem_closure_pair {x y z : S} (hx : Commute z x) (hy : Commute z y) {g : S}
    (hg : g ∈ Subgroup.closure ({x, y} : Set S)) : Commute z g := by
  induction hg using Subgroup.closure_induction with
  | mem q hq =>
    rcases hq with rfl | rfl
    · exact hx
    · exact hy
  | one => exact Commute.one_right z
  | mul q r _ _ hq hr => exact hq.mul_right hr
  | inv q _ hq => exact hq.inv_right

theorem pow_sub_one_eq_inv_of_pow_eq_one {x : S} {p : ℕ} (hp : 1 ≤ p) (hx : x ^ p = 1) :
    x ^ (p - 1) = x⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hp, hx])

end Data

section Heisenberg

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem heis_mul (a b a' b' : K) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b * heisenbergMatrix σ 0 1 a' b' =
      heisenbergMatrix σ 0 1 (a + a') (b + b' - a * σ a') :=
  heisenbergMatrix_mul σ (by decide) (by decide) (by decide) a b a' b'

theorem heis_pow (a b : K) (n : ℕ) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b ^ n =
      heisenbergMatrix σ 0 1 ((n : K) * a) ((n : K) * b - (n.choose 2 : ℕ) * (a * σ a)) := by
  induction n with
  | zero => simp [heisenbergMatrix_zero]
  | succ n ih =>
    rw [pow_succ, ih, heis_mul, Nat.choose_succ_succ, Nat.choose_one_right]
    congr 1 <;> push_cast <;> ring

variable (hσ : ∀ c, σ (σ c) = c)

@[expose] noncomputable def heisSU (a b : K) (hab : b + σ b + σ a * a = 0) : SU σ 3 :=
  ⟨⟨heisenbergMatrix σ 0 1 a b, heisenbergMatrix σ 0 1 (-a) (-b - a * σ a),
    by
      rw [heis_mul, map_neg, add_neg_cancel, show b + (-b - a * σ a) - a * -σ a = 0 by ring,
        heisenbergMatrix_zero],
    by
      rw [heis_mul, neg_add_cancel, show -b - a * σ a + b - -a * σ a = 0 by ring,
        heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ (by decide) (by decide) (by decide) a b,
    heisenbergMatrix_isometry σ hσ (by decide) (by decide) (by decide) hab⟩

theorem coe_heisSU (a b : K) (hab : b + σ b + σ a * a = 0) :
    (((heisSU hσ a b hab : SU σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix σ 0 1 a b :=
  rfl

theorem coe_heisSU_inv (a b : K) (hab : b + σ b + σ a * a = 0) :
    ((((heisSU hσ a b hab)⁻¹ : SU σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      heisenbergMatrix σ 0 1 (-a) (-b - a * σ a) :=
  rfl

omit hσ in
theorem SU_ext {g g' : SU σ 3}
    (h : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((g' : GL (Fin 3) K) : Matrix _ _ K)) :
    g = g' :=
  Subtype.ext (Units.ext h)

theorem heisSU_mul (a b a' b' : K) (hab : b + σ b + σ a * a = 0)
    (hab' : b' + σ b' + σ a' * a' = 0)
    (h'' : b + b' - a * σ a' + σ (b + b' - a * σ a') + σ (a + a') * (a + a') = 0) :
    heisSU hσ a b hab * heisSU hσ a' b' hab' = heisSU hσ (a + a') (b + b' - a * σ a') h'' :=
  SU_ext (heis_mul a b a' b')

theorem heisSU_inv_eq (a b : K) (hab : b + σ b + σ a * a = 0) (hb : σ b = b)
    (hab' : b + σ b + σ (-a) * -a = 0) : (heisSU hσ a b hab)⁻¹ = heisSU hσ (-a) b hab' := by
  apply SU_ext
  rw [coe_heisSU_inv, coe_heisSU]
  congr 1
  rw [hb] at hab
  linear_combination -hab

theorem commutator_heisSU (a b c d : K) (hab : b + σ b + σ a * a = 0)
    (hcd : d + σ d + σ c * c = 0)
    (h0 : c * σ a - a * σ c + σ (c * σ a - a * σ c) + σ 0 * 0 = 0) :
    ⁅heisSU hσ a b hab, heisSU hσ c d hcd⁆ = heisSU hσ 0 (c * σ a - a * σ c) h0 := by
  apply SU_ext
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_heisSU_inv, coe_heisSU_inv, coe_heisSU, coe_heisSU, coe_heisSU, heis_mul, heis_mul,
    heis_mul]
  congr 1
  · ring
  · simp only [map_neg]
    ring

theorem commute_heisSU_zero (β a b : K) (hβ : β + σ β + σ 0 * 0 = 0)
    (hab : b + σ b + σ a * a = 0) : Commute (heisSU hσ 0 β hβ) (heisSU hσ a b hab) := by
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_heisSU, coe_heisSU, heis_mul, heis_mul]
  congr 1
  · ring
  · simp only [map_zero, mul_zero, zero_mul]
    ring

omit hσ in
theorem diag_mul_self : (diagonal ![-1, 1, -1] : Matrix (Fin 3) (Fin 3) K) *
    diagonal ![-1, 1, -1] = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

omit hσ in
theorem diag_isometry : conjTr σ (diagonal ![-1, 1, -1] : Matrix (Fin 3) (Fin 3) K) *
    antidiag 3 * diagonal ![-1, 1, -1] = antidiag 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three, diagonal, Fin.rev]

omit hσ in
@[expose] noncomputable def hSU : SU σ 3 :=
  ⟨⟨diagonal ![-1, 1, -1], diagonal ![-1, 1, -1], diag_mul_self, diag_mul_self⟩,
    by simp [Fin.prod_univ_three], diag_isometry⟩

omit hσ in
theorem hSU_inv : (hSU : SU σ 3)⁻¹ = hSU :=
  inv_eq_of_mul_eq_one_left (SU_ext diag_mul_self)

theorem hSU_conj_heisSU (a b : K) (hab : b + σ b + σ a * a = 0)
    (hab' : b + σ b + σ (-a) * -a = 0) :
    hSU * heisSU hσ a b hab * hSU⁻¹ = heisSU hσ (-a) b hab' := by
  rw [hSU_inv]
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_heisSU, coe_heisSU]
  show diagonal ![-1, 1, -1] * heisenbergMatrix σ 0 1 a b * diagonal ![-1, 1, -1] = _
  rw [CFSG.LieType.Steinberg.heisenbergMatrix_three, CFSG.LieType.Steinberg.heisenbergMatrix_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal]

end Heisenberg

section Unitary

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem not_pow_four_dvd_card_SU_three [CharP K p] (hK : Nat.card K = (p ^ 1) ^ 2) :
    ¬ p ^ 4 ∣ Nat.card (SU (unitaryInvolution K p 1) 3) := by
  have hp' := hp.out
  rw [card_SU_three hK, pow_one]
  intro h
  have h1 : p ^ 3 * p ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    rw [← pow_succ, ← mul_assoc]; exact h
  have h2 : p ∣ (p ^ 2 - 1) * (p ^ 3 + 1) :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hp'.pos 3) h1
  rcases (Nat.Prime.dvd_mul hp').1 h2 with h3 | h3
  · have := Nat.dvd_sub (dvd_pow_self p two_ne_zero) h3
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp'.pos)] at this
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)
  · have := (Nat.dvd_add_right (dvd_pow_self p three_ne_zero)).1 h3
    exact hp'.one_lt.ne' (Nat.dvd_one.1 this)

theorem cubicSylowData_SU [CharP K p] (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ 1) ^ 2) :
    ∃ x y h : SU (unitaryInvolution K p 1) 3, CubicSylowData p x y h := by
  have hp' := hp.out
  set σ := unitaryInvolution K p 1 with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have h22 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  obtain ⟨ζ, hζ0, hζ'⟩ := exists_unitaryInvolution_eq_neg hK
  have hζ : σ ζ = -ζ := hζ'
  have hσ2 : σ (2⁻¹ : K) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  have hb1 : σ (-2⁻¹ : K) = -2⁻¹ := by rw [map_neg, hσ2]
  have hx : (-2⁻¹ : K) + σ (-2⁻¹) + σ 1 * 1 = 0 := by
    rw [hb1, map_one]; linear_combination -h22
  have hx' : (-2⁻¹ : K) + σ (-2⁻¹) + σ (-1) * -1 = 0 := by
    rw [hb1, map_neg, map_one]; linear_combination -h22
  have hb2 : σ (ζ ^ 2 * 2⁻¹) = ζ ^ 2 * 2⁻¹ := by rw [map_mul, map_pow, hσ2, hζ, neg_sq]
  have hy : ζ ^ 2 * 2⁻¹ + σ (ζ ^ 2 * 2⁻¹) + σ ζ * ζ = 0 := by
    rw [hb2, hζ]; linear_combination ζ ^ 2 * h22
  have hy' : ζ ^ 2 * 2⁻¹ + σ (ζ ^ 2 * 2⁻¹) + σ (-ζ) * -ζ = 0 := by
    rw [hb2, map_neg, hζ]; linear_combination ζ ^ 2 * h22
  have hβ : ζ * σ 1 - 1 * σ ζ + σ (ζ * σ 1 - 1 * σ ζ) + σ 0 * 0 = 0 := by
    simp only [map_sub, map_mul, map_one, map_zero, hζ, map_neg]
    ring
  have hβ' : ζ * σ 1 - 1 * σ ζ + σ (ζ * σ 1 - 1 * σ ζ) + σ (-0) * -0 = 0 := by
    rw [neg_zero]; exact hβ
  set x := heisSU hσ 1 (-2⁻¹) hx with hxdef
  set y := heisSU hσ ζ (ζ ^ 2 * 2⁻¹) hy with hydef
  set z := heisSU hσ 0 (ζ * σ 1 - 1 * σ ζ) hβ with hzdef
  set Q := Subgroup.closure ({x, y} : Set (SU σ 3)) with hQdef
  have hxy : ⁅x, y⁆ = z := commutator_heisSU hσ 1 _ ζ _ hx hy hβ
  have hz1 : z ≠ 1 := by
    intro h1
    have h02 := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) h1
    have h0 : ζ * σ 1 - 1 * σ ζ = 0 := by
      simpa [hzdef, coe_heisSU, heisenbergMatrix_three] using h02
    rw [map_one, hζ] at h0
    have h0' : 2 * ζ = 0 := by linear_combination h0
    exact hζ0 ((mul_eq_zero.1 h0').resolve_left h2)
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hzQ : z ∈ Q := by
    rw [← hxy, commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hyQ) (Q.inv_mem hxQ)) (Q.inv_mem hyQ)
  set X := heisenbergSubgroup σ hσ (i := (0 : Fin 3)) (k := 1) (by decide) (by decide)
    (by decide) with hXdef
  have hQX : Q ≤ X := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨1, -2⁻¹, hx, rfl⟩
    · exact ⟨ζ, ζ ^ 2 * 2⁻¹, hy, rfl⟩
  have hXcard : Nat.card X = p ^ 3 := by
    have h := card_rootGroup_three hK
    rw [rootGroup_three_eq_heisenbergSubgroup, pow_one] at h
    exact h
  have hexpX : ∀ g ∈ X, g ^ p = 1 := by
    rintro g ⟨a, b, -, hg⟩
    have hdvd : p ∣ p.choose 2 := hp'.dvd_choose_self (by norm_num)
      (by have := hp'.two_le; omega)
    apply SU_ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, heis_pow, CharP.cast_eq_zero,
      (CharP.cast_eq_zero_iff K p _).2 hdvd, zero_mul, zero_mul, zero_mul, sub_zero,
      heisenbergMatrix_zero]
    rfl
  have hexp : ∀ g ∈ Q, g ^ p = 1 := fun g hg => hexpX g (hQX hg)
  have hnc : ¬ Commute x y := fun hc =>
    hz1 (hxy ▸ commutatorElement_eq_one_iff_commute.2 hc)
  have hQcard : Nat.card Q = p ^ 3 := by
    have hQdvd : Nat.card Q ∣ p ^ 3 := hXcard ▸ Subgroup.card_dvd_of_le hQX
    obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp').1 hQdvd
    have hk3 : k = 3 := by
      by_contra hk3
      have hcomm := isMulCommutative_of_card_eq_pow_le_two (by omega : k ≤ 2) hkc
      exact hnc (congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hxQ⟩ ⟨y, hyQ⟩))
    rw [hkc, hk3]
  have hfact : (Nat.card (SU σ 3)).factorization p = 3 := by
    have h3 : p ^ 3 ∣ Nat.card (SU σ 3) := hQcard ▸ Subgroup.card_subgroup_dvd_card _
    have h3' := (hp'.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h3
    have h4 : ¬ 4 ≤ (Nat.card (SU σ 3)).factorization p := fun h4 =>
      not_pow_four_dvd_card_SU_three hK ((hp'.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 h4)
    omega
  have hhx : hSU * x * hSU⁻¹ = x⁻¹ := by
    rw [hxdef, hSU_conj_heisSU hσ 1 _ hx hx', heisSU_inv_eq hσ 1 _ hx hb1 hx']
  have hhy : hSU * y * hSU⁻¹ = y⁻¹ := by
    rw [hydef, hSU_conj_heisSU hσ ζ _ hy hy', heisSU_inv_eq hσ ζ _ hy hb2 hy']
  have hhz : hSU * z * hSU⁻¹ = z := by
    rw [hzdef, hSU_conj_heisSU hσ 0 _ hβ hβ']
    exact SU_ext (by rw [coe_heisSU, coe_heisSU, neg_zero])
  have hh2 : (hSU : SU σ 3) * hSU = 1 := by
    nth_rewrite 2 [← hSU_inv]
    exact mul_inv_cancel _
  have hzc : ∀ q ∈ Q, Commute z q := fun q hq =>
    commute_of_mem_closure_pair (commute_heisSU_zero hσ _ 1 _ hβ hx)
      (commute_heisSU_zero hσ _ ζ _ hβ hy) hq
  have hord : orderOf z = p := orderOf_eq_prime (hexp z hzQ) hz1
  obtain ⟨hcen, hcomm⟩ := center_eq_zpowers_of_card_eq_cube hQcard hzQ hord hzc hxQ hyQ hnc
  refine ⟨x, y, hSU, ⟨Sylow.ofCard Q (by rw [hQcard, hfact]), Sylow.coe_ofCard _ _⟩, hQcard,
    hexp, hxy ▸ hord, hxy ▸ hcen, hxy ▸ hcomm, ?_, ?_, ?_, hxy ▸ hhz⟩
  · have hconj : ∀ g ∈ Q, hSU * g * hSU⁻¹ ∈ Q := fun g hg =>
      conj_mem_closure_pair (by rw [hhx]; exact Q.inv_mem hxQ) (by rw [hhy]; exact Q.inv_mem hyQ)
        hg
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj g, fun hg => ?_⟩
    have h1 := hconj _ hg
    rwa [hSU_inv, show hSU * (hSU * g * hSU) * hSU = (hSU * hSU) * g * (hSU * hSU) by group, hh2,
      one_mul, mul_one] at h1
  · rw [hhx, pow_sub_one_eq_inv_of_pow_eq_one hp'.one_lt.le (hexp x hxQ)]
  · rw [hhy, pow_sub_one_eq_inv_of_pow_eq_one hp'.one_lt.le (hexp y hyQ)]

theorem odd_unitary_three_sylow_normalizer (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) :
    ∃ x y h : StatedSU 3 p K, CubicSylowData p x y h := by
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have : CharP K p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨x, y, h, hd⟩ := cubicSylowData_SU hp2 hK1
  let e : SU (unitaryInvolution K p 1) 3 ≃* StatedSU 3 p K :=
    (equivStatedSU hK1 3).trans (MulEquiv.subgroupCongr (by rw [pow_one]))
  exact ⟨e x, e y, e h, hd.map e⟩

theorem statedSU_three_sylow_kernel_eq_bot (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (π : E →* StatedSU 3 p K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (Cp : Sylow p π.ker) :
    (Cp : Subgroup π.ker) = ⊥ := by
  obtain ⟨x, y, h, hd⟩ := odd_unitary_three_sylow_normalizer hp2 hK
  exact hd.sylow_kernel_eq_bot hp2 π hπ hC Cp

end Unitary

end CFSG.SectionRank.OddCover
