module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TightEnd
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian
public import CFSG.Walter.J1Props.Elt

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open Matrix
open scoped MatrixGroups

theorem matrix_pow_card_eq_zero_of_pow_eq_zero {K : Type*} [Field K] {n : ℕ}
    {N : Matrix (Fin n) (Fin n) K} {m : ℕ} (h : N ^ m = 0) : N ^ n = 0 := by
  have h1 : (Matrix.toLinAlgEquiv' N) ^ m = 0 := by
    rw [← map_pow, h, map_zero]
  have h2 : LinearMap.ker ((Matrix.toLinAlgEquiv' N) ^ m) ≤
      LinearMap.ker ((Matrix.toLinAlgEquiv' N) ^ (Module.finrank K (Fin n → K))) :=
    Module.End.ker_pow_le_ker_pow_finrank _ m
  rw [h1] at h2
  have h3 : (Matrix.toLinAlgEquiv' N) ^ (Module.finrank K (Fin n → K)) = 0 := by
    refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker ((Matrix.toLinAlgEquiv' N) ^ (Module.finrank K (Fin n → K))) :=
      h2 (by simp)
    simpa using this
  rw [Module.finrank_fin_fun] at h3
  have h4 := congrArg (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).symm h3
  rw [map_pow, AlgEquiv.symm_apply_apply, map_zero] at h4
  exact h4

theorem matrix_pow_four_eq_one_of_charTwo {K : Type*} [Field K] [CharP K 2] {n : ℕ} (hn : n ≤ 4)
    {X : Matrix (Fin n) (Fin n) K} {k : ℕ} (hX : X ^ (2 ^ k) = 1) : X ^ 4 = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Subsingleton.elim _ _
  have : NeZero n := ⟨hpos.ne'⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin n) (Fin n) K := X - 1 with hN
  have hNk : N ^ (2 ^ k) = 0 := by
    rw [hN, sub_pow_char_pow_of_commute 2 k (Commute.one_right X), hX, one_pow, sub_self]
  have hNn : N ^ n = 0 := matrix_pow_card_eq_zero_of_pow_eq_zero hNk
  have hN4 : N ^ 4 = 0 := by
    have : N ^ 4 = N ^ (4 - n) * N ^ n := by rw [← pow_add]; congr 1; omega
    rw [this, hNn, mul_zero]
  have hX' : X = N + 1 := by rw [hN]; abel
  have h4 : X ^ 4 = N ^ 4 + 1 ^ 4 := by
    rw [hX']
    have := add_pow_char_pow_of_commute (R := Matrix (Fin n) (Fin n) K) (x := N) (y := 1) 2 2
      (Commute.one_right N)
    simpa using this
  rw [h4, hN4]
  simp

@[expose] def TwoElementsPowFour (G : Type*) [Group G] : Prop :=
  ∀ (y : G) (k : ℕ), y ^ (2 ^ k) = 1 → y ^ 4 = 1

theorem TwoElementsPowFour.of_injective {G H : Type*} [Group G] [Group H]
    (hH : TwoElementsPowFour H) (φ : G →* H) (hφ : Function.Injective φ) :
    TwoElementsPowFour G := fun y k hy =>
  hφ (by
    rw [map_pow, map_one]
    exact hH (φ y) k (by rw [← map_pow, hy, map_one]))

theorem twoElementsPowFour_gl {K : Type*} [Field K] [CharP K 2] {n : ℕ} (hn : n ≤ 4) :
    TwoElementsPowFour (GL (Fin n) K) := by
  intro y k hy
  apply Units.ext
  have h1 : ((y : Matrix (Fin n) (Fin n) K)) ^ (2 ^ k) = 1 := by
    have := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hy
    simpa [Units.val_pow_eq_pow_val] using this
  simpa [Units.val_pow_eq_pow_val] using matrix_pow_four_eq_one_of_charTwo hn h1

theorem twoElementsPowFour_pgl {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : n ≤ 4) :
    TwoElementsPowFour PGL(n, K) := by
  intro x k hx
  induction x using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
  obtain ⟨u, hu⟩ := hx
  have hsurj := (bijective_iterateFrobenius K 2 k).2 (u : K)
  obtain ⟨c, hc⟩ := hsurj
  rw [iterateFrobenius_def] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : (u : K) = 0 := by rw [← hc]; simp
    exact u.ne_zero this
  have hcu : (Units.mk0 c hc0) ^ (2 ^ k) = u := Units.ext (by simpa using hc)
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0)⁻¹ ∈
      Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hcent : Commute g (Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0)⁻¹) :=
    Subgroup.mem_center_iff.mp hmem g
  have key : (g * Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0)⁻¹) ^ (2 ^ k) = 1 := by
    rw [hcent.mul_pow, ← hu, ← map_pow, inv_pow, hcu, ← map_mul, mul_inv_cancel, map_one]
  have h4 := twoElementsPowFour_gl (K := K) hn _ k key
  have h5 : Matrix.ProjGenLinGroup.mk
      (g * Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0)⁻¹) =
      Matrix.ProjGenLinGroup.mk g := by
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
  rw [← h5, ← map_pow, h4, map_one]

theorem twoElementsPowFour_psl {K : Type*} [Field K] [Finite K] [CharP K 2] :
    TwoElementsPowFour PSL(2, K) :=
  (twoElementsPowFour_pgl (K := K) (n := 2) (by norm_num)).of_injective
    Matrix.ProjectiveSpecialLinearGroup.toPGL Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

theorem twoElementsPowFour_sz (n : ℕ) : TwoElementsPowFour (Sz n) :=
  (twoElementsPowFour_gl (K := GaloisField 2 (2 * n + 1)) (n := 4) le_rfl).of_injective
    (Sz n).subtype (Sz n).subtype_injective

theorem twoElementsPowFour_psu3 (f : ℕ) (hf : f ≠ 0) :
    TwoElementsPowFour (PSU3 2 f) := by
  have : NeZero (2 * f) := ⟨Nat.mul_ne_zero two_ne_zero hf⟩
  exact (twoElementsPowFour_pgl (K := GaloisField 2 (2 * f)) (n := 3) (by norm_num)).of_injective
    (PSU3 2 f).subtype (PSU3 2 f).subtype_injective

theorem not_isCyclic_sylow_of_isPerfect {G : Type*} [Group G] [Finite G]
    (hperf : Group.IsPerfect G) (P : Sylow 2 G) (hP : Nat.card ↥(P : Subgroup G) ≠ 1) :
    ¬ IsCyclic ↥(P : Subgroup G) := by
  intro hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hP (by simpa using ha)
  have h2 : 2 ∣ Nat.card G :=
    (dvd_pow_self 2 ha0).trans (ha ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G))
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hnorm := IsCyclic.normalizer_le_centralizer hmin hcyc
  have hcomp := IsCyclic.isComplement' hmin hcyc
  let f := MonoidHom.transferSylow P hnorm
  have hf := hom_trivial_of_perfect_of_commute hperf f fun x y =>
    (IsMulCommutative.is_comm (M := ↥(P : Subgroup G))).comm (f x) (f y)
  have hker : f.ker = ⊤ := by
    ext x
    simp [hf x]
  have hcard := hcomp.card_mul_card
  rw [hker, Subgroup.card_top] at hcard
  have hG0 : 0 < Nat.card G := Nat.card_pos
  exact hP (Nat.eq_of_mul_eq_mul_left hG0 (hcard.trans (mul_one _).symm))

theorem pow_four_eq_one_of_card_two_part {F : Type*} [Group F] [Finite F]
    (hperf : Group.IsPerfect F) (T : Sylow 2 F) {j k : ℕ} (hj : j ≤ 3) (hk : Odd k)
    (hcard : Nat.card F = 2 ^ j * k) : ∀ x ∈ (T : Subgroup F), x ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨a, ha⟩ := T.isPGroup'.exists_card_eq
  have hdvd : Nat.card (T : Subgroup F) ∣ 2 ^ j := by
    have h1 : 2 ^ a ∣ 2 ^ j * k := by
      rw [← ha, ← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime (2 ^ a) k := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hk)
    rw [ha]
    exact hcop.dvd_of_dvd_mul_right h1
  have hord : orderOf x ∣ 2 ^ j := (Subgroup.orderOf_dvd_natCard (T : Subgroup F) hx).trans hdvd
  by_cases h4 : orderOf x ∣ 4
  · exact orderOf_dvd_iff_pow_eq_one.mp h4
  · exfalso
    have h8 : orderOf x = 8 := by
      obtain ⟨b, hb, hbeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      by_cases hb3 : b = 3
      · rw [hbeq, hb3]
        norm_num
      · exfalso
        apply h4
        rw [hbeq]
        exact (Nat.pow_dvd_pow 2 (by omega : b ≤ 2))
    have h8T : 8 ∣ Nat.card (T : Subgroup F) := h8 ▸ Subgroup.orderOf_dvd_natCard _ hx
    have hj3 : j = 3 := by
      have : 8 ∣ 2 ^ j := h8T.trans hdvd
      interval_cases j <;> simp_all
    have hTcard : Nat.card (T : Subgroup F) = 8 := by
      rw [hj3] at hdvd
      exact Nat.dvd_antisymm hdvd h8T
    have hcyc : IsCyclic ↥(T : Subgroup F) :=
      isCyclic_of_orderOf_eq_card (⟨x, hx⟩ : ↥(T : Subgroup F))
        (by rw [Subgroup.orderOf_mk, hTcard, h8])
    exact not_isCyclic_sylow_of_isPerfect hperf T (by rw [hTcard]; norm_num) hcyc

theorem psl2_card_eq_four_mul_odd {n : ℕ} (h8 : n % 8 = 3 ∨ n % 8 = 5) :
    ∃ k, Odd k ∧ n * (n ^ 2 - 1) / 2 = 4 * k := by
  rcases h8 with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, n = 8 * j + 3 := ⟨n / 8, by omega⟩
    refine ⟨(8 * j + 3) * (8 * j ^ 2 + 6 * j + 1), ?_, ?_⟩
    · exact Odd.mul ⟨4 * j + 1, by ring⟩ ⟨4 * j ^ 2 + 3 * j, by ring⟩
    · have h1 : (8 * j + 3) ^ 2 - 1 = 8 * (8 * j ^ 2 + 6 * j + 1) := by
        have : (8 * j + 3) ^ 2 = 8 * (8 * j ^ 2 + 6 * j + 1) + 1 := by ring
        omega
      rw [h1]
      have h2 : (8 * j + 3) * (8 * (8 * j ^ 2 + 6 * j + 1)) =
          2 * (4 * ((8 * j + 3) * (8 * j ^ 2 + 6 * j + 1))) := by ring
      rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  · obtain ⟨j, rfl⟩ : ∃ j, n = 8 * j + 5 := ⟨n / 8, by omega⟩
    refine ⟨(8 * j + 5) * (8 * j ^ 2 + 10 * j + 3), ?_, ?_⟩
    · exact Odd.mul ⟨4 * j + 2, by ring⟩ ⟨4 * j ^ 2 + 5 * j + 1, by ring⟩
    · have h1 : (8 * j + 5) ^ 2 - 1 = 8 * (8 * j ^ 2 + 10 * j + 3) := by
        have : (8 * j + 5) ^ 2 = 8 * (8 * j ^ 2 + 10 * j + 3) + 1 := by ring
        omega
      rw [h1]
      have h2 : (8 * j + 5) * (8 * (8 * j ^ 2 + 10 * j + 3)) =
          2 * (4 * ((8 * j + 5) * (8 * j ^ 2 + 10 * j + 3))) := by ring
      rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]

theorem three_pow_odd_mod_eight' (m : ℕ) : 3 ^ (2 * m + 1) % 8 = 3 := by
  have h9 : (3 ^ 2) ^ m % 8 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [pow_succ, pow_mul, Nat.mul_mod, h9]

theorem ordRee_eq_eight_mul_odd (m : ℕ) : ∃ k, Odd k ∧ ordRee (3 ^ (2 * m + 1)) = 8 * k := by
  obtain ⟨q, hqdef⟩ : ∃ q, q = 3 ^ (2 * m + 1) := ⟨_, rfl⟩
  rw [← hqdef]
  have hq8 : q % 8 = 3 := hqdef ▸ three_pow_odd_mod_eight' m
  have hq3 : q ^ 3 % 8 = 3 := by
    rw [Nat.pow_mod, hq8]
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨a, ha, haodd⟩ : ∃ a, q ^ 3 + 1 = 4 * a ∧ a % 2 = 1 :=
    ⟨(q ^ 3 + 1) / 4, by omega, by omega⟩
  obtain ⟨b, hb, hbodd⟩ : ∃ b, q - 1 = 2 * b ∧ b % 2 = 1 := ⟨(q - 1) / 2, by omega, by omega⟩
  refine ⟨q ^ 3 * a * b, Odd.mul (Odd.mul hqodd.pow (Nat.odd_iff.mpr haodd))
    (Nat.odd_iff.mpr hbodd), ?_⟩
  unfold ordRee
  rw [ha, hb]
  ring

theorem card_goldschmidtJ1_eq : Nat.card goldschmidtJ1 = 2 ^ 3 * 21945 := by
  rw [show goldschmidtJ1 = walterJ1 from rfl, CFSG.Walter.J1Props.card_walterJ1]
  norm_num

abbrev GoldschmidtMilestone : Prop :=
  type_of% @CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian

theorem goldschmidtSimpleType_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L) : goldschmidtSimpleType L' := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
    ⟨p, f, hp, hodd, hf0, h5, hmod, ⟨e'⟩⟩ | ⟨m, hm, hcard⟩ | he'
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf0, h5, hmod, ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, by rw [← Nat.card_congr e.toEquiv, hcard]⟩))))
  · obtain ⟨e'⟩ := he'
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩))))

theorem exists_noncomm_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∃ a b : G, a * b ≠ b * a) : ∃ a b : H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem goldschmidtSimpleType_of_milestone (h : GoldschmidtMilestone) {F : Type} [Group F]
    [Finite F] [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) (T : Sylow 2 F)
    {A : Subgroup F} (hA1 : A ≠ ⊥) (hAT : A ≤ (T : Subgroup F)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : F, g⁻¹ * a * g ∈ (T : Subgroup F) → g⁻¹ * a * g ∈ A) :
    goldschmidtSimpleType F := by
  obtain ⟨-, -, hc⟩ := h F T A hAT hAab hcl
  set M : Subgroup F := Subgroup.normalClosure (A : Set F) with hM
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h0 | h0
    · exact absurd (le_bot_iff.mp (h0 ▸ hAM)) hA1
    · exact h0
  let eM : ↥M ≃* F := (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hF2 : 2 ∣ Nat.card F := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := T.isPGroup'.exists_card_eq
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hT1 : Nat.card (T : Subgroup F) = 1 := by simpa using ha
      have : (T : Subgroup F) = ⊥ := Subgroup.eq_bot_of_card_eq _ hT1
      exact hA1 (le_bot_iff.mp (this ▸ hAT))
    exact (dvd_pow_self 2 ha0).trans (ha ▸ Subgroup.card_subgroup_dvd_card (T : Subgroup F))
  have hodd : goldschmidtOddCore ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (goldschmidtOddCore ↥M) with h0 | h0
    · exact h0
    · exfalso
      have hoddcard : Odd (Nat.card (goldschmidtOddCore ↥M)) :=
        CFSG.ComponentClassification.OddCore.odd_card ↥M
      rw [h0, Subgroup.card_top, Nat.card_congr eM.toEquiv] at hoddcard
      exact (Nat.not_even_iff_odd.mpr hoddcard) (even_iff_two_dvd.mpr hF2)
  let eQ : (↥M ⧸ goldschmidtOddCore ↥M) ≃* F :=
    ((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).trans eM
  have : IsSimpleGroup (↥M ⧸ goldschmidtOddCore ↥M) := eQ.isSimpleGroup
  have hP : IsSimpleGroup ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) :=
    Subgroup.topEquiv.isSimpleGroup
  have hPnab : ∃ a b : ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)), a * b ≠ b * a :=
    exists_noncomm_of_mulEquiv
      (Subgroup.topEquiv (G := ↥M ⧸ goldschmidtOddCore ↥M)).symm
      (exists_noncomm_of_mulEquiv eQ.symm hnab)
  obtain ⟨hquasi, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hPnab
  have hcomp : IsComponentOf (⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _, Group.isPerfect_def.mp hquasi.1, hquasi.2.1⟩
  have hS := hc ⊤ hcomp
  let e : (↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (↥M ⧸ goldschmidtOddCore ↥M))) ≃* F :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      Subgroup.topEquiv).trans eQ
  exact goldschmidtSimpleType_of_mulEquiv e hS

theorem goldschmidtStronglyClosedExponent_of_milestone (h : GoldschmidtMilestone) :
    GoldschmidtStronglyClosedExponent := by
  intro F _ _ _ hnab T A hA1 hAT hAab hcl x hx
  have hcl' : ∀ a ∈ A, ∀ g : F, g⁻¹ * a * g ∈ (T : Subgroup F) → g⁻¹ * a * g ∈ A := by
    intro a ha g hg
    have := hcl a ha g⁻¹ (by simpa using hg)
    simpa using this
  have hAab' : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAab a.1 a.2 b.1 b.2)⟩⟩
  have hS := goldschmidtSimpleType_of_milestone h hnab T hA1 hAT hAab' hcl'
  have hperf : Group.IsPerfect F := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : ∃ k, x ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have := pow_orderOf_eq_one (⟨x, hx⟩ : ↥(T : Subgroup F))
    rw [hk] at this
    simpa using congrArg Subtype.val this
  obtain ⟨k, hk⟩ := hx2
  rcases hS with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
    ⟨p, f, hp, hodd, hf0, h5, hmod, ⟨e⟩⟩ | ⟨m, hm, hcard⟩ | he
  · have : NeZero f := ⟨by omega⟩
    exact ((twoElementsPowFour_psl (K := GaloisField 2 f)).of_injective e.toMonoidHom
      e.injective) x k hk
  · exact ((twoElementsPowFour_sz n).of_injective e.toMonoidHom e.injective) x k hk
  · exact ((twoElementsPowFour_psu3 f (by omega)).of_injective e.toMonoidHom e.injective) x k hk
  · have hf0' : f ≠ 0 := by omega
    have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0'
    have hodd' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hp.out, hodd, hf0, hK⟩
    have hc := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p f) hodd'
    rw [hK] at hc
    obtain ⟨j, hj, hj4⟩ := psl2_card_eq_four_mul_odd hmod
    have hcardF : Nat.card F = 2 ^ 2 * j := by
      rw [Nat.card_congr e.toEquiv]
      exact hc.trans (hj4.trans (by norm_num))
    exact pow_four_eq_one_of_card_two_part hperf T (by norm_num) hj hcardF x hx
  · obtain ⟨j, hj, hj8⟩ := ordRee_eq_eight_mul_odd m
    have hcardF : Nat.card F = 2 ^ 3 * j := by
      rw [hcard, hj8]
      norm_num
    exact pow_four_eq_one_of_card_two_part hperf T (by norm_num) hj hcardF x hx
  · obtain ⟨e⟩ := he
    have hcardF : Nat.card F = 2 ^ 3 * 21945 := by
      rw [← card_goldschmidtJ1_eq, Nat.card_congr e.toEquiv]
    exact pow_four_eq_one_of_card_two_part hperf T (by norm_num) ⟨10972, by norm_num⟩
      hcardF x hx

end CFSG.ClassicalInvolution.Hat2A7
