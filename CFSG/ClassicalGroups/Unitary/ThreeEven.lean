module

public import CFSG.Blueprint.Catalog
import CFSG.Quasithin.Vol2.Ch8Sec2L829NKU3InA
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bZsig
import CFSG.LocalAnalysis.WeakClosure81.EightFiveU3Aut

public section

namespace CFSG.ClassicalGroups.Unitary

open CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.Quasithin.H13.L829NK.U3In Matrix
open scoped commutatorElement

private theorem exists_unit_orderOf_eq_add_one {K : Type} [Field K] [Finite K] {q : ℕ}
    (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) : ∃ l : Kˣ, orderOf l = q + 1 := by
  have hcard : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hdvd : q - 1 ∣ orderOf μ := by
    rw [hμ, hcard]
    exact dvd_mul_left _ _
  refine ⟨μ ^ (q - 1), ?_⟩
  rw [orderOf_pow_of_dvd (by omega) hdvd, hμ, hcard, Nat.mul_div_cancel _ (by omega)]

private theorem u3SwapU_inv_mul_torusDiag_mul {K : Type} [Field K] (l : Kˣ) :
    (u3SwapU : GL (Fin 3) K)⁻¹ * torusDiag ![l, l⁻¹, 1] * u3SwapU =
      (torusDiag ![l, l⁻¹, 1])⁻¹ := by
  have hs : (u3SwapU : GL (Fin 3) K)⁻¹ = u3SwapU := by
    rw [inv_eq_iff_mul_eq_one, ← sq, u3SwapU_sq]
  have hinv : (torusDiag ![l, l⁻¹, 1] : GL (Fin 3) K)⁻¹ = torusDiag ![l⁻¹, l, 1] := by
    rw [← map_inv]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hs, hinv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u3SwapU, u3SwapMat, coe_torusDiag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Units.val_mul, Matrix.vecMul_diagonal]

private theorem orderOf_mk_u3SwapU {K : Type} [Field K] [CharP K 2] {q : ℕ} (hq : q ≠ 0) :
    orderOf (QuotientGroup.mk (⟨u3SwapU, u3SwapU_mem hq⟩ : StatedSU 3 q K) :
      StatedProj (StatedSU 3 q K)) = 2 := by
  let zQ : StatedSU 3 q K := ⟨u3SwapU, u3SwapU_mem hq⟩
  have hzsq : zQ ^ 2 = 1 := Subtype.ext u3SwapU_sq
  have hne : (QuotientGroup.mk zQ : StatedProj (StatedSU 3 q K)) ≠ 1 := by
    intro h
    have h' := (QuotientGroup.eq_one_iff zQ).1 h
    rw [Subgroup.mem_subgroupOf, StatedScalars] at h'
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h'
    have h01 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hc
    simp [zQ, u3SwapU, u3SwapMat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
  have hsq : (QuotientGroup.mk zQ : StatedProj (StatedSU 3 q K)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hzsq, QuotientGroup.mk_one]
  exact orderOf_eq_prime hsq hne

private theorem mk_torusDiag_pow_eq_one_iff {K : Type} [Field K] {q : ℕ} (l : Kˣ)
    (hl : torusDiag ![l, l⁻¹, 1] ∈ StatedSU 3 q K) (n : ℕ) :
    (QuotientGroup.mk (⟨torusDiag ![l, l⁻¹, 1], hl⟩ : StatedSU 3 q K) :
      StatedProj (StatedSU 3 q K)) ^ n = 1 ↔ l ^ n = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow, Subgroup.coe_mk, ← map_pow, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have hD := torusDiag_injective hc
    have h2 : c = 1 := by simpa using congrFun hD 2
    have h0 : c = l ^ n := by simpa [Pi.pow_apply] using congrFun hD 0
    rw [← h0, h2]
  · intro hn
    refine ⟨1, ?_⟩
    rw [scalar_eq_torusDiag]
    congr 1
    funext i
    fin_cases i <;> simp [Pi.pow_apply, inv_pow, hn]

theorem exists_inv_conj_statedProj_statedSU_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ τ t : StatedProj (StatedSU 3 q K), orderOf τ = q + 1 ∧ orderOf t = 2 ∧
      t⁻¹ * τ * t = τ⁻¹ := by
  obtain ⟨l, hl⟩ := exists_unit_orderOf_eq_add_one hq hK
  have hq0 : q ≠ 0 := by omega
  have hlq : l ^ (q + 1) = 1 := by
    rw [← hl]
    exact pow_orderOf_eq_one l
  let zQ : StatedSU 3 q K := ⟨u3SwapU, u3SwapU_mem hq0⟩
  let gQ : StatedSU 3 q K := ⟨torusDiag ![l, l⁻¹, 1], u3_torus_g_mem hq0 l hlq⟩
  refine ⟨QuotientGroup.mk gQ, QuotientGroup.mk zQ, ?_, orderOf_mk_u3SwapU hq0, ?_⟩
  · rw [← hl, orderOf_eq_orderOf_iff]
    exact mk_torusDiag_pow_eq_one_iff l _
  · have h : zQ⁻¹ * gQ * zQ = gQ⁻¹ := Subtype.ext (u3SwapU_inv_mul_torusDiag_mul l)
    have := congrArg (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 q K))) h
    simpa only [map_mul, map_inv, QuotientGroup.mk'_apply] using this

theorem two_le_exponent_of_lieModel_psu3 {Y : Type} [Group Y] {x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSU 3 2 x) : 2 ≤ x := by
  have hadm := h.admissible
  have h1 : 1 ≤ x := hadm.2.1
  by_contra hlt
  have hx1 : x = 1 := by omega
  subst hx1
  exact hadm.2.2.2 rfl

theorem exists_inv_conj_of_lieModel_psu3 {Y : Type} [Group Y] {x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSU 3 2 x) :
    ∃ τ t : Y, orderOf τ = 2 ^ x + 1 ∧ orderOf t = 2 ∧ t⁻¹ * τ * t = τ⁻¹ := by
  have hx := two_le_exponent_of_lieModel_psu3 h
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : CharP K 2 := charP_two_of_natCard_eq hK
  have hq : 2 ≤ 2 ^ x :=
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨τ, t, hτ, ht, hτt⟩ := exists_inv_conj_statedProj_statedSU_three hq hK
  refine ⟨e.symm τ, e.symm t, by rw [MulEquiv.orderOf_eq, hτ],
    by rw [MulEquiv.orderOf_eq, ht], ?_⟩
  rw [← map_inv e.symm, ← map_mul e.symm, ← map_mul e.symm, hτt, map_inv]

theorem exists_inv_conj_of_lieModel_psu3_of_orderOf_eq_two {Y : Type} [Group Y] [Finite Y]
    {x : ℕ} (h : CFSG.Blueprint.LieModel Y .PSU 3 2 x) {d : Y} (hd : orderOf d = 2) :
    ∃ τ : Y, orderOf τ = 2 ^ x + 1 ∧ d⁻¹ * τ * d = τ⁻¹ := by
  obtain ⟨τ, t, hτ, ht, hτt⟩ := exists_inv_conj_of_lieModel_psu3 h
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel
    (two_le_exponent_of_lieModel_psu3 h) (h.statedClassicalModel (by decide))
  have hB := CFSG.ComponentClassification.Asc76X.isBenderGroup_of_mulEquiv_psu3
    (two_le_exponent_of_lieModel_psu3 h) e
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hB ht hd)
  refine ⟨MulAut.conj g τ, by rw [MulEquiv.orderOf_eq, hτ], ?_⟩
  have hd' : d = MulAut.conj g t := by
    rw [MulAut.conj_apply]
    exact hg.symm
  rw [hd', ← map_inv (MulAut.conj g), ← map_mul (MulAut.conj g),
    ← map_mul (MulAut.conj g), hτt, map_inv]

private theorem inv_mul_pow_mul_eq_inv_pow {H : Type} [Group H] {t y : H} (h : t⁻¹ * y * t = y⁻¹)
    (n : ℕ) : t⁻¹ * y ^ n * t = (y ^ n)⁻¹ := by
  have h1 := map_pow (MulAut.conj t⁻¹) y n
  simp only [MulAut.conj_apply, inv_inv] at h1
  rw [h1, h, inv_pow]

theorem exists_inv_conj_lift_of_odd_card {X : Type} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] (hN : Odd (Nat.card N)) {d : X} (hd : d ^ 2 = 1) {τ₁ : X ⧸ N}
    (hτ₁ : (d : X ⧸ N)⁻¹ * τ₁ * d = τ₁⁻¹) (hodd : Odd (orderOf τ₁)) :
    ∃ τ : X, d⁻¹ * τ * d = τ⁻¹ ∧ Odd (orderOf τ) ∧ orderOf τ₁ ∣ orderOf τ := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (τ₁ ^ (k + 1))
  have hdinv : d⁻¹ = d := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hd]
  have hdi : (d : X ⧸ N)⁻¹ = d := by
    rw [← QuotientGroup.mk_inv, hdinv]
  have hσ : (d : X ⧸ N) * (τ₁ ^ (k + 1))⁻¹ * d = τ₁ ^ (k + 1) := by
    have h1 := congrArg (·⁻¹) (inv_mul_pow_mul_eq_inv_pow hτ₁ (k + 1))
    simp only [_root_.mul_inv_rev, inv_inv, hdi] at h1
    rw [mul_assoc]
    exact h1
  have hbar : ((g * d * g⁻¹ * d : X) : X ⧸ N) = τ₁ := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg]
    rw [mul_assoc _ (d : X ⧸ N), mul_assoc, hσ, ← pow_add,
      show k + 1 + (k + 1) = orderOf τ₁ + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  refine ⟨g * d * g⁻¹ * d, ?_, ?_, ?_⟩
  · have hdd : d * d = 1 := by
      rw [← sq]
      exact hd
    rw [hdinv]
    calc d * (g * d * g⁻¹ * d) * d = d * g * d * g⁻¹ * (d * d) := by
          simp only [mul_assoc]
      _ = (g * d * g⁻¹ * d)⁻¹ := by
          rw [hdd, mul_one]
          simp only [_root_.mul_inv_rev, inv_inv, hdinv, mul_assoc]
  · have hmem : (g * d * g⁻¹ * d) ^ orderOf τ₁ ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hbar, pow_orderOf_eq_one]
    have h1 : ((g * d * g⁻¹ * d) ^ orderOf τ₁) ^ Nat.card N = 1 := by
      have h := pow_card_eq_one' (x := (⟨_, hmem⟩ : N))
      exact congrArg Subtype.val h
    rw [← pow_mul] at h1
    exact Odd.of_dvd_nat (Odd.mul ⟨k, hk⟩ hN) (orderOf_dvd_of_pow_eq_one h1)
  · rw [← hbar]
    exact orderOf_map_dvd (QuotientGroup.mk' N) _

theorem isPerfect_of_lieModel_psu3 {Y : Type} [Group Y] {x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSU 3 2 x) : Group.IsPerfect Y := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKf
  haveI : Finite K := hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect (StatedSU 3 (2 ^ x) K) :=
    isPerfect_statedSU (p := 2) (f := x) hK le_rfl hadm.2.2.2
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem card_le_of_isElemAbelian_mulAut_of_lieModel_psu3
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {x : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 2 x)
    (A : Subgroup (MulAut X)) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ (x + 1) := by
  have h1 := CFSG.LocalAnalysis.WeakClosure81.card_elemAbelian_two_aut_PSU3 h
    (A.map (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X)) (hA.map _)
  rwa [Subgroup.card_map_of_injective
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X)] at h1

private theorem dvd_two_pow_cube_add_one {x ℓ : ℕ} (hℓ : ℓ.Prime) (hx : 1 ≤ x)
    (hord : orderOf (2 : ZMod ℓ) = 6 * x) : ℓ ∣ (2 ^ x) ^ 3 + 1 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hy2 : (2 : ZMod ℓ) ^ (3 * x) * (2 : ZMod ℓ) ^ (3 * x) = 1 := by
    rw [← pow_add, show 3 * x + 3 * x = 6 * x by ring, ← hord, pow_orderOf_eq_one]
  have hy1 : (2 : ZMod ℓ) ^ (3 * x) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; omega)
  have h0 : ((2 : ZMod ℓ) ^ (3 * x) + 1) * ((2 : ZMod ℓ) ^ (3 * x) - 1) = 0 := by
    linear_combination hy2
  have hy0 : (2 : ZMod ℓ) ^ (3 * x) + 1 = 0 :=
    (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hy1)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [← pow_mul, mul_comm x 3]
  exact hy0

theorem dvd_card_of_lieModel_psu3_of_orderOf_two_eq {Y : Type} [Group Y] {x ℓ : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSU 3 2 x) (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = 6 * x) : ℓ ∣ Nat.card Y := by
  obtain ⟨hadm, K, hKf, -, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKf
  have hx : 1 ≤ x := hadm.2.1
  have hmul := CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd Nat.prime_two hx hK
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
    have h6 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at h6
    have := Nat.le_of_dvd (by norm_num) h6
    omega
  have hcop : Nat.Coprime ℓ (Nat.gcd 3 (2 ^ x + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
      ((Nat.coprime_primes hℓ Nat.prime_three).mpr hℓ3)
  have hdvd : ℓ ∣ Nat.card (StatedProj (StatedSU 3 (2 ^ x) K)) * Nat.gcd 3 (2 ^ x + 1) := by
    rw [hmul]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_two_pow_cube_add_one hℓ hx hord) _) _
  rw [Nat.card_congr e.toEquiv]
  exact hcop.dvd_of_dvd_mul_right hdvd

private theorem not_dvd_pow_sub_pow {a k i ℓ : ℕ} (hℓ : ℓ.Prime) (ha : 1 ≤ a)
    (hord : orderOf (2 : ZMod ℓ) = 6 * a) (hik : i < k) (hk : k < 6) :
    ¬ ℓ ∣ (2 ^ a) ^ k - (2 ^ a) ^ i := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := rfl
    rw [h0, orderOf_zero] at hord
    omega
  have hsplit : (2 ^ a) ^ k - (2 ^ a) ^ i = (2 ^ a) ^ i * ((2 ^ a) ^ (k - i) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_of_le hik.le]
  rw [hsplit]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h1 | h1
  · rw [← pow_mul] at h1
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h1))
  · have h1' : ((2 ^ (a * (k - i)) - 1 : ℕ) : ZMod ℓ) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_mul]
      exact h1
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      sub_eq_zero] at h1'
    have hdvd' := orderOf_dvd_of_pow_eq_one h1'
    rw [hord, mul_comm a] at hdvd'
    have h6 : 6 ∣ k - i := Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd'
    have := Nat.le_of_dvd (by omega) h6
    omega

theorem not_dvd_card_GL_of_orderOf_two_eq {K : Type} [Field K] [Finite K] {a k ℓ : ℕ}
    (hK : Nat.card K = 2 ^ a) (ha : 1 ≤ a) (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = 6 * a) (hk : k < 6) :
    ¬ ℓ ∣ Nat.card (GL (Fin k) K) := by
  haveI := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK]
  intro hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hℓ.prime _).mp hdvd
  exact not_dvd_pow_sub_pow hℓ ha hord i.2 hk hi

private theorem card_quotient_center_dvd_of_map_eq_bot {X H : Type} [Group X] [Group H]
    (f : X →* H) (h : f.ker.map (QuotientGroup.mk' (Subgroup.center X)) = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card H := by
  have hle : f.ker ≤ Subgroup.center X := by
    intro g hg
    have hmem : QuotientGroup.mk' (Subgroup.center X) g ∈
        f.ker.map (QuotientGroup.mk' (Subgroup.center X)) := Subgroup.mem_map_of_mem _ hg
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hsurj : Function.Surjective
      (QuotientGroup.map f.ker (Subgroup.center X) (MonoidHom.id X) hle) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨g, rfl⟩
  have h2 : Nat.card (X ⧸ f.ker) ∣ Nat.card H := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact (Subgroup.card_dvd_of_surjective (hf := hsurj)).trans h2

private theorem hom_eq_one_of_map_ker_eq_top {X H : Type} [Group X] [Group H]
    (hX : commutator X = ⊤) (f : X →* H)
    (h : f.ker.map (QuotientGroup.mk' (Subgroup.center X)) = ⊤) : f = 1 := by
  have hc : ∀ g : X, ∃ c ∈ Subgroup.center X, f g = f c := by
    intro g
    have hg : QuotientGroup.mk' (Subgroup.center X) g ∈
        f.ker.map (QuotientGroup.mk' (Subgroup.center X)) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
    refine ⟨k⁻¹ * g, ?_, ?_⟩
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkg
      exact hkg
    · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
  have hcomm : ∀ g₁ g₂ : X, f ⁅g₁, g₂⁆ = 1 := by
    intro g₁ g₂
    obtain ⟨c₁, -, h₁⟩ := hc g₁
    obtain ⟨c₂, hc₂, h₂⟩ := hc g₂
    rw [map_commutatorElement, h₁, h₂, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc₂ c₁), map_one]
  have hle : commutator X ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact MonoidHom.mem_ker.mpr (hcomm g₁ g₂)
  ext g
  have : g ∈ f.ker := hle (by rw [hX]; exact Subgroup.mem_top g)
  simpa using this

theorem hom_eq_one_of_isSimpleGroup_quotient_center {X H : Type} [Group X] [Group H]
    (hX : commutator X = ⊤) (hs : IsSimpleGroup (X ⧸ Subgroup.center X)) {ℓ : ℕ}
    (hℓX : ℓ ∣ Nat.card (X ⧸ Subgroup.center X)) (hℓH : ¬ ℓ ∣ Nat.card H) (f : X →* H) :
    f = 1 := by
  haveI := hs
  haveI hN : (f.ker.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (f.ker.map (QuotientGroup.mk' (Subgroup.center X))) with hbot | htop
  · exact absurd (hℓX.trans (card_quotient_center_dvd_of_map_eq_bot f hbot)) hℓH
  · exact hom_eq_one_of_map_ker_eq_top hX f htop

private theorem card_generalLinearGroup_eq_card_GL (K W : Type) [Field K] [AddCommGroup W]
    [Module K W] [Module.Finite K W] :
    Nat.card (LinearMap.GeneralLinearGroup K W) =
      Nat.card (GL (Fin (Module.finrank K W)) K) :=
  Nat.card_congr (Units.mapEquiv
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K W)).toRingEquiv.toMulEquiv).toEquiv

theorem hom_eq_one_of_lieModel_psu3 {X : Type} [Group X] (hX : commutator X = ⊤) {x : ℕ}
    (h : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 2 x) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ x) {W : Type} [AddCommGroup W] [Module K W]
    [Module.Finite K W] (hW : Module.finrank K W < 6)
    (f : X →* LinearMap.GeneralLinearGroup K W) : f = 1 := by
  have hx := two_le_exponent_of_lieModel_psu3 h
  obtain ⟨ℓ, hℓ, -, hord⟩ :=
    CFSG.QuasithinUnique.Setup.X5.exists_prime_orderOf_two_eq_six_mul hx
  have hs : IsSimpleGroup (X ⧸ Subgroup.center X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  refine hom_eq_one_of_isSimpleGroup_quotient_center hX hs
    (dvd_card_of_lieModel_psu3_of_orderOf_two_eq h hℓ hord) ?_ f
  rw [card_generalLinearGroup_eq_card_GL K W]
  exact not_dvd_card_GL_of_orderOf_two_eq hK (by omega) hℓ hord hW

theorem exists_hom_generalLinearGroup_restrict {X K E : Type} [Group X] [Field K]
    [AddCommGroup E] [Module K E] (ψ : X →* (E ≃ₗ[K] E)) (W : Submodule K E)
    (hW : ∀ g, ∀ w ∈ W, ψ g w ∈ W) :
    ∃ ρ : X →* LinearMap.GeneralLinearGroup K W,
      ∀ g (w : W), ((ρ g : W →ₗ[K] W) w : E) = ψ g w := by
  let f : X →* Module.End K W :=
    { toFun := fun g => (ψ g : E →ₗ[K] E).restrict (hW g)
      map_one' := by
        ext w
        simp
      map_mul' := fun g h => by
        ext w
        simp [LinearEquiv.mul_apply] }
  exact ⟨f.toHomUnits, fun g w => rfl⟩

end CFSG.ClassicalGroups.Unitary
