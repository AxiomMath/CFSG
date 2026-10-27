module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher

namespace SpChain

variable {K : Type} [Field K]

@[expose] def uMat (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a, b, c; 0, 1, d, b + a * d; 0, 0, 1, a; 0, 0, 0, 1]

theorem uMat_zero : uMat (0 : K) 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, one_apply]

theorem uMat_apply_zero_one (a b c d : K) : uMat a b c d 0 1 = a := rfl
theorem uMat_apply_zero_two (a b c d : K) : uMat a b c d 0 2 = b := rfl
theorem uMat_apply_zero_three (a b c d : K) : uMat a b c d 0 3 = c := rfl
theorem uMat_apply_one_two (a b c d : K) : uMat a b c d 1 2 = d := rfl

theorem uMat_inj {a b c d a' b' c' d' : K} (h : uMat a b c d = uMat a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  refine ⟨congrFun (congrFun h 0) 1, congrFun (congrFun h 0) 2, congrFun (congrFun h 0) 3,
    congrFun (congrFun h 1) 2⟩

section CharTwo

variable [CharP K 2]

theorem uMat_mem (a b c d : K) : (uMat a b c d)ᵀ * minorJ K * uMat a b c d = minorJ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, mul_apply, Fin.sum_univ_four, minorJ_apply]
  all_goals first
    | ring1
    | linear_combination (d) * h2
    | linear_combination (a) * h2
    | linear_combination (-a) * h2
    | linear_combination (-d) * h2
    | linear_combination (a*d + b) * h2
    | linear_combination (-a*d - b) * h2
    | linear_combination (a^2*d + a*b + c) * h2

theorem uMat_mul (a b c d A B C D : K) :
    uMat a b c d * uMat A B C D =
      uMat (a + A) (b + B + a * D) (c + C + a * B + a * A * D + b * A) (d + D) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, mul_apply, Fin.sum_univ_four]
  all_goals first
    | ring1
    | linear_combination (D*a) * h2
    | linear_combination (-D*a) * h2

theorem uMat_mul_inv (a b c d : K) : uMat a b c d * uMat a (b + a * d) c d = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uMat_mul, ← uMat_zero]
  congr 1
  · linear_combination a * h2
  · linear_combination (b + a * d) * h2
  · linear_combination (c + a * b + a ^ 2 * d) * h2
  · linear_combination d * h2

theorem uMat_inv_mul (a b c d : K) : uMat a (b + a * d) c d * uMat a b c d = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uMat_mul, ← uMat_zero]
  congr 1
  · linear_combination a * h2
  · linear_combination (b + a * d) * h2
  · linear_combination (c + a * b + a ^ 2 * d) * h2
  · linear_combination d * h2

@[expose] def uElt (a b c d : K) : antiSp K :=
  ⟨⟨uMat a b c d, uMat a (b + a * d) c d, uMat_mul_inv a b c d, uMat_inv_mul a b c d⟩,
    uMat_mem a b c d⟩

theorem glMat_uElt (a b c d : K) : glMat (uElt a b c d : GL (Fin 4) K) = uMat a b c d :=
  rfl

theorem glMat_uElt_inv (a b c d : K) :
    glMat (((uElt a b c d)⁻¹ : antiSp K) : GL (Fin 4) K) = uMat a (b + a * d) c d :=
  rfl

omit [CharP K 2] in
theorem antiSp_ext {g h : antiSp K} (H : glMat (g : GL (Fin 4) K) = glMat h) : g = h :=
  Subtype.ext (Units.ext H)

theorem uElt_mul (a b c d A B C D : K) :
    uElt a b c d * uElt A B C D =
      uElt (a + A) (b + B + a * D) (c + C + a * B + a * A * D + b * A) (d + D) :=
  antiSp_ext (uMat_mul a b c d A B C D)

theorem uElt_inv (a b c d : K) : (uElt a b c d)⁻¹ = uElt a (b + a * d) c d :=
  antiSp_ext rfl

end CharTwo

section Unipotent

variable [CharP K 2]

variable (K) in
@[expose] def antiUnipotent : Subgroup (antiSp K) where
  carrier := {g | ∃ a b c d : K, g = uElt a b c d}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨A, B, C, D, rfl⟩
    exact ⟨_, _, _, _, uElt_mul a b c d A B C D⟩
  one_mem' := ⟨0, 0, 0, 0, antiSp_ext uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, d, rfl⟩
    exact ⟨_, _, _, _, uElt_inv a b c d⟩

theorem uElt_mem_antiUnipotent (a b c d : K) : uElt a b c d ∈ antiUnipotent K :=
  ⟨a, b, c, d, rfl⟩

theorem mem_antiUnipotent {g : antiSp K} :
    g ∈ antiUnipotent K ↔ ∃ a b c d : K, glMat (g : GL (Fin 4) K) = uMat a b c d := by
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨a, b, c, d, rfl⟩
  · rintro ⟨a, b, c, d, h⟩
    exact ⟨a, b, c, d, antiSp_ext h⟩

theorem mem_antiUnipotent_iff_upper (g : antiSp K) :
    g ∈ antiUnipotent K ↔
      (∀ i j : Fin 4, j < i → glMat (g : GL (Fin 4) K) i j = 0) ∧
        ∀ i, glMat (g : GL (Fin 4) K) i i = 1 := by
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [glMat_uElt, uMat]
    · fin_cases i <;> simp [glMat_uElt, uMat]
  · rintro ⟨hlow, hdiag⟩
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hJ := mem_antiSp.mp g.2
    have e13 := congrFun (congrFun hJ 1) 3
    have e23 := congrFun (congrFun hJ 2) 3
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at e13 e23
    set M := glMat (g : GL (Fin 4) K) with hM
    have h10 := hlow 1 0 (by decide)
    have h20 := hlow 2 0 (by decide)
    have h21 := hlow 2 1 (by decide)
    have h30 := hlow 3 0 (by decide)
    have h31 := hlow 3 1 (by decide)
    have h32 := hlow 3 2 (by decide)
    have d0 := hdiag 0
    have d1 := hdiag 1
    have d2 := hdiag 2
    have d3 := hdiag 3
    rw [h21, h31, d1, d3] at e13
    rw [h32, d2, d3] at e23
    norm_num at e13 e23
    refine ⟨M 0 1, M 0 2, M 0 3, M 1 2, antiSp_ext ?_⟩
    rw [glMat_uElt, ← hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, h10, h20, h21, h30, h31, h32, d0, d1, d2, d3]
    · linear_combination e23 - M 1 2 * e13 - M 0 2 * h2
    · linear_combination e13 - M 0 1 * h2

variable (K) in
@[expose] def antiUnipotentCenter : Subgroup (antiSp K) where
  carrier := {g | ∃ b c : K, g = uElt 0 b c 0}
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨B, C, rfl⟩
    refine ⟨b + B, c + C, ?_⟩
    rw [uElt_mul]
    congr 1 <;> ring
  one_mem' := ⟨0, 0, antiSp_ext uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨b, c, ?_⟩
    rw [uElt_inv]
    congr 1
    ring

theorem antiUnipotentCenter_le : antiUnipotentCenter K ≤ antiUnipotent K := by
  rintro _ ⟨b, c, rfl⟩
  exact uElt_mem_antiUnipotent 0 b c 0

theorem antiUnipotentCenter_comm {z u : antiSp K} (hz : z ∈ antiUnipotentCenter K)
    (hu : u ∈ antiUnipotent K) : z * u = u * z := by
  obtain ⟨b, c, rfl⟩ := hz
  obtain ⟨A, B, C, D, rfl⟩ := hu
  rw [uElt_mul, uElt_mul]
  congr 1 <;> ring

instance antiUnipotentCenter_normal :
    ((antiUnipotentCenter K).subgroupOf (antiUnipotent K)).Normal :=
  ⟨fun z hz u => Subgroup.mem_subgroupOf.mpr (by
    have hz' := Subgroup.mem_subgroupOf.mp hz
    have h1 := antiUnipotentCenter_comm hz' u.2
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, ← h1] using hz')⟩

@[expose] def centerEquiv : Multiplicative (K × K) ≃* antiUnipotentCenter K :=
  MulEquiv.ofBijective
    ({ toFun := fun p => ⟨uElt 0 p.toAdd.1 p.toAdd.2 0, p.toAdd.1, p.toAdd.2, rfl⟩
       map_one' := Subtype.ext (antiSp_ext uMat_zero)
       map_mul' := fun p p' => Subtype.ext (by
         change uElt 0 (p.toAdd.1 + p'.toAdd.1) (p.toAdd.2 + p'.toAdd.2) 0 =
           uElt 0 p.toAdd.1 p.toAdd.2 0 * uElt 0 p'.toAdd.1 p'.toAdd.2 0
         rw [uElt_mul]
         congr 1 <;> ring) } : Multiplicative (K × K) →* antiUnipotentCenter K)
    ⟨fun p p' h => by
      have h1 := uMat_inj (congrArg (fun x : antiUnipotentCenter K =>
        glMat ((x : antiSp K) : GL (Fin 4) K)) h)
      exact Prod.ext h1.2.1 h1.2.2.1,
    fun x => by
      obtain ⟨b, c, hbc⟩ := x.2
      exact ⟨Multiplicative.ofAdd (b, c), Subtype.ext hbc.symm⟩⟩

theorem centerEquiv_apply (b c : K) :
    ((centerEquiv (Multiplicative.ofAdd (b, c)) : antiUnipotentCenter K) : antiSp K) =
      uElt 0 b c 0 :=
  rfl

@[expose] def unipotentPair : antiUnipotent K →* Multiplicative (K × K) where
  toFun g := Multiplicative.ofAdd (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1,
    glMat ((g : antiSp K) : GL (Fin 4) K) 1 2)
  map_one' := by
    change Multiplicative.ofAdd ((1 : Matrix (Fin 4) (Fin 4) K) 0 1,
      (1 : Matrix (Fin 4) (Fin 4) K) 1 2) = 1
    simp [one_apply]
  map_mul' g h := by
    obtain ⟨a, b, c, d, hg⟩ := g.2
    obtain ⟨A, B, C, D, hh⟩ := h.2
    have hgh : ((g * h : antiUnipotent K) : antiSp K) =
        uElt (a + A) (b + B + a * D) (c + C + a * B + a * A * D + b * A) (d + D) := by
      rw [Subgroup.coe_mul, hg, hh, uElt_mul]
    change Multiplicative.ofAdd (glMat (((g * h : antiUnipotent K) : antiSp K) : GL (Fin 4) K) 0 1,
      glMat (((g * h : antiUnipotent K) : antiSp K) : GL (Fin 4) K) 1 2) =
      Multiplicative.ofAdd (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1,
        glMat ((g : antiSp K) : GL (Fin 4) K) 1 2) *
      Multiplicative.ofAdd (glMat ((h : antiSp K) : GL (Fin 4) K) 0 1,
        glMat ((h : antiSp K) : GL (Fin 4) K) 1 2)
    rw [hgh, hg, hh, glMat_uElt, glMat_uElt, glMat_uElt, uMat_apply_zero_one, uMat_apply_zero_one,
      uMat_apply_zero_one, uMat_apply_one_two, uMat_apply_one_two, uMat_apply_one_two]
    rfl

theorem unipotentPair_apply (g : antiUnipotent K) :
    unipotentPair g = Multiplicative.ofAdd (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1,
      glMat ((g : antiSp K) : GL (Fin 4) K) 1 2) :=
  rfl

theorem ker_unipotentPair :
    (unipotentPair (K := K)).ker = (antiUnipotentCenter K).subgroupOf (antiUnipotent K) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, unipotentPair_apply]
  obtain ⟨a, b, c, d, hg⟩ := g.2
  rw [hg, glMat_uElt]
  simp only [uMat]
  constructor
  · intro h
    have h1 := congrArg (fun p : Multiplicative (K × K) => p.toAdd) h
    simp at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨b, c, rfl⟩
  · rintro ⟨b', c', h⟩
    have h1 := uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h)
    obtain ⟨rfl, -, -, rfl⟩ := h1
    simp

theorem unipotentPair_surjective : Function.Surjective (unipotentPair (K := K)) := by
  intro p
  refine ⟨⟨uElt p.toAdd.1 0 0 p.toAdd.2, uElt_mem_antiUnipotent _ _ _ _⟩, ?_⟩
  rw [unipotentPair_apply]
  simp [glMat_uElt, uMat]

@[expose] def quotientEquiv :
    antiUnipotent K ⧸ (antiUnipotentCenter K).subgroupOf (antiUnipotent K) ≃*
      Multiplicative (K × K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_unipotentPair.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ unipotentPair_surjective)

theorem quotientEquiv_mk (g : antiUnipotent K) :
    quotientEquiv (QuotientGroup.mk g) = Multiplicative.ofAdd
      (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1, glMat ((g : antiSp K) : GL (Fin 4) K) 1 2) :=
  rfl

end Unipotent

section Eta

variable [CharP K 2]

theorem minorMap_uMat (a b c d : K) :
    minorMap (uMat a b c d) =
      uMat d (c + a * b + a ^ 2 * d) (b ^ 2 + a * b * d + c * d) (a ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext A B
  fin_cases A <;> fin_cases B <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one,
    minorIdx_two, minorIdx_three, uMat]
  all_goals first
    | ring1
    | linear_combination (c) * h2
    | linear_combination (-c) * h2
    | linear_combination (c*d) * h2
    | linear_combination (-c*d) * h2
    | linear_combination (a^2*d + c) * h2
    | linear_combination (-a^2*d - c) * h2

theorem uMat_map_pow (n : ℕ) (a b c d : K) :
    (uMat a b c d).map (· ^ 2 ^ n) = uMat (a ^ 2 ^ n) (b ^ 2 ^ n) (c ^ 2 ^ n) (d ^ 2 ^ n) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, add_pow_char_pow, mul_pow]

variable [Finite K]

theorem glMat_minorAut_sq_pow (n : ℕ) (g : antiSp K) :
    glMat ((((minorAut K) ^ 2) ^ n) g : GL (Fin 4) K) = (glMat (g : GL (Fin 4) K)).map
      (· ^ 2 ^ n) := by
  induction n generalizing g with
  | zero =>
    ext i j
    simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    have h1 : ((minorAut K) ^ 2) g = frobHom K g := by
      rw [sq, MulAut.mul_apply]
      exact minorHom_minorHom g
    rw [h1, glMat_frobHom]
    ext i j
    simp only [Matrix.map_apply]
    rw [← pow_mul, ← pow_succ']

theorem glMat_eta (m : ℕ) (g : antiSp K) :
    glMat (((minorAut K) ^ (2 * m + 1)) g : GL (Fin 4) K) =
      minorMap ((glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ m)) := by
  rw [pow_succ', pow_mul, MulAut.mul_apply, glMat_minorAut, glMat_minorAut_sq_pow]

theorem glMat_eta_uElt (m : ℕ) (a b c d : K) :
    glMat (((minorAut K) ^ (2 * m + 1)) (uElt a b c d) : GL (Fin 4) K) =
      uMat (d ^ 2 ^ m) (c ^ 2 ^ m + a ^ 2 ^ m * b ^ 2 ^ m + (a ^ 2 ^ m) ^ 2 * d ^ 2 ^ m)
        ((b ^ 2 ^ m) ^ 2 + a ^ 2 ^ m * b ^ 2 ^ m * d ^ 2 ^ m + c ^ 2 ^ m * d ^ 2 ^ m)
        ((a ^ 2 ^ m) ^ 2) := by
  rw [glMat_eta, glMat_uElt, uMat_map_pow, minorMap_uMat]

end Eta

section Order

variable [CharP K 2] [Finite K]

theorem exceptionalAut_eq_congr :
    exceptionalAut K = MulAut.congr ((antiSpEquiv K).trans (projSpEquiv K)) (minorAut K) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [exceptionalAut_proj, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    show proj 2 K g = projSpEquiv K g from rfl, MulEquiv.symm_apply_apply]
  rfl

theorem orderOf_minorAut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    orderOf (minorAut K) = 2 * f := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  rw [← (exceptionalAut_structure hf hFr hord hzp).1, exceptionalAut_eq_congr,
    MulEquiv.orderOf_eq]

theorem orderOf_eta (m : ℕ) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    orderOf (minorAut K ^ (2 * m + 1)) = 2 := by
  rw [orderOf_pow' _ (by omega), orderOf_minorAut (by omega) hK,
    Nat.gcd_eq_right (Dvd.intro_left 2 rfl)]
  exact Nat.mul_div_cancel 2 (by omega)

theorem zpowers_eta_mem (m : ℕ) {ε : MulAut (antiSp K)}
    (hε : ε ∈ Subgroup.zpowers (minorAut K ^ (2 * m + 1))) {u : antiSp K}
    (hu : u ∈ antiUnipotent K) : ε u ∈ antiUnipotent K := by
  have hfin : IsOfFinOrder (minorAut K ^ (2 * m + 1)) := isOfFinOrder_of_finite _
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hε)
  clear hε
  induction k generalizing u with
  | zero => exact hu
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply]
    obtain ⟨a, b, c, d, hab⟩ := ih hu
    rw [hab]
    refine mem_antiUnipotent.mpr ⟨_, _, _, _, glMat_eta_uElt m a b c d⟩

end Order

section Cocycle

variable [CharP K 2] [Finite K]

theorem eta_cocycle (m : ℕ) (hη2 : (minorAut K ^ (2 * m + 1)) ^ 2 = 1) {u : antiSp K}
    (hu : u ∈ antiUnipotent K) (hu1 : u * (minorAut K ^ (2 * m + 1)) u = 1) :
    ∃ h ∈ antiUnipotent K, h * u * ((minorAut K ^ (2 * m + 1)) h)⁻¹ = 1 := by
  set η := minorAut K ^ (2 * m + 1) with hηdef
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0e : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hηη : ∀ x, η (η x) = x := fun x => by
    rw [← MulAut.mul_apply, ← sq, hη2, MulAut.one_apply]
  have uElt_eq : ∀ {a b c d a' b' c' d' : K}, a = a' → b = b' → c = c' → d = d' →
      uElt a b c d = uElt a' b' c' d' := by
    intro a b c d a' b' c' d' h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  obtain ⟨a, b, c, d, rfl⟩ := hu
  have hmat := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hu1
  change uMat a b c d * glMat ((η (uElt a b c d) : antiSp K) : GL (Fin 4) K) = 1 at hmat
  rw [glMat_eta_uElt, uMat_mul, ← uMat_zero] at hmat
  obtain ⟨-, -, -, hd⟩ := uMat_inj hmat
  have hd' : d = (a ^ 2 ^ m) ^ 2 := by linear_combination hd - (a ^ 2 ^ m) ^ 2 * h2
  have hηv : η (uElt a 0 0 0) = uElt 0 0 0 d := by
    refine antiSp_ext ?_
    rw [glMat_eta_uElt, h0e, glMat_uElt, hd']
    congr 1 <;> ring
  set β := b + a * d with hβ
  set γ := c + a * b + a ^ 2 * d with hγ
  have hz : uElt a 0 0 0 * uElt a b c d * (η (uElt a 0 0 0))⁻¹ = uElt 0 β γ 0 := by
    rw [hηv, uElt_inv, uElt_mul, uElt_mul]
    refine uElt_eq ?_ ?_ ?_ ?_
    · linear_combination a * h2
    · linear_combination (a * d) * h2
    · ring
    · linear_combination d * h2
  have hzz : uElt 0 β γ 0 * η (uElt 0 β γ 0) = 1 := by
    rw [← hz, map_mul, map_mul, map_inv, hηη]
    calc uElt a 0 0 0 * uElt a b c d * (η (uElt a 0 0 0))⁻¹ *
          (η (uElt a 0 0 0) * η (uElt a b c d) * (uElt a 0 0 0)⁻¹)
        _ = uElt a 0 0 0 * (uElt a b c d * η (uElt a b c d)) * (uElt a 0 0 0)⁻¹ := by group
        _ = 1 := by rw [hu1, mul_one, mul_inv_cancel]
  have hηz : η (uElt 0 β γ 0) = uElt 0 (γ ^ 2 ^ m) ((β ^ 2 ^ m) ^ 2) 0 := by
    refine antiSp_ext ?_
    rw [glMat_eta_uElt, h0e, glMat_uElt]
    congr 1 <;> ring
  rw [hηz, uElt_mul] at hzz
  have hzz' := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hzz
  change uMat _ _ _ _ = (1 : Matrix (Fin 4) (Fin 4) K) at hzz'
  rw [← uMat_zero] at hzz'
  obtain ⟨-, -, hγ', -⟩ := uMat_inj hzz'
  have hγβ : γ = (β ^ 2 ^ m) ^ 2 := by linear_combination hγ' - (β ^ 2 ^ m) ^ 2 * h2
  have hηw : η (uElt 0 β 0 0) = uElt 0 0 γ 0 := by
    refine antiSp_ext ?_
    rw [glMat_eta_uElt, h0e, glMat_uElt, hγβ]
    congr 1 <;> ring
  refine ⟨uElt 0 β 0 0 * uElt a 0 0 0, mul_mem (uElt_mem_antiUnipotent _ _ _ _)
    (uElt_mem_antiUnipotent _ _ _ _), ?_⟩
  calc uElt 0 β 0 0 * uElt a 0 0 0 * uElt a b c d * (η (uElt 0 β 0 0 * uElt a 0 0 0))⁻¹
      _ = uElt 0 β 0 0 * (uElt a 0 0 0 * uElt a b c d * (η (uElt a 0 0 0))⁻¹) *
          (η (uElt 0 β 0 0))⁻¹ := by rw [map_mul]; group
      _ = 1 := by
        rw [hz, hηw, uElt_inv, uElt_mul, uElt_mul]
        refine (uElt_eq ?_ ?_ ?_ ?_).trans (antiSp_ext uMat_zero)
        · ring
        · linear_combination β * h2
        · linear_combination γ * h2
        · ring

end Cocycle

section Sylow

variable [CharP K 2] [Finite K]

variable (K) in
abbrev etaProduct (m : ℕ) : Type :=
  antiSp K ⋊[(Subgroup.zpowers (minorAut K ^ (2 * m + 1))).subtype]
    Subgroup.zpowers (minorAut K ^ (2 * m + 1))

instance (m : ℕ) : Finite (etaProduct K m) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

variable (K) in
@[expose] def etaUnipotent (m : ℕ) : Subgroup (etaProduct K m) where
  carrier := {x | x.left ∈ antiUnipotent K}
  mul_mem' {x y} hx hy := by
    change x.left * ((x.right : MulAut (antiSp K)) y.left) ∈ antiUnipotent K
    exact mul_mem hx (zpowers_eta_mem m x.right.2 hy)
  one_mem' := one_mem (antiUnipotent K)
  inv_mem' {x} hx := by
    change (((x.right)⁻¹ : Subgroup.zpowers _) : MulAut (antiSp K)) x.left⁻¹ ∈ antiUnipotent K
    exact zpowers_eta_mem m (x.right⁻¹).2 (inv_mem hx)

omit [Finite K] in
theorem card_antiUnipotent {q : ℕ} (hK : Nat.card K = q) :
    Nat.card (antiUnipotent K) = q ^ 4 := by
  let e : K × K × K × K ≃ antiUnipotent K :=
    { toFun := fun p => ⟨uElt p.1 p.2.1 p.2.2.1 p.2.2.2, uElt_mem_antiUnipotent _ _ _ _⟩
      invFun := fun g => (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1,
        glMat ((g : antiSp K) : GL (Fin 4) K) 0 2, glMat ((g : antiSp K) : GL (Fin 4) K) 0 3,
        glMat ((g : antiSp K) : GL (Fin 4) K) 1 2)
      left_inv := fun p => rfl
      right_inv := fun g => by
        obtain ⟨a, b, c, d, hg⟩ := g.2
        refine Subtype.ext ?_
        change uElt (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1)
          (glMat ((g : antiSp K) : GL (Fin 4) K) 0 2) (glMat ((g : antiSp K) : GL (Fin 4) K) 0 3)
          (glMat ((g : antiSp K) : GL (Fin 4) K) 1 2) = (g : antiSp K)
        rw [hg]
        rfl }
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod, hK]
  ring

theorem card_etaUnipotent (m : ℕ) {q : ℕ} (hK : Nat.card K = q) :
    Nat.card (etaUnipotent K m) =
      q ^ 4 * Nat.card (Subgroup.zpowers (minorAut K ^ (2 * m + 1))) := by
  let e : etaUnipotent K m ≃ antiUnipotent K × Subgroup.zpowers (minorAut K ^ (2 * m + 1)) :=
    { toFun := fun x => (⟨x.1.left, x.2⟩, x.1.right)
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_antiUnipotent hK]

theorem card_antiSp {q : ℕ} (hK : Nat.card K = q) :
    Nat.card (antiSp K) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  rw [Nat.card_congr (antiSpEquiv K).toEquiv,
    (symplectic_higher_order_and_Sylow 2 q hK (r := 2) (by norm_num)).1]
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem etaUnipotent_sylow (m : ℕ) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    IsPGroup 2 (etaUnipotent K m) ∧ ¬ 2 ∣ (etaUnipotent K m).index := by
  have hη : Nat.card (Subgroup.zpowers (minorAut K ^ (2 * m + 1))) = 2 := by
    rw [Nat.card_zpowers, orderOf_eta m hK]
  have hc := card_etaUnipotent m hK
  rw [hη] at hc
  refine ⟨IsPGroup.of_card (n := 4 * (2 * m + 1) + 1) (by rw [hc, ← pow_mul, pow_succ]; ring_nf),
    fun hdvd => ?_⟩
  have h1 := Subgroup.card_mul_index (etaUnipotent K m)
  rw [SemidirectProduct.card, hc, card_antiSp hK, hη] at h1
  have hq : 0 < (2 : ℕ) ^ (2 * m + 1) := by positivity
  have h2 : (etaUnipotent K m).index = ((2 ^ (2 * m + 1)) ^ 2 - 1) *
      ((2 ^ (2 * m + 1)) ^ 4 - 1) := by
    have h3 : 0 < (2 ^ (2 * m + 1)) ^ 4 * 2 := by positivity
    exact Nat.eq_of_mul_eq_mul_left h3 (by rw [h1]; ring)
  rw [h2] at hdvd
  have hodd : Odd (((2 ^ (2 * m + 1)) ^ 2 - 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1)) := by
    have he2 : Even ((2 : ℕ) ^ (2 * m + 1)) := by
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    have hp2 : 1 ≤ ((2 : ℕ) ^ (2 * m + 1)) ^ 2 := Nat.one_le_pow _ _ hq
    have hp4 : 1 ≤ ((2 : ℕ) ^ (2 * m + 1)) ^ 4 := Nat.one_le_pow _ _ hq
    refine Odd.mul ?_ ?_
    · exact Nat.Even.sub_odd hp2 (Even.pow_of_ne_zero he2 (by norm_num)) odd_one
    · exact Nat.Even.sub_odd hp4 (Even.pow_of_ne_zero he2 (by norm_num)) odd_one
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem eta_involution_conj (m : ℕ) (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : etaProduct K m)
    (hxr : x.right = ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩) (hx : x ^ 2 = 1) :
    ∃ h : antiSp K, SemidirectProduct.inl h * x * (SemidirectProduct.inl h)⁻¹ =
      SemidirectProduct.inr ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set η := minorAut K ^ (2 * m + 1) with hηdef
  have hη2 : η ^ 2 = 1 := by rw [← orderOf_eta m hK, pow_orderOf_eq_one]
  obtain ⟨hPp, hPi⟩ := etaUnipotent_sylow m hK
  set P : Sylow 2 (etaProduct K m) := hPp.toSylow hPi with hPdef
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    have hdvd : orderOf x ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hx
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨y, rfl⟩ := MulAction.exists_smul_eq (etaProduct K m) P Q
  have hxQ : x ∈ ((y • P : Sylow 2 (etaProduct K m)) : Subgroup (etaProduct K m)) :=
    hQ (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨p, hpP, hpx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hpx
  set k := y.left⁻¹ with hk
  have hinr : ∀ ε, SemidirectProduct.inr ε ∈ etaUnipotent K m := fun ε => one_mem (antiUnipotent K)
  have hky : SemidirectProduct.inl k * y = SemidirectProduct.inr y.right := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        map_one, MulAut.one_apply, hk, inv_mul_cancel, SemidirectProduct.left_inr]
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul,
        SemidirectProduct.right_inr]
  have hx' : SemidirectProduct.inl k * x * (SemidirectProduct.inl k)⁻¹ ∈ etaUnipotent K m := by
    have h1 : SemidirectProduct.inl k * x * (SemidirectProduct.inl k)⁻¹ =
        SemidirectProduct.inr y.right * p * (SemidirectProduct.inr y.right)⁻¹ := by
      rw [← hpx, ← hky]
      group
    rw [h1]
    exact mul_mem (mul_mem (hinr _) hpP) (inv_mem (hinr _))
  set x' := SemidirectProduct.inl k * x * (SemidirectProduct.inl k)⁻¹ with hx'def
  have hx'r : x'.right = ⟨η, Subgroup.mem_zpowers _⟩ := by
    rw [hx'def, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right, SemidirectProduct.right_inl, hxr, one_mul, inv_one, mul_one]
  have hx'2 : x' ^ 2 = 1 := by
    rw [hx'def, sq]
    calc SemidirectProduct.inl k * x * (SemidirectProduct.inl k)⁻¹ *
          (SemidirectProduct.inl k * x * (SemidirectProduct.inl k)⁻¹)
        _ = SemidirectProduct.inl k * (x * x) * (SemidirectProduct.inl k)⁻¹ := by group
        _ = 1 := by rw [← sq, hx, mul_one, mul_inv_cancel]
  have hu1 : x'.left * η x'.left = 1 := by
    have h1 := congrArg SemidirectProduct.left hx'2
    rw [sq, SemidirectProduct.mul_left, hx'r] at h1
    exact h1
  obtain ⟨h₂, -, hh₂⟩ := eta_cocycle m hη2 hx' hu1
  refine ⟨h₂ * k, ?_⟩
  have h3 : SemidirectProduct.inl (h₂ * k) * x * (SemidirectProduct.inl (h₂ * k))⁻¹ =
      SemidirectProduct.inl h₂ * x' * (SemidirectProduct.inl h₂)⁻¹ := by
    rw [hx'def, map_mul]
    group
  rw [h3]
  have hleft : (SemidirectProduct.inl h₂ * x' * (SemidirectProduct.inl h₂)⁻¹).left =
      h₂ * x'.left * η h₂⁻¹ := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      inv_one, one_mul, map_one, MulAut.one_apply, hx'r, Subgroup.coe_subtype]
  refine SemidirectProduct.ext ?_ ?_
  · rw [hleft, map_inv, hh₂, SemidirectProduct.left_inr]
  · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, hx'r, SemidirectProduct.right_inr, one_mul, inv_one, mul_one]

end Sylow

end SpChain


open SpChain

theorem even_symplectic_two_nonsquare_outer_involution_descent (m : ℕ) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    orderOf (minorAut K ^ (2 * m + 1)) = 2 ∧
    (∀ x : antiSp K ⋊[(Subgroup.zpowers (minorAut K ^ (2 * m + 1))).subtype]
        Subgroup.zpowers (minorAut K ^ (2 * m + 1)),
      x.right = ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩ → x ^ 2 = 1 →
      ∃ h : antiSp K, SemidirectProduct.inl h * x * (SemidirectProduct.inl h)⁻¹ =
        SemidirectProduct.inr ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩) ∧
    (∀ g : antiSp K, g ∈ antiUnipotent K ↔
      (∀ i j : Fin 4, j < i → glMat (g : GL (Fin 4) K) i j = 0) ∧
        ∀ i, glMat (g : GL (Fin 4) K) i i = 1) ∧
    (∀ g : antiSp K, g ∈ antiUnipotent K ↔
      ∃ a b c d : K, glMat (g : GL (Fin 4) K) = uMat a b c d) ∧
    (∀ a b c d : K, ∃ g : antiSp K, glMat (g : GL (Fin 4) K) = uMat a b c d) ∧
    (∀ g : antiSp K, g ∈ antiUnipotentCenter K ↔
      ∃ b c : K, glMat (g : GL (Fin 4) K) = uMat 0 b c 0) ∧
    antiUnipotentCenter K ≤ antiUnipotent K ∧
    (∀ z ∈ antiUnipotentCenter K, ∀ u ∈ antiUnipotent K, z * u = u * z) ∧
    (∃ e : Multiplicative (K × K) ≃* antiUnipotentCenter K, ∀ b c : K,
      glMat (((e (Multiplicative.ofAdd (b, c)) : antiUnipotentCenter K) : antiSp K) :
        GL (Fin 4) K) = uMat 0 b c 0) ∧
    (∃ e : antiUnipotent K ⧸ (antiUnipotentCenter K).subgroupOf (antiUnipotent K) ≃*
        Multiplicative (K × K), ∀ g : antiUnipotent K,
      e (QuotientGroup.mk g) = Multiplicative.ofAdd (glMat ((g : antiSp K) : GL (Fin 4) K) 0 1,
        glMat ((g : antiSp K) : GL (Fin 4) K) 1 2)) ∧
    (∀ g ∈ antiUnipotent K, (minorAut K ^ (2 * m + 1)) g ∈ antiUnipotent K) ∧
    (∀ g ∈ antiUnipotentCenter K, (minorAut K ^ (2 * m + 1)) g ∈ antiUnipotentCenter K) ∧
    (∀ b c : K, glMat (((minorAut K ^ (2 * m + 1)) (uElt 0 b c 0) : antiSp K) : GL (Fin 4) K) =
      uMat 0 (c ^ 2 ^ m) (b ^ 2 ^ (m + 1)) 0) ∧
    ∀ a b c d : K, ∃ b' c' : K,
      glMat (((minorAut K ^ (2 * m + 1)) (uElt a b c d) : antiSp K) : GL (Fin 4) K) =
        uMat (d ^ 2 ^ m) b' c' (a ^ 2 ^ (m + 1)) := by
  have h0e : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hsq : ∀ x : K, (x ^ 2 ^ m) ^ 2 = x ^ 2 ^ (m + 1) := fun x => by
    rw [← pow_mul, ← pow_succ]
  have hZ : ∀ b c : K, glMat (((minorAut K ^ (2 * m + 1)) (uElt 0 b c 0) : antiSp K) :
      GL (Fin 4) K) = uMat 0 (c ^ 2 ^ m) (b ^ 2 ^ (m + 1)) 0 := by
    intro b c
    rw [glMat_eta_uElt, h0e, hsq]
    congr 1 <;> ring
  refine ⟨orderOf_eta m hK, eta_involution_conj m hK, mem_antiUnipotent_iff_upper,
    fun g => mem_antiUnipotent, fun a b c d => ⟨uElt a b c d, rfl⟩, fun g => ⟨?_, ?_⟩,
    antiUnipotentCenter_le, fun z hz u hu => antiUnipotentCenter_comm hz hu,
    ⟨centerEquiv, fun b c => rfl⟩, ⟨quotientEquiv, quotientEquiv_mk⟩,
    fun g hg => zpowers_eta_mem m (Subgroup.mem_zpowers _) hg, ?_, hZ,
    fun a b c d => ⟨_, _, by rw [glMat_eta_uElt, hsq]⟩⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, h⟩
    exact ⟨b, c, antiSp_ext h⟩
  · rintro _ ⟨b, c, rfl⟩
    exact ⟨_, _, antiSp_ext (hZ b c)⟩

end CFSG.ComponentClassification.UnbalancedCatalog
