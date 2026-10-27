module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Phan.Torus
public import CFSG.ClassicalInvolution.Phan.TorusAgree

public section

namespace CFSG.ClassicalInvolution.PhanD4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary

section Matrix

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  (hK : Nat.card K = (p ^ f) ^ 2)

include hK in
theorem exists_normOne_sq_ne_one (hq : 3 ≤ p ^ f) :
    ∃ x : normOne (unitaryInvolution K p f), x * x ≠ 1 := by
  have hcard := card_normOne hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := normOne (unitaryInvolution K p f))
  refine ⟨g, fun h => ?_⟩
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have h3 : orderOf g = Nat.card (normOne (unitaryInvolution K p f)) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem coe_ne_inv_of_mul_self_ne_one {x : normOne (unitaryInvolution K p f)} (hx : x * x ≠ 1) :
    ((x : Kˣ) : K) ≠ (((x : Kˣ)⁻¹ : Kˣ) : K) := by
  intro h
  apply hx
  apply Subtype.ext
  apply Units.ext
  have h1 : (x : Kˣ) = (x : Kˣ)⁻¹ := Units.ext h
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  calc (((x : Kˣ) * (x : Kˣ) : Kˣ) : K) = (((x : Kˣ) * (x : Kˣ)⁻¹ : Kˣ) : K) := by rw [← h1]
    _ = 1 := by simp

theorem mem_range_torusTwo_of_commute {x : normOne (unitaryInvolution K p f)} (hx : x * x ≠ 1)
    {A : Su K p f 2} (h : A * torusTwo (unitaryInvolution K p f) x =
      torusTwo (unitaryInvolution K p f) x * A) :
    A ∈ (torusTwo (unitaryInvolution K p f)).range := by
  have h' := congrArg (fun g : Su K p f 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_torusTwo] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h10 := congrFun (congrFun h' 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  have hne := coe_ne_inv_of_mul_self_ne_one hx
  refine mem_range_torusTwo_of_offDiag A ?_ ?_
  · by_contra h0
    apply hne
    have : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
        ((((x : Kˣ)⁻¹ : Kˣ) : K) - ((x : Kˣ) : K)) = 0 := by
      simp only [Units.val_inv_eq_inv_val] at h01 ⊢
      linear_combination h01
    have := (mul_eq_zero.mp this).resolve_left h0
    linear_combination -this
  · by_contra h0
    apply hne
    have : ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 *
        (((x : Kˣ) : K) - ((((x : Kˣ)⁻¹ : Kˣ) : K))) = 0 := by
      simp only [Units.val_inv_eq_inv_val] at h10 ⊢
      linear_combination h10
    have := (mul_eq_zero.mp this).resolve_left h0
    linear_combination this

theorem blockEmb2_two_zero :
    blockEmb2 K p f 2 0 = embSUid (unitaryInvolution K p f) 2 := by
  rw [embSUid_two_eq_blockEmb]
  rfl

theorem blockEmb2_two_one :
    blockEmb2 K p f 2 1 = embSUid (unitaryInvolution K p f) 0 := by
  rw [embSUid_zero_eq_blockEmb]
  rfl

theorem exists_embSUid_torus_of_commute {x : normOne (unitaryInvolution K p f)}
    (hx : x * x ≠ 1) {B : Su K p f 3}
    (h : B * embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) x) =
      embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) x) * B) :
    ∃ y w : normOne (unitaryInvolution K p f),
      B = embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) y) *
        embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) w) := by
  have h' := congrArg (fun g : Su K p f 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo] at h'
  have hne := coe_ne_inv_of_mul_self_ne_one hx
  have hx1 : ((x : Kˣ) : K) ≠ 1 := by
    intro h1
    apply hx
    apply Subtype.ext
    apply Units.ext
    simp [h1]
  have hx2 : (((x : Kˣ)⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h1
    apply hx1
    have : (x : Kˣ) = 1 := inv_eq_one.mp (Units.ext (by simpa using h1))
    rw [this]
    rfl
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  have e02 := congrFun (congrFun h' 0) 2
  have e20 := congrFun (congrFun h' 2) 0
  have e12 := congrFun (congrFun h' 1) 2
  have e21 := congrFun (congrFun h' 2) 1
  simp [embPair, Matrix.mul_apply, Fin.sum_univ_three] at e01 e10 e02 e20 e12 e21
  set M : Matrix (Fin 3) (Fin 3) K := ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hinv : (((x : Kˣ)⁻¹ : Kˣ) : K) = ((x : Kˣ) : K)⁻¹ := by simp
  have hx0 : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [hinv] at hne hx2
  have hxx : ((x : Kˣ) : K) * ((x : Kˣ) : K) ≠ 1 := by
    intro h1
    apply hx
    exact Subtype.ext (Units.ext (by simpa using h1))
  have z01 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    refine eq_zero_of_eq_mul_self_of_ne_one hxx ?_
    field_simp at e01 ⊢
    linear_combination e01
  have z10 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    refine eq_zero_of_eq_mul_self_of_ne_one (u := ((x : Kˣ) : K)⁻¹ * ((x : Kˣ) : K)⁻¹) ?_ ?_
    · intro h1
      apply hxx
      field_simp at h1
      linear_combination -h1
    · field_simp at e10 ⊢
      linear_combination e10
  have z02 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 :=
    eq_zero_of_eq_mul_self_of_ne_one hx1 e02
  have z20 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    eq_zero_of_eq_mul_self_of_ne_one hx1 (by linear_combination -e20)
  have z12 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 :=
    eq_zero_of_eq_mul_self_of_ne_one hx2 e12
  have z21 : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 :=
    eq_zero_of_eq_mul_self_of_ne_one hx2 (by linear_combination -e21)
  have hB : B ∈ torus (unitaryInvolution K p f) 3 := by
    rw [mem_torus_iff]
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption
  obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) 2).surjective ⟨B, hB⟩
  have hs' : B = ((torusEquiv (unitaryInvolution K p f) 2 s : torus (unitaryInvolution K p f)
      (2 + 1)) : Su K p f 3) := by rw [hs]
  have hsplit : s = Pi.mulSingle 0 (s 0) * Pi.mulSingle 1 (s 1) := by
    ext i
    fin_cases i <;> simp
  refine ⟨s 0, s 1, ?_⟩
  rw [hs', hsplit, map_mul, Subgroup.coe_mul, coe_torusEquiv_mulSingle, coe_torusEquiv_mulSingle,
    blockEmb2_two_zero, blockEmb2_two_one]
  simp

noncomputable def weylSU {F : Type*} [Field F] (σ : F ≃+* F) : SUid σ 2 :=
  ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩,
   by simp [Matrix.det_fin_two],
   by ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two]⟩

include hK in
theorem eq_one_of_conjDiag_weyl {r : normOne (unitaryInvolution K p f)}
    (h : conjDiag hK ![r, 1] (weylSU (unitaryInvolution K p f)) =
      weylSU (unitaryInvolution K p f)) : r = 1 := by
  have h1 := congrArg (fun g : Su K p f 2 => ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp only [coe_conjDiag_apply] at h1
  simp [weylSU] at h1
  exact Subtype.ext (Units.ext (by simpa using h1))

@[expose] def negOne {F : Type*} [Field F] (σ : F ≃+* F) : normOne σ :=
  ⟨-1, by rw [mem_normOne]; simp⟩

theorem coe_negOne {F : Type*} [Field F] (σ : F ≃+* F) : (((negOne σ : normOne σ) : Fˣ) : F) = -1 :=
  rfl

theorem negOne_mul_self {F : Type*} [Field F] (σ : F ≃+* F) : negOne σ * negOne σ = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [coe_negOne]

theorem negOne_inv {F : Type*} [Field F] (σ : F ≃+* F) : (negOne σ)⁻¹ = negOne σ :=
  inv_eq_of_mul_eq_one_right (negOne_mul_self σ)

theorem negOne_ne_one {F : Type*} [Field F] (σ : F ≃+* F) (h2 : (2 : F) ≠ 0) :
    negOne σ ≠ 1 := by
  intro h
  have h1 := congrArg (fun u : normOne σ => (((u : normOne σ) : Fˣ) : F)) h
  simp only [coe_negOne] at h1
  apply h2
  simp only [Subgroup.coe_one, Units.val_one] at h1
  linear_combination -h1

include hK in
theorem exists_scalar_decomp {z : Su K p f 3} (hz : z ∈ Subgroup.center (Su K p f 3)) :
    ∃ u : normOne (unitaryInvolution K p f),
      z = embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) u) *
        embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) u⁻¹) := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center (isUnitaryInvolution_unitaryInvolution hK)
    (le_refl 3) hz
  have hdet : ((u : Kˣ) : K) ^ 3 = 1 := by
    have := z.2.1
    rw [hu, Matrix.scalar_apply, Matrix.det_diagonal] at this
    simpa using this
  have hnorm : unitaryInvolution K p f ((u : Kˣ) : K) * ((u : Kˣ) : K) = 1 := by
    have h2 := congrFun (congrFun z.2.2 0) 0
    rw [hu] at h2
    simpa [conjTr, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using h2
  refine ⟨⟨u, hnorm⟩, Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))⟩
  have hu0 : ((u : Kˣ) : K) ≠ 0 := Units.ne_zero _
  rw [hu]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo]
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply]
  field_simp
  linear_combination hdet

end Matrix

section Cartan

theorem cartan_aux {F : Type*} [Field F] {a b c d : F} (ha : a ≠ 0) (e0 : a * a = b)
    (e2 : c * c = b) (e3 : d * d = b) (e1 : b * b = a * c * d) :
    b = 1 ∧ ((a = 1 ∧ c = 1 ∧ d = 1) ∨ (a = -1 ∧ c = 1 ∧ d = -1) ∨
      (a = -1 ∧ c = -1 ∧ d = 1) ∨ (a = 1 ∧ c = -1 ∧ d = -1)) := by
  have hc : c = a ∨ c = -a := mul_self_eq_mul_self_iff.mp (e2.trans e0.symm)
  have hd : d = a ∨ d = -a := mul_self_eq_mul_self_iff.mp (e3.trans e0.symm)
  have ha3 : a * a * a ≠ 0 := mul_ne_zero (mul_ne_zero ha ha) ha
  subst e0
  rcases hc with hc | hc <;> rcases hd with hd | hd <;> rw [hc, hd] at e1 ⊢
  · have h' : a * a * a * (a - 1) = 0 := by linear_combination e1
    have h : a = 1 := by linear_combination (mul_eq_zero.mp h').resolve_left ha3
    subst h
    exact ⟨by ring, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · have h' : a * a * a * (a + 1) = 0 := by linear_combination e1
    have h : a = -1 := by linear_combination (mul_eq_zero.mp h').resolve_left ha3
    subst h
    exact ⟨by ring, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by ring⟩))⟩
  · have h' : a * a * a * (a + 1) = 0 := by linear_combination e1
    have h : a = -1 := by linear_combination (mul_eq_zero.mp h').resolve_left ha3
    subst h
    exact ⟨by ring, Or.inr (Or.inl ⟨rfl, by ring, rfl⟩)⟩
  · have h' : a * a * a * (a - 1) = 0 := by linear_combination e1
    have h : a = 1 := by linear_combination (mul_eq_zero.mp h').resolve_left ha3
    subst h
    exact ⟨by ring, Or.inr (Or.inr (Or.inr ⟨rfl, by ring, by ring⟩))⟩

theorem cartan_solutions {F : Type*} [Field F] {σ : F ≃+* F} {t0 t1 t2 t3 : normOne σ}
    (h0 : t0 * t0 = t1) (h2 : t2 * t2 = t1) (h3 : t3 * t3 = t1)
    (h1 : t1 * t1 = t0 * t2 * t3) :
    t1 = 1 ∧ ((t0 = 1 ∧ t2 = 1 ∧ t3 = 1) ∨ (t0 = negOne σ ∧ t2 = 1 ∧ t3 = negOne σ) ∨
      (t0 = negOne σ ∧ t2 = negOne σ ∧ t3 = 1) ∨ (t0 = 1 ∧ t2 = negOne σ ∧ t3 = negOne σ)) := by
  have vm : ∀ u w : normOne σ, (((u * w : normOne σ) : Fˣ) : F) =
      ((u : Fˣ) : F) * ((w : Fˣ) : F) := fun u w => rfl
  have hone : ∀ u : normOne σ, ((u : Fˣ) : F) = 1 → u = 1 := fun u h =>
    Subtype.ext (Units.ext (by simpa using h))
  have hneg : ∀ u : normOne σ, ((u : Fˣ) : F) = -1 → u = negOne σ := fun u h =>
    Subtype.ext (Units.ext (by simpa [coe_negOne] using h))
  have e0 := congrArg (fun u : normOne σ => (((u : normOne σ) : Fˣ) : F)) h0
  have e2 := congrArg (fun u : normOne σ => (((u : normOne σ) : Fˣ) : F)) h2
  have e3 := congrArg (fun u : normOne σ => (((u : normOne σ) : Fˣ) : F)) h3
  have e1 := congrArg (fun u : normOne σ => (((u : normOne σ) : Fˣ) : F)) h1
  simp only [vm] at e0 e1 e2 e3
  obtain ⟨hb, hcases⟩ := cartan_aux (Units.ne_zero _) e0 e2 e3 e1
  refine ⟨hone _ hb, ?_⟩
  rcases hcases with ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩
  · exact Or.inl ⟨hone _ x, hone _ y, hone _ z⟩
  · exact Or.inr (Or.inl ⟨hneg _ x, hone _ y, hneg _ z⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hneg _ x, hneg _ y, hone _ z⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hone _ x, hneg _ y, hneg _ z⟩))

end Cartan

end CFSG.ClassicalInvolution.PhanD4
