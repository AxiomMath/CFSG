module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import CFSG.Foundations.Basic
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Abstract

variable {P : Type*} [Group P]

private theorem eq_one_of_mul_self (hP : Nat.card P = 27) {b : P} (hb : b * b = 1) : b = 1 := by
  have h27 : b ^ 27 = 1 := hP ▸ pow_card_eq_one'
  have h28 : b ^ 28 = 1 := by
    rw [show 28 = 2 * 14 from rfl, pow_mul, sq, hb, one_pow]
  rwa [pow_succ, h27, one_mul] at h28

private theorem card_cases (hP : Nat.card P = 27) (S : Subgroup P) :
    Nat.card S = 1 ∨ Nat.card S = 3 ∨ Nat.card S = 9 ∨ Nat.card S = 27 := by
  have h := S.card_subgroup_dvd_card
  rw [hP] at h
  obtain ⟨n, hn⟩ : ∃ n, Nat.card S = n := ⟨_, rfl⟩
  rw [hn] at h ⊢
  have h27 : n ≤ 27 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> omega

private theorem comm_of_map_commutator (hP : Nat.card P = 27)
    (hc : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center P) {φ : P →* P}
    (hφZ : ∀ z ∈ Subgroup.center P, φ z = z) {g h : P}
    (h1 : φ (g * h * g⁻¹ * h⁻¹) = (g * h * g⁻¹ * h⁻¹)⁻¹) : g * h = h * g := by
  have h3 : (g * h * g⁻¹ * h⁻¹)⁻¹ * (g * h * g⁻¹ * h⁻¹) = 1 := inv_mul_cancel _
  rw [← h1, hφZ _ (hc g h)] at h3
  have h4 := eq_one_of_mul_self hP h3
  calc g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
    _ = h * g := by rw [h4, one_mul]

private theorem comm_of_fix_inv (hP : Nat.card P = 27)
    (hc : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center P) {φ : P →* P}
    (hφZ : ∀ z ∈ Subgroup.center P, φ z = z) {f b : P} (hf : φ f = f) (hb : φ b = b⁻¹) :
    f * b = b * f := by
  apply comm_of_map_commutator hP hc hφZ
  have hz := Subgroup.mem_center_iff.1 (inv_mem (hc f b)) b⁻¹
  calc φ (f * b * f⁻¹ * b⁻¹) = b⁻¹ * (f * b * f⁻¹ * b⁻¹)⁻¹ * b := by
        simp only [map_mul, map_inv, hf, hb, inv_inv]; group
    _ = (f * b * f⁻¹ * b⁻¹)⁻¹ := by rw [hz, mul_assoc, inv_mul_cancel, mul_one]

private theorem false_of_fix_inv_comm (hP : Nat.card P = 27) (hZ : Nat.card (Subgroup.center P) = 3)
    {φ : P →* P} (hφZ : ∀ z ∈ Subgroup.center P, φ z = z) {a b : P}
    (ha : a ∉ Subgroup.center P) (hb : b ∉ Subgroup.center P) (hfa : φ a = a) (hfb : φ b = b⁻¹)
    (hab : a * b = b * a) : False := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  set C := Subgroup.centralizer ({a} : Set P)
  set A := φ.eqLocus (MonoidHom.id P) ⊓ C
  have hZA : Subgroup.center P < A := by
    refine SetLike.lt_iff_le_and_exists.2
      ⟨fun z hz => Subgroup.mem_inf.2 ⟨hφZ z hz, ?_⟩, a, Subgroup.mem_inf.2 ⟨hfa, ?_⟩, ha⟩
    · exact Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]; exact Subgroup.mem_center_iff.1 hz a
    · exact Subgroup.mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]
  have hAC : A < C := by
    refine SetLike.lt_iff_le_and_exists.2 ⟨inf_le_right, b, ?_, fun h => hb ?_⟩
    · exact Subgroup.mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg, hab]
    · have h' : φ b = b := (Subgroup.mem_inf.1 h).1
      rw [hfb] at h'
      have : b * b = 1 := by
        calc b * b = b * b⁻¹ := by rw [h']
          _ = 1 := mul_inv_cancel b
      rw [eq_one_of_mul_self hP this]; exact one_mem _
  have h1 := Subgroup.card_lt_of_lt hZA
  have h2 := Subgroup.card_lt_of_lt hAC
  have hC : Nat.card C = Nat.card P := by
    rcases card_cases hP A with h | h | h | h <;> rcases card_cases hP C with h' | h' | h' | h' <;>
      omega
  have hCtop := (Subgroup.card_eq_iff_eq_top C).1 hC
  refine ha (Subgroup.mem_center_iff.2 fun g => ?_)
  have hg : g ∈ C := hCtop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.1 hg a rfl).symm

private theorem fix_or_inv_mod_center (hP : Nat.card P = 27)
    (hZ : Nat.card (Subgroup.center P) = 3)
    (hc : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center P) {φ : P →* P}
    (hφφ : ∀ x, φ (φ x) = x) (hφZ : ∀ z ∈ Subgroup.center P, φ z = z) :
    (∀ x, x * φ x ∈ Subgroup.center P) ∨ (∀ x, x⁻¹ * φ x ∈ Subgroup.center P) := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hne
  have hxc : x * φ x = φ x * x := by
    apply comm_of_map_commutator hP hc hφZ
    simp only [map_mul, map_inv, hφφ]; group
  have ha : φ (x * φ x) = x * φ x := by rw [map_mul, hφφ, hxc]
  have hb : φ (y⁻¹ * φ y) = (y⁻¹ * φ y)⁻¹ := by
    rw [map_mul, map_inv, hφφ, _root_.mul_inv_rev, inv_inv]
  exact false_of_fix_inv_comm hP hZ hφZ hx hy ha hb (comm_of_fix_inv hP hc hφZ ha hb)

private theorem eq_of_inv_mul_mem (hP : Nat.card P = 27) {φ : P →* P} (hφφ : ∀ x, φ (φ x) = x)
    (hφZ : ∀ z ∈ Subgroup.center P, φ z = z) (h : ∀ x, x⁻¹ * φ x ∈ Subgroup.center P) (x : P) :
    φ x = x := by
  obtain ⟨c, hcZ, hcx⟩ : ∃ c ∈ Subgroup.center P, φ x = x * c := ⟨x⁻¹ * φ x, h x, by group⟩
  have h2 : x * (c * c) = x := by
    calc x * (c * c) = φ (x * c) := by rw [map_mul, hcx, hφZ c hcZ, mul_assoc]
      _ = x := by rw [← hcx, hφφ]
  have h3 : c * c = 1 := mul_left_cancel (a := x) (by rw [h2, mul_one])
  rw [hcx, eq_one_of_mul_self hP h3, mul_one]

private theorem inv_mul_comp_mem {φ₀ φ₁ : P →* P} (hφ₀Z : ∀ z ∈ Subgroup.center P, φ₀ z = z)
    (h0 : ∀ x, x * φ₀ x ∈ Subgroup.center P) (h1 : ∀ x, x * φ₁ x ∈ Subgroup.center P) (x : P) :
    x⁻¹ * φ₀ (φ₁ x) ∈ Subgroup.center P := by
  obtain ⟨c₁, hc₁, hx₁⟩ : ∃ c ∈ Subgroup.center P, φ₁ x = x⁻¹ * c := ⟨x * φ₁ x, h1 x, by group⟩
  obtain ⟨c₀, hc₀, hx₀⟩ : ∃ c ∈ Subgroup.center P, φ₀ x = x⁻¹ * c := ⟨x * φ₀ x, h0 x, by group⟩
  rw [hx₁, map_mul, map_inv, hx₀, hφ₀Z c₁ hc₁,
    show x⁻¹ * ((x⁻¹ * c₀)⁻¹ * c₁) = x⁻¹ * c₀⁻¹ * x⁻¹⁻¹ * c₁ by group]
  exact mul_mem (Subgroup.Normal.conj_mem inferInstance _ (inv_mem hc₀) x⁻¹) hc₁

private theorem exists_eq_id (hP : Nat.card P = 27) (hZ : Nat.card (Subgroup.center P) = 3)
    (hc : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center P) {φ₀ φ₁ φ₂ : P →* P}
    (hφ₀ : ∀ x, φ₀ (φ₀ x) = x) (hφ₁ : ∀ x, φ₁ (φ₁ x) = x) (hφ₂ : ∀ x, φ₂ (φ₂ x) = x)
    (hφ₀Z : ∀ z ∈ Subgroup.center P, φ₀ z = z) (hφ₁Z : ∀ z ∈ Subgroup.center P, φ₁ z = z)
    (hφ₂Z : ∀ z ∈ Subgroup.center P, φ₂ z = z) (h₂ : ∀ x, φ₂ x = φ₀ (φ₁ x)) :
    (∀ x, φ₀ x = x) ∨ (∀ x, φ₁ x = x) ∨ (∀ x, φ₂ x = x) := by
  rcases fix_or_inv_mod_center hP hZ hc hφ₀ hφ₀Z with h0 | h0
  · rcases fix_or_inv_mod_center hP hZ hc hφ₁ hφ₁Z with h1 | h1
    · exact Or.inr (Or.inr (eq_of_inv_mul_mem hP hφ₂ hφ₂Z fun x =>
        (h₂ x).symm ▸ inv_mul_comp_mem hφ₀Z h0 h1 x))
    · exact Or.inr (Or.inl (eq_of_inv_mul_mem hP hφ₁ hφ₁Z h1))
  · exact Or.inl (eq_of_inv_mul_mem hP hφ₀ hφ₀Z h0)

end Abstract

section Matrix

variable {q : ℕ} [Fact q.Prime] {H : Subgroup (GL (Fin 3) (ZMod q))}

private theorem mulVec_inj_or_eq_zero (hirr : IsIrreducibleMatrixRep H.subtype)
    (N : Matrix (Fin 3) (Fin 3) (ZMod q))
    (hN : ∀ x ∈ H, N * (x : Matrix (Fin 3) (Fin 3) (ZMod q)) = (x : Matrix _ _ _) * N) :
    (∀ v, N *ᵥ v = 0 → v = 0) ∨ N = 0 := by
  have hinv : ∀ g : H, ∀ w ∈ LinearMap.ker N.mulVecLin,
      ((H.subtype g : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) *ᵥ w ∈
        LinearMap.ker N.mulVecLin := by
    intro g w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
    rw [Subgroup.coe_subtype, Matrix.mulVec_mulVec, hN g g.2, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  rcases hirr _ hinv with h | h
  · left
    intro v hv
    have hv' : v ∈ LinearMap.ker N.mulVecLin := hv
    rw [h] at hv'
    exact (Submodule.mem_bot _).1 hv'
  · right
    ext i j
    have hj : Pi.single j 1 ∈ LinearMap.ker N.mulVecLin := h ▸ Submodule.mem_top
    have h2 := congrFun (LinearMap.mem_ker.1 hj) i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using h2

private theorem exists_cube_root (hq3 : q % 3 = 1) :
    ∃ ω : ZMod q, ω ^ 3 = 1 ∧ 1 + ω + ω ^ 2 = 0 := by
  have h3 : 3 ∣ Nat.card (ZMod q)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]; omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hu3 : (u : ZMod q) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : ZMod q) ≠ 1 := by
    intro h
    rw [show u = 1 from Units.ext h, orderOf_one] at hu
    norm_num at hu
  refine ⟨u, hu3, ?_⟩
  have : ((u : ZMod q) - 1) * (1 + u + u ^ 2) = 0 := by linear_combination hu3
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu1)

private theorem cube_factor {M : Matrix (Fin 3) (Fin 3) (ZMod q)} (hM3 : M ^ 3 = 1) {ω : ZMod q}
    (hω3 : ω ^ 3 = 1) (hω : 1 + ω + ω ^ 2 = 0) :
    (M - algebraMap (ZMod q) _ 1) * (M - algebraMap (ZMod q) _ ω) *
      (M - algebraMap (ZMod q) _ (ω ^ 2)) = 0 := by
  have hp : (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ω) *
      (Polynomial.X - Polynomial.C (ω ^ 2)) = (Polynomial.X ^ 3 - 1 : Polynomial (ZMod q)) := by
    have h1 : Polynomial.C ω ^ 3 = (1 : Polynomial (ZMod q)) := by
      rw [← map_pow, hω3, map_one]
    have h2 : 1 + Polynomial.C ω + Polynomial.C ω ^ 2 = (0 : Polynomial (ZMod q)) := by
      rw [← map_pow, ← map_one Polynomial.C, ← map_add, ← map_add, hω, map_zero]
    rw [map_one, map_pow]
    linear_combination (-Polynomial.X ^ 2 + Polynomial.X) * h2 + (Polynomial.X - 1) * h1
  have := congrArg (Polynomial.aeval M) hp
  rw [map_mul, map_mul, map_sub, map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Polynomial.aeval_C, Polynomial.aeval_C, map_sub, Polynomial.aeval_X_pow, hM3, map_one, map_one,
    sub_self] at this
  rwa [map_one]

private theorem scalar_of_mem_center (hq3 : q % 3 = 1) (hirr : IsIrreducibleMatrixRep H.subtype)
    (hZ : Nat.card (Subgroup.center H) = 3) {z : H} (hz : z ∈ Subgroup.center H) :
    ∃ c : ZMod q, ((z : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) =
      algebraMap (ZMod q) _ c := by
  obtain ⟨ω, hω3, hω⟩ := exists_cube_root hq3
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (x := (⟨z, hz⟩ : Subgroup.center H))
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  have hM3 : ((z : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) ^ 3 = 1 := by
    simpa using congrArg
      (fun g : H => ((g : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q))) hz3
  have key : ∀ c : ZMod q, (((z : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) -
      algebraMap _ _ c).det = 0 →
        ((z : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) = algebraMap _ _ c := by
    intro c hc
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hc
    refine (mulVec_inj_or_eq_zero hirr _ fun x hx => ?_).elim (fun h => absurd (h v hv) hv0)
      sub_eq_zero.1
    have h2 := congrArg (fun g : H => ((g : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)))
      (Subgroup.mem_center_iff.1 hz ⟨x, hx⟩)
    simp only [Subgroup.coe_mul, Units.val_mul] at h2
    rw [sub_mul, mul_sub, h2, Algebra.commutes]
  have hdet := congrArg Matrix.det (cube_factor hM3 hω3 hω)
  rw [det_mul, det_mul, det_zero] at hdet
  rcases mul_eq_zero.1 hdet with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact ⟨1, key 1 h⟩
    · exact ⟨ω, key ω h⟩
  · exact ⟨ω ^ 2, key _ h⟩

private theorem val_diagSign (i : Fin 3) :
    ((diagSign i : GL (Fin 3) (ZMod q)) : Matrix (Fin 3) (Fin 3) (ZMod q)) =
      diagonal fun j => if j = i then 1 else -1 := by
  change diagonal _ = _
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

private theorem diagSign_mul_self (i : Fin 3) :
    (diagSign i : GL (Fin 3) (ZMod q)) * diagSign i = 1 := by
  apply Units.ext
  rw [Units.val_mul, val_diagSign, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

private theorem diagSign_two :
    (diagSign 2 : GL (Fin 3) (ZMod q)) = diagSign 0 * diagSign 1 := by
  apply Units.ext
  rw [Units.val_mul, val_diagSign, val_diagSign, val_diagSign, diagonal_mul_diagonal]
  congr 1
  funext j
  fin_cases j <;> norm_num

private def conjSign (hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H)
    (i : Fin 3) : H →* H where
  toFun x := ⟨diagSign i * (x : GL (Fin 3) (ZMod q)) * (diagSign i : GL (Fin 3) (ZMod q))⁻¹,
    hd i x x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

private theorem conjSign_conjSign (hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H)
    (i : Fin 3) (x : H) : conjSign hd i (conjSign hd i x) = x := by
  apply Subtype.ext
  have hdd := diagSign_mul_self (q := q) i
  set d : GL (Fin 3) (ZMod q) := diagSign i
  change d * (d * (x : GL (Fin 3) (ZMod q)) * d⁻¹) * d⁻¹ = x
  rw [inv_eq_of_mul_eq_one_right hdd]
  calc _ = (d * d) * (x : GL (Fin 3) (ZMod q)) * (d * d) := by group
    _ = x := by rw [hdd, one_mul, mul_one]

private theorem false_of_commute (hirr : IsIrreducibleMatrixRep H.subtype) (hq3 : q % 3 = 1)
    (i : Fin 3) (h : ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ = x) : False := by
  have hcomm : ∀ x ∈ H, (((diagSign i : GL (Fin 3) (ZMod q)) : Matrix _ _ _) - 1) *
      (x : Matrix (Fin 3) (Fin 3) (ZMod q)) =
      (x : Matrix _ _ _) * (((diagSign i : GL (Fin 3) (ZMod q)) : Matrix _ _ _) - 1) := by
    intro x hx
    have h1 : (diagSign i : GL (Fin 3) (ZMod q)) * x = x * diagSign i := by
      calc _ = diagSign i * x * (diagSign i)⁻¹ * diagSign i := by group
        _ = _ := by rw [h x hx]
    have h2 := congrArg Units.val h1
    simp only [Units.val_mul] at h2
    rw [sub_mul, mul_sub, h2, one_mul, mul_one]
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h2
    rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).1 h2
    omega
  rcases mulVec_inj_or_eq_zero hirr _ hcomm with h | h
  · have := congrFun (h (Pi.single i 1) ?_) i
    · rw [Pi.single_eq_same, Pi.zero_apply] at this
      exact one_ne_zero this
    · ext k
      rw [Matrix.mulVec_single_one, val_diagSign]
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk, one_apply_ne hk]
  · have := congrFun (congrFun h (i + 1)) (i + 1)
    rw [Matrix.sub_apply, val_diagSign, diagonal_apply_eq, one_apply_eq,
      if_neg (by fin_cases i <;> decide), Matrix.zero_apply] at this
    exact h2 (by linear_combination -this)

end Matrix

theorem false_of_extraspecial {q : ℕ} [Fact q.Prime] (hq3 : q % 3 = 1)
    {H : Subgroup (GL (Fin 3) (ZMod q))} (hirr : IsIrreducibleMatrixRep H.subtype)
    (hcard : Nat.card H = 27) (hex : CFSG.IsExtraspecialPGroup 3 H)
    (hd : ∀ i : Fin 3, ∀ x ∈ H, diagSign i * x * (diagSign i)⁻¹ ∈ H) : False := by
  have hZ : Nat.card (Subgroup.center H) = 3 := hex.2.2.2
  have hc : ∀ g h : H, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center H := fun g h => by
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
    rw [commutatorElement_def] at this
    exact hex.2.1 ▸ this
  have hfixZ : ∀ i, ∀ z ∈ Subgroup.center H, conjSign hd i z = z := fun i z hz => by
    obtain ⟨c, hc⟩ := scalar_of_mem_center hq3 hirr hZ hz
    apply Subtype.ext
    apply Units.ext
    change ((diagSign i * (z : GL (Fin 3) (ZMod q)) * (diagSign i)⁻¹ : GL (Fin 3) (ZMod q)) :
      Matrix (Fin 3) (Fin 3) (ZMod q)) = _
    rw [Units.val_mul, Units.val_mul, hc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
  have h₂ : ∀ x, conjSign hd 2 x = conjSign hd 0 (conjSign hd 1 x) := fun x => by
    apply Subtype.ext
    change diagSign 2 * (x : GL (Fin 3) (ZMod q)) * (diagSign 2)⁻¹ =
      diagSign 0 * (diagSign 1 * (x : GL (Fin 3) (ZMod q)) * (diagSign 1)⁻¹) * (diagSign 0)⁻¹
    rw [diagSign_two]; group
  rcases exists_eq_id hcard hZ hc (conjSign_conjSign hd 0) (conjSign_conjSign hd 1)
    (conjSign_conjSign hd 2) (hfixZ 0) (hfixZ 1) (hfixZ 2) h₂ with h | h | h
  · exact false_of_commute hirr hq3 0 fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)
  · exact false_of_commute hirr hq3 1 fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)
  · exact false_of_commute hirr hq3 2 fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
