module

public import CFSG.ClassicalInvolution.Asc77.AscC25V35

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.GorensteinWalter
open scoped MatrixGroups

section Alg

variable {F : Type} [Field F] [Finite F]

theorem isSquare_of_twisted_norm {m : ℕ} (hm : Odd m) (hcard : Nat.card F = m ^ 2)
    (hchar : ringChar F ≠ 2) (ψ : F ≃+* F) {d e c μ : F} (hd : d ≠ 0) (he : e ≠ 0) (hc : c ≠ 0)
    (h1 : d * ψ e = c ^ 2 * e * d ^ m) (h2 : e ^ (m + 1) = μ ^ 2)
    (h3 : ψ μ = c ^ (m + 1) * μ) : IsSquare d := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨j, rfl⟩ := hm
  rw [FiniteField.isSquare_iff hchar hd, ← Nat.card_eq_fintype_card, hcard]
  have hq : (2 * j + 1) ^ 2 / 2 = (2 * j + 2) * j := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  rw [hq]
  have hψe : ψ e = c ^ 2 * e * d ^ (2 * j) := by
    apply mul_left_cancel₀ hd
    calc d * ψ e = c ^ 2 * e * d ^ (2 * j + 1) := h1
      _ = d * (c ^ 2 * e * d ^ (2 * j)) := by ring
  have hE : ψ (e ^ (j + 1)) = (c ^ 2) ^ (j + 1) * e ^ (j + 1) := by
    have hsq : (e ^ (j + 1)) ^ 2 = μ ^ 2 := by
      have hexp : (j + 1) * 2 = 2 * j + 1 + 1 := by ring
      rw [← pow_mul, hexp, h2]
    have hc2 : c ^ (2 * j + 1 + 1) = (c ^ 2) ^ (j + 1) := by
      have hexp : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
      rw [← pow_mul, hexp]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hE | hE
    · rw [hE, h3, hc2]
    · rw [hE, map_neg, h3, hc2]
      ring
  have h4 : ψ e ^ (j + 1) = (c ^ 2) ^ (j + 1) * e ^ (j + 1) * (d ^ (2 * j)) ^ (j + 1) := by
    rw [hψe, mul_pow, mul_pow]
  have h5 : ψ e ^ (j + 1) = (c ^ 2) ^ (j + 1) * e ^ (j + 1) := by
    rw [← map_pow]
    exact hE
  have hne : (c ^ 2) ^ (j + 1) * e ^ (j + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hc)) (pow_ne_zero _ he)
  have h6 : (d ^ (2 * j)) ^ (j + 1) = 1 := by
    apply mul_left_cancel₀ hne
    rw [mul_one, ← h4, h5]
  have hexp : (2 * j + 2) * j = 2 * j * (j + 1) := by ring
  rw [hexp, pow_mul]
  exact h6

end Alg

section Abstract

variable {M Z : Type*} [Group M] [CommGroup Z]

theorem scalar_relation (sc : Z →* M) (hc : ∀ (z : Z) (x : M), sc z * x = x * sc z)
    (hsc_inj : Function.Injective sc) (s t : M →* M) (σz ψz : Z →* Z)
    (hss : ∀ x, s (s x) = x) (hst : ∀ x, s (t x) = t (s x)) (hs : ∀ z, s (sc z) = sc (σz z))
    (ht : ∀ z, t (sc z) = sc (ψz z)) (hσσ : ∀ z, σz (σz z) = z)
    (hψσ : ∀ z, ψz (σz z) = σz (ψz z)) {b g : M} {μ u : Z} (H1 : b * s b = sc μ)
    (H2 : (g * t b) * sc u = b * s g) : μ = ψz μ * (u * σz u) := by
  have E1 : s g * s (t b) * sc (σz u) = s b * g := by
    have := congrArg s H2
    simpa only [map_mul, hs, hss] using this
  have E2 : s b * b = sc (σz μ) := by
    have := congrArg s H1
    simpa only [map_mul, hs, hss] using this
  have E3 : s (t b) * t b = sc (ψz (σz μ)) := by
    rw [hst, ← map_mul, E2, ht]
  have key : ∀ (A B T : M) (a d : Z),
      (A * B * sc a) * T * sc d = A * (B * T) * (sc a * sc d) := by
    intro A B T a d
    calc (A * B * sc a) * T * sc d = A * B * (sc a * T) * sc d := by simp only [mul_assoc]
      _ = A * B * (T * sc a) * sc d := by rw [hc a T]
      _ = A * (B * T) * (sc a * sc d) := by simp only [mul_assoc]
  have E4 : s g * sc (σz μ) = s g * sc (ψz (σz μ) * (σz u * u)) := by
    calc s g * sc (σz μ) = sc (σz μ) * s g := (hc _ _).symm
      _ = (s b * b) * s g := by rw [E2]
      _ = s b * (b * s g) := by rw [mul_assoc]
      _ = s b * ((g * t b) * sc u) := by rw [H2]
      _ = (s b * g) * t b * sc u := by simp only [mul_assoc]
      _ = (s g * s (t b) * sc (σz u)) * t b * sc u := by rw [E1]
      _ = s g * (s (t b) * t b) * (sc (σz u) * sc u) := key _ _ _ _ _
      _ = s g * sc (ψz (σz μ)) * (sc (σz u) * sc u) := by rw [E3]
      _ = s g * sc (ψz (σz μ) * (σz u * u)) := by simp only [map_mul, mul_assoc]
  have E5 : σz μ = ψz (σz μ) * (σz u * u) := hsc_inj (mul_left_cancel E4)
  have E6 := congrArg σz E5
  rw [hσσ, map_mul, map_mul, hσσ, ← hψσ, hσσ] at E6
  exact E6

end Abstract

section GLRel

variable {F : Type} [Field F]

theorem scalar_injective_two {F : Type} [Field F] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
  intro u v h
  have h6 := congrArg (fun x : GL (Fin 2) F => x.val 0 0) h
  apply Units.ext
  simpa using h6

theorem scalar_relation_GL (σ ψ : F ≃+* F) (hσσ : ∀ x, σ (σ x) = x)
    (hψσ : ∀ x, ψ (σ x) = σ (ψ x)) {b g : GL (Fin 2) F} {μ u : Fˣ}
    (H1 : b * Matrix.GeneralLinearGroup.map σ.toRingHom b =
      Matrix.GeneralLinearGroup.scalar (Fin 2) μ)
    (H2 : (g * Matrix.GeneralLinearGroup.map ψ.toRingHom b) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      b * Matrix.GeneralLinearGroup.map σ.toRingHom g) :
    μ = Units.map (ψ.toRingHom : F →* F) μ * (u * Units.map (σ.toRingHom : F →* F) u) := by
  have hcompσ : σ.toRingHom.comp σ.toRingHom = RingHom.id _ := by
    ext x
    exact hσσ x
  have hcompσψ : σ.toRingHom.comp ψ.toRingHom = ψ.toRingHom.comp σ.toRingHom := by
    ext x
    exact (hψσ x).symm
  have hss : ∀ x : GL (Fin 2) F,
      Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map σ.toRingHom x) =
        x := fun x => by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map σ.toRingHom x) =
        Matrix.GeneralLinearGroup.map (σ.toRingHom.comp σ.toRingHom) x := rfl
      _ = x := by rw [hcompσ]; rfl
  have hst : ∀ x : GL (Fin 2) F,
      Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map ψ.toRingHom x) =
        Matrix.GeneralLinearGroup.map ψ.toRingHom
          (Matrix.GeneralLinearGroup.map σ.toRingHom x) := fun x => by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map ψ.toRingHom x) =
        Matrix.GeneralLinearGroup.map (σ.toRingHom.comp ψ.toRingHom) x := rfl
      _ = Matrix.GeneralLinearGroup.map (ψ.toRingHom.comp σ.toRingHom) x := by rw [hcompσψ]
      _ = _ := rfl
  have hσσ' : ∀ z : Fˣ, Units.map (σ.toRingHom : F →* F) (Units.map (σ.toRingHom : F →* F) z) =
      z := fun z => Units.ext (hσσ z)
  have hψσ' : ∀ z : Fˣ, Units.map (ψ.toRingHom : F →* F) (Units.map (σ.toRingHom : F →* F) z) =
      Units.map (σ.toRingHom : F →* F) (Units.map (ψ.toRingHom : F →* F) z) := fun z =>
    Units.ext (hψσ z)
  exact scalar_relation (Matrix.GeneralLinearGroup.scalar (Fin 2))
    (fun z x => Matrix.GeneralLinearGroup.scalar_commute z x) scalar_injective_two
    (Matrix.GeneralLinearGroup.map σ.toRingHom) (Matrix.GeneralLinearGroup.map ψ.toRingHom)
    (Units.map (σ.toRingHom : F →* F)) (Units.map (ψ.toRingHom : F →* F)) hss hst
    (fun z => Matrix.GeneralLinearGroup.map_scalar σ.toRingHom z)
    (fun z => Matrix.GeneralLinearGroup.map_scalar ψ.toRingHom z) hσσ' hψσ' H1 H2

end GLRel

section Comm

variable {p f : ℕ} [Fact p.Prime]

theorem mk_map_eq_pgl2FieldAut (τ : GaloisField p f ≃+* GaloisField p f)
    (x : GL (Fin 2) (GaloisField p f)) :
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map τ.toRingHom x) =
      pgl2FieldAut (GaloisField p f) τ (Matrix.ProjGenLinGroup.mk x) := by
  rw [pgl2FieldAut_apply]
  exact (pgl2RingEquiv_mk τ x).symm

open CFSG.ClassicalInvolution.Asc77.AscL62 in
theorem diagGamma_eq_one_of_commute (hp : p ≠ 2) (hf : f ≠ 0)
    (α α' : PGammaL2 (GaloisField p f)) (hα : α * α = 1) (hσ : α.right ≠ 1)
    (hcomm : α' * α = α * α') : diagGamma α' = 1 := by
  classical
  have hσ2 : α.right * α.right = 1 := by
    have h2 := congrArg SemidirectProduct.right hα
    simpa using h2
  have hleft : α.left * (pgl2FieldAut (GaloisField p f) α.right) α.left = 1 := by
    have h2 := congrArg SemidirectProduct.left hα
    simpa using h2
  have hcl : α'.left * (pgl2FieldAut (GaloisField p f) α'.right) α.left =
      α.left * (pgl2FieldAut (GaloisField p f) α.right) α'.left := by
    have h2 := congrArg SemidirectProduct.left hcomm
    simpa using h2
  have hcr : α'.right * α.right = α.right * α'.right := by
    have h2 := congrArg SemidirectProduct.right hcomm
    simpa using h2
  obtain ⟨k, hfk, hfrob⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ
  rw [diagGamma_apply]
  obtain ⟨g, hg⟩ := Matrix.ProjGenLinGroup.mk_surjective α'.left
  obtain ⟨b, hb⟩ := Matrix.ProjGenLinGroup.mk_surjective α.left
  set σ := α.right with hσdef
  set ψ := α'.right with hψdef
  have hσσ : ∀ x : GaloisField p f, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : GaloisField p f ≃+* GaloisField p f => τ x) hσ2
    simpa using this
  have hψσ : ∀ x : GaloisField p f, ψ (σ x) = σ (ψ x) := fun x => by
    have := congrArg (fun τ : GaloisField p f ≃+* GaloisField p f => τ x) hcr
    simpa using this
  have H1 : b * Matrix.GeneralLinearGroup.map σ.toRingHom b ∈
      Subgroup.center (GL (Fin 2) (GaloisField p f)) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, mk_map_eq_pgl2FieldAut σ b, hb]
    exact hleft
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at H1
  obtain ⟨μ, hμ⟩ := H1
  have H2 : ∃ u : (GaloisField p f)ˣ,
      (g * Matrix.GeneralLinearGroup.map ψ.toRingHom b) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) u =
        b * Matrix.GeneralLinearGroup.map σ.toRingHom g := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_mk_iff, map_mul, map_mul, mk_map_eq_pgl2FieldAut ψ b,
      mk_map_eq_pgl2FieldAut σ g, hg, hb]
    exact hcl
  obtain ⟨u, hu⟩ := H2
  have R3 := scalar_relation_GL σ ψ hσσ hψσ hμ.symm hu
  have hpodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have hm : Odd (p ^ k) := hpodd.pow
  have hcard : Nat.card (GaloisField p f) = (p ^ k) ^ 2 := by
    rw [GaloisField.card p f hf, hfk, ← pow_mul, mul_comm]
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  obtain ⟨d, hd⟩ : ∃ d : GaloisField p f,
      d = ((Matrix.GeneralLinearGroup.det g : (GaloisField p f)ˣ) : GaloisField p f) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : GaloisField p f,
      e = ((Matrix.GeneralLinearGroup.det b : (GaloisField p f)ˣ) : GaloisField p f) := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by
    rw [hd]
    exact Units.ne_zero _
  have he0 : e ≠ 0 := by
    rw [he]
    exact Units.ne_zero _
  have hu0 : (u : GaloisField p f) ≠ 0 := Units.ne_zero _
  have D1 : d * ψ e * (u : GaloisField p f) ^ 2 = e * σ d := by
    have h8 := congrArg (fun x : GL (Fin 2) (GaloisField p f) =>
      ((Matrix.GeneralLinearGroup.det x : (GaloisField p f)ˣ) : GaloisField p f)) hu
    simpa [Matrix.GeneralLinearGroup.det_scalar, map_mul, Matrix.GeneralLinearGroup.map_det, hd,
      he] using h8
  have D2 : (μ : GaloisField p f) ^ 2 = e * σ e := by
    have h8 := congrArg (fun x : GL (Fin 2) (GaloisField p f) =>
      ((Matrix.GeneralLinearGroup.det x : (GaloisField p f)ˣ) : GaloisField p f)) hμ
    simpa [Matrix.GeneralLinearGroup.det_scalar, map_mul, Matrix.GeneralLinearGroup.map_det,
      he] using h8
  have R3' : (μ : GaloisField p f) = ψ μ * ((u : GaloisField p f) * σ u) := by
    have := congrArg (fun x : (GaloisField p f)ˣ => (x : GaloisField p f)) R3
    simpa using this
  have hsq : IsSquare d := by
    refine isSquare_of_twisted_norm hm hcard hchar ψ hd0 he0 (inv_ne_zero hu0)
      (μ := (μ : GaloisField p f)) ?_ ?_ ?_
    · have hu2 : (u : GaloisField p f) ^ 2 ≠ 0 := pow_ne_zero _ hu0
      have h1 : d * ψ e * (u : GaloisField p f) ^ 2 = e * d ^ (p ^ k) := by
        rw [← hfrob d]
        exact D1
      field_simp
      linear_combination h1
    · rw [D2, hfrob e, pow_succ']
    · have hum : (u : GaloisField p f) ^ (p ^ k + 1) ≠ 0 := pow_ne_zero _ hu0
      have h3 : (μ : GaloisField p f) = ψ μ * (u : GaloisField p f) ^ (p ^ k + 1) := by
        have h4 := R3'
        rw [hfrob u, ← pow_succ'] at h4
        exact h4
      rw [inv_pow, ← div_eq_inv_mul, eq_div_iff hum]
      exact h3.symm
  rw [← hg, diagPGL_mk, sqHom_eq_one_iff]
  rw [hd] at hsq
  exact hsq

end Comm

end CFSG.ClassicalInvolution.Asc77.C25V
