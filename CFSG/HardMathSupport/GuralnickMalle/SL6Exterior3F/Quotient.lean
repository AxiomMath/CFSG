module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Compare
public import CFSG.HardMathSupport.GuralnickMalle.Prop310

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Open Module

variable {K : Type} [Field K]

@[expose] noncomputable def glNatAct (K : Type) [Field K] :
    GL (Fin 6) K →* Module.End K (Fin 6 → K) where
  toFun a := Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K))
  map_one' := by
    rw [← glNaturalRep_eq_toLin (1 : GL (Fin 6) K), map_one]
  map_mul' a b := by
    rw [← glNaturalRep_eq_toLin (a * b), ← glNaturalRep_eq_toLin a,
      ← glNaturalRep_eq_toLin b, map_mul]

@[simp] theorem glNatAct_apply (a : GL (Fin 6) K) (v : Fin 6 → K) :
    glNatAct K a v = Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) v := rfl

theorem glNatAct_injective (K : Type) [Field K] : Function.Injective (glNatAct K) := by
  intro a b h
  apply Units.ext
  exact Matrix.toLin'.injective h

theorem natCard_span_singleton {V : Type*} [AddCommGroup V] [Module K V] {v : V} (hv : v ≠ 0) :
    Nat.card (Submodule.span K {v}) = Nat.card K := by
  let s : K →ₗ[K] V := LinearMap.toSpanSingleton K V v
  have hs : Function.Injective s := by
    intro c d h
    have hcd : c • v = d • v := h
    have h' : (c - d) • v = 0 := by rw [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hv
  have hrange : Submodule.span K {v} = s.range := by
    ext x
    rw [LinearMap.mem_range, Submodule.mem_span_singleton]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨c, hc⟩⟩
  rw [hrange]
  exact (Nat.card_congr (LinearEquiv.ofInjective s hs).toEquiv).symm

theorem isElemAbelian_range {G H : Type*} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : E →* H) : IsElemAbelian p f.range := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro x y
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : H) * y = y * x
    rw [← ha, ← hb, ← map_mul, ← map_mul, isMulCommutative_iff.mp hE.1 a b]
  · intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    show (f a) ^ p = 1
    rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hE.2 a.1 a.2), map_one]

theorem exists_independent_transvections (K : Type) [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (GL (Fin 6) K)) (hAel : CFSG.Open.IsElemAbelian 2 A)
    {e : Fin 6 → K} (he : e ≠ 0)
    (hfix : ∀ a ∈ A, Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) e = e)
    (hcard : Nat.card K ^ 7 < Nat.card A) :
    ∃ (φ ψ : (Fin 6 → K) →ₗ[K] K) (a b : GL (Fin 6) K),
      a ∈ A ∧ b ∈ A ∧ φ e = 0 ∧ ψ e = 0 ∧
      (∀ c d : K, c • φ + d • ψ = 0 → c = 0 ∧ d = 0) ∧
      Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) = 1 + φ.smulRight e ∧
      Matrix.toLin' ((b : Matrix (Fin 6) (Fin 6) K)) = 1 + ψ.smulRight e := by
  classical
  let s : K →ₗ[K] (Fin 6 → K) := LinearMap.toSpanSingleton K (Fin 6 → K) e
  have hs : Function.Injective s := by
    intro c d h
    have hcd : c • e = d • e := h
    have h' : (c - d) • e = 0 := by rw [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 he
  let L : Submodule K (Fin 6 → K) := s.range
  let E : K ≃ₗ[K] L := LinearEquiv.ofInjective s hs
  let j : L →ₗ[K] K := E.symm.toLinearMap
  let Q := (Fin 6 → K) ⧸ L
  have hpres : ∀ (a : GL (Fin 6) K), a ∈ A → L ≤ Submodule.comap (glNatAct K a) L := by
    intro a ha x hx
    obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx
    show glNatAct K a (s c) ∈ L
    have hsc : s c = c • e := rfl
    rw [hsc, map_smul, glNatAct_apply, hfix a ha]
    exact ⟨c, hsc⟩
  let q (a : ↥A) : Q →ₗ[K] Q :=
    Submodule.mapQ L L (glNatAct K (a : GL (Fin 6) K)) (hpres a.1 a.2)
  have hq_apply (a : ↥A) (v : Fin 6 → K) :
      q a (Submodule.Quotient.mk (p := L) v) =
        Submodule.Quotient.mk (p := L) (glNatAct K (a : GL (Fin 6) K) v) :=
    Submodule.mapQ_apply L L (glNatAct K (a : GL (Fin 6) K)) v
  have q_mul (a b : ↥A) : q (a * b) = q a * q b := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (p := L) x
    rw [hq_apply]
    show Submodule.Quotient.mk (p := L) (glNatAct K ((a * b : ↥A) : GL (Fin 6) K) v) =
      q a (q b (Submodule.Quotient.mk (p := L) v))
    rw [hq_apply, hq_apply]
    congr 1
    rw [show ((a * b : ↥A) : GL (Fin 6) K) = (a : GL (Fin 6) K) * (b : GL (Fin 6) K) from rfl,
      map_mul]
    rfl
  have q_one : q 1 = 1 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (p := L) x
    rw [hq_apply]
    show Submodule.Quotient.mk (p := L) (glNatAct K ((1 : ↥A) : GL (Fin 6) K) v) =
      (1 : Q →ₗ[K] Q) (Submodule.Quotient.mk (p := L) v)
    rw [show ((1 : ↥A) : GL (Fin 6) K) = 1 from rfl, map_one]
    rfl
  let qu (a : ↥A) : LinearMap.GeneralLinearGroup K Q :=
    Units.mk (q a) (q a⁻¹)
      (by rw [← q_mul, mul_inv_cancel, q_one])
      (by rw [← q_mul, inv_mul_cancel, q_one])
  let qhom : ↥A →* LinearMap.GeneralLinearGroup K Q :=
    { toFun := qu
      map_one' := by
        apply Units.ext
        exact q_one
      map_mul' := by
        intro a b
        apply Units.ext
        exact q_mul a b }
  have qhom_apply (a : ↥A) :
      ((qhom a : LinearMap.GeneralLinearGroup K Q) : Q →ₗ[K] Q) = q a := rfl
  have hker (a : ↥A) (ha : qhom a = 1) (v : Fin 6 → K) :
      (glNatAct K (a : GL (Fin 6) K) - 1) v ∈ L := by
    have hq : q a = 1 := by
      have h : ((qhom a : LinearMap.GeneralLinearGroup K Q) : Q →ₗ[K] Q) = 1 := by
        rw [ha]
        rfl
      rwa [qhom_apply] at h
    have hmk : Submodule.Quotient.mk (p := L) (glNatAct K (a : GL (Fin 6) K) v) =
        Submodule.Quotient.mk (p := L) v := by
      have h := congrArg (fun f : Q →ₗ[K] Q => f (Submodule.Quotient.mk (p := L) v)) hq
      simpa [hq_apply] using h
    have h' : glNatAct K (a : GL (Fin 6) K) v - v ∈ L :=
      (Submodule.Quotient.eq L).mp hmk
    simpa [LinearMap.sub_apply] using h'
  let phi (a : ↥A) (ha : qhom a = 1) : (Fin 6 → K) →ₗ[K] K :=
    j ∘ₗ (glNatAct K (a : GL (Fin 6) K) - 1).codRestrict L (hker a ha)
  have phi_smul (a : ↥A) (ha : qhom a = 1) (v : Fin 6 → K) :
      (phi a ha v) • e = (glNatAct K (a : GL (Fin 6) K) - 1) v := by
    have h1 : E (phi a ha v) = (⟨(glNatAct K (a : GL (Fin 6) K) - 1) v, hker a ha v⟩ : L) := by
      show E (E.symm (⟨(glNatAct K (a : GL (Fin 6) K) - 1) v, hker a ha v⟩ : L)) = _
      rw [LinearEquiv.apply_symm_apply]
    have h2 : ((E (phi a ha v) : L) : Fin 6 → K) = s (phi a ha v) := rfl
    have h3 : s (phi a ha v) = (phi a ha v) • e := rfl
    have h4 := congrArg (fun x : L => (x : Fin 6 → K)) h1
    rw [h2, h3] at h4
    exact h4
  have phi_e (a : ↥A) (ha : qhom a = 1) : phi a ha e = 0 := by
    have hzero : (glNatAct K (a : GL (Fin 6) K) - 1) e = 0 := by
      rw [LinearMap.sub_apply, glNatAct_apply, hfix a.1 a.2, Module.End.one_apply, sub_self]
    have h := phi_smul a ha e
    rw [hzero, smul_eq_zero] at h
    exact h.resolve_right he
  have phi_spec (a : ↥A) (ha : qhom a = 1) :
      glNatAct K (a : GL (Fin 6) K) = 1 + (phi a ha).smulRight e := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.add_apply, LinearMap.smulRight_apply, phi_smul a ha v,
      LinearMap.sub_apply, Module.End.one_apply]
    abel
  have hQrank : finrank K Q = 5 := by
    have hL1 : finrank K L = 1 := by
      rw [← E.finrank_eq]
      exact finrank_self K
    have h := Submodule.finrank_quotient (R := K) (M := Fin 6 → K) (S := K) L
    rw [Module.finrank_fin_fun, hL1] at h
    omega
  obtain ⟨eQ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (R := K) (M := Q) (M' := Fin 5 → K) (by rw [hQrank, Module.finrank_fin_fun])
  let iso : LinearMap.GeneralLinearGroup K Q ≃* GL (Fin 5) K :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv eQ).trans
      (Matrix.GeneralLinearGroup.toLin (n := Fin 5) (R := K)).symm
  let D : Subgroup (GL (Fin 5) K) := qhom.range.map iso.toMonoidHom
  have hDcard : Nat.card D = Nat.card qhom.range :=
    Subgroup.card_map_of_injective (f := iso.toMonoidHom) iso.injective
  have hDel : IsElemAbelian 2 D := (isElemAbelian_range hAel qhom).map iso.toMonoidHom
  have hDbound : Nat.card D ≤ Nat.card K ^ 6 := by
    have h := card_le_pow_half_sq (K := K) (n := 5) (p := 2) Nat.prime_two hDel
    rwa [show (5 : ℕ) ^ 2 / 4 = 6 from by decide] at h
  have hDle : Nat.card qhom.range ≤ Nat.card K ^ 6 := by
    rw [← hDcard]
    exact hDbound
  have hAdecomp : Nat.card ↥A = Nat.card ↥qhom.ker * Nat.card ↥qhom.range :=
    (Subgroup.card_ker_mul_card_range qhom).symm
  have hBcard : Nat.card K < Nat.card ↥qhom.ker := by
    by_contra hcon
    have hcon' : Nat.card ↥qhom.ker ≤ Nat.card K := Nat.le_of_not_lt hcon
    have hle : Nat.card ↥qhom.ker * Nat.card ↥qhom.range ≤
        Nat.card K * Nat.card K ^ 6 := Nat.mul_le_mul hcon' hDle
    have hpow : Nat.card K * Nat.card K ^ 6 = Nat.card K ^ 7 := by ring
    rw [hpow] at hle
    rw [hAdecomp] at hcard
    exact absurd hcard (not_lt.mpr hle)
  let Phi : ↥qhom.ker → ((Fin 6 → K) →ₗ[K] K) :=
    fun x => phi x.1 (MonoidHom.mem_ker.mp x.2)
  have Phi_inj : Function.Injective Phi := by
    intro x y hxy
    have hgl : glNatAct K ((x.1 : ↥A) : GL (Fin 6) K) =
        glNatAct K ((y.1 : ↥A) : GL (Fin 6) K) := by
      have hphieq : phi x.1 (MonoidHom.mem_ker.mp x.2) = phi y.1 (MonoidHom.mem_ker.mp y.2) := hxy
      rw [phi_spec x.1 (MonoidHom.mem_ker.mp x.2),
        phi_spec y.1 (MonoidHom.mem_ker.mp y.2), hphieq]
    have h1 : ((x.1 : ↥A) : GL (Fin 6) K) = ((y.1 : ↥A) : GL (Fin 6) K) :=
      glNatAct_injective K hgl
    exact Subtype.ext (Subtype.ext h1)
  have hDualFin : Finite ((Fin 6 → K) →ₗ[K] K) :=
    Finite.of_injective (fun f : (Fin 6 → K) →ₗ[K] K => (f : (Fin 6 → K) → K))
      (fun f g h => LinearMap.ext (congrFun h))
  have key : ∃ x y : ↥qhom.ker,
      ∀ c d : K, c • Phi x + d • Phi y = 0 → c = 0 ∧ d = 0 := by
    have : Nonempty ↥qhom.ker := ⟨1⟩
    have hntriv : ∃ x : ↥qhom.ker, Phi x ≠ 0 := by
      by_contra h0
      push Not at h0
      have hsingle : Subsingleton ↥qhom.ker :=
        ⟨fun x y => Phi_inj (by rw [h0 x, h0 y])⟩
      have := hsingle
      have h1 : Nat.card ↥qhom.ker = 1 := Nat.card_unique
      rw [h1] at hBcard
      exact absurd hBcard (not_lt.mpr (Nat.card_pos (α := K)))
    obtain ⟨x₀, hx₀⟩ := hntriv
    have hnotmem : ∃ y : ↥qhom.ker, Phi y ∉ Submodule.span K {Phi x₀} := by
      by_contra h
      push Not at h
      have hinj : Function.Injective
          (fun x : ↥qhom.ker => (⟨Phi x, h x⟩ : Submodule.span K {Phi x₀})) := by
        intro x y hxy
        exact Phi_inj (Subtype.ext_iff.mp hxy)
      have hle := Nat.card_le_card_of_injective _ hinj
      rw [natCard_span_singleton hx₀] at hle
      exact absurd hBcard (not_lt.mpr hle)
    obtain ⟨y, hy⟩ := hnotmem
    refine ⟨x₀, y, fun c d hcd => ?_⟩
    have hd0 : d = 0 := by
      by_contra hd
      apply hy
      have h2 : d • Phi y = -(c • Phi x₀) := eq_neg_of_add_eq_zero_right hcd
      have h4 : Phi y = d⁻¹ • (-(c • Phi x₀)) := by
        rw [← h2, smul_smul, inv_mul_cancel₀ hd, one_smul]
      have h3 : Phi y = (-(d⁻¹ * c)) • Phi x₀ := by
        rw [h4]
        module
      rw [h3]
      exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    subst hd0
    rw [zero_smul, add_zero] at hcd
    exact ⟨(smul_eq_zero.mp hcd).resolve_right hx₀, rfl⟩
  obtain ⟨x, y, hxy⟩ := key
  exact ⟨Phi x, Phi y, ((x.1 : ↥A) : GL (Fin 6) K), ((y.1 : ↥A) : GL (Fin 6) K),
    x.1.2, y.1.2,
    phi_e x.1 (MonoidHom.mem_ker.mp x.2), phi_e y.1 (MonoidHom.mem_ker.mp y.2),
    hxy,
    phi_spec x.1 (MonoidHom.mem_ker.mp x.2), phi_spec y.1 (MonoidHom.mem_ker.mp y.2)⟩

end CFSG.HardMathSupport.GuralnickMalle
