module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_unit_mul_self (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> decide

private lemma aux_eq_mul_of_eq_mul {a b c d : ℤˣ} (h : a = b * c * d)
    (hc : c * c = 1) (hd : d * d = 1) : b = a * c * d := by
  rw [h, mul_assoc (b * c * d) c d]
  rw [mul_mul_mul_comm, mul_assoc b c c, hc, mul_one, hd, mul_one]

private lemma aux_units_identity (b a c : ℤˣ) (ha : a * a = 1) (hc : c * c = 1) :
    a * (b * a * c) * c = b := by
  have key : (b * a * c) * (a * c) = b := by
    rw [mul_mul_mul_comm, mul_assoc b a a, ha, mul_one, hc, mul_one]
  have hrearr : a * (b * a * c) * c = (b * a * c) * (a * c) := by
    rw [mul_comm a (b * a * c), mul_assoc]
  rw [hrearr, key]

private lemma aux_map_eq_of_agrees {N N' : Submodule (ZMod 3) V}
    (f : N ≃ₗ[ZMod 3] N') (g : V ≃ₗ[ZMod 3] V)
    (hg : ∀ x : N, g (x : V) = (f x : V)) :
    N.map (g : V →ₗ[ZMod 3] V) = N' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : (f ⟨x, hx⟩ : V) ∈ N' := (f ⟨x, hx⟩).2
    have h : (f ⟨x, hx⟩ : V) = g x := by
      simpa only [Subtype.coe_mk] using (hg ⟨x, hx⟩).symm
    rw [h] at hmem
    exact hmem
  · intro hy
    refine ⟨(f.symm ⟨y, hy⟩ : N), (f.symm ⟨y, hy⟩).2, ?_⟩
    exact (hg (f.symm ⟨y, hy⟩)).trans (by simp)

private lemma aux_conj_mul_self {G : Type*} [Group G] {g s : G} (hs : s * s = 1) :
    (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
  simp only [mul_assoc]
  rw [← mul_assoc g⁻¹ g (s * g⁻¹), inv_mul_cancel, one_mul]
  rw [← mul_assoc s s g⁻¹, hs, one_mul, mul_inv_cancel]

private noncomputable def aux_restrictTopEquiv :
    (Q.restrict (⊤ : Submodule (ZMod 3) V)).IsometryEquiv Q where
  toLinearEquiv := Submodule.topEquiv
  map_app' := fun _ => rfl

@[expose] noncomputable def piOrth (Q : QuadraticForm (ZMod 3) V) : OGroup Q :=
  QuadraticMap.negOrthogonal Q

@[expose] noncomputable def invDim (t : OGroup Q) : ℕ :=
  Module.finrank (ZMod 3) (commSp t)

@[expose] noncomputable def invSign (t : OGroup Q) : ℤˣ :=
  quadSign (Q.restrict (commSp t))

@[expose] noncomputable def invType (t : OGroup Q) : ℕ × ℤˣ := (invDim t, invSign t)

theorem piOrth_mul_self : piOrth Q * piOrth Q = 1 := by
  exact QuadraticMap.negOrthogonal_mul_self Q

theorem coe_piOrth_apply (v : V) : (piOrth Q : V ≃ₗ[ZMod 3] V) v = -v := by
  change (QuadraticMap.negOrthogonal Q : V ≃ₗ[ZMod 3] V) v = -v
  rw [QuadraticMap.coe_negOrthogonal]
  exact LinearEquiv.neg_apply v

theorem commSp_one : commSp (1 : OGroup Q) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨u, hu⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hv
  simpa using hu.symm

theorem commSp_piOrth : commSp (piOrth Q) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [mem_commSp_iff piOrth_mul_self, coe_piOrth_apply]

theorem invType_one : invType (1 : OGroup Q) = (0, 1) := by
  simp only [invType]
  apply Prod.ext
  · simp only [invDim]
    rw [commSp_one, finrank_bot]
  · simp only [invSign]
    have hbot : quadSign (Q.restrict (commSp (1 : OGroup Q))) =
        quadSign (Q.restrict (⊥ : Submodule (ZMod 3) V)) :=
      congrArg (fun M => quadSign (Q.restrict M)) commSp_one
    rw [hbot]
    haveI : Subsingleton (⊥ : Submodule (ZMod 3) V) := by
      rw [Submodule.subsingleton_iff_eq_bot]
    exact quadSign_of_subsingleton _

theorem invType_piOrth (hQ : Q.Nondegenerate) :
    invType (piOrth Q) = (Module.finrank (ZMod 3) V, quadSign Q) := by
  have hnd : (Q.restrict (⊤ : Submodule (ZMod 3) V)).Nondegenerate :=
    (aux_restrictTopEquiv (Q := Q)).nondegenerate_iff.mpr hQ
  have hsign : quadSign (Q.restrict (⊤ : Submodule (ZMod 3) V)) = quadSign Q :=
    quadSign_congr hnd ⟨aux_restrictTopEquiv (Q := Q)⟩
  have hsignTop : quadSign (Q.restrict (commSp (piOrth Q))) =
      quadSign (Q.restrict (⊤ : Submodule (ZMod 3) V)) :=
    congrArg (fun M => quadSign (Q.restrict M)) commSp_piOrth
  have hfinTop : invDim (piOrth Q) = Module.finrank (ZMod 3) V := by
    simp only [invDim]
    rw [commSp_piOrth, finrank_top]
  simp only [invType]
  apply Prod.ext
  · exact hfinTop
  · simp only [invSign]
    rw [hsignTop, hsign]

theorem invDim_le (t : OGroup Q) : invDim t ≤ Module.finrank (ZMod 3) V :=
  Submodule.finrank_le (commSp t)

theorem invDim_eq_zero_iff {t : OGroup Q} (htt : t * t = 1) : invDim t = 0 ↔ t = 1 := by
  simp only [invDim]
  rw [Submodule.finrank_eq_zero]
  exact commSp_eq_bot_iff htt

theorem invDim_eq_finrank_iff {t : OGroup Q} (htt : t * t = 1) :
    invDim t = Module.finrank (ZMod 3) V ↔ t = piOrth Q := by
  constructor
  · intro h
    have htop : commSp t = ⊤ := Submodule.eq_top_of_finrank_eq h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ commSp t := by rw [htop]; trivial
    have hvv := (mem_commSp_iff htt).mp hv
    rw [hvv, coe_piOrth_apply]
  · intro h
    rw [h]
    simp only [invDim]
    rw [commSp_piOrth, finrank_top]

theorem quadSign_fixSp_eq (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    quadSign (Q.restrict (fixSp t)) =
      quadSign Q * invSign t *
        (-1) ^ (invDim t * (Module.finrank (ZMod 3) V - invDim t)) := by
  have hmain := quadSign_eq_fixSp_commSp hQ htt
  have hdF : Module.finrank (ZMod 3) (fixSp t) =
      Module.finrank (ZMod 3) V - invDim t := by
    have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) t
    simp only [invDim] at hsum ⊢
    omega
  have hsqC : invSign t * invSign t = 1 := aux_unit_mul_self _
  have hpow : ((-1 : ℤˣ) ^ (Module.finrank (ZMod 3) (fixSp t) * invDim t)) *
      ((-1 : ℤˣ) ^ (Module.finrank (ZMod 3) (fixSp t) * invDim t)) = 1 :=
    aux_unit_mul_self _
  have hs : quadSign (Q.restrict (fixSp t)) = quadSign Q * invSign t *
      (-1 : ℤˣ) ^ (Module.finrank (ZMod 3) (fixSp t) * invDim t) :=
    aux_eq_mul_of_eq_mul hmain hsqC hpow
  rw [hs, hdF, Nat.mul_comm (Module.finrank (ZMod 3) V - invDim t) (invDim t)]

theorem invType_conj (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) (g : OGroup Q) :
    invType (g * t * g⁻¹) = invType t := by
  simp only [invType]
  apply Prod.ext
  · simp only [invDim]
    rw [commSp_conj, LinearEquiv.finrank_map_eq]
  · simp only [invSign]
    exact (quadSign_congr (nondegenerate_restrict_commSp hQ htt)
      (equivalent_restrict_commSp_conj g t)).symm

theorem isConj_of_invType_eq (hQ : Q.Nondegenerate) {s t : OGroup Q} (hs : s * s = 1)
    (ht : t * t = 1) (h : invType s = invType t) : IsConj s t := by
  have hdim : Module.finrank (ZMod 3) (commSp s) = Module.finrank (ZMod 3) (commSp t) := by
    have h2 := congrArg Prod.fst h
    simpa only [invType, invDim] using h2
  have hsign : quadSign (Q.restrict (commSp s)) = quadSign (Q.restrict (commSp t)) := by
    have h2 := congrArg Prod.snd h
    simpa only [invType, invSign] using h2
  obtain ⟨f⟩ := equivalent_of_quadSign_eq (nondegenerate_restrict_commSp hQ hs)
    (nondegenerate_restrict_commSp hQ ht) hdim hsign
  obtain ⟨e, he⟩ := f.exists_extension (nondegenerate_restrict_commSp hQ hs)
  let g : OGroup Q := (TauCeti.QuadraticMap.orthogonalGroupEquivIsometryEquiv Q).symm e
  have hg : ∀ x : commSp s, (g : V ≃ₗ[ZMod 3] V) (x : V) = (f x : V) := by
    intro x
    have h1 : (g : V ≃ₗ[ZMod 3] V) (x : V) = e (x : V) := by
      simp only [g, TauCeti.QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv_symm]
    rw [h1, he x]
  have hcomm : commSp (g * s * g⁻¹) = commSp t := by
    rw [commSp_conj]
    exact aux_map_eq_of_agrees (f : commSp s ≃ₗ[ZMod 3] commSp t)
      (g : V ≃ₗ[ZMod 3] V) hg
  have hgg : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := aux_conj_mul_self hs
  have hgt : g * s * g⁻¹ = t := eq_of_commSp_eq hQ hgg ht hcomm
  rw [isConj_iff]
  exact ⟨g, hgt⟩

theorem isConj_iff_invType_eq (hQ : Q.Nondegenerate) {s t : OGroup Q} (hs : s * s = 1)
    (ht : t * t = 1) : IsConj s t ↔ invType s = invType t := by
  constructor
  · intro h
    rw [isConj_iff] at h
    obtain ⟨g, hg⟩ := h
    rw [← hg]
    exact (invType_conj hQ hs g).symm
  · exact isConj_of_invType_eq hQ hs ht

theorem exists_involution_of_type (hQ : Q.Nondegenerate) (r : ℕ) (α : ℤˣ) :
    (∃ t : OGroup Q, t * t = 1 ∧ invType t = (r, α)) ↔
      r ≤ Module.finrank (ZMod 3) V ∧ (r = 0 → α = 1) ∧
        (r = Module.finrank (ZMod 3) V → α = quadSign Q) := by
  constructor
  · rintro ⟨t, htt, htype⟩
    have h1 : invDim t = r := by
      simpa only [invType, invDim] using congrArg Prod.fst htype
    refine ⟨?_, ?_, ?_⟩
    · calc r = invDim t := h1.symm
        _ ≤ Module.finrank (ZMod 3) V := invDim_le t
    · intro hr
      have h0 : invDim t = 0 := by rw [h1, hr]
      have ht1 : t = 1 := (invDim_eq_zero_iff htt).mp h0
      have h2 : invType t = (0, (1 : ℤˣ)) := by rw [ht1, invType_one]
      rw [h2, hr] at htype
      have : (1 : ℤˣ) = α := by simpa using htype
      exact this.symm
    · intro hn'
      have hd : invDim t = Module.finrank (ZMod 3) V := by rw [h1, hn']
      have htpi : t = piOrth Q := (invDim_eq_finrank_iff htt).mp hd
      have h2 : invType t = (Module.finrank (ZMod 3) V, quadSign Q) := by
        rw [htpi, invType_piOrth hQ]
      rw [h2, hn'] at htype
      have : quadSign Q = α := by simpa using htype
      exact this.symm
  · rintro ⟨hr, h0, hnr⟩
    set n := Module.finrank (ZMod 3) V with hn
    obtain ⟨w, hw⟩ := exists_weights_of_sign r α h0
    obtain ⟨w', hw'⟩ := exists_weights_of_sign (n - r)
      (quadSign Q * α * (-1) ^ (r * (n - r))) (by
        intro hzero
        have hr' : r = n := by omega
        have hα : α = quadSign Q := hnr hr'
        rw [hα, hzero, mul_zero, pow_zero, mul_one]
        exact aux_unit_mul_self _)
    have hs1 : quadSign (TauCeti.presentedForm ⟨r, w⟩) = α := by
      rw [quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
        TauCeti.formClass_presentedForm, signOf_mk_diag]
      exact hw
    have hs2 : quadSign (TauCeti.presentedForm ⟨n - r, w'⟩) =
        quadSign Q * α * (-1) ^ (r * (n - r)) := by
      rw [quadSign_eq_signOf _ (TauCeti.nondegenerate_presentedForm _),
        TauCeti.formClass_presentedForm, signOf_mk_diag]
      exact hw'
    have hPnd : ((TauCeti.presentedForm ⟨r, w⟩).prod
        (TauCeti.presentedForm ⟨n - r, w'⟩)).Nondegenerate :=
      (TauCeti.nondegenerate_presentedForm _).prod (TauCeti.nondegenerate_presentedForm _)
    have hPdim : Module.finrank (ZMod 3) ((Fin r → ZMod 3) × (Fin (n - r) → ZMod 3)) = n := by
      simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      omega
    have hPsign : quadSign ((TauCeti.presentedForm ⟨r, w⟩).prod
        (TauCeti.presentedForm ⟨n - r, w'⟩)) = quadSign Q := by
      rw [quadSign_prod (TauCeti.nondegenerate_presentedForm _)
        (TauCeti.nondegenerate_presentedForm _)]
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hs1, hs2]
      exact aux_units_identity (quadSign Q) α ((-1 : ℤˣ) ^ (r * (n - r)))
        (aux_unit_mul_self α) (aux_unit_mul_self _)
    obtain ⟨e⟩ := equivalent_of_quadSign_eq hPnd hQ (by rw [hPdim, hn]) hPsign
    let f : (Fin r → ZMod 3) →ₗ[ZMod 3] V :=
      e.toLinearMap.comp (LinearMap.inl (ZMod 3) (Fin r → ZMod 3) (Fin (n - r) → ZMod 3))
    have hfapply : ∀ x, f x = e (x, 0) := by
      intro x
      simp [f]
    have hinj : Function.Injective f := by
      intro x y hxy
      rw [hfapply x, hfapply y] at hxy
      have := e.injective hxy
      simpa using this
    let N : Submodule (ZMod 3) V := LinearMap.range f
    let isoA : (TauCeti.presentedForm ⟨r, w⟩).IsometryEquiv (Q.restrict N) :=
      { toLinearEquiv := LinearEquiv.ofInjective f hinj
        map_app' := by
          intro x
          change Q (f x) = (TauCeti.presentedForm ⟨r, w⟩) x
          rw [hfapply x, e.map_app]
          simp [QuadraticMap.prod_apply] }
    have hNnd : (Q.restrict N).Nondegenerate :=
      isoA.nondegenerate_iff.mp (TauCeti.nondegenerate_presentedForm ⟨r, w⟩)
    have hNdim : Module.finrank (ZMod 3) N = r := by
      have hfin := isoA.toLinearEquiv.finrank_eq
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfin
      exact hfin.symm
    have hNsign : quadSign (Q.restrict N) = α := by
      have hqc := quadSign_congr (TauCeti.nondegenerate_presentedForm ⟨r, w⟩) ⟨isoA⟩
      rw [hs1] at hqc
      exact hqc.symm
    obtain ⟨t, htt, hcomm⟩ := exists_involution_of_commSp hQ hNnd
    refine ⟨t, htt, ?_⟩
    have hdim' : invDim t = r := by
      change Module.finrank (ZMod 3) (commSp t) = r
      rw [hcomm, hNdim]
    have hsign' : invSign t = α := by
      change quadSign (Q.restrict (commSp t)) = α
      exact Eq.mpr (congrArg (fun M => quadSign (Q.restrict M) = α) hcomm) hNsign
    simp only [invType]
    rw [hdim', hsign']

end CFSG.OddStandard.SmallF3.Omega
