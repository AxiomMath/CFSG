module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup GorensteinWalter CatalogueSchreierLinearTwo AutL2Facts

@[expose] def HasOuterChar (Y : Type*) [Group Y] : Prop :=
  ∃ (m : ℕ) (ψ : MulAut Y →* Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m))),
    (∀ y, ψ (MulAut.conj y) = 1) ∧
      ∀ σ : MulAut Y, (∃ k : ℕ, σ ^ 2 ^ k = 1) → ψ σ = 1 →
        σ ∈ (MulAut.conj : Y →* MulAut Y).range

theorem HasOuterChar.of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : HasOuterChar Y') : HasOuterChar Y := by
  obtain ⟨m, ψ, hinn, hker⟩ := h
  refine ⟨m, ψ.comp (MulAut.congr e).toMonoidHom, fun y => ?_, fun σ hσ hψ => ?_⟩
  · have : MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
      ext x
      simp [MulAut.congr_apply, MulAut.conj_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, this]
    exact hinn (e y)
  · obtain ⟨k, hk⟩ := hσ
    obtain ⟨y', hy'⟩ := hker (MulAut.congr e σ) ⟨k, by rw [← map_pow, hk, map_one]⟩ hψ
    refine ⟨e.symm y', ?_⟩
    apply (MulAut.congr e).injective
    rw [← hy']
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem zmod2_eq_of_iff {a b : Multiplicative (ZMod 2)} (h : a = 1 ↔ b = 1) : a = b := by
  revert a b
  decide

@[expose] noncomputable def signZ2 (n : ℕ) : Equiv.Perm (Fin n) →* Multiplicative (ZMod 2) :=
  (mulEquivOfPrimeCardEq (p := 2) (G := ℤˣ) (G' := Multiplicative (ZMod 2))
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units_int])
    (by rw [Nat.card_eq_fintype_card]; rfl)).toMonoidHom.comp Equiv.Perm.sign

theorem signZ2_eq_one_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    signZ2 n π = 1 ↔ π ∈ alternatingGroup (Fin n) := by
  rw [signZ2, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, Equiv.Perm.mem_alternatingGroup]

theorem hasOuterChar_alt7 : HasOuterChar (alternatingGroup (Fin 7)) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let E := MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
    Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7))) hbij
  have hE : ∀ y : alternatingGroup (Fin 7), E (y : Equiv.Perm (Fin 7)) = MulAut.conj y := by
    intro y
    ext x
    simp [E, MulAut.conjNormal_apply, MulAut.conj_apply]
  refine ⟨0, (signZ2 7).prod 1 |>.comp E.symm.toMonoidHom, fun y => ?_, fun σ _ hσ => ?_⟩
  · have : E.symm (MulAut.conj y) = y := by rw [← hE, MulEquiv.symm_apply_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, this,
      MonoidHom.prod_apply, MonoidHom.one_apply]
    rw [(signZ2_eq_one_iff _).2 y.2]
    rfl
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MonoidHom.prod_apply, Prod.mk_eq_one, MonoidHom.one_apply, and_true] at hσ
    have hA := (signZ2_eq_one_iff _).1 hσ
    refine ⟨⟨E.symm σ, hA⟩, ?_⟩
    rw [← hE]
    exact E.apply_symm_apply σ

section PSL2

variable (F : Type) [Field F] [Finite F]

abbrev pslLayer : Subgroup (PGL2 F) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range

variable {F}

theorem pslLayer_index (hF : IsOddPrimePower (Nat.card F)) : (pslLayer F).index = 2 :=
  pgl2_psl2Range_index_eq_two F hF

@[expose] noncomputable def chiPGL (hF : IsOddPrimePower (Nat.card F)) :
    PGL2 F →* Multiplicative (ZMod 2) :=
  haveI := normal_of_index_eq_two (pslLayer_index hF)
  (mulEquivOfPrimeCardEq (p := 2) (by rw [← index_eq_card, pslLayer_index hF])
    (by rw [Nat.card_eq_fintype_card]; rfl)).toMonoidHom.comp (QuotientGroup.mk' (pslLayer F))

theorem chiPGL_eq_one_iff (hF : IsOddPrimePower (Nat.card F)) (x : PGL2 F) :
    chiPGL hF x = 1 ↔ x ∈ pslLayer F := by
  have := normal_of_index_eq_two (pslLayer_index hF)
  rw [chiPGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite F] in
theorem pgl2FieldAut_mem_pslLayer (σ : F ≃+* F) {x : PGL2 F} (hx : x ∈ pslLayer F) :
    pgl2FieldAut F σ x ∈ pslLayer F := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨psl2FieldAut F σ y, psl2FieldAut_toPGL σ y⟩

theorem chiPGL_fieldAut (hF : IsOddPrimePower (Nat.card F)) (σ : F ≃+* F) (x : PGL2 F) :
    chiPGL hF (pgl2FieldAut F σ x) = chiPGL hF x := by
  refine zmod2_eq_of_iff ?_
  rw [chiPGL_eq_one_iff, chiPGL_eq_one_iff]
  refine ⟨fun h => ?_, pgl2FieldAut_mem_pslLayer σ⟩
  have h2 := pgl2FieldAut_mem_pslLayer σ⁻¹ h
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2

@[expose] noncomputable def deltaPGL (hF : IsOddPrimePower (Nat.card F)) :
    PGammaL2 F →* Multiplicative (ZMod 2) :=
  SemidirectProduct.lift (chiPGL hF) 1 fun σ => by
    ext x
    simp [chiPGL_fieldAut]

theorem deltaPGL_inl (hF : IsOddPrimePower (Nat.card F)) (x : PGL2 F) :
    deltaPGL hF (SemidirectProduct.inl x) = chiPGL hF x := by
  simp [deltaPGL]

theorem zmod_eq_zero_of_two_pow {f k : ℕ} (hf : 0 < f) (x : ZMod f)
    (hk : (2 ^ k : ℕ) • x = 0)
    (h2 : ZMod.castHom (Nat.ordProj_dvd f 2) (ZMod (2 ^ f.factorization 2)) x = 0) : x = 0 := by
  have : NeZero f := ⟨hf.ne'⟩
  have hff := Nat.ordProj_mul_ordCompl_eq_self f 2
  have hodd : ¬ 2 ∣ f / 2 ^ f.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hf.ne'
  have hcop : Nat.Coprime 2 (f / 2 ^ f.factorization 2) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  rw [← ZMod.natCast_zmod_val x] at hk h2 ⊢
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hk
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at h2
  rw [ZMod.natCast_eq_zero_iff]
  have h1 : f / 2 ^ f.factorization 2 ∣ x.val := by
    have : f / 2 ^ f.factorization 2 ∣ 2 ^ k * x.val := (Dvd.intro_left _ hff).trans hk
    exact (Nat.Coprime.pow_left k hcop).symm.dvd_of_dvd_mul_left this
  have h3 : 2 ^ f.factorization 2 * (f / 2 ^ f.factorization 2) ∣ x.val :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hcop) h2 h1
  rwa [hff] at h3

variable (F) in
@[expose] noncomputable def ringAutZMod {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hf : 1 ≤ f) : (F ≃+* F) ≃* Multiplicative (ZMod f) :=
  haveI := isCyclic_ringAut F
  haveI : NeZero f := ⟨by omega⟩
  mulEquivOfCyclicCardEq (by rw [card_ringAut F hp hF, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card])

@[expose] noncomputable def epsPGL {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hf : 1 ≤ f) : PGammaL2 F →* Multiplicative (ZMod (2 ^ f.factorization 2)) :=
  (AddMonoidHom.toMultiplicative (ZMod.castHom (Nat.ordProj_dvd f 2)
    (ZMod (2 ^ f.factorization 2))).toAddMonoidHom).comp
      ((ringAutZMod F hp hF hf).toMonoidHom.comp SemidirectProduct.rightHom)

theorem hasOuterChar_psl2 (hF : IsOddPrimePower (Nat.card F)) : HasOuterChar (PSL2 F) := by
  obtain ⟨p, f, hp, hpo, hf, hcard⟩ := hF
  have hF' : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpo, hf, hcard⟩
  have hincl : ∀ y : PSL2 F, (semilinearEquivAut F).symm (MulAut.conj y) = incl F y := by
    intro y
    rw [MulEquiv.symm_apply_eq]
    exact (semilinearAction_incl F y).symm
  refine ⟨f.factorization 2, ((deltaPGL hF').prod (epsPGL hp hcard hf)).comp
    (semilinearEquivAut F).symm.toMonoidHom, fun y => ?_, fun σ hσ hψ => ?_⟩
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hincl,
      MonoidHom.prod_apply]
    refine Prod.ext ?_ ?_
    · rw [incl_apply, deltaPGL_inl, (chiPGL_eq_one_iff hF' _).2 ⟨y, rfl⟩]
      rfl
    · simp [epsPGL, incl_apply]
  · obtain ⟨k, hk⟩ := hσ
    set g := (semilinearEquivAut F).symm σ with hg
    have hgk : g ^ 2 ^ k = 1 := by rw [hg, ← map_pow, hk, map_one]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, ← hg,
      MonoidHom.prod_apply, Prod.mk_eq_one] at hψ
    obtain ⟨hδ, hε⟩ := hψ
    have hrk : g.right ^ 2 ^ k = 1 := by
      rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, hgk, map_one]
    have hright : g.right = 1 := by
      have hx0 : Multiplicative.toAdd (ringAutZMod F hp hcard hf g.right) = 0 := by
        refine zmod_eq_zero_of_two_pow (k := k) (by omega) _ ?_ ?_
        · rw [← toAdd_pow, ← map_pow, hrk, map_one, toAdd_one]
        · have h2 := congrArg Multiplicative.toAdd hε
          simpa [epsPGL] using h2
      have h3 : ringAutZMod F hp hcard hf g.right = 1 := by
        rw [← ofAdd_toAdd (ringAutZMod F hp hcard hf g.right), hx0, ofAdd_zero]
      exact (ringAutZMod F hp hcard hf).map_eq_one_iff.1 h3
    have hgl : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hright
    rw [hgl, deltaPGL_inl, chiPGL_eq_one_iff] at hδ
    obtain ⟨y, hy⟩ := hδ
    refine ⟨y, (semilinearEquivAut F).symm.injective ?_⟩
    rw [hincl, ← hg, hgl, incl_apply, hy]

end PSL2

end CFSG.ComponentClassification.CatFactsSmall
