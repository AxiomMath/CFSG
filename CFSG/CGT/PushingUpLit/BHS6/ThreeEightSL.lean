module

public import CFSG.CGT.PushingUpLit.BHS6.ThreeEightAlt

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

section Transport

variable {F K : Type} [Field F] [Field K]

@[expose] def slEquiv (e : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by
      ext A i j
      exact e.symm_apply_apply _)
    (by
      ext A i j
      exact e.apply_symm_apply _)

@[expose] def vecEquiv (e : F ≃+* K) : Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → K) :=
  (AddEquiv.piCongrRight fun _ : Fin 2 => e.toAddEquiv).toMultiplicative

theorem toAdd_vecEquiv (e : F ≃+* K) (v : Multiplicative (Fin 2 → F)) (i : Fin 2) :
    Multiplicative.toAdd (vecEquiv e v) i = e (Multiplicative.toAdd v i) := rfl

theorem toAdd_vecEquiv_mulVec (e : F ≃+* K) (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Multiplicative (Fin 2 → F)) :
    Multiplicative.toAdd (vecEquiv e (Multiplicative.ofAdd
      ((A : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd v)))) =
      ((slEquiv e A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (vecEquiv e v)) := by
  funext i
  rw [toAdd_vecEquiv]
  exact RingHom.map_mulVec e.toRingHom (A : Matrix (Fin 2) (Fin 2) F) (Multiplicative.toAdd v) i

end Transport

@[expose] def IsLin2TypeGF (E : Subgroup Γ) (n : ℕ) : Prop :=
  ∃ α : ↥E →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
    Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥E ∧
    ∃ β : ↥(CFSG.QuasithinUnique.blockU E) →* Multiplicative (Fin 2 → GaloisField 2 n),
      Function.Surjective β ∧
      β.ker = (CFSG.QuasithinUnique.blockZ E).subgroupOf (CFSG.QuasithinUnique.blockU E) ∧
      ∀ ℓ : ↥E, ∀ u v : ↥(CFSG.QuasithinUnique.blockU E), (v : Γ) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (β v) =
          (α ℓ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (β u))

theorem isLin2TypeGF_of_isLin2Type {E : Subgroup Γ} {n : ℕ} (hn : n ≠ 0)
    (h : IsLin2Type E n) : IsLin2TypeGF E n := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcardK : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n hn
  let e : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (hcard.trans hcardK.symm)
  refine ⟨(slEquiv e).toMonoidHom.comp α, (slEquiv e).surjective.comp hαs, ?_,
    (vecEquiv e).toMonoidHom.comp β, (vecEquiv e).surjective.comp hβs, ?_, ?_⟩
  · rw [← hαk]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · rw [← hβk]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · intro ℓ u v hv
    have key := hβe ℓ u v hv
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← toAdd_vecEquiv_mulVec e (α ℓ) (β u), ← key]
    rfl

theorem isNaturalSLTwoModule_of_isLin2TypeGF {E : Subgroup Γ} {n : ℕ} (h : IsLin2TypeGF E n) :
    IsNaturalSLTwoModule ↥E n := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  have hpc : CFSG.pCore 2 ↥E = α.ker := hαk.symm
  let φ : (↥E ⧸ CFSG.pCore 2 ↥E) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have hU : (shortU ↥E).map E.subtype = CFSG.QuasithinUnique.blockU E :=
    map_shortU_eq_commutator E
  let eU : ↥(shortU ↥E) ≃* ↥(CFSG.QuasithinUnique.blockU E) :=
    (Subgroup.equivMapOfInjective (shortU ↥E) E.subtype E.subtype_injective).trans
      (MulEquiv.subgroupCongr hU)
  have heU : ∀ u : ↥(shortU ↥E),
      ((eU u : ↥(CFSG.QuasithinUnique.blockU E)) : Γ) = ((u : ↥E) : Γ) := fun u => rfl
  refine ⟨φ, β.comp eU.toMonoidHom, hβs.comp eU.surjective, ?_, ?_⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, heU, ← Subgroup.mem_map_iff_mem E.subtype_injective,
      map_shortC_eq_inf]
    exact Iff.rfl
  · intro l u hu hu'
    have hcoe : ((eU ⟨l * u * l⁻¹, hu'⟩ : ↥(CFSG.QuasithinUnique.blockU E)) : Γ) =
        (l : Γ) * ((eU ⟨u, hu⟩ : ↥(CFSG.QuasithinUnique.blockU E)) : Γ) * (l : Γ)⁻¹ := rfl
    have key := hβe l (eU ⟨u, hu⟩) (eU ⟨l * u * l⁻¹, hu'⟩) hcoe
    apply Multiplicative.toAdd.injective
    exact key

end CFSG.CGT.PushingUpLit.BHS6
