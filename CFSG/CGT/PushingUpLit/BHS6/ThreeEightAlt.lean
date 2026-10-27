module

public import CFSG.CGT.PushingUpLit.BHS6.BlockFacts

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne
open CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def coreModEvenEquiv (m : ℕ) :
    ↥(coreMod m) ≃* Multiplicative (CFSG.QuasithinUnique.evenWeight m) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd (x : PermMod m), x.2⟩
  invFun y := ⟨Multiplicative.ofAdd
    ((Multiplicative.toAdd y : CFSG.QuasithinUnique.evenWeight m) : Fin m → ZMod 2),
    (Multiplicative.toAdd y).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem map_shortU_eq_commutator (E : Subgroup Γ) :
    (shortU ↥E).map E.subtype = ⁅pCoreOf 2 E, E⁆ := by
  rw [CFSG.CGT.PushingUpLit.map_shortU_subtype]
  show ⁅CFSG.CGT.PushingUpLit.oTwoIn E, E⁆ = _
  rw [oTwoIn_eq_pCoreOf]

theorem map_shortC_eq_inf (E : Subgroup Γ) :
    (shortC ↥E).map E.subtype = ⁅pCoreOf 2 E, E⁆ ⊓ Subgroup.centralizer (E : Set Γ) := by
  rw [CFSG.CGT.PushingUpLit.map_shortC_subtype]
  show CFSG.CGT.PushingUpLit.blockU E ⊓ _ = _
  show ⁅CFSG.CGT.PushingUpLit.oTwoIn E, E⁆ ⊓ _ = _
  rw [oTwoIn_eq_pCoreOf]

theorem isNaturalAltModule_of_isAltType {E : Subgroup Γ} {m : ℕ}
    (h : CFSG.QuasithinUnique.IsAltType E (2 * m + 1)) : IsNaturalAltModule ↥E m := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  have hpc : CFSG.pCore 2 ↥E = α.ker := hαk.symm
  let φ : (↥E ⧸ CFSG.pCore 2 ↥E) ≃* alternatingGroup (Fin (2 * m + 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have hU : (shortU ↥E).map E.subtype = CFSG.QuasithinUnique.blockU E :=
    map_shortU_eq_commutator E
  let eU : ↥(shortU ↥E) ≃* ↥(CFSG.QuasithinUnique.blockU E) :=
    (Subgroup.equivMapOfInjective (shortU ↥E) E.subtype E.subtype_injective).trans
      (MulEquiv.subgroupCongr hU)
  have heU : ∀ u : ↥(shortU ↥E),
      ((eU u : ↥(CFSG.QuasithinUnique.blockU E)) : Γ) = ((u : ↥E) : Γ) := fun u => rfl
  let ψ : ↥(shortU ↥E) →* Multiplicative (Fin (2 * m + 1) → ZMod 2) :=
    ((coreMod (2 * m + 1)).subtype).comp
      ((coreModEvenEquiv (2 * m + 1)).symm.toMonoidHom.comp (β.comp eU.toMonoidHom))
  have hψ : ∀ u, ψ u = (((coreModEvenEquiv (2 * m + 1)).symm (β (eU u)) : ↥(coreMod (2 * m + 1))) :
      PermMod (2 * m + 1)) := fun u => rfl
  refine ⟨φ, ψ, fun u => ?_, fun v hv => ?_, ?_, ?_⟩
  · exact ((coreModEvenEquiv (2 * m + 1)).symm (β (eU u))).2
  · obtain ⟨u', hu'⟩ := hβs (coreModEvenEquiv (2 * m + 1) ⟨Multiplicative.ofAdd v, hv⟩)
    refine ⟨eU.symm u', ?_⟩
    rw [hψ, MulEquiv.apply_symm_apply, hu']
    rfl
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ u = 1 ↔ β (eU u) = 1 := by
      constructor
      · intro h
        have h2 : (coreModEvenEquiv (2 * m + 1)).symm (β (eU u)) = 1 := Subtype.ext h
        exact (MulEquiv.map_eq_one_iff _).1 h2
      · intro h
        rw [hψ, h, map_one]
        rfl
    rw [h1, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, heU,
      ← Subgroup.mem_map_iff_mem E.subtype_injective, map_shortC_eq_inf]
    exact Iff.rfl
  · intro l u hu hu'
    have hcoe : ((eU ⟨l * u * l⁻¹, hu'⟩ : ↥(CFSG.QuasithinUnique.blockU E)) : Γ) =
        (l : Γ) * ((eU ⟨u, hu⟩ : ↥(CFSG.QuasithinUnique.blockU E)) : Γ) * (l : Γ)⁻¹ := rfl
    have key := hβe l (eU ⟨u, hu⟩) (eU ⟨l * u * l⁻¹, hu'⟩) hcoe
    apply Multiplicative.toAdd.injective
    funext i
    exact key i

end CFSG.CGT.PushingUpLit.BHS6
