module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSym
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymModel
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

section AltSwap
variable {P : Type} [AddCommGroup P] [Module (ZMod 2) P]

@[expose] def addEquivToGL (e : P ≃+ P) : LinearMap.GeneralLinearGroup (ZMod 2) P :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    { toLinearMap := e.toAddMonoidHom.toZModLinearMap 2
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

theorem addEquivToGL_apply (e : P ≃+ P) (w : P) :
    ((addEquivToGL e : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w = e w := rfl

@[expose] noncomputable def altActEquiv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    CFSG.RankThree.PartTwo.altHeart m ≃+ CFSG.RankThree.PartTwo.altHeart m :=
  { toFun := altAct σ
    invFun := altAct σ⁻¹
    left_inv := altAct_inv_apply σ
    right_inv := altAct_apply_inv σ
    map_add' := (altAct σ).map_add }

noncomputable def symModelOfAlt {m : ℕ} (hm : 5 ≤ m) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m) :
    CFSG.HardMathSupport.Solomon.Coordinator.SymModel m P where
  ψ :=
    { toFun := fun σ => addEquivToGL ((φ.trans (altActEquiv σ)).trans φ.symm)
      map_one' := by
        apply Units.ext
        apply LinearMap.ext
        intro w
        show φ.symm (altAct 1 (φ w)) = w
        rw [altAct_one, φ.symm_apply_apply]
      map_mul' := fun σ τ => by
        apply Units.ext
        apply LinearMap.ext
        intro w
        show φ.symm (altAct (σ * τ) (φ w)) = φ.symm (altAct σ (φ (φ.symm (altAct τ (φ w)))))
        rw [altAct_mul, φ.apply_symm_apply] }
  γ := ((φ.symm.toAddMonoidHom.comp
    ((QuotientAddGroup.mk' (CFSG.RankThree.PartTwo.evenWeightOnes m)).comp
      (sumZeroEquivEvenWeight m).toAddMonoidHom))).toZModLinearMap 2
  surj := by
    intro p
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (φ p)
    obtain ⟨u, rfl⟩ := (sumZeroEquivEvenWeight m).surjective x
    refine ⟨u, ?_⟩
    show φ.symm (QuotientAddGroup.mk (sumZeroEquivEvenWeight m u)) = p
    rw [hx, φ.symm_apply_apply]
  equivariant := by
    intro σ y
    show φ.symm (altAct σ (φ (φ.symm (QuotientAddGroup.mk (sumZeroEquivEvenWeight m y))))) =
      φ.symm (QuotientAddGroup.mk (sumZeroEquivEvenWeight m (sumZeroEquiv σ y)))
    rw [φ.apply_symm_apply, sumZeroEquivEvenWeight_sumZeroEquiv, altAct_mk]
  ker_const := by
    intro y hy
    have h1 : φ.symm (QuotientAddGroup.mk (sumZeroEquivEvenWeight m y)) = 0 := hy
    have h2 : (QuotientAddGroup.mk (sumZeroEquivEvenWeight m y) :
        CFSG.RankThree.PartTwo.altHeart m) = 0 := by
      have := congrArg φ h1
      rwa [φ.apply_symm_apply, φ.map_zero] at this
    have h3 := (QuotientAddGroup.eq_zero_iff _).1 h2
    have h4 : ((sumZeroEquivEvenWeight m y : CFSG.QuasithinUnique.evenWeight m) :
        Fin m → ZMod 2) ∈ AddSubgroup.zmultiples (CFSG.RankThree.PartTwo.allOnes m) := by
      rw [CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf] at h3
      exact h3
    exact (exists_const_iff_mem_zmultiples _).2 h4
  inj := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply AlternatingGeometry.perm_eq_one_of_altHeart_fixed hm σ
    intro x
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) P =>
      (g : P →ₗ[ZMod 2] P) (φ.symm (QuotientAddGroup.mk x))) hσ
    have h2 : φ.symm (altAct σ (QuotientAddGroup.mk x)) = φ.symm (QuotientAddGroup.mk x) := by
      simpa [MonoidHom.coe_mk, OneHom.coe_mk, addEquivToGL_apply, altActEquiv] using h1
    have h3 := φ.symm.injective h2
    rw [altAct_mk] at h3
    exact h3

theorem isSwap_of_act_transvection [Finite P] {m : ℕ} (hm : 5 ≤ m) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m)
    (σ : Equiv.Perm (Fin m)) (τ : LinearMap.GeneralLinearGroup (ZMod 2) P) (hτ : IsF2Transvection τ)
    (h : ∀ w : P, φ ((τ : P →ₗ[ZMod 2] P) w) = altAct σ (φ w)) : σ.IsSwap := by
  have hψ : (symModelOfAlt hm φ).ψ σ = τ := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    show φ.symm (altAct σ (φ w)) = (τ : P →ₗ[ZMod 2] P) w
    rw [← h w, φ.symm_apply_apply]
  have := CFSG.HardMathSupport.Solomon.Coordinator.i28_14_symModel_swap_of_transv
    (symModelOfAlt hm φ) hm (σ := σ) (hψ ▸ hτ)
  obtain ⟨i, j, hij, rfl⟩ := this
  exact ⟨i, j, hij, rfl⟩

theorem act_of_isAlt {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} {m : ℕ}
    (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m) (θ : ↥L ≃* ↥(alternatingGroup (Fin m)))
    (hA : ∀ (g : ↥L) (w : P) (x : CFSG.QuasithinUnique.evenWeight m),
      φ w = (x : CFSG.RankThree.PartTwo.altHeart m) →
        φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
          (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin m)) x :
            CFSG.RankThree.PartTwo.altHeart m))
    (g : ↥L) (w : P) :
    φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
      altAct (θ g : Equiv.Perm (Fin m)) (φ w) := by
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (φ w)
  rw [hA g w x hx.symm, ← hx, altAct_mk]

theorem swapConcl_of_act [Finite P] {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} {m : ℕ}
    (hm : 5 ≤ m) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m)
    (θ : ↥L ≃* ↥(alternatingGroup (Fin m)))
    (hA : ∀ (g : ↥L) (w : P) (x : CFSG.QuasithinUnique.evenWeight m),
      φ w = (x : CFSG.RankThree.PartTwo.altHeart m) →
        φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
          (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin m)) x :
            CFSG.RankThree.PartTwo.altHeart m))
    {τ : LinearMap.GeneralLinearGroup (ZMod 2) P} (hτ : IsF2Transvection τ)
    {σ : Equiv.Perm (Fin m)} (hact : ∀ w : P, φ ((τ : P →ₗ[ZMod 2] P) w) = altAct σ (φ w)) :
    AltSwapConcl L m τ := by
  refine ⟨σ, φ, θ, isSwap_of_act_transvection hm φ σ τ hτ hact, hA, ?_⟩
  intro g g' hg'
  have hL := act_of_isAlt φ θ hA
  have hinvact : ∀ w : P, φ (((τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
      altAct σ⁻¹ (φ w) := by
    intro w
    have h1 := hact (((τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w)
    have h2 : (τ : P →ₗ[ZMod 2] P) (((τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) :
        P →ₗ[ZMod 2] P) w) = w := by
      show ((τ * τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w = w
      rw [mul_inv_cancel]; rfl
    rw [h2] at h1
    rw [h1, altAct_inv_apply]
  have hsame : ∀ v : CFSG.RankThree.PartTwo.altHeart m,
      altAct (θ g' : Equiv.Perm (Fin m)) v = altAct (σ * (θ g : Equiv.Perm (Fin m)) * σ⁻¹) v := by
    intro v
    obtain ⟨w, rfl⟩ := φ.surjective v
    rw [← hL g' w, altAct_mul, altAct_mul, ← hinvact w, ← hL g, ← hact]
    have : ((g' : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w =
        (τ : P →ₗ[ZMod 2] P) (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
          (((τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w)) := by
      rw [hg']; rfl
    rw [this]
  have hfaith : ∀ ρ₁ ρ₂ : Equiv.Perm (Fin m), (∀ v, altAct ρ₁ v = altAct ρ₂ v) → ρ₁ = ρ₂ := by
    intro ρ₁ ρ₂ h12
    have h1 : ρ₂⁻¹ * ρ₁ = 1 := by
      apply AlternatingGeometry.perm_eq_one_of_altHeart_fixed hm
      intro x
      rw [← altAct_mk, altAct_mul, h12, altAct_inv_apply]
    exact (inv_mul_eq_one.1 h1).symm
  exact hfaith _ _ hsame

theorem exists_perm_act_of_ne6 [Finite P] {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)}
    {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m)
    (θ : ↥L ≃* ↥(alternatingGroup (Fin m)))
    (hA : ∀ (g : ↥L) (w : P) (x : CFSG.QuasithinUnique.evenWeight m),
      φ w = (x : CFSG.RankThree.PartTwo.altHeart m) →
        φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
          (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin m)) x :
            CFSG.RankThree.PartTwo.altHeart m))
    {τ : LinearMap.GeneralLinearGroup (ZMod 2) P}
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    ∃ σ : Equiv.Perm (Fin m), ∀ w : P, φ ((τ : P →ₗ[ZMod 2] P) w) = altAct σ (φ w) := by
  have hL := act_of_isAlt φ θ hA
  let nτ : MulAut ↥L := L.normalizerMonoidHom ⟨τ, hτn⟩
  let α : MulAut ↥(alternatingGroup (Fin m)) := MulAut.congr θ nτ
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6).2 α
  have hrel : ∀ g : ↥L, ((θ (nτ g) : ↥(alternatingGroup (Fin m))) : Equiv.Perm (Fin m)) =
      σ * (θ g : Equiv.Perm (Fin m)) * σ⁻¹ := by
    intro g
    have h1 : α (θ g) = θ (nτ g) := by
      simp [α, MulAut.congr_apply]
    rw [← h1, ← hσ, MulAut.conjNormal_apply]
  have hcoe : ∀ g : ↥L, ((nτ g : ↥L) : LinearMap.GeneralLinearGroup (ZMod 2) P) = τ * g * τ⁻¹ :=
    fun g => Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨τ, hτn⟩ g
  let tE : P ≃+ P := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) P τ).toAddEquiv
  let t : CFSG.RankThree.PartTwo.altHeart m ≃+ CFSG.RankThree.PartTwo.altHeart m :=
    (φ.symm.trans tE).trans φ
  have ht : ∀ w : P, t (φ w) = φ ((τ : P →ₗ[ZMod 2] P) w) := fun w => by
    show φ (tE (φ.symm (φ w))) = _
    rw [φ.symm_apply_apply]; rfl
  have hcomm : ∀ (h : Equiv.Perm (Fin m)), h ∈ alternatingGroup (Fin m) → ∀ v,
      t (altAct h v) = altAct (σ * h * σ⁻¹) (t v) := by
    intro h hh v
    obtain ⟨w, rfl⟩ := φ.surjective v
    set g : ↥L := θ.symm ⟨h, hh⟩ with hg
    have hθg : (θ g : Equiv.Perm (Fin m)) = h := by
      rw [hg, MulEquiv.apply_symm_apply]
    have h1 : altAct h (φ w) = φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) :
        P →ₗ[ZMod 2] P) w) := by
      rw [hL g w, hθg]
    have h2 : ((τ : P →ₗ[ZMod 2] P) (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) :
        P →ₗ[ZMod 2] P) w)) = (((nτ g : ↥L) : LinearMap.GeneralLinearGroup (ZMod 2) P) :
          P →ₗ[ZMod 2] P) ((τ : P →ₗ[ZMod 2] P) w) := by
      rw [hcoe]
      have hτinv : ∀ w : P, ((τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
          ((τ : P →ₗ[ZMod 2] P) w) = w := fun w => by
        show ((τ⁻¹ * τ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w = w
        rw [inv_mul_cancel]; rfl
      show _ = ((τ * g * τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
        ((τ : P →ₗ[ZMod 2] P) w)
      simp [mul_assoc, hτinv]
    rw [h1, ht, h2, hL (nτ g), ht, hrel g, hθg]
  let T' : CFSG.RankThree.PartTwo.altHeart m →+ CFSG.RankThree.PartTwo.altHeart m :=
    (altAct σ⁻¹).comp t.toAddMonoidHom
  have hT'comm : ∀ h ∈ alternatingGroup (Fin m), ∀ v, T' (altAct h v) = altAct h (T' v) := by
    intro h hh v
    show altAct σ⁻¹ (t (altAct h v)) = altAct h (altAct σ⁻¹ (t v))
    rw [hcomm h hh v, ← altAct_mul, ← altAct_mul]
    congr 1
    group
  have hnz : ∃ v : CFSG.RankThree.PartTwo.altHeart m, v ≠ 0 := by
    have h5 : 2 < m := by omega
    refine ⟨(AlternatingGeometry.pairEW (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ :
      CFSG.RankThree.PartTwo.altHeart m), ?_⟩
    exact mk_pairEW_ne_zero (a := (⟨0, by omega⟩ : Fin m)) (b := ⟨1, by omega⟩)
      (c := ⟨2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  rcases altHeart_endo_eq_zero_or_id hm T' hT'comm with h0 | hid
  · exfalso
    obtain ⟨v, hv⟩ := hnz
    apply hv
    have h1 : altAct σ⁻¹ (t v) = 0 := by
      have := congrArg (fun f : CFSG.RankThree.PartTwo.altHeart m →+ _ => f v) h0
      simpa [T'] using this
    have h2 : t v = 0 := by
      have := congrArg (altAct σ) h1
      rwa [altAct_apply_inv, map_zero] at this
    have h2' : φ (tE (φ.symm v)) = φ 0 := by rw [φ.map_zero]; exact h2
    have h3 : tE (φ.symm v) = 0 := φ.injective h2'
    have h4 : φ.symm v = 0 := tE.injective (h3.trans tE.map_zero.symm)
    calc v = φ (φ.symm v) := (φ.apply_symm_apply v).symm
      _ = φ 0 := by rw [h4]
      _ = 0 := φ.map_zero
  · refine ⟨σ, fun w => ?_⟩
    have h1 : altAct σ⁻¹ (t (φ w)) = φ w := by
      have := congrArg (fun f : CFSG.RankThree.PartTwo.altHeart m →+ _ => f (φ w)) hid
      simpa [T'] using this
    have h2 := congrArg (altAct σ) h1
    rw [altAct_apply_inv, ht] at h2
    exact h2

theorem isAlt_transv_swap_ne6_proof [Finite P]
    {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (hA : IsAltModel L m) {τ : LinearMap.GeneralLinearGroup (ZMod 2) P} (hτ : IsF2Transvection τ)
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    AltSwapConcl L m τ := by
  obtain ⟨φ, θ, hA'⟩ := hA
  obtain ⟨σ, hσ⟩ := exists_perm_act_of_ne6 hm hm6 φ θ hA' hτn
  exact swapConcl_of_act hm φ θ hA' hτ hσ

end AltSwap

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
