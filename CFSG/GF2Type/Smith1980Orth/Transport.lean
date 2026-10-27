module

public import CFSG.GF2Type.Smith1980Orth.Defs
public import CFSG.LargeExtraspecial.BridgeForms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Setting

open Subgroup CFSG.Monster.GMS

variable {G G' : Type*} [Group G] [Group G']

theorem map_M (S : Setting G) (e : G ≃* G') : (S.map e).M = S.M.map e.toMonoidHom :=
  (map_centralizer_singleton e S.z).symm

theorem mem_map_M_iff (S : Setting G) (e : G ≃* G') {y : G'} :
    y ∈ (S.map e).M ↔ e.symm y ∈ S.M := by
  rw [map_M, mem_map_equiv]

theorem mem_map_QG_iff (S : Setting G) (e : G ≃* G') {y : G'} :
    y ∈ (S.map e).QG ↔ e.symm y ∈ S.QG := by
  rw [map_QG, mem_map_equiv]

theorem mem_conjBy_M_iff (S : Setting G) (g : G) {x : G} :
    x ∈ (S.conjBy g).M ↔ g⁻¹ * x * g ∈ S.M := by
  rw [conjBy, mem_map_M_iff, MulAut.conj_symm_apply]

theorem mem_conjBy_QG_iff (S : Setting G) (g : G) {x : G} :
    x ∈ (S.conjBy g).QG ↔ g⁻¹ * x * g ∈ S.QG := by
  rw [conjBy, mem_map_QG_iff, MulAut.conj_symm_apply]

theorem isConj_conjBy_z_iff (S : Setting G) (g : G) {x : G} :
    IsConj (S.conjBy g).z x ↔ IsConj S.z x := by
  have h : IsConj S.z (S.conjBy g).z := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨h.trans, h.symm.trans⟩

section Quotient

variable [Finite G] [Finite G']

theorem width_map (S : Setting G) (e : G ≃* G') : (S.map e).width = S.width := by
  have h1 := (S.map e).card_Q_eq
  rw [← (S.map e).card_QG_eq_card_Q, map_QG, card_map_of_injective e.injective,
    S.card_QG_eq_card_Q, S.card_Q_eq] at h1
  have := Nat.pow_right_injective le_rfl h1
  omega

@[expose] noncomputable def mbarEquivMap (S : Setting G) (e : G ≃* G') :
    (S.map e).Mbar ≃* S.Mbar :=
  (S.map e).quotientEquivMbar.symm.trans
    ((QuotientGroup.congr S.Q (S.map e).Q (centralizerMulEquiv e S.z) rfl).symm.trans
      S.quotientEquivMbar)

@[expose] noncomputable def mbarEquivConjBy (S : Setting G) (g : G) :
    (S.conjBy g).Mbar ≃* S.Mbar :=
  S.mbarEquivMap (MulAut.conj g)

end Quotient

end CFSG.LargeExtraspecial.Setting

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open

@[expose] def finFunEquiv {n m : ℕ} (h : n = m) : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr h.symm)

@[expose] def castForm {n m : ℕ} (h : n = m) (q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)) :
    QuadraticForm (ZMod 2) (Fin m → ZMod 2) :=
  q.comp (finFunEquiv h).symm.toLinearMap

theorem castForm_finFunEquiv {n m : ℕ} (h : n = m) (q : QuadraticForm (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) : castForm h q (finFunEquiv h v) = q v := by
  simp [castForm]

theorem timmesfeldNondegenerate_castForm {n m : ℕ} (h : n = m)
    {q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)} (hq : timmesfeldNondegenerate q) :
    timmesfeldNondegenerate (castForm h q) :=
  Bridge.nondegenerate_of_map (finFunEquiv h) (castForm_finFunEquiv h q) hq

@[expose] noncomputable def omegaCastForm {n m : ℕ} (h : n = m)
    (q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)) :
    timmesfeldOmega q ≃* timmesfeldOmega (castForm h q) :=
  Bridge.omegaEquiv (finFunEquiv h) (castForm_finFunEquiv h q)

@[expose] noncomputable def isometriesCastForm {n m : ℕ} (h : n = m)
    (q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)) :
    timmesfeldIsometries q ≃* timmesfeldIsometries (castForm h q) :=
  Bridge.isometriesEquiv (finFunEquiv h) (castForm_finFunEquiv h q)

section OrthData

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

@[expose] noncomputable def OrthData.map {S : Setting G} (O : OrthData S) (e : G ≃* G') :
    OrthData (S.map e) where
  q := castForm (S.width_map e).symm O.q
  nondeg := timmesfeldNondegenerate_castForm _ O.nondeg
  four_le := by rw [S.width_map e]; exact O.four_le
  even := by rw [S.width_map e]; exact O.even
  iso := by
    rcases O.iso with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact Or.inl ⟨((S.mbarEquivMap e).trans f).trans
        (MulEquiv.prodCongr (MulEquiv.refl _) (omegaCastForm (S.width_map e).symm O.q))⟩
    · exact Or.inr ⟨((S.mbarEquivMap e).trans f).trans
        (MulEquiv.prodCongr (MulEquiv.refl _) (isometriesCastForm (S.width_map e).symm O.q))⟩

end OrthData

section ConjBy

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def OrthData.conjBy {S : Setting G} (O : OrthData S) (g : G) :
    OrthData (S.conjBy g) :=
  O.map (MulAut.conj g)

end ConjBy

end CFSG.GF2Type.Smith1980Orth
