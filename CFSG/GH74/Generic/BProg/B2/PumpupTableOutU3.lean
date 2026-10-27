module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
public import CFSG.GH74.KGroups.L3EpsUniGraph
import CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
import CFSG.GH74.KGroups.L3EpsUniInv
import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar
import CFSG.GH74.GLS.LU.Local.Transport

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.SubgroupLists
  CFSG.GH74.KGroups.L3Eps.Uni
open CFSG.GH74.KGroups.L3Eps (GraphData)
open CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3 (omega3_equiv_psl2)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {F : Type} [Field F]

theorem graphData_of_typeII_psl2 (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {φ : F ≃+* F} {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g)) :
    ∃ N : Subgroup K, CFSG.GH74.KGroups.L3Eps.GraphData K σ N ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) h.fixedField) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  have : Finite F := h.finite
  obtain ⟨D⟩ := exists_realData h h2 hAu hAA
  have hk2 : (2 : h.fixedField) ≠ 0 := CFSG.GH74.Generic.S45.Uni.two_ne_zero_fixedField h h2
  have hk : ringChar h.fixedField ≠ 2 := ringChar_ne_two_of_two_ne_zero hk2
  have h3 : Nat.card h.fixedField ≠ 3 := by rw [h.card_fixedField]; omega
  have hΩq := isQuasisimple_commutator_isometryGroup hk h3 D.G D.hGs
  let Ω : Subgroup (GL (Fin 3) h.fixedField) := ⁅D.Iso, D.Iso⁆
  have hΩle : Ω ≤ D.Iso1 := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ⟨?_, ?_⟩
    · exact D.Iso.mul_mem (D.Iso.mul_mem (D.Iso.mul_mem hx hy) (D.Iso.inv_mem hx)) (D.Iso.inv_mem hy)
    · show ⁅x, y⁆ ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) h.fixedField →* h.fixedFieldˣ).ker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  let ρ : ↥D.Iso1 →* K := θ.comp D.Phi
  have hρ : Function.Injective ρ := D.injective_theta_Phi hθ
  have hnorm : ∀ (X : ↥D.Iso1), ∀ ω ∈ Ω.subgroupOf D.Iso1, X * ω * X⁻¹ ∈ Ω.subgroupOf D.Iso1 := by
    intro X ω hω
    have hω' : (ω : GL (Fin 3) h.fixedField) ∈ Ω := hω
    show (X : GL (Fin 3) h.fixedField) * (ω : GL (Fin 3) h.fixedField) * (X : GL (Fin 3) h.fixedField)⁻¹ ∈ Ω
    have : (X : GL (Fin 3) h.fixedField) * (ω : GL (Fin 3) h.fixedField) * (X : GL (Fin 3) h.fixedField)⁻¹ =
        ⁅(X : GL (Fin 3) h.fixedField), (ω : GL (Fin 3) h.fixedField)⁆ * (ω : GL (Fin 3) h.fixedField) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact Ω.mul_mem (Subgroup.commutator_mem_commutator X.2.1 (hΩle hω').1) hω'
  have hcomm : ∀ (X Y : ↥D.Iso1), ⁅X, Y⁆ ∈ Ω.subgroupOf D.Iso1 := by
    intro X Y
    show ⁅(X : GL (Fin 3) h.fixedField), (Y : GL (Fin 3) h.fixedField)⁆ ∈ Ω
    exact Subgroup.commutator_mem_commutator X.2.1 Y.2.1
  have hfixPhi : ∀ X : ↥D.Iso1, σ (ρ X) = ρ X := by
    intro X
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (D.Phi X)
    have hgg : g' = D.Phi X := Subtype.ext (by rw [hg'GL]; exact D.Phi_fixed hφ X)
    rw [hgg] at hg'θ
    exact hg'θ.symm
  have e1 : ↥(Ω.subgroupOf D.Iso1) ≃* ↥Ω := Subgroup.subgroupOfEquivOfLe hΩle
  have e2 : ↥(Ω.subgroupOf D.Iso1) ≃* ↥((Ω.subgroupOf D.Iso1).map ρ) :=
    Subgroup.equivMapOfInjective _ ρ hρ
  obtain ⟨e3⟩ := omega3_equiv_psl2 hk h3 D.G D.hGs
  refine ⟨(Ω.subgroupOf D.Iso1).map ρ, ⟨?_, ?_, ?_, ?_⟩, ⟨e2.symm.trans (e1.trans e3)⟩⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hΩq
  · rintro n ⟨ω, -, rfl⟩
    exact hfixPhi ω
  · intro x hx n hn
    obtain ⟨g, rfl, hg⟩ := exists_fixed_rep h hθ hφ hrel hx
    obtain ⟨X, hX⟩ := D.exists_Phi_of_fixed hφ hg
    obtain ⟨ω, hω, rfl⟩ := hn
    refine ⟨X * ω * X⁻¹, hnorm X ω hω, ?_⟩
    have : θ g = ρ X := by rw [← hX]; rfl
    rw [this]
    simp only [map_mul, map_inv]
  · intro x y hx hy
    obtain ⟨g, rfl, hg⟩ := exists_fixed_rep h hθ hφ hrel hx
    obtain ⟨X, hX⟩ := D.exists_Phi_of_fixed hφ hg
    obtain ⟨g', rfl, hg'⟩ := exists_fixed_rep h hθ hφ hrel hy
    obtain ⟨Y, hY⟩ := D.exists_Phi_of_fixed hφ hg'
    refine ⟨⁅X, Y⁆, hcomm X Y, ?_⟩
    have h1 : θ g = ρ X := by rw [← hX]; rfl
    have h2' : θ g' = ρ Y := by rw [← hY]; rfl
    rw [h1, h2', map_commutatorElement]

theorem graphData_of_cover_psl2 (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hq : Odd (p ^ f)) {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} (hσ : σ * σ = 1)
    (hout : σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ N : Subgroup K, CFSG.GH74.KGroups.L3Eps.GraphData K σ N ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) h.fixedField) := by
  rcases involution_type h hp h5 hθ hσ with ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_conj_of_typeI h hθ hAu hAA hrel
    exact hout ⟨y, hy⟩
  · exact graphData_of_typeII_psl2 h h5 hq hθ hφ hAu hAA hrel

section Leaf

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg.B2
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Generic.BProg.B2.PumpupTableL2
  CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3

section Certified


theorem pumpupOut_u3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    PumpupEmptyOut (fun X _ => LieModel X .PSU 3 p f) := by
  intro N _ _ H t L hs htH hH
  have hnorm : H.Normal := hs.normal
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := stated_of_lieModel (Or.inr rfl) hH
  have hf : 1 ≤ f := hadm.2.1
  have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hU e₀
  let c : MulAut ↥H := MulAut.conjNormal t
  have hc2 : c * c = 1 := by
    change MulAut.conjNormal t * MulAut.conjNormal t = 1
    rw [← map_mul, ht2, map_one]
  have hout : c ∉ (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥H : Subgroup (MulAut ↥H)) :=
    fun hin => htH (CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3.mem_of_conjNormal_mem_inner H hs.faithful hin)
  obtain ⟨N0, hGD, ⟨eN⟩⟩ := graphData_of_cover_psl2 hU hp2 h5 hq hθ hc2 hout
  set C : Subgroup ↥H := (H ⊓ Subgroup.centralizer ({t} : Set N)).subgroupOf H with hC
  have hmemC : ∀ x : ↥H, x ∈ C ↔ c x = x := by
    intro x
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      change t * (x : N) * t⁻¹ = x
      rw [← hx]
      group
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      change t * (x : N) * t⁻¹ = x at this
      calc (x : N) * t = (t * (x : N) * t⁻¹) * t := by rw [this]
        _ = t * x := by group
  have hSC : N0 ≤ C := fun x hx => (hmemC x).2 (hGD.fixed x hx)
  have hSn : ∀ x ∈ C, ∀ s ∈ N0, x * s * x⁻¹ ∈ N0 := fun x hx s hs' =>
    hGD.conj_mem x ((hmemC x).1 hx) s hs'
  have hSc : ∀ x ∈ C, ∀ z ∈ C, ⁅x, z⁆ ∈ N0 := fun x hx z hz =>
    hGD.commutator_mem x z ((hmemC x).1 hx) ((hmemC z).1 hz)
  have hB : IsCompIn C (L.subgroupOf H) := by
    have hCH : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H := inf_le_left
    exact ⟨Subgroup.comap_mono hs.comp.1,
      (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' (K := L)
        (M := H ⊓ Subgroup.centralizer ({t} : Set N)) (H := H) hCH).2 hs.comp.2⟩
  have hLS : L.subgroupOf H = N0 :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hGD.quasisimple hSC hSn hSc hB
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  let eL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) hU.fixedField :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans ((MulEquiv.subgroupCongr hLS).trans eN)
  have := hU.finite
  exact false_of_psl2_component hs hp hp2
    (lieModel_psl2_of_equiv hp hf (by omega) hU.card_fixedField eL)

end Certified

end Leaf

end CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
