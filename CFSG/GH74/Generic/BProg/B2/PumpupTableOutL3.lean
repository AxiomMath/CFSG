module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
public import CFSG.GH74.KGroups.L3EpsOuterLin
import CFSG.GH74.KGroups.L3EpsInvLin
import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar
import CFSG.GH74.GLS.LU.Local.Transport
public import CFSG.GH74.KGroups.L3EpsSylow

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.ComponentClassification.Burgoyne.PSL CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3 (omega3_equiv_psl2)
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem eq_one_of_isometry_of_mem_scalars (R : GL (Fin 3) F) (z : SL(3, F))
    (hz : SpecialLinearGroup.toGL z ∈ CatalogueBGraphForm.isometryGroup 3 F R)
    (hs : z ∈ scalars 3 F) : z = 1 := by
  obtain ⟨c, hc3, hzc⟩ := hs
  have hzgl : SpecialLinearGroup.toGL z = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hzc
  have h1 : CatalogueBGraphForm.glTranspose 3 F (Matrix.GeneralLinearGroup.scalar (Fin 3) c) * R *
      Matrix.GeneralLinearGroup.scalar (Fin 3) c = R := by
    have := hz
    rw [hzgl] at this
    exact this
  rw [CatalogueBGraphForm.glTranspose_scalar] at h1
  have hcen : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2) * R = R := by
    rw [map_pow, pow_two]
    calc Matrix.GeneralLinearGroup.scalar (Fin 3) c * Matrix.GeneralLinearGroup.scalar (Fin 3) c * R
        = Matrix.GeneralLinearGroup.scalar (Fin 3) c * R * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
          rw [mul_assoc, mul_assoc, ← Subgroup.mem_center_iff.mp hcen R]
      _ = R := h1
  have h3 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2) = 1 := mul_eq_right.mp h2
  have h4 : (c : F) ^ 2 = 1 := by
    have h := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h3
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_pow_eq_pow_val, Units.val_one, Matrix.one_apply_eq] at h
    exact h
  have hc1 : c = 1 := by
    have h5 : (c : F) ^ 3 = 1 := by
      have := congrArg Units.val hc3
      simpa using this
    have h6 : (c : F) = 1 := by
      calc (c : F) = (c : F) ^ 3 / (c : F) ^ 2 := by
            have hc0 : (c : F) ≠ 0 := c.ne_zero
            field_simp
        _ = 1 := by rw [h5, h4]; simp
    exact Units.ext h6
  subst hc1
  apply Subtype.ext
  rw [hzc]
  simp

theorem lin_graph_centralizer_psl2 [Finite F] (hF : ringChar F ≠ 2) (h3 : Nat.card F ≠ 3) {A : GL (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) :
    ∃ N : Subgroup (projectiveSL 3 F), CFSG.IsQuasisimple ↥N ∧
      (∀ n ∈ N, (conjAut 3 F A * dualAut 3 F) n = n) ∧
      (∀ x, (conjAut 3 F A * dualAut 3 F) x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧
      (∀ x y, (conjAut 3 F A * dualAut 3 F) x = x → (conjAut 3 F A * dualAut 3 F) y = y →
        ⁅x, y⁆ ∈ N) ∧ Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  classical
  set R : GL (Fin 3) F := A⁻¹ with hR
  have hRsymm : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R := transpose_inv_of_symm A hA
  set I := CatalogueBGraphForm.isometryGroup 3 F R with hI
  set Ω := ⁅I, I⁆ with hΩ
  have hq : CFSG.IsQuasisimple Ω := by
    have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two F hF
    have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hF R hRsymm
    have hdim : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
    obtain ⟨d, ψ, e, -, -, -, hq0, -⟩ := orthogonal_three_derived hodd h3
      (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
    have := isQuasisimple_trans (isoOrthGL hF R hRsymm) hq0
    rwa [trans_commutator] at this
  set ΩS : Subgroup SL(3, F) := Ω.comap SpecialLinearGroup.toGL with hΩS
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = Ω := map_comap_toGL_of_le_commutator le_rfl
  have hqS : CFSG.IsQuasisimple ΩS :=
    LocalCores.isQuasisimple_of_mulEquiv ((ΩS.equivMapOfInjective _
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmapΩ)).symm hq
  have hrep : ∀ x : projectiveSL 3 F, (conjAut 3 F A * dualAut 3 F) x = x →
      ∃ g : SL(3, F), g ∈ isometrySL 3 A⁻¹ ∧ LinearFlag.proj 3 F g = x := by
    intro x hx
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F x
    rw [conjAut_mul_dualAut_proj] at hx
    exact exists_isometrySL_rep hA hx
  refine ⟨ΩS.map (LinearFlag.proj 3 F), ?_, ?_, ?_, ?_, ?_⟩
  · refine LocalCores.isQuasisimple_map hqS (LinearFlag.proj 3 F) fun hker => ?_
    have hab : ∀ a ∈ ΩS, ∀ b ∈ ΩS, a * b = b * a := by
      intro a ha b hb
      have ha' : a ∈ scalars 3 F := by
        have h1 : LinearFlag.proj 3 F a = 1 := hker ha
        exact LinearFlag.proj_eq_one_iff.1 h1
      exact (mem_center_iff.1 (scalars_le_center 3 F ha') b).symm
    have : Nontrivial ΩS := LocalCores.isQuasisimple_nontrivial hqS
    have hcomm : commutator ΩS = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hab a a.2 b b.2)
    have hperfF := hqS.1.commutator_eq_top
    rw [hcomm] at hperfF
    exact bot_ne_top hperfF
  · rintro _ ⟨h, hh, rfl⟩
    rw [conjAut_mul_dualAut_proj]
    congr 1
    exact (graphLift_eq_iff A h).2 (commutator_le_self I hh)
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨h, hh, rfl⟩ := hn
    refine ⟨g * h * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    change SpecialLinearGroup.toGL (g * h * g⁻¹) ∈ Ω
    rw [map_mul, map_mul, map_inv]
    have hg' : graphLiftGL A (SpecialLinearGroup.toGL g) = SpecialLinearGroup.toGL g *
        GeneralLinearGroup.scalar (Fin 3) 1 := by
      rw [map_one, mul_one]
      exact (graphLiftGL_eq_iff A _).2 hg
    exact conj_mem_commutator_isometryGroup hg' hh
  · intro x y hx hy
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨k, hk, rfl⟩ := hrep y hy
    refine ⟨⁅g, k⁆, ?_, by simp only [map_commutatorElement]⟩
    change SpecialLinearGroup.toGL ⁅g, k⁆ ∈ Ω
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hg hk
  ·
    have hinj : Function.Injective ((LinearFlag.proj 3 F).comp ΩS.subtype) := by
      intro a b hab
      have h1 : LinearFlag.proj 3 F (a : SL(3, F)) = LinearFlag.proj 3 F (b : SL(3, F)) := hab
      have hz := LinearFlag.proj_eq_proj_iff.1 h1
      have hzΩ : ((a : SL(3, F))⁻¹ * (b : SL(3, F))) ∈ ΩS := ΩS.mul_mem (ΩS.inv_mem a.2) b.2
      have hzI : SpecialLinearGroup.toGL ((a : SL(3, F))⁻¹ * (b : SL(3, F))) ∈ I :=
        commutator_le_self I hzΩ
      have h2 := eq_one_of_isometry_of_mem_scalars R _ hzI hz
      apply Subtype.ext
      exact inv_mul_eq_one.mp h2
    have hrange : ((LinearFlag.proj 3 F).comp ΩS.subtype).range = ΩS.map (LinearFlag.proj 3 F) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have e1 : ↥ΩS ≃* ↥(ΩS.map (LinearFlag.proj 3 F)) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    obtain ⟨e3⟩ := omega3_equiv_psl2 hF h3 R hRsymm
    exact ⟨e1.symm.trans (((ΩS.equivMapOfInjective _ SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr hmapΩ)).trans e3)⟩



section Leaf

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg.B2
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic CFSG.GH74.Generic.BProg.B2.PumpupTableL2
  CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3

theorem mem_of_conjNormal_mem_inner {N : Type*} [Group N] (H : Subgroup N) [H.Normal]
    (hC : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {t : N}
    (hin : MulAut.conjNormal t ∈ inner ↥H) : t ∈ H := by
  obtain ⟨h, hh⟩ := hin
  have hcomm : (h : N)⁻¹ * t ∈ Subgroup.centralizer (H : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥H => ((φ ⟨x, hx⟩ : ↥H) : N)) hh
    have hσx : ((MulAut.conjNormal t ⟨x, hx⟩ : ↥H) : N) = t * x * t⁻¹ := by
      rw [MulAut.conjNormal_apply]
    simp only [MulAut.conj_apply] at h1
    rw [hσx] at h1
    have h2 : (h : N) * x * (h : N)⁻¹ = t * x * t⁻¹ := h1
    calc x * ((h : N)⁻¹ * t) = (h : N)⁻¹ * ((h : N) * x * (h : N)⁻¹) * t := by group
      _ = (h : N)⁻¹ * (t * x * t⁻¹) * t := by rw [h2]
      _ = (h : N)⁻¹ * t * x := by group
  have h1 : (h : N)⁻¹ * t = 1 :=
    hC _ (fun y hy => (Subgroup.mem_centralizer_iff.mp hcomm y hy).symm)
  have : t = h := by
    have := congrArg (fun z => (h : N) * z) h1
    simpa using this
  rw [this]
  exact h.2


section Certified


theorem pumpupOut_l3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f) :
    PumpupEmptyOut (fun X _ => LieModel X .PSL 3 p f) := by
  intro N _ _ H t L hs htH hH
  have hnorm : H.Normal := hs.normal
  have ht2 : t * t = 1 := by
    have := hs.inv
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
  have hst := stated_of_lieModel (Or.inl rfl) hH
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hst
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hFodd
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have hF5 : 5 ≤ Nat.card F := by rw [hF]; exact h5
  have h3 : Nat.card F ≠ 3 := by omega
  let c : MulAut ↥H := MulAut.conjNormal t
  have hc2 : c * c = 1 := by
    change MulAut.conjNormal t * MulAut.conjNormal t = 1
    rw [← map_mul, ht2, map_one]
  have hout : c ∉ (inner ↥H : Subgroup (MulAut ↥H)) := fun hin =>
    htH (mem_of_conjNormal_mem_inner H hs.faithful hin)
  have hc2' : conjAutEquiv e c * conjAutEquiv e c = 1 := by
    rw [← conjAutEquiv_mul, hc2, conjAutEquiv_one]
  have hout' : conjAutEquiv e c ∉ (inner (projectiveSL 3 F) : Subgroup (MulAut (projectiveSL 3 F))) :=
    fun h => hout (conjAutEquiv_mem_inner e h)
  obtain ⟨A, hAs, hA⟩ := lin_involution_form hp hF hf h2 hc2' hout'
  obtain ⟨N0, hq, hfix, hconj, hcomm, ⟨eN⟩⟩ := lin_graph_centralizer_psl2 hF2 h3 hAs
  rw [← hA] at hfix hconj hcomm
  have hfixK : ∀ x : ↥H, c x = x → conjAutEquiv e c (e x) = e x := fun x hx => by
    rw [conjAutEquiv_apply, hx]
  set S : Subgroup ↥H := N0.map (e.symm : projectiveSL 3 F →* ↥H) with hSdef
  have hmemS : ∀ x : ↥H, x ∈ S ↔ e x ∈ N0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  have hSq : IsQuasisimple ↥S := LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm N0) hq
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
  have hSC : S ≤ C := by
    intro x hx
    rw [hmemC]
    have hx' := (hmemS x).1 hx
    apply e.injective
    have h1 := hfix (e x) hx'
    rw [conjAutEquiv_apply] at h1
    exact h1
  have hSn : ∀ x ∈ C, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    rw [hmemS] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact hconj (e x) (hfixK x ((hmemC x).1 hx)) (e s) hs
  have hSc : ∀ x ∈ C, ∀ z ∈ C, ⁅x, z⁆ ∈ S := by
    intro x hx z hz
    rw [hmemS, map_commutatorElement]
    exact hcomm (e x) (e z) (hfixK x ((hmemC x).1 hx)) (hfixK z ((hmemC z).1 hz))
  have hB : IsCompIn C (L.subgroupOf H) := by
    have hCH : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H := inf_le_left
    exact ⟨Subgroup.comap_mono hs.comp.1,
      (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' (K := L)
        (M := H ⊓ Subgroup.centralizer ({t} : Set N)) (H := H) hCH).2 hs.comp.2⟩
  have hLS : L.subgroupOf H = S :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hSq hSC hSn hSc hB
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  let eL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans ((MulEquiv.subgroupCongr hLS).trans
      ((MulEquiv.subgroupMap e.symm N0).symm.trans eN))
  exact false_of_psl2_component hs hp hp2 (lieModel_psl2_of_equiv hp hf.pos (by omega) hF eL)

end Certified

end Leaf

end CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
