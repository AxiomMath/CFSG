module

public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Dich
public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Cls
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Module Submodule Subgroup Matrix
open LinearMap (BilinForm)
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsSp4
open SymplecticHigher SymplecticFlag
open CFSG.ClassicalGroups.Alternating

section Model

variable {F : Type} [Field F]

@[expose] noncomputable def tauT1 (F : Type) [Field F] : Module.End F (Fin 2 ⊕ Fin 2 → F) :=
  Matrix.mulVecLin (blk (1 : Matrix (Fin 2) (Fin 2) F) (-1))

@[expose] def sgnT1 (F : Type) [Field F] : Fin 2 ⊕ Fin 2 → F := Sum.elim ![1, -1] ![1, -1]

theorem tauT1_apply (x : Fin 2 ⊕ Fin 2 → F) (i : Fin 2 ⊕ Fin 2) : tauT1 F x i = sgnT1 F i * x i := by
  rw [tauT1, mulVecLin_apply, blk_one_neg_one_eq_diagonal, mulVec_diagonal]
  rfl

theorem tauT1_sq : tauT1 F * tauT1 F = 1 := by
  rw [tauT1, Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, blk_mul, Matrix.one_mul, 
    show (-1 : Matrix (Fin 2) (Fin 2) F) * (-1) = 1 by simp, blk_one_one, Matrix.mulVecLin_one]
  rfl


theorem tauT1_isometry (x y : Fin 2 ⊕ Fin 2 → F) :
    pairedSympForm F 2 (tauT1 F x) (tauT1 F y) = pairedSympForm F 2 x y := by
  have := pairedSympForm_mulVec (T1 F) x y
  rw [coe_T1] at this
  exact this

@[expose] def swapPerm : Fin 2 ⊕ Fin 2 ≃ Fin 2 ⊕ Fin 2 := Equiv.sumCongr (Equiv.swap 0 1) (Equiv.swap 0 1)

@[expose] noncomputable def swapMap (F : Type) [Field F] : (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
  LinearEquiv.funCongrLeft F F swapPerm

theorem swapMap_apply (x : Fin 2 ⊕ Fin 2 → F) (i : Fin 2 ⊕ Fin 2) : swapMap F x i = x (swapPerm i) := rfl

theorem swapMap_swapMap (x : Fin 2 ⊕ Fin 2 → F) : swapMap F (swapMap F x) = x := by
  funext i
  rw [swapMap_apply, swapMap_apply]
  rcases i with i | i <;> fin_cases i <;> simp [swapPerm]

theorem sgnT1_swap (i : Fin 2 ⊕ Fin 2) : sgnT1 F (swapPerm i) = -sgnT1 F i := by
  rcases i with i | i <;> fin_cases i <;> simp [swapPerm, sgnT1]

theorem tauT1_swap (x : Fin 2 ⊕ Fin 2 → F) : tauT1 F (swapMap F x) = -(swapMap F (tauT1 F x)) := by
  funext i
  rw [tauT1_apply, swapMap_apply, Pi.neg_apply, swapMap_apply, tauT1_apply, sgnT1_swap]
  ring

theorem swapMap_eig1 : (eig1 (tauT1 F)).map (swapMap F : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F)) = eig2 (tauT1 F) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ eig1 (tauT1 F) := hx
    show swapMap F x ∈ eig2 (tauT1 F)
    rw [mem_eig2, tauT1_swap, mem_eig1.1 hx']
  · intro y hy
    refine ⟨swapMap F y, ?_, swapMap_swapMap y⟩
    show swapMap F y ∈ eig1 (tauT1 F)
    rw [mem_eig1, tauT1_swap, mem_eig2.1 hy, map_neg, neg_neg]


theorem invData_tauT1 [Finite F] (hodd : Odd (Nat.card F)) : InvData (pairedSympForm F 2) (tauT1 F) where
  two_ne_zero := two_ne_zero_of_odd_card hodd
  sq := tauT1_sq
  isometry := tauT1_isometry
  alt := pairedSympForm_isAlt
  nondeg := SymplecticFlag.pairedSympForm_nondegenerate
  finrank_eq := LinearEquiv.finrank_eq (LinearEquiv.ofSubmodules (swapMap F) (eig1 (tauT1 F)) (eig2 (tauT1 F)) swapMap_eig1)

theorem mem_statedSp_iff_toLin' {A : GL (Fin 2 ⊕ Fin 2) F} :
    A ∈ StatedSp 2 F ↔ Matrix.GeneralLinearGroup.toLin A ∈ bilinIsometryGroup (pairedSympForm F 2) := by
  rw [mem_bilinIsometryGroup]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  constructor
  · intro hA x y
    exact pairedSympForm_mulVec ⟨A, hA⟩ x y
  · intro h
    rw [SymplecticTorusWeyl.mem_statedSp_iff]
    have hB : (pairedSympForm F 2).comp (Matrix.toLin' (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
        (Matrix.toLin' (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) = pairedSympForm F 2 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply]
      exact h x y
    have hM := congrArg LinearMap.BilinForm.toMatrix' hB
    rw [LinearMap.BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin', pairedSympForm,
      LinearMap.BilinForm.toMatrix'_toBilin'] at hM
    exact hM


@[expose] noncomputable def toLinS (F : Type) [Field F] : StatedSp 2 F →* LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F) :=
  (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (StatedSp 2 F).subtype

theorem toLinS_injective : Function.Injective (toLinS F) :=
  fun _ _ h => Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective h)

theorem toLinS_mem (A : StatedSp 2 F) : toLinS F A ∈ bilinIsometryGroup (pairedSympForm F 2) :=
  mem_statedSp_iff_toLin'.1 A.2

theorem toLinS_surj {g : LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F)}
    (hg : g ∈ bilinIsometryGroup (pairedSympForm F 2)) : ∃ A : StatedSp 2 F, toLinS F A = g := by
  refine ⟨⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_⟩, ?_⟩
  · rw [mem_statedSp_iff_toLin', MulEquiv.apply_symm_apply]
    exact hg
  · exact Matrix.GeneralLinearGroup.toLin.apply_symm_apply g

theorem coe_toLinS (A : StatedSp 2 F) :
    ((toLinS F A : LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F)) : Module.End F (Fin 2 ⊕ Fin 2 → F)) =
      Matrix.mulVecLin ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  simp [toLinS]


@[expose] noncomputable def negOneSp (F : Type) [Field F] : StatedSp 2 F := toSp (-1) neg_one_symplectic

theorem proj_negOneSp : proj 2 F (negOneSp F) = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj]
  exact (mem_spScalars_iff _).mpr (Or.inr rfl)

theorem mulVecLin_mul_mulVecLin (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Matrix.mulVecLin M * Matrix.mulVecLin N = Matrix.mulVecLin (M * N) := by
  rw [Module.End.mul_eq_comp, Matrix.mulVecLin_mul]

theorem mulVecLin_injective' : Function.Injective (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => Matrix.mulVecLin M) := by
  intro M N h
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
  exact h


theorem commPm_toLinS_iff (A : StatedSp 2 F) :
    CommPm (tauT1 F) (toLinS F A) ↔ proj 2 F A ∈ centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F))) := by
  rw [Subgroup.mem_centralizer_singleton_iff, CommPm, coe_toLinS]
  have hτ : tauT1 F = Matrix.mulVecLin (blk (1 : Matrix (Fin 2) (Fin 2) F) (-1)) := rfl
  have hneg : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      -Matrix.mulVecLin M = Matrix.mulVecLin (-M) := by
    intro M
    rw [← Matrix.toLin'_apply', ← Matrix.toLin'_apply', map_neg]
  rw [hτ, mulVecLin_mul_mulVecLin, mulVecLin_mul_mulVecLin, hneg]
  constructor
  · rintro (h | h)
    · have h' := mulVecLin_injective' h
      have : A * T1 F = T1 F * A := sp_ext (by simpa [coe_T1] using h')
      change proj 2 F A * proj 2 F (T1 F) = proj 2 F (T1 F) * proj 2 F A
      rw [← map_mul, ← map_mul, this]
    · have h' := mulVecLin_injective' h
      have : A * T1 F = T1 F * A * negOneSp F := by
        apply sp_ext
        simp only [Subgroup.coe_mul, Units.val_mul, coe_T1]
        rw [show (((negOneSp F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 from rfl,
          Matrix.mul_neg, Matrix.mul_one]
        simpa [coe_T1] using h'
      change proj 2 F A * proj 2 F (T1 F) = proj 2 F (T1 F) * proj 2 F A
      rw [← map_mul, ← map_mul, this, map_mul, proj_negOneSp, mul_one]
  · intro h
    change proj 2 F A * proj 2 F (T1 F) = proj 2 F (T1 F) * proj 2 F A at h
    rw [← map_mul, ← map_mul] at h
    set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
    rcases eq_or_eq_neg_of_proj_eq h with h1 | h1
    · left
      have h2 : Am * blk 1 (-1) = blk 1 (-1) * Am := by
        have := h1.symm
        simp only [Subgroup.coe_mul, Units.val_mul, coe_T1] at this
        exact this
      rw [h2]
    · right
      have h2 : Am * blk 1 (-1) = -(blk 1 (-1) * Am) := by
        have := h1
        simp only [Subgroup.coe_mul, Units.val_mul, coe_T1] at this
        rw [this, neg_neg]
      rw [h2]


theorem isCoatom_centralizer_u1 [Finite F] (hodd : Odd (Nat.card F)) :
    IsCoatom (centralizer ({u1 F} : Set (StatedProj (StatedSp 2 F)))) := by
  have hInv := invData_tauT1 hodd
  refine ⟨?_, fun M hM => ?_⟩
  · intro htop
    let a₁ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1
    let a₂ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 1) 1
    have ha₁ : a₁ ∈ eig1 (tauT1 F) := by
      rw [mem_eig1]
      funext i
      rw [tauT1_apply]
      rcases i with i | i <;> fin_cases i <;> simp [a₁, sgnT1]
    have ha₂ : a₂ ∈ eig2 (tauT1 F) := by
      rw [mem_eig2]
      funext i
      rw [tauT1_apply]
      rcases i with i | i <;> fin_cases i <;> simp [a₂, sgnT1]
    have h₁ : a₁ ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl 0)
      simp [a₁] at this
    have h₂ : a₂ ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl 1)
      simp [a₂] at this
    have hnc := hInv.not_commPm_transvection ha₁ ha₂ h₁ h₂ (one_ne_zero (α := F))
    obtain ⟨A, hA⟩ := toLinS_surj (symplecticTransvection_mem_bilinIsometryGroup hInv.alt (a₁ + a₂) (1 : F))
    apply hnc
    rw [← hA, commPm_toLinS_iff, htop]
    exact Subgroup.mem_top _
  · let Mt : Subgroup (LinearMap.GeneralLinearGroup F (Fin 2 ⊕ Fin 2 → F)) :=
      (M.comap (proj 2 F)).map (toLinS F)
    have hMtG : Mt ≤ bilinIsometryGroup (pairedSympForm F 2) := by
      rintro _ ⟨A, -, rfl⟩
      exact toLinS_mem A
    have hC : ∀ g ∈ bilinIsometryGroup (pairedSympForm F 2), CommPm (tauT1 F) g → g ∈ Mt := by
      intro g hg hcomm
      obtain ⟨A, rfl⟩ := toLinS_surj hg
      exact ⟨A, hM.le ((commPm_toLinS_iff A).1 hcomm), rfl⟩
    rcases hInv.dichotomy Mt hMtG hC with hall | hMt
    · exfalso
      apply hM.2
      intro p hp
      obtain ⟨A, rfl⟩ := proj_surjective p
      exact (commPm_toLinS_iff A).1 (hall _ ⟨A, hp, rfl⟩)
    · rw [eq_top_iff]
      intro p _
      obtain ⟨A, rfl⟩ := proj_surjective p
      have hmem : toLinS F A ∈ Mt := hMt ▸ toLinS_mem A
      obtain ⟨A', hA', hAA'⟩ := hmem
      have := toLinS_injective hAA'
      rw [← this]
      exact hA'

end Model

section Leaf

theorem isCoatom_of_map_equiv {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) {C : Subgroup G}
    (h : IsCoatom (C.map ψ.toMonoidHom)) : IsCoatom C := by
  refine ⟨?_, fun M hM => ?_⟩
  · intro htop
    apply h.1
    rw [htop, Subgroup.map_top_of_surjective _ ψ.surjective]
  · have hlt : C.map ψ.toMonoidHom < M.map ψ.toMonoidHom := by
      refine ⟨Subgroup.map_mono hM.le, fun hle => hM.2 ?_⟩
      intro m hm
      have : ψ m ∈ C.map ψ.toMonoidHom := hle ⟨m, hm, rfl⟩
      obtain ⟨c, hc, hcm⟩ := this
      have : c = m := ψ.injective hcm
      rw [← this]
      exact hc
    have htop := h.2 _ hlt
    rw [eq_top_iff]
    intro m _
    have : ψ m ∈ M.map ψ.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcm⟩ := this
    have : c = m := ψ.injective hcm
    rw [← this]
    exact hc

theorem sp4Max : Sp4Max := by
  intro X _ _ K q u hset
  have : K.Normal := hset.normal
  obtain ⟨F, iF, fF, hFq, ⟨e⟩⟩ := hset.psp4
  have hodd : Odd (Nat.card F) := hFq ▸ hset.odd
  obtain ⟨P', hP'le, hperf, hcard⟩ := hset.big
  have hP'K : P' ≤ K := hP'le.trans inf_le_left
  have hP'u : P' ≤ centralizer ({u} : Set X) := hP'le.trans inf_le_right
  let uK : ↥K := ⟨u, hset.mem⟩
  have huK : orderOf uK = 2 := by
    rw [← hset.inv]
    exact (Subgroup.orderOf_coe uK).symm
  have hPu : P'.subgroupOf K ≤ centralizer ({uK} : Set ↥K) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpu : (p : X) * u = u * (p : X) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hP'u (Subgroup.mem_subgroupOf.1 hp))
    exact Subtype.ext hpu
  have hcardK : Nat.card F * (Nat.card F ^ 2 - 1) / 2 < Nat.card ↥(P'.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'K).toEquiv, hFq]
    exact hcard
  obtain ⟨g, hg⟩ := exists_conj_u1_of_big hodd e huK hPu (perfect_subgroupOf hP'K hperf) hcardK
  let ψ : ↥K ≃* StatedProj (StatedSp 2 F) := e.trans (MulAut.conj g⁻¹)
  have hψ : ψ uK = u1 F := by
    change (MulAut.conj g⁻¹) (e uK) = u1 F
    rw [MulAut.conj_apply]
    simpa using hg
  have hsub : (centralizer ({u} : Set X)).subgroupOf K = centralizer ({uK} : Set ↥K) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [hsub]
  refine isCoatom_of_map_equiv ψ ?_
  have hmap : (centralizer ({uK} : Set ↥K)).map ψ.toMonoidHom = centralizer ({ψ uK} : Set (StatedProj (StatedSp 2 F))) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      change ψ x * ψ uK = ψ uK * ψ x
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply ψ.injective
      rw [map_mul, map_mul, ψ.apply_symm_apply, hy]
  rw [hmap, hψ]
  exact isCoatom_centralizer_u1 hodd

end Leaf

end CFSG.GH74.GLS.Stage2.Local.P34
