module

public import CFSG.GH74.Generic.BProg.B2.FixFourS3
public import CFSG.GH74.Generic.BProg.B2.GenLocU3NF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74.Generic.BProg CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.GH74.KGroups.L3Eps.Uni
  CFSG.GH74.Generic.BProg.B2.GenLocU3Lift CFSG.Assembly.LowTwoRank
open scoped MatrixGroups
open Matrix
open Matrix.SpecialLinearGroup (toGL)

namespace FixFourS3U

section Frame

variable {K : Type} [Field K] {p f : ℕ}

theorem toGL_mem_unitarySU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {s : SL(3, K)}
    (hs : s ∈ FixFourS3.Vhat K) : toGL s ∈ unitarySU p f K 3 := by
  have hsq : toGL s * toGL s = 1 := by
    rw [← map_mul, hs.2, map_one]
  have hP := GenLocDiagU.mem_primeFormUnitary_of_diag_sq h hp2 (P := toGL s) hs.1 hsq
  have h1 := (mem_primeFormUnitary (h := h)).1 hP
  simp only [idGram, Units.val_one, Matrix.mul_one] at h1
  exact (mem_unitarySU_iff h).2 ⟨s.2, h1⟩

@[expose] def vhatToSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    ↥(FixFourS3.Vhat K) →* ↥(unitarySU p f K 3) where
  toFun s := ⟨toGL s.1, toGL_mem_unitarySU h hp2 s.2⟩
  map_one' := Subtype.ext (map_one toGL)
  map_mul' a b := Subtype.ext (map_mul toGL a.1 b.1)

theorem mem_primeFormUnitary_of_unitary (h : UnitaryFieldData p f K) {C : GL (Fin 3) K}
    (hC : ((C : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) K) = 1) :
    C ∈ primeFormUnitary h (idGram K 3) := by
  rw [mem_primeFormUnitary]
  simpa [idGram] using hC

@[expose] noncomputable def frameHom (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {J : Type} [Group J]
    (θ : ↥(unitarySU p f K 3) →* J) (C : ↥(primeFormUnitary h (idGram K 3))) :
    ↥(FixFourS3.Vhat K) →* J :=
  θ.comp ((KFU.conjSU h C).toMonoidHom.comp (vhatToSU h hp2))

theorem coe_conj_vhatToSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (C : ↥(primeFormUnitary h (idGram K 3))) (s : ↥(FixFourS3.Vhat K)) :
    (((KFU.conjSU h C) (vhatToSU h hp2 s) : ↥(unitarySU p f K 3)) : GL (Fin 3) K) =
      (C : GL (Fin 3) K) * toGL s.1 * (C : GL (Fin 3) K)⁻¹ := rfl

theorem glAut_toGL_vhat (ψ : K ≃+* K) {s : SL(3, K)} (hs : s ∈ FixFourS3.Vhat K) :
    glAut ψ (toGL s) = toGL s := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  simp only [Matrix.map_apply]
  change ψ ((s : Matrix (Fin 3) (Fin 3) K) i j) = (s : Matrix (Fin 3) (Fin 3) K) i j
  by_cases hij : i = j
  · subst hij
    rcases FixFourS3.Vhat_entry hs i with h1 | h1 <;> rw [h1] <;> simp
  · rw [hs.1 hij, map_zero]

theorem two_ne_zero_of_data (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  have hr : ringChar K = p := ringChar.eq K p
  exact Ring.two_ne_zero (by rw [hr]; exact hp2)

theorem frameHom_injective (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {J : Type} [Group J]
    {θ : ↥(unitarySU p f K 3) →* J} (hθ : IsCover h θ)
    (C : ↥(primeFormUnitary h (idGram K 3))) : Function.Injective (frameHom h hp2 θ C) := by
  have h2 := two_ne_zero_of_data h hp2
  rw [injective_iff_map_eq_one]
  intro a ha
  have hk : (KFU.conjSU h C) (vhatToSU h hp2 a) ∈ θ.ker := ha
  rw [hθ.ker, mem_unitaryScalars] at hk
  obtain ⟨c, -, hc3, hc⟩ := hk
  rw [coe_conj_vhatToSU] at hc
  have h1 : toGL a.1 = GeneralLinearGroup.scalar (Fin 3) c := by
    calc toGL a.1 = (C : GL (Fin 3) K)⁻¹ *
          ((C : GL (Fin 3) K) * toGL a.1 * (C : GL (Fin 3) K)⁻¹) * (C : GL (Fin 3) K) := by group
      _ = (C : GL (Fin 3) K)⁻¹ * GeneralLinearGroup.scalar (Fin 3) c * (C : GL (Fin 3) K) := by
          rw [hc]
      _ = GeneralLinearGroup.scalar (Fin 3) c * (C : GL (Fin 3) K)⁻¹ * (C : GL (Fin 3) K) := by
          rw [(commute_scalar c ((C : GL (Fin 3) K)⁻¹)).eq]
      _ = GeneralLinearGroup.scalar (Fin 3) c := inv_mul_cancel_right _ _
  have hc00 : (a.1 : Matrix (Fin 3) (Fin 3) K) 0 0 = (c : K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  have hcK : (c : K) = 1 := by
    have hc3' : (c : K) ^ 3 = 1 := by
      have := congrArg Units.val hc3
      simpa using this
    rcases FixFourS3.Vhat_entry a.2 0 with h0 | h0
    · rw [← hc00]; exact h0
    · exfalso
      rw [← hc00, h0] at hc3'
      apply h2
      linear_combination -hc3'
  have hc1 : c = 1 := Units.ext hcK
  rw [hc1, map_one] at h1
  exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective (h1.trans (map_one toGL).symm))

theorem frameForm_fixes (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {J : Type} [Group J]
    {θ : ↥(unitarySU p f K 3) →* J} {C : ↥(primeFormUnitary h (idGram K 3))} {x : MulAut J}
    (hx : FrameForm h θ (C : GL (Fin 3) K) x) (a : ↥(FixFourS3.Vhat K)) :
    x (frameHom h hp2 θ C a) = frameHom h hp2 θ C a := by
  obtain ⟨A, Δ, ψ, hl, -, -, hΔ, hAC⟩ := hx
  obtain ⟨g', hg'1, hg'2⟩ := hl ((KFU.conjSU h C) (vhatToSU h hp2 a))
  have hg' : g' = (KFU.conjSU h C) (vhatToSU h hp2 a) := by
    apply Subtype.ext
    rw [hg'1, coe_conj_vhatToSU]
    simp only [map_mul, map_inv, glAut_toGL_vhat ψ a.2]
    have hcomm : Δ * toGL a.1 = toGL a.1 * Δ := FixFourS3.diag_commute hΔ a.2.1
    calc A * (glAut ψ (C : GL (Fin 3) K) * toGL a.1 * (glAut ψ (C : GL (Fin 3) K))⁻¹) * A⁻¹
        = (A * glAut ψ (C : GL (Fin 3) K)) * toGL a.1 * (A * glAut ψ (C : GL (Fin 3) K))⁻¹ := by
          group
      _ = ((C : GL (Fin 3) K) * Δ) * toGL a.1 * ((C : GL (Fin 3) K) * Δ)⁻¹ := by rw [hAC]
      _ = (C : GL (Fin 3) K) * (Δ * toGL a.1) * Δ⁻¹ * (C : GL (Fin 3) K)⁻¹ := by group
      _ = (C : GL (Fin 3) K) * (toGL a.1 * Δ) * Δ⁻¹ * (C : GL (Fin 3) K)⁻¹ := by rw [hcomm]
      _ = (C : GL (Fin 3) K) * toGL a.1 * (C : GL (Fin 3) K)⁻¹ := by group
  show x (θ ((KFU.conjSU h C) (vhatToSU h hp2 a))) = θ ((KFU.conjSU h C) (vhatToSU h hp2 a))
  rw [← hg'2, hg']

theorem exists_fixedFour_of_frameForm [Finite K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {J : Type} [Group J] {θ : ↥(unitarySU p f K 3) →* J} (hθ : IsCover h θ) {C : GL (Fin 3) K}
    (hC : ((C : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) K) = 1)
    {x : MulAut J} (hx : FrameForm h θ C x) :
    ∃ E : Subgroup J, CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧ ∀ e ∈ E, x e = e := by
  have h2 := two_ne_zero_of_data h hp2
  let Cu : ↥(primeFormUnitary h (idGram K 3)) := ⟨C, mem_primeFormUnitary_of_unitary h hC⟩
  refine ⟨(frameHom h hp2 θ Cu).range, ?_, ?_, ?_⟩
  · refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
    · obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (FixFourS3.sl_diag_commute K a.2.1 b.2.1))
    · obtain ⟨a, rfl⟩ := hu
      have haa : a * a = 1 := Subtype.ext a.2.2
      rw [← map_mul, haa, map_one]
  · rw [← FixFourS3.card_Vhat h2]
    exact (Nat.card_congr (MonoidHom.ofInjective (frameHom_injective h hp2 hθ Cu)).toEquiv).symm
  · rintro _ ⟨a, rfl⟩
    exact frameForm_fixes h hp2 hx a

end Frame

section Cover

variable {K : Type} [Field K] {p f : ℕ}

theorem conj_injective_of_center_trivial {J : Type} [Group J]
    (hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  intro g h hgh
  have hc : ∀ x : J, g * x * g⁻¹ = h * x * h⁻¹ := fun x => by
    simpa [MulAut.conj_apply] using congrArg (fun φ : MulAut J => φ x) hgh
  have := hZ (h⁻¹ * g) fun x => by
    have := hc x
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [this]
      _ = (h⁻¹ * g) * x := by group
  exact (inv_mul_eq_one.1 this).symm

theorem isCover_of_equiv (h : UnitaryFieldData p f K) {J : Type} [Group J]
    (ψ : J ≃* unitaryPSU h 3) :
    IsCover h (ψ.symm.toMonoidHom.comp (unitaryProj h 3)) := by
  refine ⟨ψ.symm.surjective.comp (unitaryProj_surjective h 3), ?_⟩
  ext g
  change ψ.symm (unitaryProj h 3 g) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]

theorem conj_injective_of_isCover (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {J : Type}
    [Group J] {θ : ↥(unitarySU p f K 3) →* J} (hθ : IsCover h θ) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f K 3) := by
    rw [hθ.ker]; exact unitaryScalars_le_center h 3
  obtain ⟨hPerf, hcen⟩ := CFSG.GH74.Generic.S45.isPerfect_and_center_unitarySU' h hp2 (le_refl 3)
  have hZ : ∀ z : J, (∀ g : J, g * z = z * g) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun g => hz g
    rw [← CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.map_center_eq_center_of_perfect hθ.surj
      hker, hcen] at hzc
    obtain ⟨w, hw, rfl⟩ := hzc
    have : w ∈ θ.ker := by rw [hθ.ker]; exact hw
    exact this
  exact conj_injective_of_center_trivial hZ

end Cover

section EA

theorem isElementaryAbelian_zpowers {G : Type} [Group G] {a : G} (ha : a * a = 1) :
    CFSG.IsElementaryAbelian 2 ↥(Subgroup.zpowers a) := by
  refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu v hv => ?_) (fun u hu => ?_)
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow_self a m n).eq
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
    rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, ha2, _root_.one_zpow]

theorem isElementaryAbelian_map {G H : Type} [Group G] [Group H] (φ : G →* H) {E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian 2 ↥E) : CFSG.IsElementaryAbelian 2 ↥(E.map φ) := by
  obtain ⟨hcomm, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hE
  refine WeakSigGen.isElementaryAbelian_of_forall (fun u hu w hw => ?_) (fun u hu => ?_)
  · obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hw
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · obtain ⟨a, ha, rfl⟩ := hu
    rw [← map_mul, hsq a ha, map_one]

end EA

end FixFourS3U

theorem involFixFourSU3_proved : FixFourS3.InvolFixFourSU3 := by
  intro K _ _ p f hp hp2 hK X _ _ L _ e y hy
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  let ψ : ↥L ≃* unitaryPSU h 3 := e.trans (unitaryPSUEquiv h (by norm_num)).symm
  let θ : ↥(unitarySU p f K 3) →* ↥L := ψ.symm.toMonoidHom.comp (unitaryProj h 3)
  have hθ : IsCover h θ := FixFourS3U.isCover_of_equiv h ψ
  have hinj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) :=
    FixFourS3U.conj_injective_of_isCover h hp2 hθ
  have hq3 : 3 ≤ p ^ f := by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    exact h3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  let α : MulAut ↥L := MulAut.conjNormal y
  have hα2 : α * α = 1 := by rw [← map_mul, hy2, map_one]
  let D : Subgroup (MulAut ↥L) := Subgroup.zpowers α
  have hD : CFSG.IsElementaryAbelian 2 ↥D := FixFourS3U.isElementaryAbelian_zpowers hα2
  obtain ⟨C, hCu, hC⟩ : ∃ C : GL (Fin 3) K,
      ((C : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (C : Matrix (Fin 3) (Fin 3) K) = 1 ∧
        ∀ x ∈ D, FrameForm h θ C x := by
    by_cases hout : ∃ u ∈ D, ∀ z : ↥L, MulAut.conj z ≠ u
    · obtain ⟨u, huD, hu⟩ := hout
      exact GenLocU3NF.exists_frame h hp2 hq3 hθ hinj hD huD hu
    · push Not at hout
      exact GenLocU3NF.exists_frame_inner h hp2 hθ hinj hD hout
  obtain ⟨E, hEa, hEc, hEfix⟩ :=
    FixFourS3U.exists_fixedFour_of_frameForm h hp2 hθ hCu (hC α (Subgroup.mem_zpowers α))
  refine ⟨E.map L.subtype, ?_, FixFourS3U.isElementaryAbelian_map L.subtype hEa, ?_, ?_⟩
  · rintro _ ⟨l, -, rfl⟩
    exact l.2
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]
  · rintro _ ⟨l, hl, rfl⟩
    have h1 : MulAut.conjNormal y l = l := hEfix l hl
    have h4 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h4
    show y * (l : X) = (l : X) * y
    calc y * (l : X) = y * (l : X) * y⁻¹ * y := by group
      _ = (l : X) * y := by rw [h4]

theorem involFixFour_shape3_proved : InvolFixFour QShape3 :=
  FixFourS3.involFixFour_shape3 involFixFourSU3_proved

end CFSG.GH74.Generic.BProg.B2
