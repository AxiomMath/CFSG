module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25U02
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMB01
public import CFSG.ClassicalInvolution.Asc77.AscC5P2
public import CFSG.ClassicalInvolution.Asc77.AscC25W12

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.CX.Sp
open CFSG.ClassicalInvolution.Asc77
open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic
open CFSG.Open (classicalInvolutionOddCore)

variable {F : Type} [Field F]

theorem isSimpleGroup_of_twin3 [Finite F] (h2 : (2 : F) ≠ 0) (h3 : Nat.card F = 3) {Y : Type}
    [Group Y] (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    IsSimpleGroup Y := by
  have hk := C25W.Sp.ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  have hsimp : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inr (Or.inl ⟨h3, le_rfl⟩))
  exact (C25W.Sp.projEquiv ψ hsurj hk).symm.isSimpleGroup

end Asc77.CX.Sp

namespace Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.CX
open scoped MatrixGroups

section Simple

variable {p : ℕ} [Fact p.Prime]


theorem isSimpleGroup_of_hom3 (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (h3 : p ^ e = 3)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') : IsSimpleGroup Y := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  have h2 := C25W.two_ne_zero_gf (p := p) e hp2
  have h4 : Nat.card (GaloisField p e) = 3 := by
    rw [GaloisField.card p e he]
    exact h3
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact Sp.isSimpleGroup_of_twin3 h2 h4 ψ hker hsurj hi hi' hne hz hz'

end Simple

section Om5


theorem isSimpleGroup_of_om5Data {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    {A A' : Subgroup Y} {z' a₀ b₀ : Y} (h : C5O.Om5Data Y Φ A A' z' a₀ b₀) :
    IsSimpleGroup Y := by
  obtain ⟨D, hD1, i, hi⟩ := h.lie
  have htw := h.twin
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : ∀ j : Fin D.card, Function.Surjective (D.hom j) := by
    intro j
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom j).range := by
      intro l
      rw [Subsingleton.elim l j]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : ∀ j : Fin D.card, D.tag j = .PSp ∧ D.rank j = 2 := by
    intro j
    rw [Subsingleton.elim j i]
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : ∀ j : Fin D.card, D.exp j = 1 := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 3 ^ D.exp i₂ = 3 := by rw [hexp i₂]; norm_num
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  exact isSimpleGroup_of_hom3 (by norm_num : (3 : ℕ) ≠ 2) (D.tag i₂) (D.rank i₂) (D.exp i₂)
    (D.admissible i₂) (D.hom i₂) (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq'
    hR hR' hne hz hz'

end Om5

section Diag

open CFSG.ClassicalInvolution.Asc77.C5P (TwoClasses twoClasses_of_mulEquiv twoClasses_sl2
  diagTriv_trans_of_not)
open CFSG.ClassicalInvolution.Models.SymplecticPairs


theorem exists_sl2_equiv_of_isOm5 {K₀ K₀' : Type} [Group K₀] [Group K₀'] {L : TwinGroup K₀ K₀'}
    (hL : IsOm5 L) :
    Nonempty (K₀ ≃* SL(2, GaloisField 3 1)) ∧ Nonempty (K₀' ≃* SL(2, GaloisField 3 1)) := by
  obtain ⟨Φ, z', a₀, b₀, hD⟩ := hL
  obtain ⟨fr⟩ := C5O.M.exists_frame hD
  have h2 : (2 : GaloisField 3 1) ≠ 0 := C5O.M.two_ne_zero_gf 1 (by norm_num)
  have key : ∀ (k : Fin 2) (B : Subgroup L.X),
      B = (longRootSp2 (GaloisField 3 1) 2 k).map fr.ψ →
        Nonempty (SL(2, GaloisField 3 1) ≃* B) := by
    intro k B hB
    have hinj : Function.Injective (fr.ψ.comp (longBlock (GaloisField 3 1) 2 k)) := by
      intro x y hxy
      apply longBlock_injective k
      exact fr.injOn_L h2 k ⟨x, rfl⟩ ⟨y, rfl⟩ hxy
    have hrange : (fr.ψ.comp (longBlock (GaloisField 3 1) 2 k)).range = B := by
      rw [hB, MonoidHom.range_comp]
      rfl
    exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩
  obtain ⟨eA⟩ := key 0 L.A fr.hA
  obtain ⟨eA'⟩ := key 1 L.A' fr.hA'
  exact ⟨⟨L.ι.trans eA.symm⟩, ⟨L.ι'.trans eA'.symm⟩⟩


theorem exists_twin_iso {K₀ K₀' : Type} [Group K₀] [Group K₀'] {L₁ L₂ : TwinGroup K₀ K₀'}
    (h₁ : IsOm5 L₁) (h₂ : IsOm5 L₂) :
    ∃ φ : L₁.X ≃* L₂.X, L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A ∧
      L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A' := by
  obtain ⟨Φ₁, z₁, a₁, b₁, hD₁⟩ := h₁
  obtain ⟨Φ₂, z₂, a₂, b₂, hD₂⟩ := h₂
  obtain ⟨fr₁⟩ := C5O.M.exists_frame hD₁
  obtain ⟨fr₂⟩ := C5O.M.exists_frame hD₂
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective fr₁.ψ fr₁.surj
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective fr₂.ψ fr₂.surj
  let e := QuotientGroup.quotientMulEquivOfEq (fr₁.ker.trans fr₂.ker.symm)
  let φ : L₁.X ≃* L₂.X := e₁.symm.trans (e.trans e₂)
  have hφ : ∀ s, φ (fr₁.ψ s) = fr₂.ψ s := by
    intro s
    have h1 : e₁.symm (fr₁.ψ s) = QuotientGroup.mk s := by
      rw [MulEquiv.symm_apply_eq]; rfl
    show e₂ (e (e₁.symm (fr₁.ψ s))) = fr₂.ψ s
    rw [h1]
    rfl
  have hmap : ∀ k : Fin 2, ((longRootSp2 (GaloisField 3 1) 2 k).map fr₁.ψ).map
      (φ : L₁.X →* L₂.X) = (longRootSp2 (GaloisField 3 1) 2 k).map fr₂.ψ := by
    intro k
    rw [Subgroup.map_map]
    congr 1
    ext s
    exact hφ s
  exact ⟨φ, by rw [fr₁.hA, fr₂.hA, hmap], by rw [fr₁.hA', fr₂.hA', hmap]⟩


theorem diagThree_proved : DiagThree := by
  classical
  intro K₀ K₀' _ _ L₁ L₂ L₃ h₁ h₂ h₃
  obtain ⟨⟨eK⟩, ⟨eK'⟩⟩ := exists_sl2_equiv_of_isOm5 h₁
  have h2 : (2 : GaloisField 3 1) ≠ 0 := C5O.M.two_ne_zero_gf 1 (by norm_num)
  have hchar : ringChar (GaloisField 3 1) = 3 := ringChar.eq (GaloisField 3 1) 3
  have hTC : TwoClasses 3 K₀ := by
    have := twoClasses_of_mulEquiv eK (twoClasses_sl2 h2)
    rwa [hchar] at this
  have hTC' : TwoClasses 3 K₀' := by
    have := twoClasses_of_mulEquiv eK' (twoClasses_sl2 h2)
    rwa [hchar] at this
  obtain ⟨φ₁₂, hA₁₂, hA'₁₂⟩ := exists_twin_iso h₁ h₂
  obtain ⟨φ₂₃, hA₂₃, hA'₂₃⟩ := exists_twin_iso h₂ h₃
  by_cases h12 : DiagRel 3 L₁ L₂
  · exact Or.inl h12
  by_cases h23 : DiagRel 3 L₂ L₃
  · exact Or.inr (Or.inr h23)
  refine Or.inr (Or.inl ⟨φ₁₂.trans φ₂₃, TwinGroup.map_trans φ₁₂ φ₂₃ hA₁₂ hA₂₃,
    TwinGroup.map_trans φ₁₂ φ₂₃ hA'₁₂ hA'₂₃, ?_⟩)
  have n12 : ¬ (DiagTriv 3 (TwinGroup.restr φ₁₂ hA₁₂) ↔
      DiagTriv 3 (TwinGroup.restr' φ₁₂ hA'₁₂)) := fun h => h12 ⟨φ₁₂, hA₁₂, hA'₁₂, h⟩
  have n23 : ¬ (DiagTriv 3 (TwinGroup.restr φ₂₃ hA₂₃) ↔
      DiagTriv 3 (TwinGroup.restr' φ₂₃ hA'₂₃)) := fun h => h23 ⟨φ₂₃, hA₂₃, hA'₂₃, h⟩
  rw [TwinGroup.restr_trans φ₁₂ φ₂₃ hA₁₂ hA₂₃,
    TwinGroup.restr'_trans φ₁₂ φ₂₃ hA'₁₂ hA'₂₃]
  have flip1 : ∀ {P Q : Prop}, ¬ (P ↔ Q) → P → ¬ Q := fun h hP hQ => h ⟨fun _ => hQ, fun _ => hP⟩
  have flip2 : ∀ {P Q : Prop}, ¬ (P ↔ Q) → ¬ P → Q := fun h hP => by
    by_contra hQ; exact h ⟨fun h' => absurd h' hP, fun h' => absurd h' hQ⟩
  by_cases ha : DiagTriv 3 (TwinGroup.restr φ₁₂ hA₁₂) <;>
    by_cases hb : DiagTriv 3 (TwinGroup.restr φ₂₃ hA₂₃)
  · have ha' := flip1 n12 ha
    have hb' := flip1 n23 hb
    exact ⟨fun _ => diagTriv_trans_of_not hTC' ha' hb',
      fun _ => (diagTriv_trans_iff_left hb).mpr ha⟩
  · have ha' := flip1 n12 ha
    have hb' := flip2 n23 hb
    rw [diagTriv_trans_iff_right ha, diagTriv_trans_iff_left hb']
    exact ⟨fun h => absurd h hb, fun h => absurd h ha'⟩
  · have ha' := flip2 n12 ha
    have hb' := flip1 n23 hb
    rw [diagTriv_trans_iff_left hb, diagTriv_trans_iff_right ha']
    exact ⟨fun h => absurd h ha, fun h => absurd h hb'⟩
  · have ha' := flip2 n12 ha
    have hb' := flip2 n23 hb
    exact ⟨fun _ => (diagTriv_trans_iff_left hb').mpr ha',
      fun _ => diagTriv_trans_of_not hTC ha hb⟩

end Diag

end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
