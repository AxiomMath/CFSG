module

public import CFSG.ClassicalInvolution.Asc77.AscCX9Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic
open CFSG.Open (classicalInvolutionOddCore)

variable {F : Type} [Field F]

theorem isSimpleGroup_of_twin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {Y : Type}
    [Group Y] (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    IsSimpleGroup Y := by
  have hk := C25W.Sp.ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  have hsimp : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr h4))
  exact (C25W.Sp.projEquiv ψ hsurj hk).symm.isSimpleGroup

end CFSG.ClassicalInvolution.Asc77.CX.Sp

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap

section Simple

variable {p f : ℕ} [Fact p.Prime]


theorem isSimpleGroup_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (hq : 5 ≤ p ^ e)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') : IsSimpleGroup Y := by
  subst ht hk
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 := C25W.two_ne_zero_gf (p := p) e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  obtain ⟨P, hP, hRP⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  obtain ⟨P', hP', hRP'⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'
  obtain ⟨i, hi⟩ := (exists_isLongRootSp2_iff h2 R).mpr ⟨P, hP, hRP⟩
  obtain ⟨i', hi'⟩ := (exists_isLongRootSp2_iff h2 R').mpr ⟨P', hP', hRP'⟩
  exact Sp.isSimpleGroup_of_twin h2 h4 ψ hker hsurj hi hi' hne hz hz'

theorem isSimpleGroup_of_om5Data {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}
    {A A' : Subgroup Y} {z' a₀ b₀ : Y} (h : C5O.Om5Data p f Y Φ A A' z' a₀ b₀) :
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
  have hexp : ∀ j : Fin D.card, D.exp j = f := by
    intro j
    rcases D.exp_eq j with h | ⟨hT, -⟩
    · exact h
    · rw [(hcase j).1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A htw.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' htw.hA'
  have h₂₁ : i₂ = i₁ := Subsingleton.elim _ _
  subst h₂₁
  have hq' : 5 ≤ p ^ D.exp i₂ := by rw [hexp i₂]; exact h.five
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  exact isSimpleGroup_of_hom h.odd (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂)
    (D.hom i₂) (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz'

end Simple

section Fix

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_map_subtype_self {K : Subgroup G} (H : Subgroup ↥K) :
    (H.map K.subtype).subgroupOf K = H := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.mem_map_iff_mem K.subtype_injective

theorem map_fix_eq {X : Subgroup G} {b : G} (hb2 : b * b = 1) (hb : conjSub b X = X) :
    ((X ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf X).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) =
      fixSubgroup (C25Y.layerAut X hb) := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have hyb : (y : G) * b = b * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hy).2
    show C25Y.layerAut X hb (QuotientGroup.mk' _ y) = QuotientGroup.mk' _ y
    rw [QuotientGroup.mk'_apply, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    rw [C25Y.coe_conjOnSub, ← hyb, mul_inv_cancel_right]
  · intro yb hyb
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective yb
    have hfix : C25Y.layerAut X hb (QuotientGroup.mk y₀) = QuotientGroup.mk y₀ := hyb
    rw [C25Y.layerAut_mk, QuotientGroup.eq] at hfix
    have hOodd : Odd (Nat.card (oddCoreOf X)) := by
      unfold oddCoreOf
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact CFSG.ComponentClassification.OddCore.odd_card ↥X
    have hconj : ∀ a ∈ Subgroup.zpowers b, conjSub a X = X := by
      intro a ha
      rcases eq_one_or_eq_of_mem_zpowers hb2 ha with h | h
      · rw [h, conjSub_one]
      · rw [h]
        exact hb
    have hAN : ∀ a ∈ Subgroup.zpowers b, ∀ n ∈ oddCoreOf X, a * n * a⁻¹ ∈ oddCoreOf X := by
      intro a ha n hn
      have h1 : a * n * a⁻¹ ∈ conjSub a (oddCoreOf X) := Generic.conj_mem_conjSub hn
      rwa [← Thompson.oddCoreOf_conjSub_eq, hconj a ha] at h1
    have hx : ∀ a ∈ Subgroup.zpowers b, (y₀ : G)⁻¹ * (a * y₀ * a⁻¹) ∈ oddCoreOf X := by
      intro a ha
      rcases eq_one_or_eq_of_mem_zpowers hb2 ha with h | h
      · rw [h]
        simp
      · rw [h]
        refine Subgroup.mem_map.mpr ⟨_, (classicalInvolutionOddCore ↥X).inv_mem hfix, ?_⟩
        simp only [Subgroup.subtype_apply, Subgroup.coe_inv, Subgroup.coe_mul,
          C25Y.coe_conjOnSub]
        group
    obtain ⟨n, hn, hfixn⟩ := exists_fixed_mem_coset_of_isPGroup
      (isPGroup_zpowers_of_sq_eq_one hb2) hOodd hAN hx
    have hnX : n ∈ X := Subgroup.map_subtype_le _ hn
    have hy₁X : (y₀ : G) * n ∈ X := X.mul_mem y₀.2 hnX
    have hy₁C : (y₀ : G) * n ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hfixn b (Subgroup.mem_zpowers b)
      calc (y₀ : G) * n * b = b * ((y₀ : G) * n) * b⁻¹ * b := by rw [h1]
        _ = b * ((y₀ : G) * n) := by group
    refine ⟨⟨(y₀ : G) * n, hy₁X⟩, Subgroup.mem_subgroupOf.mpr ⟨hy₁X, hy₁C⟩, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨n', hn', hn'n⟩ := Subgroup.mem_map.mp hn
    have e : (⟨(y₀ : G) * n, hy₁X⟩ : ↥X)⁻¹ * y₀ = n'⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((n' : ↥X) : G) = n from hn'n]
      group
    rw [e]
    exact (classicalInvolutionOddCore ↥X).inv_mem hn'

theorem map_perfRes_fix_eq {X : Subgroup G} {b : G} (hb2 : b * b = 1) (hb : conjSub b X = X) :
    ((Goldschmidt75.perfRes (X ⊓ Subgroup.centralizer ({b} : Set G))).subgroupOf X).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) =
      Goldschmidt75.perfRes (fixSubgroup (C25Y.layerAut X hb)) := by
  have hMX : X ⊓ Subgroup.centralizer ({b} : Set G) ≤ X := inf_le_left
  have h1 : (Goldschmidt75.perfRes (X ⊓ Subgroup.centralizer ({b} : Set G))).subgroupOf X =
      Goldschmidt75.perfRes ((X ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf X) := by
    have h2 := Goldschmidt75.map_perfRes X.subtype
      ((X ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf X)
    rw [Subgroup.map_subgroupOf_eq_of_le hMX] at h2
    rw [← h2, subgroupOf_map_subtype_self]
  rw [h1, Goldschmidt75.map_perfRes, map_fix_eq hb2 hb]

end Fix

end CFSG.ClassicalInvolution.Asc77.CX
