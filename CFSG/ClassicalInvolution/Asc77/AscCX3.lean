module

public import CFSG.ClassicalInvolution.Asc77.AscC25W12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_one_of_mem_longRoot_of_mem_spScalars {R : Subgroup (StatedSp 2 F)} {i : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) {x : StatedSp 2 F} (hxR : x ∈ R) (hx : x ∈ spScalars 2 F) :
    x = 1 := by
  obtain ⟨k, g, rfl, -⟩ := hR
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxR
  obtain ⟨c, hc⟩ := C25W.Sp.scalar_of_mem_spScalars hx
  obtain ⟨B, rfl⟩ := hy
  have hcen : (MulAut.conj g).toMonoidHom (longBlock F 2 k B) ∈
      Subgroup.center (StatedSp 2 F) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    exact hx
  have hfix : (MulAut.conj g).toMonoidHom (longBlock F 2 k B) = longBlock F 2 k B := by
    have h1 := Subgroup.mem_center_iff.mp hcen g
    change g * (g * longBlock F 2 k B * g⁻¹) = (g * longBlock F 2 k B * g⁻¹) * g at h1
    change g * longBlock F 2 k B * g⁻¹ = longBlock F 2 k B
    calc g * longBlock F 2 k B * g⁻¹ = g⁻¹ * (g * (g * longBlock F 2 k B * g⁻¹)) := by group
      _ = g⁻¹ * ((g * longBlock F 2 k B * g⁻¹) * g) := by rw [h1]
      _ = longBlock F 2 k B := by group
  rw [hfix] at hc ⊢
  have hsupp := isSupp_longBlock k B
  have hrk : (Sum.inl (Fin.rev k) : Fin 2 ⊕ Fin 2) ∉ coords k := by
    intro h
    rcases mem_coords.1 h with h | h
    · fin_cases k <;> simp_all
    · exact Sum.inl_ne_inr h
  have h1 := hsupp (Sum.inl (Fin.rev k)) (Sum.inl (Fin.rev k)) (fun h => hrk h.1)
  rw [hc] at h1
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
  apply mat_injective
  rw [hc, h1, one_smul, map_one]

theorem oddCoreOf_map_longRoot_eq_bot [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : StatedSp 2 F →* Y)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {R : Subgroup (StatedSp 2 F)}
    {i : StatedSp 2 F} (hR : IsLongRootSp2 R i) :
    Asc77.oddCoreOf (R.map ψ) = ⊥ := by
  have hinj : Function.Injective (ψ.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxk : (x : StatedSp 2 F) ∈ ψ.ker := hx
    have hxc := hker hxk
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F] at hxc
    exact Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_mem_longRoot_of_mem_spScalars hR x.2 hxc))
  have hrange : (ψ.comp R.subtype).range = R.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := (hR.isClassicalSL2 h2).nonempty_mulEquiv
  let e₁ : ↥(R.map ψ) ≃* SL(2, F) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e
  have hO : classicalInvolutionOddCore ↥(R.map ψ) = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e₁
    have h3 : classicalInvolutionOddCore SL(2, F) = ⊥ :=
      CFSG.ClassicalInvolution.ModelFacts.LinearAut.oddCore_sl2_eq_bot h2 h4
    have h4' : (classicalInvolutionOddCore ↥(R.map ψ)).map e₁.toMonoidHom = ⊥ := by
      rw [← h3]
      exact h1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e₁.injective] at h4'
  unfold Asc77.oddCoreOf
  rw [hO, Subgroup.map_bot]

theorem center_eq_bot_of_twin [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {Y : Type}
    [Group Y] (ψ : StatedSp 2 F →* Y) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hsurj : Function.Surjective ψ) {R R' : Subgroup (StatedSp 2 F)} {i i' : StatedSp 2 F}
    (hR : IsLongRootSp2 R i) (hR' : IsLongRootSp2 R' i') (hne : R.map ψ ≠ R'.map ψ) {z' : Y}
    (hz : IsUniqueInvolution (R.map ψ) z') (hz' : IsUniqueInvolution (R'.map ψ) z') :
    Subgroup.center Y = ⊥ := by
  have hk := C25W.Sp.ker_eq_spScalars h2 ψ hker hR hR' hne hz hz'
  set e := C25W.Sp.projEquiv ψ hsurj hk with he
  have hsimp : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hperfP : Group.IsPerfect (StatedProj (StatedSp 2 F)) :=
    Group.IsPerfect.ofSurjective (f := proj 2 F) proj_surjective
  have hcP : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp 2 F)))
      with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : StatedProj (StatedSp 2 F), a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      have hbot : ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))),
          (⊤ : Subgroup (StatedProj (StatedSp 2 F)))⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        exact Subgroup.mem_centralizer_iff.mpr fun y _ => (hcomm y x)
      have htop : ⁅(⊤ : Subgroup (StatedProj (StatedSp 2 F))),
          (⊤ : Subgroup (StatedProj (StatedSp 2 F)))⁆ = ⊤ := hperfP.commutator_eq_top
      have : (⊤ : Subgroup (StatedProj (StatedSp 2 F))) = ⊥ := htop.symm.trans hbot
      exact (IsSimpleGroup.toNontrivial).exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by
          have ha' : a ∈ (⊥ : Subgroup _) := this ▸ Subgroup.mem_top a
          have hb' : b ∈ (⊥ : Subgroup _) := this ▸ Subgroup.mem_top b
          rw [Subgroup.mem_bot] at ha' hb'
          rw [ha', hb'])
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (e g)
  rw [hcP, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply x, hx', map_one]

end CFSG.ClassicalInvolution.Asc77.CX.Sp

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {p f : ℕ} [Fact p.Prime]


theorem layer5_facts_of_hom (hp2 : p ≠ 2) {Y : Type} [Group Y] (t : StatedLieTag) (k e : ℕ)
    (hadm : StatedLieAdmissible t k p e) (ψ : (modelUniv t k p e Fact.out).K →* Y)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    (hsurj : Function.Surjective ψ) (ht : t = .PSp) (hk : k = 2) (hq : 5 ≤ p ^ e)
    {R R' : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D)
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    Subgroup.center Y = ⊥ ∧ oddCoreOf (R.map ψ) = ⊥ ∧ oddCoreOf (R'.map ψ) = ⊥ := by
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
  exact ⟨Sp.center_eq_bot_of_twin h2 h4 ψ hker hsurj hi hi' hne hz hz',
    Sp.oddCoreOf_map_longRoot_eq_bot h2 h4 ψ hker hi,
    Sp.oddCoreOf_map_longRoot_eq_bot h2 h4 ψ hker hi'⟩

theorem layer5_facts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Y : Type} [Group Y]
    {Φ : Set (Subgroup Y)} (D : LieSystemData p f Y Φ) {A A' : Subgroup Y} {z' a₀ b₀ : Y}
    (hD1 : D.card = 1) (hi : ∃ i : Fin D.card, IsOrthTag 5 true (D.tag i) (D.rank i))
    (htw : TwinSect0 Φ A A' z' a₀ b₀) :
    Subgroup.center Y = ⊥ ∧ oddCoreOf A = ⊥ ∧ oddCoreOf A' = ⊥ := by
  obtain ⟨i, hi⟩ := hi
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
  have hq' : 5 ≤ p ^ D.exp i₂ := by rw [hexp i₂]; exact hq
  have hz : IsUniqueInvolution (R.map (D.hom i₂)) z' := by
    rw [← hAR]
    exact htw.hzA
  have hz' : IsUniqueInvolution (R'.map (D.hom i₂)) z' := by
    rw [← hAR']
    exact htw.hzA'
  have hne : R.map (D.hom i₂) ≠ R'.map (D.hom i₂) := by
    rw [← hAR, ← hAR']
    exact htw.ne
  rw [hAR, hAR']
  exact layer5_facts_of_hom hp2 (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible i₂) (D.hom i₂)
    (D.ker_le_center i₂) (hsurj i₂) (hcase i₂).1 (hcase i₂).2 hq' hR hR' hne hz hz'

end CFSG.ClassicalInvolution.Asc77.CX
