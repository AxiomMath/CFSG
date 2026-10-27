module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Ker

variable {Y : Type} [Group Y] [Finite Y] {Ω P : Set (Subgroup Y)}

theorem label_not_of_same {n : ℕ} (hn : 5 ≤ n) (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hPΩ : P ⊆ Ω) (I : AEIdent P n) (hk : IsPGroup 2 I.φ.ker) {B C : Subgroup Y} (hB : B ∈ P)
    (hC : C ∈ P) (hne : B ≠ C) {α : Finset (Fin n)} {h : α.card = 4} {b c : Bool}
    (hlB : (B.subgroupOf (pSpan P)).map I.φ = memBar α h b)
    (hlC : (C.subgroupOf (pSpan P)).map I.φ = memBar α h c) : c = !b := by
  by_contra hcb
  have : c = b := by cases b <;> cases c <;> simp_all
  subst this
  exact hne (aeIdent_eq_of_map_eq hΩ h2 hPΩ hn I hk hB hC (hlB.trans hlC.symm))

theorem twin_structure (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 8)
    (hPΩ : P ⊆ Ω) (I : AEIdent P 8) (hk : IsPGroup 2 I.φ.ker) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y}
    (F : FourTwins P z A₁ A₂ A₃ A₄) :
    (∃ (B C : Subgroup Y) (δ : Finset (Fin 8)) (hδ : δ.card = 4) (c : Bool), B ∈ P ∧ C ∈ P ∧
      IsUniqueInvolution B z ∧ IsUniqueInvolution C z ∧
      (B.subgroupOf (pSpan P)).map I.φ = memBar δ hδ c ∧
      (C.subgroupOf (pSpan P)).map I.φ = memBar δ hδ (!c)) ∧
    (∃ (B C : Subgroup Y) (α β : Finset (Fin 8)) (hα : α.card = 4) (hβ : β.card = 4) (b c : Bool),
      B ∈ P ∧ C ∈ P ∧ IsUniqueInvolution B z ∧ IsUniqueInvolution C z ∧
      (B.subgroupOf (pSpan P)).map I.φ = memBar α hα b ∧
      (C.subgroupOf (pSpan P)).map I.φ = memBar β hβ c ∧ α ≠ β) := by
  have hn : 5 ≤ 8 := by norm_num
  obtain ⟨α₁, h₁, b₁, hl₁⟩ := I.label A₁ F.m₁
  obtain ⟨α₂, h₂', b₂, hl₂⟩ := I.label A₂ F.m₂
  obtain ⟨α₃, h₃, b₃, hl₃⟩ := I.label A₃ F.m₃
  obtain ⟨α₄, h₄, b₄, hl₄⟩ := I.label A₄ F.m₄
  have e₁ := I.map_eq_zBar hn F.m₁ (h8 _ (hPΩ F.m₁)) hl₁ F.z₁
  have e₂ := I.map_eq_zBar hn F.m₂ (h8 _ (hPΩ F.m₂)) hl₂ F.z₂
  have e₃ := I.map_eq_zBar hn F.m₃ (h8 _ (hPΩ F.m₃)) hl₃ F.z₃
  have e₄ := I.map_eq_zBar hn F.m₄ (h8 _ (hPΩ F.m₄)) hl₄ F.z₄
  have c₂ := zBar_eq_cases (e₂.symm.trans e₁)
  have c₃ := zBar_eq_cases (e₃.symm.trans e₁)
  have c₄ := zBar_eq_cases (e₄.symm.trans e₁)
  have lab := fun {B C : Subgroup Y} (hB : B ∈ P) (hC : C ∈ P) (hne : B ≠ C) {α : Finset (Fin 8)}
    {h : α.card = 4} {b c : Bool} (hlB : (B.subgroupOf (pSpan P)).map I.φ = memBar α h b)
    (hlC : (C.subgroupOf (pSpan P)).map I.φ = memBar α h c) =>
    label_not_of_same hn hΩ h2 hPΩ I hk hB hC hne hlB hlC
  constructor
  · by_cases a₂ : α₂ = α₁
    · subst a₂
      exact ⟨A₁, A₂, α₂, h₂', b₁, F.m₁, F.m₂, F.z₁, F.z₂, hl₁, by
        rw [hl₂, lab F.m₁ F.m₂ F.ne₁₂ hl₁ hl₂]⟩
    by_cases a₃ : α₃ = α₁
    · subst a₃
      exact ⟨A₁, A₃, α₃, h₃, b₁, F.m₁, F.m₃, F.z₁, F.z₃, hl₁, by
        rw [hl₃, lab F.m₁ F.m₃ F.ne₁₃ hl₁ hl₃]⟩
    by_cases a₄ : α₄ = α₁
    · subst a₄
      exact ⟨A₁, A₄, α₄, h₄, b₁, F.m₁, F.m₄, F.z₁, F.z₄, hl₁, by
        rw [hl₄, lab F.m₁ F.m₄ F.ne₁₄ hl₁ hl₄]⟩
    have d₂ := c₂.resolve_left a₂
    have d₃ := c₃.resolve_left a₃
    have a₃₂ : α₃ = α₂ := by
      ext x
      rw [d₃ x, d₂ x]
    subst a₃₂
    exact ⟨A₂, A₃, α₃, h₃, b₂, F.m₂, F.m₃, F.z₂, F.z₃, hl₂, by
      rw [hl₃, lab F.m₂ F.m₃ F.ne₂₃ hl₂ hl₃]⟩
  · by_cases a₂ : α₂ = α₁
    · by_cases a₃ : α₃ = α₁
      · by_cases a₄ : α₄ = α₁
        · exfalso
          subst a₂ a₃ a₄
          exact false_of_same_four_set hn hΩ h2 hPΩ I hk F.m₁ F.m₂ F.m₃ F.m₄ hl₁ hl₂ hl₃ hl₄ F.ne₁₂
            F.ne₁₃ F.ne₁₄ F.ne₂₃ F.ne₂₄ F.ne₃₄
        · exact ⟨A₁, A₄, α₁, α₄, h₁, h₄, b₁, b₄, F.m₁, F.m₄, F.z₁, F.z₄, hl₁, hl₄, Ne.symm a₄⟩
      · exact ⟨A₁, A₃, α₁, α₃, h₁, h₃, b₁, b₃, F.m₁, F.m₃, F.z₁, F.z₃, hl₁, hl₃, Ne.symm a₃⟩
    · exact ⟨A₁, A₂, α₁, α₂, h₁, h₂', b₁, b₂, F.m₁, F.m₂, F.z₁, F.z₂, hl₁, hl₂, Ne.symm a₂⟩

theorem ker_eq_bot_of_twins (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hPΩ : P ⊆ Ω)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (I : AEIdent P 8) (hk : IsPGroup 2 I.φ.ker) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y}
    (F : FourTwins P z A₁ A₂ A₃ A₄) : TL4.AECoverHyp I ∧ I.φ.ker = ⊥ := by
  have hn : 5 ≤ 8 := by norm_num
  obtain ⟨⟨B, C, δ, hδ, c, hB, hC, hzB, hzC, hlB, hlC⟩,
    ⟨B', C', α, β, hα, hβ, b, c', hB', hC', hzB', hzC', hlB', hlC', hαβ⟩⟩ :=
    twin_structure hΩ h2 h8 hPΩ I hk F
  have hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L' :=
    fun L hL L' hL' he => aeIdent_eq_of_map_eq hΩ h2 hPΩ hn I hk hL hL' he
  have hH : TL4.AECoverHyp I :=
    { ker_two := hk
      card := fun L hL => h8 L (hPΩ hL)
      conj_mem := hconj
      label_inj := hinj
      twin_comm := by
        intro α h L hL L' hL' hl hl'
        refine aeIdent_comm_of_map_comm hΩ h2 hPΩ I hk hL hL' ?_ ?_
        · intro e
          subst e
          rw [hl] at hl'
          exact memBar_true_ne_false hn α h hl'
        · rw [hl, hl']
          exact memBar_twin_comm α h true
      twin_z := twin_z_of_trans₈ I hn hconj hinj htrans hB hC hlB hlC
        (fun u u' hu hu' => (hu.eq hzB).trans (hu'.eq hzC).symm) }
  refine ⟨hH, ?_⟩
  rcases (Sec13.aeCover_ker hH hn).2 with hbot | ⟨ψ, -, hψ⟩
  · exact hbot
  exfalso
  have hz : ∀ {L : Subgroup Y} (hL : L ∈ P) {γ : Finset (Fin 8)} {hγ : γ.card = 4} {d : Bool}
      (hzp : z ∈ pSpan P), IsUniqueInvolution L z →
      (L.subgroupOf (pSpan P)).map I.φ = memBar γ hγ d →
      ((ψ ⟨z, hzp⟩ : ↥(aeSub 8)) : Wr 8) = zOf (emb γ hγ) := by
    intro L hL γ hγ d hzp hzL hlab
    have hmem : ((ψ ⟨z, hzp⟩ : ↥(aeSub 8)) : Wr 8) ∈ memAt γ hγ d := by
      rw [← hψ L hL γ hγ d hlab]
      exact ⟨ψ ⟨z, hzp⟩, ⟨⟨z, hzp⟩, Subgroup.mem_subgroupOf.mpr hzL.mem, rfl⟩, rfl⟩
    have hsq : ((ψ ⟨z, hzp⟩ : ↥(aeSub 8)) : Wr 8) * ((ψ ⟨z, hzp⟩ : ↥(aeSub 8)) : Wr 8) = 1 := by
      have : (ψ ⟨z, hzp⟩) * (ψ ⟨z, hzp⟩) = 1 := by
        rw [← map_mul, ← map_one ψ]
        congr 1
        exact Subtype.ext hzL.sq
      exact congrArg Subtype.val this
    rcases eq_of_mem_memAt_mul_self hmem hsq with h1 | h1
    · exfalso
      have h3 : ψ ⟨z, hzp⟩ = 1 := Subtype.ext h1
      rw [← map_one ψ] at h3
      exact hzL.ne_one (congrArg Subtype.val (ψ.injective h3))
    · exact h1
  have hzp : z ∈ pSpan P := le_pSpan hB' hzB'.mem
  have e := (hz hB' hzp hzB' hlB').symm.trans (hz hC' hzp hzC' hlC')
  have := range_eq_of_zOf_eq e
  rw [range_emb, range_emb] at this
  exact hαβ (by exact_mod_cast this)


theorem pCoreOf_le_of_involutions (I : AEIdent P 8) (hH : TL4.AECoverHyp I) {D : Subgroup Y}
    (hD : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → u ∈ D) : pCoreOf 2 (pSpan P) ≤ D := by
  have hn : 5 ≤ 8 := by norm_num
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : Y, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    TL4.AECov.comm_of_isUniqueInvolution I hn hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL' hu hu'
  have hW := TL4.AECov.zSpan_elem hcomm
  have hWn := TL4.AECov.zSpan_normal hH.conj_mem
  have hUW := TL4.AECov.ker_permHom_le_zSpan (m := 6) I (by norm_num) hH.card hH.conj_mem hH.label_inj
    hH.ker_two hWn hW
  have hTU := TL4.AECov.le_ker_permHom_of_normal I hn
    (T := CFSG.pCore 2 ↥(pSpan P)) CFSG.pCore_normal CFSG.pCore_isPGroup
  have hzD : TL4.AECov.zSpan P ≤ D.comap (pSpan P).subtype := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨L, hL, hg⟩
    exact hD L hL _ hg
  rintro _ ⟨y, hy, rfl⟩
  exact hzD (hUW (hTU hy))

end Ker

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
