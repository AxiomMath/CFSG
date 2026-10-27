module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowCertDefs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7FrameLine
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open scoped commutatorElement

section ConjGen

variable {C : Type*} [Group C]

@[expose] def conjCentGen (x : C) : Subgroup C :=
  closure {y | y ∈ Exc.cent x ∧ ∃ b : C, y = b * x * b⁻¹}

theorem conj_mem_conjCentGen {x b : C} (hb : b * x * b⁻¹ ∈ Exc.cent x) :
    b * x * b⁻¹ ∈ conjCentGen x :=
  subset_closure ⟨hb, b, rfl⟩

theorem self_mem_conjCentGen (x : C) : x ∈ conjCentGen x := by
  have h := conj_mem_conjCentGen (x := x) (b := 1) (by
    rw [one_mul, inv_one, mul_one]
    exact mem_centralizer_singleton_iff.2 rfl)
  rwa [one_mul, inv_one, mul_one] at h

theorem commute_of_mem_conjCentGen {x w : C}
    (hw : ∀ b : C, b * x * b⁻¹ ∈ Exc.cent x → w ∈ Exc.cent (b * x * b⁻¹)) {y : C}
    (hy : y ∈ conjCentGen x) : w * y = y * w := by
  have hle : conjCentGen x ≤ centralizer {w} := by
    refine (closure_le _).2 ?_
    rintro _ ⟨hy', b, rfl⟩
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hw b hy')).symm
  exact (mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem conj_mem_conjCentGen_of_mem_cent {x g : C} (hg : g ∈ Exc.cent x) {y : C}
    (hy : y ∈ conjCentGen x) : g * y * g⁻¹ ∈ conjCentGen x := by
  have hle : conjCentGen x ≤ (conjCentGen x).comap (MulAut.conj g).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨hy', b, rfl⟩
    show (MulAut.conj g) (b * x * b⁻¹) ∈ conjCentGen x
    rw [MulAut.conj_apply]
    have e : g * (b * x * b⁻¹) * g⁻¹ = (g * b) * x * (g * b)⁻¹ := by group
    rw [e]
    refine conj_mem_conjCentGen ?_
    rw [← e]
    exact mul_mem (mul_mem hg hy') (inv_mem hg)
  exact hle hy

theorem list_prod_map_ite_mul {G : Type*} [Monoid G] {F : List (Fin Tag.E7.rank → ℤ)}
    (hnd : F.Nodup) {s : Fin Tag.E7.rank → ℤ} (hs : s ∈ F) (f : (Fin Tag.E7.rank → ℤ) → G)
    {a : G} (ha : ∀ σ ∈ F, Commute a (f σ)) :
    (F.map fun σ => if σ = s then a * f σ else f σ).prod = a * (F.map f).prod := by
  induction F with
  | nil => simp at hs
  | cons σ F ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.prod_cons]
    by_cases hσ : σ = s
    · subst hσ
      have hrest : (F.map fun τ => if τ = σ then a * f τ else f τ) = F.map f :=
        List.map_congr_left fun τ hτ => by
          rw [ite_eq_right (show τ ≠ σ by rintro rfl; exact hnd.1 hτ)]
      rw [ite_eq_left rfl, hrest, mul_assoc]
    · rw [ite_eq_right hσ, ih hnd.2 ((List.mem_cons.1 hs).resolve_left (Ne.symm hσ))
        fun τ hτ => ha τ (List.mem_cons_of_mem _ hτ), ← mul_assoc, ← mul_assoc,
        (ha σ List.mem_cons_self).eq]

end ConjGen

section Single

variable {K : Type} [Field K]

theorem coe_e7FrameElt_singleton (β : Fin Tag.E7.rank → ℤ) (c : K) :
    (e7FrameElt K [β] c : ModGL .E7 K) = pinnedX .E7 K β c := by
  rw [coe_e7FrameElt, List.map_singleton, List.prod_singleton]

end Single

section Roots

variable {K : Type} [Field K]

theorem commute_pinnedX_e7FramePt {F : List (Fin Tag.E7.rank → ℤ)}
    (hFr : ∀ σ ∈ F, IsRoot .E7 σ) {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot .E7 β)
    (h : ∀ σ ∈ F, β ≠ -σ ∧ ¬IsRoot .E7 (β + σ)) (c : K) :
    Commute (pinnedX .E7 K β c) (e7FramePt K F : ModGL .E7 K) := by
  show Commute _ (F.map fun σ => pinnedX .E7 K σ 1).prod
  refine Commute.list_prod_right _ _ fun g hg => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
  exact commute_pinnedX_of_oddDeriv hβ (hFr σ hσ) (h σ hσ).1 (h σ hσ).2 c 1

theorem e7FrameElt_single_mem_cent {F : List (Fin Tag.E7.rank → ℤ)}
    (hFr : ∀ σ ∈ F, IsRoot .E7 σ) {β : Fin Tag.E7.rank → ℤ} (hβ : IsRoot .E7 β)
    (h : ∀ σ ∈ F, β ≠ -σ ∧ ¬IsRoot .E7 (β + σ)) (c : K) :
    e7FrameElt K [β] c ∈ Exc.cent (e7FramePt K F) := by
  rw [Exc.cent, mem_centralizer_singleton_iff]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_e7FrameElt_singleton]
  exact (commute_pinnedX_e7FramePt hFr hβ h c).eq


theorem e7FrameElt_single_mem_conjCentGen_of_seed [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hFr : ∀ σ ∈ F, IsRoot .E7 σ) (hFnd : F.Nodup) {γ s : Fin Tag.E7.rank → ℤ}
    (hγ : IsRoot .E7 γ) (hs : s ∈ F) (hγs : IsRoot .E7 (γ + s)) (hne : γ ≠ s) (hne' : γ ≠ -s)
    (hγF : ∀ σ ∈ F, σ ≠ s → γ ≠ -σ ∧ ¬IsRoot .E7 (γ + σ))
    (hδF : ∀ σ ∈ F, γ + s ≠ -σ ∧ ¬IsRoot .E7 (γ + s + σ)) (c : K) :
    e7FrameElt K [γ + s] c ∈ conjCentGen (e7FramePt K F) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ := oddDerivLacedCheck_of_simplyLaced (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
  have hfac : ∀ σ ∈ F, pinnedX .E7 K γ c * pinnedX .E7 K σ 1 * (pinnedX .E7 K γ c)⁻¹ =
      if σ = s then pinnedX .E7 K (γ + s) c * pinnedX .E7 K σ 1 else pinnedX .E7 K σ 1 := by
    intro σ hσ
    by_cases e : σ = s
    · subst e
      rw [ite_eq_left rfl]
      have h := commutatorElement_pinnedX_of_oddDerivLaced h2 hτ hγ (hFr σ hσ) hne hne' hγs c 1
      rw [commutatorElement_def, mul_one] at h
      rw [← h]
      group
    · rw [ite_eq_right e, ((commute_pinnedX_of_oddDeriv hγ (hFr σ hσ) (hγF σ hσ e).1
        (hγF σ hσ e).2 c 1).eq), mul_assoc, mul_inv_cancel, mul_one]
  have hconjM : pinnedX .E7 K γ c * (e7FramePt K F : ModGL .E7 K) * (pinnedX .E7 K γ c)⁻¹ =
      pinnedX .E7 K (γ + s) c * (e7FramePt K F : ModGL .E7 K) := by
    have hmap := map_list_prod (MulAut.conj (pinnedX .E7 K γ c))
      (F.map fun σ => pinnedX .E7 K σ 1)
    simp only [MulAut.conj_apply, List.map_map, Function.comp_def] at hmap
    show pinnedX .E7 K γ c * (F.map fun σ => pinnedX .E7 K σ 1).prod * (pinnedX .E7 K γ c)⁻¹ =
      pinnedX .E7 K (γ + s) c * (F.map fun σ => pinnedX .E7 K σ 1).prod
    rw [hmap, List.map_congr_left hfac]
    exact list_prod_map_ite_mul hFnd hs (fun σ => pinnedX .E7 K σ 1) fun σ hσ =>
      commute_pinnedX_of_oddDeriv (hγs) (hFr σ hσ) (hδF σ hσ).1 (hδF σ hσ).2 c 1
  have hconj : e7FrameElt K [γ] c * e7FramePt K F * (e7FrameElt K [γ] c)⁻¹ =
      e7FrameElt K [γ + s] c * e7FramePt K F := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_e7FrameElt_singleton]
    exact hconjM
  have hδC := e7FrameElt_single_mem_cent hFr hγs hδF c
  have hxC : e7FramePt K F ∈ Exc.cent (e7FramePt K F) := mem_centralizer_singleton_iff.2 rfl
  have hmem := conj_mem_conjCentGen (x := e7FramePt K F) (b := e7FrameElt K [γ] c)
    (by rw [hconj]; exact mul_mem hδC hxC)
  rw [hconj] at hmem
  have e : e7FrameElt K [γ + s] c =
      e7FrameElt K [γ + s] c * e7FramePt K F * (e7FramePt K F)⁻¹ := by group
  rw [e]
  exact mul_mem hmem (inv_mem (self_mem_conjCentGen _))

theorem e7FrameElt_single_mem_conjCentGen_of_close [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hFr : ∀ σ ∈ F, IsRoot .E7 σ) {a b : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (hab : IsRoot .E7 (a + b)) (hne : a ≠ b) (hne' : a ≠ -b)
    (hbF : ∀ σ ∈ F, b ≠ -σ ∧ ¬IsRoot .E7 (b + σ))
    (haN : ∀ c : K, e7FrameElt K [a] c ∈ conjCentGen (e7FramePt K F)) (c : K) :
    e7FrameElt K [a + b] c ∈ conjCentGen (e7FramePt K F) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ := oddDerivLacedCheck_of_simplyLaced (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
  have hB := e7FrameElt_single_mem_cent hFr hb hbF (1 : K)
  have hcomm : e7FrameElt K [a + b] c = e7FrameElt K [a] c *
      (e7FrameElt K [b] 1 * (e7FrameElt K [a] c)⁻¹ * (e7FrameElt K [b] 1)⁻¹) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_e7FrameElt_singleton]
    have h := commutatorElement_pinnedX_of_oddDerivLaced h2 hτ ha hb hne hne' hab c 1
    rw [commutatorElement_def, mul_one] at h
    rw [← h]
    group
  rw [hcomm]
  exact mul_mem (haN c) (conj_mem_conjCentGen_of_mem_cent hB (inv_mem (haN c)))

end Roots


section Deriv


theorem of_e7SCommB {β σ : Fin Tag.E7.rank → ℤ} (h : e7SCommB β σ = true) :
    β ≠ -σ ∧ ¬IsRoot .E7 (β + σ) := by
  simp only [e7SCommB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨fun e => ?_, not_isRoot_of_oddDerivNotRootB h.2⟩
  rw [e, oddDerivVecEq_self] at h
  exact Bool.false_ne_true h.1.symm

theorem ne_of_oddDerivVecEq_eq_false {n : ℕ} {u v : Fin n → ℤ} (h : oddDerivVecEq u v = false) :
    u ≠ v := fun e => by
  rw [e, oddDerivVecEq_self] at h
  exact Bool.false_ne_true h.symm

end Deriv

section DerivSound

variable {K : Type} [Field K]

theorem e7NDeriv_sound [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hFr : ∀ σ ∈ F, IsRoot .E7 σ) (hFnd : F.Nodup)
    (htuple : ∀ ω : List (Fin Tag.E7.rank),
      (∀ t ∈ e7WordImage ω F, ∀ σ ∈ F, t ≠ -σ ∧ ¬IsRoot .E7 (t + σ)) →
        ∀ t ∈ e7WordImage ω F, ∀ c : K, e7FrameElt K [t] c ∈ conjCentGen (e7FramePt K F)) :
    ∀ (sts : List E7NStep) (D₀ D : List (Fin Tag.E7.rank → ℤ)), e7NDeriv F sts D₀ = some D →
      (∀ d ∈ D₀, ∀ c : K, e7FrameElt K [d] c ∈ conjCentGen (e7FramePt K F)) →
        ∀ d ∈ D, ∀ c : K, e7FrameElt K [d] c ∈ conjCentGen (e7FramePt K F) := by
  intro sts
  induction sts with
  | nil =>
    intro D₀ D h hD₀
    simp only [e7NDeriv, Option.some.injEq] at h
    rw [← h]
    exact hD₀
  | cons st sts ih =>
    intro D₀ D h hD₀
    simp only [e7NDeriv] at h
    split_ifs at h with hst
    refine ih _ D h fun d hd c => ?_
    rcases List.mem_append.1 hd with hd | hd
    · exact hD₀ d hd c
    · cases st with
      | seed γ s =>
        simp only [e7NStepRoots, List.mem_singleton] at hd
        subst hd
        simp only [e7NStepB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.all_eq_true, Bool.or_eq_true] at hst
        obtain ⟨⟨⟨⟨⟨⟨hγ, hs⟩, hγs⟩, hne⟩, hne'⟩, hγF⟩, hδF⟩ := hst
        exact e7FrameElt_single_mem_conjCentGen_of_seed hFr hFnd (isRoot_of_oddDerivIsRootB hγ)
          (mem_of_oddDerivMemB hs) (isRoot_of_oddDerivIsRootB hγs)
          (ne_of_oddDerivVecEq_eq_false hne) (ne_of_oddDerivVecEq_eq_false hne')
          (fun σ hσ hσs => of_e7SCommB ((hγF σ hσ).resolve_left fun e =>
            hσs (eq_of_oddDerivVecEq e)))
          (fun σ hσ => of_e7SCommB (hδF σ hσ)) c
      | close a b =>
        simp only [e7NStepRoots, List.mem_singleton] at hd
        subst hd
        simp only [e7NStepB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          List.all_eq_true] at hst
        obtain ⟨⟨⟨⟨⟨⟨haD, ha⟩, hb⟩, hab⟩, hne⟩, hne'⟩, hbF⟩ := hst
        exact e7FrameElt_single_mem_conjCentGen_of_close hFr (isRoot_of_oddDerivIsRootB ha)
          (isRoot_of_oddDerivIsRootB hb) (isRoot_of_oddDerivIsRootB hab)
          (ne_of_oddDerivVecEq_eq_false hne) (ne_of_oddDerivVecEq_eq_false hne')
          (fun σ hσ => of_e7SCommB (hbF σ hσ))
          (fun c' => hD₀ a (mem_of_oddDerivMemB haD) c') c
      | tuple ω =>
        simp only [e7NStepRoots] at hd
        simp only [e7NStepB, List.all_eq_true] at hst
        exact htuple ω (fun t ht σ hσ => of_e7SCommB (hst t ht σ hσ)) d hd c

theorem mem_borelGroup_of_commute_of_tail {D : List (Fin Tag.E7.rank → ℤ)} {h : ℤ}
    (h1 : 1 ≤ h) (hd : SimpleDiffTail .E7 h) (htail : oddDerivTailB .E7 h D = true)
    {w : adjointGroup .E7 K}
    (hw : ∀ d ∈ D, ∀ c : K, (w : ModGL .E7 K) * pinnedX .E7 K d c =
      pinnedX .E7 K d c * (w : ModGL .E7 K)) :
    (w : ModGL .E7 K) ∈ borelGroup .E7 K := by
  refine mem_borelGroup_of_normalizes_heightSeries h1 hd w.2 fun h' hh' x hx => ?_
  have hle : heightSeries .E7 K h' ≤ centralizer {(w : ModGL .E7 K)} := by
    refine le_trans ?_ (le_trans (heightSeries_le_rootSpan_of_oddDerivTailB (R := K) htail) ?_)
    · exact biSup_mono fun α hα => ⟨hα.1, hα.2.1, hh'.trans hα.2.2⟩
    · refine iSup₂_le fun γ hγ => (closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      exact mem_centralizer_singleton_iff.2 (hw γ hγ c).symm
  have hwx := mem_centralizer_singleton_iff.1 (hle hx)
  rw [← hwx, mul_inv_cancel_right]
  exact hx

end DerivSound

section ListSum

variable {K : Type} [Field K]

theorem list_sum_single_apply_e7 {l : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (β₀ : Fin Tag.E7.rank → ℤ) (v : K) :
    (l.map fun β => (Pi.single β₀ v : (Fin Tag.E7.rank → ℤ) → K) β).sum =
      if β₀ ∈ l then v else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, ih hnd.2]
    by_cases ha : a = β₀
    · subst ha
      rw [Pi.single_eq_same, ite_eq_left List.mem_cons_self, ite_eq_right hnd.1, add_zero]
    · rw [Pi.single_eq_of_ne ha, zero_add]
      by_cases hb : β₀ ∈ l
      · rw [ite_eq_left hb, ite_eq_left (List.mem_cons_of_mem _ hb)]
      · have : β₀ ∉ a :: l := by
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm ha, hb⟩
        rw [ite_eq_right hb, ite_eq_right this]

end ListSum

section Prod

open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

variable {K : Type} [Field K]

theorem exists_rootProd_eq_of_mem_rootSpan_e7 {l : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (hl : RootCommFamily .E7 K l) {g : ModGL .E7 K} (hg : g ∈ rootSpan .E7 K {β | β ∈ l}) :
    ∃ d : (Fin Tag.E7.rank → ℤ) → K, g = rootProd .E7 K l d := by
  let S : Subgroup (ModGL .E7 K) :=
    { carrier := {g | ∃ d : (Fin Tag.E7.rank → ℤ) → K, g = rootProd .E7 K l d}
      mul_mem' := by
        rintro _ _ ⟨d, rfl⟩ ⟨d', rfl⟩
        exact ⟨d + d', (E6Pilot.rootProd_add hl d d').symm⟩
      one_mem' := ⟨0, (E6Pilot.rootProd_zero l).symm⟩
      inv_mem' := by
        rintro _ ⟨d, rfl⟩
        refine ⟨-d, ?_⟩
        rw [inv_eq_iff_mul_eq_one, ← E6Pilot.rootProd_add hl, add_neg_cancel,
          E6Pilot.rootProd_zero] }
  have hle : rootSpan .E7 K {β | β ∈ l} ≤ S :=
    iSup₂_le fun β hβ => (closure_le _).2 (by
      rintro _ ⟨t, rfl⟩
      exact ⟨Pi.single β t, (E6Pilot.rootProd_single hnd hβ t).symm⟩)
  exact hle hg

theorem exists_rootProd_of_annListCheck {S L : List (Fin Tag.E7.rank → ℤ)}
    (hchk : annListCheck .E7 17 S L = true) (hLnd : L.Nodup) {z : ModGL .E7 K}
    (hz : z ∈ posUnipotent .E7 K)
    (hc : ∀ δ ∈ S, z * pinnedX .E7 K δ 1 = pinnedX .E7 K δ 1 * z) :
    RootCommFamily .E7 K L ∧ ∃ c : (Fin Tag.E7.rank → ℤ) → K, z = rootProd .E7 K L c := by
  have hτ' : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨-, hLpos, -, hLpair⟩ := annListCheck_sound hchk
  have hfam : RootCommFamily .E7 K L := fun β hβ β' hβ' s t =>
    commute_pinnedX_of_oddDeriv (hLpos β hβ).1 (hLpos β' hβ').1 (fun e => by
      have h1 := (hLpos β hβ).2
      have h2 := (hLpos β' hβ').2
      rw [e, height_neg] at h1
      linarith) (hLpair β hβ β' hβ') s t
  exact ⟨hfam, exists_rootProd_eq_of_mem_rootSpan_e7 hLnd hfam
    (mem_rootSpan_of_commute_of_annListCheck hτ' hchk hz hc)⟩

theorem conjCoeff_apply_e7 {l : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (hlr : ∀ β ∈ l, IsRoot .E7 β) (α : Fin Tag.E7.rank → ℤ) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ l) :
    conjCoeff α t l c ρ = c ρ + if ρ - α ∈ l ∧ α ≠ ρ - α then t * c (ρ - α) else 0 := by
  classical
  rw [conjCoeff, E6Pilot.list_sum_apply, List.map_map]
  have e : ∀ β ∈ l, ((fun f : (Fin Tag.E7.rank → ℤ) → K => f ρ) ∘ fun β => Pi.single β (c β) +
      if α ≠ β ∧ IsRoot .E7 (α + β) then Pi.single (α + β) (t * c β) else 0) β =
      (Pi.single β (c β) : (Fin Tag.E7.rank → ℤ) → K) ρ +
        (Pi.single (ρ - α) (if α ≠ ρ - α then t * c (ρ - α) else 0) :
          (Fin Tag.E7.rank → ℤ) → K) β := by
    intro β _
    simp only [Function.comp_apply, Pi.add_apply]
    congr 1
    by_cases hβ : β = ρ - α
    · subst hβ
      have hs : α + (ρ - α) = ρ := by abel
      rw [Pi.single_eq_same]
      by_cases hne : α ≠ ρ - α
      · have hr : IsRoot .E7 (α + (ρ - α)) := by rw [hs]; exact hlr ρ hρ
        rw [ite_eq_left ⟨hne, hr⟩, ite_eq_left hne, hs, Pi.single_eq_same]
      · rw [ite_eq_right fun h => hne h.1, ite_eq_right hne]
        rfl
    · have hs : α + β ≠ ρ := fun h => hβ (by rw [← h]; abel)
      rw [Pi.single_eq_of_ne hβ]
      split_ifs
      · exact Pi.single_eq_of_ne (Ne.symm hs) _
      · rfl
  rw [List.map_congr_left e, List.sum_map_add, E6Pilot.list_sum_single_apply hnd hρ c,
    list_sum_single_apply_e7 hnd, ite_and]

end Prod

section Conj

open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def conjCoeffList (B l : List (Fin Tag.E7.rank → ℤ))
    (c : (Fin Tag.E7.rank → ℤ) → K) : (Fin Tag.E7.rank → ℤ) → K :=
  B.foldr (fun β c' => conjCoeff β 1 l c') c

theorem conj_list_rootProd [CharP K 2] {l : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (hlr : ∀ β ∈ l, IsRoot .E7 β) (hl : RootCommFamily .E7 K l) {B : List (Fin Tag.E7.rank → ℤ)}
    (hB : ∀ β ∈ B, IsRoot .E7 β ∧ ∀ y ∈ l, β ≠ -y ∧ (IsRoot .E7 (β + y) → β + y ∈ l))
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    (B.map fun β => pinnedX .E7 K β 1).prod * rootProd .E7 K l c *
        ((B.map fun β => pinnedX .E7 K β 1).prod)⁻¹ =
      rootProd .E7 K l (conjCoeffList K B l c) := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  induction B with
  | nil => simp [conjCoeffList]
  | cons β B ih =>
    have ih' := ih fun β' hβ' => hB β' (List.mem_cons_of_mem _ hβ')
    have hβ := hB β List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, mul_inv_rev]
    calc pinnedX .E7 K β 1 * (B.map fun β => pinnedX .E7 K β 1).prod * rootProd .E7 K l c *
          (((B.map fun β => pinnedX .E7 K β 1).prod)⁻¹ * (pinnedX .E7 K β 1)⁻¹) =
          pinnedX .E7 K β 1 * ((B.map fun β => pinnedX .E7 K β 1).prod * rootProd .E7 K l c *
            ((B.map fun β => pinnedX .E7 K β 1).prod)⁻¹) * (pinnedX .E7 K β 1)⁻¹ := by group
      _ = pinnedX .E7 K β 1 * rootProd .E7 K l (conjCoeffList K B l c) *
            (pinnedX .E7 K β 1)⁻¹ := by rw [ih']
      _ = rootProd .E7 K l (conjCoeffList K (β :: B) l c) :=
          E6Pilot.conj_rootProd hτ h2 hnd hlr hl hβ.1 hβ.2 1 _

theorem conjCoeffList_apply {l C : List (Fin Tag.E7.rank → ℤ)} (hnd : l.Nodup)
    (hlr : ∀ β ∈ l, IsRoot .E7 β) (hCl : ∀ s ∈ C, s ∈ l) {B : List (Fin Tag.E7.rank → ℤ)}
    (hCB : ∀ s ∈ C, ∀ β ∈ B, s - β ∉ l)
    (hRB : ∀ ρ ∈ l, ρ ∉ C → ∀ β ∈ B, ρ - β ∈ l → ρ - β ∈ C) (c : (Fin Tag.E7.rank → ℤ) → K) :
    (∀ s ∈ C, conjCoeffList K B l c s = c s) ∧
      ∀ ρ ∈ l, ρ ∉ C → conjCoeffList K B l c ρ =
        c ρ + (B.map fun β => if ρ - β ∈ C ∧ β ≠ ρ - β then c (ρ - β) else 0).sum := by
  classical
  induction B with
  | nil => simp [conjCoeffList]
  | cons β B ih =>
    obtain ⟨ihC, ihR⟩ := ih (fun s hs β' hβ' => hCB s hs β' (List.mem_cons_of_mem _ hβ'))
      (fun ρ hρ hρC β' hβ' => hRB ρ hρ hρC β' (List.mem_cons_of_mem _ hβ'))
    have hstep : ∀ ρ ∈ l, conjCoeffList K (β :: B) l c ρ = conjCoeffList K B l c ρ +
        if ρ - β ∈ l ∧ β ≠ ρ - β then 1 * conjCoeffList K B l c (ρ - β) else 0 :=
      fun ρ hρ => conjCoeff_apply_e7 hnd hlr β 1 _ hρ
    refine ⟨fun s hs => ?_, fun ρ hρ hρC => ?_⟩
    · rw [hstep s (hCl s hs), ite_eq_right (fun h => hCB s hs β List.mem_cons_self h.1),
        add_zero, ihC s hs]
    · rw [hstep ρ hρ, ihR ρ hρ hρC, List.map_cons, List.sum_cons]
      by_cases h1 : ρ - β ∈ l ∧ β ≠ ρ - β
      · have hC : ρ - β ∈ C := hRB ρ hρ hρC β List.mem_cons_self h1.1
        rw [ite_eq_left h1, ite_eq_left ⟨hC, h1.2⟩, one_mul, ihC _ hC]
        ring
      · have h2 : ¬(ρ - β ∈ C ∧ β ≠ ρ - β) := fun h => h1 ⟨hCl _ h.1, h.2⟩
        rw [ite_eq_right h1, ite_eq_right h2]
        ring

theorem sum_eq_zero_of_commute_conj [CharP K 2] {l C : List (Fin Tag.E7.rank → ℤ)}
    (hnd : l.Nodup) (hlp : ∀ β ∈ l, IsRoot .E7 β ∧ 0 < height β) (hl : RootCommFamily .E7 K l)
    (hCl : ∀ s ∈ C, s ∈ l) {B : List (Fin Tag.E7.rank → ℤ)}
    (hB : ∀ β ∈ B, IsRoot .E7 β ∧ ∀ y ∈ l, β ≠ -y ∧ (IsRoot .E7 (β + y) → β + y ∈ l))
    (hCB : ∀ s ∈ C, ∀ β ∈ B, s - β ∉ l)
    (hRB : ∀ ρ ∈ l, ρ ∉ C → ∀ β ∈ B, ρ - β ∈ l → ρ - β ∈ C) (c : (Fin Tag.E7.rank → ℤ) → K)
    (hcomm : (B.map fun β => pinnedX .E7 K β 1).prod * rootProd .E7 K l c =
      rootProd .E7 K l c * (B.map fun β => pinnedX .E7 K β 1).prod)
    {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ l) (hρC : ρ ∉ C) :
    (B.map fun β => if ρ - β ∈ C ∧ β ≠ ρ - β then c (ρ - β) else 0).sum = 0 := by
  classical
  have hlr : ∀ β ∈ l, IsRoot .E7 β := fun β hβ => (hlp β hβ).1
  have h1 := conj_list_rootProd hnd hlr hl hB c
  rw [hcomm, mul_inv_cancel_right] at h1
  have h2 := E6Pilot.rootProd_injective hnd hlp h1 ρ hρ
  rw [(conjCoeffList_apply hnd hlr hCl hCB hRB c).2 ρ hρ hρC] at h2
  linear_combination -h2

end Conj

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
