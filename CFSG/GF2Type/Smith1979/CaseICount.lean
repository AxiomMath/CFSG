module

public import CFSG.GF2Type.Smith1979.CaseIDefs
import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Module QuadraticMap CFSG.LargeExtraspecial.O62

private def base : V₀ := ![1, 0, 0, 0, 0, 0]

private def polF (x y : V₀) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4

private def fPlus (x : V₀) : ZMod 2 := x 0 * x 1 + x 2 * x 3 + x 4 * x 5

private def fMinus (x : V₀) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5

private theorem check_plus_1 : ∀ c : V₀, ∃ x : V₀,
    polF base x = 0 ∧ polF c x = 0 ∧ fPlus x = 0 ∧ x ≠ 0 ∧ x ≠ base := by
  decide +kernel

private theorem check_minus_1 : ∀ c : V₀, ∃ x : V₀,
    polF base x = 0 ∧ polF c x = 0 ∧ fMinus x = 0 ∧ x ≠ 0 ∧ x ≠ base := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
private theorem check_plus_2 : ∀ c : V₀, ∃ x y : V₀,
    (polF base x = 0 ∧ polF c x = 0 ∧ fPlus x = 0 ∧ x ≠ 0 ∧ x ≠ base) ∧
    (polF base y = 0 ∧ polF c y = 0 ∧ fPlus y = 0 ∧ y ≠ 0 ∧ y ≠ base) ∧
      x ≠ y ∧ x ≠ y + base := by
  decide +kernel

private theorem check_minus_3 : (Finset.univ.filter (fun x : V₀ =>
    polF base x = 0 ∧ fMinus x = 0 ∧ x ≠ 0 ∧ x ≠ base)).card = 10 := by
  decide +kernel

private theorem polar_qPlus' (x y : V₀) : polar qPlus x y = polF x y := polar_qPlus x y

private theorem polar_qMinus' (x y : V₀) : polar qMinus x y = polF x y := polar_qMinus x y

private theorem qPlus_apply' (x : V₀) : qPlus x = fPlus x := qPlus_apply x

private theorem qMinus_apply' (x : V₀) : qMinus x = fMinus x := qMinus_apply x

private theorem base_ne_zero : base ≠ 0 := by decide

private theorem finrank_V₀ : finrank (ZMod 2) V₀ = 6 := by simp

private theorem exists_isometry_base {q : QuadraticForm (ZMod 2) V₀}
    (hq : q.polarBilin.Nondegenerate) (hqb : q base = 0) {a : V₀} (ha : a ≠ 0) (haq : q a = 0) :
    ∃ g : V₀ ≃ₗ[ZMod 2] V₀, (∀ v, q (g v) = q v) ∧ g a = base := by
  obtain ⟨g, hg, hga⟩ := exists_mem_omegaGroup_apply_eq hq (by rw [finrank_V₀]; norm_num) ha
    base_ne_zero (haq.trans hqb.symm)
  exact ⟨g, fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hg).1 v, hga⟩

private structure ModelFacts (q : QuadraticForm (ZMod 2) V₀) : Prop where
  trans : ∀ a : V₀, a ≠ 0 → q a = 0 →
    ∃ g : V₀ ≃ₗ[ZMod 2] V₀, (∀ v, q (g v) = q v) ∧ g a = base
  exists_sing : ∀ c : V₀, ∃ x : V₀,
    polar q base x = 0 ∧ polar q c x = 0 ∧ q x = 0 ∧ x ≠ 0 ∧ x ≠ base
  one_coset : ∀ c : V₀, (∀ x y : V₀,
    (polar q base x = 0 ∧ polar q c x = 0 ∧ q x = 0 ∧ x ≠ 0 ∧ x ≠ base) →
    (polar q base y = 0 ∧ polar q c y = 0 ∧ q y = 0 ∧ y ≠ 0 ∧ y ≠ base) →
      x = y ∨ x = y + base) → {v : V₀ | v ≠ 0 ∧ q v = 0}.ncard = 27
  count : {v : V₀ | v ≠ 0 ∧ q v = 0}.ncard = 27 →
    {x : V₀ | polar q base x = 0 ∧ q x = 0 ∧ x ≠ 0 ∧ x ≠ base}.ncard = 10

private theorem ncard_sing_qPlus : {v : V₀ | v ≠ 0 ∧ qPlus v = 0}.ncard = 35 := by
  rcases ncard_singular_nonsingular finrank_V₀ qPlus_nondegenerate with h | h
  · exact h.1
  · have h2 := h.2
    rw [ncard_qPlus] at h2
    omega

private theorem ncard_sing_qMinus : {v : V₀ | v ≠ 0 ∧ qMinus v = 0}.ncard = 27 := by
  rcases ncard_singular_nonsingular finrank_V₀ qMinus_nondegenerate with h | h
  · have h2 := h.2
    rw [ncard_qMinus] at h2
    omega
  · exact h.1

private theorem modelFacts_qPlus : ModelFacts qPlus where
  trans a ha haq :=
    exists_isometry_base qPlus_nondegenerate (by rw [qPlus_apply']; decide) ha haq
  exists_sing c := by simpa only [polar_qPlus', qPlus_apply'] using check_plus_1 c
  one_coset c h := by
    exfalso
    obtain ⟨x, y, hx, hy, hxy, hxy'⟩ := check_plus_2 c
    simp only [polar_qPlus', qPlus_apply'] at h
    rcases h x y hx hy with h | h
    exacts [hxy h, hxy' h]
  count h := by
    rw [ncard_sing_qPlus] at h
    omega

private theorem modelFacts_qMinus : ModelFacts qMinus where
  trans a ha haq :=
    exists_isometry_base qMinus_nondegenerate (by rw [qMinus_apply']; decide) ha haq
  exists_sing c := by simpa only [polar_qMinus', qMinus_apply'] using check_minus_1 c
  one_coset _ _ := ncard_sing_qMinus
  count _ := by
    rw [Set.ncard_eq_toFinset_card']
    simp only [polar_qMinus', qMinus_apply', Set.toFinset_ofPred]
    exact check_minus_3

private theorem exists_hyperplane {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {Q : QuadraticForm (ZMod 2) W}
    (hdim : finrank (ZMod 2) W = 6) (hnd : Q.polarBilin.Nondegenerate) {a : W} (ha : a ≠ 0)
    {D : Submodule (ZMod 2) W} (hD : ∀ d ∈ D, polar Q a d = 0)
    (hD4 : 4 ≤ finrank (ZMod 2) D) :
    ∃ c : W, ∀ x, polar Q a x = 0 → polar Q c x = 0 → x ∈ D := by
  set f : W →ₗ[ZMod 2] ZMod 2 := Q.polarBilin a with hf
  have hfx : ∀ x, f x = polar Q a x := fun x => by simp [hf]
  have hf0 : f ≠ 0 := fun h =>
    ha (forall_polar_of_nondegenerate hnd a fun y => by rw [← hfx, h]; rfl)
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
  rw [hdim] at hker
  by_cases hDP : D = LinearMap.ker f
  · exact ⟨0, fun x hx _ => by rw [hDP, LinearMap.mem_ker, hfx]; exact hx⟩
  · have hle : D ≤ LinearMap.ker f := fun d hd => by
      rw [LinearMap.mem_ker, hfx]
      exact hD d hd
    set P := LinearMap.ker f with hP
    have hcomap : D.comap P.subtype < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => hDP (le_antisymm hle fun x hx => ?_)
      have : (⟨x, hx⟩ : P) ∈ D.comap P.subtype := h ▸ Submodule.mem_top
      exact this
    obtain ⟨g, hg0, hgD⟩ := Submodule.exists_le_ker_of_lt_top _ hcomap
    have hgker := Module.Dual.finrank_ker_add_one_of_ne_zero hg0
    have hD' : finrank (ZMod 2) (D.comap P.subtype) = finrank (ZMod 2) D :=
      (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
    have heq : D.comap P.subtype = LinearMap.ker g :=
      Submodule.eq_of_le_of_finrank_le hgD (by omega)
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend g
    have hcψ : ∀ x, polar Q ((LinearMap.BilinForm.toDual Q.polarBilin hnd).symm ψ) x = ψ x :=
      fun x => by
        rw [← polarBilin_apply_apply]
        exact LinearMap.BilinForm.apply_toDual_symm_apply ψ x
    refine ⟨(LinearMap.BilinForm.toDual Q.polarBilin hnd).symm ψ, fun x hx hcx => ?_⟩
    have hxP : x ∈ P := by
      rw [hP, LinearMap.mem_ker, hfx]
      exact hx
    have hgx : g ⟨x, hxP⟩ = 0 := by
      rw [← LinearMap.congr_fun hψ ⟨x, hxP⟩, LinearMap.comp_apply, Submodule.subtype_apply,
        ← hcψ x]
      exact hcx
    have : (⟨x, hxP⟩ : P) ∈ D.comap P.subtype := by
      rw [heq, LinearMap.mem_ker]
      exact hgx
    exact this

private theorem ncard_eq_of_equiv {α β : Type*} (L : α ≃ β) {S : Set α} {T : Set β}
    (h : ∀ x, x ∈ S ↔ L x ∈ T) : S.ncard = T.ncard := by
  rw [← Set.ncard_image_of_injective S L.injective]
  congr 1
  ext y
  refine ⟨?_, fun hy => ⟨L.symm y, (h _).mpr (by simpa using hy), by simp⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact (h x).mp hx

private theorem countSix_aux {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {Q : QuadraticForm (ZMod 2) W}
    (hdim : finrank (ZMod 2) W = 6) (hnd : Q.polarBilin.Nondegenerate)
    {q : QuadraticForm (ZMod 2) V₀} (hq : ModelFacts q) (M : W ≃ₗ[ZMod 2] V₀)
    (hM : ∀ v, q (M v) = Q v) {a : W} (ha0 : a ≠ 0) (hMa : M a = base) :
    (∀ D : Submodule (ZMod 2) W, a ∈ D → (∀ d ∈ D, polar Q a d = 0) →
        4 ≤ finrank (ZMod 2) D →
          (∃ x ∈ D, Q x = 0 ∧ x ≠ 0 ∧ x ≠ a) ∧
          ((∀ x ∈ D, ∀ y ∈ D, Q x = 0 → Q y = 0 → x ≠ 0 → x ≠ a → y ≠ 0 → y ≠ a →
              x = y ∨ x = y + a) →
            Set.ncard {v : W | v ≠ 0 ∧ Q v = 0} = 27)) ∧
      (Set.ncard {v : W | v ≠ 0 ∧ Q v = 0} = 27 →
        Set.ncard {x : W | polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a} = 10) := by
  have hpol : ∀ x y, polar Q x y = polar q (M x) (M y) := fun x y => by
    simp only [polar, ← hM, map_add]
  have hne0 : ∀ x, M x ≠ 0 ↔ x ≠ 0 := fun x => (M.map_eq_zero_iff).not
  have hnea : ∀ x, M x ≠ base ↔ x ≠ a := fun x => by
    rw [← hMa]
    exact M.injective.ne_iff
  have hS : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = {v : V₀ | v ≠ 0 ∧ q v = 0}.ncard :=
    ncard_eq_of_equiv M.toEquiv fun x => by
      show (x ≠ 0 ∧ Q x = 0) ↔ (M x ≠ 0 ∧ q (M x) = 0)
      rw [hne0, hM]
  refine ⟨fun D _ hD hD4 => ?_, fun h27 => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hyperplane hdim hnd ha0 hD hD4
    have hmem : ∀ x : W, polar q base (M x) = 0 → polar q (M c) (M x) = 0 → x ∈ D :=
      fun x h1 h2 => hc x (by rw [hpol, hMa]; exact h1) (by rw [hpol]; exact h2)
    refine ⟨?_, fun hyp => ?_⟩
    · obtain ⟨x', h1, h2, h3, h4, h5⟩ := hq.exists_sing (M c)
      obtain ⟨x, rfl⟩ := M.surjective x'
      exact ⟨x, hmem x h1 h2, (hM x).symm.trans h3, (hne0 x).mp h4, (hnea x).mp h5⟩
    · rw [hS]
      refine hq.one_coset (M c) fun x' y' hx' hy' => ?_
      obtain ⟨x, rfl⟩ := M.surjective x'
      obtain ⟨y, rfl⟩ := M.surjective y'
      obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx'
      obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy'
      rcases hyp x (hmem x hx1 hx2) y (hmem y hy1 hy2) ((hM x).symm.trans hx3)
        ((hM y).symm.trans hy3) ((hne0 x).mp hx4) ((hnea x).mp hx5) ((hne0 y).mp hy4)
        ((hnea y).mp hy5) with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h, map_add, hMa])
  · refine (ncard_eq_of_equiv M.toEquiv fun x => ?_).trans (hq.count (hS.symm.trans h27))
    show (polar Q a x = 0 ∧ Q x = 0 ∧ x ≠ 0 ∧ x ≠ a) ↔
      (polar q base (M x) = 0 ∧ q (M x) = 0 ∧ M x ≠ 0 ∧ M x ≠ base)
    rw [hpol, hMa, hM, hne0, hnea]

theorem countSixStmt : CountSixStmt := by
  intro W _ _ Q hdim hnd a ha0 haQ
  have : FiniteDimensional (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨L, hL | hL⟩ := exists_linearEquiv_model hdim hnd
  · obtain ⟨g, hgq, hga⟩ := modelFacts_qPlus.trans (L a)
      (fun h => ha0 (L.map_eq_zero_iff.mp h)) (by rw [hL]; exact haQ)
    exact countSix_aux hdim hnd modelFacts_qPlus (L.trans g) (fun v => (hgq _).trans (hL v)) ha0
      hga
  · obtain ⟨g, hgq, hga⟩ := modelFacts_qMinus.trans (L a)
      (fun h => ha0 (L.map_eq_zero_iff.mp h)) (by rw [hL]; exact haQ)
    exact countSix_aux hdim hnd modelFacts_qMinus (L.trans g) (fun v => (hgq _).trans (hL v)) ha0
      hga

end CFSG.GF2Type.Smith1979
