module

public import CFSG.GroupTheory.AschbacherBlock
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.GroupTheory

open CFSG CFSG.RankThree.PartOne Subgroup

variable {Y Y' : Type} [Group Y] [Group Y']

private theorem map_oResidualTwo_le_abm {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') : (oResidualTwo G).map e.toMonoidHom ≤ oResidualTwo G' := by
  rw [oResidualTwo]
  refine le_sInf ?_
  rintro N ⟨hNn, hNp⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine sInf_le ⟨hNn.comap e.toMonoidHom, ?_⟩
  have hcomap : (N.comap e.toMonoidHom).map (e : G →* G') = N :=
    Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N
  have hc : G ⧸ (N.comap e.toMonoidHom) ≃* G' ⧸ N :=
    QuotientGroup.congr (N.comap e.toMonoidHom) N e hcomap
  exact hNp.of_equiv hc.symm

private theorem map_oResidualTwo_eq_abm {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') : (oResidualTwo G).map e.toMonoidHom = oResidualTwo G' := by
  refine le_antisymm (map_oResidualTwo_le_abm e) ?_
  have h : ((oResidualTwo G').map e.symm.toMonoidHom).map e.toMonoidHom ≤
      (oResidualTwo G).map e.toMonoidHom :=
    Subgroup.map_mono (map_oResidualTwo_le_abm e.symm)
  rw [Subgroup.map_map] at h
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
    ext x
    exact MulEquiv.apply_symm_apply e x
  rw [hid] at h
  simpa using h

private theorem oResidualTwo_eq_top_of_mulEquiv_abm {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (h : oResidualTwo G = ⊤) : oResidualTwo G' = ⊤ := by
  rw [← map_oResidualTwo_eq_abm e, h]
  exact Subgroup.map_top_of_surjective _ e.surjective

private theorem quotient_of_mulEquiv_abm {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (h : IsQuasisimple (G ⧸ pCore 2 G) ∨
      ((Nat.card (G ⧸ pCore 2 G)).Prime ∧ Odd (Nat.card (G ⧸ pCore 2 G)))) :
    IsQuasisimple (G' ⧸ pCore 2 G') ∨
      ((Nat.card (G' ⧸ pCore 2 G')).Prime ∧ Odd (Nat.card (G' ⧸ pCore 2 G'))) := by
  have hcore : (pCore 2 G).map (e : G →* G') = pCore 2 G' := pCore_map_iso 2 e
  have hq : G ⧸ pCore 2 G ≃* G' ⧸ pCore 2 G' :=
    QuotientGroup.congr (pCore 2 G) (pCore 2 G') e hcore
  rcases h with h | ⟨hp, ho⟩
  · exact Or.inl (h.of_mulEquiv hq.symm)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [← Nat.card_congr hq.toEquiv]
      exact hp
    · rw [← Nat.card_congr hq.toEquiv]
      exact ho

private lemma restrictEquiv_ker_comp_abm {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {X Y₀ : Subgroup G} {M : Type} [Group M] {ψ : ↥X →* M}
    (hker : ψ.ker = Y₀.subgroupOf X) :
    (ψ.comp (e.subgroupMap X).symm.toMonoidHom).ker =
      (Y₀.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom) := by
  rw [← MonoidHom.comap_ker ψ (e.subgroupMap X).symm.toMonoidHom, hker,
    Subgroup.comap_equiv_eq_map_symm', ← Subgroup.equivMapOfInjective_coe_mulEquiv X e]
  exact CFSG.StandardType.GGRootNorm.map_subgroupOf_equivMapOfInjective
    e.toMonoidHom e.injective X Y₀

private theorem isNaturalSLTwoFactor_map_abm {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {X Y₀ : Subgroup G} {n : ℕ} (h : IsNaturalSLTwoFactor G X Y₀ n) :
    IsNaturalSLTwoFactor G' (X.map e.toMonoidHom) (Y₀.map e.toMonoidHom) n := by
  obtain ⟨φ, ψ, hsurj, hker, heq⟩ := h
  let ee : ↥(X.map e.toMonoidHom) ≃* ↥X := (e.subgroupMap X).symm
  have hcore : (pCore 2 G).map (e : G →* G') = pCore 2 G' := pCore_map_iso 2 e
  let q : G' ⧸ pCore 2 G' ≃* G ⧸ pCore 2 G :=
    (QuotientGroup.congr (pCore 2 G) (pCore 2 G') e hcore).symm
  have hq : ∀ x : G', q (QuotientGroup.mk x) = QuotientGroup.mk (e.symm x) := by
    intro x
    dsimp only [q]
    rw [MulEquiv.symm_apply_eq, QuotientGroup.congr_mk]
    simp
  refine ⟨q.trans φ, ψ.comp ee.toMonoidHom, hsurj.comp ee.surjective, ?_, ?_⟩
  · exact restrictEquiv_ker_comp_abm e hker
  · intro l u hu hu'
    simp only [MonoidHom.comp_apply]
    let l₀ : G := e.symm l
    let u₀ : ↥X := ee.toMonoidHom ⟨u, hu⟩
    have hu₀ : (u₀ : G) ∈ X := u₀.2
    have hu₀' : l₀ * (u₀ : G) * l₀⁻¹ ∈ X := by
      have hmem : e (l₀ * (u₀ : G) * l₀⁻¹) ∈ X.map e.toMonoidHom := by
        have hval : e (l₀ * (u₀ : G) * l₀⁻¹) = l * u * l⁻¹ := by
          have hu₀val : (u₀ : G) = e.symm u := rfl
          rw [hu₀val]
          simp [l₀]
        rw [hval]
        exact hu'
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem
    have hmain := heq l₀ u₀ hu₀ hu₀'
    have hleft : ψ (ee.toMonoidHom ⟨l * u * l⁻¹, hu'⟩) =
        ψ ⟨l₀ * (u₀ : G) * l₀⁻¹, hu₀'⟩ := by
      apply congrArg ψ
      apply Subtype.ext
      show e.symm (l * u * l⁻¹) = e.symm l * e.symm u * (e.symm l)⁻¹
      simp
    have hright : ((q.trans φ) (l : G' ⧸ pCore 2 G') :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) =
        (φ (l₀ : G ⧸ pCore 2 G) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) := by
      rw [MulEquiv.trans_apply, hq l]
    rw [hleft, hmain, hright]

private theorem isNaturalAltFactor_map_abm {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {X Y₀ : Subgroup G} {n : ℕ} (h : IsNaturalAltFactor G X Y₀ n) :
    IsNaturalAltFactor G' (X.map e.toMonoidHom) (Y₀.map e.toMonoidHom) n := by
  obtain ⟨φ, ψ, hsum, hspan, hker, heq⟩ := h
  let ee : ↥(X.map e.toMonoidHom) ≃* ↥X := (e.subgroupMap X).symm
  have hcore : (pCore 2 G).map (e : G →* G') = pCore 2 G' := pCore_map_iso 2 e
  let q : G' ⧸ pCore 2 G' ≃* G ⧸ pCore 2 G :=
    (QuotientGroup.congr (pCore 2 G) (pCore 2 G') e hcore).symm
  have hq : ∀ x : G', q (QuotientGroup.mk x) = QuotientGroup.mk (e.symm x) := by
    intro x
    dsimp only [q]
    rw [MulEquiv.symm_apply_eq, QuotientGroup.congr_mk]
    simp
  refine ⟨q.trans φ, ψ.comp ee.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro u
    exact hsum (ee u)
  · intro v hv
    obtain ⟨u₀, hu₀⟩ := hspan v hv
    obtain ⟨u, rfl⟩ := ee.surjective u₀
    exact ⟨u, by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hu₀⟩
  · exact restrictEquiv_ker_comp_abm e hker
  · intro l u hu hu'
    simp only [MonoidHom.comp_apply]
    let l₀ : G := e.symm l
    let u₀ : ↥X := ee.toMonoidHom ⟨u, hu⟩
    have hu₀ : (u₀ : G) ∈ X := u₀.2
    have hu₀' : l₀ * (u₀ : G) * l₀⁻¹ ∈ X := by
      have hmem : e (l₀ * (u₀ : G) * l₀⁻¹) ∈ X.map e.toMonoidHom := by
        have hval : e (l₀ * (u₀ : G) * l₀⁻¹) = l * u * l⁻¹ := by
          have hu₀val : (u₀ : G) = e.symm u := rfl
          rw [hu₀val]
          simp [l₀]
        rw [hval]
        exact hu'
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hmem
    have hmain := heq l₀ u₀ hu₀ hu₀'
    have hleft : ψ (ee.toMonoidHom ⟨l * u * l⁻¹, hu'⟩) =
        ψ ⟨l₀ * (u₀ : G) * l₀⁻¹, hu₀'⟩ := by
      apply congrArg ψ
      apply Subtype.ext
      show e.symm (l * u * l⁻¹) = e.symm l * e.symm u * (e.symm l)⁻¹
      simp
    have hright : ((q.trans φ) (l : G' ⧸ pCore 2 G') :
        alternatingGroup (Fin (2 * n + 1))) =
        (φ (l₀ : G ⧸ pCore 2 G) : alternatingGroup (Fin (2 * n + 1))) := by
      rw [MulEquiv.trans_apply, hq l]
    rw [hleft, hmain, hright]

private theorem chief_of_mulEquiv_abm {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {X Y₀ : Subgroup G} (hXn : X.Normal) (hY₀n : Y₀.Normal) (hY₀X : Y₀ < X)
    (hXP : X ≤ pCore 2 G) (hY₀Z : Y₀ ≤ center G)
    (hUX : ⁅pCore 2 G, (⊤ : Subgroup G)⁆ ≤ X)
    (hmin : ∀ N : Subgroup G, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X)
    (hnc : ¬ ⁅X, (⊤ : Subgroup G)⁆ ≤ Y₀)
    (hnat : (∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor G X Y₀ n) ∨
      (∃ n, 1 ≤ n ∧ IsNaturalAltFactor G X Y₀ n)) :
    ∃ X' Y₀' : Subgroup G', X'.Normal ∧ Y₀'.Normal ∧ Y₀' < X' ∧ X' ≤ pCore 2 G' ∧
      Y₀' ≤ center G' ∧ ⁅pCore 2 G', (⊤ : Subgroup G')⁆ ≤ X' ∧
      (∀ N : Subgroup G', N.Normal → Y₀' ≤ N → N ≤ X' → N = Y₀' ∨ N = X') ∧
      ¬ ⁅X', (⊤ : Subgroup G')⁆ ≤ Y₀' ∧
      ((∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor G' X' Y₀' n) ∨
        (∃ n, 1 ≤ n ∧ IsNaturalAltFactor G' X' Y₀' n)) := by
  refine ⟨X.map e.toMonoidHom, Y₀.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hXn.map e.toMonoidHom e.surjective
  · exact hY₀n.map e.toMonoidHom e.surjective
  · exact (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr hY₀X
  · calc X.map e.toMonoidHom ≤ (pCore 2 G).map e.toMonoidHom := Subgroup.map_mono hXP
      _ = pCore 2 G' := pCore_map_iso 2 e
  · calc Y₀.map e.toMonoidHom ≤ (center G).map e.toMonoidHom := Subgroup.map_mono hY₀Z
      _ = center G' := Subgroup.map_center_eq e
  · have h := Subgroup.map_mono (f := e.toMonoidHom) hUX
    rw [Subgroup.map_commutator, pCore_map_iso 2 e,
      Subgroup.map_top_of_surjective _ e.surjective] at h
    exact h
  · intro N hNn hY hX
    have hNn' : (N.comap e.toMonoidHom).Normal := hNn.comap e.toMonoidHom
    have hY' : Y₀ ≤ N.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hY
    have hX' : N.comap e.toMonoidHom ≤ X := by
      calc N.comap e.toMonoidHom ≤ (X.map e.toMonoidHom).comap e.toMonoidHom :=
            Subgroup.comap_mono hX
        _ = X := Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective X
    rcases hmin (N.comap e.toMonoidHom) hNn' hY' hX' with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N, h]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N, h]
  · intro hle
    apply hnc
    have hmap : (⁅X, (⊤ : Subgroup G)⁆).map e.toMonoidHom ≤ Y₀.map e.toMonoidHom := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
      exact hle
    exact (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hmap
  · rcases hnat with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · exact Or.inl ⟨n, hn, isNaturalSLTwoFactor_map_abm e h⟩
    · exact Or.inr ⟨n, hn, isNaturalAltFactor_map_abm e h⟩

theorem isAschbacherBlockGomi_of_mulEquiv {B : Type} [Group B] {B' : Subgroup Y'}
    (e : B ≃* B') (hres : oResidualTwo B = ⊤)
    (hq : IsQuasisimple (B ⧸ pCore 2 B) ∨
      ((Nat.card (B ⧸ pCore 2 B)).Prime ∧ Odd (Nat.card (B ⧸ pCore 2 B))))
    (hchief : ∃ X Y₀ : Subgroup B, X.Normal ∧ Y₀.Normal ∧ Y₀ < X ∧ X ≤ pCore 2 B ∧
      Y₀ ≤ center B ∧ ⁅pCore 2 B, (⊤ : Subgroup B)⁆ ≤ X ∧
      (∀ N : Subgroup B, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X) ∧
      ¬ ⁅X, (⊤ : Subgroup B)⁆ ≤ Y₀ ∧
      ((∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor B X Y₀ n) ∨
        (∃ n, 1 ≤ n ∧ IsNaturalAltFactor B X Y₀ n)))
    (hsub : B'.IsSubnormal)
    (hcomm : ⁅pCore 2 Y', B'⁆ ≤ omegaOneCenterIn (pCore 2 Y')) :
    IsAschbacherBlockGomi B' := by
  obtain ⟨X, Y₀, hXn, hY₀n, hY₀X, hXP, hY₀Z, hUX, hmin, hnc, hnat⟩ := hchief
  exact ⟨hsub, oResidualTwo_eq_top_of_mulEquiv_abm e hres, quotient_of_mulEquiv_abm e hq,
    chief_of_mulEquiv_abm e hXn hY₀n hY₀X hXP hY₀Z hUX hmin hnc hnat, hcomm⟩

theorem IsAschbacherBlockGomi.of_mulEquiv {B : Subgroup Y} {B' : Subgroup Y'}
    (hB : IsAschbacherBlockGomi B) (e : B ≃* B') (hsub : B'.IsSubnormal)
    (hcomm : ⁅pCore 2 Y', B'⁆ ≤ omegaOneCenterIn (pCore 2 Y')) :
    IsAschbacherBlockGomi B' :=
  isAschbacherBlockGomi_of_mulEquiv e hB.residual hB.quotient hB.chief hsub hcomm

theorem IsAschbacherBlockGomi.map_of_injective {φ : Y →* Y'} (hφ : Function.Injective φ)
    {B : Subgroup Y} (hB : IsAschbacherBlockGomi B) (hsub : (B.map φ).IsSubnormal)
    (hcomm : ⁅pCore 2 Y', B.map φ⁆ ≤ omegaOneCenterIn (pCore 2 Y')) :
    IsAschbacherBlockGomi (B.map φ) :=
  hB.of_mulEquiv (B.equivMapOfInjective φ hφ) hsub hcomm

end CFSG.GroupTheory
