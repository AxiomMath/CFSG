module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.Lemma45

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem kLevel_congr (p : ℕ) {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    kLevel p S = kLevel p S' := by
  unfold kLevel IsChevSimple
  rw [catalogIs_congr e, catalogIs_congr e, catalogIs_congr e, catalogIs_congr e]

theorem center_pSimple_eq_bot {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : Subgroup.center (PSimple p L) = ⊥ := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI := hq.2
  have hperf : commutator (PSimple p L) = ⊤ := by
    have h1 := hq.1
    rw [commutator_def] at h1 ⊢
    have hs := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p L))
    have h2 := Subgroup.map_commutator (⊤ : Subgroup (PQuot p L)) ⊤
      (QuotientGroup.mk' (Subgroup.center (PQuot p L)))
    rw [h1, Subgroup.map_top_of_surjective _ hs] at h2
    exact h2.symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSimple p L)) with h | h
  · exact h
  · exfalso
    have hab : commutator (PSimple p L) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hy : y ∈ Subgroup.center (PSimple p L) := h ▸ Subgroup.mem_top y
      exact (Subgroup.mem_center_iff.1 hy g).symm
    rw [hab] at hperf
    exact bot_ne_top hperf

theorem kLevel_le_of_pumpRel {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h1412 : I1412UsedAt G p) (h1122 : I1122IsoAt G p) {t t' : Triple G}
    (hrel : PumpRel p t t') : kLevel p (PSimple p t.2.2) ≤ kLevel p (PSimple p t'.2.2) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hx, hL⟩, ⟨hB', hx', hL'c⟩, hxB', -, hx'B', hx'L, hL'⟩ := hrel
  set L := t.2.2
  set L' := t'.2.2
  set x := t.2.1
  set x' := t'.2.1
  set B' := t'.1
  set Cx := Subgroup.centralizer ({x} : Set G)
  set Cx' := Subgroup.centralizer ({x'} : Set G)
  have hB'Cx' : B' ≤ Cx' := isElemAbelian_le_centralizer hB'.1 hx'B'
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  set I := GLAPLayer p (L ⊓ Cx')
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hICx : I ≤ Cx := hIL.trans hL.1
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Cx' ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hL.2.1.inf Cx') hIc
  have hkI : kLevel p (PSimple p I) = kLevel p (PSimple p L) := by
    obtain ⟨f⟩ := nonempty_pSimple_congr eIL
    exact kLevel_congr p f
  have hKx' : CFSG.Open.IsKGroup ↥Cx' :=
    isKGroup_of_isKProper hKP (centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1)
  have hxCx' : Subgroup.zpowers x ≤ Cx' := Subgroup.zpowers_le.2 (hB'Cx' hxB')
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G Cx' hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hB'.1 hxB') I hI2
  set J := closureIn I (GLAPLayer p Cx')
  have hJ : J = ⨆ K ∈ 𝒞, K := (closureIn_eq_iSup_gLBConj I _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ J := fun K hK => hJ ▸ le_biSup (fun K => K) hK
  have hJCx' : J ≤ Cx' := hJ ▸ iSup₂_le fun K hK => (h𝒞c K hK).1
  have hIJ : I ≤ J := le_closureIn_self I _
  have h𝒞J : ∀ K ∈ 𝒞, GLAPComponent p J K := fun K hK =>
    glaPComponent_of_le hp (h𝒞c K hK) (hKJ K hK) hJCx'
  have hL'𝒞 : L' ∈ 𝒞 := by
    refine mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞J hL' ?_
    rw [sSup_eq_iSup, ← hJ]
    exact hL'.1
  by_cases hxN : x ∈ Subgroup.normalizer (L' : Set G)
  ·
    have huniq : ∀ K ∈ 𝒞, K = L' := fun K hK => by
      obtain ⟨e, he, hee⟩ := h𝒞tr L' hL'𝒞 K hK
      have heN : e ∈ Subgroup.normalizer (L' : Set G) := Subgroup.zpowers_le.2 hxN he
      rw [← hee, mem_normalizer_iff_gLBConj_eq.1 heN]
    have hJL' : J = L' := by
      rw [hJ]
      exact le_antisymm (iSup₂_le fun K hK => (huniq K hK).le) (le_biSup (fun K => K) hL'𝒞)
    have hIL' : I ≤ L' := hJL' ▸ hIJ
    have hIL'x : GLAPComponent p (L' ⊓ Cx) I := by
      refine glaPComponent_of_le hp hI2 (le_inf hIL' hICx) ?_
      rw [hCzx]
      exact inf_le_inf_right _ hL'c.1
    rw [← hkI]
    exact h1412 Cx' L' x hKx' hL'c (hB'.1.2 x hxB') hxN I hIL'x
  ·
    have hJcl : J ≤ closureIn L' B' := by
      rw [hJ]
      refine iSup₂_le fun K hK => ?_
      obtain ⟨e, he, rfl⟩ := h𝒞tr L' hL'𝒞 K hK
      rw [closureIn_eq_iSup_gLBConj]
      exact le_biSup (fun b => GLBConj b L') (Subgroup.zpowers_le.2 hxB' he)
    have hclN : closureIn L' B' ≤ Subgroup.normalizer (J : Set G) := by
      rw [closureIn_eq_iSup_gLBConj]
      refine iSup₂_le fun b hb => ?_
      have hbC : GLAPComponent p Cx' (GLBConj b L') := by
        have := glaPComponent_gLBConj hL'c b
        rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hB'Cx' hb))] at this
      intro k hk
      rw [hJ, ← sSup_eq_iSup]
      refine mem_normalizer_sSup fun K hK => ?_
      by_cases hKb : K = GLBConj b L'
      · rw [hKb]
        exact Subgroup.le_normalizer hk
      · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝒞c K hK) hbC
          hKb hk
    have hIJx : GLAPComponent p (J ⊓ Cx) I := by
      refine glaPComponent_of_le hp hI2 (le_inf hIJ hICx) ?_
      rw [hCzx]
      exact inf_le_inf_right _ hJCx'
    have hJxle : J ⊓ Cx ≤ closureIn L' B' ⊓ Cx := inf_le_inf_right _ hJcl
    have hsn : IsSubnormal (J ⊓ Cx) (closureIn L' B' ⊓ Cx) := by
      refine IsSubnormal.step hJxle ((Subgroup.normal_subgroupOf_iff_le_normalizer hJxle).2 ?_)
        (IsSubnormal.refl _)
      intro g hg
      have h1 : GLBConj g J = J := mem_normalizer_iff_gLBConj_eq.1 (hclN hg.1)
      have h2 : GLBConj g Cx = Cx := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)
      rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
    have hIdiag : GLAPComponent p (closureIn L' B' ⊓ Cx) I :=
      glaPComponent_of_isSubnormal' hp hsn hIJx
    obtain ⟨e⟩ := h1122 B' x' L' x hB' hx' hL'c hxB' hxN I hIdiag
    have hZ := center_pSimple_eq_bot hp hL'c
    have f : PQuot p L ≃* PSimple p L' := eIL.symm.trans e
    have g : PSimple p L ≃* PSimple p L' :=
      (QuotientGroup.congr _ _ f (Subgroup.map_center_eq f)).trans
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    exact (kLevel_congr p g).le

end CFSG.LocalAnalysis.GLTheoremA
