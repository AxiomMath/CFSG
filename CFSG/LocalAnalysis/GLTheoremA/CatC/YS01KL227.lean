module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS01KPump

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

private theorem isKGroup_of_mulEquiv_K {X Y : Type} [Group X] [Group Y]
    (hY : CFSG.Open.IsKGroup Y) (e : X ≃* Y) : CFSG.Open.IsKGroup X :=
  hY.of_injective e.toMonoidHom e.injective

theorem l227PumpAt_of_K (h : KDL227PumpK) : L227PumpAt G := by
  intro Y₀ K J b x hY₀ hK hbK hb3 hxK hxJ hx3 hbx hJ hJty hxinn
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hsimple, hnonab⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI : IsSimpleGroup (PSimple 3 K) := hsimple
  have hcenter : Subgroup.center (PSimple 3 K) = ⊥ :=
    chev_center_eq_bot_of_simple_nonabelian hnonab
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hKgroup : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hY₀ hK.1
  have hcat : CFSG.Open.IsCatalogGroup (PSimple 3 K) :=
    hKgroup.isCatalogGroup_of_surjective ⊤ hnonab
      ((chevQuotHom 3 K).comp (⊤ : Subgroup ↥K).subtype) (fun y => by
        obtain ⟨k, rfl⟩ := chevQuotHom_surjective 3 K y
        exact ⟨⟨k, Subgroup.mem_top k⟩, rfl⟩)
  have hKPS : CFSG.Open.IsKGroup (PSimple 3 K) :=
    hKgroup.of_surjective (chevQuotHom 3 K) (chevQuotHom_surjective 3 K)
  have hKinner : CFSG.Open.IsKGroup ↥(inner (PSimple 3 K)) :=
    isKGroup_of_mulEquiv_K hKPS (MonoidHom.ofInjective (chevToolsY_conj_injective hcenter)).symm
  have hap : IsPGroup 3 (Subgroup.zpowers b) := isPGroup_zpowers_of_pow_eq_one hb3
  have hβ3 : chevAut 3 K ⟨b, hbK⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hbK hb3
  have hξ3 : chevAut 3 K ⟨x, hxK⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hxK hx3
  have hβξ : chevAut 3 K ⟨b, hbK⟩ * chevAut 3 K ⟨x, hxK⟩ =
      chevAut 3 K ⟨x, hxK⟩ * chevAut 3 K ⟨b, hbK⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbx
  have hJ' : GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨b, hbK⟩)) (chevTransfer 3 K J) :=
    glaPComponent_chevTransfer hp hbK hap hJ
  have hker : Nat.Coprime 3 (Nat.card ↥(fixSubgroup (chevAut 3 K ⟨b, hbK⟩) ⊓
      (MulAut.conj : PSimple 3 K →* MulAut (PSimple 3 K)).ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 (chevToolsY_conj_injective hcenter), inf_bot_eq,
      Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hI : GLAPComponent 3 (inner (PSimple 3 K) ⊓
      Subgroup.centralizer ({chevAut 3 K ⟨b, hbK⟩} : Set (MulAut (PSimple 3 K))))
      (l227InnerHom 3 K J hJK).range := by
    rw [range_l227InnerHom, chevToolsY_inner_inf_centralizer hcenter]
    exact glaPComponent_map hp _ hker hJ'
  have hIq := isQuasisimple_pQuot_of_glaPComponent hp hI
  have hJq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hΦ := MonoidHom.rangeRestrict_surjective (l227InnerHom 3 K J hJK)
  have hIty : catalogIs (PSimple 3 (l227InnerHom 3 K J hJK).range) (onLie (isL2 27)) := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hJty
    obtain ⟨e⟩ := nonempty_pSimple_equiv_of_surjective hp
      (l227InnerHom 3 K J hJK).rangeRestrict hΦ hJq hIq
    exact ⟨i, hi, ⟨e.symm.trans f⟩⟩
  have hξI := l227_mem_normalizer_range 3 hJK hxK hxJ
  have hξinn : ¬ InducesInnerMod 3 (l227InnerHom 3 K J hJK).range (chevAut 3 K ⟨x, hxK⟩) := by
    intro hin
    apply hxinn
    rw [inducesInnerMod_iff_barAut_mem_inner hξI] at hin
    rw [inducesInnerMod_iff_barAut_mem_inner hxJ]
    haveI : Group.IsPerfect (PQuot 3 J) := ⟨hJq.1⟩
    haveI := isQuasisimple_nontrivial hIq
    refine chev_mem_inner_of_central_surjective
      (pQuotMapOfSurjective hp (l227InnerHom 3 K J hJK).rangeRestrict hΦ)
      (pQuotMapOfSurjective_surjective hp _ hΦ)
      (ker_pQuotMapOfSurjective_le_center hp _ hΦ hJq inferInstance) ?_ hin
    intro q
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [barAut_mk, pQuotMapOfSurjective_mk, pQuotMapOfSurjective_mk, barAut_mk]
      congr 1
      apply Subtype.ext
      rw [chev_coe_normalizerMonoidHom, MonoidHom.coe_rangeRestrict,
        MonoidHom.coe_rangeRestrict]
      exact (l227InnerHom_conj 3 hJK hxK hxJ j).symm
  have hβ := h (MulAut (PSimple 3 K)) (inner (PSimple 3 K))
    (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _)
    (chevToolsY_isSimpleGroup_inner hnonab) (chevToolsY_nonabelian_inner hnonab)
    (chevToolsY_isCatalogGroup_inner hnonab hcat) hKinner
    (chevToolsY_centralizer_inner_eq_bot hcenter) (l227InnerHom 3 K J hJK).range
    (chevAut 3 K ⟨b, hbK⟩) (chevAut 3 K ⟨x, hxK⟩) hβ3 hξ3 hβξ hI hIty hξI hξinn
  exact (chevAut_eq_one_iff hp hK hbK).1 hβ

end CFSG.LocalAnalysis.GLTheoremA
