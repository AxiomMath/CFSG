module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step7c

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv

theorem isTwoQuasisimple_of_isQuasisimple {J : Type*} [Group J] [Finite J] (hq : IsQuasisimple J)
    (h2 : 2 ∣ Nat.card J) : IsTwoQuasisimple J ∧ pPrimeCore 2 J ≠ ⊤ := by
  have hO : pPrimeCore 2 J ≠ ⊤ := by
    intro h
    have hc := pPrimeCore_coprime_card (p := 2) (G := J)
    rw [h, card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 hc
  refine ⟨⟨hq.1, ?_⟩, hO⟩
  set f := QuotientGroup.mk' (pPrimeCore 2 J)
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq f with h | h
  · exfalso
    apply hO
    rw [eq_top_iff]
    intro y _
    have hy : f y ∈ f.range := ⟨y, rfl⟩
    rw [h, mem_bot] at hy
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
  · exact LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv) h

variable {G : Type} [Group G] [Finite G]

theorem exists_component_of_fixed {Q : Subgroup G} {x : G} (hx : x ∈ normalizer (Q : Set G))
    {P : Type} [Group P] (e : ↥Q ⧸ center ↥Q ≃* P) {M : Subgroup P}
    (hMφ : M ≤ fixSub (C3.phi hx e)) (hMn : fixSub (C3.phi hx e) ≤ normalizer (M : Set P))
    (hMA : Nonempty (↥M ≃* alternatingGroup (Fin 6))) :
    ∃ J : Subgroup G, J ≤ Q ⊓ centralizer {x} ∧
      IsPComponent 2 (J.subgroupOf (Q ⊓ centralizer {x})) ∧ IsOfType (HarrisF 3) ↥J := by
  classical
  have hML : Blueprint.LieModel ↥M .PSL 2 3 2 := Or.inl ⟨by decide,
    LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _ hMA⟩
  have : IsSimpleGroup ↥M := isSimpleGroup_of_lieModel_psl2 hML
  have hMnab := nonabelian_of_lieModel_psl2 hML
  have hMq : IsQuasisimple ↥M := LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hMnab
  have hMZ : center ↥M = ⊥ := FooteLit.center_eq_bot_of_isSimpleGroup hMnab
  have hMp : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hMq.1
  have hM2 : 2 ∣ Nat.card ↥M := even_iff_two_dvd.mp (even_card_of_lieModel_psl2 (by norm_num) hML)
  have : Finite P := Finite.of_surjective _ (C3.piQ_surjective e)
  have hker : (C3.piQ e).ker ≤ center ↥Q := (C3.ker_piQ e).le
  have hMr : M ≤ (C3.piQ e).range := by
    rw [MonoidHom.range_eq_top.mpr (C3.piQ_surjective e)]
    exact le_top
  set R := GSThmB.Cent516.liftN (C3.piQ e) M with hRdef
  have hRp : ⁅R, R⁆ = R := GSThmB.Cent516.liftN_perfect hker hMp hMr
  have hRmap : R.map (C3.piQ e) = M := GSThmB.Cent516.map_liftN hMp hMr
  have hRle : R ≤ M.comap (C3.piQ e) := GSThmB.Cent516.liftN_le (C3.piQ e) M
  have hfix := C3.fixed_of_perfect hx e hRp fun q hq => mem_fixSub.mp (hMφ (hRle hq))
  have hRC : R ≤ C3.CQ Q x := fun q hq => (C3.xAut_eq_iff hx q).mp (hfix q hq)
  have hMs : (M.subgroupOf (fixSub (C3.phi hx e))).IsSubnormal :=
    ((normal_subgroupOf_iff_le_normalizer hMφ).mpr hMn).isSubnormal
  set D := (fixSub (C3.phi hx e)).comap (C3.piQ e) with hD
  let f : ↥D →* ↥(fixSub (C3.phi hx e)) :=
    ((C3.piQ e).comp D.subtype).codRestrict _ (fun d => d.2)
  have h1 : ((M.comap (C3.piQ e)).subgroupOf D).IsSubnormal := by
    have h := hMs.comap f
    have heq : (M.subgroupOf (fixSub (C3.phi hx e))).comap f =
        (M.comap (C3.piQ e)).subgroupOf D := by
      ext d
      exact Iff.rfl
    rwa [heq] at h
  have hCD : C3.CQ Q x ≤ D := fun q hq => C3.piQ_mem_fixSub hx e hq
  have h2 : ((M.comap (C3.piQ e)).subgroupOf (C3.CQ Q x)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hCD h1
  have hRM : R ≤ M.comap (C3.piQ e) ⊓ C3.CQ Q x := le_inf hRle hRC
  have h3 : (R.subgroupOf (C3.CQ Q x)).IsSubnormal := by
    refine CFSG.GroupTheory.isSubnormal_subgroupOf_trans hRM inf_le_right ?_ ?_
    · apply Subgroup.Normal.isSubnormal
      rw [normal_subgroupOf_iff_le_normalizer hRM]
      exact inf_le_left.trans (L219.le_normalizer_commutator _ _)
    · rwa [inf_subgroupOf_right]
  let g : ↥R →* ↥M := ((C3.piQ e).comp R.subtype).codRestrict M (fun r => hRle r.2)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hRmap] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    exact ⟨⟨r, hr⟩, rfl⟩
  have hgker : g.ker ≤ center ↥R := by
    intro r hr
    have hr' : (r : ↥Q) ∈ center ↥Q := hker (by
      rw [MonoidHom.mem_ker] at hr ⊢
      exact congrArg Subtype.val hr)
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (mem_center_iff.mp hr' s)
  have hRq : IsQuasisimple ↥R :=
    (LocalCores.isQuasisimple_iff_of_surjective (Subgroup.isPerfect_iff.mpr hRp) g hg hgker).mpr hMq
  have hgker' : g.ker = center ↥R := by
    refine le_antisymm hgker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hgz : g z ∈ center ↥M := by
      rw [mem_center_iff]
      intro m
      obtain ⟨y, rfl⟩ := hg m
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
    rw [hMZ, mem_bot] at hgz
    exact hgz
  have hR2 : 2 ∣ Nat.card ↥R := hM2.trans (Subgroup.card_dvd_of_surjective hg)
  obtain ⟨hR2q, hRO⟩ := isTwoQuasisimple_of_isQuasisimple hRq hR2
  have hRt : IsOfType (HarrisF 3) ↥R := by
    refine ⟨hR2q, ↥M, inferInstance, InClosure.base ⟨2, by norm_num, hML⟩, ⟨?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq
      ((CatLeaf.fusionZStar_eq_center_of_quasisimple hRq hRO).trans hgker'.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  set J := R.map Q.subtype with hJ
  have hJC : J ≤ Q ⊓ centralizer {x} := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q.2, hRC hq⟩
  have eRJ : ↥R ≃* ↥J := R.equivMapOfInjective _ Q.subtype_injective
  have hJq : IsQuasisimple ↥J := LocalCores.isQuasisimple_of_mulEquiv eRJ hRq
  have hJs : (J.subgroupOf (Q ⊓ centralizer {x})).IsSubnormal := C3.isSubnormal_map_subtype h3
  refine ⟨J, hJC, ?_, Q81.isOfType_of_mulEquiv eRJ hRt⟩
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC).symm hJq, hJs⟩ fun hle => ?_
  have h2J : 2 ∣ Nat.card ↥(J.subgroupOf (Q ⊓ centralizer {x})) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv, ← Nat.card_congr eRJ.toEquiv]
    exact hR2
  have hc := pPrimeCore_coprime_card (p := 2) (G := ↥(Q ⊓ centralizer {x}))
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (h2J.trans (card_dvd_of_le hle)) hc

end CFSG.ComponentClassification.HarrisLit.P1
