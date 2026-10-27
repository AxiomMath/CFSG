module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroPartner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroClean
public import CFSG.Goldschmidt.Steps.LemmaXBasic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
private theorem not_mem_map_conj_of_l34PartnerConfig {Q : Subgroup G} {b x₁ : G}
    (hQodd : Odd (Nat.card (center ↥Q)))
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hx1Q : x₁ ∈ Q) (hx1 : orderOf x₁ = 2) :
    x₁ ∉ Q.map (MulAut.conj b).toMonoidHom := by
  intro hx1b
  have hcenter : (⟨x₁, hx1Q⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hQB q.2) x₁ hx1b).symm
  have hx1ord : orderOf (⟨x₁, hx1Q⟩ : ↥Q) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hx1
  exact (CFSG.Goldschmidt.LemmaX.not_mem_of_odd_card hQodd hx1ord) hcenter

omit [Finite G] in
private theorem orderOf_swapDiag_of_l34PartnerConfig {Q : Subgroup G} {b x₁ : G}
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hx1Q : x₁ ∈ Q) (hx1 : orderOf x₁ = 2)
    (hx1not : x₁ ∉ Q.map (MulAut.conj b).toMonoidHom) :
    orderOf (HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩) = 2 := by
  let x : G := HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩
  have hx_eq : x = x₁ * MulAut.conj b x₁ := by
    change HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩ = x₁ * MulAut.conj b x₁
    rw [HarrisLit.swapDiag_apply]
  have hx1sq : x₁ * x₁ = 1 := by
    have h := pow_orderOf_eq_one x₁
    rwa [hx1, pow_two] at h
  have hyb_sq : MulAut.conj b x₁ * MulAut.conj b x₁ = 1 := by
    have h := congrArg (MulAut.conj b) hx1sq
    simpa [map_mul] using h
  have hxcomm : MulAut.conj b x₁ * x₁ = x₁ * MulAut.conj b x₁ :=
    Subgroup.mem_centralizer_iff.mp (hQB hx1Q) (MulAut.conj b x₁)
      (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hx1Q)
  have hx2 : x ^ 2 = 1 := by
    rw [hx_eq, pow_two]
    calc x₁ * MulAut.conj b x₁ * (x₁ * MulAut.conj b x₁)
        = x₁ * (MulAut.conj b x₁ * x₁) * MulAut.conj b x₁ := by group
      _ = x₁ * (x₁ * MulAut.conj b x₁) * MulAut.conj b x₁ := by rw [hxcomm]
      _ = (x₁ * x₁) * (MulAut.conj b x₁ * MulAut.conj b x₁) := by group
      _ = 1 := by rw [hx1sq, hyb_sq, mul_one]
  have hxne : x ≠ 1 := by
    intro hx1'
    have hmul : x₁ * MulAut.conj b x₁ = 1 := by rw [← hx_eq]; exact hx1'
    have hx1eq : x₁ = MulAut.conj b x₁ := by
      calc x₁ = x₁ * (MulAut.conj b x₁ * MulAut.conj b x₁) := by
            rw [hyb_sq, mul_one]
        _ = (x₁ * MulAut.conj b x₁) * MulAut.conj b x₁ := by group
        _ = 1 * MulAut.conj b x₁ := by rw [hmul]
        _ = MulAut.conj b x₁ := by rw [one_mul]
    exact hx1not (by
      rw [hx1eq]
      exact Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hx1Q)
  exact orderOf_eq_prime hx2 hxne

omit [Finite G] in
private theorem swapDiag_mem_centralizer_b {Q : Subgroup G} {b x₁ : G}
    (hb2 : b ^ 2 = 1)
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hx1Q : x₁ ∈ Q) :
    HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩ ∈ centralizer ({b} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := HarrisLit.conj_swapDiag Q hb2 hQB ⟨x₁, hx1Q⟩
  rw [MulAut.conj_apply] at h
  calc HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩ * b
      = (b * HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩ * b⁻¹) * b := by
        conv_lhs => rw [← h]
    _ = b * HarrisLit.swapDiag Q b hQB ⟨x₁, hx1Q⟩ := by group

omit [Finite G] in
private theorem le_centralizer_swapDiag {Q : Subgroup G} {b x₁ x : G}
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hx1Q : x₁ ∈ Q) (hx : x = x₁ * MulAut.conj b x₁)
    {Y : Subgroup G} (hYQ : Y ≤ Q) (hYx1 : Y ≤ centralizer ({x₁} : Set G)) :
    Y ≤ centralizer ({x} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hx]
  have hy1 : y * x₁ = x₁ * y := Subgroup.mem_centralizer_singleton_iff.mp (hYx1 hy)
  have hyb : y * MulAut.conj b x₁ = MulAut.conj b x₁ * y :=
    (Subgroup.mem_centralizer_iff.mp (hQB (hYQ hy)) (MulAut.conj b x₁)
      (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hx1Q)).symm
  calc y * (x₁ * MulAut.conj b x₁)
      = (y * x₁) * MulAut.conj b x₁ := by group
    _ = (x₁ * y) * MulAut.conj b x₁ := by rw [hy1]
    _ = x₁ * (y * MulAut.conj b x₁) := by group
    _ = x₁ * (MulAut.conj b x₁ * y) := by rw [hyb]
    _ = x₁ * MulAut.conj b x₁ * y := by group

omit [Finite G] in
private theorem range_swapDiag_le_centralizer_b {Q : Subgroup G} {b : G}
    (hb2 : b ^ 2 = 1)
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G)) :
    (HarrisLit.swapDiag Q b hQB).range ≤ centralizer ({b} : Set G) := by
  rintro _ ⟨q, rfl⟩
  change (q : G) * MulAut.conj b (q : G) ∈ centralizer ({b} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := HarrisLit.conj_swapDiag Q hb2 hQB q
  rw [HarrisLit.swapDiag_apply, MulAut.conj_apply] at h
  calc (q : G) * MulAut.conj b (q : G) * b
      = (b * ((q : G) * MulAut.conj b (q : G)) * b⁻¹) * b := by
        conv_lhs => rw [← h]
    _ = b * ((q : G) * MulAut.conj b (q : G)) := by group

omit [Finite G] in
private theorem card_map_subgroupOf_swapDiag {Q E : Subgroup G} {b : G}
    (hQodd : Odd (Nat.card (center ↥Q)))
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hEQ : E ≤ Q) (hEsub : Open.IsElemAbelian 2 (E.subgroupOf Q)) :
    Nat.card ((E.subgroupOf Q).map (HarrisLit.swapDiag Q b hQB)) = Nat.card E := by
  have hinj : Set.InjOn (fun q : ↥Q => (HarrisLit.swapDiag Q b hQB q : G))
      ((E.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) := by
    intro a ha c hc hac
    have hmem : a * c⁻¹ ∈ (E.subgroupOf Q : Subgroup ↥Q) :=
      (E.subgroupOf Q).mul_mem ha ((E.subgroupOf Q).inv_mem hc)
    have hker : a * c⁻¹ ∈ (HarrisLit.swapDiag Q b hQB).ker := by
      change HarrisLit.swapDiag Q b hQB a = HarrisLit.swapDiag Q b hQB c at hac
      rw [MonoidHom.mem_ker, map_mul, map_inv, hac, mul_inv_cancel]
    have hcent : a * c⁻¹ ∈ Subgroup.center ↥Q :=
      CFSG.OddStandard.HigherRank.F3.ker_swapDiag_le_center hQB hker
    by_contra hne
    have hne' : a * c⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
    have hord : orderOf (a * c⁻¹) = 2 := orderOf_eq_prime (hEsub.2 _ hmem) hne'
    exact (CFSG.Goldschmidt.LemmaX.not_mem_of_odd_card hQodd hord) hcent
  have h1 : Nat.card ((E.subgroupOf Q).map (HarrisLit.swapDiag Q b hQB)) =
      Nat.card (E.subgroupOf Q) :=
    Nat.card_congr (Equiv.Set.imageOfInjOn
      (fun q : ↥Q => (HarrisLit.swapDiag Q b hQB q : G))
      ((E.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) hinj).symm
  have h2 : Nat.card (E.subgroupOf Q) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv
  rw [h1, h2]


private theorem first_pump_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b x₁ x : G}
    (hQP : Q ≤ centralizer (P : Set G))
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hx1Q : x₁ ∈ Q) (hx1 : orderOf x₁ = 2) (hx : x = x₁ * MulAut.conj b x₁)
    (hxord : orderOf x = 2) (hxx1 : x₁ ∈ centralizer ({x} : Set G))
    (hPx1 : P ≤ centralizer ({x₁} : Set G))
    (hcompx1 : IsComponent (P.subgroupOf (centralizer ({x₁} : Set G))))
    (hPx : P ≤ centralizer ({x} : Set G)) :
    IsComponent (P.subgroupOf (centralizer ({x} : Set G))) := by
  obtain ⟨E, hE, -, hEab, hE16⟩ := exists_elemAbelian_sixteen_of_l34Odd
    hcfg.isQuasisimple_right hcfg.odd_card_center_right hcfg.isL34Type_right hx1Q hx1
  have hEQ : E ≤ Q := hE.trans inf_le_left
  have hE8 : 8 ≤ Nat.card E := by rw [hE16]; norm_num
  have hEclean : wGroup E = ⊥ := hcfg.wGroup_right E hEQ hEab hE8
  have hEx : E ≤ centralizer ({x} : Set G) :=
    le_centralizer_swapDiag hQB hx1Q hx (hE.trans inf_le_left) (hE.trans inf_le_right)
  have hYx : Q ⊓ centralizer ({x₁} : Set G) ≤ centralizer ({x} : Set G) :=
    le_centralizer_swapDiag hQB hx1Q hx inf_le_left inf_le_right
  rcases isComponent_or_swappedBar_of_l34 hcat hSch hU hheld hG hhost hx1 hxord hxx1 hPx1 hPx
      hcompx1 hcfg.odd_card_center_left hcfg.isL34Type_left (hEQ.trans hQP) hEx hEab hE8
      hEclean with hcompx | hbar
  · exact hcompx
  · exact (false_of_l34ZeroSwappedBar_of_mem_commutator hbar
      (inf_le_left.trans hQP) hYx
      (mem_commutator_inf_centralizer_of_l34Odd hcfg.isQuasisimple_right
        hcfg.odd_card_center_right hcfg.isL34Type_right hx1Q hx1)).elim

private theorem second_pump_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b x₁ x : G}
    (hb : orderOf b = 2)
    (hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G))
    (hx1Q : x₁ ∈ Q) (hx1 : orderOf x₁ = 2)
    (hxord : orderOf x = 2) (hxb : x ∈ centralizer ({b} : Set G))
    (hPx : P ≤ centralizer ({x} : Set G))
    (hcompx : IsComponent (P.subgroupOf (centralizer ({x} : Set G))))
    {D : Subgroup G} (hDdef : D = (HarrisLit.swapDiag Q b hQB).range)
    (hDP : D ≤ centralizer (P : Set G)) (hDb : D ≤ centralizer ({b} : Set G))
    (hDself : ⁅D, D⁆ = D) (hxD : x ∈ D) (hPb : P ≤ centralizer ({b} : Set G)) :
    IsComponent (P.subgroupOf (centralizer ({b} : Set G))) := by
  obtain ⟨E, hE, -, hEab, hE16⟩ := exists_elemAbelian_sixteen_of_l34Odd
    hcfg.isQuasisimple_right hcfg.odd_card_center_right hcfg.isL34Type_right hx1Q hx1
  have hEQ : E ≤ Q := hE.trans inf_le_left
  let F : Subgroup G := (E.subgroupOf Q).map (HarrisLit.swapDiag Q b hQB)
  have hFD : F ≤ D := by
    rw [hDdef]
    exact Subgroup.map_le_range (HarrisLit.swapDiag Q b hQB) (E.subgroupOf Q)
  have hFDP : F ≤ centralizer (P : Set G) := hFD.trans hDP
  have hFDb : F ≤ centralizer ({b} : Set G) := hFD.trans hDb
  have hEsub : Open.IsElemAbelian 2 (E.subgroupOf Q) := hEab.subgroupOf Q
  have hFelem : Open.IsElemAbelian 2 F := hEsub.map (HarrisLit.swapDiag Q b hQB)
  have hFcard : Nat.card F = 16 := by
    change Nat.card ((E.subgroupOf Q).map (HarrisLit.swapDiag Q b hQB)) = 16
    rw [card_map_subgroupOf_swapDiag hcfg.odd_card_center_right hQB hEQ hEsub, hE16]
  have hF8 : 8 ≤ Nat.card F := by rw [hFcard]; norm_num
  have hFW : wGroup F = ⊥ :=
    wGroup_eq_bot_of_le_centralizer_of_l34 hG hcfg.isQuasisimple_left
      hcfg.odd_card_center_left hcfg.isL34Type_left hcfg.wGroup_left hFDP hFelem hF8
  rcases isComponent_or_swappedBar_of_l34 hcat hSch hU hheld hG hhost hxord hb hxb hPx hPb
      hcompx hcfg.odd_card_center_left hcfg.isL34Type_left hFDP hFDb hFelem hF8 hFW with
    hcompb | hbar2
  · exact hcompb
  · exact (false_of_l34ZeroSwappedBar_of_mem_commutator hbar2 hDP hDb
      (by rw [hDself]; exact hxD)).elim

theorem le_centralizer_map_conj_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b : G}
    (hbP : b ∈ centralizer (P : Set G)) (hbQ : Q.map (MulAut.conj b).toMonoidHom ≠ Q) :
    Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G) := by
  obtain ⟨e, heP, he⟩ := exists_involution_mem_of_l34Odd hcfg.isQuasisimple_left
    hcfg.odd_card_center_left hcfg.isL34Type_left
  have heb : e * b = b * e := Subgroup.mem_centralizer_iff.mp hbP e heP
  have hfix : b * e * b⁻¹ = e := by
    rw [← heb]
    group
  obtain ⟨hQe, hcompQ⟩ :=
    isComponent_of_mem_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg.symm heP he
  let C : Subgroup G := centralizer ({e} : Set G)
  have hQI : CGT.PushingUpLit.CGT6.Nine7.IsCompIn Q C :=
    HarrisLit.isCompIn_of_isComponent hQe hcompQ
  have hCmap : C.map (MulAut.conj b).toMonoidHom = C := by
    change (centralizer ({e} : Set G)).map (MulAut.conj b).toMonoidHom =
      centralizer ({e} : Set G)
    rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv,
      CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer_singleton, inv_inv, hfix]
  have hQbI : CGT.PushingUpLit.CGT6.Nine7.IsCompIn
      (Q.map (MulAut.conj b).toMonoidHom) C := by
    have h := hQI.cj b⁻¹
    rwa [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv Q b,
      ← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv C b, hCmap] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CGT.PushingUpLit.CGT6.Nine7.commute_of_isCompIn_ne hQI hQbI (fun h => hbQ h.symm))

theorem isComponent_of_map_conj_ne_of_l34PartnerConfig
    (hcat : L34CyclicProperFixedCatalog)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) (hhost : L34ZeroHostFree G) {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b : G}
    (hb : orderOf b = 2) (hbP : b ∈ centralizer (P : Set G))
    (hbQ : Q.map (MulAut.conj b).toMonoidHom ≠ Q) :
    P ≤ centralizer ({b} : Set G) ∧ IsComponent (P.subgroupOf (centralizer ({b} : Set G))) := by
  have hPb : P ≤ centralizer ({b} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hbP p hp)
  refine ⟨hPb, ?_⟩
  have hQP : Q ≤ centralizer (P : Set G) := le_centralizer_iff.mp hcfg.le_centralizer
  have hQB : Q ≤ centralizer ((Q.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G) :=
    le_centralizer_map_conj_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hbP hbQ
  have hQbP : Q.map (MulAut.conj b).toMonoidHom ≤ centralizer (P : Set G) := by
    have hPconj : CFSG.conjugate P b⁻¹ = P := by
      rw [← CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv P b]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer (P : Set G) hbP)
    have hcentmap : (centralizer (P : Set G)).map (MulAut.conj b).toMonoidHom =
        centralizer (P : Set G) := by
      rw [CFSG.StandardSubgroupAPI.map_conj_eq_conjugate_inv,
        CGT.PushingUpLit.CGT6.Nine7.conjugate_centralizer, hPconj]
    rw [← hcentmap]
    exact Subgroup.map_mono hQP
  have hb2 : b ^ 2 = 1 := by
    simpa [hb] using pow_orderOf_eq_one b
  let δ : ↥Q →* G := HarrisLit.swapDiag Q b hQB
  let D : Subgroup G := δ.range
  have hDq : IsQuasisimple ↥D :=
    CFSG.OddStandard.HigherRank.F3.isQuasisimple_range_swapDiag hQB hcfg.isQuasisimple_right
  have hDP : D ≤ centralizer (P : Set G) := by
    rintro _ ⟨q, rfl⟩
    change (q : G) * MulAut.conj b (q : G) ∈ centralizer (P : Set G)
    exact mul_mem (hQP q.2) (hQbP (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom q.2))
  have hDb : D ≤ centralizer ({b} : Set G) := range_swapDiag_le_centralizer_b hb2 hQB
  have hDself : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp hDq.1
  obtain ⟨x₁, hx1Q, hx1⟩ := exists_involution_mem_of_l34Odd hcfg.isQuasisimple_right
    hcfg.odd_card_center_right hcfg.isL34Type_right
  have hx1not := not_mem_map_conj_of_l34PartnerConfig hcfg.odd_card_center_right hQB hx1Q hx1
  let x : G := δ ⟨x₁, hx1Q⟩
  have hx_eq : x = x₁ * MulAut.conj b x₁ := by
    change δ ⟨x₁, hx1Q⟩ = x₁ * MulAut.conj b x₁
    rw [HarrisLit.swapDiag_apply]
  have hxord : orderOf x = 2 := orderOf_swapDiag_of_l34PartnerConfig hQB hx1Q hx1 hx1not
  have hxb : x ∈ centralizer ({b} : Set G) := swapDiag_mem_centralizer_b hb2 hQB hx1Q
  have hxP : x ∈ centralizer (P : Set G) := by
    rw [hx_eq]
    exact mul_mem (hQP hx1Q) (hQbP (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hx1Q))
  have hPx : P ≤ centralizer ({x} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxP p hp)
  obtain ⟨hPx1, hcompx1⟩ :=
    isComponent_of_mem_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hx1Q hx1
  have hxx1 : x₁ ∈ centralizer ({x} : Set G) := by
    have hYx := le_centralizer_swapDiag hQB hx1Q hx_eq inf_le_left inf_le_right
    exact hYx ⟨hx1Q, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcompx := first_pump_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hQP hQB
    hx1Q hx1 hx_eq hxord hxx1 hPx1 hcompx1 hPx
  exact second_pump_of_l34PartnerConfig hcat hSch hU hheld hG hhost hcfg hb hQB hx1Q hx1
    hxord hxb hPx hcompx rfl hDP hDb hDself ⟨⟨x₁, hx1Q⟩, rfl⟩ hPb

end CFSG.ComponentClassification.GrSLit.L34Sec5S
