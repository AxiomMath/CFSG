module

public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeCover
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeVert
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDiag
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeSwap

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.DPrime

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial

variable {X : Type} [Group X] [Finite X]

theorem diagonal_step
    {Typ : ∀ (K : Type) [Group K], Prop} {q₀ : ℕ} (hq₀ : Odd q₀) (h5 : 5 ≤ q₀)
    (hCI : CoreInvariant Typ) (hDT : DiagonalTransfer q₀ Typ)
    {t s : X} (ht : orderOf t = 2) (hs : orderOf s = 2) (hts : t ∈ centralizer ({s} : Set X))
    {I N : Subgroup X}
    (hI : IsPCompIn 2 (centralizer ({t} : Set X) ⊓ centralizer ({s} : Set X)) I)
    (hTypI : Typ ↥I) (hNI : N ≤ I) (hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N))
    (hsN : s ∈ N) {L : Subgroup (barQ ↥(centralizer ({s} : Set X)))} (hL : CFSG.IsComponent L)
    (hAB : ⁅L, conjSub (barMk ↥(centralizer ({s} : Set X)) ⟨t, hts⟩)⁻¹ L⁆ = ⊥)
    (hIδ : (I.subgroupOf (centralizer ({s} : Set X))).map (barMk ↥(centralizer ({s} : Set X)))
      ≤ (swapDiag hAB).range) :
    ∃ (u : X) (hsu : s ∈ centralizer ({u} : Set X)) (Iu Nu : Subgroup X), orderOf u = 2 ∧
      IsPCompIn 2 (centralizer ({s} : Set X) ⊓ centralizer ({u} : Set X)) Iu ∧ Typ ↥Iu ∧
      u ∈ Iu ∧ Nu ≤ Iu ∧ ⁅Nu, Nu⁆ = Nu ∧ HarrisLit.IsSLTwoOver q₀ (↥Nu ⧸ pPrimeCore 2 ↥Nu) ∧
      u ∈ Nu ∧ Nu ≤ centralizer ({u} : Set X) ∧
      (⟨s, hsu⟩ : ↥(centralizer ({u} : Set X))) ∈
        TwoLayer.subgroup ↥(centralizer ({u} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsY : s ∈ centralizer ({s} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  set t' : ↥(centralizer ({s} : Set X)) := ⟨t, hts⟩ with ht'
  set s' : ↥(centralizer ({s} : Set X)) := ⟨s, hsY⟩ with hs'
  have hs'c : ∀ y : ↥(centralizer ({s} : Set X)), s' * y = y * s' := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.2).symm
  have hsq : ∀ {G : Type} [Group G] {g : G}, orderOf g = 2 → g * g = 1 := fun {G} _ {g} hg => by
    rw [← pow_two, ← hg, pow_orderOf_eq_one]
  have hs'2 : s' * s' = 1 := Subtype.ext (hsq hs)
  have ht'2 : t' * t' = 1 := Subtype.ext (hsq ht)
  have ht'o : orderOf t' = 2 := orderOf_mk_centralizer hts ht
  have hIY : I ≤ centralizer ({s} : Set X) := hI.1.trans inf_le_right
  have hNY : N ≤ centralizer ({s} : Set X) := hNI.trans hIY
  have hN'δ : (N.subgroupOf (centralizer ({s} : Set X))).map
      (barMk ↥(centralizer ({s} : Set X))) ≤ (swapDiag hAB).range :=
    (Subgroup.map_mono fun a ha => mem_subgroupOf.mpr (hNI (mem_subgroupOf.mp ha))).trans hIδ
  obtain ⟨P, ub, hPL, hPp, hPSL, hubP, hubub, hubδ, hubL⟩ :=
    exists_diag_sl2 hs'c hs'2 hAB hq₀ h5
      (isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hNY).symm hNSL) (mem_subgroupOf.mpr hsN) hN'δ
  obtain ⟨u', hu'π, hu'u', hu't⟩ := exists_swap_lift ht'2 hs'c hs'2 hubub hubδ
  obtain ⟨M, hM2, hML⟩ := OddKernelTwoComponents.exists_lift
    (barMk ↥(centralizer ({s} : Set X))) barMk_surjective odd_card_ker_barMk L
    (TwoLayerTransport.ordinary_isTwoComponent_of_corefree oddCore_barQ L
      ((CFSG.isComponent_iff_open L).mp hL))
  have hu'M : u' ∈ M := by
    refine le_of_isPGroup_of_map_le (barMk ↥(centralizer ({s} : Set X))) barMk_surjective
      odd_card_ker_barMk (zpowers u') M (isPGroup_zpowers_of_pow_eq_one (n := 1)
        (by rw [pow_one, pow_two]; exact hu'u')) hM2.1 ?_ (mem_zpowers u')
    rw [hML, Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, mem_comap, hu'π]
    exact hPL hubP
  set u : X := (u' : X) with hu
  have huu : u * u = 1 := congrArg Subtype.val hu'u'
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : u' = 1 := Subtype.ext h
    rw [h1, map_one] at hu'π
    rw [← hu'π] at hubδ
    have h2 := orderOf_barMk (orderOf_mk_centralizer hsY hs)
    rw [← hubδ] at h2
    simp at h2
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have hus : u ∈ centralizer ({s} : Set X) := u'.2
  have hsu : s ∈ centralizer ({u} : Set X) := mem_centralizer_symm hus
  have huC : u ∈ centralizer ({u} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  set MG : Subgroup X := M.map (centralizer ({s} : Set X)).subtype with hMG
  have hMGsub : MG.subgroupOf (centralizer ({s} : Set X)) = M :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({s} : Set X)).subtype_injective M
  have hMGpc : IsPCompIn 2 (centralizer ({s} : Set X)) MG :=
    ⟨map_subtype_le M, by rw [hMGsub]; exact (CatalogueBAlternating.pComponent_two_iff M).mpr hM2⟩
  have huMG : u ∈ MG := ⟨u', hu'M, rfl⟩
  have hucs : u ∈ centralizerSection MG (pPrimeCoreOf 2 MG) := by
    refine mem_centralizerSection_of_map_eq (map_subtype_le M) (by rw [hMGsub]; exact hM2) hus ?_
    intro m hm
    rw [hMGsub] at hm
    have hmL : barMk _ m ∈ L := hML ▸ mem_map_of_mem _ hm
    change barMk _ (u' * m * u'⁻¹) = barMk _ m
    rw [map_mul, map_mul, map_inv, hu'π, hubL _ hmL, mul_inv_cancel_right]
  obtain ⟨Iu, hIuX, -, -, -, hIuW, h2el, hcov⟩ := pumpup_cover hu2 hMGpc hucs
  have huIu : u ∈ Iu :=
    h2el u ⟨huMG, huC⟩ ⟨1, by rw [pow_one, pow_two]; exact huu⟩
  obtain ⟨N₀, hN₀M, hN₀u, hN₀p, hN₀SL, hu'N₀⟩ := exists_sl2_below hML hu'M hu'u'
    (by rw [hu'π]; exact hubL) hPL hPp hPSL (by rw [hu'π]; exact hubP)
  set Nu : Subgroup X := N₀.map (centralizer ({s} : Set X)).subtype with hNu
  have hNuMG : Nu ≤ MG := Subgroup.map_mono hN₀M
  have hNuu : Nu ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hN₀u hn)))
  have hNup : ⁅Nu, Nu⁆ = Nu := by rw [hNu, ← Subgroup.map_commutator, hN₀p]
  have hNuSL : HarrisLit.IsSLTwoOver q₀ (↥Nu ⧸ pPrimeCore 2 ↥Nu) :=
    isSLTwoOver_of_mulEquiv
      (N₀.equivMapOfInjective _ (centralizer ({s} : Set X)).subtype_injective) hN₀SL
  have huNu : u ∈ Nu := ⟨u', hu'N₀, rfl⟩
  have hNuIu : Nu ≤ Iu :=
    le_of_perfect_of_twoElements hNup fun z hz h2 => h2el z ⟨hNuMG hz, hNuu hz⟩ h2
  obtain ⟨eΛM⟩ := nonempty_fusionZStarQuot_equiv ht'o (le_centralizer_mk hI.1 hts)
    (isTwoComponent_centralizer_mk hI hts) hL hAB hIδ hM2 hML
  have eIM : Nonempty (↥I ⧸ Open.fusionZStar ↥I ≃* ↥MG ⧸ Open.fusionZStar ↥MG) :=
    ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hIY).symm).trans (eΛM.trans
      (Sol78.fusionZStarQuotCongr
        (M.equivMapOfInjective _ (centralizer ({s} : Set X)).subtype_injective)))⟩
  have hNu' : Group.IsPerfect ↥(Nu.subgroupOf MG) := by
    have : Group.IsPerfect ↥Nu := Subgroup.isPerfect_iff.mpr hNup
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hNuMG).symm.toMonoidHom)
      (subgroupOfEquivOfLe hNuMG).symm.surjective
  have huZ : (⟨u, huMG⟩ : ↥MG) ∈ Open.fusionZStar ↥MG := by
    obtain ⟨c', hc', hc'u⟩ := mem_fusionZStar_of_mem_centralizerSection huMG hucs
    have : c' = ⟨u, huMG⟩ := Subtype.ext hc'u
    rw [← this]
    exact hc'
  have hTypMG : Typ ↥MG :=
    hDT ↥I ↥MG (isTwoQuasisimple_of_isPCompIn hI) (isTwoQuasisimple_of_isPCompIn hMGpc) hTypI
      eIM (Nu.subgroupOf MG) (Subgroup.isPerfect_iff.mp hNu')
      (isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hNuMG).symm hNuSL) ⟨u, huMG⟩
      (by rw [Subgroup.orderOf_mk]; exact hu2) (mem_subgroupOf.mpr huNu)
      (fun n hn => mem_centralizer_singleton_iff.mpr (Subtype.ext
        (mem_centralizer_singleton_iff.mp (hNuu (mem_subgroupOf.mp hn))))) huZ
  obtain ⟨eIu⟩ := nonempty_coreQuotEquiv_of_cover (hIuX.trans inf_le_left) hcov
  have hTypIu : Typ ↥Iu := hCI ↥MG ↥Iu ⟨eIu.symm⟩ hTypMG
  have hsuo := orderOf_mk_centralizer hsu hs
  have hIuE := (pumpupY_structure hsuo (le_centralizer_mk hIuW.1 hsu)
    (isTwoComponent_centralizer_mk hIuW hsu)).1
  set Mt := M.map (MulAut.conj t'⁻¹).toMonoidHom with hMt
  have hMt2 : TwoComponents.IsTwoComponent Mt :=
    (TwoComponentTransport.equiv_iff (MulAut.conj t'⁻¹) M).mpr hM2
  have hcomp : (barMk ↥(centralizer ({s} : Set X))).comp (MulAut.conj t'⁻¹).toMonoidHom =
      (MulAut.conj (barMk ↥(centralizer ({s} : Set X)) t'⁻¹)).toMonoidHom.comp
        (barMk ↥(centralizer ({s} : Set X))) := by
    ext a
    simp
  have hMtL : Mt.map (barMk ↥(centralizer ({s} : Set X))) =
      conjSub (barMk ↥(centralizer ({s} : Set X)) t')⁻¹ L := by
    rw [hMt, Subgroup.map_map, hcomp, ← Subgroup.map_map, hML, map_inv]
  set MtG : Subgroup X := Mt.map (centralizer ({s} : Set X)).subtype with hMtG
  have hMtGsub : MtG.subgroupOf (centralizer ({s} : Set X)) = Mt :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({s} : Set X)).subtype_injective Mt
  have hMtGpc : IsPCompIn 2 (centralizer ({s} : Set X)) MtG :=
    ⟨map_subtype_le Mt, by
      rw [hMtGsub]; exact (CatalogueBAlternating.pComponent_two_iff Mt).mpr hMt2⟩
  have hucs' : u ∈ centralizerSection MtG (pPrimeCoreOf 2 MtG) := by
    refine mem_centralizerSection_of_map_eq (map_subtype_le Mt) (by rw [hMtGsub]; exact hMt2)
      hus ?_
    intro m hm
    rw [hMtGsub] at hm
    have hmL : barMk _ m ∈ conjSub (barMk ↥(centralizer ({s} : Set X)) t')⁻¹ L :=
      hMtL ▸ mem_map_of_mem _ hm
    have hc := commute_of_commutator_conj_eq_bot hAB (hPL hubP) hmL
    change barMk _ (u' * m * u'⁻¹) = barMk _ m
    rw [map_mul, map_mul, map_inv, hu'π, hc, mul_inv_cancel_right]
  obtain ⟨I', -, -, -, -, hI'W, h2el', -⟩ := pumpup_cover hu2 hMtGpc hucs'
  have hut : t⁻¹ * u * t = u * s := congrArg Subtype.val hu't
  have husMt : u * s ∈ MtG := by
    refine ⟨t'⁻¹ * u' * t', ⟨u', hu'M, ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · change t⁻¹ * u * t = u * s
      exact hut
  have hsuc : s * u = u * s := mem_centralizer_singleton_iff.mp hsu
  have husC : u * s ∈ centralizer ({u} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    rw [mul_assoc, ← hsuc, ← mul_assoc]
  have husI' : u * s ∈ I' := by
    refine h2el' (u * s) ⟨husMt, husC⟩ ⟨1, ?_⟩
    rw [pow_one, pow_two, mul_assoc, ← mul_assoc s, hsuc, mul_assoc, ← mul_assoc, huu, one_mul,
      hsq hs]
  have hI'E := (pumpupY_structure hsuo (le_centralizer_mk hI'W.1 hsu)
    (isTwoComponent_centralizer_mk hI'W hsu)).1
  have h1 : (⟨u, huC⟩ : ↥(centralizer ({u} : Set X))) ∈
      TwoLayer.subgroup ↥(centralizer ({u} : Set X)) := hIuE (mem_subgroupOf.mpr huIu)
  have h2 : (⟨u * s, husC⟩ : ↥(centralizer ({u} : Set X))) ∈
      TwoLayer.subgroup ↥(centralizer ({u} : Set X)) := hI'E (mem_subgroupOf.mpr husI')
  have h3 : (⟨s, hsu⟩ : ↥(centralizer ({u} : Set X))) = ⟨u, huC⟩⁻¹ * ⟨u * s, husC⟩ :=
    Subtype.ext (by simp)
  exact ⟨u, hsu, Iu, Nu, hu2, hIuW, hTypIu, huIu, hNuIu, hNup, hNuSL, huNu, hNuu,
    h3 ▸ mul_mem (inv_mem h1) h2⟩

end CFSG.ComponentClassification.GS82PumpInputs.DPrime
