module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFixHWA

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem conj_fix_two (hBC : ProperSectionB.KGroupBConclusion ↥h.W) {g : H} (hgW : g ∈ h.W)
    (heS : g⁻¹ * h.a * g ∈ h.S) (heP : g⁻¹ * h.a * g ∉ h.P) :
    g⁻¹ * h.a * g ∉ closure ((h.D : Set H) ∪ {h.a}) ⊓ centralizer ({h.x} : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := h.conj_fix_one hBC hgW heS heP
  set e := g⁻¹ * h.a * g with he
  set M := conjugate h.J g with hM
  set Ca := centralizer ({h.a} : Set H) with hCa
  intro hmem
  obtain ⟨heDa, hex⟩ := mem_inf.mp hmem
  have hxe : e * h.x = h.x * e := mem_centralizer_singleton_iff.mp hex
  have hS2 := h.isPGroup_S
  have haS := h.a_mem_S
  have hxS : h.x ∈ h.S := h.x_mem
  have hxCa : h.x ∈ Ca := (mem_inf.mp (h.S_le hxS)).1
  have hxNJ : h.x ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le hxS)).2
  have heCa : e ∈ Ca := (mem_inf.mp (h.S_le heS)).1
  have hea : e * h.a = h.a * e := mem_centralizer_singleton_iff.mp heCa
  have hJq := B5aHW.isQuasisimple_J h
  have hcomp : ∀ c ∈ Ca,
      conjugate h.J c ≤ Ca ∧ IsPComponent 2 ((conjugate h.J c).subgroupOf Ca) :=
    fun c hc => OddQuot.isPComponent_conjugate_subgroupOf hc h.J_le h.isPComponent_J
  have hfacts : ∀ c ∈ Ca, conjugate h.J c ≠ h.J →
      e ∈ coreActionKernel (conjugate h.J c) ∧
        h.P ⊓ conjugate h.J c ≤ centralizer ({e} : Set H) ∧ h.P ⊓ conjugate h.J c ≠ ⊥ := by
    intro c hc hne
    obtain ⟨hL1, hL2⟩ := hcomp c hc
    have hLK : conjugate h.J c ≤ coreActionKernel h.J :=
      B5a.le_coreActionKernel_of_ne h.J_le hL1 h.isPComponent_J hL2 hne.symm
    have hJK : h.J ≤ coreActionKernel (conjugate h.J c) :=
      B5a.le_coreActionKernel_of_ne hL1 h.J_le hL2 h.isPComponent_J hne
    refine ⟨?_, ?_, ?_⟩
    · refine (closure_le _).mpr ?_ heDa
      rintro z (hz | hz)
      · exact hJK (mem_inf.mp hz).2
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact B5a.centralizer_le_coreActionKernel _ (mem_centralizer_iff.mpr fun l hl =>
          mem_centralizer_singleton_iff.mp (hL1 hl))
    · intro l hl
      obtain ⟨hlP, hlL⟩ := mem_inf.mp hl
      have hlS : l ∈ h.S := (mem_inf.mp hlP).1
      have hcl : closure ((h.D : Set H) ∪ {h.a}) ≤ centralizer ({l} : Set H) := by
        refine (closure_le _).mpr ?_
        rintro z (hz | hz)
        · obtain ⟨hzS, hzJ⟩ := mem_inf.mp hz
          have h1 := (mem_coreActionKernel.mp (hLK hlL)).2 z hzJ
          have h2 : z⁻¹ * l⁻¹ * z * l ∈ h.S :=
            mul_mem (mul_mem (mul_mem (inv_mem hzS) (inv_mem hlS)) hzS) hlS
          have h3 := B5a.eq_one_of_isPGroup_of_odd hS2 (B5a.odd_card_oddCoreIn h.J) h2 h1
          rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
          calc z * l = l * z * (z⁻¹ * l⁻¹ * z * l) := by group
            _ = l * z := by rw [h3, mul_one]
        · rw [Set.mem_singleton_iff] at hz
          rw [hz, SetLike.mem_coe, mem_centralizer_singleton_iff]
          exact (mem_centralizer_singleton_iff.mp (hL1 hlL)).symm
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp (hcl heDa)).symm
    · obtain ⟨U, hU⟩ := h.S_sylow
      have hLY : conjugate h.J c ≤ Ca ⊓ normalizer (h.J : Set H) :=
        le_inf hL1 fun l hl => (mem_coreActionKernel.mp (hLK hl)).1
      have hsub : ((conjugate h.J c).subgroupOf
          (Ca ⊓ normalizer (h.J : Set H))).IsSubnormal := by
        obtain ⟨-, -, hs, -, -⟩ := id hL2
        exact hs.comap (inclusion (inf_le_left : Ca ⊓ normalizer (h.J : Set H) ≤ Ca))
      have hcard : Nat.card ↥(conjugate h.J c) = Nat.card h.J :=
        (Nat.card_congr (h.J.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).toEquiv).symm
      have heven : 2 ∣ Nat.card ((conjugate h.J c).subgroupOf
          (Ca ⊓ normalizer (h.J : Set H))) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hLY).toEquiv, hcard]
        exact B5a.two_dvd_card_of_isQuasisimple hJq
      have hne' := B5a.inf_sylow_ne_bot_of_isSubnormal U hsub heven
      intro hbot
      apply hne'
      rw [hU, eq_bot_iff]
      rintro ⟨y, hyY⟩ hy
      obtain ⟨hyS, hyL⟩ := mem_inf.mp hy
      have h1 : y ∈ h.P ⊓ conjugate h.J c :=
        mem_inf.mpr ⟨mem_inf.mpr ⟨hyS, hLK hyL⟩, hyL⟩
      rw [hbot, mem_bot] at h1
      exact mem_bot.mpr (Subtype.ext h1)
  have hxNM : h.x ∉ normalizer (M : Set H) := by
    intro hxNM
    apply h.B_ne_bot
    rw [eq_bot_iff, ← h.inf_conjugate_x]
    intro y hy
    refine mem_inf.mpr ⟨hy, ?_⟩
    rw [mem_conjugate_iff]
    rw [hB] at hy ⊢
    obtain ⟨hy1, hyK⟩ := mem_inf.mp hy
    obtain ⟨hyP, hyC⟩ := mem_inf.mp hy1
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨B5aHW.conj_mem_P h hxS hyP, ?_⟩,
      UnbalancedLayer.conj_mem_coreActionKernel hxNM hyK⟩
    rw [mem_centralizer_singleton_iff] at hyC ⊢
    have hc1 : Commute h.x e := hxe.symm
    have hc2 : Commute y e := hyC
    exact (hc1.mul_left hc2).mul_left hc1.inv_left
  set c := g * h.x * g⁻¹ with hc
  have hae : h.a = g * e * g⁻¹ := by rw [he]; group
  have hcCa : c ∈ Ca := by
    rw [mem_centralizer_singleton_iff, hc, hae]
    calc g * h.x * g⁻¹ * (g * e * g⁻¹) = g * (h.x * e) * g⁻¹ := by group
      _ = g * (e * h.x) * g⁻¹ := by rw [← hxe]
      _ = g * e * g⁻¹ * (g * h.x * g⁻¹) := by group
  have hL₀ : conjugate h.J c ≠ h.J := by
    intro heq
    apply hxNM
    apply mem_normalizer_of_conjugate_eq
    rw [hM, conjugate_conjugate, show g * h.x = c * g by rw [hc]; group,
      ← conjugate_conjugate, heq]
  have hMa : h.a ∈ normalizer (M : Set H) := by
    set y := g * h.a * g⁻¹ with hy
    have hyW : y ∈ h.W := mul_mem (mul_mem hgW h.a_mem_normalizer) (inv_mem hgW)
    have hyCa : y ∈ Ca := by
      rw [mem_centralizer_singleton_iff]
      calc y * h.a = g * (h.a * e) * g⁻¹ := by rw [hy, he]; group
        _ = g * (e * h.a) * g⁻¹ := by rw [hea]
        _ = h.a * y := by rw [hy, he]; group
    by_contra hnot
    have hJy : conjugate h.J y ≠ h.J := by
      intro hJy
      apply hnot
      apply mem_normalizer_of_conjugate_eq
      rw [hM, conjugate_conjugate, show g * h.a = y * g by rw [hy]; group,
        ← conjugate_conjugate, hJy]
    obtain ⟨hJy1, hJy2⟩ := hcomp y hyCa
    have hJJy : ⁅h.J, conjugate h.J y⁆ ≤ oddCoreIn Ca :=
      B5a.commutator_le_oddCoreIn_of_ne h.J_le hJy1 h.isPComponent_J hJy2 hJy.symm
    set E' := h.B ⊔ zpowers h.a with hE'
    have hE'S : E' ≤ h.S := sup_le (h.B_le.trans inf_le_left) (zpowers_le.mpr haS)
    have hE'W : E' ≤ h.W := sup_le le_normalizer (zpowers_le.mpr h.a_mem_normalizer)
    have hCE' : centralizer (E' : Set H) = Ca ⊓ centralizer (h.B : Set H) := by
      apply le_antisymm
      · refine le_inf ?_ (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
        rw [hCa, ← centralizer_zpowers_eq]
        exact centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)
      · rw [le_centralizer_iff]
        refine sup_le (le_centralizer_iff.mp inf_le_right) (le_centralizer_iff.mp ?_)
        rw [centralizer_zpowers_eq]
        exact inf_le_left
    have hHcCa : centralizer (E' : Set H) ≤ Ca := by
      rw [hCE']
      exact inf_le_left
    have hJBle : GSLit.fixedLayer h.J h.B ≤ Ca ⊓ centralizer (h.B : Set H) :=
      (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_inf_right _ h.J_le)
    have hJBl : GSLit.fixedLayer h.J h.B ≤ layerIn (centralizer (E' : Set H)) := by
      rw [hCE']
      have h1 := map_mono (f := (Ca ⊓ centralizer (h.B : Set H)).subtype)
        (show (GSLit.fixedLayer h.J h.B).subgroupOf (Ca ⊓ centralizer (h.B : Set H)) ≤
          pLayer ↥(Ca ⊓ centralizer (h.B : Set H)) 2 from le_sSup (B5aHW.isPComponent_fixedLayer h))
      rwa [map_subgroupOf_eq_of_le hJBle] at h1
    have hyE' : y ∈ normalizer (E' : Set H) := by
      refine B5a.mem_normalizer_sup hyW (centralizer_le_normalizer _ ?_)
      rw [centralizer_zpowers_eq]
      exact hyCa
    have hyHc : conjugate (centralizer (E' : Set H)) y = centralizer (E' : Set H) :=
      conjugate_eq_of_mem_normalizer (B5a.mem_normalizer_centralizer hyE')
    have hJBy : conjugate (GSLit.fixedLayer h.J h.B) y ≤ layerIn (centralizer (E' : Set H)) := by
      have h1 := B5a.conjugate_mono hJBl y
      rwa [B5a.conjugate_layerIn_eq, hyHc] at h1
    have hcomm : ⁅GSLit.fixedLayer h.J h.B, conjugate (GSLit.fixedLayer h.J h.B) y⁆ ≤
        oddCoreIn (centralizer (E' : Set H)) := by
      have hJBJ : GSLit.fixedLayer h.J h.B ≤ h.J :=
        (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
      have h1 : ⁅GSLit.fixedLayer h.J h.B, conjugate (GSLit.fixedLayer h.J h.B) y⁆ ≤
          ⁅h.J, conjugate h.J y⁆ := commutator_mono hJBJ (B5a.conjugate_mono hJBJ y)
      have hl : layerIn (centralizer (E' : Set H)) ≤ centralizer (E' : Set H) := map_subtype_le _
      have h2 : ⁅GSLit.fixedLayer h.J h.B, conjugate (GSLit.fixedLayer h.J h.B) y⁆ ≤
          centralizer (E' : Set H) :=
        (commutator_mono (hJBl.trans hl) (hJBy.trans hl)).trans (commutator_le_self _)
      exact (le_inf h2 (h1.trans hJJy)).trans (B5a.inf_oddCoreIn_le_of_le hHcCa)
    have hJBp : Group.IsPerfect (GSLit.fixedLayer h.J h.B) :=
      B5a.isPerfect_of_isPComponent_subgroupOf hJBle (B5aHW.isPComponent_fixedLayer h)
    have hbar := h.wbarImage_commutator_eq_bot_of_layer hBC (le_sup_left : h.B ≤ E') hE'W
      (hS2.to_le hE'S) hJBl hJBy hcomm hJBp
    rw [h.wbarImage_conjugate _ hyW] at hbar
    exact h.isStandard_bar.2.2.2.2 _ hbar
  have hMa' : conjugate M h.a = M := conjugate_eq_of_mem_normalizer hMa
  obtain ⟨c', hc'Ca, hc'ne, hc'K⟩ : ∃ c' ∈ Ca, conjugate h.J c' ≠ h.J ∧
      ¬ h.P ⊓ conjugate h.J c' ≤ coreActionKernel M := by
    by_contra hall
    push Not at hall
    have hle : ∀ c' ∈ Ca, conjugate h.J c' ≠ h.J → h.P ⊓ conjugate h.J c' ≤ h.B := by
      intro c' hc' hne
      rw [hB]
      exact le_inf (le_inf inf_le_left (hfacts c' hc' hne).2.1) (hall c' hc' hne)
    apply (hfacts c hcCa hL₀).2.2
    rw [eq_bot_iff, ← h.inf_conjugate_x]
    refine le_inf (hle c hcCa hL₀) ?_
    have hcx : c * h.x⁻¹ ∈ Ca := mul_mem hcCa (inv_mem hxCa)
    have hcxne : conjugate h.J (c * h.x⁻¹) ≠ h.J := by
      intro heq
      apply hL₀
      rw [show c = c * h.x⁻¹ * h.x by group, ← conjugate_conjugate, heq,
        conjugate_eq_of_mem_normalizer hxNJ]
    intro z hz
    rw [mem_conjugate_iff]
    apply hle _ hcx hcxne
    obtain ⟨hzP, hzL⟩ := mem_inf.mp hz
    refine mem_inf.mpr ⟨B5aHW.conj_mem_P h hxS hzP, ?_⟩
    rw [← conjugate_conjugate, mem_conjugate_iff,
      show h.x⁻¹ * (h.x * z * h.x⁻¹) * h.x⁻¹⁻¹ = z by group]
    exact hzL
  obtain ⟨hL1, hL2⟩ := hcomp c' hc'Ca
  obtain ⟨heL, hPLe, -⟩ := hfacts c' hc'Ca hc'ne
  set L := conjugate h.J c' with hL
  have hJL : ↥h.J ≃* ↥L := h.J.equivMapOfInjective _ (MulAut.conj c'⁻¹).injective
  have hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 hJL)).1 hJq
  have he2 : orderOf e = 2 := by
    rw [he, show g⁻¹ * h.a * g = (MulAut.conj g⁻¹) h.a by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, h.orderOf_a]
  have hez2 : IsPGroup 2 (zpowers e) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, he2, pow_one])
  have heLz : zpowers e ≤ coreActionKernel L := zpowers_le.mpr heL
  obtain ⟨-, -, hLsub, -, -⟩ := id hL2
  set Le := GSLit.fixedLayer L (zpowers e) with hLe
  obtain ⟨hLesup, hLecore⟩ := GSLit.fixedLayer_sup_pPrimeCore hLq heLz hez2
  have hLec := GSLit.fixedLayer_isPComponent hL1 hLsub (zpowers_le.mpr heCa) heLz hez2 hLq
  rw [centralizer_zpowers_eq] at hLec
  have hPLLe : h.P ⊓ L ≤ Le := by
    rw [hLe, (GSLit.fixedLayer_nested_core hLq heLz hez2).1 _ le_rfl]
    intro z hz
    obtain ⟨hzP, hzL⟩ := mem_inf.mp hz
    obtain ⟨k, hk⟩ := hS2 ⟨z, (mem_inf.mp hzP).1⟩
    have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    refine subset_closure ⟨mem_inf.mpr ⟨hzL, ?_⟩, j, hj⟩
    rw [centralizer_zpowers_eq]
    exact hPLe hz
  set Ce := centralizer ({e} : Set H) with hCe
  have haCe : h.a ∈ Ce := mem_centralizer_singleton_iff.mpr hea.symm
  let t : ↥Ce := ⟨h.a, haCe⟩
  have ht2 : orderOf t = 2 := by rw [Subgroup.orderOf_mk, h.orderOf_a]
  have hCt : centralizer ({t} : Set ↥Ce) = (Ca ⊓ Ce).subgroupOf Ce := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h1 => ⟨congrArg Subtype.val h1, y.2⟩, fun h1 => Subtype.ext h1.1⟩
  have hLeCaCe : Le ≤ Ca ⊓ Ce := by
    have h1 := GSLit.fixedLayer_le_inf L (zpowers e)
    rw [centralizer_zpowers_eq] at h1
    exact h1.trans (inf_le_inf_right _ hL1)
  have hLeCe : Le ≤ Ce := hLeCaCe.trans inf_le_right
  set T := Le.subgroupOf Ce with hT
  have hTC : T ≤ centralizer ({t} : Set ↥Ce) := by
    rw [hCt]
    intro y hy
    exact mem_subgroupOf.mpr (hLeCaCe hy)
  have hTc : IsPComponent 2 (T.subgroupOf (centralizer ({t} : Set ↥Ce))) := by
    rw [hCt]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two).mpr hLec
  have hTE : T ≤ pLayer ↥Ce 2 := by
    have h1 : T.subgroupOf (centralizer ({t} : Set ↥Ce)) ≤
        pLayer ↥(centralizer ({t} : Set ↥Ce)) 2 := le_sSup hTc
    have h2 := map_mono (f := (centralizer ({t} : Set ↥Ce)).subtype) h1
    rw [map_subgroupOf_eq_of_le hTC] at h2
    have hza : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, ht2, pow_one])
    have h3 := ClassicalInvolution.l2PrimeBalance ↥Ce (zpowers t) hza
    rw [centralizer_zpowers_eq] at h3
    exact h2.trans h3
  obtain ⟨N', hN'c, hTN', -⟩ := two_layer_fixed_component_orbit_location ht2 hTC hTc hTE
  set N := N'.map Ce.subtype with hN
  have hN1 : N ≤ Ce := map_subtype_le _
  have hNc : IsPComponent 2 (N.subgroupOf Ce) := by
    rw [hN, show (N'.map Ce.subtype).subgroupOf Ce = N' from
      comap_map_eq_self_of_injective Ce.subtype_injective N']
    exact hN'c
  have hNa : (conjugate N' t).map Ce.subtype = conjugate N h.a := by
    rw [map_conjugate]
    rfl
  have hLeN : Le ≤ N ⊔ conjugate N h.a := by
    have h1 := map_mono (f := Ce.subtype) hTN'
    rwa [hT, map_subgroupOf_eq_of_le hLeCe, Subgroup.map_sup, hNa] at h1
  obtain ⟨hNa1, hNac⟩ := OddQuot.isPComponent_conjugate_subgroupOf haCe hN1 hNc
  obtain ⟨hMC, hMc⟩ : M ≤ Ce ∧ IsPComponent 2 (M.subgroupOf Ce) := by
    have h1 := GSLit.isPComponent_map_centralizer (MulAut.conj g⁻¹) h.J_le h.isPComponent_J
    have h2 : (MulAut.conj g⁻¹) h.a = e := by rw [MulAut.conj_apply, inv_inv]
    rw [h2] at h1
    exact h1
  have hLeM : Le ≤ M := by
    by_cases h1 : N = M
    · rw [h1, hMa', sup_idem] at hLeN
      exact hLeN
    by_cases h2 : conjugate N h.a = M
    · refine absurd ?_ h1
      rw [← conjugate_conjugate_inv N h.a, h2]
      exact conjugate_eq_of_mem_normalizer (inv_mem hMa)
    exfalso
    apply hc'K
    have hNK : N ≤ coreActionKernel M :=
      B5a.le_coreActionKernel_of_ne hMC hN1 hMc hNc (Ne.symm h1)
    have hNaK : conjugate N h.a ≤ coreActionKernel M :=
      B5a.le_coreActionKernel_of_ne hMC hNa1 hMc hNac (Ne.symm h2)
    exact hPLLe.trans (hLeN.trans (sup_le hNK hNaK))
  have hLeL : Le ≤ L := (GSLit.fixedLayer_le_inf L (zpowers e)).trans inf_le_left
  have hJM : ↥h.J ≃* ↥M := h.J.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have hcard : Nat.card (M ⧸ pPrimeCore 2 M) ≤ Nat.card (Le ⧸ pPrimeCore 2 Le) := by
    have h1 := B5a.card_quotient_eq_of_sup hLeL hLesup hLecore
    have h2 : Nat.card (h.J ⧸ pPrimeCore 2 h.J) = Nat.card (L ⧸ pPrimeCore 2 L) :=
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr hJL
    have h3 : Nat.card (h.J ⧸ pPrimeCore 2 h.J) = Nat.card (M ⧸ pPrimeCore 2 M) :=
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr hJM
    omega
  have hsupM := B5a.sup_oddCoreIn_eq_of_card hLeM (B5a.inf_oddCoreIn_le_of_le hLeM) hcard
  have haM : h.a ∈ coreActionKernel M := by
    refine B5a.mem_coreActionKernel_of_sup hMa hLeM hsupM fun s hs => ?_
    have hsa : s * h.a = h.a * s := mem_centralizer_singleton_iff.mp (hLeCaCe hs).1
    rw [show s⁻¹ * h.a⁻¹ * s * h.a = s⁻¹ * h.a⁻¹ * (s * h.a) by group, hsa,
      show s⁻¹ * h.a⁻¹ * (h.a * s) = 1 by group]
    exact one_mem _
  apply B5aHW.a_not_mem_B h
  rw [hB]
  refine mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨haS, ?_⟩, ?_⟩, haM⟩
  · exact B5a.centralizer_le_coreActionKernel _ (mem_centralizer_iff.mpr fun j hj =>
      mem_centralizer_singleton_iff.mp (h.J_le hj))
  · exact mem_centralizer_singleton_iff.mpr hea.symm

theorem conj_fix
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {g : H} (hgW : g ∈ h.W) (heS : g⁻¹ * h.a * g ∈ h.S) (heP : g⁻¹ * h.a * g ∉ h.P) :
    h.B = h.P ⊓ centralizer ({g⁻¹ * h.a * g} : Set H) ⊓ coreActionKernel (conjugate h.J g) ∧
      g⁻¹ * h.a * g ∉ closure ((h.D : Set H) ∪ {h.a}) ⊓ centralizer ({h.x} : Set H) := by
  have hBC := ProperSectionB.kGroupBConclusion_of_inputs hS hU hheld h.kGroup_normalizer
  exact ⟨h.conj_fix_one hBC hgW heS heP, h.conj_fix_two hBC hgW heS heP⟩

end Hyp52W

end CFSG.ComponentClassification.GSThmB
