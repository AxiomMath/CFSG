module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasicHW

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace B5aHW

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem isQuasisimple_J : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 h.isPComponent_J
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe h.J_le))).1 hq

theorem isPComponent_fixedLayer :
    IsPComponent 2 ((GSLit.fixedLayer h.J h.B).subgroupOf
      (centralizer ({h.a} : Set H) ⊓ centralizer (h.B : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hs, -, -⟩ := id h.isPComponent_J
  exact GSLit.fixedLayer_isPComponent h.J_le hs
    (h.B_le.trans (inf_le_left.trans (h.S_le.trans inf_le_left)))
    (h.B_le.trans inf_le_right) h.isPGroup_B (isQuasisimple_J h)

theorem fixedLayer_ne_bot : GSLit.fixedLayer h.J h.B ≠ ⊥ := by
  intro hbot
  have := B5a.nontrivial_of_isPComponent_subgroupOf
    ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_inf_right _ h.J_le))
    (isPComponent_fixedLayer h)
  rw [hbot] at this
  exact not_nontrivial (⊥ : Subgroup H) this

theorem fixedLayer_le_V : GSLit.fixedLayer h.J h.B ≤ h.V := by
  show GSLit.fixedLayer h.J h.B ≤ layerIn (normalizer (h.B : Set H))
  rw [← h.conjClosure_eq]
  exact B5a.le_conjClosure _ _

theorem V_le_layerIn_centralizer : h.V ≤ layerIn (centralizer (h.B : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) h.B h.isPGroup_B
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  exact h1

theorem V_le_centralizer : h.V ≤ centralizer (h.B : Set H) :=
  (V_le_layerIn_centralizer h).trans (map_subtype_le _)

theorem a_not_mem_B : h.a ∉ h.B := by
  intro haB
  have hcomm : ⁅h.V, zpowers h.a⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, centralizer_zpowers_eq]
    exact (V_le_centralizer h).trans (centralizer_le (Set.singleton_subset_iff.mpr haB))
  rw [h.commutator_eq] at hcomm
  exact fixedLayer_ne_bot h (le_bot_iff.mp (hcomm ▸ fixedLayer_le_V h))

theorem conj_mem_P {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P := by
  obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
  have hsJ : s⁻¹ ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le (inv_mem hs))).2
  have h1 := conj_mem_coreActionKernel hsJ hyC
  rw [inv_inv] at h1
  exact mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), h1⟩

end B5aHW

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

theorem wbarImage_conjugate (X : Subgroup H) {y : H} (hy : y ∈ h.W) :
    wbarImage h.B (conjugate X y) = conjugate (wbarImage h.B X) (wbarMk h.B ⟨y, hy⟩) := by
  unfold wbarImage
  rw [show (conjugate X y).subgroupOf h.W = conjugate (X.subgroupOf h.W) ⟨y, hy⟩ from
    (conjugate_subgroupOf_eq _ h.W ⟨y, hy⟩).symm, map_conjugate]

theorem wbarImage_commutator_eq_bot_of_layer (hBC : ProperSectionB.KGroupBConclusion ↥h.W)
    {E : Subgroup H} (hBE : h.B ≤ E) (hEW : E ≤ h.W) (hE2 : IsPGroup 2 E) {X Y : Subgroup H}
    (hX : X ≤ layerIn (centralizer (E : Set H))) (hY : Y ≤ layerIn (centralizer (E : Set H)))
    (hXY : ⁅X, Y⁆ ≤ oddCoreIn (centralizer (E : Set H))) (hXp : Group.IsPerfect X) :
    ⁅wbarImage h.B X, wbarImage h.B Y⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Hc := centralizer (E : Set H) with hHc
  set NWE := h.W ⊓ normalizer (E : Set H) with hNWE
  have hHcW : Hc ≤ h.W :=
    (centralizer_le (SetLike.coe_subset_coe.mpr hBE)).trans (centralizer_le_normalizer _)
  have hHcNWE : Hc ≤ NWE := le_inf hHcW (centralizer_le_normalizer _)
  have hNWEn : NWE ≤ normalizer (Hc : Set H) := fun y hy =>
    B5a.mem_normalizer_centralizer (mem_inf.mp hy).2
  have hlay : layerIn Hc ≤ layerIn NWE := by
    have : (Hc.subgroupOf NWE).Normal := (normal_subgroupOf_iff_le_normalizer hHcNWE).mpr hNWEn
    have h1 := LBalance.pLayer_relative_normal_mono 2 Hc NWE hHcNWE
    rwa [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  have hodd : oddCoreIn Hc ≤ oddCoreIn NWE := B5a.oddCoreIn_le_of_le_normalizer hHcNWE hNWEn
  have hBprop : ⁅layerIn NWE, oddCoreIn NWE⁆ ≤ oddCoreIn h.W := by
    have hE' : E.subgroupOf h.W ≠ ⊥ := by
      intro hbot
      apply h.B_ne_bot
      rw [eq_bot_iff]
      intro b hb
      have : (⟨b, hEW (hBE hb)⟩ : h.W) ∈ E.subgroupOf h.W := hBE hb
      rw [hbot, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
    have hE'2 : IsPGroup 2 (E.subgroupOf h.W) := hE2.comap_subtype
    have h1 := (hBC.2.2 (E.subgroupOf h.W) hE' hE'2).1
    rw [← subgroupOf_normalizer_eq hEW, B5a.assembly_oddCore_eq, B5a.assembly_oddCore_eq] at h1
    have h2 := map_mono (f := h.W.subtype) h1
    rw [map_commutator, UnbalancedCorr.map_pLayer_subgroupOf_eq, B5a.map_oddCoreIn_subgroupOf]
      at h2
    exact h2
  have himg_comm : ∀ X Y : Subgroup H, X ≤ h.W → Y ≤ h.W →
      wbarImage h.B ⁅X, Y⁆ = ⁅wbarImage h.B X, wbarImage h.B Y⁆ := by
    intro X Y hX hY
    unfold wbarImage
    rw [← map_commutator]
    congr 1
    apply map_injective h.W.subtype_injective
    have hXY : ⁅X, Y⁆ ≤ h.W := (commutator_mono hX hY).trans (commutator_le_self _)
    rw [map_subgroupOf_eq_of_le hXY, map_commutator, map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hY]
  have himg_bot : ∀ X : Subgroup H, X ≤ oddCoreIn h.W → wbarImage h.B X = ⊥ := by
    intro X hX
    unfold wbarImage
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro y hy
    have h1 : (y : H) ∈ oddCoreIn h.W := hX hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp h1
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    show QuotientGroup.mk' (pPrimeCore 2 ↥h.W) z ∈ pCore 2 (↥h.W ⧸ pPrimeCore 2 ↥h.W)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
    exact one_mem _
  have hlW : layerIn Hc ≤ h.W := (map_subtype_le _).trans hHcW
  have hXW : X ≤ h.W := hX.trans hlW
  have hYW : Y ≤ h.W := hY.trans hlW
  have hAperf : Group.IsPerfect (wbarImage h.B X) := by
    have : Group.IsPerfect (X.subgroupOf h.W) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hXW).symm.toMonoidHom)
        (subgroupOfEquivOfLe hXW).symm.surjective
    exact Group.IsPerfect.map _
  have hc1 : ⁅⁅wbarImage h.B X, wbarImage h.B Y⁆, wbarImage h.B X⁆ = ⊥ := by
    have hD : ⁅X, Y⁆ ≤ h.W := (commutator_mono hXW hYW).trans (commutator_le_self _)
    rw [← himg_comm _ _ hXW hYW, ← himg_comm _ _ hD hXW]
    apply himg_bot
    calc ⁅⁅X, Y⁆, X⁆ ≤ ⁅oddCoreIn NWE, layerIn NWE⁆ :=
          commutator_mono (hXY.trans hodd) (hX.trans hlay)
      _ = ⁅layerIn NWE, oddCoreIn NWE⁆ := commutator_comm _ _
      _ ≤ oddCoreIn h.W := hBprop
  have hc2 : ⁅⁅wbarImage h.B Y, wbarImage h.B X⁆, wbarImage h.B X⁆ = ⊥ := by
    rw [commutator_comm (wbarImage h.B Y)]
    exact hc1
  have hc3 := commutator_commutator_eq_bot_of_rotate hc1 hc2
  rwa [commutator_eq_self] at hc3

theorem conj_fix_one (hBC : ProperSectionB.KGroupBConclusion ↥h.W) {g : H} (hgW : g ∈ h.W)
    (heS : g⁻¹ * h.a * g ∈ h.S) (heP : g⁻¹ * h.a * g ∉ h.P) :
    h.B = h.P ⊓ centralizer ({g⁻¹ * h.a * g} : Set H) ⊓ coreActionKernel (conjugate h.J g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := g⁻¹ * h.a * g with he
  set Y₁ := h.P ⊓ centralizer ({e} : Set H) ⊓ coreActionKernel (conjugate h.J g) with hY₁
  have hS2 := h.isPGroup_S
  have hB2 := h.isPGroup_B
  have hBP : h.B ≤ h.P := h.B_le
  have hPS : h.P ≤ h.S := inf_le_left
  have hBY : h.B ≤ Y₁ := by
    intro b hb
    have hgb : g * b * g⁻¹ ∈ h.B := (mem_normalizer_iff.mp hgW b).mp hb
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hBP hb, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff, he]
      have hc : g * b * g⁻¹ * h.a = h.a * (g * b * g⁻¹) :=
        mem_centralizer_singleton_iff.mp (mem_inf.mp (h.S_le (hPS (hBP hgb)))).1
      calc b * (g⁻¹ * h.a * g) = g⁻¹ * (g * b * g⁻¹ * h.a) * g := by group
        _ = g⁻¹ * (h.a * (g * b * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * h.a * g * b := by group
    · have h1 := B5a.conj_mem_coreActionKernel_conjugate (h.B_le hgb).2 g
      rwa [show g⁻¹ * (g * b * g⁻¹) * g = b by group] at h1
  refine le_antisymm hBY ?_
  by_contra hnot
  have hlt : h.B < Y₁ := lt_of_le_of_ne hBY fun heq => hnot heq.ge
  set E := Y₁ ⊓ normalizer (h.B : Set H) with hE
  have hY₁2 : IsPGroup 2 Y₁ := hS2.to_le (inf_le_left.trans (inf_le_left.trans hPS))
  have hBE : h.B < E := by
    have : Group.IsNilpotent Y₁ := hY₁2.isNilpotent
    have hsub : h.B.subgroupOf Y₁ < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hnot ?_
      intro y hy
      have : (⟨y, hy⟩ : Y₁) ∈ h.B.subgroupOf Y₁ := htop ▸ mem_top _
      exact this
    obtain ⟨y, hyN, hyB⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hsub)
    rw [← subgroupOf_normalizer_eq hBY] at hyN
    refine lt_of_le_of_ne (le_inf hBY le_normalizer) fun heq => hyB ?_
    have : (y : H) ∈ E := mem_inf.mpr ⟨y.2, hyN⟩
    rw [← heq] at this
    exact this
  have hEY : E ≤ Y₁ := inf_le_left
  have hEP : E ≤ h.P := hEY.trans (inf_le_left.trans inf_le_left)
  have hEN : E ≤ normalizer (h.B : Set H) := inf_le_right
  have hE2 : IsPGroup 2 E := hY₁2.to_le hEY
  have hcard : Nat.card h.B < Nat.card E := Subgroup.card_lt_of_lt hBE
  obtain ⟨L, hLN, hLc, hLa, hsup, hfix⟩ := h.isoCorr_of_le_T E (le_inf hEP hEN) hcard
  have hEe : E ≤ centralizer ({e} : Set H) := hEY.trans (inf_le_left.trans inf_le_right)
  have heE : e ∈ centralizer (E : Set H) :=
    mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hEe hy)
  have heNE : e ∈ normalizer (E : Set H) := centralizer_le_normalizer _ heE
  have heJ : e ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le heS)).2
  have hJq := B5aHW.isQuasisimple_J h
  have hEC : E ≤ coreActionKernel h.J := hEP.trans inf_le_right
  have hJEe : conjugate (GSLit.fixedLayer h.J E) e = GSLit.fixedLayer h.J E := by
    change (GSLit.fixedLayer h.J E).map (MulAut.conj e⁻¹).toMonoidHom = _
    rw [GSLit.map_fixedLayer]
    change GSLit.fixedLayer (conjugate h.J e) (conjugate E e) = _
    rw [conjugate_eq_of_mem_normalizer heJ, conjugate_eq_of_mem_normalizer heNE]
  have heJE : e ∈ normalizer (GSLit.fixedLayer h.J E : Set H) :=
    mem_normalizer_of_conjugate_eq hJEe
  have hLe : conjugate L e = L := by
    obtain ⟨hLeN, hLec⟩ := OddQuot.isPComponent_conjugate_subgroupOf heNE hLN hLc
    have hsup' : GSLit.fixedLayer h.J E ⊔ oddCoreIn (conjugate L e) = conjugate L e := by
      rw [← B5a.conjugate_oddCoreIn, ← hJEe]
      change (GSLit.fixedLayer h.J E).map (MulAut.conj e⁻¹).toMonoidHom ⊔
        (oddCoreIn L).map (MulAut.conj e⁻¹).toMonoidHom = L.map (MulAut.conj e⁻¹).toMonoidHom
      rw [← Subgroup.map_sup, hsup]
    exact GSLit.eq_of_isPComponent_cover hLeN hLec hLN hLc hsup' hsup
  have heLN : e ∈ normalizer (L : Set H) := mem_normalizer_of_conjugate_eq hLe
  have hJEL : GSLit.fixedLayer h.J E ≤ L := hsup ▸ le_sup_left
  obtain ⟨hJEsup, hJEcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hEC hE2
  have heL : e ∉ coreActionKernel L := by
    intro heL
    apply heP
    refine mem_inf.mpr ⟨heS, B5a.mem_coreActionKernel_of_sup heJ
      ((GSLit.fixedLayer_le_inf h.J E).trans inf_le_left) hJEsup fun t ht => ?_⟩
    have h1 : t⁻¹ * e⁻¹ * t * e ∈ oddCoreIn L := (mem_coreActionKernel.mp heL).2 t (hJEL ht)
    have h2 : t⁻¹ * e⁻¹ * t * e ∈ GSLit.fixedLayer h.J E := by
      have h3 := (mem_normalizer_iff.mp (inv_mem heJE) t).mp ht
      rw [inv_inv] at h3
      rw [show t⁻¹ * e⁻¹ * t * e = t⁻¹ * (e⁻¹ * t * e) by group]
      exact mul_mem (inv_mem ht) h3
    have h4 := B5a.inf_oddCoreIn_le_of_le hJEL (mem_inf.mpr ⟨h2, h1⟩)
    change t⁻¹ * e⁻¹ * t * e ∈ (pPrimeCore 2 ↥(GSLit.fixedLayer h.J E)).map _ at h4
    rw [hJEcore] at h4
    exact (mem_inf.mp h4).2
  set M := conjugate h.J g with hM
  obtain ⟨hMC, hMc⟩ : M ≤ centralizer ({e} : Set H) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({e} : Set H))) := by
    have h1 := GSLit.isPComponent_map_centralizer (MulAut.conj g⁻¹) h.J_le h.isPComponent_J
    have h2 : (MulAut.conj g⁻¹) h.a = e := by rw [MulAut.conj_apply, inv_inv]
    rw [h2] at h1
    exact h1
  have hJM : ↥h.J ≃* ↥M := h.J.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 hJM)).1 hJq
  have hEM : E ≤ coreActionKernel M := hEY.trans inf_le_right
  obtain ⟨-, -, hMsub, -, -⟩ := id hMc
  have hMEc := GSLit.fixedLayer_isPComponent hMC hMsub hEe hEM hE2 hMq
  obtain ⟨hMEsup, hMEcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hEM hE2
  set ME := GSLit.fixedLayer M E with hME
  set Hc := centralizer (E : Set H) with hHc
  have hMEHc : ME ≤ Hc := (GSLit.fixedLayer_le_inf M E).trans inf_le_right
  have hMEe : ME ≤ centralizer ({e} : Set H) :=
    (GSLit.fixedLayer_le_inf M E).trans (inf_le_left.trans hMC)
  let e' : ↥Hc := ⟨e, heE⟩
  have he2 : orderOf e = 2 := by
    rw [he, show g⁻¹ * h.a * g = (MulAut.conj g⁻¹) h.a by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, h.orderOf_a]
  have he'2 : orderOf e' = 2 := by rw [Subgroup.orderOf_mk, he2]
  have hCe' : centralizer ({e'} : Set ↥Hc) =
      (centralizer ({e} : Set H) ⊓ Hc).subgroupOf Hc := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h1 => ⟨congrArg Subtype.val h1, y.2⟩, fun h1 => Subtype.ext h1.1⟩
  set T := ME.subgroupOf Hc with hT
  have hTC : T ≤ centralizer ({e'} : Set ↥Hc) := by
    rw [hCe']
    intro y hy
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hMEe hy, y.2⟩)
  have hTc : IsPComponent 2 (T.subgroupOf (centralizer ({e'} : Set ↥Hc))) := by
    rw [hCe']
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two).mpr hMEc
  have hTE : T ≤ pLayer ↥Hc 2 := by
    have h1 : T.subgroupOf (centralizer ({e'} : Set ↥Hc)) ≤
        pLayer ↥(centralizer ({e'} : Set ↥Hc)) 2 := le_sSup hTc
    have h2 := map_mono (f := (centralizer ({e'} : Set ↥Hc)).subtype) h1
    rw [map_subgroupOf_eq_of_le hTC] at h2
    have hza : IsPGroup 2 (zpowers e') := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, he'2, pow_one])
    have h3 := ClassicalInvolution.l2PrimeBalance ↥Hc (zpowers e') hza
    rw [centralizer_zpowers_eq] at h3
    exact h2.trans h3
  obtain ⟨N', hN'c, hTN', -⟩ := two_layer_fixed_component_orbit_location he'2 hTC hTc hTE
  have hLHc : L ≤ Hc := by
    have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) E hE2
    rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
    have h2 : L ≤ (pLayer ↥(normalizer (E : Set H)) 2).map (normalizer (E : Set H)).subtype := by
      have h3 := map_mono (f := (normalizer (E : Set H)).subtype)
        (show L.subgroupOf (normalizer (E : Set H)) ≤ pLayer _ 2 from le_sSup hLc)
      rwa [map_subgroupOf_eq_of_le hLN] at h3
    exact (h2.trans h1).trans (map_subtype_le _)
  have hL'c : IsPComponent 2 (L.subgroupOf Hc) :=
    B5a.isPComponent_subgroupOf_of_le hLHc (centralizer_le_normalizer _) hLc
  set L' := L.subgroupOf Hc with hL'
  have hL'e : conjugate L' e' = L' := by
    rw [hL', conjugate_subgroupOf_eq]
    change (conjugate L e).subgroupOf Hc = _
    rw [hLe]
  have hnot : ¬ T ≤ L' := by
    intro hTL
    have hMEL : ME ≤ L := by
      intro y hy
      exact hTL (show (⟨y, hMEHc hy⟩ : Hc) ∈ T from hy)
    have hcard : Nat.card (L ⧸ pPrimeCore 2 L) ≤ Nat.card (ME ⧸ pPrimeCore 2 ME) := by
      have h1 := B5a.card_quotient_le_of_sup hJEL hsup
      have h2 := B5a.card_quotient_eq_of_sup
        ((GSLit.fixedLayer_le_inf h.J E).trans inf_le_left) hJEsup hJEcore
      have h3 : Nat.card (ME ⧸ pPrimeCore 2 ME) = Nat.card (M ⧸ pPrimeCore 2 M) :=
        B5a.card_quotient_eq_of_sup
          ((GSLit.fixedLayer_le_inf M E).trans inf_le_left) hMEsup hMEcore
      have h4 : Nat.card (h.J ⧸ pPrimeCore 2 h.J) = Nat.card (M ⧸ pPrimeCore 2 M) :=
        UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr hJM
      omega
    have hsupL := B5a.sup_oddCoreIn_eq_of_card hMEL (B5a.inf_oddCoreIn_le_of_le hMEL) hcard
    refine heL (B5a.mem_coreActionKernel_of_sup heLN hMEL hsupL fun t ht => ?_)
    have hte : t * e = e * t := mem_centralizer_singleton_iff.mp (hMEe ht)
    rw [show t⁻¹ * e⁻¹ * t * e = t⁻¹ * e⁻¹ * (t * e) by group, hte,
      show t⁻¹ * e⁻¹ * (e * t) = 1 by group]
    exact one_mem _
  have hne1 : L' ≠ N' := by
    intro heq
    apply hnot
    have h1 := hTN'
    rw [← heq, hL'e, sup_idem] at h1
    exact h1
  have hne2 : L' ≠ conjugate N' e' := by
    intro heq
    apply hnot
    have hN' : N' = L' := by
      have h1 := congrArg (fun X => conjugate X e'⁻¹) heq
      simp only [conjugate_conjugate_inv] at h1
      rw [← h1]
      have h2 := congrArg (fun X => conjugate X e'⁻¹) hL'e
      simp only [conjugate_conjugate_inv] at h2
      exact h2.symm
    have h1 := hTN'
    rw [hN', hL'e, sup_idem] at h1
    exact h1
  have hN'e : IsPComponent 2 (conjugate N' e') := isPComponent_conjugate hN'c e'
  have hcomm_mod : ⁅L', N' ⊔ conjugate N' e'⁆ ≤ pPrimeCore 2 ↥Hc := by
    have hO : ∀ K : Subgroup ↥Hc, IsPComponent 2 K →
        (pPrimeCore 2 K).map K.subtype ≤ pPrimeCore 2 ↥Hc := by
      intro K hK
      obtain ⟨-, -, hs, -, -⟩ := id hK
      rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs]
      exact inf_le_right
    obtain ⟨-, h1⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two L' N' hL'c hN'c
    obtain ⟨-, -, h1c, -⟩ := h1 hne1
    obtain ⟨-, h2⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two L' _ hL'c hN'e
    obtain ⟨-, -, h2c, -⟩ := h2 hne2
    have h1' : ⁅L', N'⁆ ≤ pPrimeCore 2 ↥Hc := h1c.trans (inf_le_left.trans (hO L' hL'c))
    have h2' : ⁅L', conjugate N' e'⁆ ≤ pPrimeCore 2 ↥Hc :=
      h2c.trans (inf_le_left.trans (hO L' hL'c))
    have hk : ∀ X Y : Subgroup ↥Hc, ⁅X, Y⁆ ≤ pPrimeCore 2 ↥Hc ↔
        ⁅X.map (QuotientGroup.mk' (pPrimeCore 2 ↥Hc)),
          Y.map (QuotientGroup.mk' (pPrimeCore 2 ↥Hc))⁆ = ⊥ := by
      intro X Y
      rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hk] at h1' h2' ⊢
    rw [Subgroup.map_sup]
    rw [commutator_eq_bot_iff_le_centralizer] at h1' h2' ⊢
    exact B5a.le_centralizer_sup h1' h2'
  have hJEHc : GSLit.fixedLayer h.J E ≤ Hc := hJEL.trans hLHc
  have hDO : ⁅GSLit.fixedLayer h.J E, ME⁆ ≤ oddCoreIn Hc := by
    have h1 : ⁅(GSLit.fixedLayer h.J E).subgroupOf Hc, T⁆ ≤ pPrimeCore 2 ↥Hc :=
      (commutator_mono (show (GSLit.fixedLayer h.J E).subgroupOf Hc ≤ L' from
        fun _ hy => hJEL hy) hTN').trans hcomm_mod
    have h2 := map_mono (f := Hc.subtype) h1
    rwa [map_commutator, map_subgroupOf_eq_of_le hJEHc, hT, map_subgroupOf_eq_of_le hMEHc] at h2
  have hHcW : Hc ≤ h.W :=
    (centralizer_le (SetLike.coe_subset_coe.mpr hBE.le)).trans (centralizer_le_normalizer _)
  have hJEW : GSLit.fixedLayer h.J E ≤ h.W := hJEHc.trans hHcW
  have hMEW : ME ≤ h.W := hMEHc.trans hHcW
  have hLlay : L ≤ layerIn Hc := by
    have h1 := map_mono (f := Hc.subtype) (show L' ≤ pLayer ↥Hc 2 from le_sSup hL'c)
    rwa [map_subgroupOf_eq_of_le hLHc] at h1
  have hMEl : ME ≤ layerIn Hc := by
    have h1 : T ≤ pLayer ↥Hc 2 :=
      hTN'.trans (sup_le (le_sSup hN'c) (le_sSup hN'e))
    have h2 := map_mono (f := Hc.subtype) h1
    rwa [map_subgroupOf_eq_of_le hMEHc] at h2
  have hJEperf : Group.IsPerfect (GSLit.fixedLayer h.J E) :=
    B5a.isPerfect_of_isPComponent_subgroupOf
      ((GSLit.fixedLayer_le_inf h.J E).trans (inf_le_inf_right _ h.J_le))
      (GSLit.fixedLayer_isPComponent h.J_le (id h.isPComponent_J).choose_spec.2.1
        (hEP.trans (inf_le_left.trans (h.S_le.trans inf_le_left))) hEC hE2 hJq)
  have hAperf : Group.IsPerfect (wbarImage h.B (GSLit.fixedLayer h.J E)) := by
    have : Group.IsPerfect ((GSLit.fixedLayer h.J E).subgroupOf h.W) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJEW).symm.toMonoidHom)
        (subgroupOfEquivOfLe hJEW).symm.surjective
    exact Group.IsPerfect.map _
  have hAM := h.wbarImage_commutator_eq_bot_of_layer hBC hBE.le hEN hE2 (hJEL.trans hLlay) hMEl
    hDO hJEperf
  have hkey : ∀ X Y : Subgroup H, X ≤ Y → Y ≤ h.W → X ⊔ oddCoreIn Y = Y →
      IsQuasisimple (wbarImage h.B Y) → Group.IsPerfect (wbarImage h.B X) →
      wbarImage h.B X = wbarImage h.B Y := by
    intro X Y hXY hYW hsupXY hYq hXp
    have hOY : oddCoreIn Y ≤ Y := map_subtype_le _
    have hOW : oddCoreIn Y ≤ h.W := hOY.trans hYW
    refine B5a.eq_of_quasisimple_sup_odd hYq (O := wbarImage h.B (oddCoreIn Y))
      (map_mono fun _ hy => hXY hy) (map_mono fun _ hy => hOY hy) ?_ ?_ ?_
    · have h1 : Y.subgroupOf h.W ≤ normalizer ((oddCoreIn Y).subgroupOf h.W : Set ↥h.W) := by
        intro y hy
        have hyN := B5a.mem_normalizer_oddCoreIn (le_normalizer (show (y : H) ∈ Y from hy))
        rw [mem_normalizer_iff]
        intro z
        rw [mem_subgroupOf, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
        exact mem_normalizer_iff.mp hyN z
      exact (map_mono h1).trans (le_normalizer_map _)
    · have h1 := Subgroup.card_map_dvd ((oddCoreIn Y).subgroupOf h.W) (wbarMk h.B)
      have h2 : Nat.card ((oddCoreIn Y).subgroupOf h.W) = Nat.card (pPrimeCore 2 Y) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hOW).toEquiv]
        exact (Nat.card_congr ((pPrimeCore 2 Y).equivMapOfInjective _
          Y.subtype_injective).toEquiv).symm
      rw [h2] at h1
      exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
    · unfold wbarImage
      rw [← Subgroup.map_sup, ← subgroupOf_sup (hXY.trans hYW) hOW, hsupXY]
  set gbar := wbarMk h.B ⟨g, hgW⟩ with hgbar
  have hJBW : GSLit.fixedLayer h.J h.B ≤ h.W :=
    (GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hBEle : h.B ≤ E := hBE.le
  obtain ⟨hJBE, hJBsup⟩ := GSLit.fixedLayer_nested hJq hEC hE2 hBEle
  obtain ⟨hMBE, hMBsup⟩ := GSLit.fixedLayer_nested hMq hEM hE2 hBEle
  have hXq : IsQuasisimple (wbarImage h.B (GSLit.fixedLayer h.J h.B)) := h.isStandard_bar.1
  have hJimg : wbarImage h.B (GSLit.fixedLayer h.J E) =
      wbarImage h.B (GSLit.fixedLayer h.J h.B) := hkey _ _ hJBE hJBW hJBsup hXq hAperf
  have hMB : GSLit.fixedLayer M h.B = conjugate (GSLit.fixedLayer h.J h.B) g := by
    have h1 := GSLit.map_fixedLayer (MulAut.conj g⁻¹) h.J h.B
    have h2 : h.B.map (MulAut.conj g⁻¹).toMonoidHom = h.B := conjugate_eq_of_mem_normalizer hgW
    rw [h2] at h1
    exact h1.symm
  have hMBW : GSLit.fixedLayer M h.B ≤ h.W :=
    (GSLit.fixedLayer_le_inf M h.B).trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hMBimg : wbarImage h.B (GSLit.fixedLayer M h.B) =
      conjugate (wbarImage h.B (GSLit.fixedLayer h.J h.B)) gbar := by
    rw [hMB]
    unfold wbarImage
    rw [show (conjugate (GSLit.fixedLayer h.J h.B) g).subgroupOf h.W =
        conjugate ((GSLit.fixedLayer h.J h.B).subgroupOf h.W) ⟨g, hgW⟩ from
      (conjugate_subgroupOf_eq _ h.W ⟨g, hgW⟩).symm, map_conjugate]
  have hMq' : IsQuasisimple (wbarImage h.B (GSLit.fixedLayer M h.B)) := by
    rw [hMBimg]
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr
      ((wbarImage h.B (GSLit.fixedLayer h.J h.B)).equivMapOfInjective _
        (MulAut.conj gbar⁻¹).injective)).1 hXq
  have hMEperf : Group.IsPerfect ME :=
    B5a.isPerfect_of_isPComponent_subgroupOf
      ((GSLit.fixedLayer_le_inf M E).trans (inf_le_inf_right _ hMC)) hMEc
  have hMperf : Group.IsPerfect (wbarImage h.B ME) := by
    have : Group.IsPerfect (ME.subgroupOf h.W) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMEW).symm.toMonoidHom)
        (subgroupOfEquivOfLe hMEW).symm.surjective
    exact Group.IsPerfect.map _
  have hMimg : wbarImage h.B ME = wbarImage h.B (GSLit.fixedLayer M h.B) :=
    hkey _ _ hMBE hMBW hMBsup hMq' hMperf
  apply h.isStandard_bar.2.2.2.2 gbar
  rw [← hMBimg, ← hMimg, ← hJimg]
  exact hAM

end Hyp52W

end CFSG.ComponentClassification.GSThmB
