module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OuterAct
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog71Cover

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

@[expose] def CF24cCenterLe : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsPGroup 2 (center L) →
    Nonempty (L ⧸ center L ≃* Blueprint.NativeSporadic.Suz) →
    ∀ α : MulAut L, α * α = 1 → ∀ M : Subgroup L, M ≤ CatFactsL4U4.OutInv.fixSub α →
      IsComponent (M.subgroupOf (CatFactsL4U4.OutInv.fixSub α)) →
      Blueprint.LieModel (↥M ⧸ center ↥M) .PSL 3 2 2 → center L ≤ (center ↥M).map M.subtype

@[expose] def CF24cCenterGe : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsPGroup 2 (center L) →
    Nonempty (L ⧸ center L ≃* Blueprint.NativeSporadic.Suz) →
    ∀ α : MulAut L, α * α = 1 → ∀ M : Subgroup L, M ≤ CatFactsL4U4.OutInv.fixSub α →
      IsComponent (M.subgroupOf (CatFactsL4U4.OutInv.fixSub α)) →
      Blueprint.LieModel (↥M ⧸ center ↥M) .PSL 3 2 2 → (center ↥M).map M.subtype ≤ center L

namespace Suz24

theorem mem_center_of_commutator_mem_center {E : Type*} [Group E] [Group.IsPerfect E] {x : E}
    (hx : ∀ e : E, ⁅x, e⁆ ∈ center E) : x ∈ center E := by
  let ψ : E →* ↥(center E) :=
    { toFun := fun e => ⟨⁅x, e⁆, hx e⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun e f => by
        apply Subtype.ext
        have hf := Subgroup.mem_center_iff.mp (hx f) e
        simp only [commutatorElement_def, Subgroup.coe_mul] at hf ⊢
        calc x * (e * f) * x⁻¹ * (e * f)⁻¹ =
            x * e * x⁻¹ * e⁻¹ * (e * (x * f * x⁻¹ * f⁻¹) * e⁻¹) := by group
          _ = x * e * x⁻¹ * e⁻¹ * (x * f * x⁻¹ * f⁻¹) := by rw [hf]; group }
  have hker : commutator E ≤ ψ.ker := by
    rw [commutator_eq_closure, closure_le]
    rintro _ ⟨u, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (ψ u).2 (ψ v : E)).symm
  rw [Subgroup.mem_center_iff]
  intro e
  have he : e ∈ ψ.ker := hker (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top e)
  have h1 : ⁅x, e⁆ = 1 := congrArg Subtype.val he
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem isQuasisimple_of_surjective {E Q : Type*} [Group E] [Group Q] [Group.IsPerfect E]
    (g : E →* Q) (hg : Function.Surjective g) (hQ : IsQuasisimple Q)
    (hker : g.ker ≤ center E) : IsQuasisimple E := by
  obtain ⟨-, hsimp, a, b, hab⟩ := hQ
  set φ : E →* Q ⧸ center Q := (QuotientGroup.mk' (center Q)).comp g with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hg
  have hkerφ : φ.ker = center E := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      apply mem_center_of_commutator_mem_center
      intro e
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hx (g e)).symm
    · intro x hx
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro q
      obtain ⟨e, rfl⟩ := hg q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx e]
  set e : E ⧸ center E ≃* Q ⧸ center Q :=
    (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs) with he
  refine ⟨inferInstance, (MulEquiv.isSimpleGroup_congr e).mpr hsimp, e.symm a, e.symm b, ?_⟩
  intro hc
  apply hab
  have := congrArg e hc
  simpa using this

section Hyp

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H) (hKa : conjugate h.K h.a = h.K)

noncomputable abbrev alpha : MulAut (OddBar h.K) :=
  oddBarConj h.K ⟨h.a, CatFactsL4U4.a_mem_normalizer_K h hKa⟩

theorem alpha_mul_self : alpha h hKa * alpha h hKa = 1 := by
  rw [alpha, ← map_mul]
  have e : (⟨h.a, CatFactsL4U4.a_mem_normalizer_K h hKa⟩ : ↥(normalizer (h.K : Set H))) *
      ⟨h.a, CatFactsL4U4.a_mem_normalizer_K h hKa⟩ = 1 := by
    apply Subtype.ext
    show h.a * h.a = 1
    rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  rw [e, map_one]

theorem imJB_le_fixSub : CatFactsL4U4.imJB h ≤ CatFactsL4U4.OutInv.fixSub (alpha h hKa) :=
  fun _ hx => CatFactsL4U4.oddBarConj_a_apply_of_mem_imJB h hKa hx

theorem mem_center_of_kbar_eq_one {x : OddBar h.K} (hx : CatFactsL4U4.kbar hKa x = 1) :
    x ∈ center (OddBar h.K) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [CatFactsL4U4.kbar_mk, wbarMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact CatFactsL4U4.OutInv.mem_center_of_mem_oddTwoCore hx

theorem kbar_mem_centralizer {x : OddBar h.K}
    (hx : x ∈ CatFactsL4U4.OutInv.fixSub (alpha h hKa)) :
    CatFactsL4U4.kbar hKa x ∈
      centralizer ({wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩} : Set (Wbar h.B)) := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [CatFactsL4U4.OutInv.mem_fixSub, alpha, oddBarConj_apply_mk] at hx
  have h1 := congrArg (CatFactsL4U4.kbar hKa) hx
  rw [CatFactsL4U4.kbar_mk, CatFactsL4U4.kbar_mk] at h1
  set w : h.W := ⟨h.a, h.a_mem_normalizer⟩ with hw
  set u : h.W := ⟨(k : H), CatFactsL4U4.K_le_W h k.2⟩ with hu
  have h2 : wbarMk h.B (w * u * w⁻¹) = wbarMk h.B u := by
    rw [← h1]
    congr 1
  rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h2
  rw [mem_centralizer_singleton_iff, CatFactsL4U4.kbar_mk]
  exact h2.symm

noncomputable abbrev toJhat : ↥(GSLit.fixedLayer h.J h.B) →* ↥(CatFactsL4U4.imJB h) :=
  (CatFactsL4U4.jbToK h hKa).codRestrict (CatFactsL4U4.imJB h) fun j => by
    rw [← CatFactsL4U4.range_jbToK h hKa]
    exact ⟨j, rfl⟩

theorem toJhat_surjective : Function.Surjective (toJhat h hKa) := by
  rintro ⟨x, hx⟩
  rw [← CatFactsL4U4.range_jbToK h hKa] at hx
  obtain ⟨j, rfl⟩ := hx
  exact ⟨j, rfl⟩

theorem imJB_isComponent : IsComponent ((CatFactsL4U4.imJB h).subgroupOf
    (CatFactsL4U4.OutInv.fixSub (alpha h hKa))) := by
  set F := CatFactsL4U4.OutInv.fixSub (alpha h hKa) with hF
  set Jt := CatFactsL4U4.imJB h with hJt
  set C := centralizer ({wbarMk h.B ⟨h.a, h.a_mem_normalizer⟩} : Set (Wbar h.B)) with hC
  set JBb := wbarImage h.B (GSLit.fixedLayer h.J h.B) with hJBb
  obtain ⟨hJBbC, hcomp⟩ := h.isComponent_bar
  have hJtF : Jt ≤ F := imJB_le_fixSub h hKa
  have hmap : Jt.map (CatFactsL4U4.kbar hKa) = JBb := CatFactsL4U4.map_kbar_imJB hKa
  have : Group.IsPerfect ↥Jt :=
    UnbalancedGS.isPerfect_of_commutator_eq (CatFactsL4U4.imJB_commutator_eq h hKa)
  have hJBbq : IsQuasisimple ↥JBb :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hJBbC)).mp hcomp.1
  set g : ↥Jt →* ↥JBb := ((CatFactsL4U4.kbar hKa).comp Jt.subtype).codRestrict JBb fun x => by
    rw [← hmap]
    exact mem_map_of_mem _ x.2 with hg
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hgk : g.ker ≤ center ↥Jt := by
    intro x hx
    have h1 : CatFactsL4U4.kbar hKa (x : OddBar h.K) = 1 := by
      simpa [hg] using congrArg Subtype.val hx
    have h2 := mem_center_of_kbar_eq_one h hKa h1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp h2 (y : OddBar h.K))
  have hJtq : IsQuasisimple ↥Jt := isQuasisimple_of_surjective g hgs hJBbq hgk
  refine ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hJtF)).mpr hJtq,
    ?_⟩
  set f : ↥F →* ↥C := ((CatFactsL4U4.kbar hKa).comp F.subtype).codRestrict C fun x =>
    kbar_mem_centralizer h hKa x.2 with hf
  set M : Subgroup ↥F := (JBb.subgroupOf C).comap f with hM
  have hMsn : M.IsSubnormal := hcomp.2.comap f
  have hJtM : Jt.subgroupOf F ≤ M := by
    intro x hx
    rw [mem_subgroupOf] at hx
    show ((f x : ↥C) : Wbar h.B) ∈ JBb
    rw [← hmap]
    exact mem_map_of_mem _ hx
  have hN : ((Jt.subgroupOf F).subgroupOf M).Normal := by
    constructor
    intro n hn m
    rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    have hm : CatFactsL4U4.kbar hKa (((m : ↥F) : OddBar h.K)) ∈ JBb := m.2
    rw [← hmap] at hm
    obtain ⟨j, hj, hje⟩ := hm
    have hu : CatFactsL4U4.kbar hKa (j⁻¹ * ((m : ↥F) : OddBar h.K)) = 1 := by
      rw [map_mul, map_inv, hje, inv_mul_cancel]
    have hc := Subgroup.mem_center_iff.mp (mem_center_of_kbar_eq_one h hKa hu)
      (((n : ↥F) : OddBar h.K))
    have e : (((m * n * m⁻¹ : ↥M) : ↥F) : OddBar h.K) = j * ((n : ↥F) : OddBar h.K) * j⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((m : ↥F) : OddBar h.K) * ((n : ↥F) : OddBar h.K) * ((m : ↥F) : OddBar h.K)⁻¹ =
          j * ((j⁻¹ * ((m : ↥F) : OddBar h.K)) * ((n : ↥F) : OddBar h.K)) *
            (j⁻¹ * ((m : ↥F) : OddBar h.K))⁻¹ * j⁻¹ := by group
        _ = j * ((n : ↥F) : OddBar h.K) * j⁻¹ := by rw [← hc]; group
    rw [e]
    exact Jt.mul_mem (Jt.mul_mem hj hn) (Jt.inv_mem hj)
  exact Subgroup.IsSubnormal.trans hJtM hN.isSubnormal hMsn

include hKa in
theorem isQuasisimple_imJB : IsQuasisimple ↥(CatFactsL4U4.imJB h) :=
  (LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (subgroupOfEquivOfLe (imJB_le_fixSub h hKa))).mp (imJB_isComponent h hKa).1

theorem mem_center_iff (j : ↥(GSLit.fixedLayer h.J h.B)) :
    toJhat h hKa j ∈ center ↥(CatFactsL4U4.imJB h) ↔
      j ∈ Open.fusionZStar ↥(GSLit.fixedLayer h.J h.B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Jt := CatFactsL4U4.imJB h with hJt
  set g := toJhat h hKa with hg
  have hq := isQuasisimple_imJB h hKa
  have : Group.IsPerfect ↥Jt :=
    UnbalancedGS.isPerfect_of_commutator_eq (CatFactsL4U4.imJB_commutator_eq h hKa)
  rw [OddQuot.mem_fusionZStar_iff]
  constructor
  · intro hc m
    apply CatFactsL4U4.ker_jbToK_le h hKa
    rw [MonoidHom.mem_ker]
    have h1 : g ⁅j, m⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hc (g m)).symm
    exact congrArg Subtype.val h1
  · intro hj
    set N : Subgroup ↥Jt := (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)).map g with hN
    have : N.Normal := Subgroup.Normal.map inferInstance g (toJhat_surjective h hKa)
    have hNc : N ≤ center ↥Jt := by
      rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq N with hc | ht
      · exact hc
      · exfalso
        have hodd : Odd (Nat.card ↥Jt) := by
          have h1 : Nat.card N ∣ Nat.card (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) :=
            Subgroup.card_map_dvd _ _
          rw [ht, Subgroup.card_top] at h1
          exact Nat.Coprime.coprime_dvd_right h1 (CFSG.pPrimeCore_coprime_card (p := 2))
            |> Nat.coprime_two_left.mp
        exact CatFactsL4U4.OutInv.false_of_isSolvable hq (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
    apply mem_center_of_commutator_mem_center
    intro x
    obtain ⟨m, rfl⟩ := toJhat_surjective h hKa x
    rw [← map_commutatorElement]
    exact hNc (mem_map_of_mem g (hj m))

include hKa in
theorem nonempty_imJB_center_equiv :
    Nonempty (↥(GSLit.fixedLayer h.J h.B) ⧸ Open.fusionZStar ↥(GSLit.fixedLayer h.J h.B) ≃*
      ↥(CatFactsL4U4.imJB h) ⧸ center ↥(CatFactsL4U4.imJB h)) := by
  set ρ := (QuotientGroup.mk' (center ↥(CatFactsL4U4.imJB h))).comp (toJhat h hKa) with hρ
  have hρs : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (toJhat_surjective h hKa)
  have hker : Open.fusionZStar ↥(GSLit.fixedLayer h.J h.B) = ρ.ker := by
    ext j
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_center_iff h hKa]
  exact ⟨QuotientGroup.liftEquiv _ hρs hker⟩

theorem nonempty_fixedLayer_zStar_equiv :
    Nonempty (↥(GSLit.fixedLayer h.J h.B) ⧸ Open.fusionZStar ↥(GSLit.fixedLayer h.J h.B) ≃*
      ZStarBar h.J) := by
  obtain ⟨e, -⟩ := CatFactsL4U4.exists_oddBar_JB_equiv h
  exact ⟨(oddBarCenterEquiv ↥(GSLit.fixedLayer h.J h.B)).symm.trans
    ((CFSG.GorensteinWalter.FieldTransport.quotientCenterMulEquiv e).trans
      (oddBarCenterEquiv ↥h.J))⟩

include hKa in
theorem lieModel_imJB (hJ : Blueprint.LieModel (ZStarBar h.J) .PSL 3 2 2) :
    Blueprint.LieModel (↥(CatFactsL4U4.imJB h) ⧸ center ↥(CatFactsL4U4.imJB h)) .PSL 3 2 2 := by
  obtain ⟨e₁⟩ := nonempty_imJB_center_equiv h hKa
  obtain ⟨e₂⟩ := nonempty_fixedLayer_zStar_equiv h
  exact LieType.CurtisTits.lieModel_of_mulEquiv (e₂.symm.trans e₁) hJ

end Hyp

end Suz24

theorem cfProp24c_of_center (hLe : CF24cCenterLe) (hGe : CF24cCenterGe) : CFProp24c := by
  intro H _ _ h hJ hKa hZ hSuz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Jt := CatFactsL4U4.imJB h with hJt
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := CatFactsL4U4.fixedLayer_le_K h hKa
  have hK2 : IsPGroup 2 (center (OddBar h.K)) :=
    CatFactsL4U4.isPGroup_two_center_of_pPrimeCore_eq_bot
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hKs : Nonempty (OddBar h.K ⧸ center (OddBar h.K) ≃* Blueprint.NativeSporadic.Suz) :=
    hSuz.map fun e => (oddBarCenterEquiv ↥h.K).trans e
  have hle := hLe (OddBar h.K) h.isQuasisimple_K hK2 hKs (Suz24.alpha h hKa)
    (Suz24.alpha_mul_self h hKa) Jt (Suz24.imJB_le_fixSub h hKa) (Suz24.imJB_isComponent h hKa)
    (Suz24.lieModel_imJB h hKa hJ)
  have hge := hGe (OddBar h.K) h.isQuasisimple_K hK2 hKs (Suz24.alpha h hKa)
    (Suz24.alpha_mul_self h hKa) Jt (Suz24.imJB_le_fixSub h hKa) (Suz24.imJB_isComponent h hKa)
    (Suz24.lieModel_imJB h hKa hJ)
  refine ⟨?_, ?_⟩
  ·
    have hnt : Nontrivial ↥(center (OddBar h.K)) := (nontrivial_iff_ne_bot _).mpr hZ
    obtain ⟨n, hn, hcard⟩ := hK2.nontrivial_iff_card.mp hnt
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center (OddBar h.K))) 2
      (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
    obtain ⟨x, hx, hxc⟩ := hle c.2
    obtain ⟨j, rfl⟩ := Suz24.toJhat_surjective h hKa x
    have hjZ := (Suz24.mem_center_iff h hKa j).mp hx
    have h2 : 2 ∣ orderOf j := by
      have h1 : orderOf (Suz24.toJhat h hKa j) ∣ orderOf j := orderOf_map_dvd _ _
      have h3 : orderOf (Suz24.toJhat h hKa j) = 2 := by
        have e : ((Suz24.toJhat h hKa j : ↥Jt) : OddBar h.K) = (c : OddBar h.K) := hxc
        rw [← Subgroup.orderOf_coe, e, Subgroup.orderOf_coe, hc]
      rw [h3] at h1
      exact h1
    have h4 : orderOf j ∣ Nat.card (Open.fusionZStar ↥JB) := by
      have := orderOf_dvd_natCard (⟨j, hjZ⟩ : Open.fusionZStar ↥JB)
      rwa [Subgroup.orderOf_mk] at this
    exact even_iff_two_dvd.mpr (h2.trans h4)
  ·
    rintro _ ⟨j, hj, rfl⟩
    have hjc := (Suz24.mem_center_iff h hKa j).mpr hj
    have hjK : (j : H) ∈ h.K := hJBK j.2
    have hz : (QuotientGroup.mk ⟨(j : H), hjK⟩ : OddBar h.K) ∈ center (OddBar h.K) :=
      hge ⟨_, hjc, rfl⟩
    refine ⟨⟨(j : H), hjK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, OddQuot.mem_fusionZStar_iff]
    intro m
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz _).symm

end CFSG.ComponentClassification.GSThmB
