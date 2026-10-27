module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Setting
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
public import CFSG.HardMathSupport.Cooperstein.Proving.TwoPrimeSup
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Proving

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

@[expose, instance_reducible] def blockVCommGroup (S L : Subgroup G) : CommGroup ↥(blockV S L) :=
  commGroupOfElemAbelian (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _)

section Aux

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hp : Group.IsPerfect Q := ⟨h.1⟩
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  refine ⟨hp, hs, ?_⟩
  have := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using this

theorem isQuasisimple_to_open' {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

omit [Finite G] in
theorem sup_le_normalizer_blockV (S L : Subgroup G) :
    L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
  AscTenThree.le_normalizer_omegaOneCenterOf_twoCore (L ⊔ S)

theorem catalogSimpleSections_of_isKGroup {X : Type*} [Group X] (hX : CFSG.Open.IsKGroup X) :
    CatalogSimpleSections X := by
  intro K L hL hsimple hnonab
  let : L.Normal := hL
  let L' : Subgroup X := L.map K.subtype
  have hL'le : L' ≤ K := Subgroup.map_subtype_le _
  have hsub : L'.subgroupOf K = L :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective L
  have hnormal : (L'.subgroupOf K).Normal := by rw [hsub]; exact hL
  let e : K ⧸ L ≃* K ⧸ L'.subgroupOf K := QuotientGroup.quotientMulEquivOfEq hsub.symm
  let : IsSimpleGroup (K ⧸ L) := hsimple
  have hsimple' : IsSimpleGroup (K ⧸ L'.subgroupOf K) := e.symm.isSimpleGroup
  have hnonab' : ∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e a, e b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm h
  exact IsCatalogGroup.of_mulEquiv e (hX K L' hL'le hsimple' hnonab')

omit [Finite G] in
theorem exists_pow_mem_sup_subgroupOf {S L : Subgroup G} (hS : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (y : ↥(L ⊔ S)) :
    ∃ e : ℕ, y ^ 2 ^ e ∈ L.subgroupOf (L ⊔ S) := by
  have hn : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSL)
  have hy : (y : G) ∈ ((S ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm S L]; exact y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S L hSL] at hy
  obtain ⟨s, hs, l, hl, hsl⟩ := hy
  obtain ⟨e, he⟩ := hS ⟨s, hs⟩
  refine ⟨e, ?_⟩
  let q := QuotientGroup.mk' (L.subgroupOf (L ⊔ S))
  have hqs : q ⟨s, Subgroup.mem_sup_right hs⟩ ^ 2 ^ e = 1 := by
    rw [← map_pow]
    have : (⟨s, Subgroup.mem_sup_right hs⟩ : ↥(L ⊔ S)) ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
    rw [this, map_one]
  have hql : q ⟨l, Subgroup.mem_sup_left hl⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hl
  have hyq : q y = q ⟨s, Subgroup.mem_sup_right hs⟩ := by
    have : y = ⟨s, Subgroup.mem_sup_right hs⟩ * ⟨l, Subgroup.mem_sup_left hl⟩ := Subtype.ext hsl.symm
    rw [this, map_mul, hql, mul_one]
  have : q (y ^ 2 ^ e) = 1 := by rw [map_pow, hyq]; exact hqs
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

omit [Finite G] in
theorem exists_pow_mem_sup {S L : Subgroup G} (hS : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ L ⊔ S) :
    ∃ e : ℕ, y ^ 2 ^ e ∈ L := by
  obtain ⟨e, he⟩ := exists_pow_mem_sup_subgroupOf hS hSL ⟨y, hy⟩
  exact ⟨e, he⟩

omit [Finite G] in
theorem barM_inf_le_center_of_core_le {M C : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hLC : L ≤ Subgroup.normalizer (C : Set G)) (hcore : L ⊓ pCoreOf 2 M ≤ C) (hnle : ¬ L ≤ C) :
    barM M (L ⊓ C) ≤ (Subgroup.center ↥(barM M L)).map (barM M L).subtype := by
  have hq := hL.component.2.2
  have hπ := barMHomSub_surjective hL.le
  have hN : (barM M (L ⊓ C)).subgroupOf (barM M L) = ((L ⊓ C).subgroupOf L).map (barMHomSub hL.le) :=
    subgroupOf_barM_eq_map hL.le inf_le_left
  have hLn : ((L ⊓ C).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hLC hx⟩
  have hNn : ((barM M (L ⊓ C)).subgroupOf (barM M L)).Normal := by
    rw [hN]
    exact hLn.map _ hπ
  rcases StarAux.normal_le_center_or_eq_top hq.1 hq.2 _ hNn with hc | htop
  · intro y hy
    have hyL : y ∈ barM M L := by
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx).1, rfl⟩
    exact ⟨⟨y, hyL⟩, hc (show (⟨y, hyL⟩ : ↥(barM M L)) ∈
      (barM M (L ⊓ C)).subgroupOf (barM M L) from hy), rfl⟩
  · exfalso
    apply hnle
    intro l hl
    have hmem : barMHomSub hL.le ⟨l, hl⟩ ∈ (barM M (L ⊓ C)).subgroupOf (barM M L) := by
      rw [htop]; trivial
    rw [hN] at hmem
    obtain ⟨d, hd, hdl⟩ := hmem
    have hker : d⁻¹ * ⟨l, hl⟩ ∈ (barMHomSub hL.le).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, inv_mul_cancel]
    rw [ker_barMHomSub] at hker
    have h1 : ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ C := hcore ⟨(d⁻¹ * ⟨l, hl⟩ : ↥L).2, hker⟩
    have h2 : (d : G) ∈ C := (Subgroup.mem_subgroupOf.mp hd).2
    have : l = (d : G) * ((d⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [this]
    exact C.mul_mem h2 h1

omit [Finite G] in
theorem le_normalizer_centralizer_blockV (S L : Subgroup G) :
    L ⊔ S ≤ Subgroup.normalizer (Subgroup.centralizer (blockV S L : Set G) : Set G) :=
  InternalSec.le_normalizer_centralizer (sup_le_normalizer_blockV S L)

omit [Finite G] in
noncomputable def autOnHom (S L : Subgroup G) : ↥L →* ↥(autOn L (blockV S L)) :=
  (Setup.rho (blockV S L) L (le_sup_left.trans (sup_le_normalizer_blockV S L))).codRestrict _
    fun l => (Setup.range_rho (le_sup_left.trans (sup_le_normalizer_blockV S L))).le ⟨l, rfl⟩

omit [Finite G] in
theorem autOnHom_surjective (S L : Subgroup G) : Function.Surjective (autOnHom S L) := by
  rintro ⟨x, hx⟩
  have hLV := le_sup_left.trans (sup_le_normalizer_blockV S L)
  rw [← Setup.range_rho hLV] at hx
  obtain ⟨l, rfl⟩ := hx
  exact ⟨l, rfl⟩

omit [Finite G] in
theorem autOnHom_eq_one_iff (S L : Subgroup G) (l : ↥L) :
    autOnHom S L l = 1 ↔ (l : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
  have hLV := le_sup_left.trans (sup_le_normalizer_blockV S L)
  rw [← Setup.rho_eq_one_iff hLV l]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Aux

section Star

variable (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))

include hA hL hSL

omit hSL in
theorem pCoreOf_le_centralizer_blockV :
    pCoreOf 2 L ≤ Subgroup.centralizer (blockV S L : Set G) := by
  have hX : L ⊔ S ≤ X := sup_le hL.le hA.twoRadical.1
  have hQS : pCoreOf 2 X ≤ L ⊔ S := hA.twoCore_le.trans le_sup_right
  have h1 : pCoreOf 2 X ≤ pCoreOf 2 (L ⊔ S) :=
    normal_pGroup_le_pCoreOf 2 _ _ hQS
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr
        (hX.trans (localGroup_le_normalizer_pCoreOf 2 X)))
      (pCoreOf_isPGroup 2 X)
  exact (hL.toIsTwoPrimeComponent.inf_twoCore.symm.le.trans inf_le_right).trans
    (h1.trans (AscTenThree.le_centralizer_omegaOneCenterOf_self _))

theorem barM_inf_centralizer_le_center :
    barM X (L ⊓ Subgroup.centralizer (blockV S L : Set G)) ≤
      (Subgroup.center ↥(barM X L)).map (barM X L).subtype :=
  barM_inf_le_center_of_core_le hL.toIsTwoPrimeComponent
    (le_sup_left.trans (le_normalizer_centralizer_blockV S L))
    (hL.toIsTwoPrimeComponent.inf_twoCore.le.trans (pCoreOf_le_centralizer_blockV hA hL))
    (not_le_centralizer_blockV hA hL hSL)

theorem exists_central_factor_autOn :
    ∃ h : ↥(barM X L) →* ↥(autOn L (blockV S L)), Function.Surjective h ∧
      h.ker ≤ Subgroup.center ↥(barM X L) := by
  have hcore := pCoreOf_le_centralizer_blockV hA hL
  have hk1 : (barMHomSub hL.le).ker ≤ (autOnHom S L).ker := by
    intro x hx
    rw [ker_barMHomSub] at hx
    exact (autOnHom_eq_one_iff S L x).mpr
      (hcore (hL.toIsTwoPrimeComponent.inf_twoCore.le ⟨x.2, hx⟩))
  have hk2 : ∀ a ∈ (autOnHom S L).ker, barMHomSub hL.le a ∈ Subgroup.center ↥(barM X L) := by
    intro a ha
    have haC := (autOnHom_eq_one_iff S L a).mp ha
    have hmem : barMHomSub hL.le a ∈ (barM X (L ⊓ Subgroup.centralizer (blockV S L : Set G))).subgroupOf
        (barM X L) := by
      rw [subgroupOf_barM_eq_map hL.le inf_le_left]
      exact ⟨a, Subgroup.mem_subgroupOf.mpr ⟨a.2, haC⟩, rfl⟩
    obtain ⟨z, hz, hza⟩ := barM_inf_centralizer_le_center hA hL hSL (Subgroup.mem_subgroupOf.mp hmem)
    have : z = barMHomSub hL.le a := Subtype.ext hza
    rw [← this]
    exact hz
  obtain ⟨h, hs, hk, -⟩ := StarAux.exists_central_factor (barMHomSub hL.le)
    (barMHomSub_surjective hL.le) (autOnHom S L) (autOnHom_surjective S L) hk1 hk2
  exact ⟨h, hs, hk⟩

theorem isQuasisimple_autOn : CFSG.IsQuasisimple ↥(autOn L (blockV S L)) := by
  obtain ⟨h, hs, hk⟩ := exists_central_factor_autOn hA hL hSL
  have hq := hL.component.2.2
  have hperf : ⁅(⊤ : Subgroup ↥(barM X L)), (⊤ : Subgroup ↥(barM X L))⁆ = ⊤ := by
    rw [← commutator_def]; exact hq.1
  obtain ⟨e⟩ := StarAux.nonempty_quotientCenterEquiv_of_central_ker h hs hk hperf
  have := hq.2
  exact isQuasisimple_of_open' ⟨StarAux.commutator_eq_top_of_surjective h hs hq.1,
    e.symm.isSimpleGroup⟩

theorem nonempty_autOnCenterQuotientEquiv :
    Nonempty (↥(autOn L (blockV S L)) ⧸ Subgroup.center ↥(autOn L (blockV S L)) ≃*
      ↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) := by
  obtain ⟨h, hs, hk⟩ := exists_central_factor_autOn hA hL hSL
  have hq := hL.component.2.2
  have hperf : ⁅(⊤ : Subgroup ↥(barM X L)), (⊤ : Subgroup ↥(barM X L))⁆ = ⊤ := by
    rw [← commutator_def]; exact hq.1
  obtain ⟨e⟩ := StarAux.nonempty_quotientCenterEquiv_of_central_ker h hs hk hperf
  exact ⟨e.symm⟩

theorem pCoreOf_autOn_sup_eq_bot : pCoreOf 2 (autOn (L ⊔ S) (blockV S L)) = ⊥ := by
  have hPV := sup_le_normalizer_blockV S L
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hLc : IsTwoPrimeComponent (L ⊔ S) L :=
    isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1 hS2 hSL
  have hq := hLc.component.2.2
  let ρ' : ↥(L ⊔ S) →* ↥(autOn (L ⊔ S) (blockV S L)) :=
    (Setup.rho (blockV S L) (L ⊔ S) hPV).codRestrict _ fun l =>
      (Setup.range_rho hPV).le ⟨l, rfl⟩
  have hρ's : Function.Surjective ρ' := by
    rintro ⟨x, hx⟩
    rw [← Setup.range_rho hPV] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l, rfl⟩
  have hρ'1 : ∀ l : ↥(L ⊔ S), ρ' l = 1 ↔ (l : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
    intro l
    rw [← Setup.rho_eq_one_iff hPV l]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : CFSG.pCore 2 ↥(L ⊔ S) ≤ ρ'.ker := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 (L ⊔ S) := mem_pCoreOf_iff.mpr ⟨x, hx, rfl⟩
    exact (hρ'1 x).mpr (AscTenThree.le_centralizer_omegaOneCenterOf_self _ hx')
  let ψ : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S) →* ↥(autOn (L ⊔ S) (blockV S L)) :=
    QuotientGroup.lift _ ρ' hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hρ's y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hnormL : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSL)
  have hKn : (barM (L ⊔ S) L).Normal :=
    hnormL.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S))) (QuotientGroup.mk'_surjective _)
  have hcen := barM_inf_le_center_of_core_le hLc
    (le_sup_left.trans (le_normalizer_centralizer_blockV S L))
    (inf_le_right.trans (AscTenThree.le_centralizer_omegaOneCenterOf_self _))
    (not_le_centralizer_blockV hA hL hSL)
  have hbot := StarAux.pCore_eq_bot_of_surjective ψ hψ (barM (L ⊔ S) L) hq.1 hq.2
    (by
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨e, he⟩ := exists_pow_mem_sup_subgroupOf hS2 hSL y
      exact ⟨e, ⟨y ^ 2 ^ e, he, by simp⟩⟩)
    StarAux.pCore_quotient_pCore_eq_bot
    (by
      intro d hd hψd
      obtain ⟨y, hy, rfl⟩ := hd
      have hyC : (y : G) ∈ Subgroup.centralizer (blockV S L : Set G) :=
        (hρ'1 y).mp (by simpa [ψ] using hψd)
      obtain ⟨z, hz, hzy⟩ := hcen
        (show QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S)) y ∈
          barM (L ⊔ S) (L ⊓ Subgroup.centralizer (blockV S L : Set G)) from
        ⟨y, ⟨Subgroup.mem_subgroupOf.mp hy, hyC⟩, rfl⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_center_iff.mp hz ⟨k, hk⟩
      rw [← hzy]
      have h' := congrArg Subtype.val this
      exact h')
  rw [CFSG.Open.pCoreOf, hbot,
    Subgroup.map_bot]

theorem quasithinGenFitting_autOn_sup :
    quasithinGenFitting (autOn (L ⊔ S) (blockV S L)) = autOn L (blockV S L) := by
  have hLV := le_sup_left.trans (sup_le_normalizer_blockV S L)
  refine InternalSec.quasithinGenFitting_eq_of_two_pow
    (InternalSec.autOn_le_autOn_of_le le_sup_left)
    (InternalSec.autOn_normal_of (sup_le Subgroup.le_normalizer hSL))
    (isQuasisimple_to_open' (isQuasisimple_autOn hA hL hSL))
    (InternalSec.autOn_two_of hLV fun y hy => ?_)
    (pCoreOf_autOn_sup_eq_bot hA hL hSL)
  obtain ⟨e, he⟩ := exists_pow_mem_sup hA.twoRadical.isPGroup hSL hy
  exact ⟨e, Subgroup.mem_sup_left he⟩

theorem ffHyp_autOn (hX : CFSG.Open.IsKGroup ↥X) :
    @FFHyp ↥(blockV S L) (blockVCommGroup S L) _ (autOn (L ⊔ S) (blockV S L))
      (autOn L (blockV S L)) := by
  have hq := hL.component.2.2
  have hnonab : ∃ a b : ↥(barM X L) ⧸ Subgroup.center ↥(barM X L), a * b ≠ b * a :=
    (isQuasisimple_of_open' hq).2.2
  have hcat : IsCatalogGroup (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) :=
    ((catalogSimpleSections_of_isKGroup hX).quotient (CFSG.pCore 2 ↥X))
      (barM X L) (Subgroup.center ↥(barM X L)) inferInstance hq.2 hnonab
  obtain ⟨e⟩ := nonempty_autOnCenterQuotientEquiv hA hL hSL
  refine ⟨(quasithinGenFitting_autOn_sup hA hL hSL).symm, isQuasisimple_autOn hA hL hSL, ?_,
    IsCatalogGroup.of_mulEquiv e hcat⟩
  have h5 := pCoreOf_autOn_sup_eq_bot hA hL hSL
  rw [CFSG.Open.pCoreOf] at h5
  exact (Subgroup.map_eq_bot_iff_of_injective _ (autOn (L ⊔ S) (blockV S L)).subtype_injective).mp h5

end Star

end CFSG.HardMathSupport.Cooperstein.Coordinator
