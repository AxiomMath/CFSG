module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sylow
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Kinds
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
  CFSG.ComponentClassification

@[expose] def Ivk93CovOneClass : Prop :=
  ∀ (J : Type) [Group J] [Finite J],
    (NativeSporadic.IsSporadic J .McL ∨ NativeSporadic.IsSporadic J .Ly) →
    ∀ u v : J, orderOf u = 2 → orderOf v = 2 → IsConj u v

theorem ivk93cov_eq_one_of_two_group_odd {Y : Type} [Group Y] {T : Subgroup Y} (hT : IsPGroup 2 ↥T)
    {k : Y} (hk : k ∈ T) (hodd : Odd (orderOf k)) : k = 1 := by
  obtain ⟨m, hm⟩ := hT ⟨k, hk⟩
  have h1 : orderOf k ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hm
    simpa using this
  have h2 : orderOf k = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hodd)) h1
  exact orderOf_eq_one_iff.1 h2

theorem ivk93cov_conj_into_sylow {Y : Type} [Group Y] [Finite Y] (T : Sylow 2 Y) (u : Y)
    (hu : orderOf u = 2) : ∃ g : Y, g * u * g⁻¹ ∈ (T : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgroup : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨overSylow, hle⟩ := hgroup.exists_le_sylow
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq Y overSylow T
  refine ⟨actor, ?_⟩
  rw [← hactor, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
  exact ⟨u, hle (Subgroup.mem_zpowers u), rfl⟩

theorem ivk93cov_le_of_subnormal_surj {Y Q : Type} [Group Y] [Finite Y] [Group Q] [Finite Q]
    (ρ : Y →* Q) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    {A : Subgroup Y} (hA : A.IsSubnormal) (hAρ : ∀ q : Q, ∃ a ∈ A, ρ a = q) {U : Subgroup Y}
    (hU : IsPGroup 2 ↥U) : U ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hUT⟩ := hU.exists_le_sylow
  refine hUT.trans ?_
  obtain ⟨PA, hPA⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_subnormal T hA
  let ρ₁ : ↥A →* Q := ρ.comp A.subtype
  have hρ₁ : Function.Surjective ρ₁ := fun q => by
    obtain ⟨a, ha, h⟩ := hAρ q
    exact ⟨⟨a, ha⟩, h⟩
  let R₁ : Sylow 2 Q := PA.mapSurjective hρ₁
  let R₂ : Sylow 2 Q := T.mapSurjective hρ
  have hR₁ : (R₁ : Subgroup Q) = ((T : Subgroup Y) ⊓ A).map ρ := by
    rw [Sylow.coe_mapSurjective, ← hPA, Subgroup.map_map]
  have hR₂ : (R₂ : Subgroup Q) = (T : Subgroup Y).map ρ := Sylow.coe_mapSurjective hρ T
  have hle : (R₁ : Subgroup Q) ≤ R₂ := by
    rw [hR₁, hR₂]
    exact Subgroup.map_mono inf_le_left
  have hcard : Nat.card ↥(R₂ : Subgroup Q) ≤ Nat.card ↥(R₁ : Subgroup Q) := by
    rw [Sylow.card_eq_multiplicity R₂, Sylow.card_eq_multiplicity R₁]
  have heq : (R₁ : Subgroup Q) = R₂ := Subgroup.eq_of_le_of_card_ge hle hcard
  intro t ht
  have h1 : ρ t ∈ (R₂ : Subgroup Q) := by
    rw [hR₂]
    exact Subgroup.mem_map_of_mem ρ ht
  rw [← heq, hR₁] at h1
  obtain ⟨s, ⟨hsT, hsA⟩, hs⟩ := h1
  have hk : s⁻¹ * t ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  have hkT : s⁻¹ * t ∈ (T : Subgroup Y) := (T : Subgroup Y).mul_mem ((T : Subgroup Y).inv_mem hsT) ht
  have h1' : s⁻¹ * t = 1 := ivk93cov_eq_one_of_two_group_odd T.isPGroup' hkT (hodd _ hk)
  have : t = s := by
    have := congrArg (fun w => s * w) h1'
    simpa using this
  rw [this]
  exact hsA

theorem ivk93cov_cfg_of_lift {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (hctx : Stage2Ctx G z k S) {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hcov : IsDoubleCoverOfAlt (CentralizerBar z) n) {H : Subgroup G} (hCH : Cen z ≤ H)
    (hperf : PerfInJ H) :
    ∃ (B : Subgroup (HBar H)) (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H)),
      B ≤ generalizedFitting (HBar H) ∧ B ≤ barIn H (Cen z) ∧
      IsPComponent 2 (B.subgroupOf (barIn H (Cen z))) ∧
      (B.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = ⊤ ∧
      Ivk93Cov (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) n
        (B.subgroupOf (generalizedFitting (HBar H))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  have hcomp : IsComponent (⊤ : Subgroup (CentralizerBar z)) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hcov.1, Subgroup.IsSubnormal.top⟩
  obtain ⟨B, hBJ, hBC, hxB, hBcomp, hBmap⟩ :=
    lift_comp hz2 hCH hperf (L := ⊤) hcomp (Subgroup.mem_top _)
  have hxJ : mkH H ⟨z, hzmem⟩ ∈ generalizedFitting (HBar H) := hBJ hxB
  refine ⟨B, hxJ, hBJ, hBC, hBcomp, hBmap, ?_⟩
  set x : HBar H := mkH H ⟨z, hzmem⟩ with hx
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  have hcent : centralizer ({x} : Set (HBar H)) = C' := centralizer_mk_eq H hz2 hzmem
  have hcJ := centralizer_singleton_subgroupOf (J := generalizedFitting (HBar H)) hxJ
  rw [hcent] at hcJ
  have hx2 : orderOf x = 2 := orderOf_mk_eq_two H (by rw [← Subgroup.orderOf_coe]; exact hz2)
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have hY : pPrimeCore 2 (CentralizerBar z) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  set A : Subgroup ↥C' := B.subgroupOf C' with hA
  let ρ₁ : ↥A →* CentralizerBar z := (cenToBar H hCH).comp A.subtype
  have hρ₁ : Function.Surjective ρ₁ := by
    intro y
    have hy : y ∈ A.map (cenToBar H hCH) := by rw [hBmap]; exact Subgroup.mem_top y
    obtain ⟨a, ha, hay⟩ := hy
    exact ⟨⟨a, ha⟩, hay⟩
  have hodd₁ : ∀ u ∈ ρ₁.ker, Odd (orderOf u) := by
    intro u hu
    have hu1 : (cenToBar H hCH) (u : ↥C') = 1 := MonoidHom.mem_ker.1 hu
    have := hodd (u : ↥C') (MonoidHom.mem_ker.2 hu1)
    rwa [Subgroup.orderOf_coe] at this
  have hcovA : IsDoubleCoverOfAlt (↥A ⧸ pPrimeCore 2 ↥A) n :=
    ivk93cov_isDoubleCoverOfAlt_of_equiv (quotEquivOfHom ρ₁ hρ₁ hodd₁ hY).symm hcov
  have e₂ : ↥A ≃* ↥(B.subgroupOf (generalizedFitting (HBar H))) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans (Subgroup.subgroupOfEquivOfLe hBJ).symm
  have comp : IsPCompIn 2 (centralizer ({(⟨x, hxJ⟩ : ↥(generalizedFitting (HBar H)))} :
      Set ↥(generalizedFitting (HBar H)))) (B.subgroupOf (generalizedFitting (HBar H))) := by
    rw [hcJ]
    exact ⟨fun y hy => hBC hy,
      ComponentClassification.Sp4Rec.isPComponent_subgroupOf_restrict hBC hBJ hBcomp⟩
  refine ⟨?_, hn8, hn11, comp, Subgroup.mem_subgroupOf.2 hxB, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hx2
  · exact ivk93cov_isDoubleCoverOfAlt_of_equiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e₂) hcovA

theorem ivk93Kind_sporadic_of (hJ : Ivk93CovJ) (hOne : Ivk93CovOneClass) {k : Kind}
    (hk : k = Kind.mcl ∨ k = Kind.ly) : Ivk93Kind k := by
  classical
  intro G _ _ z S hctx H hH hCH hO2 hsimple hnab hperf h2cl
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  obtain ⟨n, hn, hs⟩ : ∃ n : ℕ, (8 ≤ n ∧ n ≤ 11) ∧ Stage1Sporadic G z S n := by
    have hd := hctx.data
    rcases hk with rfl | rfl
    · cases hd with
      | mcl h =>
        obtain ⟨n, hn, hs⟩ := h
        exact ⟨n, by omega, hs⟩
    · cases hd with
      | ly h =>
        obtain ⟨n, hn, hs⟩ := h
        exact ⟨n, by omega, hs⟩
  obtain ⟨B, hzJ, hBJ, hBC, hBcomp, hBmap, hcfg⟩ :=
    ivk93cov_cfg_of_lift hctx hn.1 hn.2 hs.cover hCH hperf
  set J : Subgroup (HBar H) := generalizedFitting (HBar H) with hJdef
  have hcen := isCentralInvolution_zbar hctx hCH hzJ
  have hgh : GHList ↥J := ghList_of_subgroup_of_quotient hctx.std.kgh hH (mkH H)
    (QuotientGroup.mk'_surjective _) J hsimple hnab
  have hres := hJ ↥J hsimple hgh _ hcen n _ hcfg
  have hspor : NativeSporadic.IsSporadic ↥J .McL ∨ NativeSporadic.IsSporadic ↥J .Ly := by
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hone := hOne ↥J hspor
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  have hSC : barIn H S ≤ C' := Subgroup.map_mono (fun a ha => hctx.S_le_Cen ha)
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have hρ := cenToBar_surjective H hCH
  have hAsub : (B.subgroupOf C').IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hBcomp
    exact h
  have hAρ : ∀ q : CentralizerBar z, ∃ a ∈ B.subgroupOf C', cenToBar H hCH a = q := by
    intro q
    have hq : q ∈ (B.subgroupOf C').map (cenToBar H hCH) := by
      rw [hBmap]
      exact Subgroup.mem_top q
    obtain ⟨a, ha, haq⟩ := hq
    exact ⟨a, ha, haq⟩
  have hU : IsPGroup 2 ↥((barIn H S).subgroupOf C') := by
    have h1 : IsPGroup 2 ↥(barIn H S) := by
      rw [← hT]
      exact T.isPGroup'
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  have hSB : (barIn H S).subgroupOf C' ≤ B.subgroupOf C' :=
    ivk93cov_le_of_subnormal_surj (cenToBar H hCH) hρ hodd hAsub hAρ hU
  have hSJ : ∀ s ∈ T, s ∈ J := by
    intro s hs'
    have hs'' : s ∈ barIn H S := by
      rw [← hT]
      exact hs'
    have h1 : (⟨s, hSC hs''⟩ : ↥C') ∈ (barIn H S).subgroupOf C' := hs''
    exact hBJ (hSB h1)
  have hmove : ∀ u : HBar H, orderOf u = 2 → ∃ (g : HBar H) (hg : g * u * g⁻¹ ∈ J),
      IsConj u (g * u * g⁻¹) ∧ orderOf (⟨g * u * g⁻¹, hg⟩ : ↥J) = 2 := by
    intro u hu
    obtain ⟨g, hg⟩ := ivk93cov_conj_into_sylow T u hu
    have hgJ : g * u * g⁻¹ ∈ J := hSJ _ hg
    have hconj : IsConj u (g * u * g⁻¹) := (isConj_iff.2 ⟨g, rfl⟩)
    refine ⟨g, hgJ, hconj, ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_eq_of_isConj' hconj).symm.trans hu
  obtain ⟨a, b, ha, hb, hab⟩ := h2cl
  obtain ⟨g, hga, hca, hoa⟩ := hmove a ha
  obtain ⟨h, hhb, hcb, hob⟩ := hmove b hb
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone ⟨g * a * g⁻¹, hga⟩ ⟨h * b * h⁻¹, hhb⟩ hoa hob)
  have hc' : (c : HBar H) * (g * a * g⁻¹) * (c : HBar H)⁻¹ = h * b * h⁻¹ := congrArg Subtype.val hc
  exact hab (hca.trans ((isConj_iff.2 ⟨(c : HBar H), hc'⟩).trans hcb.symm))

end CFSG.GH74.GLS.IVK.Proofs2
