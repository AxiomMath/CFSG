module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitTools
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen4
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleNotTwoGroupQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer

public section

section Ckpt6

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.UnbalancedGS.OrbitFixedComponent
  CFSG.ComponentClassification.UnbalancedLayer

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

theorem swap_case_exists {H : Type*} [Group H] [Finite H] {t : H} (ht : orderOf t = 2)
    (M : Subgroup H) (hM : IsPComponent 2 M) (hne : M ≠ conjugate M t) :
    ∃ T : Subgroup H, T ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H) ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hM'comp : IsPComponent 2 (conjugate M t) :=
    ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
      (MulAut.conj t⁻¹)).1 M).mp hM
  have hMsub : M.IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).1
  have hconjM : ∀ x, x ∈ conjugate M t ↔ t * x * t⁻¹ ∈ M := by
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      change t * (t⁻¹ * m * t⁻¹⁻¹) * t⁻¹ ∈ M
      simpa [mul_assoc] using hm
    · intro hx
      refine ⟨t * x * t⁻¹, hx, ?_⟩
      change t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x
      group
  generalize hK : M ⊔ conjugate M t = K
  generalize hCK : K ⊓ centralizer ({t} : Set H) = CK
  have hCKK : CK ≤ K := hCK ▸ inf_le_left
  have hCKt : ∀ c ∈ CK, c * t = t * c := fun c hc =>
    mem_centralizer_singleton_iff.mp (hCK ▸ hc : c ∈ K ⊓ centralizer ({t} : Set H)).2
  have htK : ∀ x, x ∈ K ↔ t * x * t⁻¹ ∈ K := by
    have hle : ∀ x ∈ K, t * x * t⁻¹ ∈ K := by
      intro x hx
      have hsub : K ≤ K.comap (MulAut.conj t).toMonoidHom := by
        rw [← hK]
        refine sup_le (fun m hm => ?_) (fun m hm => ?_)
        · apply mem_sup_right
          rw [hconjM]
          change t * (t * m * t⁻¹) * t⁻¹ ∈ M
          have h1 : t * (t * m * t⁻¹) * t⁻¹ = m := by
            calc t * (t * m * t⁻¹) * t⁻¹ = (t * t) * m * (t * t)⁻¹ := by group
              _ = m := by rw [htt]; group
          rw [h1]
          exact hm
        · apply mem_sup_left
          exact (hconjM m).mp hm
      exact hsub hx
    intro x
    refine ⟨hle x, fun h => ?_⟩
    have h1 := hle _ h
    have h2 : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt]; group
    rwa [h2] at h1
  set N := pPrimeCore 2 H with hNdef
  have hNcop : Nat.Coprime 2 (Nat.card N) := pPrimeCore_coprime_card (p := 2) (G := H)
  obtain ⟨-, hbijH⟩ := CatalogueBPrimeJoin.canonical_prime_component_lift (X := H) 2
  set A := M.map (QuotientGroup.mk' N) with hAdef
  set B := (conjugate M t).map (QuotientGroup.mk' N) with hBdef
  have hA : IsComponent A := hbijH.mapsTo hM
  have hB : IsComponent B := hbijH.mapsTo hM'comp
  have hAB : A ≠ B := fun h => hne (hbijH.injOn hM hM'comp h)
  have hcomm : ⁅A, B⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hA hB).resolve_left hAB
  have hABc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha
    exact (mem_centralizer_iff.mp h1 b hb).symm
  have hAq : IsQuasisimple A := hA.1
  have hAcore : pPrimeCore 2 A = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 A hA.2,
      pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.bot_subgroupOf]
  set tb : H ⧸ N := (t : H ⧸ N) with htbdef
  have htb : tb * tb = 1 := by rw [htbdef, ← QuotientGroup.mk_mul, htt, QuotientGroup.mk_one]
  have htbinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb
  have hπconj : ∀ g : H, ((t * g * t⁻¹ : H) : H ⧸ N) = tb * (g : H ⧸ N) * tb⁻¹ := fun g => by
    rw [htbdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hAB_conj : ∀ x, x ∈ B ↔ tb * x * tb⁻¹ ∈ A := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← hπconj]
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have h1 : (g : H ⧸ N) = g' := hgg'.symm
      refine ⟨t * g' * t⁻¹, (hconjM g').mp hg', ?_⟩
      change ((t * g' * t⁻¹ : H) : H ⧸ N) = ((t * g * t⁻¹ : H) : H ⧸ N)
      rw [hπconj, hπconj, h1]
    · rintro ⟨m, hm, hmg⟩
      refine ⟨t⁻¹ * m * t, ?_, ?_⟩
      · exact (hconjM _).mpr (by simpa [mul_assoc] using hm)
      · change ((t⁻¹ * m * t : H) : H ⧸ N) = g
        have h1 : ((m : H) : H ⧸ N) = ((t * g * t⁻¹ : H) : H ⧸ N) := hmg
        have h2 : ((t⁻¹ * m * t : H) : H ⧸ N) = tb⁻¹ * (m : H ⧸ N) * tb := by
          rw [htbdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [h2, h1, hπconj]
        group
  have hBA_conj : ∀ x, x ∈ A ↔ tb * x * tb⁻¹ ∈ B := by
    intro x
    rw [hAB_conj]
    have h1 : tb * (tb * x * tb⁻¹) * tb⁻¹ = x := by
      calc tb * (tb * x * tb⁻¹) * tb⁻¹ = (tb * tb) * x * (tb * tb)⁻¹ := by group
        _ = x := by rw [htb]; group
    rw [h1]
  have hconjAB : (A ⊔ B).map (MulAut.conj tb).toMonoidHom = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hsub : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj tb).toMonoidHom :=
        sup_le (fun a ha => mem_sup_right ((hBA_conj a).mp ha))
          (fun b hb => mem_sup_left ((hAB_conj b).mp hb))
      exact hsub hx
    · intro x hx
      have hsub : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj tb).toMonoidHom :=
        sup_le (fun a ha => mem_sup_right ((hBA_conj a).mp ha))
          (fun b hb => mem_sup_left ((hAB_conj b).mp hb))
      refine ⟨tb * x * tb⁻¹, hsub hx, ?_⟩
      change tb * (tb * x * tb⁻¹) * tb⁻¹ = x
      calc tb * (tb * x * tb⁻¹) * tb⁻¹ = (tb * tb) * x * (tb * tb)⁻¹ := by group
        _ = x := by rw [htb]; group
  let α : (A ⊔ B : Subgroup (H ⧸ N)) ≃* (A ⊔ B : Subgroup (H ⧸ N)) :=
    ((MulAut.conj tb).subgroupMap (A ⊔ B)).trans (MulEquiv.subgroupCongr hconjAB)
  have hαapp : ∀ k : (A ⊔ B : Subgroup (H ⧸ N)), ((α k : _) : H ⧸ N) = tb * k * tb⁻¹ :=
    fun _ => rfl
  have hα : ∀ k, α (α k) = k := by
    intro k
    apply Subtype.ext
    rw [hαapp, hαapp]
    calc tb * (tb * (k : H ⧸ N) * tb⁻¹) * tb⁻¹ = (tb * tb) * k * (tb * tb)⁻¹ := by group
      _ = k := by rw [htb]; group
  have hαA : (A.subgroupOf (A ⊔ B)).map α.toMonoidHom = B.subgroupOf (A ⊔ B) := by
    ext k
    constructor
    · rintro ⟨k', hk', rfl⟩
      change ((α k' : _) : H ⧸ N) ∈ B
      rw [hαapp, hAB_conj]
      have h1 : tb * (tb * (k' : H ⧸ N) * tb⁻¹) * tb⁻¹ = k' := by
        calc tb * (tb * (k' : H ⧸ N) * tb⁻¹) * tb⁻¹ = (tb * tb) * k' * (tb * tb)⁻¹ := by group
          _ = k' := by rw [htb]; group
      rw [h1]
      exact hk'
    · intro hk
      have hkB : (k : H ⧸ N) ∈ B := hk
      have hk' : tb * (k : H ⧸ N) * tb⁻¹ ∈ A := (hAB_conj _).mp hkB
      refine ⟨⟨_, mem_sup_left hk'⟩, hk', Subtype.ext ?_⟩
      change tb * (tb * (k : H ⧸ N) * tb⁻¹) * tb⁻¹ = k
      calc tb * (tb * (k : H ⧸ N) * tb⁻¹) * tb⁻¹ = (tb * tb) * k * (tb * tb)⁻¹ := by group
        _ = k := by rw [htb]; group
  set Cbar : Subgroup (A ⊔ B : Subgroup (H ⧸ N)) :=
    (centralizer ({tb} : Set (H ⧸ N))).subgroupOf (A ⊔ B) with hCbardef
  have hCbar : ∀ k, k ∈ Cbar ↔ α k = k := by
    intro k
    rw [hCbardef, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply Subtype.ext
      rw [hαapp, ← h, mul_inv_cancel_right]
    · intro h
      have h1 := congrArg Subtype.val h
      rw [hαapp] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  obtain ⟨-, -, -, δ, -, -, hΔq, -, -, hΔcore, -, hlayer, -, hle, -, -⟩ :=
    swapped_central_product_fixed_layer A B hABc hAq hAcore α hα hαA Cbar hCbar
  have hPLiso : pLayer Cbar 2 ≃* δ.range :=
    ((pLayer Cbar 2).equivMapOfInjective Cbar.subtype Cbar.subtype_injective).trans
      (MulEquiv.subgroupCongr hlayer)
  have hPLcore : pPrimeCore 2 (pLayer Cbar 2) = ⊥ := by
    have h := pPrimeCore_map_iso 2 hPLiso
    rw [hΔcore] at h
    exact Subgroup.map_injective hPLiso.injective (h.trans (Subgroup.map_bot _).symm)
  have hPLq : IsQuasisimple (pLayer Cbar 2) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv hPLiso.symm hΔq
  have hPLchar := CatalogueBPrimeJoin.pLayer_characteristic (G := Cbar) (p := 2)
  have hPLcomp : IsPComponent 2 (pLayer Cbar 2) := by
    rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 (pLayer Cbar 2)]
    refine ⟨(inferInstance : (pLayer Cbar 2).Normal).isSubnormal,
      CatalogueBPrimeJoin.primeResidual_eq_top_of_corefree_quasisimple 2 hPLq hPLcore, ?_⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hPLcore).symm)
      hPLq
  have hKmap : K.map (QuotientGroup.mk' N) = A ⊔ B := by
    rw [← hK, Subgroup.map_sup]
  have hπK : ∀ c : CK, (QuotientGroup.mk' N) (c : H) ∈ A ⊔ B := fun c =>
    hKmap ▸ mem_map_of_mem _ (hCKK c.2)
  let f₀ : CK →* (A ⊔ B : Subgroup (H ⧸ N)) :=
    ((QuotientGroup.mk' N).comp CK.subtype).codRestrict (A ⊔ B) hπK
  have hf₀ : ∀ c, f₀ c ∈ Cbar := by
    intro c
    rw [hCbardef, mem_subgroupOf, mem_centralizer_singleton_iff]
    change ((c : H) : H ⧸ N) * (t : H ⧸ N) = (t : H ⧸ N) * ((c : H) : H ⧸ N)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hCKt c c.2]
  let f : CK →* Cbar := f₀.codRestrict Cbar hf₀
  have hfapp : ∀ c : CK, (((f c : Cbar) : (A ⊔ B : Subgroup (H ⧸ N))) : H ⧸ N) =
      ((c : H) : H ⧸ N) := fun _ => rfl
  have hfker : ¬ 2 ∣ Nat.card f.ker := by
    let ι : f.ker →* N :=
      { toFun := fun x => ⟨((x : CK) : H), by
          have h1 := congrArg (fun y : Cbar => ((y : (A ⊔ B : Subgroup (H ⧸ N))) : H ⧸ N))
            (MonoidHom.mem_ker.mp x.2)
          simp only [hfapp] at h1
          exact (QuotientGroup.eq_one_iff _).mp h1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : H)) h))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (hNcop.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι))
  have hzp : ∀ c ∈ zpowers t, c = 1 ∨ c = t := fun c hc => eq_one_or_eq_of_mem_zpowers htt hc
  have htN : zpowers t ≤ normalizer (K : Set H) := by
    rw [zpowers_le, mem_normalizer_iff]
    exact htK
  let αK : zpowers t →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion htN)
  have hαK : ∀ (a : zpowers t) (k : K), ((αK a k : K) : H) = (a : H) * k * (a : H)⁻¹ :=
    fun a k => Subgroup.normalizerMonoidHom_apply_apply_coe K _ k
  have hNKn : (N.subgroupOf K).Normal := (pPrimeCore_normal (p := 2) (G := H)).subgroupOf K
  have hNKinv : ∀ a : zpowers t, ∀ n ∈ N.subgroupOf K, αK a n ∈ N.subgroupOf K := by
    intro a n hn
    change ((αK a n : K) : H) ∈ N
    rw [hαK]
    exact (pPrimeCore_normal (p := 2) (G := H)).conj_mem _ hn _
  have hNKodd : ¬ 2 ∣ Nat.card (N.subgroupOf K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (hNcop.coprime_dvd_right (Subgroup.card_comap_dvd_of_injective N K.subtype
        K.subtype_injective))
  have hzp2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hzp2 αK
    (N.subgroupOf K) hNKinv hNKodd
  have hfsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyAB⟩, hyC⟩
    have hy' : y ∈ K.map (QuotientGroup.mk' N) := by rw [hKmap]; exact hyAB
    obtain ⟨k, hkK, hky⟩ := mem_map.mp hy'
    have hyt : y * tb = tb * y := mem_centralizer_singleton_iff.mp hyC
    have hfixq : ((⟨k, hkK⟩ : K) : K ⧸ N.subgroupOf K) ∈ {q : K ⧸ N.subgroupOf K | ∀ a,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction αK (N.subgroupOf K)
          hNKinv a q = q} := by
      intro a
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, QuotientGroup.eq]
      rcases hzp a a.2 with ha | ha
      · have ha1 : a = 1 := Subtype.ext ha
        rw [ha1, map_one, MulAut.one_apply, inv_mul_cancel]
        exact one_mem _
      · change (((αK a ⟨k, hkK⟩)⁻¹ * ⟨k, hkK⟩ : K) : H) ∈ N
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hαK, ha, ← QuotientGroup.eq_one_iff,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπconj]
        have hk' : ((k : H) : H ⧸ N) = y := hky
        rw [hk', ← hyt]
        group
    rw [hlift] at hfixq
    obtain ⟨c, hcfix, hcq⟩ := hfixq
    have hct : (c : H) * t = t * c := by
      have h1 := congrArg Subtype.val (hcfix ⟨t, mem_zpowers t⟩)
      rw [hαK] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hcCK : (c : H) ∈ CK := by
      rw [← hCK]
      exact ⟨c.2, mem_centralizer_singleton_iff.mpr hct⟩
    refine ⟨⟨c, hcCK⟩, ?_⟩
    have h2 : (c : K)⁻¹ * ⟨k, hkK⟩ ∈ N.subgroupOf K := QuotientGroup.eq.mp hcq
    have h3 : ((c : H) : H ⧸ N) = (k : H ⧸ N) := QuotientGroup.eq.mpr h2
    have hk' : ((k : H) : H ⧸ N) = y := hky
    apply Subtype.ext
    apply Subtype.ext
    rw [hfapp]
    change ((c : H) : H ⧸ N) = y
    rw [h3, hk']
  obtain ⟨hbij, -, hiso⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hfsurj hfker
  obtain ⟨U, hU, -⟩ := hbij.surjOn hPLcomp
  refine ⟨U.map CK.subtype, ?_, ?_⟩
  · exact (map_subtype_le U)
  · have : (U.map CK.subtype).subgroupOf CK = U :=
      Subgroup.comap_map_eq_self_of_injective CK.subtype_injective U
    rw [this]
    exact hU

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS

theorem pLayerOf_eq_map' {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    pLayerOf p H = (pLayer ↥H p).map H.subtype := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    obtain ⟨hLH, hL2⟩ := hL
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH]
    exact Subgroup.map_mono (le_sSup hL2)
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨?_, ?_⟩
    · rintro _ ⟨m, -, rfl⟩
      exact m.2
    · have : (M.map H.subtype).subgroupOf H = M :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective M
      rw [this]
      exact hM

theorem mem_normalizer_sup' {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem isSubnormal_subgroupOf_of_normal_chain' {G : Type*} [Group G] {D M X : Subgroup G}
    (hDM : D ≤ M) (hMX : M ≤ X) (hD : (D.subgroupOf M).Normal) (hM : (M.subgroupOf X).Normal) :
    (D.subgroupOf X).IsSubnormal := by
  have hDX : D.subgroupOf X ≤ M.subgroupOf X := fun x hx => hDM hx
  refine Subgroup.IsSubnormal.trans hDX ?_ hM.isSubnormal
  let e := Subgroup.subgroupOfEquivOfLe hMX
  have heq : (D.subgroupOf X).subgroupOf (M.subgroupOf X) =
      (D.subgroupOf M).comap e.toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact (hD.comap e.toMonoidHom).isSubnormal

theorem isSubnormal_inf_centralizer' {G : Type*} [Group G] {K Z Y : Subgroup G} (hZK : Z ≤ K)
    (hKY : K ≤ Y) (hZ : (Z.subgroupOf K).Normal) (hK : (K.subgroupOf Y).Normal) (c : Set G) :
    ((Z ⊓ Subgroup.centralizer c).subgroupOf (Y ⊓ Subgroup.centralizer c)).IsSubnormal := by
  have hMX : K ⊓ Subgroup.centralizer c ≤ Y ⊓ Subgroup.centralizer c :=
    inf_le_inf_right _ hKY
  refine isSubnormal_subgroupOf_of_normal_chain' (inf_le_inf_right _ hZK) hMX ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right _ hZK)]
    intro d m hd hm
    obtain ⟨hdZ, hdc⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hmK, hmc⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hZK).mp hZ d m hdZ hmK,
        mul_mem (mul_mem hmc hdc) (inv_mem hmc)⟩
  · rw [Subgroup.normal_subgroupOf_iff hMX]
    intro m x hm hx
    obtain ⟨hmK, hmc⟩ := Subgroup.mem_inf.mp hm
    obtain ⟨hxY, hxc⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hKY).mp hK m x hmK hxY,
        mul_mem (mul_mem hxc hmc) (inv_mem hxc)⟩

theorem exists_diag_pcomp {G : Type} [Group G] [Finite G] {a b : G} (ha : orderOf a = 2)
    (hab : a * b = b * a) {M : Subgroup G} (hMHb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G)))) (hne : M ≠ conjugate M a) :
    ∃ T : Subgroup G, T ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G) ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Hb := centralizer ({b} : Set G) with hHb
  have haHb : a ∈ Hb := mem_centralizer_singleton_iff.mpr hab
  have ha' : orderOf (⟨a, haHb⟩ : Hb) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena := centralizer_mk_eq_subgroupOf haHb
  obtain ⟨hMaHb, -⟩ := conjugate_isPComponent_centralizer hab hMHb hM
  have hKHb : M ⊔ conjugate M a ≤ Hb := sup_le hMHb hMaHb
  have hconj : conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ = (conjugate M a).subgroupOf Hb :=
    conjugate_subgroupOf_eq M Hb ⟨a, haHb⟩
  have hne' : M.subgroupOf Hb ≠ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ := by
    rw [hconj]
    intro h
    exact hne (eq_of_subgroupOf_eq hMHb hMaHb h)
  have hK'eq : M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩ =
      (M ⊔ conjugate M a).subgroupOf Hb := by
    rw [hconj, subgroupOf_sup hMHb hMaHb]
  have hCeq : (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨a, haHb⟩) ⊓
      centralizer ({(⟨a, haHb⟩ : Hb)} : Set Hb) = ((M ⊔ conjugate M a) ⊓ Ca).subgroupOf Hb := by
    rw [hK'eq, hcena]
    ext y
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, y.2⟩⟩
  obtain ⟨T', hT'C, hT'⟩ := swap_case_exists ha' (M.subgroupOf Hb) hM hne'
  rw [hCeq] at hT'C hT'
  refine ⟨T'.map Hb.subtype, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact mem_subgroupOf.mp (hT'C hz)
  · have h1 : (T'.map Hb.subtype).subgroupOf Hb = T' :=
      Subgroup.comap_map_eq_self_of_injective Hb.subtype_injective T'
    rw [← h1] at hT'
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (inf_le_left.trans hKHb) 2
      Nat.prime_two).mp hT'

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS

section

variable {G : Type} [Group G] [Finite G]

theorem sup_conjugate_le_pLayerOf {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) :
    L ⊔ conjugate L y ≤ pLayerOf 2 (centralizer ({x} : Set G)) ∧
      pLayerOf 2 (centralizer ({x} : Set G)) ≤ normalizer ((L ⊔ conjugate L y : Subgroup G) : Set G) :=
  have hL' := isIntrinsic_conjugate hxy hL
  ⟨sup_le (le_sSup hL.1) (le_sSup hL'.1), fun _ hg =>
    mem_normalizer_sup' (pLayerOf_le_normalizer hL.1 hg) (pLayerOf_le_normalizer hL'.1 hg)⟩

theorem isSubnormal_fixed_sup {x y : G} (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) :
    (((L ⊔ conjugate L y) ⊓ centralizer ({y} : Set G)).subgroupOf
      (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G))).IsSubnormal := by
  obtain ⟨hKE, hEN⟩ := sup_conjugate_le_pLayerOf hxy hL
  have hEC : pLayerOf 2 (centralizer ({x} : Set G)) ≤ centralizer ({x} : Set G) :=
    TwoThin.pLayerOf_le 2 _
  have hZ : ((L ⊔ conjugate L y).subgroupOf (pLayerOf 2 (centralizer ({x} : Set G)))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hEN g.2) n).mp hn
    simpa using this
  have hK : ((pLayerOf 2 (centralizer ({x} : Set G))).subgroupOf (centralizer ({x} : Set G))).Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (mem_normalizer_pLayerOf g.2) n).mp hn
    simpa using this
  exact isSubnormal_inf_centralizer' hKE hEC hZ hK {y}

theorem IG_i {x y : G} (hy : orderOf y = 2) (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G)) :
    IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)) (IDiag y L) := by
  have hab : y * x = x * y := hxy.symm
  have hMHb : L ≤ centralizer ({x} : Set G) := hL.1.1
  have hM : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set G))) := hL.1.2
  have hne : L ≠ conjugate L y := (conjugate_ne_of_not_mem_normalizer hyL).symm
  obtain ⟨T, hTK, hTpc⟩ := exists_diag_pcomp hy hab hMHb hM hne
  have hcomp := orbit_fixed_component_comparison hy hab hMHb hM hTK hTpc
  have hfix : gsFixedLayer (L ⊔ conjugate L y) y = T := hcomp.2.1 hne
  have hI : IDiag y L = T := by
    rw [← hfix]
    unfold IDiag gsFixedLayer
    rw [inf_comm (centralizer ({y} : Set G)), pLayerOf_eq_map']
  rw [hI]
  obtain ⟨hMaHb, -⟩ := conjugate_isPComponent_centralizer hab hMHb hM
  have hKC : L ⊔ conjugate L y ≤ centralizer ({x} : Set G) := sup_le hMHb hMaHb
  have hDW : (L ⊔ conjugate L y) ⊓ centralizer ({y} : Set G) ≤
      centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := inf_le_inf_right _ hKC
  have hD2 : TwoComponents.IsTwoComponent
      (T.subgroupOf ((L ⊔ conjugate L y) ⊓ centralizer ({y} : Set G))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hTpc
  refine ⟨hTK.trans hDW, ?_⟩
  exact (CatalogueBAlternating.pComponent_two_iff _).mpr
    (TwoComponentTransport.extend_nested T _ _ hTK hDW (isSubnormal_fixed_sup hxy hL) hD2)

end

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS CFSG.LocalAnalysis.ComponentInitial

theorem map_conjugate' {H G' : Type*} [Group H] [Group G'] (f : H →* G') (L : Subgroup H) (g : H) :
    (CFSG.conjugate L g).map f = CFSG.conjugate (L.map f) (f g) := by
  unfold CFSG.conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem commutator_sup_sup_eq_bot {H : Type*} [Group H] {A B C D : Subgroup H}
    (h1 : ⁅A, C⁆ = ⊥) (h2 : ⁅A, D⁆ = ⊥) (h3 : ⁅B, C⁆ = ⊥) (h4 : ⁅B, D⁆ = ⊥) :
    ⁅A ⊔ B, C ⊔ D⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1))
      (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2))
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3))
      (Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h4))

theorem iSup_map_conj_eq {G : Type} [Group G] [Finite G] {X Λ₀ : Subgroup G} (hΛ₀ : Λ₀ ≤ X) :
    (⨆ g ∈ pLayerOf 2 X, Λ₀.map (MulAut.conj g).toMonoidHom) =
      (TwoThin.pumpupY (Λ₀.subgroupOf X)).map X.subtype := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [TwoThin.pLayerOf_two_eq_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    rintro _ ⟨a, ha, rfl⟩
    have hz := TwoThin.le_pumpupY (Λ₀.subgroupOf X) hg' ⟨⟨a, hΛ₀ ha⟩, ha, rfl⟩
    exact ⟨_, hz, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine TwoThin.pumpupY_le_of_forall fun g' hg' => ?_
    rintro _ ⟨⟨a, ha⟩, ha', rfl⟩
    have hg'mem : (g' : G) ∈ pLayerOf 2 X := by
      rw [TwoThin.pLayerOf_two_eq_map]
      exact ⟨g', hg', rfl⟩
    exact le_iSup₂ (f := fun g _ => Λ₀.map (MulAut.conj g).toMonoidHom) (g' : G) hg'mem
      ⟨a, ha', rfl⟩

section

variable {G : Type} [Group G] [Finite G]

theorem IG_iii {x y : G} (hy : orderOf y = 2) (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G)) :
    (⨆ g ∈ pLayerOf 2 (centralizer ({x} : Set G)),
        (IDiag y L).map (MulAut.conj g).toMonoidHom) = L ⊔ conjugate L y := by
  obtain ⟨hKE, hEN⟩ := sup_conjugate_le_pLayerOf hxy hL
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    exact (Subgroup.map_mono (IDiag_le_sup y L)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEN hg)).le
  · have hI := IG_i hy hxy hL hyL
    have hL' := isIntrinsic_conjugate hxy hL
    set C := centralizer ({x} : Set G) with hC
    have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
    have hI' : IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({x} : Set G)) (IDiag y L) := by
      rw [inf_comm]; exact hI
    have hso : orderOf (⟨y, hyC⟩ : ↥C) = 2 := TwoThin.orderOf_mk_centralizer hyC hy
    have hΛC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hI').1 hyC
    have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hI' hyC
    obtain ⟨hΛE, hJsub, L₀, hL₀, hcases, hLJ, hLsJ, hiff⟩ :=
      TwoThin.pumpupY_structure hso hΛC hΛ2
    have hIC : IDiag y L ≤ C := hI.1.trans inf_le_left
    have hLC : L ≤ C := hL.1.1
    have hL'C : conjugate L y ≤ C := hL'.1.1
    set s : ↥C := ⟨y, hyC⟩ with hs
    set π := TwoThin.barMk ↥C with hπ
    have hinv : (π s)⁻¹ = π s := inv_eq_self_of_orderOf_eq_two (TwoThin.orderOf_barMk hso)
    have hLY2 : TwoComponents.IsTwoComponent (L.subgroupOf C) := (TwoThin.isPCompIn_two_iff.mp hL.1).2
    have hLY'2 : TwoComponents.IsTwoComponent ((conjugate L y).subgroupOf C) :=
      (TwoThin.isPCompIn_two_iff.mp hL'.1).2
    have hAb := TwoThin.isComponent_map_barMk hLY2
    have hBb := TwoThin.isComponent_map_barMk hLY'2
    have hconjLY : conjugate (L.subgroupOf C) s = (conjugate L y).subgroupOf C :=
      conjugate_subgroupOf_eq L C s
    set Ab : Subgroup (TwoThin.barQ ↥C) := (L.subgroupOf C).map π with hAbdef
    set Bb : Subgroup (TwoThin.barQ ↥C) := ((conjugate L y).subgroupOf C).map π with hBbdef
    set Ib : Subgroup (TwoThin.barQ ↥C) := ((IDiag y L).subgroupOf C).map π with hIbdef
    have hB : Bb = conjSub (π s)⁻¹ Ab := by
      rw [hBbdef, ← hconjLY, map_conjugate']
      rfl
    have hperf : ⁅(IDiag y L).subgroupOf C, (IDiag y L).subgroupOf C⁆ = (IDiag y L).subgroupOf C :=
      TwoThin.commutator_self_of_isTwoComponent hΛC hΛ2
    have hne : (IDiag y L).subgroupOf C ≠ ⊥ := TwoThin.ne_bot_of_isTwoComponent hΛ2
    have hIne : Ib ≠ ⊥ := TwoThin.map_barMk_ne_bot_of_perfect hperf hne
    have hIperf : ⁅Ib, Ib⁆ = Ib := by
      rw [hIbdef, ← Subgroup.map_commutator, hperf]
    have hIT : Ib ≤ L₀ ⊔ conjSub (π s)⁻¹ L₀ := by
      rcases hcases with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
      · exact hAL.trans le_sup_left
      · refine hAD.trans ?_
        rintro _ ⟨x, rfl⟩
        exact swapDiag_mem_sup hAB x
    have hIAB : Ib ≤ Ab ⊔ Bb := by
      rw [hAbdef, hBbdef, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLC hL'C]
      exact Subgroup.map_mono (fun z hz => IDiag_le_sup y L hz)
    have hL₀AB : L₀ = Ab ∨ L₀ = Bb := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hL₀s : CFSG.IsComponent (conjSub (π s)⁻¹ L₀) := isComponent_conjSub hL₀ _
      have c1 := (CFSG.LocalCores.distinct_components_commute hL₀ hAb).resolve_left h1
      have c2 := (CFSG.LocalCores.distinct_components_commute hL₀ hBb).resolve_left h2
      have h3 : conjSub (π s)⁻¹ L₀ ≠ Ab := fun h =>
        h2 (by rw [hB, ← h, conjSub_conjSub_of_inv_eq hinv])
      have h4 : conjSub (π s)⁻¹ L₀ ≠ Bb := fun h => h1 (by
        have e1 : L₀ = conjSub (π s)⁻¹ (conjSub (π s)⁻¹ L₀) :=
          (conjSub_conjSub_of_inv_eq hinv L₀).symm
        rw [e1, h, hB, conjSub_conjSub_of_inv_eq hinv])
      have c3 := (CFSG.LocalCores.distinct_components_commute hL₀s hAb).resolve_left h3
      have c4 := (CFSG.LocalCores.distinct_components_commute hL₀s hBb).resolve_left h4
      have hcomm : ⁅L₀ ⊔ conjSub (π s)⁻¹ L₀, Ab ⊔ Bb⁆ = ⊥ := commutator_sup_sup_eq_bot c1 c2 c3 c4
      refine hIne (eq_bot_iff.mpr ?_)
      calc Ib = ⁅Ib, Ib⁆ := hIperf.symm
        _ ≤ ⁅L₀ ⊔ conjSub (π s)⁻¹ L₀, Ab ⊔ Bb⁆ := Subgroup.commutator_mono hIT hIAB
        _ = ⊥ := hcomm
    have hpair : ∀ M : Subgroup (TwoThin.barQ ↥C), (M = Ab ∨ M = Bb) →
        (M = L₀ ∨ M = conjSub (π s)⁻¹ L₀) := by
      intro M hM
      rcases hL₀AB with h | h
      · rcases hM with rfl | rfl
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, hB])
      · rcases hM with rfl | rfl
        · exact Or.inr (by rw [h, hB, conjSub_conjSub_of_inv_eq hinv])
        · exact Or.inl h.symm
    have hLle : ∀ K : Subgroup G, K ≤ C → TwoComponents.IsTwoComponent (K.subgroupOf C) →
        ((K.subgroupOf C).map π = Ab ∨ (K.subgroupOf C).map π = Bb) →
        K ≤ ⨆ g ∈ pLayerOf 2 C, (IDiag y L).map (MulAut.conj g).toMonoidHom := by
      intro K hKC hK2 hKimg
      rw [iSup_map_conj_eq hIC]
      have h1 : K.subgroupOf C ≤ TwoThin.pumpupY ((IDiag y L).subgroupOf C) :=
        (hiff _ hK2).mpr (hpair _ hKimg)
      calc K = (K.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hKC).symm
        _ ≤ _ := Subgroup.map_mono h1
    exact sup_le (hLle L hLC hLY2 (Or.inl rfl)) (hLle _ hL'C hLY'2 (Or.inr rfl))

end

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS CFSG.LocalAnalysis.ComponentInitial

section

variable {G : Type} [Group G] [Finite G]

theorem IG_bar {x y : G} (hy : orderOf y = 2) (hxy : x * y = y * x) {L : Subgroup G}
    (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G))
    (hyC : y ∈ centralizer ({x} : Set G)) :
    ∃ hAB : ⁅(L.subgroupOf (centralizer ({x} : Set G))).map (TwoThin.barMk ↥(centralizer ({x} : Set G))),
        conjSub (TwoThin.barMk ↥(centralizer ({x} : Set G)) ⟨y, hyC⟩)⁻¹
          ((L.subgroupOf (centralizer ({x} : Set G))).map
            (TwoThin.barMk ↥(centralizer ({x} : Set G))))⁆ = ⊥,
      ((IDiag y L).subgroupOf (centralizer ({x} : Set G))).map
          (TwoThin.barMk ↥(centralizer ({x} : Set G))) = (swapDiag hAB).range := by
  have hI := IG_i hy hxy hL hyL
  have hL' := isIntrinsic_conjugate hxy hL
  set C := centralizer ({x} : Set G) with hC
  have hI' : IsPCompIn 2 (centralizer ({y} : Set G) ⊓ centralizer ({x} : Set G)) (IDiag y L) := by
    rw [inf_comm]; exact hI
  have hso : orderOf (⟨y, hyC⟩ : ↥C) = 2 := TwoThin.orderOf_mk_centralizer hyC hy
  have hΛC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hI').1 hyC
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hI' hyC
  have hLC : L ≤ C := hL.1.1
  have hL'C : conjugate L y ≤ C := hL'.1.1
  set s : ↥C := ⟨y, hyC⟩ with hs
  set π := TwoThin.barMk ↥C with hπ
  have hinv : (π s)⁻¹ = π s := inv_eq_self_of_orderOf_eq_two (TwoThin.orderOf_barMk hso)
  have hLY2 : TwoComponents.IsTwoComponent (L.subgroupOf C) := (TwoThin.isPCompIn_two_iff.mp hL.1).2
  have hLY'2 : TwoComponents.IsTwoComponent ((conjugate L y).subgroupOf C) :=
    (TwoThin.isPCompIn_two_iff.mp hL'.1).2
  have hAb := TwoThin.isComponent_map_barMk hLY2
  have hBb := TwoThin.isComponent_map_barMk hLY'2
  have hconjLY : conjugate (L.subgroupOf C) s = (conjugate L y).subgroupOf C :=
    conjugate_subgroupOf_eq L C s
  set Ab : Subgroup (TwoThin.barQ ↥C) := (L.subgroupOf C).map π with hAbdef
  set Bb : Subgroup (TwoThin.barQ ↥C) := ((conjugate L y).subgroupOf C).map π with hBbdef
  set Ib : Subgroup (TwoThin.barQ ↥C) := ((IDiag y L).subgroupOf C).map π with hIbdef
  have hB : Bb = conjSub (π s)⁻¹ Ab := by
    rw [hBbdef, ← hconjLY, map_conjugate']
    rfl
  have hAneB : Ab ≠ Bb := by
    intro h
    have h3 := OddKernelTwoComponents.lift_unique π TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk _ _ hLY2 hLY'2 h
    have h4 := Subgroup.subgroupOf_inj.mp h3
    rw [inf_eq_left.mpr hLC, inf_eq_left.mpr hL'C] at h4
    exact conjugate_ne_of_not_mem_normalizer hyL h4.symm
  have hne : conjSub (π s)⁻¹ Ab ≠ Ab := fun h => hAneB (by rw [hB, h])
  have hAB : ⁅Ab, conjSub (π s)⁻¹ Ab⁆ = ⊥ := commutator_conjSub_eq_bot hAb hne
  refine ⟨hAB, ?_⟩
  have hAq := assembly_isQuasisimple_of_isComponent hAb
  have hperf : ⁅(IDiag y L).subgroupOf C, (IDiag y L).subgroupOf C⁆ = (IDiag y L).subgroupOf C :=
    TwoThin.commutator_self_of_isTwoComponent hΛC hΛ2
  have hne0 : (IDiag y L).subgroupOf C ≠ ⊥ := TwoThin.ne_bot_of_isTwoComponent hΛ2
  have hIne : Ib ≠ ⊥ := TwoThin.map_barMk_ne_bot_of_perfect hperf hne0
  have hIperf : ⁅Ib, Ib⁆ = Ib := by
    rw [hIbdef, ← Subgroup.map_commutator, hperf]
  have hIAB : Ib ≤ Ab ⊔ Bb := by
    rw [hAbdef, hBbdef, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLC hL'C]
    exact Subgroup.map_mono (fun z hz => IDiag_le_sup y L hz)
  have hIZ : Ib ≤ centralizer ({π s} : Set (TwoThin.barQ ↥C)) :=
    (Subgroup.map_mono hΛC).trans (TwoThin.map_centralizer_barMk hso).le
  have hIΔ : Ib ≤ (swapDiag hAB).range := by
    calc Ib = ⁅Ib, Ib⁆ := hIperf.symm
      _ ≤ ⁅(Ab ⊔ conjSub (π s)⁻¹ Ab) ⊓ centralizer ({π s} : Set (TwoThin.barQ ↥C)),
            (Ab ⊔ conjSub (π s)⁻¹ Ab) ⊓ centralizer ({π s} : Set (TwoThin.barQ ↥C))⁆ := by
          refine Subgroup.commutator_mono ?_ ?_ <;>
            exact le_inf (hB ▸ hIAB) hIZ
      _ = (swapDiag hAB).range := commutator_fixed_eq_range_swapDiag hAB hinv hAq
  have hΔZ : (swapDiag hAB).range ≤ centralizer ({π s} : Set (TwoThin.barQ ↥C)) := by
    rintro _ ⟨a, rfl⟩
    exact swapDiag_mem_centralizer hAB hinv a
  have hIcomp := TwoThin.isTwoComponent_map_barMk hso hΛC hΛ2
  have hIsub : (Ib.subgroupOf (centralizer ({π s} : Set (TwoThin.barQ ↥C)))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hIcomp.1 Subgroup.IsSubnormal.top
  have hIΔsub : (Ib.subgroupOf (swapDiag hAB).range).IsSubnormal :=
    TwoThin.isSubnormal_inf_subgroupOf hIsub hΔZ
  have hΔq : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1 (isQuasisimple_range_swapDiag hAB hAq)
  have hΔcomp : CFSG.IsComponent (⊤ : Subgroup ↥(swapDiag hAB).range) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hΔq,
      Subgroup.IsSubnormal.top⟩
  refine le_antisymm hIΔ ?_
  rcases CFSG.LocalCores.component_subnormal_subgroup hΔcomp hIΔsub with h | h
  · intro d hd
    have := h (Subgroup.mem_top (⟨d, hd⟩ : ↥(swapDiag hAB).range))
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    apply hIne
    rw [eq_bot_iff, ← hIperf, Subgroup.commutator_le]
    intro a ha b hb
    have h1 := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨a, hIΔ ha⟩ : ↥(swapDiag hAB).range))
      (Subgroup.mem_subgroupOf.mpr hb : (⟨b, hIΔ hb⟩ : ↥(swapDiag hAB).range) ∈
        Ib.subgroupOf (swapDiag hAB).range)
    rw [h, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    simpa [commutatorElement_def] using h2

end

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def IGLeafIV : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.GH74.GLS.IsKProperSimple G → ∀ (x y : G),
    orderOf x = 2 → orderOf y = 2 → Commute x y → ∀ L : Subgroup G, IsIntrinsic x L →
      y ∉ Subgroup.normalizer (L : Set G) →
      ∀ T : Subgroup G, CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In T (L ⊔ conjugate L y) →
        y ∈ Subgroup.normalizer (T : Set G) →
        ∃ S₀ : Subgroup G, CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In S₀ (IDiag y L) ∧
          (S₀ : Set G) = (fun a : G => a * (y⁻¹ * a * y)) '' ((T ⊓ L : Subgroup G) : Set G)

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS CFSG.LocalAnalysis.ComponentInitial

theorem natCard_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center B) = Nat.card (Subgroup.center A) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective (f := (e : A →* B)) e.injective]

theorem card_center_range_eq_one {A G' : Type*} [Group A] [Group G'] [Finite A] [Finite G']
    (δ : A →* G')
    (e : Nonempty ((δ.range ⧸ Subgroup.center δ.range) ≃* (A ⧸ Subgroup.center A)))
    (hZ : Nat.card (Subgroup.center A) = 2) (a : A) (ha : a ∈ δ.ker) (ha1 : a ≠ 1) :
    Nat.card (Subgroup.center δ.range) = 1 := by
  obtain ⟨e⟩ := e
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center δ.range)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center A)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
  have h4 : Nat.card (A ⧸ δ.ker) = Nat.card δ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have h5 : Nat.card (δ.range ⧸ Subgroup.center δ.range) = Nat.card (A ⧸ Subgroup.center A) :=
    Nat.card_congr e.toEquiv
  have hk : 2 ≤ Nat.card δ.ker := by
    have : 1 < Nat.card δ.ker :=
      Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨⟨a, ha⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    omega
  have hq : 0 < Nat.card (A ⧸ Subgroup.center A) := Nat.card_pos
  have hzpos : 0 < Nat.card (Subgroup.center δ.range) := Nat.card_pos
  have hmain : Nat.card (A ⧸ Subgroup.center A) * 2 =
      Nat.card (A ⧸ Subgroup.center A) * (Nat.card (Subgroup.center δ.range) * Nat.card δ.ker) := by
    calc Nat.card (A ⧸ Subgroup.center A) * 2 = Nat.card A := by rw [h2, hZ]
      _ = Nat.card (A ⧸ δ.ker) * Nat.card δ.ker := h3
      _ = Nat.card δ.range * Nat.card δ.ker := by rw [h4]
      _ = (Nat.card (δ.range ⧸ Subgroup.center δ.range) * Nat.card (Subgroup.center δ.range)) *
            Nat.card δ.ker := by rw [← h1]
      _ = _ := by rw [h5]; ring
  have h6 := Nat.eq_of_mul_eq_mul_left hq hmain
  rcases Nat.lt_or_ge (Nat.card (Subgroup.center δ.range)) 2 with h | h
  · omega
  · nlinarith

theorem pRank_eq_of_surjective_of_odd_ker {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hodd : ¬ 2 ∣ Nat.card f.ker) :
    CFSG.pRank 2 B = CFSG.pRank 2 A :=
  (pRank_eq_of_mulEquiv' (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm.trans
    (CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two f.ker hodd)

theorem card_center_of_rank_one {J : Type*} [Group J] [Finite J] (hrank : CFSG.pRank 2 J ≤ 1)
    (hA : CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J)) :
    Nat.card (Subgroup.center (J ⧸ CFSG.oddCore J)) = 2 := by
  obtain ⟨-, z, hz, -, -, hZcard, -⟩ :=
    ComponentClassification.UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{_, 0}
      hrank hA
  exact hZcard

theorem isQuasisimple_oddCore_quotient {J : Type*} [Group J] [Finite J]
    (h : CFSG.IsQuasisimple (J ⧸ CFSG.pPrimeCore 2 J)) :
    CFSG.IsQuasisimple (J ⧸ CFSG.oddCore J) := by
  have hO : CFSG.oddCore J = CFSG.pPrimeCore 2 J :=
    (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hO).symm h

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UGSChain
  CFSG.ComponentClassification.UnbalancedGS CFSG.LocalAnalysis.ComponentInitial

section

variable {G : Type} [Group G] [Finite G]

theorem gw_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.GorensteinWalter.IsQuasisimple Q := by
  obtain ⟨hperf, hsimple, -⟩ := h
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  have hnt : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  exact ⟨hnt, Group.IsPerfect.commutator_eq_top, hsimple⟩

theorem IG_ii
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    {L : Subgroup G} (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G)) :
    2 ≤ pRank 2 ↥(IDiag y L) := by
  have hyC : y ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
  obtain ⟨hAB, hbar⟩ := IG_bar hy hxy hL hyL hyC
  have hI := IG_i hy hxy hL hyL
  have hL' := isIntrinsic_conjugate hxy hL
  set C := centralizer ({x} : Set G) with hC
  have hso : orderOf (⟨y, hyC⟩ : ↥C) = 2 := TwoThin.orderOf_mk_centralizer hyC hy
  have hLC : L ≤ C := hL.1.1
  have hIC : IDiag y L ≤ C := (hI.1).trans inf_le_left
  set s : ↥C := ⟨y, hyC⟩ with hs
  set π := TwoThin.barMk ↥C with hπ
  have hLY2 : TwoComponents.IsTwoComponent (L.subgroupOf C) := (TwoThin.isPCompIn_two_iff.mp hL.1).2
  have hAb := TwoThin.isComponent_map_barMk hLY2
  have hAq := assembly_isQuasisimple_of_isComponent hAb
  set Ab : Subgroup (TwoThin.barQ ↥C) := (L.subgroupOf C).map π with hAbdef
  set Ib : Subgroup (TwoThin.barQ ↥C) := ((IDiag y L).subgroupOf C).map π with hIbdef
  have hLsub : (L.subgroupOf C).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hLY2.1 Subgroup.IsSubnormal.top
  have hZAb : Nat.card (Subgroup.center ↥Ab) = 2 := by
    have hO : CFSG.oddCore ↥(L.subgroupOf C) = CFSG.pPrimeCore 2 ↥(L.subgroupOf C) :=
      (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
    have hrank : CFSG.pRank 2 ↥(L.subgroupOf C) ≤ 1 := by
      rw [pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hLC)]
      exact hL.2.1.le
    obtain ⟨e1⟩ := TwoThin.hat_equiv_subgroupOf hLC
    have hq : CFSG.IsQuasisimple (↥(L.subgroupOf C) ⧸ CFSG.pPrimeCore 2 ↥(L.subgroupOf C)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e1 (TwoThin.isQuasisimple_hat hL.1)
    have h2 := card_center_of_rank_one hrank (isQuasisimple_oddCore_quotient hq)
    obtain ⟨e2⟩ := TwoThin.hat_equiv_map hLsub
    have e3 : (↥(L.subgroupOf C) ⧸ CFSG.oddCore ↥(L.subgroupOf C)) ≃* ↥Ab :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans e2
    rw [natCard_center_congr e3]
    exact h2
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set X : ↥C := ⟨x, hxC⟩ with hX
  have hXcent : ∀ c : ↥C, X * c = c * X := fun c =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  have hX2 : X * X = 1 := Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hx)
  have hXL : X ∈ L.subgroupOf C := Subgroup.mem_subgroupOf.mpr hL.2.2
  have hXb : π X ∈ Ab := Subgroup.mem_map_of_mem π hXL
  have hXb2 : orderOf (π X) = 2 := TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer hxC hx)
  have hXs : π X * π s = π s * π X := by rw [← map_mul, ← map_mul, hXcent s]
  have hker : (⟨π X, hXb⟩ : ↥Ab) ∈ (swapDiag hAB).ker := by
    rw [MonoidHom.mem_ker, swapDiag_apply]
    have h1 : (π s)⁻¹ * π X * π s = π X := by
      calc (π s)⁻¹ * π X * π s = (π s)⁻¹ * (π X * π s) := by group
        _ = (π s)⁻¹ * (π s * π X) := by rw [hXs]
        _ = π X := inv_mul_cancel_left _ _
    show π X * ((π s)⁻¹ * π X * π s) = 1
    rw [h1, ← map_mul, hX2, map_one]
  have hne1 : (⟨π X, hXb⟩ : ↥Ab) ≠ 1 := fun h =>
    ne_one_of_orderOf_eq_two hXb2 (congrArg Subtype.val h)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcen⟩ :=
    swapped_quasisimple_fixed_central_product (t := π s) (TwoThin.orderOf_barMk hso) hAq hAB
  have hZΔ : Nat.card (Subgroup.center ↥(swapDiag hAB).range) = 1 :=
    card_center_range_eq_one (swapDiag hAB) hcen hZAb _ hker hne1
  have hrank : CFSG.pRank 2 ↥(swapDiag hAB).range = CFSG.pRank 2 ↥(IDiag y L) := by
    let f₀ : ↥(IDiag y L) →* TwoThin.barQ ↥C := π.comp (Subgroup.inclusion hIC)
    let f : ↥(IDiag y L) →* ↥f₀.range := f₀.rangeRestrict
    have hsurj : Function.Surjective f := MonoidHom.rangeRestrict_surjective f₀
    have hodd : ¬ 2 ∣ Nat.card f.ker := by
      have hker' : f.ker = f₀.ker := MonoidHom.ker_rangeRestrict f₀
      rw [hker']
      let incl : f₀.ker →* (TwoThin.barMk ↥C).ker :=
        { toFun := fun w => ⟨Subgroup.inclusion hIC w.1, w.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hinj : Function.Injective incl := by
        intro u v h
        have h1 := congrArg (fun z : (TwoThin.barMk ↥C).ker => (z : ↥C)) h
        apply Subtype.ext
        exact Subgroup.inclusion_injective hIC h1
      have hodd' : Odd (Nat.card f₀.ker) :=
        TwoThin.odd_card_ker_barMk.of_dvd_nat (Subgroup.card_dvd_of_injective incl hinj)
      exact fun h => (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h)
    have hrange : f₀.range = (swapDiag hAB).range := by
      rw [← hbar]
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨Subgroup.inclusion hIC i, i.2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨c, hc⟩, rfl⟩
    rw [← pRank_eq_of_surjective_of_odd_ker f hsurj hodd]
    exact pRank_eq_of_mulEquiv' (MulEquiv.subgroupCongr hrange).symm
  by_contra hlt
  push Not at hlt
  have hΔq : CFSG.IsQuasisimple ↥(swapDiag hAB).range :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).1 (isQuasisimple_range_swapDiag hAB hAq)
  have hcenter : CFSG.oddCore ↥(swapDiag hAB).range ≤ Subgroup.center ↥(swapDiag hAB).range := by
    have hO : CFSG.oddCore ↥(swapDiag hAB).range = CFSG.pPrimeCore 2 ↥(swapDiag hAB).range :=
      (CFSG.oddCore_eq_piCore _).trans (CFSG.pPrimeCore_eq_piCore _ 2).symm
    rw [hO]
    exact GorensteinWalter.pPrimeCore_le_center_of_isQuasisimple (gw_isQuasisimple hΔq)
  have hA2 : CFSG.IsQuasisimple (↥(swapDiag hAB).range ⧸ CFSG.oddCore ↥(swapDiag hAB).range) :=
    (CFSG.LocalCores.quasisimple_central_quotient hΔq (CFSG.oddCore ↥(swapDiag hAB).range)
      hcenter).1
  have hc2 := card_center_of_rank_one (by omega : CFSG.pRank 2 ↥(swapDiag hAB).range ≤ 1) hA2
  have hbot : CFSG.oddCore ↥(swapDiag hAB).range = ⊥ :=
    eq_bot_iff.mpr ((hcenter.trans (Subgroup.eq_bot_of_card_eq _ hZΔ).le))
  have e4 : (↥(swapDiag hAB).range ⧸ CFSG.oddCore ↥(swapDiag hAB).range) ≃*
      ↥(swapDiag hAB).range :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  rw [natCard_center_congr e4.symm, hZΔ] at hc2
  omega

end

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

open CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem IG_3_27_of_leafIV (h4 : IGLeafIV) : IG_3_27 := by
  intro G _ _ hG x y hx hy hxy L hL hyL
  exact ⟨IG_i hy hxy.eq hL hyL, IG_ii hx hy hxy.eq hL hyL, IG_iii hy hxy.eq hL hyL,
    h4 G hG x y hx hy hxy L hL hyL⟩

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B

end Ckpt6

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327F

theorem isSylow2In_map {H Q : Type*} [Group H] [Group Q] (φ : H →* Q) {T R : Subgroup H}
    (hR : IsSylow2In R T) : IsSylow2In (R.map φ) (T.map φ) := by
  obtain ⟨hRT, hRp, hRi⟩ := hR
  refine ⟨Subgroup.map_mono hRT, hRp.map φ, ?_⟩
  let ψ : ↥T →* ↥(T.map φ) :=
    (φ.comp T.subtype).codRestrict (T.map φ) (fun t => ⟨t, t.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have h1 : (R.map φ).subgroupOf (T.map φ) = (R.subgroupOf T).map ψ := by
    ext ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hRT hr⟩, hr, Subtype.ext rfl⟩
    · rintro ⟨⟨t, ht⟩, htR, hψt⟩
      exact ⟨t, htR, congrArg Subtype.val hψt⟩
  have h2 : (R.map φ).relIndex (T.map φ) = ((R.subgroupOf T).map ψ).index := by
    rw [Subgroup.relIndex, h1]
  rw [h2, Subgroup.index_map, MonoidHom.range_eq_top.mpr hψ, Subgroup.index_top, mul_one]
  intro hd
  exact hRi (hd.trans (Subgroup.index_dvd_of_le le_sup_left))

theorem isSylow2In_subgroupOf {G : Type*} [Group G] {C P Q : Subgroup G} (hPQ : IsSylow2In P Q)
    (hQC : Q ≤ C) : IsSylow2In (P.subgroupOf C) (Q.subgroupOf C) := by
  obtain ⟨hPQ', hPp, hPi⟩ := hPQ
  refine ⟨fun a ha => hPQ' ha, ?_, ?_⟩
  · exact hPp.of_equiv (Subgroup.subgroupOfEquivOfLe (hPQ'.trans hQC)).symm
  · rw [Subgroup.relIndex_subgroupOf hQC]
    exact hPi

theorem mem_of_two_power_of_odd {G : Type*} [Group G] {I : Subgroup G} {w n s : G} (hw : w ∈ I)
    (hn : n ∈ normalizer (I : Set G)) (hodd : Odd (orderOf n)) (hs : s = w * n) {k : ℕ}
    (hk : s ^ (2 ^ k) = 1) : s ∈ I := by
  have key : ∀ j : ℕ, ∃ w' ∈ I, s ^ j = w' * n ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨w', hw', hj⟩ := ih
      refine ⟨w * (n * w' * n⁻¹), mul_mem hw ((mem_normalizer_iff.mp hn w').mp hw'), ?_⟩
      rw [pow_succ' s j, hj, hs, pow_succ' n j]
      group
  obtain ⟨w', hw', h⟩ := key (2 ^ k)
  rw [hk] at h
  have hnk : n ^ (2 ^ k) = w'⁻¹ := by
    have : w' * n ^ (2 ^ k) = 1 := h.symm
    exact (eq_inv_of_mul_eq_one_right this)
  have hcop : Nat.Coprime (2 ^ k) (orderOf n) :=
    (Nat.coprime_two_left.mpr hodd).pow_left k
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hnI : n ∈ I := by
    rw [← hm, hnk]
    exact pow_mem (inv_mem hw') m
  rw [hs]
  exact mul_mem hw hnI

theorem exists_diag_subgroup {G : Type} [Group G] [Finite G] {x y : G} (hxy : x * y = y * x)
    (hy : y * y = 1) {L : Subgroup G} (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G))
    {T : Subgroup G} (hT : IsPGroup 2 ↥T) (hyT : y ∈ normalizer (T : Set G)) :
    ∃ S₀ : Subgroup G,
      (S₀ : Set G) = (fun a : G => a * (y⁻¹ * a * y)) '' ((T ⊓ L : Subgroup G) : Set G) ∧
      IsPGroup 2 ↥S₀ ∧ S₀ ≤ T ∧ S₀ ≤ centralizer ({y} : Set G) ∧ S₀ ≤ L ⊔ conjugate L y := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  let δ : ↥(T ⊓ L) →* G :=
    { toFun := fun a => (a : G) * (y⁻¹ * (a : G) * y)
      map_one' := by simp
      map_mul' := fun a b => by
        have h := comm_of_mem_sylow_inf hxy hL hyL hT hyT (a := (b : G)) (b := (a : G)) b.2 a.2
        simp only [Subgroup.coe_mul]
        calc (a : G) * b * (y⁻¹ * (a * b) * y)
            = a * (b * (y⁻¹ * a * y)) * (y⁻¹ * b * y) := by group
          _ = a * ((y⁻¹ * a * y) * b) * (y⁻¹ * b * y) := by rw [h]
          _ = (a : G) * (y⁻¹ * a * y) * ((b : G) * (y⁻¹ * b * y)) := by group }
  have hδ : ∀ a : ↥(T ⊓ L), δ a = (a : G) * (y⁻¹ * (a : G) * y) := fun a => rfl
  have hyT' : ∀ a ∈ T, y⁻¹ * a * y ∈ T := by
    intro a ha
    have := (mem_normalizer_iff.mp (inv_mem hyT) a).mp ha
    rwa [inv_inv] at this
  refine ⟨δ.range, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [MonoidHom.coe_range, Set.mem_range, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  · exact (hT.to_le (inf_le_left : T ⊓ L ≤ T)).of_surjective δ.rangeRestrict
      δ.rangeRestrict_surjective
  · rintro _ ⟨a, rfl⟩
    rw [hδ]
    exact mul_mem a.2.1 (hyT' _ a.2.1)
  · rintro _ ⟨a, rfl⟩
    rw [hδ, mem_centralizer_singleton_iff]
    have hcomm := comm_of_mem_sylow_inf hxy hL hyL hT hyT a.2 a.2
    rw [hyi] at hcomm ⊢
    calc (a : G) * (y * a * y) * y = a * y * a * (y * y) := by simp only [mul_assoc]
      _ = a * y * a := by rw [hy, mul_one]
      _ = (y * y) * a * y * a := by rw [hy, one_mul]
      _ = y * ((y * a * y) * a) := by simp only [mul_assoc]
      _ = y * (a * (y * a * y)) := by rw [hcomm]
  · rintro _ ⟨a, rfl⟩
    rw [hδ]
    refine mul_mem (mem_sup_left a.2.2) (mem_sup_right ?_)
    rw [mem_conjugate_iff', show y * (y⁻¹ * (a : G) * y) * y⁻¹ = a by group]
    exact a.2.2

section Main

variable {G : Type} [Group G] [Finite G]

theorem IG_iv_of_bar {x y : G} (hy : orderOf y = 2) (hxy : x * y = y * x)
    {L : Subgroup G} (hL : IsIntrinsic x L) (hyL : y ∉ normalizer (L : Set G))
    (hyC : y ∈ centralizer ({x} : Set G))
    (hbar : ∃ δ : ↥((L.subgroupOf (centralizer ({x} : Set G))).map
        (TwoThin.barMk ↥(centralizer ({x} : Set G)))) →*
          TwoThin.barQ ↥(centralizer ({x} : Set G)),
      (∀ ā, δ ā = (ā : TwoThin.barQ ↥(centralizer ({x} : Set G))) *
        ((TwoThin.barMk ↥(centralizer ({x} : Set G)) ⟨y, hyC⟩)⁻¹ *
          (ā : TwoThin.barQ ↥(centralizer ({x} : Set G))) *
          TwoThin.barMk ↥(centralizer ({x} : Set G)) ⟨y, hyC⟩)) ∧
      ((IDiag y L).subgroupOf (centralizer ({x} : Set G))).map
        (TwoThin.barMk ↥(centralizer ({x} : Set G))) = δ.range)
    {T : Subgroup G} (hT : IsSylow2In T (L ⊔ conjugate L y)) (hyT : y ∈ normalizer (T : Set G)) :
    ∃ S₀ : Subgroup G, IsSylow2In S₀ (IDiag y L) ∧
      (S₀ : Set G) = (fun a : G => a * (y⁻¹ * a * y)) '' ((T ⊓ L : Subgroup G) : Set G) := by
  classical
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set π := TwoThin.barMk ↥C with hπdef
  set s : ↥C := ⟨y, hyC⟩ with hsdef
  obtain ⟨δ, hδapp, hδI⟩ := hbar
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hL' : IsIntrinsic x (conjugate L y) := isIntrinsic_conjugate hxy hL
  have hLC : L ≤ C := hL.1.1
  have hL'C : conjugate L y ≤ C := hL'.1.1
  have hKC : L ⊔ conjugate L y ≤ C := sup_le hLC hL'C
  have hIK : IDiag y L ≤ L ⊔ conjugate L y := IDiag_le_sup y L
  have hIC : IDiag y L ≤ C := hIK.trans hKC
  obtain ⟨S₀, hS₀set, hS₀p, hS₀T, hS₀y, hS₀K⟩ :=
    exists_diag_subgroup hxy hy2 hL hyL hT.2.1 hyT
  have hAbmem : ∀ (a : G) (ha : a ∈ L), π ⟨a, hLC ha⟩ ∈ (L.subgroupOf C).map π :=
    fun a ha => ⟨⟨a, hLC ha⟩, ha, rfl⟩
  have hπδ : ∀ (a : G) (ha : a ∈ L) (hc : a * (y⁻¹ * a * y) ∈ C),
      π ⟨a * (y⁻¹ * a * y), hc⟩ = δ ⟨π ⟨a, hLC ha⟩, hAbmem a ha⟩ := by
    intro a ha hc
    rw [hδapp]
    show π ⟨_, hc⟩ = π ⟨a, _⟩ * ((π s)⁻¹ * π ⟨a, _⟩ * π s)
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext rfl)
  have hS₀I : S₀ ≤ IDiag y L := by
    intro z hz
    have hz' : z ∈ (fun a : G => a * (y⁻¹ * a * y)) '' ((T ⊓ L : Subgroup G) : Set G) := by
      rw [← hS₀set]
      exact hz
    obtain ⟨a, ha, rfl⟩ := hz'
    have haL : a ∈ L := (Subgroup.mem_inf.mp ha).2
    have hz₀C : a * (y⁻¹ * a * y) ∈ C := hKC (hS₀K hz)
    have hmem : π ⟨a * (y⁻¹ * a * y), hz₀C⟩ ∈ ((IDiag y L).subgroupOf C).map π := by
      rw [hδI, hπδ a haL hz₀C]
      exact ⟨_, rfl⟩
    obtain ⟨w, hwI, hwπ⟩ := Subgroup.mem_map.mp hmem
    have hwI' : (w : G) ∈ IDiag y L := Subgroup.mem_subgroupOf.mp hwI
    have hn : ((w : G)⁻¹ * (a * (y⁻¹ * a * y))) ∈ pPrimeCoreOf 2 C := by
      have h1 : (w⁻¹ * ⟨a * (y⁻¹ * a * y), hz₀C⟩ : ↥C) ∈ pPrimeCore 2 ↥C :=
        QuotientGroup.eq.mp hwπ
      exact ⟨_, h1, rfl⟩
    have hnodd : Odd (orderOf ((w : G)⁻¹ * (a * (y⁻¹ * a * y)))) := by
      have h1 : orderOf (⟨(w : G)⁻¹ * (a * (y⁻¹ * a * y)), hn⟩ : ↥(pPrimeCoreOf 2 C)) ∣
          Nat.card (pPrimeCoreOf 2 C) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact (TwoThin.card_pPrimeCoreOf_odd C).of_dvd_nat h1
    have hwX : (w : G) ∈ centralizer ({y} : Set G) ⊓ (L ⊔ conjugate L y) :=
      (TwoThin.pLayerOf_le 2 _) hwI'
    have hz₀X : a * (y⁻¹ * a * y) ∈ centralizer ({y} : Set G) ⊓ (L ⊔ conjugate L y) :=
      ⟨hS₀y hz, hS₀K hz⟩
    have hnX : ((w : G)⁻¹ * (a * (y⁻¹ * a * y))) ∈
        centralizer ({y} : Set G) ⊓ (L ⊔ conjugate L y) :=
      mul_mem (inv_mem hwX) hz₀X
    have hnN : ((w : G)⁻¹ * (a * (y⁻¹ * a * y))) ∈ normalizer (IDiag y L : Set G) :=
      mem_normalizer_pLayerOf hnX
    obtain ⟨k, hk⟩ := hS₀p ⟨_, hz⟩
    have hk' : (a * (y⁻¹ * a * y)) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact mem_of_two_power_of_odd hwI' hnN hnodd (mul_inv_cancel_left (w : G) _).symm hk'
  refine ⟨S₀, ?_, hS₀set⟩
  obtain ⟨R, hR, hS₀R⟩ := exists_isSylow2In_of_le hS₀p hS₀I
  have hP : IsSylow2In (T ⊓ L) L :=
    isSylow2In_inf_normal hT le_sup_left (sup_conjugate_le_normalizer hxy hL hyL)
  have hPC : IsSylow2In ((T ⊓ L).subgroupOf C) (L.subgroupOf C) :=
    isSylow2In_subgroupOf hP hLC
  have hPb := isSylow2In_map π hPC
  have hQ : IsSylow2In ((((T ⊓ L).subgroupOf C).map π).subgroupOf ((L.subgroupOf C).map π))
      (⊤ : Subgroup ↥((L.subgroupOf C).map π)) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hPb.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPb.1).symm
    · rw [Subgroup.relIndex_top_right]
      exact hPb.2.2
  have hQδ : IsSylow2In (((((T ⊓ L).subgroupOf C).map π).subgroupOf
      ((L.subgroupOf C).map π)).map δ) δ.range := by
    have := isSylow2In_map δ hQ
    rwa [← MonoidHom.range_eq_map] at this
  have hQeq : ((((T ⊓ L).subgroupOf C).map π).subgroupOf ((L.subgroupOf C).map π)).map δ =
      (S₀.subgroupOf C).map π := by
    ext z
    constructor
    · rintro ⟨ā, hāQ, rfl⟩
      obtain ⟨a', ha'mem, ha'π⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hāQ)
      have ha'TL : (a' : G) ∈ T ⊓ L := ha'mem
      have hz0 : (a' : G) * (y⁻¹ * (a' : G) * y) ∈ S₀ := by
        rw [← SetLike.mem_coe, hS₀set]
        exact ⟨a', ha'TL, rfl⟩
      refine ⟨⟨(a' : G) * (y⁻¹ * (a' : G) * y), hKC (hS₀K hz0)⟩, hz0, ?_⟩
      rw [hδapp, ← ha'π, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext rfl)
    · rintro ⟨c, hc, rfl⟩
      have hcS₀ : (c : G) ∈ S₀ := hc
      have h1 : (c : G) ∈ (fun a : G => a * (y⁻¹ * a * y)) '' ((T ⊓ L : Subgroup G) : Set G) := by
        rw [← hS₀set]
        exact hcS₀
      obtain ⟨a, haTL, hac⟩ := h1
      have haL : a ∈ L := (Subgroup.mem_inf.mp haTL).2
      have haC : a ∈ C := hLC haL
      have hc' : a * (y⁻¹ * a * y) ∈ C := by
        rw [show a * (y⁻¹ * a * y) = (c : G) from hac]
        exact c.2
      refine ⟨⟨π ⟨a, haC⟩, hAbmem a haL⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr ⟨⟨a, haC⟩, haTL, rfl⟩
      · rw [← hπδ a haL hc']
        exact congrArg π (Subtype.ext hac)
  rw [hQeq] at hQδ
  have hRC : IsSylow2In (R.subgroupOf C) ((IDiag y L).subgroupOf C) :=
    isSylow2In_subgroupOf hR hIC
  have hRb := isSylow2In_map π hRC
  rw [hδI] at hRb
  have hcard := Sec12.sylow2_card_eq hQδ hRb
  have hle : (S₀.subgroupOf C).map π ≤ (R.subgroupOf C).map π :=
    Subgroup.map_mono (fun c hc => hS₀R hc)
  have heq : (S₀.subgroupOf C).map π = (R.subgroupOf C).map π :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hRS₀ : R ≤ S₀ := by
    intro r hr
    have hrC : r ∈ C := hIC (hR.1 hr)
    have hmem : π ⟨r, hrC⟩ ∈ (R.subgroupOf C).map π := ⟨⟨r, hrC⟩, hr, rfl⟩
    rw [← heq] at hmem
    obtain ⟨c, hc, hcπ⟩ := Subgroup.mem_map.mp hmem
    have hcR : (c : G) ∈ R := hS₀R (Subgroup.mem_subgroupOf.mp hc)
    have hcr : (c : G) = r :=
      eq_of_hatMk_eq (K := C) (S := R) (hR.1.trans hIC) hR.2.1 hcR hr hcπ
    rw [← hcr]
    exact Subgroup.mem_subgroupOf.mp hc
  exact (le_antisymm hRS₀ hS₀R) ▸ hR

end Main

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327F

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327F

open CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.LocalAnalysis.ComponentInitial

theorem IGLeafIV_proof : CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.IGLeafIV := by
  intro G _ _ hG x y hx hy hxy L hL hyL T hT hyT
  have hyC : y ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxy.eq.symm
  obtain ⟨hAB, hI⟩ := CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.IG_bar hy hxy.eq hL hyL hyC
  exact IG_iv_of_bar hy hxy.eq hL hyL hyC ⟨swapDiag hAB, fun ā => rfl, hI⟩ hT hyT

theorem IG_3_27_proof : IG_3_27 :=
  CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.IG_3_27_of_leafIV IGLeafIV_proof

end CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327F
