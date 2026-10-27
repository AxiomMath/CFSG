module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMirror
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolOrbit
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAOrbitFixedComponent
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolForward
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitWeakMaximal

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.UnbalancedGS

theorem swap_fusionZStar_equiv_and_oddCore {H : Type*} [Group H] [Finite H] {t : H}
    (ht : orderOf t = 2) (M : Subgroup H) (hM : IsPComponent 2 M)
    (hne : M ≠ conjugate M t) (T : Subgroup H)
    (hTC : T ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))
    (hT : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H)))) :
    Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* ↥M ⧸ Open.fusionZStar ↥M) ∧
      (pPrimeCore 2 T).map T.subtype ≤ pPrimeCore 2 H := by
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
  generalize hK : M ⊔ conjugate M t = K at hTC hT ⊢
  generalize hCK : K ⊓ centralizer ({t} : Set H) = CK at hTC hT ⊢
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
  obtain ⟨-, -, -, δ, -, -, hΔq, -, -, hΔcore, -, hlayer, -, -, -, -⟩ :=
    UnbalancedGS.swapped_central_product_fixed_layer A B hABc hAq hAcore α hα hαA Cbar hCbar
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
  have hzp : ∀ c ∈ zpowers t, c = 1 ∨ c = t := fun c hc =>
    UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers htt hc
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
  have hTbar : IsPComponent 2 ((T.subgroupOf CK).map f) := hbij.mapsTo hT
  have hTeq : (T.subgroupOf CK).map f = pLayer Cbar 2 :=
    CatalogueBPrimeJoin.eq_of_le 2 _ _ hTbar hPLcomp (le_sSup hTbar)
  obtain ⟨e₁, -⟩ := hiso (T.subgroupOf CK) hT
  let eT : T.subgroupOf CK ≃* T := subgroupOfEquivOfLe hTC
  let eL : ((T.subgroupOf CK).map f) ≃* pLayer Cbar 2 := MulEquiv.subgroupCongr hTeq
  let e₂ : (T.subgroupOf CK) ⧸ pPrimeCore 2 (T.subgroupOf CK) ≃*
      δ.range ⧸ pPrimeCore 2 δ.range :=
    e₁.trans ((QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)).trans
      (QuotientGroup.congr _ _ hPLiso (pPrimeCore_map_iso 2 hPLiso)))
  have : Group.IsPerfect A := hAq.1
  have hAq' : IsQuasisimple (A ⧸ pPrimeCore 2 A) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hAcore).symm) hAq
  have hΔne : pPrimeCore 2 δ.range ≠ ⊤ := by
    rw [hΔcore]
    intro hbt
    have h1 : ∀ x : δ.range, x = 1 := fun x => by
      have hx : x ∈ (⊤ : Subgroup δ.range) := mem_top x
      rw [← hbt, mem_bot] at hx
      exact hx
    obtain ⟨u, v, huv⟩ := hΔq.2.2
    apply huv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [h1 x, h1 y]
  obtain ⟨eA⟩ := GrSLit.nonempty_fusionZStar_equiv_of_surjective' δ.rangeRestrict
    δ.rangeRestrict_surjective hAq' hΔne
  let eM : M ⧸ pPrimeCore 2 M ≃* A ⧸ pPrimeCore 2 A :=
    (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage 2 M hMsub).trans
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hAcore).symm)
  have hPLodd : CFSG.ComponentClassification.GSThmB.oddCoreIn (pLayer Cbar 2) = ⊥ := by
    rw [CFSG.ComponentClassification.GSThmB.oddCoreIn, hPLcore, Subgroup.map_bot]
  have hOmap : (CFSG.ComponentClassification.GSThmB.oddCoreIn (T.subgroupOf CK)).map f = ⊥ := by
    rw [CFSG.ComponentClassification.GSThmB.OddQuot.map_oddCoreIn f hfker (T.subgroupOf CK),
      hTeq, hPLodd]
  have hOle : CFSG.ComponentClassification.GSThmB.oddCoreIn (T.subgroupOf CK) ≤ f.ker := by
    intro x hx
    have hx' : f x ∈ (CFSG.ComponentClassification.GSThmB.oddCoreIn
        (T.subgroupOf CK)).map f := ⟨x, hx, rfl⟩
    rw [hOmap] at hx'
    exact MonoidHom.mem_ker.mpr (by simpa using hx')
  have hker_le : f.ker.map CK.subtype ≤ N := by
    rintro x ⟨c, hc, rfl⟩
    have h1 : (((f c : Cbar) : (A ⊔ B : Subgroup (H ⧸ N))) : H ⧸ N) = 1 := by
      rw [MonoidHom.mem_ker.mp hc]
      rfl
    rw [hfapp] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hOsub : (CFSG.ComponentClassification.GSThmB.oddCoreIn
      (T.subgroupOf CK)).map CK.subtype ≤ N :=
    (Subgroup.map_mono hOle).trans hker_le
  have hcore : (pPrimeCore 2 T).map T.subtype ≤ pPrimeCore 2 H := by
    rw [← CFSG.pPrimeCore_map_subgroupOf 2 T CK hTC]
    exact hOsub
  exact ⟨⟨(((Sol78.fusionZStarQuotCongr eT).symm.trans (Sol78.fusionZStarQuotOfCore e₂)).trans
    eA.symm).trans (Sol78.fusionZStarQuotOfCore eM).symm⟩, hcore⟩

variable {G : Type} [Group G] [Finite G]

theorem diagonal_fusionZStar_equiv_and_oddCore {z s : G} (hs : orderOf s = 2)
    (hzs : z * s = s * z) {Y D : Subgroup G}
    (hY : IsTwoComponentIn Y (centralizer ({z} : Set G)))
    (hYs : conjugate Y s ≠ Y)
    (hD : IsTwoComponentIn D (centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G)))
    (hDY : D ≤ Y ⊔ conjugate Y s) :
    Nonempty (↥D ⧸ Open.fusionZStar ↥D ≃* ↥Y ⧸ Open.fusionZStar ↥Y) ∧
      CFSG.ComponentClassification.GSThmB.oddCoreIn D ≤
        CFSG.ComponentClassification.GSThmB.oddCoreIn (centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hC
  have hsC : s ∈ C := mem_centralizer_singleton_iff.mpr hzs.symm
  have hto : orderOf (⟨s, hsC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have hYsC : conjugate Y s ≤ C := UnbalancedCorr.conjugate_le_of_mem hY.1 hsC
  have hMt : conjugate (Y.subgroupOf C) ⟨s, hsC⟩ = (conjugate Y s).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subtype_conjugate, map_subgroupOf_eq_of_le hY.1, map_subgroupOf_eq_of_le hYsC]
  have hne : Y.subgroupOf C ≠ conjugate (Y.subgroupOf C) ⟨s, hsC⟩ := by
    intro h
    apply hYs
    have h1 := congrArg (Subgroup.map C.subtype) h
    rw [hMt, map_subgroupOf_eq_of_le hY.1, map_subgroupOf_eq_of_le hYsC] at h1
    exact h1.symm
  set K' := (Y ⊔ conjugate Y s) ⊓ centralizer ({s} : Set G) with hK'
  have hK'C : K' ≤ C := inf_le_left.trans (sup_le hY.1 hYsC)
  have hCK : (Y.subgroupOf C ⊔ conjugate (Y.subgroupOf C) ⟨s, hsC⟩) ⊓
      centralizer ({(⟨s, hsC⟩ : ↥C)} : Set ↥C) = K'.subgroupOf C := by
    rw [hMt, ← Subgroup.subgroupOf_sup hY.1 hYsC, UGSChain.centralizer_mk_eq_subgroupOf hsC]
    ext x
    simp only [hK', mem_inf, mem_subgroupOf, x.2, and_true]
  have hDK' : D ≤ K' := le_inf hDY (hD.1.trans inf_le_right)
  have hDC : D ≤ C := hD.1.trans inf_le_left
  have hTC : D.subgroupOf C ≤ (Y.subgroupOf C ⊔ conjugate (Y.subgroupOf C) ⟨s, hsC⟩) ⊓
      centralizer ({(⟨s, hsC⟩ : ↥C)} : Set ↥C) := by
    rw [hCK]
    intro x hx
    exact mem_subgroupOf.mpr (hDK' (mem_subgroupOf.mp hx))
  have hT : IsPComponent 2 ((D.subgroupOf C).subgroupOf
      ((Y.subgroupOf C ⊔ conjugate (Y.subgroupOf C) ⟨s, hsC⟩) ⊓
        centralizer ({(⟨s, hsC⟩ : ↥C)} : Set ↥C))) := by
    rw [hCK, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hK'C 2 Nat.prime_two]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hDK'
      (le_inf hK'C inf_le_right) hD.2
  obtain ⟨⟨e⟩, hO⟩ :=
    swap_fusionZStar_equiv_and_oddCore hto (Y.subgroupOf C) hY.2 hne (D.subgroupOf C) hTC hT
  refine ⟨⟨((Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hDC)).symm.trans e).trans
    (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hY.1))⟩, ?_⟩
  have hO' : (pPrimeCore 2 D).map D.subtype ≤ (pPrimeCore 2 C).map C.subtype := by
    rw [← CFSG.pPrimeCore_map_subgroupOf 2 D C hDC]
    exact Subgroup.map_mono hO
  simpa [CFSG.ComponentClassification.GSThmB.oddCoreIn] using hO'

theorem diagonal_fusionZStar_equiv {z s : G} (hs : orderOf s = 2) (hzs : z * s = s * z)
    {Y D : Subgroup G} (hY : IsTwoComponentIn Y (centralizer ({z} : Set G)))
    (hYs : conjugate Y s ≠ Y)
    (hD : IsTwoComponentIn D (centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G)))
    (hDY : D ≤ Y ⊔ conjugate Y s) :
    Nonempty (↥D ⧸ Open.fusionZStar ↥D ≃* ↥Y ⧸ Open.fusionZStar ↥Y) :=
  (diagonal_fusionZStar_equiv_and_oddCore hs hzs hY hYs hD hDY).1

theorem mirror_fusionZStar_equiv_of_free {z s : G} (hz : orderOf z = 2) (hs : orderOf s = 2)
    (hzs : z * s = s * z) {Y D X : Subgroup G}
    (hY : IsTwoComponentIn Y (centralizer ({z} : Set G))) (hYs : conjugate Y s ≠ Y)
    (hX : IsTwoComponentIn X (centralizer ({s} : Set G)))
    (hD : IsTwoComponentIn D (centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G)))
    (hDY : D ≤ Y ⊔ conjugate Y s) (hDX : D ≤ X ⊔ conjugate X z)
    (hfree : conjugate X z ≠ X ∨ z ∈ coreActionKernel X) :
    Nonempty (↥Y ⧸ Open.fusionZStar ↥Y ≃* ↥X ⧸ Open.fusionZStar ↥X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eY⟩ := diagonal_fusionZStar_equiv hs hzs hY hYs hD hDY
  suffices hDX' : Nonempty (↥D ⧸ Open.fusionZStar ↥D ≃* ↥X ⧸ Open.fusionZStar ↥X) by
    obtain ⟨eX⟩ := hDX'
    exact ⟨eY.symm.trans eX⟩
  rcases hfree with hXz | hzX
  ·
    have hD' : IsTwoComponentIn D (centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G)) := by
      rw [inf_comm]; exact hD
    exact diagonal_fusionZStar_equiv hz hzs.symm hX hXz hD' hDX
  ·
    have hXz : conjugate X z = X := by
      have h1 : X.map (MulAut.conj z⁻¹).toMonoidHom = X :=
        mem_normalizer_iff_map_conj_eq.mp (inv_mem (mem_coreActionKernel.mp hzX).1)
      exact h1
    have hDX₁ : D ≤ X := by rw [hXz, sup_idem] at hDX; exact hDX
    have hXq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) :=
      isQuasisimple_quotient_of_isPComponent hX.1 hX.2
    obtain ⟨hJc, hJr, -, ⟨eJ⟩⟩ := Sol76.cover_facts hXq inf_le_left
      (Sol76.inf_centralizer_sup_oddCoreIn_eq (isPGroup_zpowers_of_orderOf hz)
        (zpowers_le.mpr hzX))
    rw [centralizer_zpowers'] at hJc hJr eJ
    have hXzC : X ⊓ centralizer ({z} : Set G) ≤
        centralizer ({z} : Set G) ⊓ centralizer ({s} : Set G) :=
      le_inf inf_le_right (inf_le_left.trans hX.1)
    have hDXz : IsTwoComponentIn D (X ⊓ centralizer ({z} : Set G)) :=
      ⟨le_inf hDX₁ (hD.1.trans inf_le_left),
        CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
          (le_inf hDX₁ (hD.1.trans inf_le_left)) hXzC hD.2⟩
    have hDJ : D ≤ oddResidualIn (X ⊓ centralizer ({z} : Set G)) := by
      rw [← hJr]; exact le_twoLayerIn_of_isTwoComponentIn hDXz
    have hDeq := eq_of_le_of_isTwoComponentIn hDXz hJc hDJ
    rw [← hDeq] at eJ
    exact ⟨Sol78.fusionZStarQuotOfCore eJ⟩

theorem gsFixedLayer_eq_of_common_component {a b : G} {X D : Subgroup G}
    (ha : orderOf a = 2) (hX : IsTwoComponentIn X (Subgroup.centralizer ({b} : Set G)))
    (hab : a * b = b * a) (hXa : conjugate X a = X)
    (haK : a ∈ coreActionKernel X)
    (hD : IsTwoComponentIn D
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)))
    (hDX : D ≤ X) :
    gsFixedLayer X a = D := by
  have haCb : a ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hab
  have hXC : X ⊓ Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hX.1)
  have hDXC : IsTwoComponentIn D (X ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Sol76.isTwoComponentIn_of_le hD (le_inf hDX (hD.1.trans inf_le_left)) hXC
  have hDT : D ≤ gsFixedLayer X a := by
    simpa [gsFixedLayer, twoLayerIn] using le_twoLayerIn_of_isTwoComponentIn hDXC
  have hXsub : (X.subgroupOf (Subgroup.centralizer ({b} : Set G))).IsSubnormal :=
    hX.2.choose_spec.2.1
  have hXq : IsQuasisimple (X ⧸ pPrimeCore 2 X) :=
    isQuasisimple_quotient_of_isPComponent hX.1 hX.2
  have haN : a ∈ Subgroup.normalizer (X : Set G) :=
    UnbalancedLayer.mem_normalizer_of_conjugate_eq hXa
  have hpc := UnbalancedCorr.gsFixedLayer_isPComponent (X := Subgroup.centralizer ({b} : Set G))
    hX.1 hXsub haCb ha haN hXq (mem_coreActionKernel.mp haK).2
  have hTle : gsFixedLayer X a ≤
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
    (gsFixedLayer_le_inf X a).trans (le_inf inf_le_right (inf_le_left.trans hX.1))
  have hT : IsTwoComponentIn (gsFixedLayer X a)
      (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)) := by
    refine ⟨hTle, ?_⟩
    rw [inf_comm]
    exact hpc
  exact (eq_of_le_of_isTwoComponentIn hD hT hDT).symm

end CFSG.ComponentClassification.Foote5.SolMax
