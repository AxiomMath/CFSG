module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASwappedCentralProduct
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSANestedFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup

namespace OrbitFixedComponent

theorem pLayer_eq_of_cover {G Q : Type*} [Group G] [Finite G] [Group Q] (f : G →* Q)
    (hker : Nat.Coprime 2 (Nat.card f.ker)) (T : Subgroup G) (hT : IsPComponent 2 T)
    (hcover : Function.Surjective (f.domRestrict T)) : pLayer G 2 = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTle : T ≤ pLayer G 2 := le_sSup hT
  have hcoverL : Function.Surjective (f.domRestrict (pLayer G 2)) := fun q => by
    obtain ⟨x, hx⟩ := hcover q
    exact ⟨⟨x, hTle x.2⟩, hx⟩
  have hf : Function.Surjective f := fun q => by
    obtain ⟨x, hx⟩ := hcover q
    exact ⟨x, hx⟩
  have h1 := NestedFixedLayer.pLayer_eq_primeResidual 2 f hker hcoverL
  have hindex := CatalogueBPrimeJoin.coprime_index_of_surjective_restriction 2 f hf hker T hcover
  have hTsub : T.IsSubnormal :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 T).mp hT).1
  have h2 := CatalogueBPrimeJoin.primeResidual_le_subnormal_of_coprime_index 2 T hTsub hindex
  exact le_antisymm (h1 ▸ h2) hTle

theorem stable_case {H : Type*} [Group H] [Finite H] (M C : Subgroup H) (hCM : C ≤ M)
    (T : Subgroup H) (hTC : T ≤ C) (hT : IsPComponent 2 (T.subgroupOf C)) :
    (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index ∧
      ((pPrimeCore 2 T).index = (pPrimeCore 2 M).index →
        (pLayer C 2).map C.subtype = T ∧ T ⊔ (pPrimeCore 2 M).map M.subtype = M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : T ≤ M := hTC.trans hCM
  have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 M)) :=
    pPrimeCore_coprime_card (p := 2) (G := M)
  let φ : T →* M ⧸ pPrimeCore 2 M :=
    (QuotientGroup.mk' (pPrimeCore 2 M)).comp (Subgroup.inclusion hTM)
  have hφker : ∀ x : T, x ∈ φ.ker ↔ Subgroup.inclusion hTM x ∈ pPrimeCore 2 M := fun x => by
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff _
  have hkercop : Nat.Coprime 2 (Nat.card φ.ker) := by
    let ι : φ.ker →* pPrimeCore 2 M :=
      { toFun := fun x => ⟨Subgroup.inclusion hTM x, (hφker x).mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (Subgroup.inclusion_injective hTM (congrArg Subtype.val h))
    exact hOcop.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι)
  have hkernorm : φ.ker.Normal := inferInstance
  have hkerle : φ.ker ≤ pPrimeCore 2 T := le_sSup ⟨hkernorm, hkercop⟩
  have hle1 : (pPrimeCore 2 T).index ≤ φ.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.index_dvd_of_le hkerle)
  have hle2 : φ.ker.index ≤ (pPrimeCore 2 M).index := by
    rw [Subgroup.index_ker]
    exact Subgroup.card_le_card_group _
  refine ⟨hle1.trans hle2, fun heq => ?_⟩
  have hrange : Nat.card φ.range = Nat.card (M ⧸ pPrimeCore 2 M) := by
    have h1 : Nat.card φ.range = φ.ker.index := (Subgroup.index_ker φ).symm
    have h2 : Nat.card (M ⧸ pPrimeCore 2 M) = (pPrimeCore 2 M).index := rfl
    omega
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ hrange
  have hsup : T ⊔ (pPrimeCore 2 M).map M.subtype = M := by
    apply le_antisymm (sup_le hTM (map_subtype_le _))
    intro m hm
    obtain ⟨τ, hτ⟩ := hφsurj (⟨m, hm⟩ : M)
    have h1 : (Subgroup.inclusion hTM τ)⁻¹ * ⟨m, hm⟩ ∈ pPrimeCore 2 M :=
      QuotientGroup.eq.mp hτ
    have h2 : m = (τ : H) * (((Subgroup.inclusion hTM τ)⁻¹ * ⟨m, hm⟩ : M) : H) := by simp
    rw [h2]
    exact mul_mem (mem_sup_left τ.2) (mem_sup_right ⟨_, h1, rfl⟩)
  let ψ : C →* M ⧸ pPrimeCore 2 M :=
    (QuotientGroup.mk' (pPrimeCore 2 M)).comp (Subgroup.inclusion hCM)
  have hψker : Nat.Coprime 2 (Nat.card ψ.ker) := by
    let ι : ψ.ker →* pPrimeCore 2 M :=
      { toFun := fun x => ⟨Subgroup.inclusion hCM x,
          (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (Subgroup.inclusion_injective hCM (congrArg Subtype.val h))
    exact hOcop.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι)
  have hcover : Function.Surjective (ψ.domRestrict (T.subgroupOf C)) := by
    intro q
    obtain ⟨τ, hτ⟩ := hφsurj q
    exact ⟨⟨⟨τ, hTC τ.2⟩, τ.2⟩, hτ⟩
  have hlayer := pLayer_eq_of_cover ψ hψker (T.subgroupOf C) hT hcover
  refine ⟨?_, hsup⟩
  rw [hlayer, subgroupOf_map_subtype, inf_of_le_left hTC]

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

theorem swap_case {H : Type*} [Group H] [Finite H] {t : H} (ht : orderOf t = 2)
    (M : Subgroup H) (hM : IsPComponent 2 M) (hne : M ≠ conjugate M t) (T : Subgroup H)
    (hTC : T ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))
    (hT : IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H)))) :
    (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index ∧
      (pLayer ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H) : Subgroup H) 2).map
        ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H)).subtype = T := by
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
  have hTbar : IsPComponent 2 ((T.subgroupOf CK).map f) := hbij.mapsTo hT
  have hTeq : (T.subgroupOf CK).map f = pLayer Cbar 2 :=
    CatalogueBPrimeJoin.eq_of_le 2 _ _ hTbar hPLcomp (le_sSup hTbar)
  have huniq : ∀ U : Subgroup CK, IsPComponent 2 U → U = T.subgroupOf CK := by
    intro U hU
    have hUbar : IsPComponent 2 (U.map f) := hbij.mapsTo hU
    have hUeq : U.map f = pLayer Cbar 2 :=
      CatalogueBPrimeJoin.eq_of_le 2 _ _ hUbar hPLcomp (le_sSup hUbar)
    exact hbij.injOn hU hT (hUeq.trans hTeq.symm)
  have hlayerCK : pLayer CK 2 = T.subgroupOf CK :=
    le_antisymm (sSup_le fun U hU => (huniq U hU).le) (le_sSup hT)
  refine ⟨?_, by rw [hlayerCK, subgroupOf_map_subtype, inf_of_le_left hTC]⟩
  obtain ⟨e₁, -⟩ := hiso (T.subgroupOf CK) hT
  have hcardA : Nat.card A = (pPrimeCore 2 M).index :=
    (Nat.card_congr (CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage 2 M
      hMsub).toEquiv).symm
  let eT : T.subgroupOf CK ≃* T := subgroupOfEquivOfLe hTC
  have h1 : (pPrimeCore 2 T).index =
      Nat.card ((T.subgroupOf CK) ⧸ pPrimeCore 2 (T.subgroupOf CK)) :=
    (Nat.card_congr (QuotientGroup.congr _ _ eT (pPrimeCore_map_iso 2 eT)).toEquiv).symm
  have h2 := Nat.card_congr e₁.toEquiv
  let eL : ((T.subgroupOf CK).map f) ≃* pLayer Cbar 2 := MulEquiv.subgroupCongr hTeq
  have h3 : Nat.card (((T.subgroupOf CK).map f) ⧸ pPrimeCore 2 ((T.subgroupOf CK).map f)) =
      Nat.card ((pLayer Cbar 2) ⧸ pPrimeCore 2 (pLayer Cbar 2)) :=
    Nat.card_congr (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)).toEquiv
  have h4 : Nat.card ((pLayer Cbar 2) ⧸ pPrimeCore 2 (pLayer Cbar 2)) =
      Nat.card (pLayer Cbar 2) :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hPLcore).trans
      QuotientGroup.quotientBot).toEquiv
  rw [h1, h2, h3, h4, ← hcardA]
  exact hle

end OrbitFixedComponent

theorem involution_orbit_fixed_component_quotient_comparison {H : Type*} [Group H] [Finite H]
    {t : H} (ht : orderOf t = 2) (M : Subgroup H) (hM : IsPComponent 2 M) (K : Subgroup H)
    (hK : K = M ⊔ conjugate M t) (C : Subgroup H) (hC : C = K ⊓ centralizer ({t} : Set H))
    (T : Subgroup H) (hTC : T ≤ C) (hT : IsPComponent 2 (T.subgroupOf C)) :
    (pPrimeCore 2 T).index ≤ (pPrimeCore 2 M).index ∧
      (M ≠ conjugate M t → (pLayer C 2).map C.subtype = T) ∧
      ((pPrimeCore 2 T).index = (pPrimeCore 2 M).index →
        (pLayer C 2).map C.subtype = T ∧
          (M = conjugate M t → T ⊔ (pPrimeCore 2 M).map M.subtype = M)) := by
  subst hK hC
  by_cases hMt : M = conjugate M t
  · have hCM : (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H) ≤ M := by
      rw [← hMt, sup_idem]
      exact inf_le_left
    obtain ⟨hle, heq⟩ := OrbitFixedComponent.stable_case M _ hCM T hTC hT
    exact ⟨hle, fun h => absurd hMt h, fun h => ⟨(heq h).1, fun _ => (heq h).2⟩⟩
  · obtain ⟨hle, hlayer⟩ := OrbitFixedComponent.swap_case ht M hM hMt T hTC hT
    exact ⟨hle, fun _ => hlayer, fun _ => ⟨hlayer, fun h => absurd h hMt⟩⟩

end CFSG.ComponentClassification.UnbalancedGS
