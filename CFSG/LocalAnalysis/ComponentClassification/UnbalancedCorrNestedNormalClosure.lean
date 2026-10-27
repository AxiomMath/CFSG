module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNormalClosure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedNormalGeneration

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem map_map_pPrimeCore_subtype {X : Subgroup G} (Y : Subgroup X) :
    ((pPrimeCore 2 Y).map Y.subtype).map X.subtype =
      (pPrimeCore 2 ↥(Y.map X.subtype)).map (Y.map X.subtype).subtype := by
  let e : Y ≃* ↥(Y.map X.subtype) := Y.equivMapOfInjective X.subtype X.subtype_injective
  have hcomm : X.subtype.comp Y.subtype = (Y.map X.subtype).subtype.comp e.toMonoidHom := by
    ext y
    rfl
  rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso 2 e]

theorem normalClosure_eq_top_of_iSup_conjugate {K W : Subgroup G} (hWK : W ≤ K)
    (h : (⨆ k ∈ K, conjugate W k) = K) :
    normalClosure ((W.subgroupOf K : Subgroup K) : Set K) = ⊤ := by
  set M := normalClosure ((W.subgroupOf K : Subgroup K) : Set K) with hM
  have hMn : M.Normal := normalClosure_normal
  have hle' : (⨆ k ∈ K, conjugate W k) ≤ M.map K.subtype := by
    refine iSup₂_le fun k hk => ?_
    intro y hy
    rw [mem_conjugate_iff] at hy
    have hyK : y ∈ K := by
      have h1 := mul_mem (mul_mem (inv_mem hk) (hWK hy)) hk
      rwa [show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h1
    have h1 : (⟨k * y * k⁻¹, hWK hy⟩ : K) ∈ M :=
      subset_normalClosure (show (⟨k * y * k⁻¹, hWK hy⟩ : K) ∈ W.subgroupOf K from hy)
    have h2 := hMn.conj_mem _ h1 (⟨k, hk⟩⁻¹)
    have heq : (⟨y, hyK⟩ : K) = ⟨k, hk⟩⁻¹ * ⟨k * y * k⁻¹, hWK hy⟩ * ⟨k, hk⟩⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv, inv_inv]
      group
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    rw [heq]
    exact h2
  have hle : K ≤ M.map K.subtype := by
    rw [h] at hle'
    exact hle'
  apply eq_top_iff.mpr
  intro x _
  exact (mem_map_iff_mem K.subtype_injective).mp (hle x.2)

theorem normalClosure_subgroupOf_map {K W : Subgroup G} (V : Subgroup K)
    (h : normalClosure (((W.subgroupOf K).subgroupOf V : Subgroup V) : Set V) = ⊤) :
    normalClosure ((W.subgroupOf (V.map K.subtype) : Subgroup (V.map K.subtype)) :
      Set (V.map K.subtype)) = ⊤ := by
  let f : V →* ↥(V.map K.subtype) :=
    (V.equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom
  have hf : Function.Surjective f :=
    (V.equivMapOfInjective K.subtype K.subtype_injective).surjective
  have himg : f '' (((W.subgroupOf K).subgroupOf V : Subgroup V) : Set V) =
      ((W.subgroupOf (V.map K.subtype) : Subgroup _) : Set _) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx, hxy⟩ := mem_map.mp y.2
      refine ⟨⟨x, hx⟩, ?_, Subtype.ext hxy⟩
      show ((x : K) : G) ∈ W
      rw [show ((x : K) : G) = y from hxy]
      exact hy
  rw [← himg, ← map_normalClosure _ f hf, h, map_top_of_surjective f hf]

theorem isPGroup_closure_pair {b e : G} (hbb : b * b = 1) (hee : e * e = 1)
    (hbe : b * e = e * b) : IsPGroup 2 (closure ({b, e} : Set G)) := by
  have hcomm : closure ({b, e} : Set G) ≤
      centralizer ((closure ({b, e} : Set G) : Subgroup G) : Set G) := by
    rw [centralizer_closure, closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_iff] <;>
      rintro y (rfl | rfl)
    all_goals first | rfl | exact hbe | exact hbe.symm
  have hsq : ∀ x ∈ closure ({b, e} : Set G), x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hbb
      · exact hee
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := mem_centralizer_iff.mp (hcomm hy) x hx
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ih => rw [← mul_inv_rev, ih, inv_one]
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, coe_pow, pow_two, hsq x x.2, coe_one]

variable [Finite G]

theorem map_pLayer_subgroupOf_eq (J Y : Subgroup G) :
    ((pLayer ↥(Y.subgroupOf J) 2).map (Y.subgroupOf J).subtype).map J.subtype =
      (pLayer ↥(J ⊓ Y) 2).map (J ⊓ Y).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.map_map]
  let φ : ↥(Y.subgroupOf J) ≃* ↥(J ⊓ Y) :=
    { toFun := fun x => ⟨x, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcomp : J.subtype.comp (Y.subgroupOf J).subtype = (J ⊓ Y).subtype.comp φ.toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 φ]

theorem corr_factor_le_of_image {a b : G} {J L : Subgroup G} (h : UnbalancedGS.GSCorr a J b L)
    {R : Subgroup G} (hRK : R ≤ L ⊔ conjugate L a)
    (hKR : L ⊔ conjugate L a ≤ normalizer (R : Set G))
    (hfixed : conjugate L a = L → ∃ P : Subgroup G, P ≤ R ∧ ⁅P, P⁆ = P ∧
      UnbalancingLocal.corrImage b P ≠ ⊥)
    (hswap : conjugate L a ≠ L → UnbalancingLocal.corrImage b (UnbalancedGS.gsFixedLayer J b) ≤
      UnbalancingLocal.corrImage b R) :
    L ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison h
  obtain ⟨hao, -, hab, -, -, hLb, hL, -, -, -⟩ := h
  set H := centralizer ({b} : Set G) with hHdef
  have haa : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  have haH : a ∈ H := mem_centralizer_singleton_iff.mpr hab
  have hLaH : conjugate L a ≤ H := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem haH) (hLb hy)) haH
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
  have hKH : L ⊔ conjugate L a ≤ H := sup_le hLb hLaH
  have hL₂ : IsPComponent 2 ((conjugate L a).subgroupOf H) := by
    have h1 := isPComponent_conjugate hL (⟨a, haH⟩ : H)
    rwa [conjugate_subgroupOf_eq] at h1
  have hKL : L ⊔ conjugate L a ≤ normalizer (L : Set G) := by
    refine sup_le le_normalizer fun y hy => ?_
    by_cases heq : L.subgroupOf H = (conjugate L a).subgroupOf H
    · have h1 : (⟨y, hLaH hy⟩ : H) ∈ normalizer (L.subgroupOf H : Set H) := by
        rw [heq]
        exact le_normalizer (show (⟨y, hLaH hy⟩ : H) ∈ (conjugate L a).subgroupOf H from hy)
      exact mem_normalizer_of_subgroupOf hLb h1
    · exact mem_normalizer_of_subgroupOf hLb
        (((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hL
          hL₂).2 heq).1 (show (⟨y, hLaH hy⟩ : H) ∈ (conjugate L a).subgroupOf H from hy))
  have hR₁L : R.subgroupOf H ≤ normalizer (L.subgroupOf H : Set H) := fun r hr =>
    mem_normalizer_subgroupOf_of_mem (hKL (hRK hr))
  have hL₁R : L.subgroupOf H ≤ normalizer (R.subgroupOf H : Set H) := fun l hl =>
    mem_normalizer_subgroupOf_of_mem (hKR (le_sup_left (a := L) hl))
  have hmain : ⁅(L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)),
      (R.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))⁆ =
      (L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
    have hle : ⁅(L.subgroupOf H).map π, (R.subgroupOf H).map π⁆ ≤ (L.subgroupOf H).map π :=
      commutator_le_left_of_le_normalizer ((map_mono hR₁L).trans (le_normalizer_map π))
    obtain ⟨Kc, hKc, -, hmapL, -⟩ := id hL
    have hAq : IsQuasisimple ↥((L.subgroupOf H).map π) := by
      rw [hmapL]
      exact hKc.1
    have hAperf : ⁅(L.subgroupOf H).map π, (L.subgroupOf H).map π⁆ = (L.subgroupOf H).map π :=
      Subgroup.isPerfect_iff.mp hAq.1
    by_cases hLa : conjugate L a = L
    ·
      obtain ⟨P, hPR, hPperf, hPnt⟩ := hfixed hLa
      have hRL : R.subgroupOf H ≤ L.subgroupOf H := fun y hy => by
        have := hRK hy
        rwa [hLa, sup_idem] at this
      have hPH : P ≤ H := hPR.trans (hRK.trans hKH)
      have hP₁R₁ : P.subgroupOf H ≤ R.subgroupOf H := fun y hy => hPR hy
      have hP₁perf : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
        apply map_injective H.subtype_injective
        rw [map_commutator, map_subgroupOf_eq_of_le hPH, hPperf]
      have hnorm : (((R.subgroupOf H).map π).subgroupOf ((L.subgroupOf H).map π)).Normal := by
        rw [normal_subgroupOf_iff_le_normalizer (map_mono hRL)]
        exact (map_mono hL₁R).trans (le_normalizer_map π)
      rcases quasisimple_normal_subgroups hAq hnorm with htop | hcen
      · have hRLeq : (R.subgroupOf H).map π = (L.subgroupOf H).map π :=
          le_antisymm (map_mono hRL) ((subgroupOf_eq_top (H := (R.subgroupOf H).map π)
            (K := (L.subgroupOf H).map π)).mp htop)
        rw [hRLeq, hAperf]
      · exfalso
        apply hPnt
        apply eq_bot_of_perfect_of_comm (by
          show ⁅(P.subgroupOf H).map π, (P.subgroupOf H).map π⁆ = (P.subgroupOf H).map π
          rw [← map_commutator, hP₁perf])
        intro x hx y hy
        have hxR := map_mono hP₁R₁ hx
        have hyL : y ∈ (L.subgroupOf H).map π := map_mono (hP₁R₁.trans hRL) hy
        have hxc := hcen (show (⟨x, map_mono hRL hxR⟩ : ↥((L.subgroupOf H).map π)) ∈
          ((R.subgroupOf H).map π).subgroupOf ((L.subgroupOf H).map π) from hxR)
        have := congrArg Subtype.val ((mem_center_iff.mp hxc) ⟨y, hyL⟩)
        exact this.symm
    ·
      obtain ⟨α, hαk, -, hcomm, -, -, -, -, hmemT, -⟩ := hcmp.2.2.1 hLa haH
      have hTR := hswap hLa
      have hαB : ∀ u : ↥(UnbalancingLocal.corrImage b L ⊔
          UnbalancingLocal.corrImage b (conjugate L a)),
          (u : UnbalancingLocal.CorrQuotient b) ∈ UnbalancingLocal.corrImage b L →
          ((α u : ↥(UnbalancingLocal.corrImage b L ⊔
            UnbalancingLocal.corrImage b (conjugate L a))) : UnbalancingLocal.CorrQuotient b) ∈
            UnbalancingLocal.corrImage b (conjugate L a) := by
        intro u hu
        rw [hαk u]
        obtain ⟨l, hl, hlu⟩ := mem_map.mp hu
        refine ⟨⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹, ?_, ?_⟩
        · show ((⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹ : H) : G) ∈ conjugate L a
          rw [mem_conjugate_iff]
          have hl' : (l : G) ∈ L := hl
          rwa [show a * ((⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹ : H) : G) * a⁻¹ = (l : G) by
            simp only [coe_mul, coe_inv]
            rw [show a * (a * (l : G) * a⁻¹) * a⁻¹ = (a * a) * l * (a * a)⁻¹ by group, haa]
            group]
        · rw [map_mul, map_mul, map_inv, hlu]
          rfl
      apply le_antisymm hle
      calc (L.subgroupOf H).map π = ⁅(L.subgroupOf H).map π, (L.subgroupOf H).map π⁆ :=
            hAperf.symm
        _ ≤ ⁅(L.subgroupOf H).map π, (R.subgroupOf H).map π⁆ := by
          rw [commutator_le]
          intro v hv u hu
          have hu' : u ∈ UnbalancingLocal.corrImage b L ⊔
              UnbalancingLocal.corrImage b (conjugate L a) := le_sup_left (a :=
                UnbalancingLocal.corrImage b L) hu
          have hΔ : u * ((α ⟨u, hu'⟩ : ↥(UnbalancingLocal.corrImage b L ⊔
              UnbalancingLocal.corrImage b (conjugate L a))) : UnbalancingLocal.CorrQuotient b) ∈
              UnbalancingLocal.corrImage b (UnbalancedGS.gsFixedLayer J b) :=
            (hmemT _).mpr ⟨⟨u, hu'⟩, hu, rfl⟩
          have hw := hαB ⟨u, hu'⟩ hu
          set w := ((α ⟨u, hu'⟩ : ↥(UnbalancingLocal.corrImage b L ⊔
            UnbalancingLocal.corrImage b (conjugate L a))) : UnbalancingLocal.CorrQuotient b)
          have hvw : v * w = w * v := hcomm v hv w hw
          have hwv : w * v⁻¹ = v⁻¹ * w := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hvw, inv_mul_cancel_left]
          have hid : ⁅v, u⁆ = ⁅v, u * w⁆ := by
            rw [commutatorElement_def, commutatorElement_def]
            calc v * u * v⁻¹ * u⁻¹ = v * u * (v⁻¹ * w) * w⁻¹ * u⁻¹ := by group
              _ = v * u * (w * v⁻¹) * w⁻¹ * u⁻¹ := by rw [hwv]
              _ = v * (u * w) * v⁻¹ * (u * w)⁻¹ := by group
          rw [hid]
          exact commutator_mem_commutator hv (hTR hΔ)
  have hLR₁ := le_of_commutator_map_eq hL hR₁L hL₁R hmain
  exact fun y hy => hLR₁ (show (⟨y, hLb hy⟩ : H) ∈ L.subgroupOf H from hy)

theorem correspondence_nested_fixed_layer_normal_closure {a b e : G} {J L : Subgroup G}
    (h : UnbalancedGS.GSCorr a J b L) (he : orderOf e = 2) (hbe : b * e = e * b)
    (heJ : e ∈ normalizer (J : Set G))
    (heK : e ∈ normalizer ((L ⊔ conjugate L a : Subgroup G) : Set G))
    (hJe : ∀ j ∈ J, j⁻¹ * e⁻¹ * j * e ∈ (pPrimeCore 2 J).map J.subtype)
    (hKe : ∀ k ∈ L ⊔ conjugate L a, k⁻¹ * e⁻¹ * k * e ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype)
    {T U W V : Subgroup G} (hT : T = UnbalancedGS.gsFixedLayer J b)
    (hU : U = UnbalancedGS.gsFixedLayer J e)
    (hW : W = (pLayer ↥(J ⊓ centralizer ({b, e} : Set G)) 2).map
      (J ⊓ centralizer ({b, e} : Set G)).subtype)
    (hV : V = UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) e) :
    W ≤ T ⊓ U ∧ W ⊔ (pPrimeCore 2 T).map T.subtype = T ∧
      (W : Set G) * ((pPrimeCore 2 T).map T.subtype : Set G) = T ∧
      W ⊔ (pPrimeCore 2 U).map U.subtype = U ∧
      (W : Set G) * ((pPrimeCore 2 U).map U.subtype : Set G) = U ∧
      W ≤ V ∧ normalClosure ((W.subgroupOf V : Subgroup V) : Set V) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hT hU hW hV
  have hcard := UnbalancingLocal.Correspondence.card_gsFixedLayer_quotient h
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison h
  have hcorr := h
  obtain ⟨hao, hbo, hab, hJa, hJ, hLb, hL, hbN, hcomm, hfix⟩ := hcorr
  set H := centralizer ({b} : Set G) with hHdef
  set N := (pPrimeCore 2 H).map H.subtype with hNdef
  have haa : a * a = 1 := by rw [← pow_two, ← hao, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hbo, pow_orderOf_eq_one]
  have hee : e * e = 1 := by rw [← pow_two, ← he, pow_orderOf_eq_one]
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have haH : a ∈ H := mem_centralizer_singleton_iff.mpr hab
  have hLaH : conjugate L a ≤ H := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem haH) (hLb hy)) haH
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
  have hKH : L ⊔ conjugate L a ≤ H := sup_le hLb hLaH
  have hL₂ : IsPComponent 2 ((conjugate L a).subgroupOf H) := by
    have h1 := isPComponent_conjugate hL (⟨a, haH⟩ : H)
    rwa [conjugate_subgroupOf_eq] at h1
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hJnt : Nontrivial (J ⧸ pPrimeCore 2 J) := by
    have : IsSimpleGroup ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) := hJq.2.1
    exact (QuotientGroup.mk'_surjective (center (J ⧸ pPrimeCore 2 J))).nontrivial
  have hTK : UnbalancedGS.gsFixedLayer J b ≤ L ⊔ conjugate L a := by
    rw [hfix]
    exact (UnbalancedGS.gsFixedLayer_le_inf _ a).trans inf_le_left
  have hTH : UnbalancedGS.gsFixedLayer J b ≤ H := hTK.trans hKH
  have hbQ : b ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨hbN, hcomm⟩
  have heQ : e ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨heJ, hJe⟩
  set A := closure ({b, e} : Set G) with hAdef
  have hAQ : A ≤ coreActionKernel J := by
    rw [hAdef, closure_le]
    rintro x (rfl | rfl)
    · exact hbQ
    · exact heQ
  have hAN : A ≤ normalizer (J : Set G) := fun x hx => (mem_coreActionKernel.mp (hAQ hx)).1
  have hA2 : IsPGroup 2 A := isPGroup_closure_pair hbb hee hbe
  let α : A →* MulAut J := J.normalizerMonoidHom.comp (inclusion hAN)
  have hα : ∀ (c : A) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => normalizerMonoidHom_apply_apply_coe J _ j
  have htriv : ∀ (c : A) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rw [eq_comm, QuotientGroup.eq]
    apply (mem_map_iff_mem J.subtype_injective).mp
    have h1 := (mem_coreActionKernel.mp (inv_mem (hAQ c.2))).2 j j.2
    rw [inv_inv] at h1
    show (j : G)⁻¹ * ((α c j : J) : G) ∈ (pPrimeCore 2 J).map J.subtype
    rw [hα]
    rwa [show (j : G)⁻¹ * ((c : G) * j * (c : G)⁻¹) = (j : G)⁻¹ * c * j * (c : G)⁻¹ by group]
  set C : Subgroup A → Subgroup J := fun B =>
    (centralizer ((B.map A.subtype : Subgroup G) : Set G)).subgroupOf J with hCdef
  have hC : ∀ (B : Subgroup A) (x : J), x ∈ C B ↔ ∀ c ∈ B, α c x = x := by
    intro B x
    show (x : G) ∈ centralizer ((B.map A.subtype : Subgroup G) : Set G) ↔ _
    rw [mem_centralizer_iff]
    constructor
    · intro h1 c hc
      apply Subtype.ext
      rw [hα, h1 (c : G) ⟨c, hc, rfl⟩, mul_inv_cancel_right]
    · intro h1 g hg
      obtain ⟨c, hc, rfl⟩ := mem_map.mp hg
      have h2 := congrArg Subtype.val (h1 c hc)
      rw [hα] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
  set Tf : Subgroup A → Subgroup J := fun B => (pLayer (C B) 2).map (C B).subtype with hTfdef
  obtain ⟨hclos, hnest⟩ :=
    UnbalancedGS.nested_fixed_prime_layer_covering 2 hA2 α hJq htriv C hC Tf (fun B => rfl)
  have hTfY : ∀ (B : Subgroup A) (Y : Subgroup G),
      centralizer ((B.map A.subtype : Subgroup G) : Set G) = Y →
      (Tf B).map J.subtype = (pLayer ↥(J ⊓ Y) 2).map (J ⊓ Y).subtype := by
    intro B Y hY
    subst hY
    exact map_pLayer_subgroupOf_eq J _
  have hbA : b ∈ A := subset_closure (Set.mem_insert b {e})
  have heA : e ∈ A := subset_closure (Set.mem_insert_of_mem b rfl)
  have hB₁ : centralizer ((((zpowers (⟨b, hbA⟩ : A)).map A.subtype : Subgroup G)) : Set G) =
      centralizer ({b} : Set G) := by
    rw [MonoidHom.map_zpowers]
    exact centralizer_zpowers_eq b
  have hB₂ : centralizer ((((zpowers (⟨e, heA⟩ : A)).map A.subtype : Subgroup G)) : Set G) =
      centralizer ({e} : Set G) := by
    rw [MonoidHom.map_zpowers]
    exact centralizer_zpowers_eq e
  have hBtop : centralizer ((((⊤ : Subgroup A)).map A.subtype : Subgroup G) : Set G) =
      centralizer ({b, e} : Set G) := by
    rw [← MonoidHom.range_eq_map, range_subtype, hAdef, centralizer_closure]
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  set U := UnbalancedGS.gsFixedLayer J e with hUdef
  set W := (pLayer ↥(J ⊓ centralizer ({b, e} : Set G)) 2).map
    (J ⊓ centralizer ({b, e} : Set G)).subtype with hWdef
  have hWmap : (Tf ⊤).map J.subtype = W := hTfY _ _ hBtop
  have hTmap : (Tf (zpowers ⟨b, hbA⟩)).map J.subtype = T := hTfY _ _ hB₁
  have hUmap : (Tf (zpowers ⟨e, heA⟩)).map J.subtype = U := hTfY _ _ hB₂
  obtain ⟨hle₁, hsup₁, -⟩ := hnest (zpowers ⟨b, hbA⟩) ⊤ le_top
  obtain ⟨hle₂, hsup₂, -⟩ := hnest (zpowers ⟨e, heA⟩) ⊤ le_top
  have hWT : W ≤ T := by
    rw [← hWmap, ← hTmap]
    exact map_mono hle₁
  have hWU : W ≤ U := by
    rw [← hWmap, ← hUmap]
    exact map_mono hle₂
  have hWsupT : W ⊔ (pPrimeCore 2 T).map T.subtype = T := by
    have h1 := congrArg (Subgroup.map J.subtype) hsup₁
    rw [Subgroup.map_sup, map_map_pPrimeCore_subtype, hTmap, hWmap] at h1
    exact h1
  have hWsupU : W ⊔ (pPrimeCore 2 U).map U.subtype = U := by
    have h1 := congrArg (Subgroup.map J.subtype) hsup₂
    rw [Subgroup.map_sup, map_map_pPrimeCore_subtype, hUmap, hWmap] at h1
    exact h1
  have hWmulT : (W : Set G) * ((pPrimeCore 2 T).map T.subtype : Set G) = T := by
    rw [← UnbalancedGS.coe_sup_primeCore_eq_mul hWT, hWsupT]
  have hWmulU : (W : Set G) * ((pPrimeCore 2 U).map U.subtype : Set G) = U := by
    rw [← UnbalancedGS.coe_sup_primeCore_eq_mul hWU, hWsupU]
  have hWgen : W = closure {x : G | x ∈ W ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
    apply le_antisymm _ ((closure_le _).mpr fun x hx => hx.1)
    intro y hy
    rw [← hWmap] at hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    rw [hclos ⊤] at hx
    have h1 : (closure {x : J | x ∈ C ⊤ ∧ ∃ k : ℕ, orderOf x = 2 ^ k}).map J.subtype ≤
        closure {x : G | x ∈ W ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨z, ⟨hzC, k, hk⟩, rfl⟩
      refine ⟨?_, k, ?_⟩
      · rw [← hWmap]
        refine mem_map_of_mem _ ?_
        rw [hclos ⊤]
        exact subset_closure ⟨hzC, k, hk⟩
      · show orderOf (z : G) = 2 ^ k
        rw [Subgroup.orderOf_coe, hk]
    exact h1 (mem_map_of_mem _ hx)
  have hWperf : ⁅W, W⁆ = W := by
    rw [hWdef, ← map_commutator, pLayer_two_isPerfect]
  have hWJ : W ≤ J := hWT.trans ((UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left)
  have hWK : W ≤ L ⊔ conjugate L a := hWT.trans hTK
  have hWH : W ≤ H := hWK.trans hKH
  have hWe : W ≤ centralizer ({e} : Set G) :=
    (map_subtype_le _).trans (inf_le_right.trans (centralizer_le (by simp)))
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, card_map_of_injective H.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hWnt : UnbalancingLocal.corrImage b W ≠ ⊥ := by
    intro hbot
    have hWN : W ≤ N := by
      intro w hw
      have h1 : (⟨w, hWH hw⟩ : H) ∈ W.subgroupOf H := hw
      have h2 := mem_map_of_mem (QuotientGroup.mk' (pPrimeCore 2 H)) h1
      have h3 : (W.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)) = ⊥ := hbot
      rw [h3, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact ⟨_, h2, rfl⟩
    have hW1 : W = ⊥ := by
      apply eq_bot_iff.mpr
      calc W = closure {x : G | x ∈ W ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := hWgen
        _ ≤ ⊥ := by
          rw [closure_le]
          rintro x ⟨hxW, k, hk⟩
          rw [SetLike.mem_coe, mem_bot]
          exact eq_one_of_mem_of_pow_two_pow hNodd (hWN hxW) (by rw [← hk, pow_orderOf_eq_one])
    have hOT : (pPrimeCore 2 T).map T.subtype = T := by
      have h1 := hWsupT
      rwa [hW1, bot_sup_eq] at h1
    have htop : pPrimeCore 2 T = ⊤ := by
      apply map_injective T.subtype_injective
      rw [hOT, ← MonoidHom.range_eq_map, range_subtype]
    have h1 : Nat.card (T ⧸ pPrimeCore 2 T) = 1 := by
      rw [← index_eq_card, htop, index_top]
    rw [hcard] at h1
    exact (Finite.one_lt_card_iff_nontrivial.mpr hJnt).ne' h1
  set R := ⨆ k ∈ L ⊔ conjugate L a, conjugate W k with hRdef
  have hWR : W ≤ R := by
    have h1 : conjugate W 1 ≤ R := le_iSup₂_of_le (1 : G) (one_mem _) le_rfl
    rwa [conjugate_one] at h1
  have hRK : R ≤ L ⊔ conjugate L a := iSup₂_le fun k hk => by
    rw [← conjugate_eq_of_mem_normalizer (le_normalizer hk)]
    exact map_mono hWK
  have hKR : L ⊔ conjugate L a ≤ normalizer (R : Set G) := fun g hg =>
    mem_normalizer_iSup_conjugate_of_mem hg
  have haK : a ∈ normalizer ((L ⊔ conjugate L a : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conjugate_eq
    rw [conjugate_sup, conjugate_conjugate_self_of_mul_self haa, sup_comm]
  have haW : a ∈ normalizer (W : Set G) := mem_normalizer_of_conjugate_eq
    (conjugate_eq_self_of_le_centralizer (hWJ.trans hJa))
  have haR : a ∈ normalizer (R : Set G) := mem_normalizer_iSup_conjugate_of_normalizer haK haW
  have hOTN : conjugate L a ≠ L → (pPrimeCore 2 T).map T.subtype ≤ N := by
    intro hne x hx
    obtain ⟨-, -, -, -, -, -, -, -, -, ⟨eT, heT⟩, -⟩ := hcmp.2.2.1 hne haH
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hx
    have htH : (t : G) ∈ H := hTH t.2
    have h1 := heT t htH
    have h2 : (t : T ⧸ pPrimeCore 2 T) = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    rw [h2, map_one, Subgroup.coe_one] at h1
    have h3 := h1.symm
    rw [QuotientGroup.eq_one_iff] at h3
    exact ⟨_, h3, rfl⟩
  have hswap : conjugate L a ≠ L →
      UnbalancingLocal.corrImage b T ≤ UnbalancingLocal.corrImage b R := by
    intro hne x hx
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hx
    have htT : (t : G) ∈ T := ht
    have hmem : (t : G) ∈ (W : Set G) * ((pPrimeCore 2 T).map T.subtype : Set G) := by
      rw [hWmulT]
      exact htT
    obtain ⟨w, hw, n, hn, hwn⟩ := Set.mem_mul.mp hmem
    obtain ⟨n', hn', hn'eq⟩ := mem_map.mp (hOTN hne hn)
    refine ⟨⟨w, hWH hw⟩, hWR hw, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    convert hn' using 1
    apply Subtype.ext
    have hn'' : (n' : G) = n := hn'eq
    rw [coe_mul, coe_inv, hn'', ← hwn]
    group
  have hLR : L ≤ R := corr_factor_le_of_image h hRK hKR (fun _ => ⟨W, hWR, hWperf, hWnt⟩) hswap
  have hLaR : conjugate L a ≤ R := by
    rw [← conjugate_eq_of_mem_normalizer haR]
    exact map_mono hLR
  have hReq : R = L ⊔ conjugate L a := le_antisymm hRK (sup_le hLR hLaR)
  have hnc := normalClosure_eq_top_of_iSup_conjugate hWK hReq
  set K := L ⊔ conjugate L a with hKdef
  set NK : Subgroup K := N.subgroupOf K with hNKdef
  have hHN : ∀ g ∈ H, g ∈ normalizer (N : Set G) := fun g hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pPrimeCore 2 H)
      (le_normalizer hg)
  have hNKn : NK.Normal := ⟨fun n hn k => by
    have hk : (k : G) ∈ normalizer (N : Set G) := hHN _ (hKH k.2)
    exact (mem_normalizer_iff.mp hk n).mp hn⟩
  have hNKodd : ¬ 2 ∣ Nat.card NK := by
    have h1 : Nat.card NK ∣ Nat.card N :=
      card_comap_dvd_of_injective N K.subtype K.subtype_injective
    exact fun h2 => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr (h2.trans h1))
  have hLK : IsPComponent 2 (L.subgroupOf K) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le le_sup_left hKH hL
  have hLaK : IsPComponent 2 ((conjugate L a).subgroupOf K) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le le_sup_right hKH hL₂
  have hKlayer : pLayer ↥K 2 = ⊤ := by
    have h1 : L.subgroupOf K ⊔ (conjugate L a).subgroupOf K = ⊤ := by
      apply map_injective K.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
        map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
    apply eq_top_iff.mpr
    rw [← h1]
    have h2 : L.subgroupOf K ≤ pLayer ↥K 2 := le_sSup hLK
    have h3 : (conjugate L a).subgroupOf K ≤ pLayer ↥K 2 := le_sSup hLaK
    exact sup_le h2 h3
  have hEQ : pLayer (↥K ⧸ NK) 2 = ⊤ := by
    have h1 := UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel (p := 2)
      (QuotientGroup.mk' NK) (QuotientGroup.mk'_surjective NK) (by rwa [QuotientGroup.ker_mk'])
    rw [← h1, hKlayer, map_top_of_surjective _ (QuotientGroup.mk'_surjective NK)]
  have hzp : ∀ c ∈ zpowers e, c = 1 ∨ c = e := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hee, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hee, one_zpow, one_mul, zpow_one]
  have heK' : zpowers e ≤ normalizer (K : Set G) := zpowers_le.mpr heK
  let αe : zpowers e →* MulAut K := K.normalizerMonoidHom.comp (inclusion heK')
  have hαe : ∀ (c : zpowers e) (k : K), ((αe c k : K) : G) = (c : G) * k * (c : G)⁻¹ :=
    fun c k => normalizerMonoidHom_apply_apply_coe K _ k
  have hAe : IsPGroup 2 (zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he, pow_one])
  have hαQ : ∀ (c : zpowers e) (k : K), ((αe c k : K) : K ⧸ NK) = (k : K ⧸ NK) := by
    intro c k
    rcases hzp c c.2 with hc | hc
    · have hc1 : c = 1 := Subtype.ext hc
      rw [hc1, map_one]
      rfl
    · rw [eq_comm, QuotientGroup.eq]
      show (k : G)⁻¹ * ((αe c k : K) : G) ∈ N
      rw [hαe, hc, heinv]
      have h1 := hKe k k.2
      rw [heinv] at h1
      rwa [show (k : G)⁻¹ * (e * k * e) = (k : G)⁻¹ * e * k * e by group]
  have hfixK : UnbalancedGS.actionFixedSubgroup αe = (centralizer ({e} : Set G)).subgroupOf K := by
    ext k
    rw [UnbalancedGS.mem_actionFixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 := congrArg Subtype.val (h1 ⟨e, mem_zpowers e⟩)
      rw [hαe] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    · intro h1 c
      apply Subtype.ext
      rw [hαe]
      rcases hzp c c.2 with hc | hc
      · rw [hc]
        group
      · rw [hc, ← h1, mul_inv_cancel_right]
  set VK := (pLayer ↥(UnbalancedGS.actionFixedSubgroup αe) 2).map
    (UnbalancedGS.actionFixedSubgroup αe).subtype with hVKdef
  obtain ⟨-, -, -, hgen, -⟩ := UnbalancedGS.core_trivial_fixed_layer_normal_generation
    Nat.prime_two NK hNKodd hAe αe hαQ hEQ VK rfl
  have hVKmap : VK.map K.subtype = UnbalancedGS.gsFixedLayer K e := by
    rw [hVKdef, hfixK]
    exact map_pLayer_subgroupOf_eq K _
  have hW'fix : W.subgroupOf K ≤ UnbalancedGS.actionFixedSubgroup αe := by
    rw [hfixK]
    exact fun y hy => hWe hy
  have hW'gen : W.subgroupOf K =
      closure {x : K | x ∈ W.subgroupOf K ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
    apply le_antisymm _ ((closure_le _).mpr fun x hx => hx.1)
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWK, MonoidHom.map_closure]
    calc W = closure {x : G | x ∈ W ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := hWgen
      _ ≤ _ := by
        apply Subgroup.closure_mono
        rintro x ⟨hxW, k, hk⟩
        refine ⟨⟨x, hWK hxW⟩, ⟨hxW, k, ?_⟩, rfl⟩
        rw [← Subgroup.orderOf_coe]
        exact hk
  have hW'nc : normalClosure (((W.subgroupOf K).map (QuotientGroup.mk' NK) : Subgroup (K ⧸ NK)) :
      Set (K ⧸ NK)) = ⊤ := by
    rw [coe_map, ← map_normalClosure _ _ (QuotientGroup.mk'_surjective NK), hnc,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective NK)]
  obtain ⟨hWVK, hncVK⟩ := hgen (W.subgroupOf K) hW'fix hW'gen hW'nc
  have hWV : W ≤ UnbalancedGS.gsFixedLayer K e := by
    rw [← hVKmap, ← map_subgroupOf_eq_of_le hWK]
    exact map_mono hWVK
  have hncV := normalClosure_subgroupOf_map (W := W) VK hncVK
  rw [hVKmap] at hncV
  exact ⟨le_inf hWT hWU, hWsupT, hWmulT, hWsupU, hWmulU, hWV, hncV⟩

end CFSG.ComponentClassification.UnbalancedCorr
