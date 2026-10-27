module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolPiece
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem two_layer_orbit_of_sq_central {t : H} (ht2 : IsPGroup 2 (zpowers t))
    (htc : ∀ x : H, t ^ 2 * x = x * t ^ 2) {T : Subgroup H}
    (hTC : T ≤ centralizer ({t} : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer ({t} : Set H)))) (hTE : T ≤ pLayer H 2) :
    ∃ M : Subgroup H, IsPComponent 2 M ∧ T ≤ M ⊔ conjugate M t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRodd : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have : Fact (IsPGroup 2 ↥(zpowers t)) := ⟨ht2⟩
  have hCmap : (centralizer ({t} : Set H)).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)) := by
    have h1 := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (zpowers t) (pPrimeCore 2 H)
      pPrimeCore_normal pPrimeCore_coprime_card
    simp only at h1
    rw [MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure, zpowers_eq_closure,
      centralizer_closure] at h1
    exact h1.symm
  have hTperf : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hT
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hTbC : T.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)) := by
    rw [← hCmap]
    exact map_mono hTC
  let f : centralizer ({t} : Set H) →*
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)) :=
    ((QuotientGroup.mk' (pPrimeCore 2 H)).comp (centralizer ({t} : Set H)).subtype).codRestrict _
      fun c => by
        rw [← hCmap]
        exact mem_map_of_mem _ c.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    have hq' := hq
    rw [← hCmap] at hq'
    obtain ⟨c, hc, hcq⟩ := hq'
    exact ⟨⟨c, hc⟩, Subtype.ext hcq⟩
  have hmemR : ∀ x : f.ker, ((x : centralizer ({t} : Set H)) : H) ∈ pPrimeCore 2 H := by
    intro x
    have h : QuotientGroup.mk' (pPrimeCore 2 H) ((x : centralizer ({t} : Set H)) : H) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hfker : ¬ 2 ∣ Nat.card f.ker := by
    let ι : f.ker →* pPrimeCore 2 H :=
      { toFun := fun x => ⟨_, hmemR x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      have h' : ((ι x : pPrimeCore 2 H) : H) = ((ι y : pPrimeCore 2 H) : H) :=
        congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    intro h2
    exact (Nat.not_even_iff_odd.mpr hRodd)
      (even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_injective ι hι)))
  have hTb : IsPComponent 2 ((T.map (QuotientGroup.mk' (pPrimeCore 2 H))).subgroupOf
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)))) := by
    have h := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hf
      hfker).1.mapsTo hT
    have heq : (T.subgroupOf (centralizer ({t} : Set H))).map f =
        (T.map (QuotientGroup.mk' (pPrimeCore 2 H))).subgroupOf
          (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H))) := by
      ext q
      rw [mem_map, mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, mem_subgroupOf.mp hc, rfl⟩
      · rintro ⟨x, hx, hxq⟩
        exact ⟨⟨x, hTC hx⟩, mem_subgroupOf.mpr hx, Subtype.ext hxq⟩
    rw [← heq]
    exact h
  have hTbE : T.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ layer (H ⧸ pPrimeCore 2 H) := by
    rw [map_le_iff_le_comap]
    refine hTE.trans (sSup_le fun L hL => ?_)
    rw [← map_le_iff_le_comap]
    obtain ⟨K, hK, -, hLK, -⟩ := hL
    rw [hLK]
    exact component_le_layer hK
  obtain ⟨Mb, hMb, hTK0, -, -⟩ :=
    ordinary_layer_local_prime_component_orbit_location Nat.prime_two hTbC hTb hTbE
  set tb := QuotientGroup.mk' (pPrimeCore 2 H) t with htb
  have htbc : ∀ x : H ⧸ pPrimeCore 2 H, tb ^ 2 * x = x * tb ^ 2 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) x
    rw [htb, ← map_pow, ← map_mul, ← map_mul, htc y]
  have hconj2 : ∀ k : ℕ, conjugate Mb (tb ^ (2 * k)) = Mb := by
    intro k
    ext x
    rw [mem_conjugate_iff, pow_mul]
    have h1 : (tb ^ 2) ^ k * x * ((tb ^ 2) ^ k)⁻¹ = x := by
      have hc : Commute ((tb ^ 2) ^ k) x := by
        refine Commute.pow_left ?_ k
        exact htbc x
      rw [hc.eq, mul_inv_cancel_right]
    rw [h1]
  have hTK : T.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ Mb ⊔ conjugate Mb tb := by
    refine hTK0.trans (iSup_le fun i => ?_)
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (i : ℕ)
    · rw [hk, hconj2 k]
      exact le_sup_left
    · rw [hk, pow_succ, ← conjugate_conjugate, hconj2 k]
      exact le_sup_right
  obtain ⟨M, hM, hMb'⟩ : ∃ M : Subgroup H, IsPComponent 2 M ∧
      M.map (QuotientGroup.mk' (pPrimeCore 2 H)) = Mb :=
    ⟨_, CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 Mb hMb⟩
  have hMt := isPComponent_conjugate hM t
  have hKmap : (M ⊔ conjugate M t).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      Mb ⊔ conjugate Mb (QuotientGroup.mk' (pPrimeCore 2 H) t) := by
    rw [Subgroup.map_sup, map_conjugate, hMb']
  have hRK : pPrimeCore 2 H ≤ normalizer ((M ⊔ conjugate M t : Subgroup H) : Set H) := by
    intro n hn
    have h := mem_normalizer_sSup (S := {M, conjugate M t}) (g := n) (by
      intro N hN
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
      rcases hN with hN | hN <;> rw [hN]
      · exact pPrimeCore_le_normalizer hM hn
      · exact pPrimeCore_le_normalizer hMt hn)
    rwa [sSup_pair] at h
  have hTKR : T ≤ (M ⊔ conjugate M t) ⊔ pPrimeCore 2 H := by
    have h2 : T ≤ ((M ⊔ conjugate M t).map (QuotientGroup.mk' (pPrimeCore 2 H))).comap
        (QuotientGroup.mk' (pPrimeCore 2 H)) :=
      (le_comap_map (QuotientGroup.mk' (pPrimeCore 2 H)) T).trans
        (comap_mono (hTK.trans hKmap.symm.le))
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hTK' := le_of_perfect_le_sup_of_odd hRodd hRK hTperf hTKR
  exact ⟨M, hM, hTK'⟩

end CFSG.ComponentClassification.UnbalancedLayer

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_conjugate {H : Subgroup G} (M : Subgroup ↥H) (s : ↥H) :
    (conjugate M s).map H.subtype = conjugate (M.map H.subtype) (s : G) := by
  ext x
  rw [UnbalancedLayer.mem_conjugate_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, UnbalancedLayer.mem_conjugate_iff] at hy
    exact ⟨_, hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : G) = s * x * s⁻¹ := hyx
    have hxH : x ∈ H := by
      have h1 : x = (s : G)⁻¹ * y * s := by rw [hyx']; simp [mul_assoc]
      rw [h1]
      exact mul_mem (mul_mem (inv_mem s.2) y.2) s.2
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, UnbalancedLayer.mem_conjugate_iff]
    have : s * ⟨x, hxH⟩ * s⁻¹ = y := Subtype.ext (by simp [hyx'])
    rw [this]
    exact hy

theorem exists_orbit_of_sq {X Y : Subgroup G} {s : G} (hsX : s ∈ normalizer (X : Set G))
    (hs2 : IsPGroup 2 (zpowers s)) (hs2c : ∀ x ∈ X, s ^ 2 * x = x * s ^ 2)
    (hY : IsTwoComponentIn Y (X ⊓ centralizer ({s} : Set G))) (hYL : Y ≤ twoLayerIn X) :
    ∃ M : Subgroup G, IsTwoComponentIn M X ∧ Y ≤ M ⊔ conjugate M s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ := X ⊔ zpowers s with hH₀
  have hXH₀ : X ≤ H₀ := le_sup_left
  have hsH₀ : s ∈ H₀ := mem_sup_right (mem_zpowers s)
  have hH₀N : H₀ ≤ normalizer (X : Set G) := sup_le le_normalizer (zpowers_le.mpr hsX)
  have hXn : (X.subgroupOf H₀).Normal := (normal_subgroupOf_iff_le_normalizer hXH₀).mpr hH₀N
  set s₀ : ↥H₀ := ⟨s, hsH₀⟩ with hs₀
  have hzs : zpowers s₀ = (zpowers s).subgroupOf H₀ := by
    rw [← comap_subtype, show zpowers s = (zpowers s₀).map H₀.subtype by
      rw [MonoidHom.map_zpowers]; rfl, comap_map_eq_self_of_injective H₀.subtype_injective]
  have hs₀2 : IsPGroup 2 (zpowers s₀) := by rw [hzs]; exact hs2.comap_subtype
  have hs₀c : ∀ x : ↥H₀, s₀ ^ 2 * x = x * s₀ ^ 2 := by
    have hle : H₀ ≤ centralizer ({s ^ 2} : Set G) := by
      refine sup_le (fun x hx => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact (hs2c x hx).symm
      · rw [mem_centralizer_singleton_iff]
        exact ((Commute.refl s).pow_right 2).eq
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hle x.2)).symm
  set T := Y.subgroupOf H₀ with hT
  have hYH₀ : Y ≤ H₀ := hY.1.trans (inf_le_left.trans hXH₀)
  have hTC : T ≤ centralizer ({s₀} : Set ↥H₀) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have h1 := (mem_inf.mp (hY.1 (mem_subgroupOf.mp hy))).2
    exact Subtype.ext (mem_centralizer_singleton_iff.mp h1)
  have hYc : IsPComponent 2 (Y.subgroupOf (centralizer ({s} : Set G) ⊓ H₀)) := by
    have hNH : X ⊓ centralizer ({s} : Set G) ≤ centralizer ({s} : Set G) ⊓ H₀ :=
      le_inf inf_le_right (inf_le_left.trans hXH₀)
    refine GrSLit.isPComponent_subgroupOf_of_isSubnormal hY.1 hNH ?_ hY.2
    refine Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hNH).mpr ?_)
    intro h hh
    obtain ⟨hhs, hhH⟩ := mem_inf.mp hh
    exact Sol76.mem_normalizer_inf (hH₀N hhH) (le_normalizer hhs)
  have hT' : IsPComponent 2 (T.subgroupOf (centralizer ({s₀} : Set ↥H₀))) := by
    rw [UGSChain.centralizer_mk_eq_subgroupOf hsH₀,
      UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
    exact hYc
  have hTE : T ≤ pLayer ↥H₀ 2 := by
    have h1 : twoLayerIn X ≤ twoLayerIn H₀ :=
      GrSLit.pLayer_map_le_of_isSubnormal hXH₀ hXn.isSubnormal
    intro y hy
    obtain ⟨z, hz, hzy⟩ := h1 (hYL (mem_subgroupOf.mp hy))
    rwa [← Subtype.ext hzy]
  obtain ⟨M', hM', hTM'⟩ := UnbalancedLayer.two_layer_orbit_of_sq_central hs₀2 hs₀c hTC hT' hTE
  set M := M'.map H₀.subtype with hM
  have hMsub : M.subgroupOf H₀ = M' := by
    rw [hM, ← comap_subtype, comap_map_eq_self_of_injective H₀.subtype_injective]
  have hMH₀ : M ≤ twoLayerIn H₀ := map_mono (le_sSup hM')
  have hL : twoLayerIn H₀ ≤ twoLayerIn X :=
    GrSLit.pLayer_map_le_of_le_sup hXH₀ le_rfl hs2 (zpowers_le.mpr hsX)
  have hMX : M ≤ X := (hMH₀.trans hL).trans (map_subtype_le _)
  refine ⟨M, ⟨hMX, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hMX hXH₀
    (by rw [hMsub]; exact hM')⟩, ?_⟩
  have h1 := map_mono (f := H₀.subtype) hTM'
  rw [Subgroup.map_sup, map_subtype_conjugate, ← hM, hT, map_subgroupOf_eq_of_le hYH₀] at h1
  exact h1

omit [Finite G] in
theorem centralizer_sup_eq (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  ext x
  constructor
  · intro hx
    have hA : (A : Set G) ⊆ ((A ⊔ B : Subgroup G) : Set G) := fun a ha => mem_sup_left ha
    have hB : (B : Set G) ⊆ ((A ⊔ B : Subgroup G) : Set G) := fun b hb => mem_sup_right hb
    exact mem_inf.mpr ⟨centralizer_le hA hx, centralizer_le hB hx⟩
  · intro hx
    obtain ⟨hxA, hxB⟩ := mem_inf.mp hx
    have hle : A ⊔ B ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp hxA) a ha)
      · rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp hxB) b hb)
    rw [mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hle hy)

theorem orbit_of_isPGroup {H R : Subgroup G} (hRH : R ≤ H) (hR2 : IsPGroup 2 R) :
    ∀ Y : Subgroup G, IsTwoComponentIn Y (H ⊓ centralizer (R : Set G)) → Y ≤ twoLayerIn H →
      ∃ M₀ : Subgroup G, IsTwoComponentIn M₀ H ∧ ∀ M : Subgroup G, IsTwoComponentIn M H →
        ¬ Y ≤ coreActionKernel M → ∃ g ∈ R, M = conjugate M₀ g := by
  classical
  let C : Subgroup G → Prop := fun A => ∀ Y : Subgroup G,
    IsTwoComponentIn Y (H ⊓ centralizer (A : Set G)) → Y ≤ twoLayerIn H →
      ∃ M₀ : Subgroup G, IsTwoComponentIn M₀ H ∧ ∀ M : Subgroup G, IsTwoComponentIn M H →
        ¬ Y ≤ coreActionKernel M → ∃ g ∈ A, M = conjugate M₀ g
  have hbot : C ⊥ := by
    intro Y hY _
    have h1 : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => mem_centralizer_iff.mpr fun y hy => ?_
      rw [SetLike.mem_coe, mem_bot] at hy
      rw [hy, one_mul, mul_one]
    rw [h1, inf_top_eq] at hY
    refine ⟨Y, hY, fun M hM hmv => ⟨1, one_mem _, ?_⟩⟩
    rw [UnbalancedLayer.conjugate_one]
    by_contra hne
    exact hmv (le_coreActionKernel_of_ne hM hY hne)
  have hstep : ∀ (A : Subgroup G) (s : G), A ≤ R → s ∈ R → s ∈ normalizer (A : Set G) →
      s ^ 2 ∈ A → C A → C (A ⊔ zpowers s) := by
    intro A s hAR hsR hsN hs2 hC Y hY hYL
    set X := H ⊓ centralizer (A : Set G) with hX
    have hYX : IsTwoComponentIn Y (X ⊓ centralizer ({s} : Set G)) := by
      rw [centralizer_sup_eq, centralizer_zpowers', ← inf_assoc] at hY
      exact hY
    have hsH : s ∈ H := hRH hsR
    have hsXN : s ∈ normalizer (X : Set G) :=
      Sol76.mem_normalizer_inf (le_normalizer hsH)
        (Sol76.le_normalizer_centralizer (zpowers_le.mpr hsN) (mem_zpowers s))
    have hs2c : ∀ x ∈ X, s ^ 2 * x = x * s ^ 2 := fun x hx =>
      ((mem_centralizer_iff.mp (mem_inf.mp hx).2) _ hs2)
    have hs2' : IsPGroup 2 (zpowers s) := hR2.to_le (zpowers_le.mpr hsR)
    have hYLX : Y ≤ twoLayerIn X := by
      have h1 := GrSLit.pLayer_inf_centralizer_le_of_normalizes (Q := X) (A := zpowers s) hs2'
        (zpowers_le.mpr hsXN)
      rw [centralizer_zpowers'] at h1
      exact (le_twoLayerIn_of_isTwoComponentIn hYX).trans h1
    obtain ⟨M₁, hM₁, hYM₁⟩ := exists_orbit_of_sq hsXN hs2' hs2c hYX hYLX
    have hM₁L : M₁ ≤ twoLayerIn H := by
      have h1 := GrSLit.pLayer_inf_centralizer_le (Y := H) (A := A) (hAR.trans hRH)
        (hR2.to_le hAR)
      exact (le_twoLayerIn_of_isTwoComponentIn hM₁).trans h1
    obtain ⟨M₀, hM₀, horb⟩ := hC M₁ hM₁ hM₁L
    refine ⟨M₀, hM₀, fun M hM hmv => ?_⟩
    by_cases h1 : M₁ ≤ coreActionKernel M
    · have h2 : ¬ conjugate M₁ s ≤ coreActionKernel M := fun h2 =>
        hmv (hYM₁.trans (sup_le h1 h2))
      set M' := conjugate M s⁻¹ with hM'def
      have hM'M : conjugate M' s = M := by
        rw [hM'def, UnbalancedLayer.conjugate_conjugate, inv_mul_cancel,
          UnbalancedLayer.conjugate_one]
      have hM' : IsTwoComponentIn M' H := by
        have h3 := Sol76.isTwoComponentIn_map (MulAut.conj s) hM
        have h4 : H.map (MulAut.conj s).toMonoidHom = H :=
          mem_normalizer_iff_map_conj_eq.mp (le_normalizer hsH)
        rw [h4] at h3
        have h5 : M' = M.map (MulAut.conj s).toMonoidHom := by
          rw [hM'def]; unfold conjugate; rw [inv_inv]
        rw [h5]
        exact h3
      have hmv' : ¬ M₁ ≤ coreActionKernel M' := by
        intro h3
        apply h2
        have h4 := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) h3
        rw [Sol76.map_coreActionKernel (MulAut.conj s⁻¹) M'] at h4
        have h5 : M'.map (MulAut.conj s⁻¹).toMonoidHom = M := hM'M
        rw [h5] at h4
        exact h4
      obtain ⟨g, hgA, hg⟩ := horb M' hM' hmv'
      refine ⟨g * s, mul_mem (mem_sup_left hgA) (mem_sup_right (mem_zpowers s)), ?_⟩
      rw [← UnbalancedLayer.conjugate_conjugate, ← hg, hM'M]
    · obtain ⟨g, hgA, hg⟩ := horb M hM h1
      exact ⟨g, mem_sup_left hgA, hg⟩
  have key : ∀ n : ℕ, ∀ A : Subgroup G, Nat.card R - Nat.card A = n → A ≤ R → C A → C R := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hn hAR hCA
      by_cases hAR' : A = R
      · rw [← hAR']; exact hCA
      obtain ⟨s, hsR, hsN, hsA, hs2⟩ := exists_sq_mem_of_ne hR2 hAR hAR'
      have hA'R : A ⊔ zpowers s ≤ R := sup_le hAR (zpowers_le.mpr hsR)
      have hAA' : A < A ⊔ zpowers s := lt_of_le_of_ne le_sup_left fun h =>
        hsA (h ▸ mem_sup_right (mem_zpowers s))
      have hcard : Nat.card A < Nat.card ↥(A ⊔ zpowers s) := Subgroup.card_lt_of_lt hAA'
      have hcardR : Nat.card ↥(A ⊔ zpowers s) ≤ Nat.card R := card_le_of_le hA'R
      exact ih _ (by omega) _ rfl hA'R (hstep A s hAR hsR hsN hs2 hCA)
  exact key _ ⊥ rfl bot_le hbot

end CFSG.ComponentClassification.Foote5.SolMax
