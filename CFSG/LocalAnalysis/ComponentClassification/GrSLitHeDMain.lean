module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUVert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace HeDM

theorem isElemTwo_of_isFourGroup {X : Type*} [Group X] {U : Subgroup X} (hU : IsFourGroup U) :
    IsElemTwo U ∧ Nat.card U = 4 := by
  obtain ⟨φ⟩ := hU
  have hsq : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
  have hcm : ∀ y z : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * z = z * y := by
    decide
  refine ⟨⟨fun x hx y hy => ?_, fun x hx => ?_⟩, ?_⟩
  · have h : φ ⟨x, hx⟩ * φ ⟨y, hy⟩ = φ ⟨y, hy⟩ * φ ⟨x, hx⟩ := hcm _ _
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (φ.injective h)
  · have h : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := hsq _
    rw [← map_mul, MulEquiv.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  · rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    simp

theorem gsFixedLayer_subgroupOf {G : Type} [Group G] [Finite G] {C K : Subgroup G} {a : G}
    (haC : a ∈ C) (hKC : K ≤ C) :
    gsFixedLayer (K.subgroupOf C) ⟨a, haC⟩ = (gsFixedLayer K a).subgroupOf C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := K ⊓ centralizer ({a} : Set G) with hS
  set S' := K.subgroupOf C ⊓ centralizer ({(⟨a, haC⟩ : C)} : Set C) with hS'
  have hSS : S' = S.subgroupOf C := by
    ext y
    rw [mem_inf, mem_subgroupOf, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨h.1, congrArg Subtype.val h.2⟩, fun h => ⟨h.1, Subtype.ext h.2⟩⟩
  let ψ : ↥S' ≃* ↥S :=
    (MulEquiv.subgroupCongr hSS).trans (subgroupOfEquivOfLe (inf_le_left.trans hKC))
  have hP := FixedLayerPComponent.map_pLayer_mulEquiv 2 ψ
  have hcomp : S.subtype.comp ψ.toMonoidHom = C.subtype.comp S'.subtype := by
    ext x
    rfl
  show (pLayer ↥S' 2).map S'.subtype = ((pLayer ↥S 2).map S.subtype).subgroupOf C
  rw [← hP, map_map, hcomp, ← map_map]
  exact (comap_map_eq_self_of_injective C.subtype_injective _).symm

theorem isPComponent_map {H : Type} [Group H] [Finite H] {M : Subgroup H}
    (hM : IsPComponent 2 M) : IsPComponent 2 (M.map (QuotientGroup.mk' (pPrimeCore 2 H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := GSThmB.OddQuot.isPComponent_map (QuotientGroup.mk' (pPrimeCore 2 H))
    GSThmB.OddQuot.not_two_dvd_card_ker (X := ⊤) le_top
    (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hM le_top)
  rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  exact (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 _ ⊤ le_top
    IsSubnormal.top).mp h

theorem fixedLayer_zpowers {G : Type} [Group G] (J : Subgroup G) (g : G) :
    GSLit.fixedLayer J (zpowers g) = gsFixedLayer J g := by
  unfold GSLit.fixedLayer gsFixedLayer
  rw [centralizer_zpowers_eq]

theorem central_of_trivial_meet
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldSetting X L)
    (hW : ∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥)
    {a u : X} {U T M : Subgroup X} (ha : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set X))
    (hUL : U ≤ L) (hUf : IsFourGroup U) (hu : u ∈ U) (hu1 : u ≠ 1) (hTL : T ≤ L)
    (hTau : T ≤ centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))
    (hTp : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set X) ⊓ centralizer ({u} : Set X))))
    (hUT : U ≤ (Open.fusionZStar ↥T).map T.subtype)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = T)
    (hI : M ⊓ (conjugate M a ⊔ (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map
          (centralizer ({u} : Set X)).subtype) ≤
        (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype) :
    ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimp, hnab, hK, -, hLB, -, ⟨e⟩⟩ := id hset
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  obtain ⟨hUe, hU4⟩ := isElemTwo_of_isFourGroup hUf
  have huu : u * u = 1 := hUe.2 u hu
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have hau : a * u = u * a := (mem_centralizer_singleton_iff.mp (hLa (hUL hu))).symm
  have hZX : ∀ x : X, x ≠ 1 → centralizer ({x} : Set X) ≠ ⊤ := by
    intro x hx htop
    have hcen : center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
      · exact h
      · exfalso
        obtain ⟨y, z, hyz⟩ := hnab
        have hy : y ∈ center X := h ▸ mem_top y
        exact hyz (mem_center_iff.mp hy z).symm
    have hxc : x ∈ center X := mem_center_iff.mpr fun g =>
      (mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({x} : Set X)))
    rw [hcen, mem_bot] at hxc
    exact hx hxc
  obtain ⟨B, hBT, hBe, hB8⟩ := HeDB.exists_eight_le hLa e (hUL hu) huu hu1 hTL hTau hTp
  set C := centralizer ({u} : Set X) with hC
  set N := conjugate M a with hN
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hau
  obtain ⟨hNu, hNp⟩ := UGSChain.conjugate_isPComponent_centralizer hau hMu hMp
  have hTC : T ≤ C := hTau.trans inf_le_right
  have hUT' : U ≤ T := fun x hx => by
    obtain ⟨t, -, rfl⟩ := hUT hx
    exact t.2
  have hBC : B ≤ C := hBT.trans hTC
  set a' : ↥C := ⟨a, haC⟩ with ha'
  have ha'a' : a' * a' = 1 := Subtype.ext haa
  set M' := M.subgroupOf C with hM'
  set N' := N.subgroupOf C with hN'
  have hM'N' : ∀ m ∈ M', a' * m * a'⁻¹ ∈ N' := by
    intro m hm
    show a * (m : X) * a⁻¹ ∈ N
    rw [hN, UnbalancedLayer.mem_conjugate_iff,
      show a * (a * (m : X) * a⁻¹) * a⁻¹ = (a * a) * m * (a * a)⁻¹ by group, haa]
    simpa using mem_subgroupOf.mp hm
  have hN'M' : ∀ n ∈ N', a' * n * a'⁻¹ ∈ M' := fun n hn => by
    show a * (n : X) * a⁻¹ ∈ M
    exact UnbalancedLayer.mem_conjugate_iff.mp (mem_subgroupOf.mp hn)
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set A := M'.map π with hA
  set Bq := N'.map π with hBq
  set α := π a' with hα
  have hOQ : pPrimeCore 2 (↥C ⧸ pPrimeCore 2 ↥C) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hAp : IsPComponent 2 A := isPComponent_map hMp
  have hBp : IsPComponent 2 Bq := isPComponent_map hNp
  have hAc := HeldFix.isComponent_of_isPComponent hOQ hAp
  have hBc := HeldFix.isComponent_of_isPComponent hOQ hBp
  have hAB : A ≠ Bq := by
    intro h
    have h1 : M' = N' := GSThmB.OddQuot.eq_of_map_eq π GSThmB.OddQuot.not_two_dvd_card_ker
      (X := ⊤) le_top le_top (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hMp le_top)
      (CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 hNp le_top) h
    apply hne
    rw [hM', hN', subgroupOf_inj, inf_of_le_left hMu, inf_of_le_left hNu] at h1
    exact h1.symm
  have hcomm : ∀ x ∈ A, ∀ y ∈ Bq, x * y = y * x := by
    rcases LocalCores.distinct_components_commute hAc hBc with h | h
    · exact absurd h hAB
    · intro x hx y hy
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ ⁅A, Bq⁆ := commutator_mem_commutator hx hy
      rw [h, mem_bot] at hmem
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [hmem, one_mul]
  have hAB1 : A ⊓ Bq = ⊥ := by
    rw [eq_bot_iff]
    rintro q ⟨⟨m, hm, rfl⟩, ⟨n, hn, hnm⟩⟩
    have ho : n⁻¹ * m ∈ pPrimeCore 2 ↥C := by
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥C), MonoidHom.mem_ker, map_mul, map_inv, hnm,
        inv_mul_cancel]
    have hmX : (m : X) ∈ M ⊓ (N ⊔ (pPrimeCore 2 ↥C).map C.subtype) := by
      refine mem_inf.mpr ⟨hm, ?_⟩
      have h1 : (m : X) = (n : X) * ((n⁻¹ * m : ↥C) : X) := by simp
      rw [h1]
      exact mul_mem (mem_sup_left hn) (mem_sup_right ⟨_, ho, rfl⟩)
    obtain ⟨o, ho', hoe⟩ := hI hmX
    have h2 : o = m := Subtype.ext hoe
    rw [mem_bot, ← h2]
    exact (QuotientGroup.eq_one_iff _).mpr ho'
  have hαA : ∀ x ∈ A, α * x * α⁻¹ ∈ Bq := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨a' * m * a'⁻¹, hM'N' m hm, by simp [hα]⟩
  have hαB : ∀ y ∈ Bq, α * y * α⁻¹ ∈ A := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨a' * n * a'⁻¹, hN'M' n hn, by simp [hα]⟩
  have hαα : α * α = 1 := by rw [hα, ← map_mul, ha'a', map_one]
  have hAq : IsQuasisimple ↥A := hAc.1
  have hAO : pPrimeCore 2 ↥A = ⊥ := HeldFix.pPrimeCore_eq_bot_of_isPComponent hOQ hAp
  set T' := T.subgroupOf C with hT'
  have hKC : M ⊔ N ≤ C := sup_le hMu hNu
  have hK' : (M ⊔ N).subgroupOf C = M' ⊔ N' := subgroupOf_sup hMu hNu
  have hT'eq : gsFixedLayer (M' ⊔ N') a' = T' := by
    rw [← hK', gsFixedLayer_subgroupOf haC hKC, hfix]
  have hE2 : IsPGroup 2 (zpowers a') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha'a') (fun h => by
      have := congrArg Subtype.val h
      simp only [ha', OneMemClass.coe_one] at this
      rw [this, orderOf_one] at ha
      norm_num at ha)
  have hEN : zpowers a' ≤ normalizer ((M' ⊔ N' : Subgroup ↥C) : Set ↥C) := by
    have hle : ∀ y ∈ M' ⊔ N', a' * y * a'⁻¹ ∈ M' ⊔ N' := by
      have h : M' ⊔ N' ≤ (M' ⊔ N').comap (MulAut.conj a').toMonoidHom :=
        sup_le (fun m hm => mem_sup_right (hM'N' m hm)) (fun n hn => mem_sup_left (hN'M' n hn))
      intro y hy
      exact h hy
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    refine ⟨hle y, fun h => ?_⟩
    have h1 := hle _ h
    rwa [show a' * (a' * y * a'⁻¹) * a'⁻¹ = (a' * a') * y * (a' * a')⁻¹ by group, ha'a',
      one_mul, inv_one, mul_one] at h1
  have hTb : T'.map π = gsFixedLayer (A ⊔ Bq) α := by
    have h := GSThmB.OddQuot.map_fixedLayer hE2 hEN
    rw [fixedLayer_zpowers, hT'eq, Subgroup.map_sup, MonoidHom.map_zpowers,
      fixedLayer_zpowers] at h
    exact h
  set U' := U.subgroupOf C with hU'
  set V := U'.map π with hV
  have hU'T : U' ≤ (Open.fusionZStar ↥T').map T'.subtype := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hUT (show (y : X) ∈ U from hy)
    let ψ : ↥T' ≃* ↥T := subgroupOfEquivOfLe hTC
    have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective ψ.toMonoidHom ψ.surjective
      (by rw [show ψ.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr ψ.injective,
        card_bot]; norm_num)
    refine ⟨ψ.symm t, ?_, ?_⟩
    · rw [← hcomap]
      show ψ (ψ.symm t) ∈ Open.fusionZStar ↥T
      rw [MulEquiv.apply_symm_apply]
      exact ht
    · apply Subtype.ext
      exact hty
  have hV' : V ≤ (Open.fusionZStar ↥(T'.map π)).map (T'.map π).subtype := by
    let f : ↥T' →* ↥(T'.map π) := (π.comp T'.subtype).codRestrict _ fun t =>
      mem_map_of_mem π t.2
    have hf : Function.Surjective f := by
      rintro ⟨q, t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    have hfk : ¬ 2 ∣ Nat.card f.ker := by
      let g : f.ker →* pPrimeCore 2 ↥C :=
        (T'.subtype.comp f.ker.subtype).codRestrict (pPrimeCore 2 ↥C) fun k => by
          have h1 : f (k : T') = 1 := k.2
          exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      have hg : Function.Injective g := fun k₁ k₂ h => by
        have h' := congrArg (fun x : pPrimeCore 2 ↥C => (x : ↥C)) h
        exact Subtype.ext (Subtype.ext h')
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥C)) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)) ∘
        even_iff_two_dvd.mpr
    have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hfk
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hty⟩ := hU'T hy
    refine ⟨f t, ?_, ?_⟩
    · rw [← hcomap] at ht
      exact ht
    · rw [← hty]
      rfl
  rw [hTb] at hV'
  have hU'e : IsElemTwo U' :=
    ⟨fun x hx y hy => Subtype.ext (hUe.1 _ hx _ hy), fun x hx => Subtype.ext (hUe.2 _ hx)⟩
  have hVe : IsElemTwo V := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hU'e.1 x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hU'e.2 x hx, map_one]
  have hV4 : Nat.card V = 4 := by
    rw [hV, GSThmB.OddQuot.card_map_of_isPGroup hU'e.isPGroup, hU',
      Nat.card_congr (subgroupOfEquivOfLe (hUT'.trans hTC)).toEquiv, hU4]
  obtain ⟨hVc, x, hxA, hxx, hx1, hxV, hxc⟩ :=
    HeDQ.exists_central_involution hαα hcomm hαA hαB hAB1 hAq hAO hV' hVe hV4
  have hVK : ∀ v ∈ V, v ∈ A ⊔ Bq := by
    intro v hv
    obtain ⟨t, -, rfl⟩ := hV' hv
    exact (mem_inf.mp (gsFixedLayer_le_inf (A ⊔ Bq) α t.2)).1
  set Eb := V ⊔ zpowers x with hEb
  have hEbe : IsElemTwo Eb := hVe.sup (isElemTwo_zpowers hxx) (fun v hv y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute v x from (hxc v (hVK v hv)).symm) i).eq)
  have hEb8 : 8 ≤ Nat.card Eb := by
    have hVE : V ≤ Eb := le_sup_left
    have hne' : V.subgroupOf Eb ≠ ⊤ := by
      intro h
      have hmem : (⟨x, mem_sup_right (mem_zpowers x)⟩ : Eb) ∈ V.subgroupOf Eb := h ▸ mem_top _
      exact hxV hmem
    have hidx : 2 ≤ (V.subgroupOf Eb).index := by
      have h1 : (V.subgroupOf Eb).index ≠ 1 := fun h => hne' (index_eq_one.mp h)
      have h0 : (V.subgroupOf Eb).index ≠ 0 := index_ne_zero_of_finite
      omega
    have hcard := card_mul_index (V.subgroupOf Eb)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVE).toEquiv, hV4] at hcard
    omega
  have hEbc : ∀ e' ∈ Eb, ∀ g ∈ A ⊔ Bq, e' * g = g * e' := by
    have h : Eb ≤ centralizer ((A ⊔ Bq : Subgroup _) : Set (↥C ⧸ pPrimeCore 2 ↥C)) := by
      refine sup_le (fun v hv => mem_centralizer_iff.mpr fun g hg => (hVc v hv g hg).symm) ?_
      rw [zpowers_le]
      exact mem_centralizer_iff.mpr fun g hg => (hxc g hg).symm
    intro e' he' g hg
    exact ((mem_centralizer_iff.mp (h he')) g hg).symm
  set B' := B.subgroupOf C with hB'
  have hB'p : IsPGroup 2 B' := hBe.isPGroup.comap_of_injective C.subtype C.subtype_injective
  have hB'K : ∀ r ∈ B', π r ∈ A ⊔ Bq := by
    intro r hr
    have hTK : T ≤ M ⊔ N := hfix ▸ (gsFixedLayer_le_inf _ _).trans inf_le_left
    have h1 : r ∈ (M ⊔ N).subgroupOf C := mem_subgroupOf.mpr (hTK (hBT (mem_subgroupOf.mp hr)))
    rw [hK'] at h1
    have h2 := mem_map_of_mem π h1
    rwa [Subgroup.map_sup] at h2
  obtain ⟨Z, hZB, hZE, hZe, hZcard⟩ := HeDL.exists_lift_centralizing hB'p hEbe
    (fun r hr e' he' => (hEbc e' he' (π r) (hB'K r hr)).symm)
  have hZM : ∀ z ∈ Z, z ∈ normalizer (M' : Set ↥C) ∧
      ∀ m ∈ M', z * m * z⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M').map M'.subtype := by
    intro z hz
    apply HeDL.normalizes_of_central hMp
    intro m hm
    have hzE : π z ∈ Eb := hZE ▸ mem_map_of_mem π hz
    exact hEbc _ hzE _ (mem_sup_left (mem_map_of_mem π hm))
  set E := Z.map C.subtype with hE
  have hEu : E ≤ C := map_subtype_le _
  have hEe : IsElemTwo E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
      exact congrArg Subtype.val (hZe.1 _ hx₁ _ hy₁)
    · rintro _ ⟨x₁, hx₁, rfl⟩
      exact congrArg Subtype.val (hZe.2 _ hx₁)
  have hE8 : 8 ≤ Nat.card E := by
    rw [hE, card_map_of_injective C.subtype_injective, hZcard]
    exact hEb8
  have hEN : E ≤ normalizer (M : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzN := (hZM z hz).1
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := (mem_normalizer_iff.mp hzN ⟨y, hMu hy⟩).mp (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
    · intro hy
      have hyC : y ∈ C := by
        have h2 := mul_mem (mul_mem (inv_mem z.2) (hMu hy)) z.2
        have h3 : ((z : ↥C) : X)⁻¹ * (C.subtype z * y * (C.subtype z)⁻¹) * z = y := by
          simp only [coe_subtype]
          group
        rwa [h3] at h2
      have h1 := (mem_normalizer_iff.mp hzN ⟨y, hyC⟩).mpr (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp h1
  have hEcen : ∀ e' ∈ E, ∀ l ∈ M, e' * l * e'⁻¹ * l⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
    rintro _ ⟨z, hz, rfl⟩ l hl
    have h1 := (hZM z hz).2 ⟨l, hMu hl⟩ (mem_subgroupOf.mpr hl)
    have h2 := mem_map_of_mem C.subtype h1
    rw [GSThmB.B5a.map_oddCoreIn_subgroupOf C M, inf_of_le_right hMu] at h2
    exact h2
  have hGW := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have hEB : ∀ x₁ ∈ E, ∀ y₁ ∈ B, x₁ * y₁ = y₁ * x₁ := by
    rintro _ ⟨z, hz, rfl⟩ y₁ hy₁
    have h1 := mem_centralizer_iff.mp (hZB hz) ⟨y₁, hBC hy₁⟩ (mem_subgroupOf.mpr hy₁)
    exact (congrArg Subtype.val h1).symm
  have hWB : wGroup B = ⊥ :=
    HeUV.wGroup_eq_bot_of_le hW hBe ((hBT.trans hTL).trans le_normalizer)
  have hWE : wGroup E = ⊥ := by
    rw [wGroup_eq_of_commute hGW (hEe.isAbelianTwoOfRank hE8)
      (hBe.isAbelianTwoOfRank (by omega)) hEB]
    exact hWB
  have hbal : ∀ e' ∈ E, e' ≠ 1 →
      ⁅(pPrimeCore 2 ↥M).map M.subtype ⊓ centralizer ({e'} : Set X),
        (pLayer ↥(M ⊓ centralizer ({e'} : Set X)) 2).map
          (M ⊓ centralizer ({e'} : Set X)).subtype⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({e'} : Set X))).map (centralizer ({e'} : Set X)).subtype :=
    fun e' he' he1 => GrS5.commutator_oddCore_pLayer_le hS hUO hheld hK hu2 hMu hMp
      (mem_centralizer_singleton_iff.mp (hEu he')).symm (hZX e' he1)
  exact oddCore_le_center_of_wGroup_eq_bot hMu hMp hEu hEe.1 hEe.2 (by omega) hEN hEcen hWE
    hbal (Or.inr hE8)

end HeDM

theorem heldUDiagonalStep_of_meet
    (hS : SchreierFor Blueprint.Catalog)
    (hUO : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hMeet : HeldUDiagonalMeetStep) : HeldUDiagonalStep := by
  intro X _ _ L hset hW a u U T M ha hLa hLc hUL hUf hu hu1 hTL hTau hTp htype hUT hMu hMp hne
    hfix
  by_cases hI : M ⊓ (conjugate M a ⊔ (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map
      (centralizer ({u} : Set X)).subtype) ≤
      (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype
  · exact HeDM.central_of_trivial_meet hS hUO hheld hset hW ha hLa hUL hUf hu hu1 hTL hTau hTp
      hUT hMu hMp hne hfix hI
  · exact hMeet X L hset hW a u U T M ha hLa hLc hUL hUf hu hu1 hTL hTau hTp htype hUT hMu hMp
      hne hfix hI

end CFSG.ComponentClassification.GrSLit
