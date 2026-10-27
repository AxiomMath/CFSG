module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.Foundations.GilmanSolomonGrammarChains
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrFusionBridge

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type*} [Group G]

theorem map_centralizer_singleton (φ : G ≃* G) (c : G) :
    (centralizer ({c} : Set G)).map φ.toMonoidHom = centralizer ({φ c} : Set G) := by
  ext z
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hz
    have h1 := congrArg φ hz
    rwa [map_mul, map_mul, φ.apply_symm_apply] at h1
  · intro hz
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hz]

theorem map_map_pPrimeCore (φ : G ≃* G) (J : Subgroup G) :
    ((pPrimeCore 2 J).map J.subtype).map φ.toMonoidHom =
      (pPrimeCore 2 (J.map φ.toMonoidHom)).map (J.map φ.toMonoidHom).subtype := by
  let e : J ≃* J.map φ.toMonoidHom := J.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomm : φ.toMonoidHom.comp J.subtype =
      (J.map φ.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext j
    rfl
  rw [map_map, hcomm, ← map_map, pPrimeCore_map_iso 2 e]

theorem isPComponent_map_centralizer (φ : G ≃* G) {c : G} {J : Subgroup G}
    (hJc : J ≤ centralizer ({c} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({c} : Set G)))) :
    J.map φ.toMonoidHom ≤ centralizer ({φ c} : Set G) ∧
      IsPComponent 2 ((J.map φ.toMonoidHom).subgroupOf (centralizer ({φ c} : Set G))) := by
  have hC := map_centralizer_singleton φ c
  refine ⟨hC ▸ map_mono hJc, ?_⟩
  let ψ : centralizer ({c} : Set G) ≃* centralizer ({φ c} : Set G) :=
    ((centralizer ({c} : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hC)
  have h := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 ψ hJ
  convert h using 1
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj, hjy⟩ := mem_map.mp (mem_subgroupOf.mp hy)
    exact ⟨⟨j, hJc hj⟩, mem_subgroupOf.mpr hj, Subtype.ext hjy⟩
  · rintro ⟨w, hw, rfl⟩
    exact mem_subgroupOf.mpr ⟨w, mem_subgroupOf.mp hw, rfl⟩

variable [Finite G]

theorem map_gsFixedLayer (φ : G ≃* G) (Y : Subgroup G) (t : G) :
    (gsFixedLayer Y t).map φ.toMonoidHom = gsFixedLayer (Y.map φ.toMonoidHom) (φ t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : (Y ⊓ centralizer ({t} : Set G)).map φ.toMonoidHom =
      Y.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G) := by
    rw [map_inf _ _ _ φ.injective, map_centralizer_singleton]
  let ψ : ↥(Y ⊓ centralizer ({t} : Set G)) ≃*
      ↥(Y.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G)) :=
    ((Y ⊓ centralizer ({t} : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hY)
  have hcomm : φ.toMonoidHom.comp (Y ⊓ centralizer ({t} : Set G)).subtype =
      (Y.map φ.toMonoidHom ⊓ centralizer ({φ t} : Set G)).subtype.comp ψ.toMonoidHom := by
    ext y
    rfl
  rw [gsFixedLayer, gsFixedLayer, map_map, hcomm, ← map_map,
    FixedLayerPComponent.map_pLayer_mulEquiv 2 ψ]

theorem gsCorr_map (φ : G ≃* G) {c b : G} {J L : Subgroup G} (h : GSCorr c J b L) :
    GSCorr (φ c) (J.map φ.toMonoidHom) (φ b) (L.map φ.toMonoidHom) := by
  obtain ⟨hc, hb, hcb, hJc, hJ, hLb, hL, hbJ, hJb, hfix⟩ := h
  obtain ⟨hJc', hJ'⟩ := isPComponent_map_centralizer φ hJc hJ
  obtain ⟨hLb', hL'⟩ := isPComponent_map_centralizer φ hLb hL
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hc, by rw [MulEquiv.orderOf_eq]; exact hb,
    by rw [← map_mul, ← map_mul, hcb], hJc', hJ', hLb', hL', ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    rw [mem_map_equiv, mem_map_equiv, map_mul, map_mul, map_inv, φ.symm_apply_apply]
    exact mem_normalizer_iff.mp hbJ _
  · intro j hj
    obtain ⟨j', hj', rfl⟩ := mem_map.mp hj
    rw [← map_map_pPrimeCore]
    refine ⟨j'⁻¹ * b⁻¹ * j' * b, hJb j' hj', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  · rw [← map_gsFixedLayer, hfix, map_gsFixedLayer, Subgroup.map_sup, map_conjugate]
    rfl

theorem gsCorr_conjugate {c b : G} {J L : Subgroup G} (h : GSCorr c J b L) (g : G) :
    GSCorr (g⁻¹ * c * g) (conjugate J g) (g⁻¹ * b * g) (conjugate L g) := by
  have h' := gsCorr_map (MulAut.conj g⁻¹) h
  simp only [MulAut.conj_apply, inv_inv] at h'
  exact h'

omit [Finite G] in
theorem index_pPrimeCore_conjugate (L : Subgroup G) (g : G) :
    (pPrimeCore 2 (conjugate L g)).index = (pPrimeCore 2 L).index := by
  let e : L ≃* conjugate L g :=
    L.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  rw [← pPrimeCore_map_iso 2 e]
  exact index_map_equiv _ e

theorem GSCorr.index_le {a b : G} {J L : Subgroup G} (h : GSCorr a J b L) :
    (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hle, -, -⟩ :=
    commuting_source_change_and_quotient_control h.1 rfl h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h rfl rfl
  exact hle

theorem GSCorr.zStar_of_index_eq {a b : G} {J L : Subgroup G} (h : GSCorr a J b L)
    (heq : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) :
    Nonempty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hiso, -⟩ :=
    commuting_source_change_and_quotient_control h.1 rfl h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h rfl rfl
  exact (hiso (Or.inr heq)).2

theorem GSReach.index_le {J L : Subgroup G} (h : GSReach J L) :
    (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index :=
  (gsReach_iff_grammar.1 h).le fun _ _ _ _ hC => GSCorr.index_le hC

omit [Finite G] in
theorem GSReach.isInvolutionTwoComponent {J L : Subgroup G} (h : GSReach J L) :
    ∃ b : G, orderOf b = 2 ∧ L ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))) :=
  (gsReach_iff_grammar.1 h).vertex_right fun _ _ _ _ hC =>
    (gsCorr_iff_grammar.1 hC).involutionComponent_right

theorem gsMaximalComponent_of_index_le {J : Subgroup G}
    (hJ : ∃ a : G, orderOf a = 2 ∧ J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (h : ∀ L : Subgroup G, GSReach J L → (pPrimeCore 2 L).index ≤ (pPrimeCore 2 J).index) :
    GSMaximalComponent J :=
  gsMaximalComponent_iff_grammar.2 <|
    GSGrammar.maximalComponent_of_le (fun L => (pPrimeCore 2 L).index)
      (fun _ _ _ _ hC => GSCorr.index_le hC)
      (fun _ _ _ _ hC heq => GSCorr.zStar_of_index_eq hC heq) hJ
      fun L hL => h L (gsReach_iff_grammar.2 hL)

omit [Finite G] in
theorem GSMaximalComponent.of_reach {J L : Subgroup G} (hJ : GSMaximalComponent J)
    (hL : GSReach J L) : GSMaximalComponent L :=
  gsMaximalComponent_iff_grammar.2 <|
    (gsMaximalComponent_iff_grammar.1 hJ).of_reach
      (fun _ _ _ _ hC => (gsCorr_iff_grammar.1 hC).involutionComponent_right)
      (gsReach_iff_grammar.1 hL)

theorem gsFixedLayer_eq_self {c : G} {K : Subgroup G} (hKc : K ≤ centralizer ({c} : Set G))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({c} : Set G)))) : gsFixedLayer K c = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hKc).1 hK
  have htop : IsPComponent 2 (K.subgroupOf K) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K K le_rfl).2
      ⟨by rw [subgroupOf_self]; exact Subgroup.IsSubnormal.top, hres, hq⟩
  rw [subgroupOf_self] at htop
  have hlayer : pLayer ↥K 2 = ⊤ :=
    eq_top_iff.mpr (le_sSup (s := {L : Subgroup ↥K | IsPComponent 2 L}) htop)
  unfold gsFixedLayer
  rw [inf_eq_left.mpr hKc, hlayer, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
private theorem conjugate_eq_self_of_le_centralizer {b : G} {K : Subgroup G}
    (hKb : K ≤ centralizer ({b} : Set G)) : conjugate K b = K := by
  have hcomm : ∀ y ∈ K, b * y * b⁻¹ = y := fun y hy => by
    have hc := mem_centralizer_singleton_iff.mp (hKb hy)
    rw [← hc, mul_inv_cancel_right]
  ext y
  rw [mem_conjugate_iff]
  constructor
  · intro hy
    have h1 := hcomm _ hy
    have h2 : b * y * b⁻¹ = y :=
      calc b * y * b⁻¹ = b⁻¹ * (b * (b * y * b⁻¹) * b⁻¹) * b := by group
        _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [h1]
        _ = y := by group
    rwa [h2] at hy
  · intro hy
    rwa [hcomm y hy]

theorem GSCorr.eq_of_eq_involution {b : G} {L K : Subgroup G} (h : GSCorr b L b K) : K = L := by
  obtain ⟨-, -, -, hLb, hL, hKb, hK, -, -, hfix⟩ := h
  rw [gsFixedLayer_eq_self hLb hL, conjugate_eq_self_of_le_centralizer hKb, sup_idem,
    gsFixedLayer_eq_self hKb hK] at hfix
  exact hfix.symm

omit [Finite G] in
theorem mem_coreActionKernel_of_le_centralizer {s : G} {L : Subgroup G}
    (hLs : L ≤ centralizer ({s} : Set G)) : s ∈ coreActionKernel L := by
  have hsC : s ∈ centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hLs hh)
  refine ⟨centralizer_le_normalizer _ hsC, fun j hj => ?_⟩
  have hjs : j * s = s * j := mem_centralizer_singleton_iff.mp (hLs hj)
  have h1 : j⁻¹ * s⁻¹ * j * s = 1 := by
    calc j⁻¹ * s⁻¹ * j * s = j⁻¹ * s⁻¹ * (j * s) := by group
      _ = j⁻¹ * s⁻¹ * (s * j) := by rw [hjs]
      _ = 1 := by group
  rw [h1]
  exact one_mem _

omit [Finite G] in
theorem isPGroup_two_sup_zpowers {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : s * t = t * s) : IsPGroup 2 ↥(zpowers t ⊔ zpowers s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2s : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have h2t : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hnorm : zpowers t ≤ normalizer (zpowers s : Set G) := by
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (show Commute s t from hst) k)).eq
  exact h2t.to_sup_of_normal_right' h2s hnorm

theorem reach_conjugate_of_cyclic_kernel {b : G} {L : Subgroup G} (hb : orderOf b = 2)
    (hP : ∃ P : Sylow 2 ↥(coreActionKernel L),
      (P : Subgroup _) = (zpowers b).subgroupOf (coreActionKernel L))
    {M : Subgroup G} (hM : GSReach L M) : ∃ g : G, M = conjugate L g := by
  obtain ⟨-, hR⟩ := hM
  induction hR with
  | refl => exact ⟨1, (conjugate_one L).symm⟩
  | @tail M N _ hst ih =>
    obtain ⟨g, rfl⟩ := ih
    obtain ⟨s, t, hC⟩ := hst
    have hC' := gsCorr_conjugate hC g⁻¹
    rw [conjugate_conjugate_inv] at hC'
    set s' := g⁻¹⁻¹ * s * g⁻¹ with hs'
    set t' := g⁻¹⁻¹ * t * g⁻¹ with ht'
    have hs'K : s' ∈ coreActionKernel L := mem_coreActionKernel_of_le_centralizer hC'.2.2.2.1
    have ht'K : t' ∈ coreActionKernel L := ⟨hC'.2.2.2.2.2.2.2.1, hC'.2.2.2.2.2.2.2.2.1⟩
    have hE : zpowers t' ⊔ zpowers s' ≤ coreActionKernel L :=
      sup_le (zpowers_le.mpr ht'K) (zpowers_le.mpr hs'K)
    obtain ⟨n, hnK, hEn⟩ := exists_conjugate_le_of_sylow hP hE
      (isPGroup_two_sup_zpowers hC'.1 hC'.2.1 hC'.2.2.1)
    have hC'' := gsCorr_conjugate hC' n
    have hLn : conjugate L n = L := by
      ext y
      rw [mem_conjugate_iff]
      exact ((mem_normalizer_iff.mp hnK.1) y).symm
    rw [hLn] at hC''
    have hinv : ∀ u : G, orderOf u = 2 → u ∈ zpowers b → u = b := fun u hu hub => by
      rcases (LocalB.mem_zpowers_iff_of_involution b u hb).1 hub with rfl | rfl
      · rw [orderOf_one] at hu
        exact absurd hu (by norm_num)
      · rfl
    have hs1 : n⁻¹ * s' * n = b := hinv _ hC''.1
      (hEn (conj_mem_conjugate (mem_sup_right (mem_zpowers s')) n))
    have ht1 : n⁻¹ * t' * n = b := hinv _ hC''.2.1
      (hEn (conj_mem_conjugate (mem_sup_left (mem_zpowers t')) n))
    rw [hs1, ht1] at hC''
    have hN := GSCorr.eq_of_eq_involution hC''
    refine ⟨n⁻¹ * g, ?_⟩
    rw [← hN, conjugate_conjugate, conjugate_conjugate]
    have hgn : g⁻¹ * (n * (n⁻¹ * g)) = 1 := by group
    rw [hgn, conjugate_one]

theorem gsMaximalComponent_of_cyclic_kernel {b : G} {L : Subgroup G} (hb : orderOf b = 2)
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))))
    (hP : ∃ P : Sylow 2 ↥(coreActionKernel L),
      (P : Subgroup _) = (zpowers b).subgroupOf (coreActionKernel L)) :
    GSMaximalComponent L := by
  refine gsMaximalComponent_of_index_le ⟨b, hb, hLb, hL⟩ fun M hM => ?_
  obtain ⟨g, rfl⟩ := reach_conjugate_of_cyclic_kernel hb hP hM
  exact (index_pPrimeCore_conjugate L g).le

end CFSG.ComponentClassification.GSLit
