module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLemma228
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalNested
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Conj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pumpUp_le_centralizer (J : Subgroup G) (t : G) :
    pumpUp J t ≤ centralizer ({t} : Set G) := by
  apply iSup₂_le
  intro g hg
  have hgC : g ∈ centralizer ({t} : Set G) := map_subtype_le _ hg
  rintro _ ⟨y, hy, rfl⟩
  have hyC : y ∈ centralizer ({t} : Set G) := (gsFixedLayer_le_inf J t hy).2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact mul_mem (mul_mem (inv_mem hgC) hyC) hgC

omit [Finite G] in
theorem wGroup_mono {A B : Subgroup G} (h : B ≤ A) : wGroup B ≤ wGroup A := by
  apply iSup_le
  intro B'
  apply iSup_le
  intro hB'
  exact le_iSup_of_le B' (le_iSup_of_le (hB'.trans h) le_rfl)

omit [Finite G] in
theorem normalizer_le_normalizer_oddIn (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (oddIn L : Set G) :=
  normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L)

theorem exists_conj_mem_of_isSylowTwoIn {S H : Subgroup G} (hS : IsSylowTwoIn S H) {x : G}
    (hxH : x ∈ H) (hx : IsPGroup 2 (zpowers x)) : ∃ g ∈ H, g⁻¹ * x * g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, P, hP⟩ := hS
  have hx' : IsPGroup 2 (zpowers (⟨x, hxH⟩ : H)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(zpowers x))).mp hx
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, ← orderOf_coe, ← Nat.card_zpowers]
    exact hk
  obtain ⟨Q, hQ⟩ := hx'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨(h⁻¹ : H), (h⁻¹ : H).2, ?_⟩
  have hmem : (⟨x, hxH⟩ : H) ∈ (Q : Subgroup H) := hQ (mem_zpowers _)
  have h1 : h * ⟨x, hxH⟩ * h⁻¹ ∈ (P : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mpr ⟨_, hmem, rfl⟩
  rw [hP, mem_subgroupOf] at h1
  simpa [inv_inv] using h1

omit [Finite G] in
theorem isPComponent_centralizer_conj {L : Subgroup G} {a g : G}
    (hLa : L ≤ centralizer ({a} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G))))
    (hg : g ∈ normalizer (L : Set G)) :
    L ≤ centralizer ({g⁻¹ * a * g} : Set G) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({g⁻¹ * a * g} : Set G))) := by
  obtain ⟨h1, h2⟩ := GSThmB.Six.isPComponent_conjugate hLa hL g
  have hLg : conjugate L g = L := by
    ext y
    simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      simpa using this
    · intro hy
      refine ⟨g * y * g⁻¹, (mem_normalizer_iff.mp hg y).mp hy, by group⟩
  have hCg : conjugate (centralizer ({a} : Set G)) g = centralizer ({g⁻¹ * a * g} : Set G) := by
    ext y
    simp only [conjugate, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      calc g⁻¹ * c * g * (g⁻¹ * a * g) = g⁻¹ * (c * a) * g := by group
        _ = g⁻¹ * (a * c) * g := by rw [hc]
        _ = g⁻¹ * a * g * (g⁻¹ * c * g) := by group
    · intro hy
      refine ⟨g * y * g⁻¹, ?_, by group⟩
      calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by rw [hy]
        _ = a * (g * y * g⁻¹) := by group
  rw [hLg, hCg] at h1 h2
  exact ⟨h1, h2⟩

omit [Finite G] in
theorem isSubnormal_inf_subgroupOf {L H K : Subgroup G} (hKH : K ≤ H)
    (hL : (L.subgroupOf H).IsSubnormal) : ((L ⊓ K).subgroupOf K).IsSubnormal := by
  have h1 : ((L.subgroupOf H).subgroupOf (K.subgroupOf H)).IsSubnormal := hL.subgroupOf
  set ψ : ↥(K.subgroupOf H) ≃* ↥K := subgroupOfEquivOfLe hKH with hψ
  have h2 := h1.map (f := ψ.toMonoidHom) ψ.surjective
  convert h2 using 1
  ext k
  simp only [mem_subgroupOf, mem_inf, mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨hkL, -⟩
    refine ⟨⟨⟨k, hKH k.2⟩, k.2⟩, hkL, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, (ψ y).2⟩

theorem commutator_oddCore_pLayer_le (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hK : Assembly.KProper Blueprint.Catalog G) {b e : G} {L : Subgroup G} (hb : orderOf b = 2)
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G)))) (hbe : b * e = e * b)
    (htop : centralizer ({e} : Set G) ≠ ⊤) :
    ⁅(pPrimeCore 2 L).map L.subtype ⊓ centralizer ({e} : Set G),
      (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map (L ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({e} : Set G) with hH
  have hKH : SectionRank.IsKGroupCat ↥H :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK H htop
  have hbH : b ∈ H := mem_centralizer_singleton_iff.mpr hbe
  have hb1 : b ≠ 1 := by rintro rfl; simp at hb
  have hD1 : zpowers b ≠ ⊥ := fun h => hb1 (zpowers_eq_bot.mp h)
  have hD2 : IsPGroup 2 (zpowers b) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hb, pow_one]
  have h := commutator_pLayer_pPrimeCore_le_of_inputs hS hU hheld hKH
    (zpowers_le.mpr hbH) hD1 hD2
  rw [LocalB.normalizer_zpowers_of_involution b hb] at h
  set K := H ⊓ centralizer ({b} : Set G) with hKdef
  have hO : (pPrimeCore 2 L).map L.subtype ⊓ H ≤ (pPrimeCore 2 K).map K.subtype := by
    have h1 := GSLit.map_pPrimeCore_le_of_isPComponent hLb hL
    have hKN : K ≤ normalizer ((pPrimeCore 2 (centralizer ({b} : Set G))).map
        (centralizer ({b} : Set G)).subtype : Set G) := fun k hk =>
      normalizer_le_normalizer_map_of_characteristic _ _ (le_normalizer hk.2)
    have hodd : Odd (Nat.card ((pPrimeCore 2 (centralizer ({b} : Set G))).map
        (centralizer ({b} : Set G)).subtype)) := by
      rw [card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    refine le_trans ?_ (inf_le_map_pPrimeCore_two hKN hodd)
    refine le_inf (le_inf inf_le_right ?_) (inf_le_left.trans h1)
    exact inf_le_left.trans ((map_subtype_le _).trans hLb)
  have hlay : (pLayer ↥(L ⊓ H) 2).map (L ⊓ H).subtype ≤ (pLayer ↥K 2).map K.subtype := by
    have hLK : L ⊓ H ≤ K := le_inf inf_le_right (inf_le_left.trans hLb)
    have hsub : ((L ⊓ H).subgroupOf K).IsSubnormal := by
      have h1 := isSubnormal_inf_subgroupOf (inf_le_right : K ≤ centralizer ({b} : Set G))
        (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLb |>.mp hL).1
      have hLHK : L ⊓ K = L ⊓ H :=
        le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
          (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hLb)))
      rwa [hLHK] at h1
    exact pLayer_map_le_of_isSubnormal hLK hsub
  calc ⁅(pPrimeCore 2 L).map L.subtype ⊓ H, (pLayer ↥(L ⊓ H) 2).map (L ⊓ H).subtype⁆
      ≤ ⁅(pPrimeCore 2 K).map K.subtype, (pLayer ↥K 2).map K.subtype⁆ := commutator_mono hO hlay
    _ = ⁅(pLayer ↥K 2).map K.subtype, (pPrimeCore 2 K).map K.subtype⁆ := commutator_comm _ _
    _ ≤ (pPrimeCore 2 H).map H.subtype := h

theorem mem_centralizer_of_mem_coreActionKernel {L C : Subgroup G} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) {s : G} (hsC : s ∈ C)
    (hs : s ∈ coreActionKernel L) (hs2 : IsPGroup 2 (zpowers s))
    (hsX : s ∈ centralizer (oddIn L : Set G)) : s ∈ centralizer (L : Set G) := by
  have hN := (mem_coreActionKernel.mp hs).1
  have hcen : ∀ f ∈ zpowers s, ∀ l ∈ L, f * l * f⁻¹ * l⁻¹ ∈ (pPrimeCore 2 L).map L.subtype := by
    intro f hf l hl
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hf
    have hfK : s ^ i ∈ coreActionKernel L := zpow_mem hs i
    have h1 := (mem_coreActionKernel.mp (inv_mem hfK)).2 l hl
    rw [inv_inv] at h1
    have hlN : l ∈ normalizer (oddIn L : Set G) :=
      normalizer_le_normalizer_oddIn L (le_normalizer hl)
    have h2 := (mem_normalizer_iff.mp hlN _).mp h1
    have e : l * (l⁻¹ * s ^ i * l * (s ^ i)⁻¹) * l⁻¹ = s ^ i * l * (s ^ i)⁻¹ * l⁻¹ := by group
    rw [e] at h2
    exact h2
  have hcov := le_pLayer_inf_centralizer_sup hLC hL (zpowers_le.mpr hsC) hs2
    (zpowers_le.mpr hN) hcen
  rw [mem_centralizer_iff]
  intro l hl
  have hle : (pLayer ↥(L ⊓ centralizer ((zpowers s : Subgroup G) : Set G)) 2).map
      (L ⊓ centralizer ((zpowers s : Subgroup G) : Set G)).subtype ⊔
      (pPrimeCore 2 L).map L.subtype ≤ centralizer ({s} : Set G) := by
    refine sup_le ((map_subtype_le _).trans (inf_le_right.trans ?_)) ?_
    · intro y hy
      rw [mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp hy) s (mem_zpowers s)).symm
    · intro y hy
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hsX) y hy
  exact mem_centralizer_singleton_iff.mp (hle (hcov hl))

end CFSG.ComponentClassification.GrSLit.GrS5
