module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique CFSG.ABGLocalTools

theorem isSylowOf_top_of_sylowTwo {X : Type*} [Group X] [Finite X] {T H : Subgroup X}
    (hT : IsSylowTwoOf T H) : IsSylowOf 2 (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
  have := Fact.mk Nat.prime_two
  rw [isSylowOf_iff]
  refine ⟨le_top, hT.2.1.comap_subtype, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hT.2.2

theorem isSylowOf_map_injective_local {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    {p : ℕ} [Fact p.Prime] {P K : Subgroup G} (f : G →* G') (hf : Function.Injective f)
    (h : IsSylowOf p P K) : IsSylowOf p (P.map f) (K.map f) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map f, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective _ _ hf]


theorem pairConclusion_of_sl {G : Type} [Group G] [Finite G] {L R : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m)
    (hord : ¬ Chi0Order (Nat.card (SpecialLinearGroup (Fin m) K)))
    (φ : ↥L ≃* SpecialLinearGroup (Fin (m + 1)) K) (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hS : IsSylowTwoOf (R ⊓ L) L)
    (hinner : ∀ s ∈ R, Ch1.InducesInner s L) : PairConclusion L R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SL : Subgroup ↥L := (R ⊓ L).subgroupOf L with hSL
  have hSyl : IsSylowOf 2 SL (⊤ : Subgroup ↥L) := isSylowOf_top_of_sylowTwo hS
  have hSyl' : IsSylowOf 2 (SL.map φ.toMonoidHom) (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)) := by
    have := isSylowOf_map_injective_local φ.toMonoidHom φ.injective hSyl
    rwa [Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at this
  obtain ⟨Sy, hSy⟩ := exists_sylow_unitriangular (K := K) 2 (n := m + 1) (by omega)
  have hU : IsSylowOf 2 (unitriangular (m + 1) K) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hSy]
      exact Sy.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hSy]
      exact Sy.not_dvd_index
  obtain ⟨k, -, hk⟩ := hSyl'.exists_mem_conj hU
  let φ' : ↥L ≃* SpecialLinearGroup (Fin (m + 1)) K := φ.trans (MulAut.conj k)
  have hφ' : ∀ l : ↥L, φ' l ∈ unitriangular (m + 1) K ↔ l ∈ SL := by
    intro l
    have h1 : φ' l = k * φ l * k⁻¹ := rfl
    rw [hk, h1, Subgroup.mem_map_equiv]
    have h2 : k⁻¹ * (k * φ l * k⁻¹) * k = φ l := by group
    rw [h2, MulEquiv.symm_apply_apply]
  have hφ'U : ∀ x : SpecialLinearGroup (Fin (m + 1)) K,
      x ∈ unitriangular (m + 1) K ↔ φ'.symm x ∈ SL := fun x => by
    rw [← hφ' (φ'.symm x), MulEquiv.apply_symm_apply]
  have hmemSL : ∀ l : ↥L, l ∈ SL ↔ (l : G) ∈ R := fun l => by
    rw [hSL, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, l.2⟩⟩
  obtain ⟨P₁, P₂, hU1, hU2, hne1, hne2, hsup, ⟨q₁, hq₁, hk₁, hC₁⟩, ⟨q₂, hq₂, hk₂, hC₂⟩⟩ :=
    sl_pairs hK (by omega : 2 ≤ m)
  let ι : SpecialLinearGroup (Fin (m + 1)) K →* G := L.subtype.comp φ'.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ'.symm.injective
  have hιL : ∀ x, ι x ∈ L := fun x => (φ'.symm x).2
  have hιsurj : ∀ y ∈ L, ∃ x, ι x = y := fun y hy => ⟨φ' ⟨y, hy⟩, by simp [ι]⟩
  have hnorm : ∀ P : Subgroup (SpecialLinearGroup (Fin (m + 1)) K), unitriangular (m + 1) K ≤ P →
      R ≤ Subgroup.normalizer ((P.map ι : Subgroup G) : Set G) := by
    intro P hUP r hr
    obtain ⟨l, hlL, hl⟩ := hinner r hr
    have hconj : ∀ x ∈ L, r * x * r⁻¹ = l * x * l⁻¹ := by
      intro x hx
      have hrx : r * x * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hRN hr) x).1 hx
      have := hl _ hrx
      have h2 : r⁻¹ * (r * x * r⁻¹) * r = x := by group
      rw [h2] at this
      calc r * x * r⁻¹ = l * (l⁻¹ * (r * x * r⁻¹) * l) * l⁻¹ := by group
        _ = l * x * l⁻¹ := by rw [← this]
    set l' : ↥L := ⟨l, hlL⟩ with hl'
    have hlR : l ∈ R := by
      have hmem : φ' l' ∈ Subgroup.normalizer ((unitriangular (m + 1) K : Subgroup _) : Set _) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        obtain ⟨s, rfl⟩ := φ'.surjective h
        have h1 : φ' l' * φ' s * (φ' l')⁻¹ = φ' (l' * s * l'⁻¹) := by rw [map_mul, map_mul, map_inv]
        rw [h1, hφ', hφ', hmemSL, hmemSL]
        have h3 : ((l' * s * l'⁻¹ : ↥L) : G) = r * (s : G) * r⁻¹ := (hconj s s.2).symm
        rw [h3]
        constructor
        · intro hs
          exact R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr)
        · intro hs
          have := R.mul_mem (R.mul_mem (R.inv_mem hr) hs) hr
          have h4 : r⁻¹ * (r * (s : G) * r⁻¹) * r = (s : G) := by group
          rwa [h4] at this
      rw [normalizer_unitriangular] at hmem
      have hUmem := upperTriangular_le_unitriangular hK hmem
      exact (hmemSL l').1 ((hφ' l').1 hUmem)
    have hlP : l ∈ P.map ι := by
      refine ⟨φ' l', hUP ((hφ' l').2 ((hmemSL l').2 hlR)), ?_⟩
      simp [ι]
      rfl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxL : x ∈ L := by
        obtain ⟨y, -, rfl⟩ := hx
        exact hιL y
      rw [hconj x hxL]
      exact (P.map ι).mul_mem ((P.map ι).mul_mem hlP hx) ((P.map ι).inv_mem hlP)
    · intro hx
      have hxL : r * x * r⁻¹ ∈ L := by
        obtain ⟨y, -, hy⟩ := hx
        exact hy ▸ hιL y
      have := hl _ hxL
      have h2 : r⁻¹ * (r * x * r⁻¹) * r = x := by group
      rw [h2] at this
      rw [this]
      exact (P.map ι).mul_mem ((P.map ι).mul_mem ((P.map ι).inv_mem hlP) hx) hlP
  have hsimple : IsSimpleGroup (SpecialLinearGroup (Fin m) K) := sl_isSimple_of_card_two hK hm
  have hT2 : ¬ IsPGroup 2 (SpecialLinearGroup (Fin m) K) := fun hp => by
    have : Group.IsNilpotent (SpecialLinearGroup (Fin m) K) := hp.isNilpotent
    obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two hK hm
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  have h1 := charTwo_not_hasChi0Block_map ι hι q₁ hq₁ hsimple hT2 hk₁ hC₁ hord
  have h2 := charTwo_not_hasChi0Block_map ι hι q₂ hq₂ hsimple hT2 hk₂ hC₂ hord
  have hle : ∀ P : Subgroup (SpecialLinearGroup (Fin (m + 1)) K), P.map ι ≤ L := fun P y hy => by
    obtain ⟨x, -, rfl⟩ := hy
    exact hιL x
  have hne : ∀ P : Subgroup (SpecialLinearGroup (Fin (m + 1)) K), P ≠ ⊤ → P.map ι ≠ L :=
    fun P hP h => by
      apply hP
      rw [eq_top_iff]
      intro x _
      have : ι x ∈ P.map ι := h ▸ hιL x
      obtain ⟨y, hy, hyx⟩ := this
      exact hι hyx ▸ hy
  have htop : (⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) K)).map ι = L := by
    apply le_antisymm (hle ⊤)
    intro y hy
    obtain ⟨x, hx⟩ := hιsurj y hy
    exact ⟨x, Subgroup.mem_top x, hx⟩
  refine ⟨P₁.map ι, P₂.map ι, hle P₁, hle P₂, hne P₁ hne1, hne P₂ hne2, ?_, hnorm P₁ hU1,
    hnorm P₂ hU2, h1.1, h2.1, h1.2, h2.2⟩
  rw [← Subgroup.map_sup, hsup, htop]

theorem chi0_mono {n k : ℕ} (h : k ≤ n) : 2 ^ k * (4 ^ k - 1) ≤ 2 ^ n * (4 ^ n - 1) :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1)

theorem not_chi0Order_168 : ¬ Chi0Order 168 := by
  rintro (h | ⟨n, hn, h⟩)
  · omega
  · by_cases h2 : n = 2
    · subst h2
      norm_num at h
    · have h3 : 2 ^ 3 * (4 ^ 3 - 1) ≤ 2 ^ n * (4 ^ n - 1) := chi0_mono (by omega)
      norm_num at h3
      omega

theorem not_chi0Order_20160 : ¬ Chi0Order 20160 := by
  rintro (h | ⟨n, hn, h⟩)
  · omega
  · by_cases h5 : 5 ≤ n
    · have h3 : 2 ^ 5 * (4 ^ 5 - 1) ≤ 2 ^ n * (4 ^ n - 1) := chi0_mono h5
      norm_num at h3
      omega
    · have : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases this with rfl | rfl | rfl <;> norm_num at h

theorem card_sl_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (SpecialLinearGroup (Fin 3) K) = 168 := by
  have := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_SL_field 3]
  simp [Fin.prod_univ_three, hKf]

theorem card_sl_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (SpecialLinearGroup (Fin 4) K) = 20160 := by
  have := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_SL_field 4]
  simp [Fin.prod_univ_four, hKf]

theorem pairsFor_L42 : PairsFor TypeL42 := by
  intro G _ _ L R hq ⟨hmodel, hout⟩ hR hRN hS
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hmodel
  have hK : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have hcard' : Fintype.card K = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) hcard'
  let φ : ↥L ≃* SpecialLinearGroup (Fin (3 + 1)) K := e.trans (slEquivStatedProj hK 4).symm
  have hinner : ∀ s ∈ R, Ch1.InducesInner s L := fun s hs => by
    by_contra h
    exact hout ⟨s, hs, hRN hs, h⟩
  refine pairConclusion_of_sl hK (by norm_num) ?_ φ hRN hS hinner
  rw [card_sl_three hK]
  exact not_chi0Order_168

theorem pairsFor_L52In : PairsFor TypeL52In := by
  intro G _ _ L R hq ⟨hmodel, hout⟩ hR hRN hS
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hmodel
  have hK : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have hcard' : Fintype.card K = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) hcard'
  let φ : ↥L ≃* SpecialLinearGroup (Fin (4 + 1)) K := e.trans (slEquivStatedProj hK 5).symm
  have hinner : ∀ s ∈ R, Ch1.InducesInner s L := fun s hs => by
    by_contra h
    exact hout ⟨s, hs, hRN hs, h⟩
  refine pairConclusion_of_sl hK (by norm_num) ?_ φ hRN hS hinner
  rw [card_sl_four hK]
  exact not_chi0Order_20160

theorem l239ParabolicPairs_of_remaining
    (hG2 : PairsFor TypeG2) (h3D4 : PairsFor Type3D4) (h2F4 : PairsFor Type2F4)
    (hTits : PairsFor TypeTits) (hL52Out : PairsFor TypeL52Out) (hU33 : PairsFor TypeU33)
    (hG24 : PairsFor TypeG24) (hM12 : PairsFor (TypeSporadic .M12))
    (hM24 : PairsFor (TypeSporadic .M24)) (hJ2 : PairsFor (TypeSporadic .J2))
    (hJ4 : PairsFor (TypeSporadic .J4)) (hHS : PairsFor (TypeSporadic .HS))
    (hHe : PairsFor (TypeSporadic .He)) (hRu : PairsFor (TypeSporadic .Ru)) :
    L239ParabolicPairs :=
  l239ParabolicPairs_of_cases hG2 h3D4 h2F4 hTits pairsFor_L52In hL52Out hU33 hG24 hM12 hM24 hJ2
    hJ4 hHS hHe hRu pairsFor_L42

end CFSG.QuasithinUnique.Vol2Native.L239
