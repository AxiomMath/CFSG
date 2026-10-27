module

public import CFSG.GH74.GLS.LU.Local.KStep
public import CFSG.GH74.GLS.LU.Local.A3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.TwoThin
open scoped MatrixGroups

abbrev CY (G : Type) [Group G] (x : G) : Type := ↥(centralizer ({x} : Set G))

@[expose] def toCY {G : Type} [Group G] {x g : G} (hg : g * x = x * g) : CY G x :=
  ⟨g, mem_centralizer_singleton_iff.mpr hg⟩

@[expose] def LUKStepLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), A3Hyp G p f z S K₁ K₂ t u →
    ∀ ε : ℤ, LUEps G (p ^ f) ε z K₁ u →
      ∃ (u' h x : G) (L : Subgroup G) (hxz : z * x = x * z) (hxu : u' * x = x * u'),
        (u' = u ∨ u' = u * z) ∧ h⁻¹ * z * h = u' ∧ (L = cj K₁ h ∨ L = cj K₂ h) ∧
        t ∈ normalizer (L : Set G) ∧ x ≠ 1 ∧
        K₁ ≤ centralizer ({x} : Set G) ∧ L ≤ centralizer ({x} : Set G) ∧
        KPair (CY G x) (toCY hxz) (toCY hxu) (K₁.subgroupOf (centralizer ({x} : Set G)))
          (L.subgroupOf (centralizer ({x} : Set G))) ∧
        (∀ T : Sylow 2 ↥(centralizer
            ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x))),
          IsCyclic ↥T) ∧
        (∀ d ∈ pPrimeCore 2 (CY G x), d ∈ centralizer ({toCY hxz} : Set (CY G x)) →
          toCY hxu * d = d * toCY hxu) ∧
        (∀ d ∈ pPrimeCore 2 (CY G x), d ∈ centralizer ({toCY hxu} : Set (CY G x)) →
          toCY hxz * d = d * toCY hxz) ∧
        ∃ g : CY G x, g * toCY hxz * g⁻¹ = toCY hxz * toCY hxu

variable {G : Type} [Group G]

theorem isKGroupNative_centralizer [Finite G] (hG : IsKProperSimple G) {x : G} (hx : x ≠ 1) :
    IsKGroupNative (CY G x) := by
  have hne : centralizer ({x} : Set G) ≠ ⊤ := by
    intro h
    have hz : x ∈ center G := by
      rw [mem_center_iff]
      intro g
      have : g ∈ centralizer ({x} : Set G) := by rw [h]; exact mem_top g
      exact ((mem_centralizer_iff.mp this) x (Set.mem_singleton x)).symm
    have hsimple : IsSimpleGroup G := hG.1
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h1 | h1
    · rw [h1, mem_bot] at hz
      exact hx hz
    · obtain ⟨a, b, hab⟩ := hG.2.1
      apply hab
      have : a ∈ center G := by rw [h1]; exact mem_top a
      exact (mem_center_iff.mp this b).symm
  exact isKGroupNative_of_kProper hG.2.2 hne

theorem card_inf_toCY {x : G} {K₁ : Subgroup G} (hK : K₁ ≤ centralizer ({x} : Set G)) {u' : G}
    (hxu : u' * x = x * u') :
    Nat.card ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓
        centralizer ({toCY hxu} : Set (CY G x))) = Nat.card ↥(K₁ ⊓ centralizer ({u'} : Set G)) := by
  let f : ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓ centralizer ({toCY hxu} : Set (CY G x))) →
      ↥(K₁ ⊓ centralizer ({u'} : Set G)) := fun k =>
    ⟨((k : CY G x) : G), Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp k.2).1,
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
          (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).2))⟩⟩
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    exact h1
  · rintro ⟨y, hy⟩
    obtain ⟨hyK, hyu⟩ := Subgroup.mem_inf.mp hy
    refine ⟨⟨⟨y, hK hyK⟩, Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyK,
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hyu))⟩⟩, rfl⟩

theorem map_subtype_sup_subgroupOf (C K₁ L : Subgroup G) (hK : K₁ ≤ C) (hL : L ≤ C) :
    (K₁.subgroupOf C ⊔ L.subgroupOf C).map C.subtype = K₁ ⊔ L := by
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hK, Subgroup.map_subgroupOf_eq_of_le hL]

theorem charP_of_card_eq_pow {K : Type} [Field K] [Finite K] {p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hK : Nat.card K = p ^ m) : CharP K p := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card K (ringChar K)
  have h1 : p ^ m = (ringChar K) ^ (n : ℕ) := by
    rw [← hK, Nat.card_eq_fintype_card, hcard]
  have h2 : p ∣ (ringChar K) ^ (n : ℕ) := by rw [← h1]; exact dvd_pow_self p hm.ne'
  have h3 : p ∣ ringChar K := hp.dvd_of_dvd_pow h2
  have h4 : p = ringChar K := (Nat.prime_dvd_prime_iff_eq hp hpr).mp h3
  rw [h4]
  exact ringChar.charP K

theorem ker_le_center_of_range {S₀ : Type} [Group S₀] (hS : IsQuasisimple S₀) (α : S₀ →* G)
    {z : G} (hz1 : z ≠ 1) (hz : z ∈ α.range) : α.ker ≤ center S₀ := by
  obtain ⟨a, ha⟩ := hz
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hS ⟨a, by rw [ha]; exact hz1⟩


theorem range_comp_subtype_sup {x : G} {K₁ L : Subgroup G} (hK : K₁ ≤ centralizer ({x} : Set G))
    (hL : L ≤ centralizer ({x} : Set G)) {S₀ : Type} [Group S₀]
    (α₀ : S₀ →* ↥((K₁.subgroupOf (centralizer ({x} : Set G))) ⊔ (L.subgroupOf (centralizer ({x} : Set G)))))
    (hα₀ : Function.Surjective α₀) :
    ((centralizer ({x} : Set G)).subtype.comp
        ((K₁.subgroupOf (centralizer ({x} : Set G)) ⊔ L.subgroupOf (centralizer ({x} : Set G))).subtype.comp
          α₀)).range = K₁ ⊔ L := by
  rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hα₀, Subgroup.map_top,
    Subgroup.range_subtype, map_subtype_sup_subgroupOf _ _ _ hK hL]

open scoped MatrixGroups in
theorem luA3Lin_of_leaf (h95 : IVK_9_5) (h44a : IVK_4_4a) (hM3 : L3InvTorus) (hCov : L3Cover)
    (hLeaf : LUKStepLeaf) : LUA3Lin := by
  intro G _ _ hG p f hp hp2 hq hq5 z S K₁ K₂ t u hH he
  obtain ⟨u', h, x, L, hxz, hxu, hu', hh, hL, htL, hx1, hK₁C, hLC, hKP, hcyc, hD1, hD2, hg⟩ :=
    hLeaf G hG p f hp hp2 hq z S K₁ K₂ t u hH 1 he
  obtain ⟨hc, hs, -, -, -⟩ := hH
  have hY := isKGroupNative_centralizer hG hx1
  have hsl : HasSL2Model ↥(K₁.subgroupOf (centralizer ({x} : Set G))) (fun r => r = p ^ f) := by
    obtain ⟨F, hF, hFin, hFc, ⟨e⟩⟩ := hc.sl₁
    exact ⟨F, hF, hFin, hFc, ⟨(Subgroup.subgroupOfEquivOfLe hK₁C).trans e⟩⟩
  have he' : LUEps G (p ^ f) 1 z K₁ u' := by
    rcases hu' with rfl | rfl
    · exact he
    · exact he.mul_z hc
  have hcard : (Nat.card ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓
      centralizer ({toCY hxu} : Set (CY G x))) : ℤ) = ((p ^ f : ℕ) : ℤ) - 1 := by
    rw [card_inf_toCY hK₁C hxu]; exact he'.H_card
  have hfin := kstep_final (IVK_9_5At_of h95 (by omega)) h44a hM3 hCov hY hp hp2 (by omega) hKP hsl hcyc hD1 hD2 hg hcard
  obtain ⟨F, hF, hFin, hFc, α₀, hα₀⟩ := hfin.1 rfl
  have hz1 : z ≠ 1 := hs.z_ne_one
  have hzK : z ∈ K₁ := hc.z_mem₁
  have hrange := range_comp_subtype_sup hK₁C hLC α₀ hα₀
  have hquasi : CFSG.IsQuasisimple SL(3, F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
  refine ⟨F, hF, hFin, u', h, L, hFc, hu', hh, hL, ?_, ?_⟩
  · refine ⟨_, ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK), hrange⟩
  · refine ⟨(MulAut.conj t).toMonoidHom.comp ((centralizer ({x} : Set G)).subtype.comp
        ((K₁.subgroupOf (centralizer ({x} : Set G)) ⊔ L.subgroupOf (centralizer ({x} : Set G))).subtype.comp
          α₀)), ?_, ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj t).injective]
      exact ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK)
    · have hLmap : L.map (MulAut.conj t).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
      rw [MonoidHom.range_comp, hrange, Subgroup.map_sup, hs.t_swap, hLmap, sup_comm]


@[expose] def LUA3UniFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    p ^ f = 5 → ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
      A3Hyp G p f z S K₁ K₂ t u → LUEps G (p ^ f) (-1) z K₁ u → A3CoreUni G p f z K₁ K₂ u

open scoped MatrixGroups in
theorem luA3Uni_of_leaf (h95 : IVK_9_5) (h44a : IVK_4_4a) (hM3 : L3InvTorus) (hCov : L3Cover)
    (hLeaf : LUKStepLeaf) (hFive : LUA3UniFive) : LUA3Uni := by
  intro G _ _ hG p f hp hp2 hq z S K₁ K₂ t u hH he
  by_cases h5 : p ^ f = 5
  · exact hFive G hG p f hp hp2 hq h5 z S K₁ K₂ t u hH he
  have hq5 : 5 < p ^ f := lt_of_le_of_ne hq (Ne.symm h5)
  obtain ⟨u', h, x, L, hxz, hxu, hu', hh, hL, htL, hx1, hK₁C, hLC, hKP, hcyc, hD1, hD2, hg⟩ :=
    hLeaf G hG p f hp hp2 hq z S K₁ K₂ t u hH (-1) he
  obtain ⟨hc, hs, -, -, -⟩ := hH
  have hY := isKGroupNative_centralizer hG hx1
  have hsl : HasSL2Model ↥(K₁.subgroupOf (centralizer ({x} : Set G))) (fun r => r = p ^ f) := by
    obtain ⟨F, hF, hFin, hFc, ⟨e⟩⟩ := hc.sl₁
    exact ⟨F, hF, hFin, hFc, ⟨(Subgroup.subgroupOfEquivOfLe hK₁C).trans e⟩⟩
  have he' : LUEps G (p ^ f) (-1) z K₁ u' := by
    rcases hu' with rfl | rfl
    · exact he
    · exact he.mul_z hc
  have hcard : (Nat.card ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓
      centralizer ({toCY hxu} : Set (CY G x))) : ℤ) = ((p ^ f : ℕ) : ℤ) - (-1) := by
    rw [card_inf_toCY hK₁C hxu]; exact he'.H_card
  have hfin := kstep_final (IVK_9_5At_of h95 hq5) h44a hM3 hCov hY hp hp2 hq5.le hKP hsl hcyc hD1 hD2 hg hcard
  obtain ⟨F, hF, hFin, hFc, α₀, hα₀⟩ := hfin.2 rfl
  have hz1 : z ≠ 1 := hs.z_ne_one
  have hzK : z ∈ K₁ := hc.z_mem₁
  have hrange := range_comp_subtype_sup hK₁C hLC α₀ hα₀
  have hf : 0 < f := Nat.pos_of_ne_zero fun h0 => by rw [h0, pow_zero] at hq; omega
  have : Fact p.Prime := ⟨hp⟩
  have hquasi : CFSG.IsQuasisimple (StatedSU 3 (p ^ f) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hFc le_rfl
      (fun h => by have := (Prod.mk.inj h).2; omega)).1
  have hFcp : CharP F p := charP_of_card_eq_pow hp (m := f * 2) (by omega) (by rw [hFc, ← pow_mul])
  refine ⟨F, hF, hFin, hFcp, GaloisField p f, inferInstance, inferInstance, u', h, L, hFc,
    ?_, hu', hh, hL, ?_, ?_⟩
  · exact GaloisField.card p f (by omega)
  · refine ⟨_, ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK), hrange⟩
  · have hLmap : L.map (MulAut.conj t).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
    refine ⟨(MulAut.conj t).toMonoidHom.comp ((centralizer ({x} : Set G)).subtype.comp
        ((K₁.subgroupOf (centralizer ({x} : Set G)) ⊔ L.subgroupOf (centralizer ({x} : Set G))).subtype.comp
          α₀)), ?_, ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj t).injective]
      exact ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK)
    · rw [MonoidHom.range_comp, hrange, Subgroup.map_sup, hs.t_swap, hLmap, sup_comm]

end CFSG.GH74.GLS.LU.Local
