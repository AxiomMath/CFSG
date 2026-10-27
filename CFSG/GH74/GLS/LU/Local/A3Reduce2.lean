module

public import CFSG.GH74.GLS.LU.Local.A3Reduce
public import CFSG.GH74.GLS.LU.Local.KStep2

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.TwoThin
open scoped MatrixGroups

theorem subgroupOf_map_conj {G : Type} [Group G] (C K : Subgroup G) (g : G) (hg : g ∈ C) (hK : K ≤ C) :
    (K.subgroupOf C).map (MulAut.conj (⟨g, hg⟩ : C)).toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).subgroupOf C := by
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨k, hkC⟩, hk, hky⟩
    have h1 : g * k * g⁻¹ = y := by
      have := congrArg Subtype.val hky
      exact this
    exact ⟨k, hk, h1⟩
  · rintro ⟨k, hk, hky⟩
    have hkC : k ∈ C := hK hk
    refine ⟨⟨k, hkC⟩, hk, ?_⟩
    apply Subtype.ext
    exact hky

@[expose] def LUKStepLeaf₁ : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G), A3Hyp G p f z S K₁ K₂ t u →
    ∀ ε : ℤ, ¬ (p ^ f = 5 ∧ ε = 1) → LUEps G (p ^ f) ε z K₁ u →
      ∃ (u' h x : G) (hxz : z * x = x * z),
        h * x = x * h ∧ (u' = u ∨ u' = u * z) ∧ h⁻¹ * z * h = u' ∧
        t ∈ normalizer (cj K₁ h : Set G) ∧ x ≠ 1 ∧ K₁ ≤ centralizer ({x} : Set G) ∧
        KComp (CY G x) (toCY hxz) (K₁.subgroupOf (centralizer ({x} : Set G))) ∧
        (∀ T : Sylow 2 ↥(centralizer
            ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x))),
          IsCyclic ↥T) ∧
        (∀ d ∈ pPrimeCore 2 (CY G x), (d : G) * z = z * (d : G) → u' * (d : G) = (d : G) * u') ∧
        ∃ g : G, g * x = x * g ∧ g * z * g⁻¹ = z * u'

variable {G : Type} [Group G]

theorem kstep_data_of_leaf₁ [Finite G] {p f : ℕ} (h95 : IVK_9_5At (p ^ f)) (h44a : IVK_4_4a)
    (hM3 : L3InvTorus) (hCov : L3Cover) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ f) (ε : ℤ)
    {z : G} {K₁ : Subgroup G} (hK₁sl : HasSL2Model ↥K₁ (fun r => r = p ^ f))
    {u' h x : G} {L : Subgroup G} (hxz : z * x = x * z) (hhx : h * x = x * h)
    (hhz : h⁻¹ * z * h = u') (hL : L = cj K₁ h) (hK₁C : K₁ ≤ centralizer ({x} : Set G))
    (hY : IsKGroupNative (CY G x))
    (hKC : KComp (CY G x) (toCY hxz) (K₁.subgroupOf (centralizer ({x} : Set G))))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer
        ((K₁.subgroupOf (centralizer ({x} : Set G)) : Subgroup (CY G x)) : Set (CY G x))),
      IsCyclic ↥T)
    (hD1 : ∀ d ∈ pPrimeCore 2 (CY G x), (d : G) * z = z * (d : G) → u' * (d : G) = (d : G) * u')
    (hg : ∃ g : G, g * x = x * g ∧ g * z * g⁻¹ = z * u')
    (hcard : (Nat.card ↥(K₁ ⊓ centralizer ({u'} : Set G)) : ℤ) = ((p ^ f : ℕ) : ℤ) - ε) :
    (ε = 1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ∃ α₀ : SL(3, F) →* ↥((K₁.subgroupOf (centralizer ({x} : Set G))) ⊔
          (L.subgroupOf (centralizer ({x} : Set G)))), Function.Surjective α₀) ∧
    (ε = -1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ f) ^ 2 ∧
      ∃ α₀ : ↥(StatedSU 3 (p ^ f) F) →* ↥((K₁.subgroupOf (centralizer ({x} : Set G))) ⊔
          (L.subgroupOf (centralizer ({x} : Set G)))), Function.Surjective α₀) := by
  have hxu : u' * x = x * u' := by
    rw [← hhz]
    have h1 : h⁻¹ * x = x * h⁻¹ := by
      have := congrArg (fun y => h⁻¹ * y * h⁻¹) hhx
      simpa [mul_assoc] using this.symm
    calc h⁻¹ * z * h * x = h⁻¹ * z * (h * x) := by group
      _ = h⁻¹ * z * (x * h) := by rw [hhx]
      _ = h⁻¹ * (z * x) * h := by group
      _ = h⁻¹ * (x * z) * h := by rw [hxz]
      _ = (h⁻¹ * x) * z * h := by group
      _ = (x * h⁻¹) * z * h := by rw [h1]
      _ = x * (h⁻¹ * z * h) := by group
  have hhC : h ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hhx
  have hh'C : h⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hhC
  have hLC : L ≤ centralizer ({x} : Set G) := by
    intro y hy
    rw [hL, mem_cj] at hy
    have hyC : h * y * h⁻¹ ∈ centralizer ({x} : Set G) := hK₁C hy
    have : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [this]
    exact (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hh'C hyC) hhC
  set g'Y : CY G x := ⟨h⁻¹, hh'C⟩ with hg'Y
  have hgY : g'Y * toCY hxz * g'Y⁻¹ = toCY hxu := by
    apply Subtype.ext
    show h⁻¹ * z * h⁻¹⁻¹ = u'
    rw [inv_inv]; exact hhz
  have hK' : L.subgroupOf (centralizer ({x} : Set G)) =
      (K₁.subgroupOf (centralizer ({x} : Set G))).map (MulAut.conj g'Y).toMonoidHom := by
    rw [hg'Y, subgroupOf_map_conj _ _ _ hh'C hK₁C, hL]
    rfl
  have hhD1 : ∀ d ∈ pPrimeCore 2 (CY G x), d ∈ centralizer ({toCY hxz} : Set (CY G x)) →
      toCY hxu * d = d * toCY hxu := by
    intro d hd hdc
    have h1 : (d : G) * z = z * (d : G) := by
      have := mem_centralizer_singleton_iff.mp hdc
      exact congrArg Subtype.val this
    exact Subtype.ext (by
      show u' * (d : G) = (d : G) * u'
      exact hD1 d hd h1)
  have hsl : HasSL2Model ↥(K₁.subgroupOf (centralizer ({x} : Set G))) (fun r => r = p ^ f) := by
    obtain ⟨F, hF, hFin, hFc, ⟨e⟩⟩ := hK₁sl
    exact ⟨F, hF, hFin, hFc, ⟨(Subgroup.subgroupOfEquivOfLe hK₁C).trans e⟩⟩
  obtain ⟨g, hgx, hgzu⟩ := hg
  have hgY' : ∃ g : CY G x, g * toCY hxz * g⁻¹ = toCY hxz * toCY hxu :=
    ⟨⟨g, mem_centralizer_singleton_iff.mpr hgx⟩, Subtype.ext hgzu⟩
  have hcardY : (Nat.card ↥(K₁.subgroupOf (centralizer ({x} : Set G)) ⊓
      centralizer ({toCY hxu} : Set (CY G x))) : ℤ) = ((p ^ f : ℕ) : ℤ) - ε := by
    rw [card_inf_toCY hK₁C hxu]; exact hcard
  exact kstep_final₁ h95 h44a hM3 hCov hY hp hp2 hq5 hKC hsl hcyc hhD1 hgY' g'Y hgY hK' hcardY

open scoped MatrixGroups in
theorem luA3Lin_of_leaf₁ (h95 : IVK_9_5) (h44a : IVK_4_4a) (hM3 : L3InvTorus) (hCov : L3Cover)
    (hLeaf : LUKStepLeaf₁) : LUA3Lin := by
  intro G _ _ hG p f hp hp2 hq hq5 z S K₁ K₂ t u hH he
  obtain ⟨u', h, x, hxz, hhx, hu', hh, htL, hx1, hK₁C, hKC, hcyc, hD1, hg⟩ :=
    hLeaf G hG p f hp hp2 hq z S K₁ K₂ t u hH 1 (fun h => hq5 h.1) he
  obtain ⟨hc, hs, -, -, -⟩ := hH
  have hY := isKGroupNative_centralizer hG hx1
  have hsl : HasSL2Model ↥K₁ (fun r => r = p ^ f) := hc.sl₁
  have he' : LUEps G (p ^ f) 1 z K₁ u' := by
    rcases hu' with rfl | rfl
    · exact he
    · exact he.mul_z hc
  have hfin := (kstep_data_of_leaf₁ (IVK_9_5At_of h95 (by omega)) h44a hM3 hCov hp hp2 (by omega) 1 hsl hxz
    hhx hh rfl hK₁C hY hKC hcyc hD1 hg he'.H_card).1 rfl
  obtain ⟨F, hF, hFin, hFc, α₀, hα₀⟩ := hfin
  have hz1 : z ≠ 1 := hs.z_ne_one
  have hzK : z ∈ K₁ := hc.z_mem₁
  have hhC : h ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hhx
  have hh'C : h⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hhC
  have hLC : cj K₁ h ≤ centralizer ({x} : Set G) := by
    intro y hy
    rw [mem_cj] at hy
    have hyC : h * y * h⁻¹ ∈ centralizer ({x} : Set G) := hK₁C hy
    have : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [this]
    exact (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hh'C hyC) hhC
  have hrange := range_comp_subtype_sup hK₁C hLC α₀ hα₀
  have hquasi : CFSG.IsQuasisimple SL(3, F) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl
  refine ⟨F, hF, hFin, u', h, cj K₁ h, hFc, hu', hh, Or.inl rfl, ?_, ?_⟩
  · refine ⟨_, ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK), hrange⟩
  · refine ⟨(MulAut.conj t).toMonoidHom.comp ((centralizer ({x} : Set G)).subtype.comp
        ((K₁.subgroupOf (centralizer ({x} : Set G)) ⊔
          (cj K₁ h).subgroupOf (centralizer ({x} : Set G))).subtype.comp α₀)), ?_, ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj t).injective]
      exact ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK)
    · have hLmap : (cj K₁ h).map (MulAut.conj t).toMonoidHom = cj K₁ h :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
      rw [MonoidHom.range_comp, hrange, Subgroup.map_sup, hs.t_swap, hLmap, sup_comm]

open scoped MatrixGroups in
theorem luA3Uni_core (h44a : IVK_4_4a) (hM3 : L3InvTorus) (hCov : L3Cover) (hLeaf : LUKStepLeaf₁)
    {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (h95 : IVK_9_5At (p ^ f)) {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
    {t u : G} (hH : A3Hyp G p f z S K₁ K₂ t u) (he : LUEps G (p ^ f) (-1) z K₁ u) :
    A3CoreUni G p f z K₁ K₂ u := by
  obtain ⟨u', h, x, hxz, hhx, hu', hh, htL, hx1, hK₁C, hKC, hcyc, hD1, hg⟩ :=
    hLeaf G hG p f hp hp2 hq z S K₁ K₂ t u hH (-1) (fun h => by have := h.2; omega) he
  obtain ⟨hc, hs, -, -, -⟩ := hH
  have hY := isKGroupNative_centralizer hG hx1
  have hsl : HasSL2Model ↥K₁ (fun r => r = p ^ f) := hc.sl₁
  have he' : LUEps G (p ^ f) (-1) z K₁ u' := by
    rcases hu' with rfl | rfl
    · exact he
    · exact he.mul_z hc
  have hfin := (kstep_data_of_leaf₁ h95 h44a hM3 hCov hp hp2 hq (-1) hsl hxz hhx hh
    rfl hK₁C hY hKC hcyc hD1 hg he'.H_card).2 rfl
  obtain ⟨F, hF, hFin, hFc, α₀, hα₀⟩ := hfin
  have hz1 : z ≠ 1 := hs.z_ne_one
  have hzK : z ∈ K₁ := hc.z_mem₁
  have hhC : h ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hhx
  have hh'C : h⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hhC
  have hLC : cj K₁ h ≤ centralizer ({x} : Set G) := by
    intro y hy
    rw [mem_cj] at hy
    have hyC : h * y * h⁻¹ ∈ centralizer ({x} : Set G) := hK₁C hy
    have : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [this]
    exact (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hh'C hyC) hhC
  have hrange := range_comp_subtype_sup hK₁C hLC α₀ hα₀
  have hf : 0 < f := Nat.pos_of_ne_zero fun h0 => by rw [h0, pow_zero] at hq; omega
  have : Fact p.Prime := ⟨hp⟩
  have hquasi : CFSG.IsQuasisimple (StatedSU 3 (p ^ f) F) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hFc le_rfl
      (fun h => by have := (Prod.mk.inj h).2; omega)).1
  have hFcp : CharP F p := charP_of_card_eq_pow hp (m := f * 2) (by omega) (by rw [hFc, ← pow_mul])
  refine ⟨F, hF, hFin, hFcp, GaloisField p f, inferInstance, inferInstance, u', h, cj K₁ h, hFc,
    ?_, hu', hh, Or.inl rfl, ?_, ?_⟩
  · exact GaloisField.card p f (by omega)
  · refine ⟨_, ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK), hrange⟩
  · have hLmap : (cj K₁ h).map (MulAut.conj t).toMonoidHom = cj K₁ h :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp htL
    refine ⟨(MulAut.conj t).toMonoidHom.comp ((centralizer ({x} : Set G)).subtype.comp
        ((K₁.subgroupOf (centralizer ({x} : Set G)) ⊔
          (cj K₁ h).subgroupOf (centralizer ({x} : Set G))).subtype.comp α₀)), ?_, ?_⟩
    · rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj t).injective]
      exact ker_le_center_of_range hquasi _ hz1 (by rw [hrange]; exact mem_sup_left hzK)
    · rw [MonoidHom.range_comp, hrange, Subgroup.map_sup, hs.t_swap, hLmap, sup_comm]

theorem luA3Uni_of_leaf₁ (h95 : IVK_9_5) (h44a : IVK_4_4a) (hM3 : L3InvTorus) (hCov : L3Cover)
    (hLeaf : LUKStepLeaf₁) (hFive : LUA3UniFive) : LUA3Uni := by
  intro G _ _ hG p f hp hp2 hq z S K₁ K₂ t u hH he
  by_cases h5 : p ^ f = 5
  · exact hFive G hG p f hp hp2 hq h5 z S K₁ K₂ t u hH he
  exact luA3Uni_core h44a hM3 hCov hLeaf hG hp hp2 hq
    (IVK_9_5At_of h95 (lt_of_le_of_ne hq (Ne.symm h5))) hH he

theorem luA3UniFive_of_leaf₁ (h95 : IVK_9_5At 5) (h44a : IVK_4_4a) (hM3 : L3InvTorus)
    (hCov : L3Cover) (hLeaf : LUKStepLeaf₁) : LUA3UniFive := by
  intro G _ _ hG p f hp hp2 hq h5 z S K₁ K₂ t u hH he
  exact luA3Uni_core h44a hM3 hCov hLeaf hG hp hp2 hq (by rw [h5]; exact h95) hH he

end CFSG.GH74.GLS.LU.Local
