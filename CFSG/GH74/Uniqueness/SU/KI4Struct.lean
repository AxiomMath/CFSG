module

public import CFSG.GH74.Uniqueness.SU.KI6BComp
import CFSG.Adapters.WholeGroupLayer
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.Open
open scoped Pointwise commutatorElement

structure Setup (Y : Type) [Group Y] [Finite Y] : Prop where
  odd : CFSG.oddCore Y = ⊥
  sup : CFSG.Open.pCore 2 Y ⊔ goldschmidtLayer Y = ⊤

variable {Y : Type} [Group Y] [Finite Y]

theorem openLayer_eq_layer (G : Type*) [Group G] : goldschmidtLayer G = CFSG.layer G :=
  CFSG.Adapters.goldschmidtLayer_eq_foundations G

omit [Finite Y] in
theorem pPrimeCore_two_eq_bot (h : CFSG.oddCore Y = ⊥) : CFSG.pPrimeCore 2 Y = ⊥ := by
  rw [eq_bot_iff, ← h]
  exact sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mp hN.2⟩

theorem fitting_eq_openPCore (h : CFSG.oddCore Y = ⊥) :
    fittingSubgroup Y = CFSG.Open.pCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.Fitting_eq_pcore Y 2 (pPrimeCore_two_eq_bot h)]

omit [Finite Y] in
theorem openPCore_le_sylow (S : Sylow 2 Y) : CFSG.Open.pCore 2 Y ≤ (S : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Glauberman.pCore_le_sylow S

theorem exists_proj_of_sup_centralizer_eq_top {G : Type*} [Group G] (K : Subgroup G)
    (hK : K ⊔ Subgroup.centralizer (K : Set G) = ⊤) :
    ∃ f : G →* K ⧸ Subgroup.center K, (∀ k : K, f (k : G) = (k : K ⧸ Subgroup.center K)) ∧
      ∀ y : G, f y = 1 ↔ y ∈ Subgroup.centralizer (K : Set G) := by
  have hdec : ∀ y : G, ∃ k : K, ∃ c ∈ Subgroup.centralizer (K : Set G), y = (k : G) * c := by
    intro y
    have hy : y ∈ Subgroup.centralizer (K : Set G) ⊔ K := by
      rw [sup_comm, hK]; exact Subgroup.mem_top y
    have hle : Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
      Subgroup.centralizer_le_normalizer _
    have hy' : y ∈ ((Subgroup.centralizer (K : Set G) ⊔ K : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hy'
    obtain ⟨c, hc, k, hk, rfl⟩ := Set.mem_mul.1 hy'
    refine ⟨⟨k, hk⟩, c, hc, ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 hc k hk).symm
  have hcomm : ∀ c ∈ Subgroup.centralizer (K : Set G), ∀ k : K, (k : G) * c = c * k :=
    fun c hc k => Subgroup.mem_centralizer_iff.1 hc k k.2
  have hwd : ∀ (k k' : K) (c c' : G), c ∈ Subgroup.centralizer (K : Set G) →
      c' ∈ Subgroup.centralizer (K : Set G) → (k : G) * c = k' * c' →
      (k : K ⧸ Subgroup.center K) = k' := by
    intro k k' c c' hc hc' heq
    rw [QuotientGroup.eq, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : (k : G)⁻¹ * k' = c * c'⁻¹ := by
      calc (k : G)⁻¹ * k' = (k : G)⁻¹ * (k' * c') * c'⁻¹ := by group
        _ = (k : G)⁻¹ * (k * c) * c'⁻¹ := by rw [heq]
        _ = c * c'⁻¹ := by group
    have h2 : (c * c'⁻¹) ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hc')
    have := Subgroup.mem_centralizer_iff.1 h2 g g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    exact this
  choose g c hc hg using hdec
  have h1 : (g 1 : K ⧸ Subgroup.center K) = 1 := by
    have := hwd (g 1) 1 (c 1) 1 (hc 1) (Subgroup.one_mem _) (by rw [← hg 1]; simp)
    simpa using this
  have hmul : ∀ y y' : G, (g (y * y') : K ⧸ Subgroup.center K) = g y * g y' := by
    intro y y'
    have := hwd (g (y * y')) (g y * g y') (c (y * y')) (c y * c y') (hc _)
      (Subgroup.mul_mem _ (hc y) (hc y')) (by
        rw [← hg (y * y'), Subgroup.coe_mul]
        calc y * y' = (g y * c y) * (g y' * c y') := by rw [← hg y, ← hg y']
          _ = g y * (c y * g y') * c y' := by group
          _ = g y * (g y' * c y) * c y' := by rw [← hcomm _ (hc y) (g y')]
          _ = g y * g y' * (c y * c y') := by group)
    simpa using this
  let f : G →* K ⧸ Subgroup.center K :=
    { toFun := fun y => (g y : K ⧸ Subgroup.center K), map_one' := h1, map_mul' := hmul }
  have hf : ∀ y, f y = (g y : K ⧸ Subgroup.center K) := fun y => rfl
  refine ⟨f, fun k => ?_, fun y => ?_⟩
  · rw [hf]
    have := hwd (g (k : G)) k (c (k : G)) 1 (hc _) (Subgroup.one_mem _) (by
      rw [← hg (k : G)]; simp)
    simpa using this
  · rw [hf]
    constructor
    · intro hy
      rw [QuotientGroup.eq_one_iff] at hy
      have hgy : (g y : G) ∈ Subgroup.centralizer (K : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun k hk =>
          congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨k, hk⟩)
      rw [hg y]
      exact Subgroup.mul_mem _ hgy (hc y)
    · intro hy
      have := hwd (g y) 1 (c y) y (hc y) hy (by rw [← hg y]; simp)
      simpa using this

theorem Setup.pCore_comm (h : Setup Y) {q e : Y} (hq : q ∈ CFSG.Open.pCore 2 Y)
    (he : e ∈ goldschmidtLayer Y) : q * e = e * q := by
  rw [openLayer_eq_layer] at he
  have hqF : q ∈ fittingSubgroup Y := by rw [fitting_eq_openPCore h.odd]; exact hq
  have hcomm : ⁅q, e⁆ ∈ ⁅fittingSubgroup Y, layer Y⁆ :=
    Subgroup.commutator_mem_commutator hqF he
  rw [CFSG.LocalCores.fitting_layer_commute (G := Y)] at hcomm
  have h1 : q * e * q⁻¹ * e⁻¹ = 1 := Subgroup.mem_bot.mp hcomm
  calc q * e = (q * e * q⁻¹ * e⁻¹) * (e * q) := by group
    _ = e * q := by rw [h1, one_mul]

theorem Setup.center_layer_le (h : Setup Y) {z : Y} (hz : z ∈ goldschmidtLayer Y)
    (hc : ∀ e ∈ goldschmidtLayer Y, z * e = e * z) : z ∈ CFSG.Open.pCore 2 Y := by
  rw [openLayer_eq_layer] at hz hc
  have hzc : (⟨z, hz⟩ : layer Y) ∈ Subgroup.center (layer Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  have hF : z ∈ fittingSubgroup Y :=
    CFSG.ComponentClassification.UnbalancedLayer.center_layer_le_fittingSubgroup
      (Subgroup.mem_map_of_mem _ hzc)
  rwa [fitting_eq_openPCore h.odd] at hF

theorem Setup.pCore_le_centralizer (h : Setup Y) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    CFSG.Open.pCore 2 Y ≤ Subgroup.centralizer (K : Set Y) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkE : k ∈ goldschmidtLayer Y := by
    rw [openLayer_eq_layer]; exact CFSG.LocalCores.component_le_layer hK hk
  exact (h.pCore_comm hq hkE).symm

theorem Setup.sup_centralizer_eq_top (h : Setup Y) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    K ⊔ Subgroup.centralizer (K : Set Y) = ⊤ := by
  have hE : goldschmidtLayer Y ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
    rw [openLayer_eq_layer]
    refine sSup_le fun K₂ hK₂ => ?_
    rcases CFSG.LocalCores.distinct_components_commute hK₂ hK with rfl | hne
    · exact le_sup_left
    · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hne)
  rw [eq_top_iff, ← h.sup]
  exact sup_le ((h.pCore_le_centralizer hK).trans le_sup_right) hE

theorem Setup.exists_proj (h : Setup Y) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    ∃ f : Y →* K ⧸ Subgroup.center K, (∀ k : K, f (k : Y) = (k : K ⧸ Subgroup.center K)) ∧
      ∀ y : Y, f y = 1 ↔ y ∈ Subgroup.centralizer (K : Set Y) :=
  exists_proj_of_sup_centralizer_eq_top K (h.sup_centralizer_eq_top hK)

theorem Setup.sylow_dec (h : Setup Y) {K : Subgroup Y} (hK : CFSG.IsComponent K)
    (S : Sylow 2 Y) {w : Y} (hw : w ∈ (S : Subgroup Y)) :
    ∃ k ∈ (S : Subgroup Y) ⊓ K, ∃ c ∈ (S : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y),
      w = k * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf1, hf2⟩ := h.exists_proj hK
  obtain ⟨S₀, hS₀⟩ := CFSG.GH74.Uniqueness.SU.K.R6.exists_sylow_component S hK
  let P₀ : Sylow 2 (K ⧸ Subgroup.center K) :=
    S₀.mapSurjective (f := QuotientGroup.mk' (Subgroup.center K)) (QuotientGroup.mk'_surjective _)
  have hP₀ : (P₀ : Subgroup (K ⧸ Subgroup.center K)) =
      (S₀ : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) S₀
  have hfS : IsPGroup 2 ((S : Subgroup Y).map f) := S.isPGroup'.map f
  have hle : (P₀ : Subgroup (K ⧸ Subgroup.center K)) ≤ (S : Subgroup Y).map f := by
    rw [hP₀]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(x : Y), (hS₀ x).1 hx, hf1 x⟩
  have heq := P₀.is_maximal' hfS hle
  have hfw : f w ∈ (P₀ : Subgroup (K ⧸ Subgroup.center K)) := heq ▸ ⟨w, hw, rfl⟩
  rw [hP₀] at hfw
  obtain ⟨x, hx, hxw⟩ := hfw
  have hxS : (x : Y) ∈ (S : Subgroup Y) := (hS₀ x).1 hx
  have hcK : (x : Y)⁻¹ * w ∈ Subgroup.centralizer (K : Set Y) := by
    rw [← hf2, map_mul, map_inv, hf1 x]
    change (x : K ⧸ Subgroup.center K)⁻¹ * f w = 1
    rw [← hxw]
    exact inv_mul_cancel _
  exact ⟨(x : Y), ⟨hxS, x.2⟩, (x : Y)⁻¹ * w,
    ⟨(S : Subgroup Y).mul_mem ((S : Subgroup Y).inv_mem hxS) hw, hcK⟩, by group⟩

theorem Setup.center_le_sylow (h : Setup Y) {K : Subgroup Y} (hK : CFSG.IsComponent K)
    (S : Sylow 2 Y) {z : Y} (hzK : z ∈ K) (hz : ∀ k ∈ K, z * k = k * z) :
    z ∈ (S : Subgroup Y) := by
  have hzE : z ∈ goldschmidtLayer Y := by
    rw [openLayer_eq_layer]; exact CFSG.LocalCores.component_le_layer hK hzK
  have hle : CFSG.layer Y ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine sSup_le fun K₂ hK₂ => ?_
    rcases CFSG.LocalCores.distinct_components_commute hK₂ hK with rfl | hne
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hz x hx).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hne hx)) z hzK).symm
  have hc : ∀ e ∈ goldschmidtLayer Y, z * e = e * z := by
    intro e he
    rw [openLayer_eq_layer] at he
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm
  exact openPCore_le_sylow S (h.center_layer_le hzE hc)

end CFSG.GH74.Uniqueness.SU.K.R4
