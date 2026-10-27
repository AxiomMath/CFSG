module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeLayer
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeBig
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Inner

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G]

theorem eq_or_eq_barM_of_layer {M X W : Subgroup G} (hXW : X ≤ W) (hWM : W ≤ M) {g : G}
    (hgM : g ∈ M) (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (hlay : ∀ Y : Subgroup G, X ≤ Y → Y ≤ W → g ∈ Subgroup.normalizer (Y : Set G) →
      Y = X ∨ Y = W)
    {Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hXY : barM M X ≤ Y₀) (hYW : Y₀ ≤ barM M W)
    (hgY₀ : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      Subgroup.normalizer (Y₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Y₀ = barM M X ∨ Y₀ = barM M W := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Y₁ : Subgroup G := W ⊓ (Y₀.comap mk).map M.subtype with hY₁
  have hgY₁ : g ∈ Subgroup.normalizer (Y₁ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hgW, Subgroup.le_normalizer_map M.subtype
      (Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer_comap mk hgY₀))⟩
  have hmem : ∀ (x : G) (hx : x ∈ W), x ∈ Y₁ ↔ mk ⟨x, hWM hx⟩ ∈ Y₀ := by
    intro x hx
    refine ⟨fun h => ?_, fun h => ⟨hx, ⟨x, hWM hx⟩, h, rfl⟩⟩
    obtain ⟨m, hm, hmx⟩ := h.2
    have : m = ⟨x, hWM hx⟩ := Subtype.ext hmx
    rw [← this]
    exact hm
  have hXY₁ : X ≤ Y₁ := fun x hx =>
    (hmem x (hXW hx)).mpr (hXY ⟨⟨x, hWM (hXW hx)⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have hY₁eq : barM M Y₁ = Y₀ := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
      have hxY : x ∈ Y₁ := Subgroup.mem_subgroupOf.mp hx
      exact (hmem x hxY.1).mp hxY
    · intro y hy
      obtain ⟨⟨x, hxM⟩, hx, rfl⟩ := hYW hy
      have hxW : x ∈ W := Subgroup.mem_subgroupOf.mp hx
      exact ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr ((hmem x hxW).mpr hy), rfl⟩
  rcases hlay Y₁ hXY₁ inf_le_left hgY₁ with h | h
  · left
    rw [← hY₁eq, h]
  · right
    rw [← hY₁eq, h]

variable [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem le_centralizer_threeComponents_of_pair_G (hKB : KFactBlockThreeCentCoprime)
    (h3 : D1PhaseThree 3 P M H R) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {z : G} (hzM : z ∈ M)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥)
    (hzb3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) ^ 3 = 1)
    {X W : Subgroup G} {t : G} (hXW : X ≤ W)
    (hWCM : W ≤ Subgroup.centralizer ({z} : Set G) ⊓ M) (hW3 : IsPGroup 3 W)
    (hW6 : Nat.card W = 3 ^ 6) (hX9 : Nat.card X = 3 ^ 2)
    (hcen : ∀ x ∈ X, ∀ w ∈ W, x * w = w * x) (hXder : X ≤ ⁅W, W⁆)
    (htCM : t ∈ Subgroup.centralizer ({z} : Set G) ⊓ M)
    (htW : t ∈ Subgroup.normalizer (W : Set G)) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (ht6 : Nat.Coprime 6 (orderOf t)) (hnt : ∃ u ∈ W, t * u * t⁻¹ * u⁻¹ ∉ X)
    (hlay : ∀ Y : Subgroup G, X ≤ Y → Y ≤ W → t ∈ Subgroup.normalizer (Y : Set G) →
      Y = X ∨ Y = W)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3d : ¬ Nat.Coprime 3 (Nat.card Lb)) :
    barM M X ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hWM : W ≤ M := fun w hw => (hWCM hw).2
  have hXM : X ≤ M := hXW.trans hWM
  have htM : t ∈ M := htCM.2
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hAW : barM M X ≤ barM M W := Subgroup.map_mono (Subgroup.comap_mono hXW)
  have hAc : ∀ a ∈ barM M X, ∀ w ∈ barM M W, a * w = w * a := by
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩ _ ⟨⟨w, hwM⟩, hw, rfl⟩
    have h : (⟨x, hxM⟩ : M) * ⟨w, hwM⟩ = ⟨w, hwM⟩ * ⟨x, hxM⟩ :=
      Subtype.ext (hcen x (Subgroup.mem_subgroupOf.mp hx) w (Subgroup.mem_subgroupOf.mp hw))
    rw [← map_mul, ← map_mul, h]
  have hAder : barM M X ≤ ⁅barM M W, barM M W⁆ :=
    (barM_commutator hWM) ▸ Subgroup.map_mono (Subgroup.comap_mono hXder)
  have hidx : 4 ≤ (barM M X).relIndex (barM M W) := by
    have h1 := Subgroup.card_mul_index ((barM M X).subgroupOf (barM M W))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv,
      card_barM_of_isPGroup Nat.prime_three (by norm_num) hWM hW3,
      card_barM_of_isPGroup Nat.prime_three (by norm_num) hXM (hW3.to_le hXW), hW6, hX9] at h1
    have h2 : 9 * ((barM M X).subgroupOf (barM M W)).index = 729 := by
      have e1 : (3 : ℕ) ^ 2 = 9 := by norm_num
      have e2 : (3 : ℕ) ^ 6 = 729 := by norm_num
      rw [e1, e2] at h1
      exact h1
    show 4 ≤ ((barM M X).subgroupOf (barM M W)).index
    omega
  have ht6' : Nat.Coprime 6 (orderOf (mk ⟨t, htM⟩)) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_map_dvd mk _) ?_
    rw [← Subgroup.orderOf_coe]
    exact ht6
  have hnt' : ∃ w ∈ barM M W, mk ⟨t, htM⟩ * w * (mk ⟨t, htM⟩)⁻¹ * w⁻¹ ∉ barM M X := by
    obtain ⟨u, hu, hut⟩ := hnt
    refine ⟨mk ⟨u, hWM hu⟩, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu), ?_⟩
    rintro ⟨⟨x, hxM⟩, hx, hxe⟩
    have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hcW : t * u * t⁻¹ * u⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp htW u).mp hu) (W.inv_mem hu)
    apply hut
    have := eq_of_mk_eq_three hWM hW3 (hXW hxX) hcW (by
      rw [hxe]
      simp only [← map_mul, ← map_inv]
      rfl)
    rw [← this]
    exact hxX
  exact hAW.trans (le_centralizer_threeComponents_of_pair hKB h3 h85 h93 hD2 hB3 hrank hperf hzb3
    hZ hAW hAc hAder hidx ht6'
    (mk_mem_centralizer_of_commute htM hzM (Subgroup.mem_centralizer_singleton_iff.mp htCM.1))
    (mem_normalizer_barM htM htW) (mem_normalizer_barM htM htX) hnt'
    (fun Y₀ hXY hYW htY => eq_or_eq_barM_of_layer hXW hWM htM htW hlay hXY hYW htY) hLb h3d)

end CFSG.AGLEmbedding
