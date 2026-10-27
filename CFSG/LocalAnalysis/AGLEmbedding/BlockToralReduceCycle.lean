module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTransport
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceOddMain
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCycle

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

namespace ToralReduce

variable {Y : Type} [Group Y] {L : Subgroup Y} {K : Type} [Field K]

theorem not_centralizer_le_projStabilizer_of_perfect {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {d : ℕ} (hd : d = 1 ∨ d = 2) {V : Subgroup (projectiveSL 3 K)}
    (hV : V ≤ projStabilizer (flagSpace 3 K d)) (hVp : ⁅V, V⁆ = V) {x : projectiveSL 3 K}
    (hxV : x ∈ V) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ¬ Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) ≤ projStabilizer (flagSpace 3 K d) := by
  rcases hd with rfl | rfl
  · exact LinearThreeKit.not_centralizer_le_projStabilizer_one_of_perfect hω1 hω3 hV hVp hxV
      hx3 hx1
  · exact LinearThreeKit.not_centralizer_le_projStabilizer_two_of_perfect hω1 hω3 hV hVp hxV
      hx3 hx1

theorem false_of_fix_of_cube_root [Finite Y] [Finite K] [CharP K 2] {J : Subgroup Y}
    (hCP : CompParab L J) (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K) {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) {u : Y}
    (huL : u ∈ L) (hu3 : u ^ 3 = 1) (huC : u ∉ Subgroup.centralizer (L : Set Y))
    (hjoin : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) : False := by
  obtain ⟨g, d, hd, hJ⟩ := exists_eq_map_conj_projStabilizer φ hCP
  have hJL := hCP.parab.1
  have hWL : perfectJoin J ≤ L := (perfectJoin_le J).trans hJL
  have hu' := hjoin
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hWL.trans (ToralCensus.le_normalizer_centralizer L))] at hu'
  obtain ⟨w, hw, c, hc, hwc⟩ := hu'
  have hcL : c ∈ L := by
    have := L.mul_mem (L.inv_mem (hWL hw)) huL
    rwa [← hwc, inv_mul_cancel_left] at this
  have hcZ : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc m m.2)
  have hπu : censusHom φ ⟨u, huL⟩ = censusHom φ ⟨w, hWL hw⟩ := by
    rw [censusHom_eq_iff]
    have : (⟨u, huL⟩ : ↥L)⁻¹ * ⟨w, hWL hw⟩ = (⟨c, hcL⟩ : ↥L)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hwc]
      group
    rw [this]
    exact (Subgroup.center ↥L).inv_mem hcZ
  set W := ((perfectJoin J).subgroupOf L).map (censusHom φ) with hWdef
  have hWp : ⁅W, W⁆ = W := by
    rw [hWdef, ← Subgroup.map_commutator, commutator_subgroupOf_eq hWL (perfectJoin_perfect J)]
  have hWJ : W ≤ (J.subgroupOf L).map (censusHom φ) :=
    Subgroup.map_mono fun a (ha : (a : Y) ∈ perfectJoin J) => (perfectJoin_le J ha : (a : Y) ∈ J)
  set c' := MulAut.conj g⁻¹
  set x := c' (censusHom φ ⟨u, huL⟩) with hxdef
  have hconj : ∀ y, y ∈ (J.subgroupOf L).map (censusHom φ) ↔
      c' y ∈ projStabilizer (flagSpace 3 K d) := by
    intro y
    rw [hJ]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hq' : c' ((MulAut.conj g).toMonoidHom q) = q := by
        simp only [c', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hq']
      exact hq
    · intro hy
      refine ⟨c' y, hy, ?_⟩
      simp [c', MulAut.conj_apply, mul_assoc]
  have hV : W.map c'.toMonoidHom ≤ projStabilizer (flagSpace 3 K d) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hconj y).mp (hWJ hy)
  have hVp : ⁅W.map c'.toMonoidHom, W.map c'.toMonoidHom⁆ = W.map c'.toMonoidHom := by
    rw [← Subgroup.map_commutator, hWp]
  have hxV : x ∈ W.map c'.toMonoidHom := ⟨_, by rw [hπu]; exact ⟨⟨w, hWL hw⟩, hw, rfl⟩, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    have hu3' : (⟨u, huL⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [hxdef, ← map_pow, ← map_pow, hu3', map_one, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply huC
    have h1 : censusHom φ ⟨u, huL⟩ = 1 := by
      rw [hxdef, map_eq_one_iff _ c'.injective] at h
      exact h
    rw [censusHom_eq_one_iff] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨l, hl⟩)
  have hC : Subgroup.centralizer ({x} : Set (projectiveSL 3 K)) ≤
      projStabilizer (flagSpace 3 K d) := by
    intro y hy
    have hy' := Subgroup.mem_centralizer_iff.mp hy x rfl
    obtain ⟨l, hl⟩ := censusHom_surjective φ (c'.symm y)
    have hcomm : censusHom φ (l * ⟨u, huL⟩ * l⁻¹) = censusHom φ ⟨u, huL⟩ := by
      rw [map_mul, map_mul, map_inv, hl]
      have := congrArg c'.symm hy'
      rw [map_mul, map_mul] at this
      rw [hxdef, MulEquiv.symm_apply_apply] at this
      rw [← this, mul_inv_cancel_right]
    have h3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
    have heq := eq_of_censusHom_eq_of_pow φ h3 (a := l * ⟨u, huL⟩ * l⁻¹) (b := ⟨u, huL⟩)
      (by
        rw [conj_pow, show (⟨u, huL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hu3),
          mul_one, mul_inv_cancel])
      (Subtype.ext (by simpa using hu3)) hcomm
    have hlJ : (l : Y) ∈ J := by
      apply hfix l l.2
      have h1 : (l : Y) * u * (l : Y)⁻¹ = u := by simpa using congrArg Subtype.val heq
      calc u * l * u⁻¹ = (l * u * (l : Y)⁻¹) * l * u⁻¹ := by rw [h1]
        _ = l := by group
    have := (hconj (censusHom φ l)).mp ⟨l, hlJ, rfl⟩
    rwa [hl, MulEquiv.apply_symm_apply] at this
  exact not_centralizer_le_projStabilizer_of_perfect hω1 hω3 hd hV hVp hxV hx3 hx1 hC

end ToralReduce

end CFSG.AGLEmbedding
