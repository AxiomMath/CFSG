module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUPKey
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUFinal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightUPRoot

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Universal.Symplectic.SpExtras (elt mat_elt E)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem exists_omega_eightU (hF : Nat.card F = (2 ^ 1) ^ 2) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  obtain ⟨ω, hω⟩ : ∃ ω : F, ω ∉ ({0, 1} : Finset F) := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => h x
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hF4] at h1
    have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  refine ⟨ω, hω.1, hω.2, ?_⟩
  have h := FiniteField.pow_card_sub_one_eq_one ω hω.1
  rwa [hF4] at h

@[expose] noncomputable def torusEightU (hF : Nat.card F = (2 ^ 1) ^ 2)
    (j : Fin ((2 * 4 + 0) / 2)) (hj : j.val + 1 < (2 * 4 + 0) / 2) (ω : F) :
    SU (unitaryInvolution F 2 1) (2 * 4 + 0) :=
  shortTorus (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) (lowIdx_ne_succ hj)
    (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _) ω

theorem coe_torusEightU (hF : Nat.card F = (2 ^ 1) ^ 2) (j : Fin ((2 * 4 + 0) / 2))
    (hj : j.val + 1 < (2 * 4 + 0) / 2) {ω : F} (hω0 : ω ≠ 0) :
    ((torusEightU hF j hj ω : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0))
      (Fin (2 * 4 + 0)) F) =
        diagonal (shortTorusFun (unitaryInvolution F 2 1) (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) ω) :=
  coe_shortTorus _ _ _ _ _ (lowIdx_ne_rev _ _) hω0

theorem torusEightU_pow_three (hF : Nat.card F = (2 ^ 1) ^ 2) (j : Fin ((2 * 4 + 0) / 2))
    (hj : j.val + 1 < (2 * 4 + 0) / 2) {ω : F} (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) :
    torusEightU hF j hj ω ^ 3 = 1 :=
  shortTorus_pow_three _ _ _ (lowIdx_ne_rev _ _) hω0 hω3

theorem barPow_torusEightU_ne (hF : Nat.card F = (2 ^ 1) ^ 2) (j : Fin ((2 * 4 + 0) / 2))
    (hj : j.val + 1 < (2 * 4 + 0) / 2) {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) :
    barPow (unitaryInvolution_involutive hF) true (torusEightU hF j hj ω) ≠
      torusEightU hF j hj ω := by
  intro h
  have h1 := congrArg (fun x : SU (unitaryInvolution F 2 1) (2 * 4 + 0) =>
    ((x : GL (Fin (2 * 4 + 0)) F) : Matrix (Fin (2 * 4 + 0)) (Fin (2 * 4 + 0)) F)
      (lowIdx j) (lowIdx j)) h
  rw [coe_barPow, Bool.cond_true, map_apply, coe_torusEightU hF j hj hω0, diagonal_apply_eq,
    shortTorusFun_left, unitaryInvolution_apply, pow_one] at h1
  apply hω1
  have h2 : ω * ω = ω * 1 := by rw [mul_one, ← pow_two, h1]
  exact mul_left_cancel₀ hω0 h2

theorem ne_ctuCoord_of_mem_ctuPlanes {N ε : ℕ} {R : Finset (Fin N)} {s : Fin (2 * N + ε)}
    (hs : s ∈ ctuPlanes ε R) {q : Fin N} (hq : q ∉ R) :
    s ≠ ctuCoord N ε (Sum.inl (Sum.inl q)) ∧ s ≠ ctuCoord N ε (Sum.inl (Sum.inr q)) := by
  constructor <;> rintro rfl <;> rw [ctuCoord_mem_ctuPlanes, inPlanes_inl] at hs <;> exact hq hs

theorem torusEightU_mem_ctuBlock (hF : Nat.card F = (2 ^ 1) ^ 2) (j : Fin ((2 * 4 + 0) / 2))
    (hj : j.val + 1 < (2 * 4 + 0) / 2) {ω : F} (hω0 : ω ≠ 0) {R : Finset (Fin 4)}
    (hR : ∀ q ∈ R, q.val ≠ j.val ∧ q.val ≠ j.val + 1) :
    torusEightU hF j hj ω ∈ ctuBlock (unitaryInvolution F 2 1) 0 R := by
  have hjN : j.val < 4 := by have := j.2; omega
  have hjN' : j.val + 1 < 4 := hj
  have h1 : (⟨j.val, hjN⟩ : Fin 4) ∉ R := fun h => (hR _ h).1 rfl
  have h2 : (⟨j.val + 1, hjN'⟩ : Fin 4) ∉ R := fun h => (hR _ h).2 rfl
  refine shortTorus_mem_ctuBlock _ _ _ (lowIdx_ne_rev _ _) hω0 fun s hs => ?_
  obtain ⟨a1, a2⟩ := ne_ctuCoord_of_mem_ctuPlanes hs h1
  obtain ⟨b1, b2⟩ := ne_ctuCoord_of_mem_ctuPlanes hs h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rwa [lowIdx_eq_ctuCoord hjN]
  · rwa [lowIdx_eq_ctuCoord (j := ⟨j.val + 1, hj⟩) hjN']
  · rwa [rev_lowIdx_eq_ctuCoord (Nat.zero_le 1) hjN]
  · rwa [rev_lowIdx_eq_ctuCoord (Nat.zero_le 1) (j := ⟨j.val + 1, hj⟩) hjN']

theorem commute_torusEightU_ctuEmbed (hF : Nat.card F = (2 ^ 1) ^ 2) {K : Type} [Field K]
    [CharP K 2] {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c}
    (j : Fin ((2 * 4 + 0) / 2)) (hj : j.val + 1 < (2 * 4 + 0) / 2) {ω : F} (hω0 : ω ≠ 0)
    (hω3 : ω ^ 3 = 1) {m : Fin 4} (hm : m.val = j.val ∨ m.val = j.val + 1) {y : StatedSp 4 K}
    (hy : y ∈ spBlock K ({m} : Finset (Fin 4))) :
    torusEightU hF j hj ω * ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι y =
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι y * torusEightU hF j hj ω := by
  have hσω : unitaryInvolution F 2 1 ω * ω = 1 := by
    rw [unitaryInvolution_apply, pow_one, ← pow_succ, hω3]
  refine commute_shortTorus_ctuEmbed _ _ _ (lowIdx_ne_rev _ _) hω0 hσω ?_ hy
  rcases hm with hm | hm
  · left
    intro s hs
    have h := eq_or_eq_rev_of_mem_ctuPlanes_singleton (Nat.zero_le 1) hs
    have he : ctuCoord 4 0 (Sum.inl (Sum.inl m)) = lowIdx (n := 2 * 4 + 0) j := Fin.ext hm
    rwa [he] at h
  · right
    intro s hs
    have h := eq_or_eq_rev_of_mem_ctuPlanes_singleton (Nat.zero_le 1) hs
    have he : ctuCoord 4 0 (Sum.inl (Sum.inl m)) =
        lowIdx (n := 2 * 4 + 0) (⟨j.val + 1, hj⟩ : Fin ((2 * 4 + 0) / 2)) := Fin.ext hm
    rwa [he] at h

end Torus

section Product

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F}
  {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp 4 K}

omit [Finite G] [Finite K] in
theorem commute_symm_rankOne_two (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k)
    {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (hd : torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω ∈
      ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4)))
    (hD : ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4))),
      (P 0).Φ ⟨torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω, hd⟩ *
          (P 2).Φ ⟨x, ctuBlock_pair_le_left _ 2 3 hx⟩ =
        (P 2).Φ ⟨x, ctuBlock_pair_le_left _ 2 3 hx⟩ *
          (P 0).Φ ⟨torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω, hd⟩)
    {s : StatedSp 4 K} (hs : s ∈ spBlock K ({0, 1} : Finset (Fin 4)))
    {y : SU (unitaryInvolution F 2 1) (2 * 4 + 0)}
    (hy : y ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF)
      (2 * 4 + 0)) ⟨2, by norm_num⟩)
    (hy0 : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4))) :
    ((e.symm s : L) : G) * (P 0).Φ ⟨y, hy0⟩ = (P 0).Φ ⟨y, hy0⟩ * ((e.symm s : L) : G) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨u, hu⟩ : ∃ u : G, u = ((e.symm s : L) : G) := ⟨_, rfl⟩
  rw [← hu]
  set M : Subgroup (SU (unitaryInvolution F 2 1) (2 * 4 + 0)) :=
    ((centralizer ({u} : Set G)).comap (P 0).Φ).map
      (ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4))).subtype with hM
  have hmemM : ∀ (z : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hz : z ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4))),
      (P 0).Φ ⟨z, hz⟩ * u = u * (P 0).Φ ⟨z, hz⟩ → z ∈ M := fun z hz h =>
    ⟨⟨z, hz⟩, mem_centralizer_singleton_iff.2 h, rfl⟩
  have hroot : ∀ (p p' : Fin 4) (hpp : p ≠ p'), p ∈ ({2, 3} : Finset (Fin 4)) →
      p' ∈ ({2, 3} : Finset (Fin 4)) →
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (elt (.difference p p' hpp) (1 : K)) ∈ M := by
    intro p p' hpp hp hp'
    have ht : elt (.difference p p' hpp) (1 : K) ∈ spBlock K ({2, 3} : Finset (Fin 4)) :=
      elt_difference_mem_spBlock hpp hp hp' 1
    have ht0 : elt (.difference p p' hpp) (1 : K) ∈ spBlock K ({0} : Finset (Fin 4))ᶜ :=
      spBlock_mono (by decide) ht
    refine hmemM _ (ctuEmbed_mem_ctuBlock_iff.2 ht0) ?_
    rw [(P 0).N1 _ ht0, hu, ← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul,
      (commute_of_mem_spBlock_of_disjoint (by decide) ht hs).eq]
  have hdM : torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω ∈ M := by
    refine hmemM _ hd ?_
    have hs23 : s ∈ spBlock K ({2, 3} : Finset (Fin 4))ᶜ := by
      have hc : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
      rw [hc]
      exact hs
    have hs2 : s ∈ spBlock K ({2} : Finset (Fin 4))ᶜ := spBlock_mono (by decide) hs23
    have hcs : ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι s ∈
        ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4)) :=
      ctuEmbed_mem_ctuBlock_iff.2 hs23
    have hu2 : u = (P 2).Φ ⟨ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι s,
        ctuBlock_pair_le_left _ 2 3 hcs⟩ := hu.trans ((P 2).N1 s hs2).symm
    rw [hu2]
    exact hD _ hcs
  have hL2 : rankOne (rootGroup (unitaryInvolution F 2 1) hσ (2 * 4 + 0))
      (⟨2, by norm_num⟩ : Fin ((2 * 4 + 0) / 2)) ≤ M := by
    refine rankOne_short_le_of_shortTorus hF4 (by norm_num) hω0 hω1 hdM ?_ ?_
    · have h := ctuEmbed_elt_difference_eq_rootHom (ε := 0) (hε := Nat.zero_le 1) (ι := ι)
        (hι := hι) hσ (by decide : (2 : Fin 4) ≠ 3) (Fin.ext rfl) (Fin.ext rfl)
        (lowIdx_ne_succ (n := 2 * 4 + 0) (k := ⟨2, by norm_num⟩) (by norm_num))
        (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (1 : K)
      rw [map_one] at h
      have h2 := hroot 2 3 (by decide) (by decide) (by decide)
      rw [h] at h2
      exact h2
    · have h := ctuEmbed_elt_difference_eq_rootHom (ε := 0) (hε := Nat.zero_le 1) (ι := ι)
        (hι := hι) hσ (by decide : (3 : Fin 4) ≠ 2) (Fin.ext rfl) (Fin.ext rfl)
        (lowIdx_ne_succ (n := 2 * 4 + 0) (k := ⟨2, by norm_num⟩) (by norm_num)).symm
        (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (1 : K)
      rw [map_one] at h
      have h2 := hroot 3 2 (by decide) (by decide) (by decide)
      rw [h] at h2
      exact h2
  obtain ⟨⟨y', hy'⟩, hy'C, hyy⟩ := hL2 hy
  have hyy' : (⟨y', hy'⟩ : ctuBlock (unitaryInvolution F 2 1) 0 ({0} : Finset (Fin 4))) =
      ⟨y, hy0⟩ := Subtype.ext hyy
  rw [hyy'] at hy'C
  exact (mem_centralizer_singleton_iff.1 hy'C).symm

omit [Finite G] [Finite K] in
theorem nsUniProductCommute_of_torus (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k)
    {ω : F} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (hd23 : torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω ∈
      ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4)))
    (hd01 : torusEightU hF ⟨0, by norm_num⟩ (by norm_num) ω ∈
      ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4)))
    (hD : ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4))),
      (P 0).Φ ⟨torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω,
          ctuBlock_pair_le_left _ 0 1 hd23⟩ * (P 2).Φ ⟨x, ctuBlock_pair_le_left _ 2 3 hx⟩ =
        (P 2).Φ ⟨x, ctuBlock_pair_le_left _ 2 3 hx⟩ *
          (P 0).Φ ⟨torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω,
            ctuBlock_pair_le_left _ 0 1 hd23⟩)
    (hE : ∀ (x : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hx : x ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4))),
      (P 2).Φ ⟨torusEightU hF ⟨0, by norm_num⟩ (by norm_num) ω,
          ctuBlock_pair_le_left _ 2 3 hd01⟩ * (P 0).Φ ⟨x, ctuBlock_pair_le_left _ 0 1 hx⟩ =
        (P 0).Φ ⟨x, ctuBlock_pair_le_left _ 0 1 hx⟩ *
          (P 2).Φ ⟨torusEightU hF ⟨0, by norm_num⟩ (by norm_num) ω,
            ctuBlock_pair_le_left _ 2 3 hd01⟩) :
    NsUniProductCommute hF P := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF4 : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, hF]; norm_num
  have hσ := unitaryInvolution_involutive hF
  intro x hx hx2 y hy hy0
  have hy1 : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({1} : Finset (Fin 4)) :=
    rankOne_le_ctuBlock (Nat.zero_le 1) (⟨2, by norm_num⟩ : Fin ((2 * 4 + 0) / 2)) (by decide)
      (by decide) hy
  have hy01 : y ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4)) := by
    have h := mem_ctuBlock_union hy0 hy1
    have hc : ({0} ∪ {1} : Finset (Fin 4)) = {0, 1} := by decide
    rwa [hc] at h
  set M : Subgroup (SU (unitaryInvolution F 2 1) (2 * 4 + 0)) :=
    ((centralizer ({(P 0).Φ ⟨y, hy0⟩} : Set G)).comap (P 2).Φ).map
      (ctuBlock (unitaryInvolution F 2 1) 0 ({2} : Finset (Fin 4))).subtype with hM
  have hmemM : ∀ (z : SU (unitaryInvolution F 2 1) (2 * 4 + 0))
      (hz : z ∈ ctuBlock (unitaryInvolution F 2 1) 0 ({2} : Finset (Fin 4))),
      (P 2).Φ ⟨z, hz⟩ * (P 0).Φ ⟨y, hy0⟩ = (P 0).Φ ⟨y, hy0⟩ * (P 2).Φ ⟨z, hz⟩ → z ∈ M :=
    fun z hz h => ⟨⟨z, hz⟩, mem_centralizer_singleton_iff.2 h, rfl⟩
  have hroot : ∀ (p p' : Fin 4) (hpp : p ≠ p'), p ∈ ({0, 1} : Finset (Fin 4)) →
      p' ∈ ({0, 1} : Finset (Fin 4)) →
      ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι
        (elt (.difference p p' hpp) (1 : K)) ∈ M := by
    intro p p' hpp hp hp'
    have ht : elt (.difference p p' hpp) (1 : K) ∈ spBlock K ({0, 1} : Finset (Fin 4)) :=
      elt_difference_mem_spBlock hpp hp hp' 1
    have ht2 : elt (.difference p p' hpp) (1 : K) ∈ spBlock K ({2} : Finset (Fin 4))ᶜ :=
      spBlock_mono (by decide) ht
    refine hmemM _ (ctuEmbed_mem_ctuBlock_iff.2 ht2) ?_
    rw [(P 2).N1 _ ht2]
    exact commute_symm_rankOne_two hF P hω0 hω1 (ctuBlock_pair_le_left _ 0 1 hd23) hD ht hy hy0
  have hdM : torusEightU hF ⟨0, by norm_num⟩ (by norm_num) ω ∈ M :=
    hmemM _ (ctuBlock_pair_le_left _ 2 3 hd01) (hE y hy01)
  have hL0 : rankOne (rootGroup (unitaryInvolution F 2 1) hσ (2 * 4 + 0))
      (⟨0, by norm_num⟩ : Fin ((2 * 4 + 0) / 2)) ≤ M := by
    refine rankOne_short_le_of_shortTorus hF4 (by norm_num) hω0 hω1 hdM ?_ ?_
    · have h := ctuEmbed_elt_difference_eq_rootHom (ε := 0) (hε := Nat.zero_le 1) (ι := ι)
        (hι := hι) hσ (by decide : (0 : Fin 4) ≠ 1) (Fin.ext rfl) (Fin.ext rfl)
        (lowIdx_ne_succ (n := 2 * 4 + 0) (k := ⟨0, by norm_num⟩) (by norm_num))
        (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (1 : K)
      rw [map_one] at h
      have h2 := hroot 0 1 (by decide) (by decide) (by decide)
      rw [h] at h2
      exact h2
    · have h := ctuEmbed_elt_difference_eq_rootHom (ε := 0) (hε := Nat.zero_le 1) (ι := ι)
        (hι := hι) hσ (by decide : (1 : Fin 4) ≠ 0) (Fin.ext rfl) (Fin.ext rfl)
        (lowIdx_ne_succ (n := 2 * 4 + 0) (k := ⟨0, by norm_num⟩) (by norm_num)).symm
        (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) (1 : K)
      rw [map_one] at h
      have h2 := hroot 1 0 (by decide) (by decide) (by decide)
      rw [h] at h2
      exact h2
  obtain ⟨⟨x', hx'⟩, hx'C, hxx⟩ := hL0 hx
  have hxx' : (⟨x', hx'⟩ : ctuBlock (unitaryInvolution F 2 1) 0 ({2} : Finset (Fin 4))) =
      ⟨x, hx2⟩ := Subtype.ext hxx
  rw [hxx'] at hx'C
  exact mem_centralizer_singleton_iff.1 hx'C

theorem nsUniProductCommute_even_of_swap (hK : Nat.card K = 2) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin 4, NsUniParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P)
    (hkey : ∀ (k l : Fin 4), k ≠ l → ∀ z ∈ centralizerPerfectCore
        (modelToG e (nsTorusSp K k ⊔ nsTorusSp K l)),
      ((e.symm (permSp K (Equiv.swap k l)) : L) : G) * z =
        z * ((e.symm (permSp K (Equiv.swap k l)) : L) : G)) :
    NsUniProductCommute hF P := by
  obtain ⟨ω, hω0, hω1, hω3⟩ := exists_omega_eightU hF
  have hd01 : torusEightU hF ⟨0, by norm_num⟩ (by norm_num) ω ∈
      ctuBlock (unitaryInvolution F 2 1) 0 ({2, 3} : Finset (Fin 4)) :=
    torusEightU_mem_ctuBlock hF _ _ hω0 (by decide)
  have hd23 : torusEightU hF ⟨2, by norm_num⟩ (by norm_num) ω ∈
      ctuBlock (unitaryInvolution F 2 1) 0 ({0, 1} : Finset (Fin 4)) :=
    torusEightU_mem_ctuBlock hF _ _ hω0 (by decide)
  refine nsUniProductCommute_of_torus hF P hω0 hω1 hd23 hd01 ?_ ?_
  · exact commute_overlap_of_torus hK hF P hagree (k := 2) (l := 3) (p := 0) (p' := 1)
      (by decide) (by decide) (by decide) (hkey 0 1 (by decide)) hd23
      (torusEightU_pow_three hF _ _ hω0 hω3)
      (commute_torusEightU_ctuEmbed hF _ _ hω0 hω3 (Or.inl rfl) (nsElt_mem_spBlock_singleton 2))
      (commute_torusEightU_ctuEmbed hF _ _ hω0 hω3 (Or.inr rfl) (nsElt_mem_spBlock_singleton 3))
      hd01 (barPow_torusEightU_ne hF _ _ hω0 hω1)
  · exact commute_overlap_of_torus hK hF P hagree (k := 0) (l := 1) (p := 2) (p' := 3)
      (by decide) (by decide) (by decide) (hkey 2 3 (by decide)) hd01
      (torusEightU_pow_three hF _ _ hω0 hω3)
      (commute_torusEightU_ctuEmbed hF _ _ hω0 hω3 (Or.inl rfl) (nsElt_mem_spBlock_singleton 0))
      (commute_torusEightU_ctuEmbed hF _ _ hω0 hω3 (Or.inr rfl) (nsElt_mem_spBlock_singleton 1))
      hd23 (barPow_torusEightU_ne hF _ _ hω0 hω1)

end Product

theorem spTwoUnitaryEvenEightProductInput_holds : SpTwoUnitaryEvenEightProductInput := by
  intro G _ _ L _ K _ _ _ hK e t _ _ _ hkey F _ _ _ hF ι hι P hagree
  exact nsUniProductCommute_even_of_swap hK hF P hagree hkey

section Reduction

theorem spTwoUnitaryEvenEightAgreeInput_holds : SpTwoUnitaryEvenEightAgreeInput :=
  spTwoUnitaryEvenEightAgreeInput_of_product spTwoUnitaryEvenEightProductInput_holds

end Reduction

end CFSG.SeitzReduction.SymplecticPilot
