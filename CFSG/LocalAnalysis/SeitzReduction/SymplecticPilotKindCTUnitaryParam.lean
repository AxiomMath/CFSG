module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryRoots
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N : ℕ}
  {F : Type} [Field F]

structure CtuParam (ε : ℕ) (hε : ε ≤ 1) (σ : F ≃+* F) (ι : K →+* F) (hι : ∀ c, σ (ι c) = ι c)
    (e : L ≃* StatedSp N K) (k : Fin N) where
  Φ : ctuBlock σ ε ({k} : Finset (Fin N)) →* G
  ker_le : Φ.ker ≤ center (ctuBlock σ ε ({k} : Finset (Fin N)))
  range_eq : Φ.range = neighbourCore e k
  N1 : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ),
    Φ ⟨ctuEmbed ε hε σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ = ((e.symm y : L) : G)

variable {ε : ℕ} {hε : ε ≤ 1} {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}
  {e : L ≃* StatedSp N K}

@[expose] def CtuParamAgree (P : ∀ k : Fin N, CtuParam ε hε σ ι hι e k) : Prop :=
  ∀ (k l : Fin N) (x : SU σ (2 * N + ε)) (hx : x ∈ ctuBlock σ ε ({k} : Finset (Fin N)))
    (hx' : x ∈ ctuBlock σ ε ({l} : Finset (Fin N))), (P k).Φ ⟨x, hx⟩ = (P l).Φ ⟨x, hx'⟩

theorem CtuParam.N1' {k : Fin N} (P : CtuParam ε hε σ ι hι e k) {y : StatedSp N K}
    (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ) (x : ctuBlock σ ε ({k} : Finset (Fin N)))
    (hx : (x : SU σ (2 * N + ε)) = ctuEmbed ε hε σ ι hι y) : P.Φ x = ((e.symm y : L) : G) := by
  rw [← P.N1 y hy]
  congr 1
  exact Subtype.ext hx

end Param

section Pieces

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
  {hε : ε ≤ 1} {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c}
  {e : L ≃* StatedSp N K}

theorem CtuParam.mem_pieceCore (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hn3 : 3 ≤ 2 * N + ε) {k : Fin N} (P : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)
    (j : Fin ((2 * N + ε) / 2)) (hkj : k.val ≠ j.val) (hkj' : k.val ≠ j.val + 1)
    {x : SU (unitaryInvolution F 2 f) (2 * N + ε)}
    (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * N + ε)) j) :
    P.Φ ⟨x, rankOne_le_ctuBlock hε j hkj hkj' hx⟩ ∈
      pieceCore e ({⟨j.val, by omega⟩} : Finset (Fin N)) := by
  set R := rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
    (2 * N + ε)) j with hR
  have hRle : R ≤ ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N)) :=
    rankOne_le_ctuBlock hε j hkj hkj'
  set H : Subgroup (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))) :=
    R.subgroupOf _ with hH
  have hHmap : H.map (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype = R := by
    rw [hH, subgroupOf_map_subtype, inf_eq_left.mpr hRle]
  have hRperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.1 (isPerfect_rankOne hF hf hn3 j)
  have hHperf : ⁅H, H⁆ = H := by
    apply Subgroup.map_injective
      (ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))).subtype_injective
    rw [map_commutator, hHmap, hRperf]
  have hmem : (⟨x, hRle hx⟩ : ctuBlock (unitaryInvolution F 2 f) ε ({k} : Finset (Fin N))) ∈ H :=
    hx
  have hjN : j.val < N := by omega
  set j' : Fin N := ⟨j.val, hjN⟩ with hj'
  have hcent : H.map P.Φ ≤ centralizer (modelToG e (leviTorusSp K ({j'} : Finset (Fin N))) :
      Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨d, ⟨t, ht, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
    rw [diagSp_eq_rootTorusHom_mul t k, map_mul, Subgroup.coe_mul]
    have h1 : P.Φ z ∈ centralizer (modelToG e (rootTorusSp K k) : Set G) := by
      have : P.Φ z ∈ neighbourCore e k := P.range_eq ▸ ⟨z, rfl⟩
      exact F4Pilot.centralizerPerfectCore_le_centralizer _ this
    have h2 := mem_centralizer_iff.1 h1 _ (UnitaryPilot.symm_mem_modelToG e ⟨t k, rfl⟩)
    have hd := diagSp_update_mem_spBlock_compl (K := K) t k
    have h3 : ((e.symm (diagSp K N (Function.update t k 1)) : L) : G) =
        P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N (Function.update t k 1)),
          ctuEmbed_mem_ctuBlock_iff.2 hd⟩ := (P.N1 _ hd).symm
    have hzc : (z : SU (unitaryInvolution F 2 f) (2 * N + ε)) *
        ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N (Function.update t k 1)) =
        ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι (diagSp K N (Function.update t k 1)) * z := by
      have htj := (mem_leviTorusParam.1 ht) j' (Finset.mem_singleton_self j')
      by_cases hj : j.val + 1 < (2 * N + ε) / 2
      · refine commute_rankOne_short_ctuEmbed_diagSp hj ?_ hz
        have hk1 : (⟨j.val, by omega⟩ : Fin N) ≠ k := fun h => hkj (by rw [← h])
        have hk2 : (⟨j.val + 1, by omega⟩ : Fin N) ≠ k := fun h => hkj' (by rw [← h])
        rw [Function.update_of_ne hk1, Function.update_of_ne hk2]
        exact htj.1 (by simp only [hj']; omega)
      · refine commute_rankOne_last_ctuEmbed_diagSp hj ?_ hz
        have hk1 : (⟨j.val, by omega⟩ : Fin N) ≠ k := fun h => hkj (by rw [← h])
        rw [Function.update_of_ne hk1]
        exact htj.2 (by simp only [hj']; omega)
    have h4 : P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
        (diagSp K N (Function.update t k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ * P.Φ z =
        P.Φ z * P.Φ ⟨ctuEmbed ε hε (unitaryInvolution F 2 f) ι hι
          (diagSp K N (Function.update t k 1)), ctuEmbed_mem_ctuBlock_iff.2 hd⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hzc.symm
    rw [h3]
    calc ((e.symm (rootTorusHom K N k (t k)) : L) : G) * P.Φ ⟨_, _⟩ * P.Φ z
        = ((e.symm (rootTorusHom K N k (t k)) : L) : G) * (P.Φ z * P.Φ ⟨_, _⟩) := by
          rw [mul_assoc, h4]
      _ = P.Φ z * (((e.symm (rootTorusHom K N k (t k)) : L) : G) * P.Φ ⟨_, _⟩) := by
          rw [← mul_assoc, h2, mul_assoc]
  have hle : H.map P.Φ ≤ pieceCore e ({j'} : Finset (Fin N)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect hcent (by rw [← map_commutator, hHperf])
  exact hle ⟨_, hmem, rfl⟩

end Pieces

end CFSG.SeitzReduction.SymplecticPilot
