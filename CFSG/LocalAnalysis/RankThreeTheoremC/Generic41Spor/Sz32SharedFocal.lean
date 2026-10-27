module

import CFSG.LocalAnalysis.RankThreeTheoremC.D2FusionFocal3
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem sz32_shared_nilpotent_perfect_trivial {Q : Type*} [Group Q] (hQ : Group.IsNilpotent Q)
    (h : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) : (⊤ : Subgroup Q) = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hQ
  have key : ∀ m : ℕ, (⊤ : Subgroup Q).lowerCentralSeries m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Subgroup.lowerCentralSeries_succ, ih]; exact h
  rw [← key n, hn]

theorem sz32_shared_pindex_normal_eq_top {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [hfact : Fact p.Prime] {P' N' : Subgroup Γ} [N'.Normal] (hP' : ¬ p ∣ P'.index)
    (hcomm : P' ≤ ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆) {k : ℕ} (hk : N'.index = p ^ k) :
    N' = ⊤ := by
  let π : Γ →* Γ ⧸ N' := QuotientGroup.mk' N'
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N'
  have hπker : π.ker = N' := QuotientGroup.ker_mk' N'
  have hcard : Nat.card (Γ ⧸ N') = p ^ k := hk
  have hnil : Group.IsNilpotent (Γ ⧸ N') := (IsPGroup.of_card hcard).isNilpotent
  have himg : P'.map π = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have h1 : (P'.map π).index = (P' ⊔ N').index := by
      rw [← Subgroup.index_comap_of_surjective (P'.map π) hπsurj, Subgroup.comap_map_eq, hπker]
    have h2 : (P' ⊔ N').index ∣ P'.index := Subgroup.index_dvd_of_le le_sup_left
    have h4 : (P'.map π).index ∣ p ^ k := hcard ▸ Subgroup.index_dvd_card _
    have hnd : ¬ p ∣ (P'.map π).index := fun hd => hP' (hd.trans (h1 ▸ h2))
    have hcop : Nat.Coprime (P'.map π).index (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hfact.out).mpr hnd).symm
    exact Nat.Coprime.eq_one_of_dvd hcop h4
  have hQcomm : ⁅(⊤ : Subgroup (Γ ⧸ N')), (⊤ : Subgroup (Γ ⧸ N'))⁆ = ⊤ := by
    refine eq_top_iff.mpr ?_
    calc (⊤ : Subgroup (Γ ⧸ N')) = P'.map π := himg.symm
      _ ≤ (⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆).map π := Subgroup.map_mono hcomm
      _ = ⁅(⊤ : Subgroup Γ).map π, (⊤ : Subgroup Γ).map π⁆ := Subgroup.map_commutator _ _ π
      _ = ⁅(⊤ : Subgroup (Γ ⧸ N')), (⊤ : Subgroup (Γ ⧸ N'))⁆ := by
          rw [Subgroup.map_top_of_surjective π hπsurj]
  have htriv := sz32_shared_nilpotent_perfect_trivial hnil hQcomm
  rw [eq_top_iff]
  intro m _
  have h : π m ∈ (⊤ : Subgroup (Γ ⧸ N')) := trivial
  rw [htriv] at h
  rwa [Subgroup.mem_bot, ← MonoidHom.mem_ker, hπker] at h

theorem sz32_shared_P_le_commutator (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    (P : Subgroup G) ≤ ⁅M, M⁆ := by
  haveI : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  exact sylow_le_commutator_of_gamma_two hS hp hM (hU0 p hp P M hM)

theorem sz32_shared_oP_eq_self (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) :
    ∀ N : Subgroup G, N ≤ M → (N.subgroupOf M).Normal → (∃ k : ℕ, N.relIndex M = p ^ k) → N = M := by
  intro N hNM hNn ⟨k, hk⟩
  haveI hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPcomm := sz32_shared_P_le_commutator hS hU0 hp hM
  haveI : (N.subgroupOf M).Normal := hNn
  have hP'comm : (P : Subgroup G).subgroupOf M ≤ ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ := by
    intro x hx
    have hx' : (x : G) ∈ ⁅M, M⁆ := hPcomm hx
    have hmap : ⁅M, M⁆ = (⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆).map M.subtype := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  have hnd : ¬ p ∣ ((P : Subgroup G).subgroupOf M).index := fun hd =>
    P.not_dvd_index (hd.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  have htop : N.subgroupOf M = ⊤ :=
    sz32_shared_pindex_normal_eq_top (P' := (P : Subgroup G).subgroupOf M) hnd hP'comm hk
  apply le_antisymm hNM
  intro m hm
  have : (⟨m, hm⟩ : M) ∈ N.subgroupOf M := htop ▸ trivial
  exact this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
