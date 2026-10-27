module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3Cent
public import CFSG.ClassicalInvolution.Q3.TL4E3C269Gr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

theorem E3.oddCore_le_centralizer_of_alpha {G : Type} [Group G] {a b : G}
    (hα : alphaOf (Subgroup.closure ({a, b} : Set G)) = ⊥) (ha : a ≠ 1) :
    oddCoreOf (Subgroup.centralizer ({a} : Set G)) ≤ Subgroup.centralizer ({b} : Set G) := by
  have haA : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (Set.mem_insert a _)
  have hbA : b ∈ Subgroup.closure ({a, b} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have h1 : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), Subgroup.closure ({a, b} : Set G)⁆ ≤
      alphaOf (Subgroup.closure ({a, b} : Set G)) := by
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le a haA (le_iSup_of_le ha le_rfl)
  rw [hα, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (h1 hx) b hbA).symm

theorem E3.exists_sylow_le_centralizer_of_modOdd {G : Type} [Group G] [Finite G]
    {M N : Subgroup G} (hNodd : Odd (Nat.card N)) (hNM : N ≤ Subgroup.normalizer (M : Set G))
    {w : G} (hw2 : IsPGroup 2 (Subgroup.zpowers w)) (hwN : ∀ x ∈ N, w * x * w⁻¹ ∈ N)
    (htriv : ∀ x ∈ M, w * x * w⁻¹ * x⁻¹ ∈ N) :
    ∃ P : Subgroup G, IsSylow2In P M ∧ P ≤ Subgroup.centralizer ({w} : Set G) := by
  classical
  set H : Subgroup G := M ⊔ N with hHdef
  have hHM : H ≤ Subgroup.normalizer (M : Set G) := sup_le Subgroup.le_normalizer hNM
  have hwH : conjSub w H ≤ H := by
    show H.map (MulAut.conj w).toMonoidHom ≤ H
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · show w * x * w⁻¹ ∈ H
      have h1 : w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
      rw [h1]
      exact H.mul_mem (Subgroup.mem_sup_right (htriv x hx)) (Subgroup.mem_sup_left hx)
    · exact Subgroup.mem_sup_right (hwN x hx)
  have hwHe : conjSub w H = H :=
    Subgroup.eq_of_le_of_card_ge hwH (by rw [conjSub, Subgroup.card_map_of_injective
      (MulAut.conj w).injective])
  set H' : Subgroup G := H ⊔ Subgroup.zpowers w with hH'def
  have hH'N : H' ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr (mem_normalizer_of_conjSub_eq hwHe))
  obtain ⟨V, hV, hwV⟩ := IsSylow2In.exists_ge hw2 (le_sup_right : Subgroup.zpowers w ≤ H')
  have hVH := Sec6Gen.isSylow2In_inf_of_le_normalizer' hV le_sup_left hH'N
  have hVM := Sec6Gen.isSylow2In_inf_of_le_normalizer' hVH le_sup_left hHM
  refine ⟨V ⊓ H ⊓ M, hVM, fun x hx => ?_⟩
  have hxV : x ∈ V := hx.1.1
  have hxM : x ∈ M := hx.2
  have hwVm : w ∈ V := hwV (Subgroup.mem_zpowers w)
  have hc : w * x * w⁻¹ * x⁻¹ ∈ V ⊓ N :=
    ⟨V.mul_mem (V.mul_mem (V.mul_mem hwVm hxV) (V.inv_mem hwVm)) (V.inv_mem hxV), htriv x hxM⟩
  have hbot : V ⊓ N = ⊥ := by
    obtain ⟨k, hk⟩ := hV.2.1.exists_card_eq
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hNodd.not_two_dvd_nat)
  rw [hbot, Subgroup.mem_bot] at hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * w = (w * x * w⁻¹ * x⁻¹)⁻¹ * (w * x) := by group
    _ = w * x := by rw [hc, inv_one, one_mul]


section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.conjSub_image_orbOf (hF : E3Frame n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c '' orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J =
      orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J := by
  have hFam := hF.graphFam
  have hcK : conjSub c (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hF.large.datum.le_normalizer_core hc)
  have h1 := isMaxOrb_conj hFam hF.maxAdj.2 c
  rw [hcK] at h1
  exact maxOrb_unique hFam (CoreAssembly.mem_conjClass_self _) h1 hF.maxAdj.2

theorem E3Frame.conjSub_orbGen_core (hF : E3Frame n R S t J u) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    conjSub c (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J) =
      E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J := by
  have hcK : conjSub c (tightCore R) = tightCore R :=
    mem_normalizer_iff_conjSub_eq.mp (hF.large.datum.le_normalizer_core hc)
  have hcl := hF.large.datum.hypOmegaGen.conjInvariant
  rw [← E3.orbGen_conj hcl (CoreAssembly.mem_conjClass_self _) c, hcK]
  have h1 := orbOf_conj hF.graphFam.graph (tightCore R) J c
  rw [hcK, hF.conjSub_image_orbOf hc] at h1
  show (⨆ M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R)
    (conjSub c J), M) = ⨆ M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
      (tightCore R) J, M
  rw [h1]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
