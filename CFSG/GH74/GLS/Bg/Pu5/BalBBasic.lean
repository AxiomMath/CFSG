module

public import CFSG.GH74.GLS.Bg.Iii2.Basic

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Bg.Iii2 CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G]

theorem subnormal_of_isPCompIn {X M : Subgroup G} (hM : IsPCompIn 2 X M) :
    (M.subgroupOf X).IsSubnormal :=
  Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hM).2.1
    Subgroup.IsSubnormal.top

variable [Finite G]

theorem pPrimeCoreOf_le_of_isPCompIn {X M : Subgroup G} (hM : IsPCompIn 2 X M) :
    pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 X := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal (subnormal_of_isPCompIn hM)
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hM.1]
  exact Subgroup.map_mono h1

theorem inf_pPrimeCoreOf_le {M K : Subgroup G} (hMK : M ≤ K) :
    M ⊓ pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 M := by
  have hnorm : ((M ⊓ pPrimeCoreOf 2 K).subgroupOf M).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨M.mul_mem (M.mul_mem m.2 hx.1) (M.inv_mem m.2), ?_⟩
    have hmn : (m : G) ∈ normalizer (pPrimeCoreOf 2 K : Set G) :=
      TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer (hMK m.2))
    exact (Subgroup.mem_normalizer_iff.mp hmn _).mp hx.2
  have hodd : Odd (Nat.card ((M ⊓ pPrimeCoreOf 2 K).subgroupOf M)) := by
    have hcard : Nat.card ((M ⊓ pPrimeCoreOf 2 K).subgroupOf M) =
        Nat.card ↥(M ⊓ pPrimeCoreOf 2 K) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ pPrimeCoreOf 2 K ≤ M)).toEquiv
    rw [hcard]
    exact (TwoThin.card_pPrimeCoreOf_odd K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hle : (M ⊓ pPrimeCoreOf 2 K).subgroupOf M ≤ pPrimeCore 2 ↥M :=
    le_sSup ⟨hnorm, Nat.coprime_two_left.mpr hodd⟩
  intro g hg
  have hgM : g ∈ M := hg.1
  have hmem : (⟨g, hgM⟩ : ↥M) ∈ (M ⊓ pPrimeCoreOf 2 K).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hg
  exact ⟨⟨g, hgM⟩, hle hmem, rfl⟩

omit [Finite G] in
theorem commutator_mem_of_le_sSup {C N : Subgroup G} {y : G}
    (hN : ∀ g ∈ C, g ∈ normalizer (N : Set G)) {S : Set (Subgroup G)} (hS : ∀ M ∈ S, M ≤ C)
    (h : ∀ M ∈ S, ∀ m ∈ M, ⁅m, y⁆ ∈ N) : ∀ l ∈ sSup S, ⁅l, y⁆ ∈ N := by
  let A : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ⁅g, y⁆ ∈ N}
      one_mem' := ⟨one_mem _, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro g k ⟨hgC, hg⟩ ⟨hkC, hk⟩
        refine ⟨mul_mem hgC hkC, ?_⟩
        have e : ⁅g * k, y⁆ = g * ⁅k, y⁆ * g⁻¹ * ⁅g, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN g hgC) _).mp hk) hg
      inv_mem' := by
        rintro g ⟨hgC, hg⟩
        refine ⟨inv_mem hgC, ?_⟩
        have e : ⁅g⁻¹, y⁆ = g⁻¹ * (⁅g, y⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hN g⁻¹ (inv_mem hgC)) _).mp (inv_mem hg) }
  have hle : sSup S ≤ A := sSup_le fun M hM m hm => ⟨hS M hM hm, h M hM m hm⟩
  exact fun l hl => (hle hl).2

omit [Finite G] in
theorem rigidProduct_le_pLayerOf (b : G) :
    rigidProduct b ≤ pLayerOf 2 (centralizer ({b} : Set G)) :=
  sSup_le_sSup fun _ hK => rr_pcomp hK

theorem mem_cSec_of_mem_zStar_rigidProduct {b y : G} (hy : y ∈ zStar (rigidProduct b))
    {M : Subgroup G} (hM : IsPCompIn 2 (centralizer ({b} : Set G)) M) : y ∈ cSec M := by
  by_cases hrig : IsRigidRankOneComp b M
  · have hMK : M ≤ rigidProduct b := le_sSup hrig
    have hyL : y ∈ pLayerOf 2 (centralizer ({b} : Set G)) :=
      rigidProduct_le_pLayerOf b hy.1
    have hyN : y ∈ normalizer (M : Set G) := pLayerOf_le_normalizer hM hyL
    refine ⟨hyN, TwoThin.mem_normalizer_pPrimeCoreOf hyN, fun k hk => ?_⟩
    have h1 : ⁅k, y⁆ ∈ pPrimeCoreOf 2 (rigidProduct b) := hy.2.2.2 k (hMK hk)
    have h2 : ⁅k, y⁆ ∈ M := by
      have e : ⁅k, y⁆ = k * (y * k⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact M.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hyN k⁻¹).mp (M.inv_mem hk))
    exact inf_pPrimeCoreOf_le hMK ⟨h2, h1⟩
  · have hle : rigidProduct b ≤ cSec M :=
      sSup_le fun K hK => le_cSec_of_ne (rr_pcomp hK) hM (fun h => hrig (h ▸ hK))
    exact hle hy.1

theorem commutator_mem_pPrimeCoreOf_of_forall_mem_cSec {b y : G}
    (hy : ∀ M : Subgroup G, IsPCompIn 2 (centralizer ({b} : Set G)) M → y ∈ cSec M) :
    ∀ l ∈ pLayerOf 2 (centralizer ({b} : Set G)), ⁅l, y⁆ ∈ pPrimeCoreOf 2 (centralizer ({b} : Set G)) :=
  commutator_mem_of_le_sSup (fun _ hg => TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer hg))
    (fun _ hM => hM.1)
    (fun M hM m hm => pPrimeCoreOf_le_of_isPCompIn hM ((hy M hM).2.2 m hm))

end CFSG.GH74.GLS.Bg.Pu5
