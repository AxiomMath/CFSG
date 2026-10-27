module

public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocal
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentNormalization
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces

public section

namespace CFSG.QuasithinUnique

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace EscapingComponents

theorem charTwo_map_subtype_of_isSubnormal {K : Subgroup G} (hK : CharTwo K) {Y : Subgroup K}
    (hY : Y.IsSubnormal) : CharTwo (Y.map K.subtype) := by
  induction hY with
  | top =>
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hK
  | step Y Z hYZ hZ hN ih =>
    refine ih.of_normal (Subgroup.map_mono hYZ) ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hYZ)]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYZ] at hN
    exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map _)

theorem charTwo_of_isSubnormal {K X : Subgroup G} (hK : CharTwo K) (hXK : X ≤ K)
    (hX : (X.subgroupOf K).IsSubnormal) : CharTwo X := by
  have := charTwo_map_subtype_of_isSubnormal hK hX
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK] at this

end EscapingComponents

theorem UniqueFusionDatum.escaping_component_central_involution {T M U : Subgroup G} {z : G}
    (hd : UniqueFusionDatum T M U z) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) {S : Subgroup G}
    (hS : IsSylowTwoOf S (Subgroup.centralizer ({u} : Set G))) (hUS : U ≤ S) {w : G}
    (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G))
    (hwC : Subgroup.centralizer ({w} : Set G) ≤ M) {L : Subgroup G}
    (hL : IsComponentIn L (Subgroup.centralizer ({u} : Set G))) :
    w ∈ Subgroup.normalizer (L : Set G) ∧ ⁅L, Subgroup.zpowers w⁆ = L ∧
      CFSG.oddCore L = ⊥ ∧ CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G)) := by
  obtain ⟨hodd, -, hnocomp⟩ := hd.escaping_centralizer_odd_core_components hu hu1 hH
  obtain ⟨-, hcharN, -, -⟩ := hd.escaping_centralizer_local_structure hu hu1 hH
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hHdef
  have hUH : U ≤ H := by
    intro a ha
    rw [hHdef, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hd.elem.1.is_comm.comm (⟨a, ha⟩ : U) ⟨u, hu⟩)
  have hUp : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hd.elem.2 x x.2)⟩
  have hwH : w ∈ H := hUH hwU
  have hwM : w ∈ M := hd.setting.le (hd.le_T hwU)
  have hLM : ¬ L ≤ M := by
    intro hle
    apply hnocomp _ hL.2
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL.1]
    exact hle
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let P : Sylow 2 H := hS2.toSylow hS.2.2
  have hcoreH : CFSG.pPrimeCore 2 H = ⊥ := by
    rw [← EscapingLocal.oddCore_eq_pPrimeCore]
    exact hodd
  have hwz : (⟨w, hwH⟩ : H) ∈ Subgroup.centralizer ((P : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hwS (y : G) (show (y : G) ∈ S from hy))
  have hwzS : (⟨w, hwH⟩ : H) ∈ (P : Subgroup H) := show w ∈ S from hUS hwU
  have hwnormH := central_sylow_normalizes_components hcoreH P hwz hwzS hL.2
  have hwL : w ∈ Subgroup.normalizer (L : Set G) := by
    have h2 : w ∈ (Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H)).map H.subtype :=
      ⟨_, hwnormH, rfl⟩
    rw [map_subtype_normalizer hL.1] at h2
    exact h2.2
  have hDL : ⁅L, Subgroup.zpowers w⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := (Subgroup.zpowers_le.mpr hwL) hy
    have h1 : y * x⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (L.inv_mem hx)
    have h2 : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact L.mul_mem hx h1
  have hDnorm : ((⁅L, Subgroup.zpowers w⁆ : Subgroup G).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr
      (Subgroup.normalizer_commutator_ge_left L _)
  have hQ : CFSG.IsQuasisimple L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.1
  have hcomm : ⁅L, Subgroup.zpowers w⁆ = L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hDnorm with htop | hcent
    · refine le_antisymm hDL fun x hx => ?_
      have : (⟨x, hx⟩ : L) ∈ (⁅L, Subgroup.zpowers w⁆ : Subgroup G).subgroupOf L :=
        htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hDcent : ⁅⁅L, Subgroup.zpowers w⁆, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro d hd'
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hdc : (⟨d, hDL hd'⟩ : L) ∈ Subgroup.center L :=
          hcent (show (⟨d, hDL hd'⟩ : L) ∈ (⁅L, Subgroup.zpowers w⁆ : Subgroup G).subgroupOf L
            from hd')
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hdc ⟨l, hl⟩)
      have h1 : ⁅L, Subgroup.zpowers w⁆ = ⊥ :=
        CFSG.LocalCores.perfect_double_commutator hQ.1 hDcent
      have h2 : L ≤ Subgroup.centralizer ({w} : Set G) := by
        intro x hx
        have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hx
        exact Subgroup.centralizer_le
          (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers w)) this
      exact hLM (h2.trans hwC)
  have hLodd : CFSG.oddCore L = ⊥ := by
    have h1 : CFSG.piCore {q : Nat.Primes | q.val ≠ 2} H = ⊥ := by
      rw [← CFSG.oddCore_eq_piCore]
      exact hodd
    have h2 := piCore_eq_bot_of_isSubnormal h1 hL.2.2
    rw [CFSG.oddCore_eq_piCore,
      ← CFSG.LocalCores.piCore_map_mulEquiv _ (Subgroup.subgroupOfEquivOfLe hL.1), h2,
      Subgroup.map_bot]
  have hzpH : Subgroup.zpowers w ≤ H ⊓ M := Subgroup.zpowers_le.mpr ⟨hwH, hwM⟩
  have hzpp : IsPGroup 2 (Subgroup.zpowers w) := hUp.to_le (Subgroup.zpowers_le.mpr hwU)
  have hK := hcharN.inf_centralizer hzpH hzpp
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hK
  have hXK : L ⊓ Subgroup.centralizer ({w} : Set G) ≤
      H ⊓ M ⊓ Subgroup.centralizer ({w} : Set G) :=
    fun x hx => ⟨⟨hL.1 hx.1, hwC hx.2⟩, hx.2⟩
  have hKH : H ⊓ M ⊓ Subgroup.centralizer ({w} : Set G) ≤ H := inf_le_left.trans inf_le_left
  have hsn : (L.subgroupOf (H ⊓ M ⊓ Subgroup.centralizer ({w} : Set G))).IsSubnormal := by
    have := hL.2.2.comap (Subgroup.inclusion hKH)
    rwa [Subgroup.comap_inclusion_subgroupOf] at this
  have hsn' : ((L ⊓ Subgroup.centralizer ({w} : Set G)).subgroupOf
      (H ⊓ M ⊓ Subgroup.centralizer ({w} : Set G))).IsSubnormal := by
    have heq : (L ⊓ Subgroup.centralizer ({w} : Set G)).subgroupOf
        (H ⊓ M ⊓ Subgroup.centralizer ({w} : Set G)) =
        L.subgroupOf (H ⊓ M ⊓ Subgroup.centralizer ({w} : Set G)) := by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩
    rw [heq]
    exact hsn
  exact ⟨hwL, hcomm, hLodd, EscapingComponents.charTwo_of_isSubnormal hK hXK hsn'⟩

end CFSG.QuasithinUnique
