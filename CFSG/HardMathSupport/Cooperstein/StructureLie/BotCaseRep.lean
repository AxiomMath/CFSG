module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

namespace TransvIrr

open Subgroup
open scoped commutatorElement
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV)
open CFSG.QuasithinUnique
open CFSG.Open (pCoreOf)
open CFSG.Quasithin (autOn)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (sup_le_normalizer_blockV le_normalizer_of_isWeakSBlock not_le_centralizer_blockV
    isQuasisimple_autOn quasithinGenFitting_autOn_sup)

theorem normal_gen' {G : Type} [Group G] [Finite G]
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {M' T : Subgroup G} {x : G} (hLM' : L ≤ M') (hM'M : M' ≤ L ⊔ S)
    (hTM' : T ≤ M') (hM'T : M' ≤ normalizer (T : Set G))
    (hCT : M' ⊓ centralizer (blockV S L : Set G) ≤ T) (hxT : x ∈ T)
    (hxn : x ∉ L ⊔ M' ⊓ centralizer (blockV S L : Set G)) : L ≤ T := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hMV := sup_le_normalizer_blockV S L
  have hTM : T ≤ L ⊔ S := hTM'.trans hM'M
  have hxM : x ∈ L ⊔ S := hTM hxT
  have hq := isQuasisimple_autOn hA hL hSL
  have hFit := quasithinGenFitting_autOn_sup hA hL hSL
  set V := blockV S L with hV
  set M := L ⊔ S with hM
  let ρ := Setup.rho V M hMV
  have hρ1 : ∀ a b : M, ρ a = ρ b → (a : G)⁻¹ * b ∈ M ⊓ centralizer (V : Set G) := by
    intro a b hab
    have : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact ⟨(a⁻¹ * b).2, (Setup.rho_eq_one_iff hMV _).mp this⟩
  have hcent : autOn M' V ⊓ centralizer (autOn L V : Set (MulAut V)) ≤ autOn L V := by
    have := CFSG.Quasithin.centralizer_quasithinGenFitting_le (autOn M V)
    rw [hFit] at this
    exact fun y hy => this ⟨CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le hM'M hy.1, hy.2⟩
  have htN : ρ ⟨x, hxM⟩ ∈ autOn T V :=
    (Setup.mem_autOn_iff_rho hMV hTM).mpr ⟨⟨x, hxM⟩, hxT, rfl⟩
  have htK : ρ ⟨x, hxM⟩ ∉ autOn L V := by
    intro hk
    obtain ⟨p, hpL, hρ⟩ := (Setup.mem_autOn_iff_rho hMV le_sup_left).mp hk
    have h2 := hρ1 p _ hρ
    apply hxn
    have hpM' : (p : G) ∈ M' := hLM' hpL
    have e : x = (p : G) * ((p : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hpL ⟨M'.mul_mem (M'.inv_mem hpM') (hTM' hxT), h2.2⟩
  have hle := le_of_mem_normal (H := autOn M' V) (K := autOn L V) (N := autOn T V)
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le hLM')
    (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le hTM')
    (CFSG.Quasithin.InternalSec.autOn_normal_of (hM'M.trans (sup_le Subgroup.le_normalizer hSL)))
    (CFSG.Quasithin.InternalSec.autOn_normal_of hM'T) hq hcent htN htK
  intro l hl
  have hmem := hle ((Setup.mem_autOn_iff_rho hMV le_sup_left).mpr
    ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, rfl⟩)
  obtain ⟨p, hpT, hρ⟩ := (Setup.mem_autOn_iff_rho hMV hTM).mp hmem
  have h2 := hρ1 p _ hρ
  have e : l = (p : G) * ((p : G)⁻¹ * l) := by group
  rw [e]
  exact T.mul_mem hpT (hCT ⟨M'.mul_mem (M'.inv_mem (hTM' hpT)) (hLM' hl), h2.2⟩)

theorem setting_of_transvection {G : Type} [Group G] [Finite G]
    {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {a : G} (haS : a ∈ S)
    (hcard : Nat.card ↥⁅blockV S L, zpowers a⁆ = 2)
    (hsn : a ∉ L ⊔ (L ⊔ S) ⊓ centralizer (blockV S L : Set G)) :
    Setting (L ⊔ zpowers a ⊔ (L ⊔ S) ⊓ centralizer (blockV S L : Set G)) L (blockV S L) a := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  have hMV := sup_le_normalizer_blockV S L
  have haM : a ∈ L ⊔ S := Subgroup.mem_sup_right haS
  have hq := isQuasisimple_autOn hA hL hSL
  have hnotCent := not_le_centralizer_blockV hA hL hSL
  have hcomm : ∀ v ∈ blockV S L, ∀ w ∈ blockV S L, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val
      ((CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).1.is_comm.comm
        ⟨v, hv⟩ ⟨w, hw⟩)
  set V := blockV S L with hV
  set M := L ⊔ S with hM
  set M₀ := L ⊔ zpowers a ⊔ M ⊓ centralizer (V : Set G) with hM₀
  have hM₀M : M₀ ≤ M :=
    sup_le (sup_le le_sup_left (zpowers_le.mpr haM)) inf_le_left
  have hM₀C : M₀ ⊓ centralizer (V : Set G) = M ⊓ centralizer (V : Set G) :=
    le_antisymm (fun x hx => ⟨hM₀M hx.1, hx.2⟩) (le_inf le_sup_right inf_le_right)
  let ρ := Setup.rho V M hMV
  have hρ1 : ∀ a b : M, ρ a = ρ b → (a : G)⁻¹ * b ∈ M ⊓ centralizer (V : Set G) := by
    intro a b hab
    have : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact ⟨(a⁻¹ * b).2, (Setup.rho_eq_one_iff hMV _).mp this⟩
  have hK : autOn L V = (L.subgroupOf M).map ρ := by
    ext x
    rw [Setup.mem_autOn_iff_rho hMV le_sup_left, Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  have hperfK : ⁅autOn L V, autOn L V⁆ = autOn L V := Subgroup.isPerfect_iff.mp hq.1
  refine ⟨hM₀M.trans hMV, hcomm, hM₀M.trans (sup_le Subgroup.le_normalizer hSL),
    le_sup_left.trans le_sup_left,
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)), hcard, ?_,
    hnotCent, ?_, ?_⟩
  · rw [hM₀C]
  · rw [hM₀C]
    intro l hl
    have hmem : ρ ⟨l, Subgroup.mem_sup_left hl⟩ ∈ autOn L V :=
      (Setup.mem_autOn_iff_rho hMV le_sup_left).mpr ⟨⟨l, Subgroup.mem_sup_left hl⟩, hl, rfl⟩
    rw [← hperfK, hK, ← Subgroup.map_commutator] at hmem
    obtain ⟨a', ha', hρa⟩ := hmem
    have hsub : ⁅L.subgroupOf M, L.subgroupOf M⁆ ≤ (⁅L, L⁆ : Subgroup G).subgroupOf M :=
      commutator_le.mpr fun p hp q hq' => by
        show ((⁅p, q⁆ : M) : G) ∈ ⁅L, L⁆
        have : ((⁅p, q⁆ : M) : G) = ⁅(p : G), (q : G)⁆ := rfl
        rw [this]
        exact commutator_mem_commutator hp hq'
    have haL : (a' : G) ∈ ⁅L, L⁆ := hsub ha'
    have h2 := hρ1 a' _ hρa
    have e : l = (a' : G) * ((a' : G)⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem_sup haL h2
  · intro T hTM hMT hCT hsT
    refine normal_gen' hX hA hL (M' := M₀) (le_sup_left.trans le_sup_left) hM₀M hTM hMT hCT hsT ?_
    rw [hM₀C]; exact hsn

end TransvIrr

end CFSG.HardMathSupport.Cooperstein.StructureLie
