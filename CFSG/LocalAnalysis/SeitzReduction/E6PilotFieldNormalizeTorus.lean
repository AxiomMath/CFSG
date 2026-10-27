module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

local instance e6PilotFieldNormalizeTorusNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Triangular

variable {τ : Tag} {R : Type*} [CommRing R]

theorem isUpperTriangular_iff_raisesPos
    {A : Module.End R (RootModule τ R)} :
    IsUpperTriangular τ R A ↔ RaisesPos Label.position 0 A := by
  constructor
  · intro h a b hab
    rw [add_zero]
    by_cases hab' : a = b
    · rw [hab']
    · rcases Label.precedes_or_precedes hab' with h' | h'
      · exact (Label.position_lt_position h').le
      · exact absurd (h a b h') hab
  · intro h a b hba
    by_contra hne
    have h1 := h a b hne
    have h2 := Label.position_lt_position hba
    omega

theorem isUpperTriangular_of_mem_diagonalGroup {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ diagonalGroup) : IsUpperTriangular τ R (g : Module.End R (RootModule τ R)) := by
  intro a b hba
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hg b
  have hab : a ≠ b := fun h => Label.Precedes.irrefl b (h ▸ hba)
  rw [hc, Finsupp.smul_apply, Finsupp.single_eq_of_ne hab, smul_zero]

end Triangular

section Diagonal

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_mem_diagonalGroup
    (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ (diagonalGroup : Subgroup (ModGL τ K)) :=
  ⟨fun j => rootDiag_hVec a j, fun _ hα => ⟨rootChar a _, rootDiag_rootVec a hα⟩⟩


theorem mem_torusGroup_of_mem_adjointGroup_of_mem_diagonalGroup {g : ModGL τ K}
    (hgC : g ∈ adjointGroup τ K) (hgD : g ∈ (diagonalGroup : Subgroup (ModGL τ K))) :
    g ∈ torusGroup τ K := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hgC
  rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hg'
  obtain ⟨w, hw⟩ := hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hup : ∀ x ∈ borelGroup τ K, RaisesPos Label.position 0 (x : Module.End K (RootModule τ K)) :=
    fun x hx => isUpperTriangular_iff_raisesPos.1 (hTB.2.2.2.2.2.2.2.2.2.1 x hx)
  have hneq : n = b⁻¹ * (b * n * b') * b'⁻¹ := by group
  have hnU : IsUpperTriangular τ K (n : Module.End K (RootModule τ K)) := by
    rw [isUpperTriangular_iff_raisesPos, hneq, Units.val_mul, Units.val_mul]
    exact ((hup _ (inv_mem hb)).mul (isUpperTriangular_iff_raisesPos.1
      (isUpperTriangular_of_mem_diagonalGroup hgD))).mul (hup _ (inv_mem hb'))
  have hnT : n ∈ torusGroup τ K :=
    mem_torusGroup_of_isUpperTriangular (Subgroup.mem_sup_right (canonicalRep_mem_closure _ K w))
      hnU
  have hgB : b * n * b' ∈ borelGroup τ K :=
    mul_mem (mul_mem hb (Subgroup.mem_sup_left hnT)) hb'
  have hgB' : b * n * b' ∈
      (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hTB.2.2.2.2.1]
    exact hgB
  obtain ⟨h, hh, u, hu, hhu'⟩ := hgB'
  have hhu : h * u = b * n * b' := hhu'
  have huD : u ∈ (diagonalGroup : Subgroup (ModGL τ K)) := by
    have hue : u = h⁻¹ * (b * n * b') := by rw [← hhu]; group
    rw [hue]
    exact mul_mem (inv_mem (torusGroup_le_diagonalGroup hh)) hgD
  have hu1 := isUpperUnitriangular_of_mem (posUnipotent_le_posFiltration τ K hu)
  have hone : ∀ c : Label τ, (u : Module.End K (RootModule τ K)) (Finsupp.single c 1) =
      Finsupp.single c 1 := fun c => by
    obtain ⟨x, hx⟩ := exists_apply_single_of_mem_diagonalGroup huD c
    have h1 := hu1.1 c
    rw [hx, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h1
    rw [hx, h1, one_smul]
  have hueq : u = 1 := by
    refine Units.ext (rootModule_end_ext (fun j => ?_) (fun α hα => ?_))
    · exact hone (Sum.inl j)
    · rw [Units.val_one, Module.End.one_apply, rootVec_eq_single_of_isRoot hα]
      exact hone _
  rw [← hhu, hueq, mul_one]
  exact hh

theorem rootDiagUnit_mem_torusGroup_of_mem_adjointGroup (a : Fin τ.rank → Kˣ)
    (ha : rootDiagUnit τ a ∈ adjointGroup τ K) : rootDiagUnit τ a ∈ torusGroup τ K :=
  mem_torusGroup_of_mem_adjointGroup_of_mem_diagonalGroup ha (rootDiagUnit_mem_diagonalGroup a)

theorem leviTorus_inf_adjointGroup_le_torusGroup (J : Finset (Fin (Tag.rank .E6))) :
    leviTorus K J ⊓ adjointGroup .E6 K ≤ torusGroup .E6 K := by
  rintro g ⟨hgT, hgC⟩
  obtain ⟨b, -, rfl⟩ := mem_leviTorus.1 hgT
  exact rootDiagUnit_mem_torusGroup_of_mem_adjointGroup b hgC

end Diagonal

section Neighbour

variable {K : Type} [Field K]

theorem map_subtype_levi
    (N : E6Neighbour) :
    (N.levi K).map (adjointGroup .E6 K).subtype = rootSpan .E6 K (orthRoots N.root) := by
  rw [E6Neighbour.levi, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_E6 _)]

theorem mem_levi_of_coe_mem
    {N : E6Neighbour} {g : adjointGroup .E6 K}
    (h : (g : ModGL .E6 K) ∈ (N.levi K).map (adjointGroup .E6 K).subtype) : g ∈ N.levi K := by
  obtain ⟨y, hy, hyg⟩ := h
  rwa [show y = g from Subtype.ext hyg] at hy


theorem rootSubgroup_le_centralizer_corootLine {δ γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (h0 : iform δ γ = 0) :
    rootSubgroup .E6 K γ ≤ centralizer (corootLine K δ : Set (ModGL .E6 K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro t ht
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨a, rfl⟩ := mem_corootLine.1 ht
  have hconj := rootDiagUnit_conj_pinnedX (corootTuple δ a) hγ c
  rw [rootChar_corootTuple, h0, zpow_zero, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

theorem rootSpan_orthRoots_le_centralizer_torus (N : E6Neighbour) :
    rootSpan .E6 K (orthRoots N.root) ≤ centralizer (N.torus K : Set (ModGL .E6 K)) :=
  iSup₂_le fun _ hγ => rootSubgroup_le_centralizer_corootLine hγ.1 hγ.2

theorem levi_le_centralizer_torus (N : E6Neighbour) :
    (N.levi K).map (adjointGroup .E6 K).subtype ≤
      centralizer (N.torus K : Set (ModGL .E6 K)) := by
  rw [map_subtype_levi]
  exact rootSpan_orthRoots_le_centralizer_torus N

theorem coe_torus_sup_eq_mul (N : E6Neighbour) :
    ((N.torus K ⊔ rootSpan .E6 K (orthRoots N.root) : Subgroup (ModGL .E6 K)) :
        Set (ModGL .E6 K)) =
      (N.torus K : Set (ModGL .E6 K)) * (rootSpan .E6 K (orthRoots N.root) : Set (ModGL .E6 K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((le_centralizer_iff.1 (rootSpan_orthRoots_le_centralizer_torus N)).trans
      (centralizer_le_normalizer _))

end Neighbour

section Decomp

variable {k : Type} [Field k]


theorem coe_rep_mem_monomialSubgroup (N : E6Neighbour) :
    (N.rep k : ModGL .E6 k) ∈ monomialSubgroup .E6 k := by
  rw [E6Neighbour.coe_rep]
  refine Subgroup.mem_sup_right (list_prod_mem fun x hx => ?_)
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem rep_inv_mul_mul_rep_mem_torusGroup (N : E6Neighbour) {h : ModGL .E6 k}
    (hh : h ∈ torusGroup .E6 k) :
    (N.rep k : ModGL .E6 k)⁻¹ * h * (N.rep k : ModGL .E6 k) ∈ torusGroup .E6 k := by
  have hnorm := (triangular_borel_structure.{0, 0} .E6 k).2.2.2.2.2.2.2.2.2.2.1
  have hnM := coe_rep_mem_monomialSubgroup (k := k) N
  have h1 := hnorm.conj_mem ⟨h, Subgroup.mem_sup_left hh⟩ (mem_subgroupOf.2 hh)
    (⟨_, hnM⟩ : monomialSubgroup .E6 k)⁻¹
  rw [mem_subgroupOf] at h1
  simpa only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h1

theorem exists_eq_mul_of_mem_torusGroup [Finite k] [CharP k 2] (N : E6Neighbour)
    {h : ModGL .E6 k} (hh : h ∈ torusGroup .E6 k) :
    ∃ d₁ ∈ N.torus k, ∃ d₂ ∈ (N.levi k).map (adjointGroup .E6 k).subtype, h = d₁ * d₂ := by
  have hsq : ∀ t : kˣ, ∃ v : kˣ, v ^ 2 = t :=
    F4Pilot.exists_sq_eq_of_ringChar_eq_two (ringChar.eq k 2)
  have hhigh : ∀ h' ∈ torusGroup .E6 k, ∃ d₁ ∈ E6Neighbour.high.torus k,
      ∃ d₂ ∈ rootSpan .E6 k (orthRoots (highRoot .E6)), h' = d₁ * d₂ := by
    intro h' hh'
    have h1 := EPilot.torusGroup_le_highTorusLine_sup (Or.inl rfl) hsq hh'
    rw [perpRoots_eq_orthRoots, ← E6Neighbour.torus_high] at h1
    have h2 : h' ∈ ((E6Neighbour.high.torus k ⊔ rootSpan .E6 k (orthRoots (highRoot .E6)) :
        Subgroup (ModGL .E6 k)) : Set (ModGL .E6 k)) := h1
    rw [show highRoot .E6 = E6Neighbour.high.root from rfl, coe_torus_sup_eq_mul] at h2
    obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := h2
    exact ⟨d₁, hd₁, d₂, hd₂, he.symm⟩
  set n : ModGL .E6 k := (N.rep k : ModGL .E6 k) with hn
  obtain ⟨d₁, hd₁, d₂, hd₂, he⟩ := hhigh _ (rep_inv_mul_mul_rep_mem_torusGroup N hh)
  refine ⟨n * d₁ * n⁻¹, ?_, n * d₂ * n⁻¹, ?_, ?_⟩
  · rw [← E6Neighbour.map_conj_rep_torus_high N]
    exact ⟨d₁, hd₁, rfl⟩
  · rw [map_subtype_levi, ← image_weyl_orthRoots_highRoot N,
      ← map_conj_rep_rootSpan N fun γ hγ => hγ.1]
    exact ⟨d₂, hd₂, rfl⟩
  · have h1 : h = n * (n⁻¹ * h * n) * n⁻¹ := by group
    rw [h1, he]
    group

theorem exists_eq_mul_of_mem_leviTorus_inf [Finite k] [CharP k 2] (N : E6Neighbour)
    {J : Finset (Fin (Tag.rank .E6))} {d : ModGL .E6 k}
    (hd : d ∈ leviTorus k J ⊓ adjointGroup .E6 k) :
    ∃ d₁ ∈ N.torus k, ∃ d₂ ∈ (N.levi k).map (adjointGroup .E6 k).subtype, d = d₁ * d₂ :=
  exists_eq_mul_of_mem_torusGroup N (leviTorus_inf_adjointGroup_le_torusGroup J hd)

end Decomp

end CFSG.SeitzReduction.E6Pilot
