module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Gen

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2 rankOne_eq_range)

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {x : G}

theorem exists_chart_of_chain (hq : 4 ≤ p ^ f) (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (ψ : SL(4, GaloisField p f) →* locQuot Ω x) {L : Fin 3 → Subgroup G}
    (hL : ∀ k, L k ∈ centralizingMembers Ω {x}) (hψ : ∀ k, locImg Ω x (L k) ≤ ψ.range)
    (hcomm : Commutes (L 0) (L 2))
    (hp01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 0) (L 1))
    (hp12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L 1) (L 2)) :
    ∃ Θ : SL(3 + 1, GaloisField p f) →* locQuot Ω x,
      Θ.ker ≤ Subgroup.center SL(3 + 1, GaloisField p f) ∧ Θ.range = ψ.range ∧
      Θ.range = ⨆ k, locImg Ω x (L k) ∧
      ∀ k : Fin 3, (blockSL2 (GaloisField p f) 3 k).range.map Θ = locImg Ω x (L k) := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  set H : Subgroup G := ⨆ k, L k with hHdef
  have hLle : ∀ k, L k ≤ H := fun k => le_iSup L k
  have hHlayer : H ≤ locLayer Ω x := iSup_le fun k => le_centralizingLayer (hL k)
  obtain ⟨Ψ₀, hsurj, -, hnodes⟩ := weakCT_recognition_nodes (GaloisField p f) p f hp.out hK hq
    (n := 3) (by omega) (X := ↥H) (U := fun k => (L k).subgroupOf H)
    (fun i j hij u hu v hv => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exact Subtype.ext (hcomm u (Subgroup.mem_subgroupOf.mp hu) v
        (Subgroup.mem_subgroupOf.mp hv)))
    (fun i j hij => by
      have hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W (L i) (L j) := by
        fin_cases i <;> fin_cases j <;> simp at hij
        · exact hp01
        · exact hp12
      obtain ⟨W, hW⟩ := hpair
      have hWle : W ≤ H := (linearBlockStandardPair_le_sup hW).trans (sup_le (hLle i) (hLle j))
      exact ⟨W.subgroupOf H, linearBlockStandardPair_subgroupOf hWle hW⟩)
    (iSup_subgroupOf_self L)
  let Ψ : SL(4, GaloisField p f) →* locQuot Ω x :=
    (locMk Ω x).comp ((Subgroup.inclusion hHlayer).comp Ψ₀)
  have hrange : Ψ.range = locImg Ω x H := by
    unfold locImg
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.map_top, Subgroup.inclusion_range]
  have hrange' : locImg Ω x H = ⨆ k, locImg Ω x (L k) :=
    locImg_iSup L fun k => le_centralizingLayer (hL k)
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hf, by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hqs : CFSG.IsQuasisimple SL(4, GaloisField p f) :=
    CFSG.ClassicalInvolution.ModelFacts.native_isQuasisimple
      (CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv .PSL 4 p f hp.out trivial hadm)
  have hΨker : Ψ.ker ≤ Subgroup.center SL(4, GaloisField p f) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hqs Ψ.ker with h | h
    · exact h
    · exfalso
      have hbot : Ψ.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨s, rfl⟩
        have : s ∈ Ψ.ker := h ▸ Subgroup.mem_top s
        simp [MonoidHom.mem_ker.mp this]
      have h0 : locImg Ω x (L 0) ≤ ⊥ := by
        rw [← hbot, hrange, hrange']
        exact le_iSup (fun k => locImg Ω x (L k)) 0
      exact locImg_ne_bot hΩ hex (hL 0) (le_bot_iff.mp h0)
  have hle : Ψ.range ≤ ψ.range := by
    rw [hrange, hrange']
    exact iSup_le hψ
  have : Group.IsPerfect SL(4, GaloisField p f) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have heq := range_eq_of_central_ker (card_center_sl4_le_four _) ψ Ψ hΨker hle
  refine ⟨Ψ, hΨker, heq, hrange.trans hrange', fun k => ?_⟩
  have hnode : ((blockSL2 (GaloisField p f) 3 k).range).map Ψ₀ = (L k).subgroupOf H := by
    rw [← rankOne_eq_range]
    exact hnodes k
  have hmap : ((L k).subgroupOf H).map (Subgroup.inclusion hHlayer) =
      (L k).subgroupOf (locLayer Ω x) := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hy
      exact ⟨⟨(y : G), hLle k (Subgroup.mem_subgroupOf.mp hy)⟩, Subgroup.mem_subgroupOf.mp hy,
        Subtype.ext rfl⟩
  unfold locImg
  show (((blockSL2 (GaloisField p f) 3 k).range).map ((locMk Ω x).comp
    ((Subgroup.inclusion hHlayer).comp Ψ₀))) = _
  rw [← Subgroup.map_map, ← Subgroup.map_map, hnode, hmap]

end CFSG.ClassicalInvolution.RouteD
