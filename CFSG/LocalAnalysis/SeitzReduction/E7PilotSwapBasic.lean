module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeConj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapPieces

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e7PilotSwapBasicNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Structure

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E7 K) (t : G)

structure SwapNeighbourIso (N : E7Neighbour) where
  Φ : N.levi K × N.levi K ≃* neighbourCore e N
  diag : ∀ x : N.levi K, ((Φ (x, x) : neighbourCore e N) : G) =
    ((e.symm (x : adjointGroup .E7 K) : L) : G)
  swap : ∀ x y : N.levi K, t * ((Φ (x, y) : neighbourCore e N) : G) * t⁻¹ =
    ((Φ (y, x) : neighbourCore e N) : G)

variable {e t}

@[expose] noncomputable def SwapNeighbourIso.flip {N : E7Neighbour}
    (h : SwapNeighbourIso e t N) : SwapNeighbourIso e t N where
  Φ := MulEquiv.prodComm.trans h.Φ
  diag x := h.diag x
  swap x y := h.swap y x

theorem SwapNeighbourIso.flip_apply {N : E7Neighbour} (h : SwapNeighbourIso e t N)
    (x y : N.levi K) : h.flip.Φ (x, y) = h.Φ (y, x) :=
  rfl

theorem SwapNeighbourIso.coe_injective {N : E7Neighbour} (h : SwapNeighbourIso e t N) :
    Function.Injective fun z : N.levi K × N.levi K => ((h.Φ z : neighbourCore e N) : G) :=
  Subtype.val_injective.comp h.Φ.injective

theorem SwapNeighbourIso.coe_apply_eq_mul {N : E7Neighbour} (h : SwapNeighbourIso e t N)
    (x y : N.levi K) :
    ((h.Φ (x, y) : neighbourCore e N) : G) =
      ((h.Φ (x, 1) : neighbourCore e N) : G) * ((h.Φ (1, y) : neighbourCore e N) : G) := by
  rw [← coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem SwapNeighbourIso.commute_apply_one_one_apply {N : E7Neighbour}
    (h : SwapNeighbourIso e t N) (x y : N.levi K) :
    Commute ((h.Φ (x, 1) : neighbourCore e N) : G) ((h.Φ (1, y) : neighbourCore e N) : G) := by
  have hc : Commute ((x, 1) : N.levi K × N.levi K) (1, y) := by
    change ((x, 1) : N.levi K × N.levi K) * (1, y) = (1, y) * (x, 1)
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  exact (hc.map h.Φ).map (neighbourCore e N).subtype

theorem SwapNeighbourIso.conj_apply_one {N : E7Neighbour} (h : SwapNeighbourIso e t N)
    (x : N.levi K) :
    t * ((h.Φ (x, 1) : neighbourCore e N) : G) * t⁻¹ = ((h.Φ (1, x) : neighbourCore e N) : G) :=
  h.swap x 1

theorem SwapNeighbourIso.apply_one_mul_one_apply {N : E7Neighbour}
    (h : SwapNeighbourIso e t N) (x : N.levi K) :
    ((h.Φ (x, 1) : neighbourCore e N) : G) * ((h.Φ (1, x) : neighbourCore e N) : G) =
      ((e.symm (x : adjointGroup .E7 K) : L) : G) := by
  rw [← h.coe_apply_eq_mul, h.diag]

theorem SwapNeighbourIso.map_conj_of_mem {N : E7Neighbour} (h : SwapNeighbourIso e t N)
    (y x x' : N.levi K) :
    ((h.Φ (y * x * y⁻¹, y * x' * y⁻¹) : neighbourCore e N) : G) =
      ((e.symm (y : adjointGroup .E7 K) : L) : G) * (h.Φ (x, x') : G) *
        ((e.symm (y : adjointGroup .E7 K) : L) : G)⁻¹ := by
  have : ((y * x * y⁻¹, y * x' * y⁻¹) : N.levi K × N.levi K) = (y, y) * (x, x') * (y, y)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, h.diag y]

theorem SwapNeighbourIso.map_conj_one_of_mem {N : E7Neighbour} (h : SwapNeighbourIso e t N)
    (y x : N.levi K) :
    ((h.Φ (y * x * y⁻¹, 1) : neighbourCore e N) : G) =
      ((e.symm (y : adjointGroup .E7 K) : L) : G) * (h.Φ (x, 1) : G) *
        ((e.symm (y : adjointGroup .E7 K) : L) : G)⁻¹ := by
  rw [← h.map_conj_of_mem y x 1, mul_one, mul_inv_cancel]

end Structure

section Factors

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G} {N : E7Neighbour}

@[expose] noncomputable def SwapNeighbourIso.fst (h : SwapNeighbourIso e t N)
    {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J →* G :=
  (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp
    ((MonoidHom.inl (N.levi K) (N.levi K)).comp (Subgroup.inclusion (levi_le_neighbourLevi hJ))))

@[expose] noncomputable def SwapNeighbourIso.snd (h : SwapNeighbourIso e t N)
    {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J →* G :=
  (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp
    ((MonoidHom.inr (N.levi K) (N.levi K)).comp (Subgroup.inclusion (levi_le_neighbourLevi hJ))))

variable (h : SwapNeighbourIso e t N) {I J : Finset (Fin (Tag.rank .E7))}

theorem SwapNeighbourIso.fst_apply (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J) :
    h.fst hJ x = ((h.Φ (⟨x, levi_le_neighbourLevi hJ x.2⟩, 1) : neighbourCore e N) : G) :=
  rfl

theorem SwapNeighbourIso.conj_fst (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J) :
    t * h.fst hJ x * t⁻¹ = h.snd hJ x :=
  h.conj_apply_one _

theorem SwapNeighbourIso.fst_mul_snd (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J) :
    h.fst hJ x * h.snd hJ x = ((e.symm (x : adjointGroup .E7 K) : L) : G) :=
  h.apply_one_mul_one_apply _

theorem SwapNeighbourIso.commute_fst_snd (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J) :
    Commute (h.fst hI x) (h.snd hJ y) :=
  h.commute_apply_one_one_apply _ _

theorem SwapNeighbourIso.fst_injective (hJ : J ⊆ N.nodes) : Function.Injective (h.fst hJ) :=
  fun _ _ hxy => Subtype.ext (congrArg (fun z : N.levi K × N.levi K => (z.1 : adjointGroup .E7 K))
    (h.coe_injective hxy))

theorem SwapNeighbourIso.fst_eq_of_coe_eq (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J)
    (hxy : (x : adjointGroup .E7 K) = y) : h.fst hI x = h.fst hJ y := by
  rw [h.fst_apply, h.fst_apply]
  exact congrArg (fun z => ((h.Φ (z, 1) : neighbourCore e N) : G)) (Subtype.ext hxy)

end Factors

section Transport

variable {K : Type} [Field K] {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

theorem conj_conj_comm_of_commute {M : Type*} [Group M] {t n : M} (htn : Commute t n) (a : M) :
    t * (n * a * n⁻¹) * t⁻¹ = n * (t * a * t⁻¹) * n⁻¹ := by
  have h1 : t * n = n * t := htn.eq
  have h2 : n⁻¹ * t⁻¹ = t⁻¹ * n⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, h1]
  calc t * (n * a * n⁻¹) * t⁻¹ = (t * n) * a * (n⁻¹ * t⁻¹) := by group
    _ = (n * t) * a * (t⁻¹ * n⁻¹) := by rw [h1, h2]
    _ = n * (t * a * t⁻¹) * n⁻¹ := by group

variable (e) in
@[expose] noncomputable def neighbourCoreRepEquiv (N : E7Neighbour) :
    ↥(neighbourCore e .high) ≃* ↥(neighbourCore e N) :=
  ((MulAut.conj ((e.symm (N.rep K) : L) : G)).subgroupMap
    (neighbourCore e .high)).trans (MulEquiv.subgroupCongr (neighbourCore_eq_map_conj e N).symm)

@[expose] noncomputable def SwapNeighbourIso.toNeighbour (h : SwapNeighbourIso e t .high)
    (N : E7Neighbour) (htn : Commute t ((e.symm (N.rep K) : L) : G)) : SwapNeighbourIso e t N where
  Φ := (((highLeviConjEquiv K N).symm.prodCongr (highLeviConjEquiv K N).symm).trans h.Φ).trans
    (neighbourCoreRepEquiv e N)
  diag x := by
    obtain ⟨x₀, rfl⟩ := (highLeviConjEquiv K N).surjective x
    change ((e.symm (N.rep K) : L) : G) *
        (h.Φ ((highLeviConjEquiv K N).symm (highLeviConjEquiv K N x₀),
          (highLeviConjEquiv K N).symm (highLeviConjEquiv K N x₀)) : G) *
          ((e.symm (N.rep K) : L) : G)⁻¹ =
      ((e.symm (N.rep K * (x₀ : adjointGroup .E7 K) * (N.rep K)⁻¹) : L) : G)
    rw [MulEquiv.symm_apply_apply, h.diag x₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul,
      L.coe_inv]
  swap x y := by
    change t * (((e.symm (N.rep K) : L) : G) *
        (h.Φ ((highLeviConjEquiv K N).symm x, (highLeviConjEquiv K N).symm y) : G) *
          ((e.symm (N.rep K) : L) : G)⁻¹) * t⁻¹ =
      ((e.symm (N.rep K) : L) : G) *
        (h.Φ ((highLeviConjEquiv K N).symm y, (highLeviConjEquiv K N).symm x) : G) *
          ((e.symm (N.rep K) : L) : G)⁻¹
    rw [conj_conj_comm_of_commute htn, h.swap]

theorem commute_symm_rep_of_mem_centralizer {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : E7Neighbour) : Commute t ((e.symm (N.rep K) : L) : G) :=
  (mem_centralizer_iff.1 ht _ (e.symm (N.rep K)).2).symm

end Transport

section Equivariance

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

theorem SwapNeighbourIso.commute_iff [Finite K] [CharP K 2] {N : E7Neighbour}
    (h : SwapNeighbourIso e t N) {d : adjointGroup .E7 K}
    (hd : (d : ModGL .E7 K) ∈ torusGroup .E7 K) (x y : N.levi K) :
    Commute ((h.Φ (x, y) : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .E7 K) : ModGL .E7 K) (d : ModGL .E7 K) ∧
        Commute ((y : adjointGroup .E7 K) : ModGL .E7 K) (d : ModGL .E7 K) := by
  obtain ⟨d₁, hd₁, d₂, ⟨x₂, hx₂, rfl⟩, he⟩ := exists_eq_mul_of_mem_torusGroup N hd
  simp only [Subgroup.coe_subtype] at he
  have hdd : d = ⟨d₁, N.torus_le_adjointGroup hd₁⟩ * x₂ := Subtype.ext he
  have hd₁G := symm_mem_modelToG e (x := ⟨d₁, N.torus_le_adjointGroup hd₁⟩) hd₁
  have hc₂ : Commute ((h.Φ (x, y) : neighbourCore e N) : G)
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) :=
    (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ (h.Φ (x, y)).2) _
      hd₁G).symm
  have hc₁ : ∀ z : N.levi K, Commute ((z : adjointGroup .E7 K) : ModGL .E7 K) d₁ := by
    intro z
    have hz : ((z : adjointGroup .E7 K) : ModGL .E7 K) ∈
        (N.levi K).map (adjointGroup .E7 K).subtype := ⟨z, z.2, rfl⟩
    exact (show Commute d₁ ((z : adjointGroup .E7 K) : ModGL .E7 K) from
      mem_centralizer_iff.1 (levi_le_centralizer_torus N hz) _ hd₁).symm
  have hdiag : ((e.symm x₂ : L) : G) =
      ((h.Φ (⟨x₂, hx₂⟩, ⟨x₂, hx₂⟩) : neighbourCore e N) : G) := (h.diag ⟨x₂, hx₂⟩).symm
  rw [he, F4Pilot.commute_mul_right_iff_of_commute (hc₁ x),
    F4Pilot.commute_mul_right_iff_of_commute (hc₁ y), hdd, map_mul, L.coe_mul,
    F4Pilot.commute_mul_right_iff_of_commute hc₂, hdiag, F4Pilot.commute_subtype_coe_iff]
  constructor
  · intro hc
    have hc' := hc.map h.Φ.symm.toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hc'
    exact ⟨congrArg (fun z : N.levi K × N.levi K => ((z.1 : adjointGroup .E7 K) : ModGL .E7 K))
      hc', congrArg (fun z : N.levi K × N.levi K => ((z.2 : adjointGroup .E7 K) : ModGL .E7 K))
      hc'⟩
  · rintro ⟨hxc, hyc⟩
    have hc : Commute ((x, y) : N.levi K × N.levi K) (⟨x₂, hx₂⟩, ⟨x₂, hx₂⟩) :=
      Prod.ext (Subtype.ext (Subtype.ext hxc)) (Subtype.ext (Subtype.ext hyc))
    exact hc.map h.Φ.toMonoidHom

end Equivariance

end CFSG.SeitzReduction.E7Pilot
