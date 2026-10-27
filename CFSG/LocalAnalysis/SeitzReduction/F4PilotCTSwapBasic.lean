module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeExists

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotCTSwapBasicNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Structure


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .F4 K) (t : G)

structure SwapNeighbourIso (N : AmalgamNeighbour) where
  Φ : N.levi K × N.levi K ≃* neighbourCore e N
  diag : ∀ x : N.levi K, ((Φ (x, x) : neighbourCore e N) : G) =
    ((e.symm (x : adjointGroup .F4 K) : L) : G)
  swap : ∀ x y : N.levi K, t * ((Φ (x, y) : neighbourCore e N) : G) * t⁻¹ =
    ((Φ (y, x) : neighbourCore e N) : G)

variable {e t}

@[expose] noncomputable def SwapNeighbourIso.flip {N : AmalgamNeighbour}
    (h : SwapNeighbourIso e t N) : SwapNeighbourIso e t N where
  Φ := MulEquiv.prodComm.trans h.Φ
  diag x := h.diag x
  swap x y := h.swap y x

theorem SwapNeighbourIso.flip_apply {N : AmalgamNeighbour} (h : SwapNeighbourIso e t N)
    (x y : N.levi K) : h.flip.Φ (x, y) = h.Φ (y, x) :=
  rfl

theorem SwapNeighbourIso.coe_injective {N : AmalgamNeighbour} (h : SwapNeighbourIso e t N) :
    Function.Injective fun z : N.levi K × N.levi K => ((h.Φ z : neighbourCore e N) : G) :=
  Subtype.val_injective.comp h.Φ.injective

theorem SwapNeighbourIso.coe_apply_eq_mul {N : AmalgamNeighbour} (h : SwapNeighbourIso e t N)
    (x y : N.levi K) :
    ((h.Φ (x, y) : neighbourCore e N) : G) =
      ((h.Φ (x, 1) : neighbourCore e N) : G) * ((h.Φ (1, y) : neighbourCore e N) : G) := by
  rw [← coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem SwapNeighbourIso.commute_apply_one_one_apply {N : AmalgamNeighbour}
    (h : SwapNeighbourIso e t N) (x y : N.levi K) :
    Commute ((h.Φ (x, 1) : neighbourCore e N) : G) ((h.Φ (1, y) : neighbourCore e N) : G) := by
  have hc : Commute ((x, 1) : N.levi K × N.levi K) (1, y) := by
    change ((x, 1) : N.levi K × N.levi K) * (1, y) = (1, y) * (x, 1)
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  exact (hc.map h.Φ).map (neighbourCore e N).subtype

theorem SwapNeighbourIso.conj_apply_one {N : AmalgamNeighbour} (h : SwapNeighbourIso e t N)
    (x : N.levi K) :
    t * ((h.Φ (x, 1) : neighbourCore e N) : G) * t⁻¹ = ((h.Φ (1, x) : neighbourCore e N) : G) :=
  h.swap x 1

theorem SwapNeighbourIso.apply_one_mul_one_apply {N : AmalgamNeighbour}
    (h : SwapNeighbourIso e t N) (x : N.levi K) :
    ((h.Φ (x, 1) : neighbourCore e N) : G) * ((h.Φ (1, x) : neighbourCore e N) : G) =
      ((e.symm (x : adjointGroup .F4 K) : L) : G) := by
  rw [← h.coe_apply_eq_mul, h.diag]

end Structure

section Factors


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G} {N : AmalgamNeighbour}

@[expose] noncomputable def SwapNeighbourIso.fst (h : SwapNeighbourIso e t N)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J →* G :=
  (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp
    ((MonoidHom.inl (N.levi K) (N.levi K)).comp (Subgroup.inclusion (levi_le_neighbourLevi hJ))))

@[expose] noncomputable def SwapNeighbourIso.snd (h : SwapNeighbourIso e t N)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J →* G :=
  (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp
    ((MonoidHom.inr (N.levi K) (N.levi K)).comp (Subgroup.inclusion (levi_le_neighbourLevi hJ))))

variable (h : SwapNeighbourIso e t N) {I J : Finset (Fin (Tag.rank .F4))}

theorem SwapNeighbourIso.fst_apply (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.fst hJ x = ((h.Φ (⟨x, levi_le_neighbourLevi hJ x.2⟩, 1) : neighbourCore e N) : G) :=
  rfl

theorem SwapNeighbourIso.snd_apply (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.snd hJ x = ((h.Φ (1, ⟨x, levi_le_neighbourLevi hJ x.2⟩) : neighbourCore e N) : G) :=
  rfl

theorem SwapNeighbourIso.flip_fst (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.flip.fst hJ x = h.snd hJ x :=
  rfl

theorem SwapNeighbourIso.flip_snd (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.flip.snd hJ x = h.fst hJ x :=
  rfl

theorem SwapNeighbourIso.conj_fst (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    t * h.fst hJ x * t⁻¹ = h.snd hJ x :=
  h.conj_apply_one _

theorem SwapNeighbourIso.conj_snd (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    t * h.snd hJ x * t⁻¹ = h.fst hJ x :=
  h.swap 1 _

theorem SwapNeighbourIso.fst_mul_snd (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    h.fst hJ x * h.snd hJ x = ((e.symm (x : adjointGroup .F4 K) : L) : G) :=
  h.apply_one_mul_one_apply _

theorem SwapNeighbourIso.commute_fst_snd (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J) :
    Commute (h.fst hI x) (h.snd hJ y) :=
  h.commute_apply_one_one_apply _ _

theorem SwapNeighbourIso.fst_injective (hJ : J ⊆ N.nodes) : Function.Injective (h.fst hJ) :=
  fun _ _ hxy => Subtype.ext (congrArg (fun z : N.levi K × N.levi K => (z.1 : adjointGroup .F4 K))
    (h.coe_injective hxy))

theorem SwapNeighbourIso.snd_injective (hJ : J ⊆ N.nodes) : Function.Injective (h.snd hJ) :=
  fun _ _ hxy => Subtype.ext (congrArg (fun z : N.levi K × N.levi K => (z.2 : adjointGroup .F4 K))
    (h.coe_injective hxy))

theorem SwapNeighbourIso.fst_eq_of_coe_eq (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : (x : adjointGroup .F4 K) = y) : h.fst hI x = h.fst hJ y := by
  rw [h.fst_apply, h.fst_apply]
  exact congrArg (fun z => ((h.Φ (z, 1) : neighbourCore e N) : G)) (Subtype.ext hxy)

theorem SwapNeighbourIso.snd_eq_of_coe_eq (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : (x : adjointGroup .F4 K) = y) : h.snd hI x = h.snd hJ y := by
  rw [h.snd_apply, h.snd_apply]
  exact congrArg (fun z => ((h.Φ (1, z) : neighbourCore e N) : G)) (Subtype.ext hxy)

theorem SwapNeighbourIso.commute_fst (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : Commute (x : adjointGroup .F4 K) y) : Commute (h.fst hI x) (h.fst hJ y) := by
  have hc : Commute ((⟨x, levi_le_neighbourLevi hI x.2⟩ : N.levi K), (1 : N.levi K))
      (⟨y, levi_le_neighbourLevi hJ y.2⟩, 1) :=
    Prod.ext (Subtype.ext hxy.eq) rfl
  exact (hc.map h.Φ).map (neighbourCore e N).subtype

theorem SwapNeighbourIso.commute_snd (hI : I ⊆ N.nodes) (hJ : J ⊆ N.nodes)
    (x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup I)
    (y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J)
    (hxy : Commute (x : adjointGroup .F4 K) y) : Commute (h.snd hI x) (h.snd hJ y) := by
  have hc : Commute ((1 : N.levi K), (⟨x, levi_le_neighbourLevi hI x.2⟩ : N.levi K))
      (1, ⟨y, levi_le_neighbourLevi hJ y.2⟩) :=
    Prod.ext rfl (Subtype.ext hxy.eq)
  exact (hc.map h.Φ).map (neighbourCore e N).subtype

end Factors

section ToX'


variable {K : Type} [Field K] {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G}

@[expose] noncomputable def SwapNeighbourIso.toX' (h : SwapNeighbourIso e t .X)
    (htn : Commute t ((e.symm (n1242 K) : L) : G)) : SwapNeighbourIso e t .X' where
  Φ := ((((c3LeviConjEquiv K).symm.prodCongr (c3LeviConjEquiv K).symm).trans h.Φ).trans
    ((MulAut.conj ((e.symm (n1242 K) : L) : G)).subgroupMap (neighbourCore e .X))).trans
      (MulEquiv.subgroupCongr (neighbourCore_X'_eq_map_conj e).symm)
  diag x := by
    obtain ⟨x₀, rfl⟩ := (c3LeviConjEquiv K).surjective x
    change ((e.symm (n1242 K) : L) : G) *
        (h.Φ ((c3LeviConjEquiv K).symm (c3LeviConjEquiv K x₀),
          (c3LeviConjEquiv K).symm (c3LeviConjEquiv K x₀)) : G) *
          ((e.symm (n1242 K) : L) : G)⁻¹ =
      ((e.symm (n1242 K * (x₀ : adjointGroup .F4 K) * (n1242 K)⁻¹) : L) : G)
    rw [MulEquiv.symm_apply_apply, h.diag x₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul,
      L.coe_inv]
  swap x y := by
    have key := h.swap ((c3LeviConjEquiv K).symm x) ((c3LeviConjEquiv K).symm y)
    have h1 : t * ((e.symm (n1242 K) : L) : G) = ((e.symm (n1242 K) : L) : G) * t := htn.eq
    have e1 : ∀ a : G, t * (((e.symm (n1242 K) : L) : G) * a * ((e.symm (n1242 K) : L) : G)⁻¹) *
        t⁻¹ = ((e.symm (n1242 K) : L) : G) * (t * a * t⁻¹) * ((e.symm (n1242 K) : L) : G)⁻¹ :=
      fun a => by
        have h2 : ((e.symm (n1242 K) : L) : G)⁻¹ * t⁻¹ = t⁻¹ * ((e.symm (n1242 K) : L) : G)⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, h1]
        calc t * (((e.symm (n1242 K) : L) : G) * a * ((e.symm (n1242 K) : L) : G)⁻¹) * t⁻¹ =
            (t * ((e.symm (n1242 K) : L) : G)) * a * (((e.symm (n1242 K) : L) : G)⁻¹ * t⁻¹) := by
              group
          _ = (((e.symm (n1242 K) : L) : G) * t) * a * (t⁻¹ * ((e.symm (n1242 K) : L) : G)⁻¹) := by
              rw [h1, h2]
          _ = _ := by group
    exact (e1 _).trans (congrArg (fun z => ((e.symm (n1242 K) : L) : G) * z *
      ((e.symm (n1242 K) : L) : G)⁻¹) key)

theorem SwapNeighbourIso.toX'_apply (h : SwapNeighbourIso e t .X)
    (htn : Commute t ((e.symm (n1242 K) : L) : G)) (x y : AmalgamNeighbour.X'.levi K) :
    (((h.toX' htn).Φ (x, y) : neighbourCore e .X') : G) =
      ((e.symm (n1242 K) : L) : G) *
        (h.Φ ((c3LeviConjEquiv K).symm x, (c3LeviConjEquiv K).symm y) : G) *
          ((e.symm (n1242 K) : L) : G)⁻¹ :=
  rfl

end ToX'

section CommuteN


theorem commute_symm_n1242_of_mem_centralizer {K : Type} [Field K] {G : Type} [Group G]
    {L : Subgroup G} {e : L ≃* adjointGroup .F4 K} {t : G} (ht : t ∈ centralizer (L : Set G)) :
    Commute t ((e.symm (n1242 K) : L) : G) :=
  (mem_centralizer_iff.1 ht _ (e.symm (n1242 K)).2).symm

end CommuteN

end CFSG.SeitzReduction.F4Pilot
