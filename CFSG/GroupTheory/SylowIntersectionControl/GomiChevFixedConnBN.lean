module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevFixedLink
public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.GroupTheory.TitsSystem.FixedChambers
import CFSG.GroupTheory.TitsSystem.Atoms
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.GH74.BNPair Subgroup
open scoped Pointwise

private lemma map_map_of_coe {G : Type} [Group G] {L I : Subgroup G} (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    (γ : ↥I) (H : Subgroup ↥L) :
    (H.map (φ γ).toMonoidHom).map L.subtype =
      (H.map L.subtype).map (MulAut.conj (γ : G)).toMonoidHom := by
  have hcomp : L.subtype.comp (φ γ).toMonoidHom =
      (MulAut.conj (γ : G)).toMonoidHom.comp L.subtype := by
    ext x
    exact hφ γ x
  rw [Subgroup.map_map H L.subtype (φ γ).toMonoidHom,
    Subgroup.map_map H (MulAut.conj (γ : G)).toMonoidHom L.subtype, hcomp]

private lemma map_sylow_eq_self_of_invariant {G : Type} [Group G] {L I : Subgroup G}
    (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    (P : Sylow 2 ↥L)
    (hP : I ≤ normalizer (((P : Subgroup ↥L).map L.subtype : Subgroup G) : Set G))
    (γ : ↥I) : (P : Subgroup ↥L).map (φ γ).toMonoidHom = P := by
  have hmain : ((P : Subgroup ↥L).map (φ γ).toMonoidHom).map L.subtype =
      (P : Subgroup ↥L).map L.subtype := by
    rw [map_map_of_coe φ hφ γ (P : Subgroup ↥L)]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP γ.2)
  exact Subgroup.map_injective L.subtype_injective hmain

private lemma map_sylow_eq_self {G : Type} [Group G] {L I U : Subgroup G} {Q : Sylow 2 ↥L}
    (hQU : (Q : Subgroup ↥L).map L.subtype = U) (hIU : I ≤ normalizer (U : Set G))
    (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    (γ : ↥I) : (Q : Subgroup ↥L).map (φ γ).toMonoidHom = Q := by
  have hP : I ≤ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) := by
    rw [hQU]
    exact hIU
  exact map_sylow_eq_self_of_invariant φ hφ Q hP γ

private lemma map_normalizer_eq_self {G : Type} [Group G] {L I U : Subgroup G}
    {Q : Sylow 2 ↥L} (hQU : (Q : Subgroup ↥L).map L.subtype = U)
    (hIU : I ≤ normalizer (U : Set G)) (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    (γ : ↥I) :
    (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)).map (φ γ).toMonoidHom =
      Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
  have hP : I ≤ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) := by
    rw [hQU]
    exact hIU
  rw [Subgroup.map_equiv_normalizer_eq (Q : Subgroup ↥L) (φ γ),
    map_sylow_eq_self_of_invariant φ hφ Q hP γ]

private lemma inf_normalizer_smul_map {G : Type} [Group G] (L : Subgroup G) (Q : Sylow 2 ↥L)
    (x : ↥L) :
    L ⊓ normalizer ((((x • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype : Subgroup G) : Set G) =
      ((Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)).map
        (MulAut.conj x).toMonoidHom).map L.subtype := by
  have hle : (((x • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype : Subgroup G) ≤ L :=
    Subgroup.map_subtype_le _
  rw [inf_normalizer_eq_map_normalizer_subgroupOf hle]
  have hinner : Subgroup.normalizer
        ((((x • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype : Subgroup G).subgroupOf L) =
      (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)).map (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective ((x • Q : Sylow 2 ↥L))]
    have hQx : (x • Q : Sylow 2 ↥L) = (Q : Subgroup ↥L).map (MulAut.conj x).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hQx, ← Subgroup.map_equiv_normalizer_eq (Q : Subgroup ↥L) (MulAut.conj x)]
  rw [hinner]

private lemma sup_parabolic_map_ne_top {G : Type} [Group G] {L I U : Subgroup G}
    {Q : Sylow 2 ↥L} (hQU : (Q : Subgroup ↥L).map L.subtype = U)
    (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    (horb : ∀ A : Subgroup G, IsGomiAtom L U A →
      (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≠ L)
    {N : Subgroup ↥L} [(cartan (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N).Normal]
    {S : Set (WeylGroup (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N)}
    (h : TitsSystem.IsBNPair (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N S)
    {s : WeylGroup (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N} (hs : s ∈ S) :
    (⨆ γ : ↥I, (parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map
      (φ γ).toMonoidHom) ≠ ⊤ := by
  intro hsup
  have hAatom : IsGomiAtom ⊤ (Q : Subgroup ↥L)
      (parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}) :=
    (isGomiAtom_top_iff_covBy (Q : Subgroup ↥L) _).mpr (h.covBy_parabolic_singleton hs)
  have hA : IsGomiAtom L U
      ((parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map L.subtype) := by
    have h' := (isGomiAtom_map_subtype_iff L (Q : Subgroup ↥L) _).mpr hAatom
    rwa [hQU] at h'
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← L.subtype.range_eq_map, Subgroup.range_subtype]
  have hmap : (⨆ γ : ↥I, ((parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map
      (φ γ).toMonoidHom)).map L.subtype = L := by
    rw [hsup, htop]
  rw [Subgroup.map_iSup] at hmap
  have hrewrite : ∀ γ : ↥I,
      (((parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map
        (φ γ).toMonoidHom).map L.subtype) =
      (((parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map L.subtype).map
        (MulAut.conj (γ : G)).toMonoidHom) :=
    fun γ => map_map_of_coe φ hφ γ _
  simp only [hrewrite] at hmap
  refine horb ((parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map L.subtype) hA ?_
  rw [iSup_subtype' (p := fun i => i ∈ I)
    (f := fun i _ => ((parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map
      L.subtype).map (MulAut.conj i).toMonoidHom)]
  exact hmap

private lemma invariantLink_imp_gomiChevFixedLink {G : Type} [Group G] {L I : Subgroup G}
    {Q : Sylow 2 ↥L} (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    {x y : ↥L}
    (hlink : TitsSystem.InvariantLink
      (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) φ x y) :
    (((x • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype) =
        (((y • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype) ∨
      GomiChevFixedLink L I
        (((x • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype)
        (((y • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype) := by
  rcases hlink with hmem | ⟨P, hPne, hPinv, hxP, hyP⟩
  · left
    have h1 : (x⁻¹ * y) • Q = Q := (Sylow.smul_eq_iff_mem_normalizer).mpr hmem
    have h2 : x • Q = y • Q := by
      calc x • Q = x • ((x⁻¹ * y) • Q) := by rw [h1]
        _ = (x * (x⁻¹ * y)) • Q := (mul_smul x (x⁻¹ * y) Q).symm
        _ = y • Q := by rw [mul_inv_cancel_left]
    rw [h2]
  · right
    refine ⟨⟨x • Q, rfl⟩, ⟨y • Q, rfl⟩, P.map L.subtype, ?_, ?_, ?_, ?_⟩
    · intro i hi
      refine (Subgroup.mem_normalizer_iff_map_conj_eq).mpr ?_
      rw [← MulEquiv.toMonoidHom_eq_coe, ← map_map_of_coe φ hφ ⟨i, hi⟩ P, hPinv ⟨i, hi⟩]
    · rw [inf_normalizer_smul_map L Q x]
      exact Subgroup.map_mono hxP
    · rw [inf_normalizer_smul_map L Q y]
      exact Subgroup.map_mono hyP
    · have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
        rw [← L.subtype.range_eq_map, Subgroup.range_subtype]
      have hPlt : P.map L.subtype < (⊤ : Subgroup ↥L).map L.subtype :=
        Subgroup.map_subtype_lt_map_subtype.mpr (lt_top_iff_ne_top.mpr hPne)
      rwa [htop] at hPlt

private lemma inv_mul_apply_mem_normalizer {G : Type} [Group G] {L I U : Subgroup G}
    {Q : Sylow 2 ↥L} (hQU : (Q : Subgroup ↥L).map L.subtype = U)
    (hIU : I ≤ normalizer (U : Set G)) (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹)
    (g : ↥L)
    (hIV : I ≤ normalizer
      ((((g • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype : Subgroup G) : Set G))
    (γ : ↥I) : g⁻¹ * φ γ g ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
  have hVfix : ((g • Q : Sylow 2 ↥L) : Subgroup ↥L).map (φ γ).toMonoidHom =
      (g • Q : Sylow 2 ↥L) :=
    map_sylow_eq_self_of_invariant φ hφ (g • Q) hIV γ
  have hconj : (φ γ).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (φ γ g)).toMonoidHom.comp (φ γ).toMonoidHom := by
    ext y
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply, map_mul, map_inv]
  have hcalc : ((g • Q : Sylow 2 ↥L) : Subgroup ↥L).map (φ γ).toMonoidHom =
      ((φ γ g) • Q : Sylow 2 ↥L) := by
    calc ((g • Q : Sylow 2 ↥L) : Subgroup ↥L).map (φ γ).toMonoidHom
        = ((Q : Subgroup ↥L).map (MulAut.conj g).toMonoidHom).map (φ γ).toMonoidHom := by
          rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
          rfl
      _ = (Q : Subgroup ↥L).map ((φ γ).toMonoidHom.comp (MulAut.conj g).toMonoidHom) :=
          Subgroup.map_map (Q : Subgroup ↥L) (φ γ).toMonoidHom (MulAut.conj g).toMonoidHom
      _ = (Q : Subgroup ↥L).map
            ((MulAut.conj (φ γ g)).toMonoidHom.comp (φ γ).toMonoidHom) := by rw [hconj]
      _ = ((Q : Subgroup ↥L).map (φ γ).toMonoidHom).map
            (MulAut.conj (φ γ g)).toMonoidHom :=
          (Subgroup.map_map (Q : Subgroup ↥L) (MulAut.conj (φ γ g)).toMonoidHom
            (φ γ).toMonoidHom).symm
      _ = (Q : Subgroup ↥L).map (MulAut.conj (φ γ g)).toMonoidHom := by
          rw [map_sylow_eq_self hQU hIU φ hφ γ]
      _ = ((φ γ g) • Q : Sylow 2 ↥L) := by
          rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
          rfl
  have hQsmul : ((φ γ g) • Q : Sylow 2 ↥L) = (g • Q : Sylow 2 ↥L) :=
    Sylow.ext (hcalc.symm.trans hVfix)
  have h1 : ((g⁻¹ * φ γ g) • Q : Sylow 2 ↥L) = Q := by
    rw [mul_smul, hQsmul, inv_smul_smul]
  exact (Sylow.smul_eq_iff_mem_normalizer).mp h1

private lemma eqvGen_map_smul_map_subtype {G : Type} [Group G] {L I : Subgroup G}
    {Q : Sylow 2 ↥L} (φ : ↥I →* MulAut ↥L)
    (hφ : ∀ (γ : ↥I) (x : ↥L), ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹) :
    ∀ x y : ↥L, Relation.EqvGen
      (TitsSystem.InvariantLink (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) φ) x y →
      Relation.EqvGen (GomiChevFixedLink L I)
        (((x • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype)
        (((y • Q : Sylow 2 ↥L) : Subgroup ↥L).map L.subtype) := by
  intro x y hxy
  induction hxy with
  | rel a b hab =>
      rcases invariantLink_imp_gomiChevFixedLink φ hφ hab with heq | hlnk
      · rw [heq]
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ hlnk
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem eqvGen_gomiChevFixedLink_of_isBNPair {G : Type} [Group G] [Finite G]
    {L I U : Subgroup G} {Q : Sylow 2 ↥L} {N : Subgroup ↥L}
    [(cartan (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N).Normal]
    {S : Set (WeylGroup (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N)}
    (h : TitsSystem.IsBNPair (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N S)
    (hQU : (Q : Subgroup ↥L).map L.subtype = U) (hIL : I ≤ normalizer (L : Set G))
    (hIU : I ≤ normalizer (U : Set G))
    (horb : ∀ A : Subgroup G, IsGomiAtom L U A →
      (⨆ i ∈ I, A.map (MulAut.conj i).toMonoidHom) ≠ L)
    {V : Subgroup G} (hV : IsSylowOf 2 V L) (hIV : I ≤ normalizer (V : Set G)) :
    Relation.EqvGen (GomiChevFixedLink L I) U V := by
  obtain ⟨Q', rfl⟩ := hV
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq ↥L Q Q'
  let φ : ↥I →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hIL)
  have hφ : ∀ (γ : ↥I) (x : ↥L),
      ((φ γ x : ↥L) : G) = (γ : G) * (x : G) * (γ : G)⁻¹ := by
    intro γ x
    change (((Subgroup.normalizerMonoidHom (H := L))
      (Subgroup.inclusion hIL γ)) x : G) = (γ : G) * (x : G) * (γ : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  have hB : ∀ γ : ↥I,
      (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)).map (φ γ).toMonoidHom =
      Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) :=
    fun γ => map_normalizer_eq_self hQU hIU φ hφ γ
  have hS : ∀ s ∈ S,
      (⨆ γ : ↥I, (parabolic (normalizer ((Q : Subgroup ↥L) : Set ↥L)) N {s}).map
        (φ γ).toMonoidHom) ≠ ⊤ :=
    fun s hs => sup_parabolic_map_ne_top hQU φ hφ horb h hs
  have hg : ∀ γ : ↥I,
      g⁻¹ * φ γ g ∈ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) :=
    fun γ => inv_mul_apply_mem_normalizer hQU hIU φ hφ g hIV γ
  have hlink : Relation.EqvGen
      (TitsSystem.InvariantLink (Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L)) φ) 1 g :=
    h.eqvGen_invariantLink φ hB hS hg
  have hmain := eqvGen_map_smul_map_subtype (Q := Q) φ hφ
  simpa only [one_smul, hQU] using hmain 1 g hlink

end CFSG.GroupTheory
