module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ComponentClassification.AS76b

section OddCore

variable {H : Type*} [Group H]

theorem odd_card_assemblyOddCore [Finite H] : Odd (Nat.card (CFSG.Assembly.oddCore H)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

theorem le_assemblyOddCore {N : Subgroup H} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ CFSG.Assembly.oddCore H :=
  CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore N hN hodd

theorem assemblyOddCore_map_le {H' : Type*} [Group H'] [Finite H] (e : H ≃* H') :
    (CFSG.Assembly.oddCore H).map e.toMonoidHom ≤ CFSG.Assembly.oddCore H' := by
  refine le_assemblyOddCore ((CFSG.Assembly.oddCore_normal H).map _ e.surjective) ?_
  rw [card_map_of_injective e.injective]
  exact odd_card_assemblyOddCore

theorem assemblyOddCore_map_mulEquiv [Finite H] {H' : Type*} [Group H'] (e : H ≃* H') :
    (CFSG.Assembly.oddCore H).map e.toMonoidHom = CFSG.Assembly.oddCore H' := by
  have : Finite H' := Finite.of_equiv H e.toEquiv
  refine le_antisymm (assemblyOddCore_map_le e) ?_
  have h := map_mono (f := e.toMonoidHom) (assemblyOddCore_map_le e.symm)
  rwa [map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H' by
    ext; simp, map_id] at h

end OddCore

variable {G : Type*} [Group G]

theorem oddCoreIn_le (X : Subgroup G) : oddCoreIn X ≤ X := map_subtype_le _

theorem twoPrimeLayerIn_le (X : Subgroup G) : twoPrimeLayerIn X ≤ X := map_subtype_le _

theorem odd_card_oddCoreIn [Finite G] (X : Subgroup G) : Odd (Nat.card (oddCoreIn X)) := by
  rw [oddCoreIn, card_map_of_injective X.subtype_injective]
  exact odd_card_assemblyOddCore

theorem map_subtype_subgroupOf (X : Subgroup G) (K : Subgroup X) :
    (K.map X.subtype).subgroupOf X = K :=
  comap_map_eq_self_of_injective X.subtype_injective K

theorem oddCoreIn_subgroupOf (X : Subgroup G) :
    (oddCoreIn X).subgroupOf X = CFSG.Assembly.oddCore X :=
  map_subtype_subgroupOf X _

theorem twoPrimeLayerIn_subgroupOf (X : Subgroup G) :
    (twoPrimeLayerIn X).subgroupOf X =
      (CFSG.layer (X ⧸ CFSG.Assembly.oddCore X)).comap
        (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) :=
  map_subtype_subgroupOf X _

theorem mem_twoPrimeLayerIn_iff {X : Subgroup G} {x : G} :
    x ∈ twoPrimeLayerIn X ↔ ∃ hx : x ∈ X,
      QuotientGroup.mk' (CFSG.Assembly.oddCore X) ⟨x, hx⟩ ∈
        CFSG.layer (X ⧸ CFSG.Assembly.oddCore X) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_oddCoreIn_iff {X : Subgroup G} {x : G} :
    x ∈ oddCoreIn X ↔ ∃ hx : x ∈ X, (⟨x, hx⟩ : X) ∈ CFSG.Assembly.oddCore X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem oddCoreIn_le_twoPrimeLayerIn (X : Subgroup G) : oddCoreIn X ≤ twoPrimeLayerIn X := by
  intro x hx
  obtain ⟨hxX, h⟩ := mem_oddCoreIn_iff.mp hx
  refine mem_twoPrimeLayerIn_iff.mpr ⟨hxX, ?_⟩
  rw [show QuotientGroup.mk' (CFSG.Assembly.oddCore X) (⟨x, hxX⟩ : X) = 1 from
    (QuotientGroup.eq_one_iff _).mpr h]
  exact one_mem _

theorem oddCoreIn_normalIn (X : Subgroup G) : NormalIn (oddCoreIn X) X :=
  ⟨oddCoreIn_le X, by rw [oddCoreIn_subgroupOf]; infer_instance⟩

theorem layer_normal (H : Type*) [Group H] [Finite H] : (CFSG.layer H).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := H)
  infer_instance

theorem twoPrimeLayerIn_normalIn [Finite G] (X : Subgroup G) : NormalIn (twoPrimeLayerIn X) X := by
  refine ⟨twoPrimeLayerIn_le X, ?_⟩
  rw [twoPrimeLayerIn_subgroupOf]
  have := layer_normal (X ⧸ CFSG.Assembly.oddCore X)
  infer_instance

theorem le_oddCoreIn {N X : Subgroup G} (hN : NormalIn N X) (hodd : Odd (Nat.card N)) :
    N ≤ oddCoreIn X := by
  intro x hx
  refine mem_oddCoreIn_iff.mpr ⟨hN.1 hx, ?_⟩
  have := hN.2
  refine le_assemblyOddCore hN.2 ?_ (show (⟨x, hN.1 hx⟩ : X) ∈ N.subgroupOf X from hx)
  rw [Nat.card_congr (subgroupOfEquivOfLe hN.1).toEquiv]
  exact hodd

section Transport

theorem layer_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

@[expose] noncomputable def quotOddCoreEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) : A ⧸ CFSG.Assembly.oddCore A ≃* B ⧸ CFSG.Assembly.oddCore B :=
  QuotientGroup.congr _ _ e (assemblyOddCore_map_mulEquiv e)

theorem quotOddCoreEquiv_mk' {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) (a : A) :
    quotOddCoreEquiv e (QuotientGroup.mk' (CFSG.Assembly.oddCore A) a) =
      QuotientGroup.mk' (CFSG.Assembly.oddCore B) (e a) :=
  rfl

theorem mk_mem_layer_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B)
    (a : A) :
    QuotientGroup.mk' (CFSG.Assembly.oddCore A) a ∈ CFSG.layer (A ⧸ CFSG.Assembly.oddCore A) ↔
      QuotientGroup.mk' (CFSG.Assembly.oddCore B) (e a) ∈
        CFSG.layer (B ⧸ CFSG.Assembly.oddCore B) := by
  rw [← quotOddCoreEquiv_mk' e, ← layer_map_mulEquiv (quotOddCoreEquiv e)]
  exact (mem_map_iff_mem (quotOddCoreEquiv e).injective).symm

theorem mem_twoPrimeLayerIn_iff_of_mulEquiv [Finite G] {G' : Type*} [Group G'] {X : Subgroup G}
    {Y : Subgroup G'} (e : X ≃* Y) (x : X) :
    (x : G) ∈ twoPrimeLayerIn X ↔ (e x : G') ∈ twoPrimeLayerIn Y := by
  rw [mem_twoPrimeLayerIn_iff, mem_twoPrimeLayerIn_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨(e x).2, (mk_mem_layer_iff_of_mulEquiv e x).mp h⟩
  · rintro ⟨hx, h⟩
    exact ⟨x.2, (mk_mem_layer_iff_of_mulEquiv e x).mpr h⟩

theorem mem_oddCoreIn_iff_of_mulEquiv [Finite G] {G' : Type*} [Group G'] {X : Subgroup G}
    {Y : Subgroup G'} (e : X ≃* Y) (x : X) :
    (x : G) ∈ oddCoreIn X ↔ (e x : G') ∈ oddCoreIn Y := by
  rw [mem_oddCoreIn_iff, mem_oddCoreIn_iff, ← assemblyOddCore_map_mulEquiv e]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨(e x).2, ⟨x, h, rfl⟩⟩
  · rintro ⟨hx, h⟩
    refine ⟨x.2, ?_⟩
    have h' : e.toMonoidHom x ∈ (CFSG.Assembly.oddCore X).map e.toMonoidHom := h
    exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp h'

theorem twoPrimeLayerIn_map [Finite G] {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) :
    twoPrimeLayerIn (X.map f) = (twoPrimeLayerIn X).map f := by
  let e := X.equivMapOfInjective f hf
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (twoPrimeLayerIn_le (X.map f)) hy
    refine ⟨x, ?_, rfl⟩
    have h := (mem_twoPrimeLayerIn_iff_of_mulEquiv e ⟨x, hx⟩).mpr hy
    exact h
  · rintro ⟨x, hx, rfl⟩
    exact (mem_twoPrimeLayerIn_iff_of_mulEquiv e ⟨x, twoPrimeLayerIn_le X hx⟩).mp hx

theorem oddCoreIn_map [Finite G] {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) :
    oddCoreIn (X.map f) = (oddCoreIn X).map f := by
  let e := X.equivMapOfInjective f hf
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (oddCoreIn_le (X.map f)) hy
    exact ⟨x, (mem_oddCoreIn_iff_of_mulEquiv e ⟨x, hx⟩).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_oddCoreIn_iff_of_mulEquiv e ⟨x, oddCoreIn_le X hx⟩).mp hx

theorem normalizer_le_normalizer_twoPrimeLayerIn [Finite G] (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (twoPrimeLayerIn X : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [← twoPrimeLayerIn_map _ (MulAut.conj n).injective, hn]

theorem normalizer_le_normalizer_oddCoreIn [Finite G] (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (oddCoreIn X : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [← oddCoreIn_map _ (MulAut.conj n).injective, hn]

end Transport

section Solvable

theorem layer_ne_bot_of_ne {X : Subgroup G} (h : twoPrimeLayerIn X ≠ oddCoreIn X) :
    CFSG.layer (X ⧸ CFSG.Assembly.oddCore X) ≠ ⊥ := by
  intro hbot
  apply h
  rw [twoPrimeLayerIn, hbot, MonoidHom.comap_bot, QuotientGroup.ker_mk', oddCoreIn]

theorem not_isSolvable_of_layer_ne_bot {A : Type*} [Group A] [Finite A] {M : Subgroup A}
    (hM : CFSG.layer A ≤ M) (h : CFSG.layer A ≠ ⊥) : ¬ Group.IsSolvable M := by
  intro hs
  have : ∃ L : Subgroup A, CFSG.IsComponent L := by
    by_contra hno
    push Not at hno
    exact h (CFSG.LocalCores.layer_eq_bot_of_forall hno)
  obtain ⟨L, hL⟩ := this
  have hLM : L ≤ M := (CFSG.LocalCores.component_le_layer hL).trans hM
  have : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have : Group.IsPerfect L := hL.1.1
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem not_isSolvable_twoPrimeLayerIn [Finite G] {X : Subgroup G}
    (h : twoPrimeLayerIn X ≠ oddCoreIn X) : ¬ Group.IsSolvable (twoPrimeLayerIn X) := by
  intro hs
  set q := QuotientGroup.mk' (CFSG.Assembly.oddCore X)
  set L := CFSG.layer (X ⧸ CFSG.Assembly.oddCore X)
  let f : twoPrimeLayerIn X →* L :=
    (q.comp (Subgroup.inclusion (twoPrimeLayerIn_le X))).codRestrict L fun y => by
      obtain ⟨hyX, hy⟩ := mem_twoPrimeLayerIn_iff.mp y.2
      exact hy
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Assembly.oddCore X) z
    exact ⟨⟨x, mem_twoPrimeLayerIn_iff.mpr ⟨x.2, hz⟩⟩, Subtype.ext rfl⟩
  have : Group.IsSolvable L := Group.isSolvable_of_surjective hf
  exact not_isSolvable_of_layer_ne_bot (M := L) le_rfl (layer_ne_bot_of_ne h) this

theorem even_card_twoPrimeLayerIn [Finite G] {X : Subgroup G}
    (h : twoPrimeLayerIn X ≠ oddCoreIn X) : Even (Nat.card (twoPrimeLayerIn X)) := by
  by_contra hodd
  exact not_isSolvable_twoPrimeLayerIn h
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))

end Solvable

section Normal

theorem normalIn_le_normalizer {M X : Subgroup G} (h : NormalIn M X) :
    X ≤ normalizer (M : Set G) :=
  (normal_subgroupOf_iff_le_normalizer h.1).mp h.2

theorem normalIn_of_le_normalizer {M X : Subgroup G} (hMX : M ≤ X)
    (hX : X ≤ normalizer (M : Set G)) : NormalIn M X :=
  ⟨hMX, (normal_subgroupOf_iff_le_normalizer hMX).mpr hX⟩

theorem oddCoreIn_le_of_normalIn [Finite G] {N X : Subgroup G} (hN : NormalIn N X) :
    oddCoreIn N ≤ oddCoreIn X :=
  le_oddCoreIn (normalIn_of_le_normalizer ((oddCoreIn_le N).trans hN.1)
    ((normalIn_le_normalizer hN).trans (normalizer_le_normalizer_oddCoreIn N)))
    (odd_card_oddCoreIn N)

theorem inf_oddCoreIn_eq [Finite G] {N X : Subgroup G} (hN : NormalIn N X) :
    N ⊓ oddCoreIn X = oddCoreIn N := by
  refine le_antisymm (le_oddCoreIn (normalIn_of_le_normalizer inf_le_left ?_) ?_)
    (le_inf (oddCoreIn_le N) (oddCoreIn_le_of_normalIn hN))
  · intro n hn
    rw [mem_normalizer_iff]
    intro y
    have hnX : n ∈ X := hN.1 hn
    have hO := normalIn_le_normalizer (oddCoreIn_normalIn X) hnX
    have hNn := normalIn_le_normalizer hN hnX
    rw [mem_inf, mem_inf, (mem_normalizer_iff.mp hO) y, (mem_normalizer_iff.mp hNn) y]
  · exact (odd_card_oddCoreIn X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

@[expose] def IsSemisimpleQ (X : Subgroup G) : Prop :=
  CFSG.layer (X ⧸ CFSG.Assembly.oddCore X) = ⊤

theorem map_subtype_layer_le_layer {A : Type*} [Group A] [Finite A] {M : Subgroup A}
    (hM : M.Normal) : (CFSG.layer M).map M.subtype ≤ CFSG.layer A := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  refine le_sSup (show CFSG.IsComponent (L.map M.subtype) from ⟨?_, hL.2.trans' hM.isSubnormal⟩)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (L.equivMapOfInjective M.subtype M.subtype_injective) hL.1

theorem layer_map_mk_eq_top [Finite G] {N X : Subgroup G} (hNX : N ≤ X)
    (hinf : N ⊓ oddCoreIn X = oddCoreIn N) (hs : IsSemisimpleQ N) :
    CFSG.layer ((N.subgroupOf X).map (QuotientGroup.mk' (CFSG.Assembly.oddCore X))) = ⊤ := by
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore X)
  set M : Subgroup (X ⧸ CFSG.Assembly.oddCore X) := (N.subgroupOf X).map π with hMdef
  let φ : N →* M := (π.comp (Subgroup.inclusion hNX)).codRestrict M fun n =>
    ⟨Subgroup.inclusion hNX n, n.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hker : φ.ker = CFSG.Assembly.oddCore N := by
    ext n
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : π (Subgroup.inclusion hNX n) = 1 := congrArg Subtype.val h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have h2 : (n : G) ∈ N ⊓ oddCoreIn X :=
        ⟨n.2, mem_oddCoreIn_iff.mpr ⟨hNX n.2, h1⟩⟩
      rw [hinf] at h2
      obtain ⟨hh, h3⟩ := mem_oddCoreIn_iff.mp h2
      exact h3
    · intro h
      have h2 : (n : G) ∈ oddCoreIn N := mem_oddCoreIn_iff.mpr ⟨n.2, h⟩
      rw [← hinf] at h2
      obtain ⟨hnX, h3⟩ := mem_oddCoreIn_iff.mp h2.2
      apply Subtype.ext
      show π (Subgroup.inclusion hNX n) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h3
  let e : N ⧸ CFSG.Assembly.oddCore N ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  rw [← layer_map_mulEquiv e, show CFSG.layer (N ⧸ CFSG.Assembly.oddCore N) = ⊤ from hs,
    map_top_of_surjective _ e.surjective]

theorem le_twoPrimeLayerIn_of_normalIn [Finite G] {N X : Subgroup G} (hN : NormalIn N X)
    (hs : IsSemisimpleQ N) : N ≤ twoPrimeLayerIn X := by
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore X)
  set M : Subgroup (X ⧸ CFSG.Assembly.oddCore X) := (N.subgroupOf X).map π with hMdef
  have hMn : M.Normal := @Subgroup.Normal.map _ _ _ _ _ hN.2 π (QuotientGroup.mk'_surjective _)
  have hlayer : CFSG.layer M = ⊤ := layer_map_mk_eq_top hN.1 (inf_oddCoreIn_eq hN) hs
  have hMle : M ≤ CFSG.layer (X ⧸ CFSG.Assembly.oddCore X) := by
    have h := map_subtype_layer_le_layer hMn
    rwa [hlayer, ← MonoidHom.range_eq_map, range_subtype] at h
  intro n hn
  refine mem_twoPrimeLayerIn_iff.mpr ⟨hN.1 hn, hMle ⟨⟨n, hN.1 hn⟩, hn, rfl⟩⟩

end Normal

theorem layer_layer_eq_top (A : Type*) [Group A] [Finite A] :
    CFSG.layer (CFSG.layer A) = ⊤ :=
  CFSG.WholeGroup.layer_layer_eq_top

theorem oddCoreIn_twoPrimeLayerIn [Finite G] (X : Subgroup G) :
    oddCoreIn (twoPrimeLayerIn X) = oddCoreIn X := by
  refine le_antisymm (oddCoreIn_le_of_normalIn (twoPrimeLayerIn_normalIn X)) ?_
  refine le_oddCoreIn (normalIn_of_le_normalizer (oddCoreIn_le_twoPrimeLayerIn X)
    ((twoPrimeLayerIn_le X).trans (normalIn_le_normalizer (oddCoreIn_normalIn X))))
    (odd_card_oddCoreIn X)

theorem isSemisimpleQ_twoPrimeLayerIn [Finite G] (X : Subgroup G) :
    IsSemisimpleQ (twoPrimeLayerIn X) := by
  set K := twoPrimeLayerIn X
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore X)
  set E := CFSG.layer (X ⧸ CFSG.Assembly.oddCore X)
  let ψ : K →* E :=
    (π.comp (Subgroup.inclusion (twoPrimeLayerIn_le X))).codRestrict E fun y => by
      obtain ⟨hyX, hy⟩ := mem_twoPrimeLayerIn_iff.mp y.2
      exact hy
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Assembly.oddCore X) z
    exact ⟨⟨x, mem_twoPrimeLayerIn_iff.mpr ⟨x.2, hz⟩⟩, Subtype.ext rfl⟩
  have hker : ψ.ker = CFSG.Assembly.oddCore K := by
    ext k
    rw [MonoidHom.mem_ker]
    have hiff : (k : G) ∈ oddCoreIn K ↔ (k : G) ∈ oddCoreIn X := by
      rw [oddCoreIn_twoPrimeLayerIn]
    constructor
    · intro h
      have h1 : π (Subgroup.inclusion (twoPrimeLayerIn_le X) k) = 1 := congrArg Subtype.val h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      obtain ⟨hk, h2⟩ := mem_oddCoreIn_iff.mp
        (hiff.mpr (mem_oddCoreIn_iff.mpr ⟨twoPrimeLayerIn_le X k.2, h1⟩))
      exact h2
    · intro h
      obtain ⟨hk, h2⟩ := mem_oddCoreIn_iff.mp (hiff.mp (mem_oddCoreIn_iff.mpr ⟨k.2, h⟩))
      apply Subtype.ext
      show π (Subgroup.inclusion (twoPrimeLayerIn_le X) k) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
  let e : K ⧸ CFSG.Assembly.oddCore K ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  show CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) = ⊤
  rw [← layer_map_mulEquiv e.symm, layer_layer_eq_top, map_top_of_surjective _ e.symm.surjective]

theorem normalIn_twoPrimeLayerIn_top_of_normal [Finite G] {Q : Subgroup G} (hQ : Q.Normal) :
    NormalIn (twoPrimeLayerIn Q) (twoPrimeLayerIn (⊤ : Subgroup G)) := by
  have hK : (twoPrimeLayerIn Q).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro g _
    exact normalizer_le_normalizer_twoPrimeLayerIn Q (normalizer_eq_top_iff.mpr hQ ▸ mem_top g)
  have hle : twoPrimeLayerIn Q ≤ twoPrimeLayerIn (⊤ : Subgroup G) :=
    le_twoPrimeLayerIn_of_normalIn (normalIn_of_le_normalizer le_top
      (by rw [normalizer_eq_top_iff.mpr hK])) (isSemisimpleQ_twoPrimeLayerIn Q)
  exact normalIn_of_le_normalizer hle (by rw [normalizer_eq_top_iff.mpr hK]; exact le_top)

section Surjective

theorem map_layer_le_layer_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) : (CFSG.layer A).map f ≤ CFSG.layer B := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  by_cases hker : L ≤ f.ker
  · rw [(map_eq_bot_iff L).mpr hker]
    exact bot_le
  · exact le_sSup (show CFSG.IsComponent (L.map f) from
      ⟨CFSG.LocalCores.isQuasisimple_map hL.1 f hker, hL.2.map hf⟩)

theorem layer_eq_top_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (h : CFSG.layer A = ⊤) : CFSG.layer B = ⊤ := by
  have := map_layer_le_layer_of_surjective f hf
  rwa [h, map_top_of_surjective f hf, top_le_iff] at this

theorem isSemisimpleQ_of_le_sup [Finite G] {J₀ J : Subgroup G} (hJ₀ : J₀ ≤ J)
    (hcov : J ≤ J₀ ⊔ oddCoreIn J) (hs : IsSemisimpleQ J) : IsSemisimpleQ J₀ := by
  set O := CFSG.Assembly.oddCore J
  set π := QuotientGroup.mk' O
  let ψ : J₀ →* J ⧸ O := π.comp (Subgroup.inclusion hJ₀)
  have htop : J₀.subgroupOf J ⊔ O = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_of_le_left hJ₀, ← MonoidHom.range_eq_map,
      range_subtype]
    exact le_antisymm (sup_le hJ₀ (oddCoreIn_le J)) hcov
  have hψ : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    have hrange : ψ.range = (J₀.subgroupOf J).map π := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [hrange]
    have h := congrArg (Subgroup.map π) htop
    rwa [Subgroup.map_sup, show O.map π = ⊥ from by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'], sup_bot_eq,
      map_top_of_surjective π (QuotientGroup.mk'_surjective O)] at h
  have hker : ψ.ker ≤ CFSG.Assembly.oddCore J₀ := by
    intro x hx
    have h1 : π (Subgroup.inclusion hJ₀ x) = 1 := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (x : G) ∈ J₀ ⊓ oddCoreIn J := ⟨x.2, mem_oddCoreIn_iff.mpr ⟨hJ₀ x.2, h1⟩⟩
    have hN : NormalIn (J₀ ⊓ oddCoreIn J) J₀ := by
      refine normalIn_of_le_normalizer inf_le_left fun n hn => ?_
      rw [mem_normalizer_iff]
      intro y
      have hO := normalIn_le_normalizer (oddCoreIn_normalIn J) (hJ₀ hn)
      rw [mem_inf, mem_inf, (mem_normalizer_iff.mp hO) y]
      constructor
      · rintro ⟨hy, hyO⟩
        exact ⟨J₀.mul_mem (J₀.mul_mem hn hy) (J₀.inv_mem hn), hyO⟩
      · rintro ⟨hy, hyO⟩
        refine ⟨?_, hyO⟩
        have := J₀.mul_mem (J₀.mul_mem (J₀.inv_mem hn) hy) hn
        simpa [mul_assoc] using this
    have hodd : Odd (Nat.card ↥(J₀ ⊓ oddCoreIn J)) :=
      (odd_card_oddCoreIn J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    obtain ⟨hxJ₀, h3⟩ := mem_oddCoreIn_iff.mp (le_oddCoreIn hN hodd h2)
    exact h3
  let f : J ⧸ O →* J₀ ⧸ CFSG.Assembly.oddCore J₀ :=
    (QuotientGroup.map ψ.ker (CFSG.Assembly.oddCore J₀) (MonoidHom.id J₀) hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Assembly.oddCore J₀) z
    refine ⟨QuotientGroup.quotientKerEquivOfSurjective ψ hψ (QuotientGroup.mk' ψ.ker y), ?_⟩
    simp only [f, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulEquiv.symm_apply_apply]
    rfl
  exact layer_eq_top_of_surjective f hf hs

end Surjective

end CFSG.ComponentClassification.Asc75T4
