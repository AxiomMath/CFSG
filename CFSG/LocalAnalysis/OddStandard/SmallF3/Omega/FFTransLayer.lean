module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayerAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem ff_twoRes_eq_map (H : Subgroup G) :
    twoRes H = (twoRes (⊤ : Subgroup ↥H)).map H.subtype := by
  rw [ff_map_twoRes _ H.subtype_injective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ff_twoPrimeRes_eq_map (H : Subgroup G) :
    twoPrimeRes H = (twoPrimeRes (⊤ : Subgroup ↥H)).map H.subtype := by
  rw [ff_map_twoPrimeRes _ H.subtype_injective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem ff_XOut_eq_map (C : Subgroup G) :
    twoPrimeRes (twoRes C) = (ffX ↥C).map C.subtype := by
  unfold ffX
  rw [ff_map_twoPrimeRes _ C.subtype_injective, ff_map_twoRes _ C.subtype_injective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ff_twoPrimeRes_twoRes_le (C : Subgroup G) : twoPrimeRes (twoRes C) ≤ C := by
  have h1 : twoRes C ≤ C := (Subgroup.closure_le C).mpr fun g hg => hg.1
  exact (Subgroup.closure_le C).mpr fun g hg => h1 hg.1

theorem ff_ffX_map_equiv {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    ffX B = (ffX A).map f.toMonoidHom := by
  exact (ff_map_ffX f).symm

theorem ff_layer_map_equiv {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    CFSG.layer B = (CFSG.layer A).map f.toMonoidHom := by
  exact (ff_layer_map f).symm

theorem ff_xTwoCore_congr {A B : Type} [Group A] [Group B] (f : A ≃* B) :
    XTwoCore A ↔ XTwoCore B := by
  have h1 : (ffX A).map f.toMonoidHom = ffX B := ff_map_ffX f
  have h2 : (CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup A))).map f.toMonoidHom =
      CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup B)) := by
    rw [ff_inSubgroup_map (CFSG.pCore 2) (fun _ _ _ _ ε => CFSG.pCore_map_iso 2 ε)
      f.toMonoidHom f.injective, ff_map_twoRes _ f.injective,
      Subgroup.map_top_of_surjective _ f.surjective]
  unfold XTwoCore
  rw [← h1, ← h2, Subgroup.map_injective (f := f.toMonoidHom) f.injective |>.eq_iff]

theorem ff_isOmega5_layerIn_iff {C : Subgroup G} {B : Type} [Group B] (f : ↥C ≃* B) :
    IsOmega5 (CFSG.inSubgroup CFSG.layer C) ↔ IsOmega5 (CFSG.layer B) := by
  exact ff_isOmega5_congr (ff_inSubgroupEquiv CFSG.layer (fun _ _ _ _ ε => ff_layer_map ε) C f)

theorem ff_isL29_layerIn_iff {C : Subgroup G} {B : Type} [Group B] (f : ↥C ≃* B) :
    IsL29 (CFSG.inSubgroup CFSG.layer C) ↔ IsL29 (CFSG.layer B) := by
  exact ff_isL29_congr (ff_inSubgroupEquiv CFSG.layer (fun _ _ _ _ ε => ff_layer_map ε) C f)

theorem ff_isL3Eps3_layerIn_iff {C : Subgroup G} {B : Type} [Group B] (f : ↥C ≃* B) :
    IsL3Eps3 (CFSG.inSubgroup CFSG.layer C) ↔ IsL3Eps3 (CFSG.layer B) := by
  exact ff_isL3Eps3_congr (ff_inSubgroupEquiv CFSG.layer (fun _ _ _ _ ε => ff_layer_map ε) C f)

theorem ff_X_eq_layer_iff {C : Subgroup G} {B : Type} [Group B] (f : ↥C ≃* B) :
    twoPrimeRes (twoRes C) = CFSG.inSubgroup CFSG.layer C ↔ ffX B = CFSG.layer B := by
  rw [ff_XOut_eq_map, ff_ffX_map_equiv f, ff_layer_map_equiv f]
  unfold CFSG.inSubgroup
  rw [(Subgroup.map_injective C.subtype_injective).eq_iff,
    (Subgroup.map_injective (f := f.toMonoidHom) f.injective).eq_iff]

theorem ff_X_eq_pCore_iff {C : Subgroup G} {B : Type} [Group B] (f : ↥C ≃* B) :
    twoPrimeRes (twoRes C) = CFSG.inSubgroup (CFSG.pCore 2) (twoRes C) ↔ XTwoCore B := by
  rw [← ff_xTwoCore_congr f]
  have h1 : (ffX ↥C).map C.subtype = twoPrimeRes (twoRes C) := (ff_XOut_eq_map C).symm
  have h2 : (CFSG.inSubgroup (CFSG.pCore 2) (twoRes (⊤ : Subgroup ↥C))).map C.subtype =
      CFSG.inSubgroup (CFSG.pCore 2) (twoRes C) := by
    rw [ff_inSubgroup_map (CFSG.pCore 2) (fun _ _ _ _ ε => CFSG.pCore_map_iso 2 ε)
      C.subtype C.subtype_injective, ff_map_twoRes _ C.subtype_injective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  unfold XTwoCore
  rw [← h1, ← h2, (Subgroup.map_injective C.subtype_injective).eq_iff]

theorem ff_not_isL29_X_of_solvable {C : Subgroup G} (hC : Group.IsSolvable ↥C) :
    ¬ IsL29 (twoPrimeRes (twoRes C)) := by
  intro h
  refine ff_isL29_not_solvable h ?_
  haveI := hC
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective (ff_twoPrimeRes_twoRes_le C))

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {L : Subgroup G}

theorem ff_XOut_le (L : Subgroup G) (s : G) : XOut L s ≤ L := by
  exact (ff_twoPrimeRes_twoRes_le _).trans inf_le_left

theorem ff_mem_layerCent_iff (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) {u : G} (hu : u ∈ L) :
    u ∈ layerCent L s ↔
      ffPhi hz e ⟨u, hu⟩ ∈ CFSG.inSubgroup CFSG.layer (ffFix hQ (by omega) x) := by
  obtain ⟨f, hf⟩ := ff_exists_centEquiv hQ h5 hz e hs
  exact ff_mem_inSubgroup_iff CFSG.layer (fun _ _ _ _ ε => ff_layer_map ε) (ffPhi hz e)
    (inf_le_left : L ⊓ centralizer ({s} : Set G) ≤ L) f (fun c => hf c) hu

theorem ff_mem_XOut_iff (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) {u : G} (hu : u ∈ L) :
    u ∈ XOut L s ↔ ffPhi hz e ⟨u, hu⟩ ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) x)) := by
  obtain ⟨f, hf⟩ := ff_exists_centEquiv hQ h5 hz e hs
  have h := ff_mem_inSubgroup_iff (fun K _ => ffX K) (fun _ _ _ _ ε => ff_map_ffX ε)
    (ffPhi hz e) (inf_le_left : L ⊓ centralizer ({s} : Set G) ≤ L) f (fun c => hf c) hu
  unfold XOut
  rw [ff_XOut_eq_map, ff_XOut_eq_map]
  exact h

theorem ff_orderOf_phi (hQ : Q.Nondegenerate) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {u : G} (hu : u ∈ L) :
    orderOf (ffPhi hz e ⟨u, hu⟩) = orderOf u := by
  exact (orderOf_injective (ffPhi hz e).toMonoidHom (ffPhi hz e).injective ⟨u, hu⟩).trans
    (Subgroup.orderOf_mk u hu)

theorem ff_layerCent_eq_of_central [Finite G] (hq : CFSG.IsQuasisimple ↥L)
    (hz : Subgroup.center ↥L = ⊥) (hev : 2 ∣ Nat.card ↥L) {s : G}
    (hs : s ∈ centralizer (L : Set G)) : layerCent L s = L ∧ XOut L s = L := by
  have hC : L ⊓ centralizer ({s} : Set G) = L := inf_eq_left.mpr fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hs l hl)
  haveI := hq.2.1
  haveI hsL : IsSimpleGroup ↥L :=
    MulEquiv.isSimpleGroup (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hz.symm))
  haveI hsT : IsSimpleGroup ↥(⊤ : Subgroup ↥L) := MulEquiv.isSimpleGroup Subgroup.topEquiv
  have hnc : ∃ a b : ↥(⊤ : Subgroup ↥L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨a', Subgroup.mem_top _⟩, ⟨b', Subgroup.mem_top _⟩, fun h => hab ?_⟩
    have h' : a' * b' = b' * a' := congrArg Subtype.val h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']
  have hev' : 2 ∣ Nat.card ↥(⊤ : Subgroup ↥L) := by rwa [Subgroup.card_top]
  haveI : Subsingleton (↥L ⧸ (⊤ : Subgroup ↥L)) := QuotientGroup.subsingleton_quotient_top
  have h2 : IsPGroup 2 (↥L ⧸ (⊤ : Subgroup ↥L)) := fun g =>
    ⟨0, by rw [pow_zero, pow_one]; exact Subsingleton.elim _ _⟩
  obtain ⟨hl, hx⟩ := ff_layer_ffX_eq_of_normal_simple (⊤ : Subgroup ↥L) hsT hnc hev' h2
  refine ⟨?_, ?_⟩
  · unfold layerCent CFSG.inSubgroup
    rw [hC, hl, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · unfold XOut
    rw [hC, ff_XOut_eq_map, hx, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ff_two_dvd_card_of_isOmega6Plus [Finite G] {X : Subgroup G} (h : IsOmega6Plus X) :
    2 ∣ Nat.card ↥X := by
  have h1 := ff_card_isOmega6Plus h
  have h2 : Nat.card (↥X ⧸ oddCore ↥X) ∣ Nat.card ↥X := Subgroup.card_quotient_dvd_card _
  rw [h1] at h2
  exact (by norm_num : 2 ∣ 6065280).trans h2

end CFSG.OddStandard.SmallF3.Omega
