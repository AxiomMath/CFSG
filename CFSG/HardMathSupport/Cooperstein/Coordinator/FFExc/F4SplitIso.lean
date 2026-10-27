module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitCenter
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitSimple

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem isogeny_sX (l : List (Fin Tag.E6.rank)) (c : K) :
    ((e6IsogenyT K (sX e6Data_valid K l c) : adjointGroup TwistTag.E6.tag K) :
      ModGL TwistTag.E6.tag K) = (l.map fun i => xUnit TwistTag.E6.tag K i c).prod := by
  unfold sX
  rw [map_list_prod, List.map_map]
  rw [show ((List.map (⇑(e6IsogenyT K) ∘ fun i => e6Data_valid.xm K (Pi.single i 1) c) l).prod :
      adjointGroup TwistTag.E6.tag K).1 = (adjointGroup TwistTag.E6.tag K).subtype
      (List.map (⇑(e6IsogenyT K) ∘ fun i => e6Data_valid.xm K (Pi.single i 1) c) l).prod from rfl,
    map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  change (↑(e6Isogeny K (e6Data_valid.xm K (Pi.single i 1) c)) : ModGL Tag.E6 K) =
    xUnit TwistTag.E6.tag K i c
  rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]
  rfl

theorem isogeny_sY (l : List (Fin Tag.E6.rank)) (c : K) :
    ((e6IsogenyT K (sY e6Data_valid K l c) : adjointGroup TwistTag.E6.tag K) :
      ModGL TwistTag.E6.tag K) = (l.map fun i => yUnit TwistTag.E6.tag K i c).prod := by
  unfold sY
  rw [map_list_prod, List.map_map]
  rw [show ((List.map (⇑(e6IsogenyT K) ∘ fun i => e6Data_valid.xm K (-Pi.single i 1) c) l).prod :
      adjointGroup TwistTag.E6.tag K).1 = (adjointGroup TwistTag.E6.tag K).subtype
      (List.map (⇑(e6IsogenyT K) ∘ fun i => e6Data_valid.xm K (-Pi.single i 1) c) l).prod from rfl,
    map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  change (↑(e6Isogeny K (e6Data_valid.xm K (-Pi.single i 1) c)) : ModGL Tag.E6 K) =
    yUnit TwistTag.E6.tag K i c
  rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
  rfl

theorem orbs_eq : ∀ l ∈ orbs, ∃ j : Fin Tag.F4.rank,
    l = TwistTag.E6.orbitWord (f4FoldedIndex j) := by
  intro l hl
  simp only [orbs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨⟨3, by decide⟩, rfl⟩
  · exact ⟨⟨2, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩
  · exact ⟨⟨0, by decide⟩, rfl⟩

theorem orbitWord_mem (j : Fin Tag.F4.rank) : TwistTag.E6.orbitWord (f4FoldedIndex j) ∈ orbs := by
  fin_cases j
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) = [nd1] := rfl
    change TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) ∈ orbs
    rw [h]; decide
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) = [nd3] := rfl
    change TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) ∈ orbs
    rw [h]; decide
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) = [nd2, nd4] := rfl
    change TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) ∈ orbs
    rw [h]; decide
  · have h : TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) = [nd0, nd5] := rfl
    change TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) ∈ orbs
    rw [h]; decide

@[expose] def isoToGL : F4simple e6Data_valid K →* ModGL TwistTag.E6.tag K :=
  ((adjointGroup TwistTag.E6.tag K).subtype.comp (e6IsogenyT K)).comp
    (F4simple e6Data_valid K).subtype

theorem isoToGL_mem (g : F4simple e6Data_valid K) :
    isoToGL K g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
  obtain ⟨g, hg⟩ := g
  let Hm : Subgroup (e6Data_valid.minGroup K) := (twistedFixedGroup TwistTag.E6 K (RingHom.id K)).comap
    ((adjointGroup TwistTag.E6.tag K).subtype.comp (e6IsogenyT K))
  have hle : F4simple e6Data_valid K ≤ Hm := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨l, hl, c, rfl | rfl⟩
    · obtain ⟨j, rfl⟩ := orbs_eq l hl
      change ((e6IsogenyT K (sX e6Data_valid K _ c) : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)
      have h : ((e6IsogenyT K (sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c) :
          adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) = f4OrbitXUnit K j c :=
        isogeny_sX K _ c
      rw [h]
      exact f4OrbitXUnit_mem j c
    · obtain ⟨j, rfl⟩ := orbs_eq l hl
      change ((e6IsogenyT K (sY e6Data_valid K _ c) : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)
      have h : ((e6IsogenyT K (sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c) :
          adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) = f4OrbitYUnit K j c :=
        isogeny_sY K _ c
      rw [h]
      exact f4OrbitYUnit_mem j c
  exact hle hg

@[expose] def isoToFixed : F4simple e6Data_valid K →* twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  (isoToGL K).codRestrict _ (isoToGL_mem K)

theorem isoToFixed_injective : Function.Injective (isoToFixed K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : e6IsogenyT K g.1 = 1 := by
    have := congrArg (fun x : twistedFixedGroup TwistTag.E6 K (RingHom.id K) =>
      (x : ModGL TwistTag.E6.tag K)) hg
    exact Subtype.ext this
  have h2 : g.1 ∈ (e6Isogeny K).ker := h1
  rw [e6Isogeny_ker_eq_center] at h2
  exact Subtype.ext (eq_one_of_mem_center_of_mem_F4in27 _ h2
    (by rw [F4in27_eq_F4simple]; exact g.2))

theorem isoToFixed_surjective : Function.Surjective (isoToFixed K) := by
  rintro ⟨x, hx⟩
  have hγ : x ∈ Subgroup.closure
      {g | ∃ (j : Fin Tag.F4.rank) (c : K), g = f4OrbitXUnit K j c ∨ g = f4OrbitYUnit K j c} :=
    twistedFixedGroup_id_eq_closure (K := K) ▸ hx
  have key : ∃ y : F4simple e6Data_valid K, isoToGL K y = x := by
    refine Subgroup.closure_induction (p := fun x _ => ∃ y : F4simple e6Data_valid K,
      isoToGL K y = x) ?_ ?_ ?_ ?_ hγ
    · rintro x ⟨j, c, rfl | rfl⟩
      · refine ⟨⟨sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
          sX_mem_F4simple _ (orbitWord_mem j) c⟩, ?_⟩
        exact isogeny_sX K _ c
      · refine ⟨⟨sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
          sY_mem_F4simple _ (orbitWord_mem j) c⟩, ?_⟩
        exact isogeny_sY K _ c
    · exact ⟨1, map_one _⟩
    · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, by rw [map_mul, ha, hb]⟩
    · rintro x _ ⟨a, ha⟩
      exact ⟨a⁻¹, by rw [map_inv, ha]⟩
  obtain ⟨y, hy⟩ := key
  exact ⟨y, Subtype.ext hy⟩

@[expose] def F4simpleEquivFixed :
    F4simple e6Data_valid K ≃* twistedFixedGroup TwistTag.E6 K (RingHom.id K) :=
  MulEquiv.ofBijective (isoToFixed K) ⟨isoToFixed_injective K, isoToFixed_surjective K⟩

@[expose] def f4in27Equiv : F4in27 e6Data_valid K ≃* adjointGroup Tag.F4 K :=
  (MulEquiv.subgroupCongr (F4in27_eq_F4simple e6Data_valid)).trans
    ((F4simpleEquivFixed K).trans (e6FixedF4Equiv K CharTwo.two_eq_zero))

theorem f4in27Equiv_apply (g : F4in27 e6Data_valid K) :
    ((f4in27Equiv K g : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      e6FixedToF4 K (isoToFixed K ⟨g.1, by rw [← F4in27_eq_F4simple e6Data_valid]; exact g.2⟩) :=
  rfl

theorem f4in27Equiv_sX (j : Fin Tag.F4.rank) (c : K) :
    ((f4in27Equiv K ⟨sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      sX_mem_F4in27 _ (orbitWord_mem j) c⟩ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      xUnit Tag.F4 K j c := by
  rw [f4in27Equiv_apply]
  have : isoToFixed K ⟨sX e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      by rw [← F4in27_eq_F4simple e6Data_valid]
         exact sX_mem_F4in27 _ (orbitWord_mem j) c⟩ =
      ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩ :=
    Subtype.ext (isogeny_sX K _ c)
  rw [this]
  exact e6FixedToF4_f4OrbitXUnit CharTwo.two_eq_zero j c

theorem f4in27Equiv_sY (j : Fin Tag.F4.rank) (c : K) :
    ((f4in27Equiv K ⟨sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      sY_mem_F4in27 _ (orbitWord_mem j) c⟩ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      yUnit Tag.F4 K j c := by
  rw [f4in27Equiv_apply]
  have : isoToFixed K ⟨sY e6Data_valid K (TwistTag.E6.orbitWord (f4FoldedIndex j)) c,
      by rw [← F4in27_eq_F4simple e6Data_valid]
         exact sY_mem_F4in27 _ (orbitWord_mem j) c⟩ =
      ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩ :=
    Subtype.ext (isogeny_sY K _ c)
  rw [this]
  exact e6FixedToF4_f4OrbitYUnit CharTwo.two_eq_zero j c

@[expose] def f4Embed (θ : adjointGroup Tag.F4 K ≃* adjointGroup Tag.F4 K) :
    adjointGroup Tag.F4 K →* e6Data_valid.minGroup K :=
  (F4in27 e6Data_valid K).subtype.comp
    (((f4in27Equiv K).symm : adjointGroup Tag.F4 K ≃* F4in27 e6Data_valid K).toMonoidHom.comp
      θ.toMonoidHom)

theorem f4Embed_injective (θ : adjointGroup Tag.F4 K ≃* adjointGroup Tag.F4 K) :
    Function.Injective (f4Embed K θ) := by
  intro a b h
  exact θ.injective ((f4in27Equiv K).symm.injective (Subtype.ext h))

theorem f4Embed_mem (θ : adjointGroup Tag.F4 K ≃* adjointGroup Tag.F4 K)
    (a : adjointGroup Tag.F4 K) : f4Embed K θ a ∈ F4in27 e6Data_valid K :=
  ((f4in27Equiv K).symm (θ a)).2

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
