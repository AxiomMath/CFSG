module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti
  commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll mem_fixAll consecutiveBlock mem_consecutiveBlock)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective liftParam
  planeTorusParam)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open scoped MatrixGroups

section Frame

variable {G : Type} [Group G] {F : Type} [Field F] {r : ℕ} (τ : (Fin (r + 1) → Fˣ) →* G)

@[expose] noncomputable def q2FrameCore (P : Subgroup (Fin (r + 1) → Fˣ)) : Subgroup G :=
  centralizerPerfectCore (P.map τ)

@[expose] noncomputable def q2NbrCore (k : Fin (r + 1)) : Subgroup G :=
  q2FrameCore τ (rootParam k)

@[expose] noncomputable def q2LevelCore (J : Finset (Fin (r + 1))) : Subgroup G :=
  q2FrameCore τ (levelParam J)

@[expose] noncomputable def q2PieceCore (I : Finset (Fin (r + 1))) : Subgroup G :=
  q2FrameCore τ (planeTorusParam F I)

theorem commute_frame (t s : Fin (r + 1) → Fˣ) : Commute (τ t) (τ s) := by
  change τ t * τ s = τ s * τ t
  rw [← map_mul, ← map_mul, mul_comm]

theorem frame_mem_normalizer_q2FrameCore [Finite G] (P : Subgroup (Fin (r + 1) → Fˣ))
    (t : Fin (r + 1) → Fˣ) : τ t ∈ normalizer (q2FrameCore τ P : Set G) := by
  refine F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
    (Subgroup.centralizer_le_normalizer _ ?_)
  rw [mem_centralizer_iff]
  rintro _ ⟨s, -, rfl⟩
  exact (commute_frame τ s t).eq

theorem q2FrameCore_le_q2NbrCore {P : Subgroup (Fin (r + 1) → Fˣ)} {k : Fin (r + 1)}
    (hk : rootParam k ≤ P) : q2FrameCore τ P ≤ q2NbrCore τ k :=
  centralizerPerfectCore_anti (Subgroup.map_mono hk)

theorem q2LevelCore_le_q2NbrCore {J : Finset (Fin (r + 1))} {k : Fin (r + 1)} (hk : k ∉ J) :
    q2LevelCore τ J ≤ q2NbrCore τ k :=
  q2FrameCore_le_q2NbrCore τ (rootParam_le_levelParam hk)

theorem q2PieceCore_le_q2NbrCore {I : Finset (Fin (r + 1))} {k : Fin (r + 1)} (hk : k ∉ I) :
    q2PieceCore τ I ≤ q2NbrCore τ k :=
  q2FrameCore_le_q2NbrCore τ (rootParam_le_planeTorusParam hk)

theorem commutator_q2FrameCore [Finite G] (P : Subgroup (Fin (r + 1) → Fˣ)) :
    ⁅q2FrameCore τ P, q2FrameCore τ P⁆ = q2FrameCore τ P :=
  commutator_centralizerPerfectCore _

end Frame

section Chart

variable {G : Type} [Group G] {F : Type} [Field F] {r : ℕ}

structure Q2FrameChart (τ : (Fin (r + 1) → Fˣ) →* G) (k : Fin (r + 1)) where
  π : q2NbrCore τ k ≃* StatedOmega (StatedQuadPlus (r + 1) F)
  equivariant : ∀ (t : Fin (r + 1) → Fˣ) (hN : τ t ∈ normalizer (q2NbrCore τ k : Set G))
    (x : q2NbrCore τ k),
    π ((q2NbrCore τ k).normalizerMonoidHom ⟨_, hN⟩ x) =
      (StatedOmega (StatedQuadPlus (r + 1) F)).normalizerMonoidHom
        ⟨minusNeighbourDiag (RingHom.id F) k t, minusNeighbourDiag_mem_normalizer _ k t⟩ (π x)

variable {τ : (Fin (r + 1) → Fˣ) →* G} {k : Fin (r + 1)}

@[expose] noncomputable def Q2FrameChart.toGL (C : Q2FrameChart τ k) :
    q2NbrCore τ k →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
  (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp C.π.toMonoidHom

theorem Q2FrameChart.toGL_injective (C : Q2FrameChart τ k) : Function.Injective C.toGL :=
  Subtype.val_injective.comp C.π.injective

theorem Q2FrameChart.ker_toGL_le (C : Q2FrameChart τ k) :
    C.toGL.ker ≤ center (q2NbrCore τ k) := by
  rw [(MonoidHom.ker_eq_bot_iff _).2 C.toGL_injective]
  exact bot_le

theorem Q2FrameChart.map_toGL (C : Q2FrameChart τ k) (A : Subgroup (q2NbrCore τ k)) :
    A.map C.toGL = (A.map C.π.toMonoidHom).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype :=
  (Subgroup.map_map _ _ _).symm

theorem Q2FrameChart.range_toGL (C : Q2FrameChart τ k) :
    C.toGL.range = StatedOmega (StatedQuadPlus (r + 1) F) := by
  rw [Q2FrameChart.toGL, MonoidHom.range_comp, MonoidHom.range_eq_top.2 C.π.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

end Chart

section Glue

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G} {k : Fin (r + 1)}

theorem Q2FrameChart.map_frameCore (C : Q2FrameChart τ k) {P : Subgroup (Fin (r + 1) → Fˣ)}
    (hkP : rootParam k ≤ P) :
    (((q2FrameCore τ P).subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      perfectCore (StatedOmega (StatedQuadPlus (r + 1) F) ⊓
        centralizer (minusNeighbourDiag (RingHom.id F) k '' (P : Set (Fin (r + 1) → Fˣ)))) := by
  set S := StatedOmega (StatedQuadPlus (r + 1) F) with hS
  set E := q2NbrCore τ k with hE
  have hXT : (rootParam k).map τ ≤ P.map τ := Subgroup.map_mono hkP
  have hN : ∀ d : P.map τ, (d : G) ∈ normalizer (E : Set G) := fun d => by
    obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 d.2
    rw [← ht]
    exact frame_mem_normalizer_q2FrameCore τ _ t
  let α : P.map τ → MulAut E := fun d => E.normalizerMonoidHom ⟨d, hN d⟩
  let β : P.map τ → MulAut S := fun d => (C.π.symm.trans (α d)).trans C.π
  have hαβ : ∀ d x, C.π.toMonoidHom (α d x) = β d (C.π.toMonoidHom x) := by
    intro d x
    simp [β]
  have hker : C.π.toMonoidHom.ker ≤ center (centralizerPerfectCore ((rootParam k).map τ)) := by
    intro x hx
    have hx1 : x = 1 := C.π.injective ((MonoidHom.mem_ker.1 hx).trans (map_one C.π).symm)
    rw [hx1]
    exact one_mem _
  have h1 := map_centralizerPerfectCore_subgroupOf_eq hXT C.π.toMonoidHom C.π.surjective
    hker α (fun _ _ => rfl) β hαβ
  have hβ : ∀ (t : Fin (r + 1) → Fˣ) (ht : t ∈ P) (z : S),
      β ⟨τ t, t, ht, rfl⟩ z = S.normalizerMonoidHom
        ⟨minusNeighbourDiag (RingHom.id F) k t, minusNeighbourDiag_mem_normalizer _ k t⟩ z := by
    intro t ht z
    change C.π (E.normalizerMonoidHom ⟨τ t, hN ⟨τ t, t, ht, rfl⟩⟩ (C.π.symm z)) = _
    rw [C.equivariant t _ (C.π.symm z), MulEquiv.apply_symm_apply]
  have h2 : (fixAll β).map S.subtype =
      S ⊓ centralizer (minusNeighbourDiag (RingHom.id F) k '' (P : Set (Fin (r + 1) → Fˣ))) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.2 ⟨z.2, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have hc : minusNeighbourDiag (RingHom.id F) k t * (z : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) *
          (minusNeighbourDiag (RingHom.id F) k t)⁻¹ = z :=
        congrArg Subtype.val ((hβ t ht z).symm.trans (mem_fixAll.1 hz ⟨τ t, t, ht, rfl⟩))
      calc minusNeighbourDiag (RingHom.id F) k t * (z : GL (Fin (r + 1) ⊕ Fin (r + 1)) F)
          = minusNeighbourDiag (RingHom.id F) k t * (z : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) *
              (minusNeighbourDiag (RingHom.id F) k t)⁻¹ *
              minusNeighbourDiag (RingHom.id F) k t := by group
        _ = (z : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) * minusNeighbourDiag (RingHom.id F) k t := by
          rw [hc]
    · intro hy'
      obtain ⟨hyS, hy⟩ := Subgroup.mem_inf.1 hy'
      refine ⟨⟨y, hyS⟩, mem_fixAll.2 fun d => ?_, rfl⟩
      obtain ⟨t, ht, hd⟩ := Subgroup.mem_map.1 d.2
      have hd' : d = ⟨τ t, t, ht, rfl⟩ := Subtype.ext hd.symm
      rw [hd', hβ t ht]
      apply Subtype.ext
      change minusNeighbourDiag (RingHom.id F) k t * y *
        (minusNeighbourDiag (RingHom.id F) k t)⁻¹ = y
      rw [mem_centralizer_iff.1 hy _ ⟨t, ht, rfl⟩, mul_inv_cancel_right]
  refine (congrArg (fun H => H.map S.subtype) h1).trans ?_
  rw [CFSG.Quasithin.map_perfectCore, h2]

theorem Q2FrameChart.map_levelCore (C : Q2FrameChart τ k) (hF : 4 ≤ Nat.card F)
    {J : Finset (Fin (r + 1))} (hk : k ∉ J) (hJ : 2 ≤ J.card) :
    (((q2LevelCore τ J).subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      siegelBlockGL F (castSuccPlanes (preimagePlanes k J)) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hF
  have hJ' : 2 ≤ (preimagePlanes k J).card := by
    rw [card_preimagePlanes hk]
    exact hJ
  rw [q2LevelCore, C.map_frameCore (rootParam_le_levelParam hk), image_minusNeighbourDiag,
    image_restrictParam_levelParam hk,
    perfectCore_statedOmega_inf_centralizer_snocLevel hF (RingHom.id F) hκ hJ']

theorem Q2FrameChart.map_pieceCore [CharP F 2] (C : Q2FrameChart τ k) (hF : 4 ≤ Nat.card F)
    {I : Finset (Fin (r + 1))} (hk : k ∉ I) (hI : I.Nonempty) :
    (((q2PieceCore τ I).subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (StatedOmega (StatedQuadPlus
          (insert (Fin.last r) (castSuccPlanes (preimagePlanes k I))).card F)).map
        (spEmbedGL (planeEnum (insert (Fin.last r) (castSuccPlanes (preimagePlanes k I))))
          (planeEnum_injective _)) := by
  obtain ⟨κ, hκ⟩ := SymplecticPilot.exists_units_mul_self_ne_one_of_four_le hF
  have hI' : (preimagePlanes k I).Nonempty := by
    rw [← Finset.card_pos, card_preimagePlanes hk]
    exact hI.card_pos
  rw [q2PieceCore, C.map_frameCore (rootParam_le_planeTorusParam hk), image_minusNeighbourDiag,
    image_restrictParam_planeTorusParam hk,
    perfectCore_statedOmega_inf_centralizer_snocPlane hF (RingHom.id F) hκ hI']

end Glue

section Pairs

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G} {k : Fin (r + 1)}

@[expose] noncomputable def Q2FrameChart.lift (C : Q2FrameChart τ k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) : Subgroup G :=
  perfectCore ((B.comap C.toGL).map (q2NbrCore τ k).subtype)

theorem Q2FrameChart.lift_eq (C : Q2FrameChart τ k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) :
    C.lift B = (perfectCore (B.comap C.toGL)).map (q2NbrCore τ k).subtype :=
  (CFSG.Quasithin.map_perfectCore _ _).symm

theorem Q2FrameChart.lift_le (C : Q2FrameChart τ k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) : C.lift B ≤ q2NbrCore τ k := by
  rw [C.lift_eq]
  exact map_subtype_le _

theorem Q2FrameChart.commutator_lift (C : Q2FrameChart τ k)
    (B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)) : ⁅C.lift B, C.lift B⁆ = C.lift B :=
  perfectCore_perfect _

theorem Q2FrameChart.map_lift (C : Q2FrameChart τ k)
    {B : Subgroup (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)}
    (hBΩ : B ≤ StatedOmega (StatedQuadPlus (r + 1) F)) (hBp : ⁅B, B⁆ = B) :
    (((C.lift B).subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
      (StatedOmega (StatedQuadPlus (r + 1) F)).subtype = B := by
  have hsub : (C.lift B).subgroupOf (q2NbrCore τ k) = perfectCore (B.comap C.toGL) := by
    rw [C.lift_eq]
    ext x
    rw [mem_subgroupOf, mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← C.map_toGL, hsub, CFSG.Quasithin.map_perfectCore, Subgroup.map_comap_eq, C.range_toGL,
    inf_of_le_right hBΩ]
  exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hBp

theorem Q2FrameChart.le_centralizer (C : Q2FrameChart τ k) {A B : Subgroup G}
    (hA : A ≤ q2NbrCore τ k) (hB : B ≤ q2NbrCore τ k)
    (h : ∀ x ∈ ((A.subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype,
      ∀ y ∈ ((B.subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype, Commute x y) :
    A ≤ centralizer (B : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have hc := h _ ⟨C.π ⟨a, hA ha⟩, ⟨⟨a, hA ha⟩, ha, rfl⟩, rfl⟩ _
    ⟨C.π ⟨b, hB hb⟩, ⟨⟨b, hB hb⟩, hb, rfl⟩, rfl⟩
  have h2 : C.toGL (⟨b, hB hb⟩ * ⟨a, hA ha⟩) = C.toGL (⟨a, hA ha⟩ * ⟨b, hB hb⟩) := by
    rw [map_mul, map_mul]
    exact hc.eq.symm
  exact congrArg Subtype.val (C.toGL_injective h2)

theorem Q2FrameChart.exists_theta_of_images (C : Q2FrameChart τ k) (hF : 4 ≤ Nat.card F)
    {U V : Subgroup G} (hUE : U ≤ q2NbrCore τ k) (hVE : V ≤ q2NbrCore τ k) {a : ℕ}
    (ha : a + 3 ≤ r + 1) (P : Finset (Fin (r + 1)))
    (hU : ((U.subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) a 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom)
    (hV : ((V.subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      (siegelBlockGL F (consecutiveBlock (r + 1) (a + 1) 2)).map
        (MulAut.conj (flipGL F P)).toMonoidHom) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = U ∧ (B23 F).map θ = V := by
  set S := StatedOmega (StatedQuadPlus (r + 1) F) with hS
  set E := q2NbrCore τ k with hE
  have hθS : ∀ A, modelTheta F a ha P A ∈ S := by
    intro A
    have hA : modelTheta F a ha P A ∈ (modelTheta F a ha P).range := ⟨A, rfl⟩
    rw [range_modelTheta] at hA
    obtain ⟨x, hx, hxA⟩ := hA
    rw [← hxA]
    exact (mem_normalizer_iff.1 (flipGL_mem_normalizer (F := F) P) x).1
      (siegelBlockGL_le_statedOmega hF (by rw [card_consecutiveBlock (by omega)]; omega) hx)
  let θ₀ : SL(3, F) →* S := (modelTheta F a ha P).codRestrict S hθS
  have hθ₀ : S.subtype.comp θ₀ = modelTheta F a ha P := rfl
  have hid : C.π.symm.toMonoidHom.comp C.π.toMonoidHom = MonoidHom.id E := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have key : ∀ (W : Subgroup G) (B : Subgroup SL(3, F)), W ≤ E →
      ((W.subgroupOf E).map C.π.toMonoidHom).map S.subtype = B.map (modelTheta F a ha P) →
      B.map (E.subtype.comp (C.π.symm.toMonoidHom.comp θ₀)) = W := by
    intro W B hWE hWB
    have h1 : (W.subgroupOf E).map C.π.toMonoidHom = B.map θ₀ := by
      apply Subgroup.map_injective S.subtype_injective
      rw [hWB, Subgroup.map_map, hθ₀]
    have h2 : W.subgroupOf E = (B.map θ₀).map C.π.symm.toMonoidHom := by
      rw [← h1, Subgroup.map_map, hid, Subgroup.map_id]
    rw [← Subgroup.map_map, ← Subgroup.map_map, ← h2, subgroupOf_map_subtype,
      inf_of_le_left hWE]
  have hinj : Function.Injective (E.subtype.comp (C.π.symm.toMonoidHom.comp θ₀)) := by
    intro x y hxy
    apply modelTheta_injective a ha P
    have h1 := C.π.symm.injective (Subtype.val_injective hxy)
    exact congrArg Subtype.val h1
  refine ⟨E.subtype.comp (C.π.symm.toMonoidHom.comp θ₀), ?_,
    key U (B12 F) hUE (by rw [hU, map_B12_modelTheta]),
    key V (B23 F) hVE (by rw [hV, map_B23_modelTheta])⟩
  intro A hA
  have hA1 : A = 1 := hinj ((MonoidHom.mem_ker.1 hA).trans (map_one _).symm)
  rw [hA1]
  exact one_mem _

end Pairs

end CFSG.SeitzReduction.OmegaPilot
