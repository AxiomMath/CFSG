module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

universe u v

variable {X : Type u} {X' : Type v} [Group X] [Group X']

namespace TwoHSData

@[expose] noncomputable def mapMulEquiv (e : X ≃* X') (N : Subgroup X) :
    N ≃* N.map e.toMonoidHom :=
  Subgroup.equivMapOfInjective N e.toMonoidHom e.injective

instance instNormalMapMulEquiv (e : X ≃* X') (N : Subgroup X) [N.Normal] :
    (N.map e.toMonoidHom).Normal :=
  Subgroup.Normal.map ‹_› e.toMonoidHom e.surjective

@[expose] noncomputable def quotMapMulEquiv (e : X ≃* X') (N : Subgroup X) [N.Normal] :
    X ⧸ N ≃* X' ⧸ N.map e.toMonoidHom :=
  QuotientGroup.congr N (N.map e.toMonoidHom) e rfl

private theorem map_subgroupOf_mapMulEquiv (e : X ≃* X') (V N : Subgroup X) :
    (V.subgroupOf N).map (mapMulEquiv e N).toMonoidHom =
      (V.map e.toMonoidHom).subgroupOf (N.map e.toMonoidHom) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨v, hv, hvx⟩
    have hv' : (v : X) ∈ V := Subgroup.mem_subgroupOf.mp hv
    have hxval : (x : X') = e (v : X) := by
      rw [← hvx]
      rfl
    rw [hxval]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hv'
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hyN : y ∈ N := by
      obtain ⟨z, hzN, hzx⟩ := Subgroup.mem_map.mp x.2
      have hzy : z = y := e.injective (hzx.trans hyx.symm)
      rwa [hzy] at hzN
    refine Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    apply Subtype.ext
    change e y = (x : X')
    exact hyx

theorem nonempty_subquot_mulEquiv (e : X ≃* X') (V N : Subgroup X) [V.Normal] :
    Nonempty (N ⧸ V.subgroupOf N ≃*
      (N.map e.toMonoidHom) ⧸ (V.map e.toMonoidHom).subgroupOf (N.map e.toMonoidHom)) :=
  ⟨QuotientGroup.congr (V.subgroupOf N)
    ((V.map e.toMonoidHom).subgroupOf (N.map e.toMonoidHom)) (mapMulEquiv e N)
    (map_subgroupOf_mapMulEquiv e V N)⟩

theorem isComplement'_map_mulEquiv (e : X ≃* X') {A B : Subgroup X} (h : A.IsComplement' B) :
    (A.map e.toMonoidHom).IsComplement' (B.map e.toMonoidHom) := by
  rw [Subgroup.isComplement'_def] at h ⊢
  refine isComplement_iff_existsUnique.mpr fun g => ?_
  obtain ⟨⟨a, b⟩, hab, huniq⟩ := isComplement_iff_existsUnique.mp h (e.symm g)
  refine ⟨(⟨e ↑a, Subgroup.mem_map_of_mem e.toMonoidHom (show (a : X) ∈ A from a.2)⟩,
    ⟨e ↑b, Subgroup.mem_map_of_mem e.toMonoidHom (show (b : X) ∈ B from b.2)⟩), ?_, ?_⟩
  · show e ↑a * e ↑b = g
    rw [← map_mul, hab, e.apply_symm_apply]
  · rintro ⟨y1, y2⟩ hy
    have hy1mem : e.symm (y1 : X') ∈ A :=
      (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := A)).mp
        (by simpa using y1.2)
    have hy2mem : e.symm (y2 : X') ∈ B :=
      (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective (K := B)).mp
        (by simpa using y2.2)
    have hy'mul :
        ((⟨e.symm (y1 : X'), hy1mem⟩ : A) : X) * ((⟨e.symm (y2 : X'), hy2mem⟩ : B) : X) =
          e.symm g := by
      show e.symm (y1 : X') * e.symm (y2 : X') = e.symm g
      rw [← map_mul, hy]
    have hy'eq := huniq (⟨e.symm (y1 : X'), hy1mem⟩, ⟨e.symm (y2 : X'), hy2mem⟩) hy'mul
    have h1 : e.symm (y1 : X') = (a : X) :=
      congrArg (fun z : A × B => ((z.1 : A) : X)) hy'eq
    have h2 : e.symm (y2 : X') = (b : X) :=
      congrArg (fun z : A × B => ((z.2 : B) : X)) hy'eq
    apply Prod.ext
    · apply Subtype.ext
      show (y1 : X') = e ↑a
      rw [← h1, e.apply_symm_apply]
    · apply Subtype.ext
      show (y2 : X') = e ↑b
      rw [← h2, e.apply_symm_apply]

private theorem isElemAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) [h : CFSG.IsElementaryAbelian p A] : CFSG.IsElementaryAbelian p B where
  toIsMulCommutative := ⟨⟨fun a b => by
    have := congrArg e (mul_comm' (e.symm a) (e.symm b))
    simpa using this⟩⟩
  exponent_dvd_p := by
    rw [← Monoid.exponent_eq_of_mulEquiv e]
    exact CFSG.IsElementaryAbelian.exponent_dvd_p p A

theorem isExtraspecial_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsExtraspecial p A) : CFSG.IsExtraspecial p B where
  center_order_p := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact h.center_order_p
  quotient_elementary_abelian := by
    haveI := h.quotient_elementary_abelian
    exact isElemAbelian_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e))
  quotient_nontrivial := by
    haveI := h.quotient_nontrivial
    exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).symm.toEquiv.nontrivial

end TwoHSData

open TwoHSData

theorem IsExtensionShape.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : X ≃* X')
    (h : IsExtensionShape X A B) : IsExtensionShape X' A B := by
  obtain ⟨N, hN, h1, h2⟩ := h
  haveI : N.Normal := hN
  obtain ⟨isoN⟩ := h1
  obtain ⟨isoQ⟩ := h2
  exact ⟨N.map e.toMonoidHom, Subgroup.Normal.map hN e.toMonoidHom e.surjective,
    ⟨(mapMulEquiv e N).symm.trans isoN⟩, ⟨(quotMapMulEquiv e N).symm.trans isoQ⟩⟩

theorem IsShapeTwoTwoSixS5.of_mulEquiv (e : X ≃* X') (h : IsShapeTwoTwoSixS5 X) :
    IsShapeTwoTwoSixS5 X' := by
  obtain ⟨V, N, hV, hN, hVN, h1, h2, h3⟩ := h
  haveI : V.Normal := hV
  haveI : N.Normal := hN
  obtain ⟨isoV⟩ := h1
  obtain ⟨isoQ⟩ := h2
  obtain ⟨isoX⟩ := h3
  refine ⟨V.map e.toMonoidHom, N.map e.toMonoidHom,
    Subgroup.Normal.map hV e.toMonoidHom e.surjective,
    Subgroup.Normal.map hN e.toMonoidHom e.surjective,
    Subgroup.map_mono hVN, ?_, ?_, ?_⟩
  · exact ⟨(mapMulEquiv e V).symm.trans isoV⟩
  · exact ⟨(nonempty_subquot_mulEquiv e V N).some.symm.trans isoQ⟩
  · exact ⟨(quotMapMulEquiv e N).symm.trans isoX⟩

theorem IsShapeTwoTwoTimesA8.of_mulEquiv (e : X ≃* X') (h : IsShapeTwoTwoTimesA8 X) :
    IsShapeTwoTwoTimesA8 X' :=
  ⟨e.symm.trans h.some⟩

theorem IsShapeTwoTwoTimesTwoFourA5.of_mulEquiv (e : X ≃* X')
    (h : IsShapeTwoTwoTimesTwoFourA5 X) : IsShapeTwoTwoTimesTwoFourA5 X' := by
  obtain ⟨Y, hY, hshape, hiso⟩ := h
  exact ⟨Y, hY, hshape, ⟨e.symm.trans hiso.some⟩⟩

theorem IsNonsplitDoubleCoverOfS5.of_mulEquiv (e : X ≃* X') (h : IsNonsplitDoubleCoverOfS5 X) :
    IsNonsplitDoubleCoverOfS5 X' := by
  obtain ⟨Z, hZ, hcard, hisoQ, hcomm⟩ := h
  refine ⟨Z.map e.toMonoidHom, Subgroup.Normal.map hZ e.toMonoidHom e.surjective, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (mapMulEquiv e Z).toEquiv]
    exact hcard
  · exact ⟨(quotMapMulEquiv e Z).symm.trans hisoQ.some⟩
  · have hc : (commutator X).map e.toMonoidHom = commutator X' := by
      rw [_root_.map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    rw [← hc]
    exact Subgroup.map_mono hcomm

theorem IsShapeCentralizerThree.of_mulEquiv (e : X ≃* X') (h : IsShapeCentralizerThree X) :
    IsShapeCentralizerThree X' := by
  obtain ⟨Y, hY, hshape, hiso⟩ := h
  exact ⟨Y, hY, hshape, ⟨e.symm.trans hiso.some⟩⟩

theorem IsShapeCentralizerFiveA.of_mulEquiv (e : X ≃* X') (h : IsShapeCentralizerFiveA X) :
    IsShapeCentralizerFiveA X' := by
  obtain ⟨N, S, hN, hExt, hcard, hexp, hisoS, hcompl⟩ := h
  refine ⟨N.map e.toMonoidHom, S.map e.toMonoidHom,
    Subgroup.Normal.map hN e.toMonoidHom e.surjective, ?_, ?_, ?_, ?_, ?_⟩
  · exact isExtraspecial_of_mulEquiv (mapMulEquiv e N) hExt
  · rw [← Nat.card_congr (mapMulEquiv e N).toEquiv]
    exact hcard
  · intro x
    rw [← (mapMulEquiv e N).apply_symm_apply x, ← map_pow, hexp, map_one]
  · exact ⟨(mapMulEquiv e S).symm.trans hisoS.some⟩
  · exact isComplement'_map_mulEquiv e hcompl

theorem IsShapeCentralizerFiveB.of_mulEquiv (e : X ≃* X') (h : IsShapeCentralizerFiveB X) :
    IsShapeCentralizerFiveB X' :=
  ⟨e.symm.trans h.some⟩

theorem IsShapeCentralizerFiveC.of_mulEquiv (e : X ≃* X') (h : IsShapeCentralizerFiveC X) :
    IsShapeCentralizerFiveC X' := by
  obtain ⟨Y, hY, hshape, hiso⟩ := h
  exact ⟨Y, hY, hshape, ⟨e.symm.trans hiso.some⟩⟩

theorem IsShapeCentralizerSeven.of_mulEquiv (e : X ≃* X') (h : IsShapeCentralizerSeven X) :
    IsShapeCentralizerSeven X' :=
  ⟨e.symm.trans h.some⟩

theorem IsShapeCentralizerEleven.of_mulEquiv (e : X ≃* X') (h : IsShapeCentralizerEleven X) :
    IsShapeCentralizerEleven X' :=
  ⟨e.symm.trans h.some⟩

end CFSG.EvenSporadicStandard.HNRecog
