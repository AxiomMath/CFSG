module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRowsUnique
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Conj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandard

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

inductive OmegaRow
  | field
  | swap
  deriving DecidableEq

section Abstract

variable {Y : Type} [Group Y]

@[expose] def NeighbourRowOmega (s : Y) (D : Subgroup Y) (r : OmegaRow) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    (r = .field ↔ Kc.map (MulAut.conj s).toMonoidHom = Kc)

theorem neighbourRowOmega_of_alternative {s : Y} {D Kc : Subgroup Y} {m f : ℕ}
    (hKc : IsComponent Kc) (h : OmegaNeighbourAlternative s D Kc m f) :
    ∃ r : OmegaRow, NeighbourRowOmega s D r ∧
      (r = .field ↔ Kc.map (MulAut.conj s).toMonoidHom = Kc) := by
  by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
  · exact ⟨.field, ⟨Kc, hKc, h.1, iff_of_true rfl hKt⟩, iff_of_true rfl hKt⟩
  · exact ⟨.swap, ⟨Kc, hKc, h.1, iff_of_false (by decide) hKt⟩, iff_of_false (by decide) hKt⟩

theorem NeighbourRowOmega.unique [Finite Y] {s : Y} (hs : s ^ 2 = 1) {D : Subgroup Y}
    (hDperf : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) {r r' : OmegaRow} (h : NeighbourRowOmega s D r)
    (h' : NeighbourRowOmega s D r') : r = r' := by
  obtain ⟨Kc, hKc, hDK, hr⟩ := h
  obtain ⟨Kc', hKc', hDK', hr'⟩ := h'
  have hKK : Kc'.map (MulAut.conj s).toMonoidHom = Kc' ↔
      Kc.map (MulAut.conj s).toMonoidHom = Kc := by
    rcases SymplecticPilot.eq_or_eq_map_conj_of_le_sup hs hDperf hD1 hKc hKc' hDK hDK' with h | h
    · rw [h]
    · rw [h, SymplecticPilot.map_conj_map_conj_of_sq_eq_one hs]
      exact ⟨fun h1 => h1.symm, fun h1 => h1.symm⟩
  cases r <;> cases r'
  · rfl
  · exact absurd (hr'.2 (hKK.2 (hr.1 rfl))) (by decide)
  · exact absurd (hr.2 (hKK.1 (hr'.1 rfl))) (by decide)
  · rfl

variable {Y' : Type} [Group Y']

theorem NeighbourRowOmega.map_mulEquiv (γ : Y ≃* Y') {s : Y} {D : Subgroup Y} {r : OmegaRow}
    (h : NeighbourRowOmega s D r) : NeighbourRowOmega (γ s) (D.map γ.toMonoidHom) r := by
  obtain ⟨Kc, hKc, hDK, hr⟩ := h
  refine ⟨Kc.map γ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv γ hKc, ?_, ?_⟩
  · rw [← SymplecticPilot.map_map_conj_mulEquiv, ← Subgroup.map_sup]
    exact map_mono hDK
  · rw [hr, ← SymplecticPilot.map_map_conj_mulEquiv]
    exact ⟨fun h1 => by rw [h1], fun h1 => map_injective γ.injective h1⟩

end Abstract

section Ambient

variable {G : Type} [Group G]

@[expose] def OmegaRowAt (t : G) (X D : Subgroup G) (r : OmegaRow) : Prop :=
  ∃ htX : t ∈ centralizer (X : Set G),
    NeighbourRowOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) r

theorem exists_omegaRowAt_of_neighbourOvergroupOmega {t : G} {X D : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) {m f : ℕ}
    (h : NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f) :
    ∃ r : OmegaRow, OmegaRowAt t X D r := by
  obtain ⟨Kc, hKc, hK⟩ := h
  obtain ⟨r, hr, -⟩ := neighbourRowOmega_of_alternative hKc hK
  exact ⟨r, htX, hr⟩

theorem OmegaRowAt.unique [Finite G] {t : G} (ht : orderOf t = 2) {X D : Subgroup G}
    (hDq : ∀ htX : t ∈ centralizer (X : Set G), CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    {r r' : OmegaRow} (h : OmegaRowAt t X D r) (h' : OmegaRowAt t X D r') : r = r' := by
  obtain ⟨htX, hr⟩ := h
  obtain ⟨_, hr'⟩ := h'
  have h2 : (⟨t, htX⟩ : centralizer (X : Set G)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← ht]
    exact pow_orderOf_eq_one t
  have hs : (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow, h2, map_one]
  exact NeighbourRowOmega.unique hs
    (SymplecticPilot.commutator_eq_self_of_isQuasisimple (hDq htX).2.2)
    (ne_bot_of_isQuasisimple (hDq htX).2.2) hr hr'

variable {G' : Type} [Group G']

theorem OmegaRowAt.map_mulEquiv [Finite G] [Finite G'] (α : G ≃* G') {t : G}
    {X D : Subgroup G} {r : OmegaRow} (h : OmegaRowAt t X D r) :
    OmegaRowAt (α t) (X.map α.toMonoidHom) (D.map α.toMonoidHom) r := by
  obtain ⟨htX, hK⟩ := h
  have htX' : α t ∈ centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G') :=
    (SymplecticPilot.centralizerCongr α X ⟨t, htX⟩).2
  refine ⟨htX', ?_⟩
  have h1 := hK.map_mulEquiv
    (SymplecticPilot.quotientOddCoreCongr (SymplecticPilot.centralizerCongr α X))
  have hs : SymplecticPilot.quotientOddCoreCongr (SymplecticPilot.centralizerCongr α X)
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) =
      QuotientGroup.mk' (oddCore (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G')))
        ⟨α t, htX'⟩ := rfl
  have hD : ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).map
        (SymplecticPilot.quotientOddCoreCongr (SymplecticPilot.centralizerCongr α X)).toMonoidHom =
      ((D.map α.toMonoidHom).subgroupOf
          (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G'))).map
        (QuotientGroup.mk'
          (oddCore (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G')))) := by
    rw [← SymplecticPilot.map_subgroupOf_centralizerCongr, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hs, hD] at h1
  exact h1

theorem OmegaRowAt.map_conj_of_commute [Finite G] {g t : G} (hg : g * t = t * g)
    {X D : Subgroup G} {r : OmegaRow} (h : OmegaRowAt t X D r) :
    OmegaRowAt t (X.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom) r := by
  have h1 := h.map_mulEquiv (MulAut.conj g)
  rwa [show MulAut.conj g t = t by rw [MulAut.conj_apply, hg, mul_inv_cancel_right]] at h1

end Ambient

section Swap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b a' b' : Fin d}

@[expose] noncomputable def pairSwap (Q : QuadraticForm K (Fin d → K)) (a b a' b' : Fin d) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  eichler Q (Pi.single a 1 + Pi.single a' 1) (Pi.single b 1 + Pi.single b' 1)

theorem pairSwap_comm : pairSwap Q a b a' b' = pairSwap Q a' b' a b := by
  unfold pairSwap
  congr 1 <;> exact add_comm _ _

theorem pairSwap_hyp [CharP K 2] (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') :
    Q (Pi.single a 1 + Pi.single a' 1) = 0 ∧
      polar Q (Pi.single a 1 + Pi.single a' 1) (Pi.single b 1 + Pi.single b' 1) = 0 := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_⟩
  · rw [QuadraticMap.map_add Q, h.map_left, h'.map_left, h.polar_left,
      Pi.single_eq_of_ne hd.left_ne_right.symm]
    simp
  · rw [polar_add_left, polar_add_right, polar_add_right, h.polar_left, h.polar_left,
      h'.polar_left, h'.polar_left, Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_of_ne hd.right_ne_right.symm, Pi.single_eq_of_ne hd.right_ne_right]
    linear_combination htwo

theorem pairSwap_hyp_right (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') : Q (Pi.single b 1 + Pi.single b' 1) = 0 := by
  rw [QuadraticMap.map_add Q, h.map_right, h'.map_right, h.polar_right,
    Pi.single_eq_of_ne hd.right_ne_left.symm]
  simp

theorem pairSwap_apply_left [CharP K 2] (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') :
    pairSwap Q a b a' b' (Pi.single a 1) = Pi.single a' 1 ∧
      pairSwap Q a b a' b' (Pi.single b 1) = Pi.single b' 1 := by
  obtain ⟨hu, hw⟩ := pairSwap_hyp h h' hd
  have hQw := pairSwap_hyp_right h h' hd
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_⟩
  · have hub : (Pi.single a (1 : K) + Pi.single a' 1 : Fin d → K) b = 0 := by
      rw [Pi.add_apply, Pi.single_eq_of_ne h.ne.symm, Pi.single_eq_of_ne hd.left_ne_right.symm,
        add_zero]
    have hwb : (Pi.single b (1 : K) + Pi.single b' 1 : Fin d → K) b = 1 := by
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hd.right_ne_right.symm, add_zero]
    rw [pairSwap, eichler_apply hu hw, h.polar_left, h.polar_left, hub, hwb, hQw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(Pi.single a' (1 : K) : Fin d → K) i) * htwo
  · have hua : (Pi.single a (1 : K) + Pi.single a' 1 : Fin d → K) a = 1 := by
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hd.left_ne_left.symm, add_zero]
    have hwa : (Pi.single b (1 : K) + Pi.single b' 1 : Fin d → K) a = 0 := by
      rw [Pi.add_apply, Pi.single_eq_of_ne h.ne, Pi.single_eq_of_ne hd.right_ne_left.symm,
        add_zero]
    rw [pairSwap, eichler_apply hu hw, h.polar_right, h.polar_right, hua, hwa, hQw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((Pi.single b (1 : K) : Fin d → K) i) * htwo

theorem pairSwap_mem_orthDerived [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    pairSwap Q a b a' b' ∈ orthDerived Q :=
  eichler_mem_orthDerived hQ hT _ _

variable [CharP K 2]

theorem pairSwap_conj_torusLin (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') (c : Kˣ) :
    pairSwap Q a b a' b' * torusLin a b c * (pairSwap Q a b a' b')⁻¹ = torusLin a' b' c := by
  obtain ⟨ha, hb⟩ := pairSwap_apply_left h h' hd
  refine (eq_conj_torusLin_of_apply h (eichler_mem_orthogonalGroup Q _ _) ha hb
    (torusLin_single_left h'.ne c) (torusLin_single_right h'.ne c) fun x hxu hxv => ?_).symm
  rw [polar_comm, h'.polar_left] at hxu
  rw [polar_comm, h'.polar_right] at hxv
  exact torusLin_eq_self_of hxv hxu c

theorem pairSwap_conj_mem_stabSub (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hx : x ∈ stabSub a b) :
    pairSwap Q a b a' b' * x * (pairSwap Q a b a' b')⁻¹ ∈ stabSub a' b' := by
  obtain ⟨ha, hb⟩ := pairSwap_apply_left h h' hd
  obtain ⟨hxa, hxb⟩ := mem_stabSub.1 hx
  have ha' : (pairSwap Q a b a' b')⁻¹ (Pi.single a' 1) = Pi.single a 1 := by
    rw [← ha, LinearEquiv.inv_apply_apply']
  have hb' : (pairSwap Q a b a' b')⁻¹ (Pi.single b' 1) = Pi.single b 1 := by
    rw [← hb, LinearEquiv.inv_apply_apply']
  refine mem_stabSub.2 ⟨?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha', hxa, ha]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hb', hxb, hb]

theorem map_conj_pairSwap_le (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') (hg : pairSwap Q a b a' b' ∈ orthDerived Q) :
    (pairTorusOf Q a b).map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom ≤ pairTorusOf Q a' b' ∧
      (pairPerpOf Q a b).map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom ≤
        pairPerpOf Q a' b' := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := mem_subgroupOf.1 hx
    refine ⟨⟨_, hg⟩ * x * ⟨_, hg⟩⁻¹, mem_subgroupOf.2 ⟨c, ?_⟩, ?_⟩
    · change torusLin a' b' c = pairSwap Q a b a' b' * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) *
        (pairSwap Q a b a' b')⁻¹
      rw [← hc, pairSwap_conj_torusLin h h' hd]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨_, hg⟩ * x * ⟨_, hg⟩⁻¹, mem_subgroupOf.2 ?_, ?_⟩
    · exact pairSwap_conj_mem_stabSub h h' hd (mem_subgroupOf.1 hx)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem pairSwap_mul_self (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') : pairSwap Q a b a' b' * pairSwap Q a b a' b' = 1 := by
  obtain ⟨-, hw⟩ := pairSwap_hyp h h' hd
  rw [pairSwap, eichler_mul hw hw]
  have h2w : (Pi.single b (1 : K) + Pi.single b' 1 : Fin d → K) +
      (Pi.single b 1 + Pi.single b' 1) = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rw [h2w, eichler_zero_right]

theorem map_conj_pairSwap_eq (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') (hg : pairSwap Q a b a' b' ∈ orthDerived Q) :
    (pairTorusOf Q a b).map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom = pairTorusOf Q a' b' ∧
      (pairPerpOf Q a b).map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom =
        pairPerpOf Q a' b' := by
  have hg' : pairSwap Q a' b' a b ∈ orthDerived Q := pairSwap_comm (Q := Q) ▸ hg
  have hx : projHom Q ⟨_, hg'⟩ = projHom Q ⟨_, hg⟩ := by
    congr 1
    exact Subtype.ext pairSwap_comm.symm
  obtain ⟨h1, h2⟩ := map_conj_pairSwap_le h h' hd hg
  obtain ⟨h3, h4⟩ := map_conj_pairSwap_le h' h hd.symm hg'
  rw [hx] at h3 h4
  have hxx : projHom Q ⟨_, hg⟩ * projHom Q ⟨_, hg⟩ = 1 := by
    rw [← map_mul, ← map_one (projHom Q)]
    congr 1
    exact Subtype.ext (pairSwap_mul_self h h' hd)
  have hmm : ∀ A : Subgroup (matrixProjectiveDerived Q),
      (A.map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom).map
        (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom = A := fun A =>
    SymplecticPilot.map_conj_map_conj_of_sq_eq_one (by rw [pow_two]; exact hxx) A
  refine ⟨le_antisymm h1 ?_, le_antisymm h2 ?_⟩
  · calc pairTorusOf Q a' b' = ((pairTorusOf Q a' b').map
          (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom).map
            (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom := (hmm _).symm
      _ ≤ (pairTorusOf Q a b).map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom := map_mono h3
  · calc pairPerpOf Q a' b' = ((pairPerpOf Q a' b').map
          (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom).map
            (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom := (hmm _).symm
      _ ≤ (pairPerpOf Q a b).map (MulAut.conj (projHom Q ⟨_, hg⟩)).toMonoidHom := map_mono h4

end Swap

section SplitTori

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] in
theorem exists_conj_pairTorus {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {k l : Fin n} (hkl : k ≠ l) :
    ∃ w ∈ L, (modelToG e (pairTorus (K := K) k)).map (MulAut.conj w).toMonoidHom =
        modelToG e (pairTorus l) ∧
      (modelToG e (pairPerp (K := K) k)).map (MulAut.conj w).toMonoidHom =
        modelToG e (pairPerp l) := by
  have hreg := regular_coordinateQuadPlus n K hn
  have hg := pairSwap_mem_orthDerived (a := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv n (.inl k))
    (b := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv n (.inr k))
    (a' := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv n (.inl l))
    (b' := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv n (.inr l))
    hreg.1 hreg.2
  obtain ⟨hX, hD⟩ := map_conj_pairSwap_eq (isHypCoord_coordinateQuadPlus k)
    (isHypCoord_coordinateQuadPlus l) (pairDisjoint_plus hkl) hg
  refine ⟨((e.symm (projHom _ ⟨_, hg⟩) : L) : G), (e.symm _).2, ?_, ?_⟩
  · rw [← UnitaryPilot.modelToG_map_conj]
    exact congrArg (modelToG e) hX
  · rw [← UnitaryPilot.modelToG_map_conj]
    exact congrArg (modelToG e) hD

omit [Finite G] in
theorem exists_conj_minusPairTorus {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {k l : Fin (n - 1)} (hkl : k ≠ l) :
    ∃ w ∈ L, (modelToG e (minusPairTorus (K := K) (by omega) b c k)).map
          (MulAut.conj w).toMonoidHom = modelToG e (minusPairTorus (by omega) b c l) ∧
      (modelToG e (minusPairPerp (K := K) (by omega) b c k)).map (MulAut.conj w).toMonoidHom =
        modelToG e (minusPairPerp (by omega) b c l) := by
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  have hn1 : 1 ≤ n := by omega
  have hg := pairSwap_mem_orthDerived
    (a := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.minusIndexEquiv n hn1 (.inl k))
    (b := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.minusIndexEquiv n hn1
      (.inr (.inl k)))
    (a' := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.minusIndexEquiv n hn1 (.inl l))
    (b' := CFSG.ComponentClassification.CatalogueBOrthogonalPointData.minusIndexEquiv n hn1
      (.inr (.inl l)))
    hreg.1 hreg.2
  obtain ⟨hX, hD⟩ := map_conj_pairSwap_eq (isHypCoord_coordinateQuadMinus hn1 b c k)
    (isHypCoord_coordinateQuadMinus hn1 b c l) (pairDisjoint_minus hn1 hkl) hg
  refine ⟨((e.symm (projHom _ ⟨_, hg⟩) : L) : G), (e.symm _).2, ?_, ?_⟩
  · rw [← UnitaryPilot.modelToG_map_conj]
    exact congrArg (modelToG e) hX
  · rw [← UnitaryPilot.modelToG_map_conj]
    exact congrArg (modelToG e) hD

theorem omegaRowAt_pairTorus_iff {n : ℕ} (hn : 3 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (k l : Fin n) (r : OmegaRow) :
    OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k)) r ↔
      OmegaRowAt t (modelToG e (pairTorus (K := K) l)) (modelToG e (pairPerp (K := K) l)) r := by
  have key : ∀ k l : Fin n, k ≠ l →
      OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k)) r →
      OmegaRowAt t (modelToG e (pairTorus (K := K) l)) (modelToG e (pairPerp (K := K) l)) r := by
    intro k l hkl h
    obtain ⟨w, hw, hX, hD⟩ := exists_conj_pairTorus hn e hkl
    have h1 := h.map_conj_of_commute (mem_centralizer_iff.mp htC w hw)
    rwa [hX, hD] at h1
  by_cases hkl : k = l
  · subst hkl
    exact Iff.rfl
  · exact ⟨key k l hkl, key l k (Ne.symm hkl)⟩

theorem omegaRowAt_minusPairTorus_iff {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (k l : Fin (n - 1)) (r : OmegaRow) :
    OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c k))
        (modelToG e (minusPairPerp (K := K) (by omega) b c k)) r ↔
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c l))
        (modelToG e (minusPairPerp (K := K) (by omega) b c l)) r := by
  have key : ∀ k l : Fin (n - 1), k ≠ l →
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c k))
        (modelToG e (minusPairPerp (K := K) (by omega) b c k)) r →
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c l))
        (modelToG e (minusPairPerp (K := K) (by omega) b c l)) r := by
    intro k l hkl h
    obtain ⟨w, hw, hX, hD⟩ := exists_conj_minusPairTorus hn hirr e hkl
    have h1 := h.map_conj_of_commute (mem_centralizer_iff.mp htC w hw)
    rwa [hX, hD] at h1
  by_cases hkl : k = l
  · subst hkl
    exact Iff.rfl
  · exact ⟨key k l hkl, key l k (Ne.symm hkl)⟩

theorem existsUnique_row_pairTorus (hset : SeitzSetting G L) {n f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k₀ : Fin n) {m f' : ℕ}
    (h0 : ∃ htX : t ∈ centralizer (modelToG e (pairTorus (K := K) k₀) : Set G),
      NeighbourOvergroupOmega
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k₀) : Set G)))
          ⟨t, htX⟩)
        (((modelToG e (pairPerp (K := K) k₀)).subgroupOf
          (centralizer (modelToG e (pairTorus (K := K) k₀) : Set G))).map
          (QuotientGroup.mk'
            (oddCore (centralizer (modelToG e (pairTorus (K := K) k₀) : Set G))))) m f') :
    ∃! r : OmegaRow, ∀ k : Fin n,
      OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k)) r := by
  obtain ⟨htX0, hN⟩ := h0
  obtain ⟨r, hr⟩ := exists_omegaRowAt_of_neighbourOvergroupOmega htX0 hN
  refine ⟨r, fun k => (omegaRowAt_pairTorus_iff (by omega) e htC k₀ k r).1 hr, fun r' hr' => ?_⟩
  exact OmegaRowAt.unique ht (fun htX =>
    (neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k₀ e htC ht rfl htX rfl).1)
    (hr' k₀) hr

theorem existsUnique_row_minusPairTorus (hset : SeitzSetting G L) {n f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k₀ : Fin (n - 1)) {m f' : ℕ}
    (h0 : ∃ htX : t ∈ centralizer
        (modelToG e (minusPairTorus (K := K) (by omega) b c k₀) : Set G),
      NeighbourOvergroupOmega
        (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (minusPairTorus (K := K) (by omega) b c k₀) : Set G))) ⟨t, htX⟩)
        (((modelToG e (minusPairPerp (K := K) (by omega) b c k₀)).subgroupOf
          (centralizer (modelToG e (minusPairTorus (K := K) (by omega) b c k₀) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (minusPairTorus (K := K) (by omega) b c k₀) : Set G))))) m f') :
    ∃! r : OmegaRow, ∀ k : Fin (n - 1),
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c k))
        (modelToG e (minusPairPerp (K := K) (by omega) b c k)) r := by
  obtain ⟨htX0, hN⟩ := h0
  obtain ⟨r, hr⟩ := exists_omegaRowAt_of_neighbourOvergroupOmega htX0 hN
  refine ⟨r, fun k => (omegaRowAt_minusPairTorus_iff (by omega) hirr e htC k₀ k r).1 hr,
    fun r' hr' => ?_⟩
  exact OmegaRowAt.unique ht (fun htX =>
    (neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr k₀ e htC ht rfl htX
      rfl).1) (hr' k₀) hr

end SplitTori

end CFSG.SeitzReduction.OmegaPilot
