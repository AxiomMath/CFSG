module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentFix
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentBound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU62O10CentAut

public section

namespace CFSG.AGLEmbedding.O10Cent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module CFSG.AGLEmbedding.OmegaMinusCent
  CFSG.AGLEmbedding.OmegaMinusPerf CFSG.GroupTheory.WeirSylow CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Plus

@[expose] def singPlane {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (P P' : AnisoPair Q) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {P.a + P'.a, P.b + P'.b}

theorem map_eq_zero_of_mem_singPlane {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {P P' : AnisoPair Q} (h : P.Orth P') {y : V}
    (hy : y ∈ singPlane P P') : Q y = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hy
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, h.map_a_add,
    h.map_b_add, polar_smul_left_eq, polar_smul_right_eq, h.polar_add]
  simp

theorem finrank_singPlane {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {P P' : AnisoPair Q} (h : P.Orth P') :
    finrank (ZMod 2) (singPlane P P') = 2 := by
  rw [singPlane, ← Matrix.range_cons_cons_empty (P.a + P'.a) (P.b + P'.b) ![],
    finrank_span_eq_card h.linearIndependent_sing, Fintype.card_fin]

theorem isPlusType_fix_of_three {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {x : V ≃ₗ[ZMod 2] V}
    (hQ : (polarBilin Q).Nondegenerate) (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hx3 : ∀ v, x (x (x v)) = v)
    (hws : ∀ T : Submodule (ZMod 2) V, (∀ y ∈ T, Q y = 0) → finrank (ZMod 2) T ≤ 4)
    {PsM : List (AnisoPair Q)} (hlen : PsM.length = 3) (hpw : PsM.Pairwise AnisoPair.Orth)
    (hmem : ∀ P ∈ PsM, P.a ∈ moveSpace x ∧ P.b = x P.a)
    (hCdim : finrank (ZMod 2) (fixSpace x) = 4) : IsPlusType (Q.restrict (fixSpace x)) := by
  have hC := polarNondegOn_fix hQ hx hx3
  obtain ⟨Ps, hPpw, hPmem, hcases⟩ := exists_aniso_pairs_nondeg 2 (fixSpace x) hCdim hC
  rcases hcases with hl | ⟨hl, e, heC, he0, heQ, heP⟩
  · obtain ⟨P₁, P₂, rfl⟩ := List.length_eq_two.1 hl
    have h12 : P₁.Orth P₂ := (List.pairwise_pair.1 hPpw)
    have hle : singPlane P₁ P₂ ≤ fixSpace x := by
      rw [singPlane, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact (fixSpace x).add_mem (hPmem P₁ (by simp)).1 (hPmem P₂ (by simp)).1
      · exact (fixSpace x).add_mem (hPmem P₁ (by simp)).2 (hPmem P₂ (by simp)).2
    refine ⟨(singPlane P₁ P₂).comap (fixSpace x).subtype, ?_, fun y hy => ?_⟩
    · rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, finrank_singPlane h12, hCdim]
    · exact map_eq_zero_of_mem_singPlane h12 hy
  · exfalso
    have hpwV : (PsM ++ Ps).Pairwise AnisoPair.Orth := by
      rw [List.pairwise_append]
      refine ⟨hpw, hPpw, fun P hP P' hP' => ?_⟩
      exact orth_of_split hx hx3 (hmem P hP) ⟨(hPmem P' hP').1, (hPmem P' hP').2⟩
    obtain ⟨T, hT, hle⟩ := exists_totSing_of_pairs (PsM ++ Ps) (Submodule.span (ZMod 2) {e})
      (fun y hy => by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        rw [QuadraticMap.map_smul, heQ, smul_zero]) hpwV
      (fun y hy P hP => by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        rcases List.mem_append.1 hP with hP | hP
        · have hyC : a • e ∈ fixSpace x := (fixSpace x).smul_mem a heC
          have hPb : P.b ∈ moveSpace x := by
            rw [(hmem P hP).2]
            exact apply_mem_moveSpace hx3 (hmem P hP).1
          exact ⟨by rw [polar_comm]; exact polar_fix_move hx hyC (hmem P hP).1,
            by rw [polar_comm]; exact polar_fix_move hx hyC hPb⟩
        · exact ⟨by rw [polar_smul_right_eq, (heP P hP).1, mul_zero],
            by rw [polar_smul_right_eq, (heP P hP).2, mul_zero]⟩)
    have h1 := hws T hT
    rw [finrank_span_singleton he0, List.length_append, hlen] at hle
    have hPs : Ps.length = 1 := by omega
    rw [hPs] at hle
    omega

end Plus

section Orders

theorem card_orthogonalGroup_plus_four {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {q : QuadraticForm (ZMod 2) W}
    (hq : (polarBilin q).Nondegenerate) (hdim : finrank (ZMod 2) W = 4) (h : IsPlusType q) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup q) = 72 := by
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (n := 2) hq hdim h
  rw [natCard_orthogonalGroup_congr e]
  have h1 := natCard_orthogonalGroup_quadPlus (K := ZMod 2) 1
  simp only [Nat.card_zmod] at h1
  have h2 : (∏ i ∈ Finset.Icc 1 1, ((((2 : ℕ) : ℤ) ^ 2) ^ i - 1)) = 3 := by decide
  have h3 : ((Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus (1 + 1) (ZMod 2))) : ℕ) : ℤ) = 72 := by
    rw [h1, h2]
    norm_num
  exact_mod_cast h3

end Orders

section Embedding

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem card_centralizer_dvd_isoCent {L : Type*} [Group L] (e : L ≃* elementaryGroup Q) (x : L) :
    Nat.card (Subgroup.centralizer ({x} : Set L)) ∣
      Nat.card (isoCent Q ((e x : elementaryGroup Q) : V ≃ₗ[ZMod 2] V)) := by
  let f : Subgroup.centralizer ({x} : Set L) →* (V ≃ₗ[ZMod 2] V) :=
    ((elementaryGroup Q).subtype.comp e.toMonoidHom).comp
      (Subgroup.centralizer ({x} : Set L)).subtype
  have hf : ∀ g, f g ∈ isoCent Q ((e x : elementaryGroup Q) : V ≃ₗ[ZMod 2] V) := fun g => by
    rw [mem_isoCent]
    refine ⟨elementaryGroup_le_orthogonalGroup Q (e g).2, fun v => ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 g.2
    have h2 := congrArg (fun y : L => ((e y : elementaryGroup Q) : V ≃ₗ[ZMod 2] V) v) h1
    change ((e (g : L) : elementaryGroup Q) : V ≃ₗ[ZMod 2] V)
      (((e x : elementaryGroup Q) : V ≃ₗ[ZMod 2] V) v) =
      ((e x : elementaryGroup Q) : V ≃ₗ[ZMod 2] V)
        (((e (g : L) : elementaryGroup Q) : V ≃ₗ[ZMod 2] V) v)
    simpa using h2
  refine Subgroup.card_dvd_of_injective (f.codRestrict _ hf) fun g g' hgg' => ?_
  apply Subtype.ext
  apply e.injective
  apply Subtype.ext
  exact congrArg (fun u : isoCent Q ((e x : elementaryGroup Q) : V ≃ₗ[ZMod 2] V) =>
    (u : V ≃ₗ[ZMod 2] V)) hgg'

end Embedding

section Main

theorem o10_perfect_or_card {L : Type} [Group L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaMinusTwoIndex 5 d) (he : Nonempty (L ≃* CatGroup d)) {x : L}
    (hx : orderOf x = 3) :
    (∃ D : Subgroup L, D ≤ Subgroup.centralizer ({x} : Set L) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D) ∨
      Nat.card (Subgroup.centralizer ({x} : Set L)) ∣ 72 * 648 := by
  obtain ⟨e⟩ := omegaMinusModel hd he
  have hx' : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx3 : (((e x : elementaryGroup (minusForm 5))) :
      MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5) ^ 3 = 1 := by
    have h : (e x) ^ 3 = 1 := by rw [← map_pow, hx', map_one]
    simpa using congrArg Subtype.val h
  set xe : MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5 :=
    ((e x : elementaryGroup (minusForm 5)) : MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5) with hxe
  have hxO : xe ∈ TauCeti.QuadraticMap.orthogonalGroup (minusForm 5) :=
    elementaryGroup_le_orthogonalGroup _ (e x).2
  have hx3' : ∀ v, xe (xe (xe v)) = v := fun v => by
    have h := congrArg (fun g : MinusSpace 5 ≃ₗ[ZMod 2] MinusSpace 5 => g v) hx3
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hdim : finrank (ZMod 2) (MinusSpace 5) = 2 * 5 := finrank_minusSpace (by norm_num)
  obtain ⟨PsM, hlen, hpw, hmem, hCdim⟩ :=
    exists_move_pairs (nondegenerate_minusForm 5) hxO hx3' hdim
  by_cases hk3 : PsM.length = 3
  · right
    have hws : ∀ T : Submodule (ZMod 2) (MinusSpace 5), (∀ y ∈ T, minusForm 5 y = 0) →
        finrank (ZMod 2) T ≤ 4 := fun T hT => finrank_le_minusForm hT
    have hC4 : finrank (ZMod 2) (fixSpace xe) = 4 := by rw [hCdim, hk3]
    have hplus := isPlusType_fix_of_three (nondegenerate_minusForm 5) hxO hx3' hws hk3 hpw hmem hC4
    have hCnd : (polarBilin ((minusForm 5).restrict (fixSpace xe))).Nondegenerate :=
      nondegenerate_polarBilin_restrict (polarNondegOn_fix (nondegenerate_minusForm 5) hxO hx3')
    have h72 := card_orthogonalGroup_plus_four hCnd hC4 hplus
    obtain ⟨F, hFa⟩ : ∃ F : Frame (minusForm 5) xe 3, ∀ i, (F.P i).a ∈ moveSpace xe := by
      have key : ∀ k, k = 3 → (∃ F : Frame (minusForm 5) xe k,
          ∀ i, (F.P i).a ∈ moveSpace xe) →
          ∃ F : Frame (minusForm 5) xe 3, ∀ i, (F.P i).a ∈ moveSpace xe := by
        rintro k rfl h
        exact h
      exact key _ hk3 ⟨Frame.ofList PsM hpw hmem, fun i => (hmem _ (List.get_mem _ _)).1⟩
    have hspan : Spans F := Spans.of_dim hx3' F hFa (by rw [hC4, hdim])
    exact (card_centralizer_dvd_isoCent e x).trans (card_isoCent_dvd hxO hx3' hspan h72)
  · left
    obtain ⟨D, hDO, hDc, hDp, hD3⟩ := exists_perfect_cent_ne_three (nondegenerate_minusForm 5)
      hxO hx3' hlen hpw hmem hCdim hk3
    obtain ⟨P, P', hPP'⟩ := exists_orth_hypPair (m := 5) (by norm_num)
    have hDE := le_elementaryGroup_of_perfect (nondegenerate_minusForm 5)
      (by rw [hdim]; norm_num) hPP' hDO hDp
    obtain ⟨D', hmem', hcard, hperf⟩ := exists_pullback_subgroup e hDE
    refine ⟨D', fun g hg => ?_, hperf hDp, by rw [hcard]; exact hD3⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have := Subgroup.mem_centralizer_iff.1 (hDc ((hmem' g).1 hg)) xe rfl
    exact e.injective (Subtype.ext (by simpa using this))

theorem o10ThreeCentAut {L : Type} [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaMinusTwoIndex 5 d) (he : Nonempty (L ≃* CatGroup d)) {x : L}
    (hx : orderOf x = 3) : U62O10Cent.CentAlt x := by
  rcases o10_perfect_or_card hd he hx with hD | hcard
  · exact Or.inl hD
  · obtain ⟨hnt, hs⟩ := isSimpleGroup_of_index hd he
    obtain ⟨e⟩ := omegaMinusModel hd he
    have hq := nondegenerate_minusForm 5
    have hdim : finrank (ZMod 2) (MinusSpace 5) = 2 * 5 := finrank_minusSpace (by norm_num)
    have hperfE : Group.IsPerfect (elementaryGroup (minusForm 5)) := by
      rcases exists_totSing_or_three_planes hq (c := 5) (by norm_num) hdim with hT | ⟨h, -⟩
      · exact (exists_order_three_of_totSing hq (by norm_num) hdim hT).1
      · omega
    have hperfL : Group.IsPerfect L :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hc : Subgroup.center L = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
      · exact h
      · exfalso
        have hcomm : ∀ a b : L, a * b = b * a := fun a b =>
          Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a
        exact Group.IsPerfect.not_isMulCommutative L ⟨⟨hcomm⟩⟩
    exact U62O10Cent.centAlt_of_dvd hc x hcard
      (card_outer_dvd_two (by norm_num) (stated_model_of_index hd he)) (by norm_num)

end Main

end CFSG.AGLEmbedding.O10Cent
