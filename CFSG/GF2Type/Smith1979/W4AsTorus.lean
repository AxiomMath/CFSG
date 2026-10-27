module

public import CFSG.GF2Type.Smith1979.W4O83Defs
public import CFSG.GF2Type.Widths1112.Co2Module.Idempotents
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Module QuadraticMap CFSG.Open CFSG.GF2Type.Widths1112.Co2Module
open CFSG.RankThree.Literature.FSmith (zmod2_cases)
open CFSG.RankThree.OrthogonalInvolutions (neg_vec_eq polar_self_eq_zero)

section Blocks

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem apply_piE (v : F3Vec) (x : V) : ρ (ι v) (piE ρ ι x) = piE ρ ι x := by
  have h := LinearMap.congr_fun (θ_mul_sumE (rhoChar ρ ι) v) x
  rw [Module.End.mul_apply, rhoChar_apply] at h
  exact h

theorem exists_blocks [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 8)
    (hfaith : ∀ v : F3Vec, (∀ x, ρ (ι v) x = x) → v = 0) :
    ∃ w u : Fin 4 → F3Vec, (∀ i, w i ⬝ᵥ u i = 1) ∧ (∀ i j, i ≠ j → w i ⬝ᵥ u j = 0) ∧
      (∀ i, finrank (ZMod 2) (LinearMap.range (eK ρ ι (w i))) = 2) ∧
      ∀ x, ∑ i, eK ρ ι (w i) x = x := by
  classical
  have hR : IsLineReps lineReps := isLineReps_lineReps
  obtain ⟨T, hTmem⟩ : ∃ T : Finset F3Vec, ∀ w, w ∈ T ↔
      w ∈ lineReps ∧ finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) ≠ 0 :=
    ⟨lineReps.filter fun w => finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) ≠ 0,
      fun w => Finset.mem_filter⟩
  have hTR : T ⊆ lineReps := fun w hw => ((hTmem w).mp hw).1
  have hzero : ∀ w ∈ lineReps, w ∉ T → ∀ x, eK ρ ι w x = 0 := by
    intro w hw hwT x
    have h0 : finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) = 0 := by
      by_contra hne
      exact hwT ((hTmem w).mpr ⟨hw, hne⟩)
    have := Submodule.finrank_eq_zero.mp h0
    have hx : eK ρ ι w x ∈ LinearMap.range (eK ρ ι w) := ⟨x, rfl⟩
    rw [this] at hx
    exact (Submodule.mem_bot (ZMod 2)).mp hx
  have hsum8 := finrank_eq_finrank_range_piE_add_sum ρ ι hR
  rw [hV] at hsum8
  have hsumT : ∑ w ∈ lineReps, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
      ∑ w ∈ T, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
    refine (Finset.sum_subset hTR fun w hw hwT => ?_).symm
    by_contra hne
    exact hwT ((hTmem w).mpr ⟨hw, hne⟩)
  have hD2 : ∀ w ∈ T, 2 ≤ finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
    intro w hw
    obtain ⟨hwR, hne⟩ := (hTmem w).mp hw
    obtain ⟨v₀, hv₀⟩ := exists_dot_ne_zero (hR.ne_zero w hwR)
    obtain ⟨k, hk⟩ := even_finrank_range_eK ρ ι hv₀
    omega
  have hTle : T.card ≤ 4 := by
    have h1 : 2 * T.card ≤ ∑ w ∈ T, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
      calc 2 * T.card = ∑ _w ∈ T, 2 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum hD2
    omega
  have hdual : ∀ v : F3Vec, (∀ w ∈ T, w ⬝ᵥ v = 0) → v = 0 := by
    intro v hv
    refine hfaith v fun x => ?_
    have hx : ∑ w ∈ lineReps, eK ρ ι w x + piE ρ ι x = x := by
      have := LinearMap.congr_fun (sum_eK_add_piE ρ ι hR) x
      simpa [LinearMap.sum_apply] using this
    calc ρ (ι v) x = ρ (ι v) (∑ w ∈ lineReps, eK ρ ι w x + piE ρ ι x) := by rw [hx]
      _ = ∑ w ∈ lineReps, ρ (ι v) (eK ρ ι w x) + piE ρ ι x := by
          rw [map_add, map_sum, apply_piE]
      _ = ∑ w ∈ lineReps, eK ρ ι w x + piE ρ ι x := by
          have hsum : ∑ w ∈ lineReps, ρ (ι v) (eK ρ ι w x) = ∑ w ∈ lineReps, eK ρ ι w x := by
            refine Finset.sum_congr rfl fun w hw => ?_
            by_cases hwT : w ∈ T
            · exact fixed_of_mem_range_eK ρ ι ⟨x, rfl⟩ (hv w hwT)
            · rw [hzero w hw hwT x, map_zero]
          rw [hsum]
      _ = x := hx
  have hcard4 : 4 ≤ T.card := by
    have hinj : Function.Injective (fun v : F3Vec => fun w : T => (w : F3Vec) ⬝ᵥ v) := by
      intro v v' h
      refine sub_eq_zero.mp (hdual _ fun w hw => ?_)
      have := congr_fun h ⟨w, hw⟩
      rw [dotProduct_sub]
      exact sub_eq_zero.mpr this
    have h := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe, Fintype.card_fin] at h
    by_contra hlt
    have h3 : 3 ^ T.card ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 3 ^ 4 ≤ 3 ^ 3 := h.trans h3
    norm_num at h4
  have hT4 : T.card = 4 := le_antisymm hTle hcard4
  have hD8 : ∑ w ∈ T, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) = 8 ∧
      finrank (ZMod 2) (LinearMap.range (piE ρ ι)) = 0 := by
    have h1 : 2 * T.card ≤ ∑ w ∈ T, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
      calc 2 * T.card = ∑ _w ∈ T, 2 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum hD2
    omega
  have hD2eq : ∀ w ∈ T, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) = 2 := by
    have h8 : ∑ _w ∈ T, 2 = ∑ w ∈ T, finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) := by
      rw [hD8.1]
      simp [hT4]
    exact fun w hw => ((Finset.sum_eq_sum_iff_of_le hD2).mp h8 w hw).symm
  have hpiE0 : ∀ x, piE ρ ι x = 0 := by
    intro x
    have := Submodule.finrank_eq_zero.mp hD8.2
    have hx : piE ρ ι x ∈ LinearMap.range (piE ρ ι) := ⟨x, rfl⟩
    rw [this] at hx
    exact (Submodule.mem_bot (ZMod 2)).mp hx
  let eT : Fin 4 ≃ ↥T := (Finset.equivFinOfCardEq hT4).symm
  have hΦinj : Function.Injective
      (fun v : F3Vec => fun i : Fin 4 => ((eT i : ↥T) : F3Vec) ⬝ᵥ v) := by
    intro v v' h
    refine sub_eq_zero.mp (hdual _ fun w hw => ?_)
    obtain ⟨i, hi⟩ := eT.surjective ⟨w, hw⟩
    have hiw : ((eT i : ↥T) : F3Vec) = w := congrArg Subtype.val hi
    have := congr_fun h i
    simp only at this
    rw [hiw] at this
    rw [dotProduct_sub]
    exact sub_eq_zero.mpr this
  obtain ⟨u, hu⟩ : ∃ u : Fin 4 → F3Vec, ∀ j, (fun i : Fin 4 => ((eT i : ↥T) : F3Vec) ⬝ᵥ u j) =
      Pi.single j 1 := by
    have hsurj := Finite.injective_iff_surjective.mp hΦinj
    exact ⟨fun j => (hsurj (Pi.single j 1)).choose, fun j => (hsurj (Pi.single j 1)).choose_spec⟩
  refine ⟨fun i => ((eT i : ↥T) : F3Vec), u, fun i => ?_, fun i j hij => ?_,
    fun i => hD2eq _ (eT i).2, fun x => ?_⟩
  · simpa using congr_fun (hu i) i
  · simpa [Pi.single_eq_of_ne hij] using congr_fun (hu j) i
  · have h1 : ∑ i : Fin 4, eK ρ ι ((eT i : ↥T) : F3Vec) x = ∑ w ∈ T, eK ρ ι w x := by
      rw [← Finset.sum_coe_sort T (fun w => eK ρ ι w x)]
      exact Equiv.sum_comp eT (fun w : ↥T => eK ρ ι (w : F3Vec) x)
    rw [h1, Finset.sum_subset hTR fun w hw hwT => hzero w hw hwT x]
    have h2 := LinearMap.congr_fun (sum_eK_add_piE ρ ι hR) x
    simpa [LinearMap.sum_apply, hpiE0] using h2

end Blocks

section Plane

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_span_pair_of_finrank_two [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V}
    (hP : finrank (ZMod 2) P = 2) {a b : V} (ha : a ∈ P) (hb : b ∈ P) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : a ≠ b) : P = Submodule.span (ZMod 2) {a, b} := by
  have hli : LinearIndependent (ZMod 2) ![a, b] := by
    rw [LinearIndependent.pair_iff' ha0]
    intro c hc
    rcases zmod2_cases c with rfl | rfl
    · exact hb0 (by simpa using hc.symm)
    · exact hab (by simpa using hc)
  have hspan : Submodule.span (ZMod 2) {a, b} ≤ P := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  refine (Submodule.eq_of_le_of_finrank_eq hspan ?_).symm
  rw [hP]
  have h2 := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty] at h2
  simpa using h2

variable (q : QuadraticForm (ZMod 2) V) (T : V →ₗ[ZMod 2] V)

theorem polar_eq_zero_of_apply_eq (hTiso : ∀ a b, polar q (T a) (T b) = polar q a b) {y v : V}
    (hy : y + T y + T (T y) = 0) (hv : T v = v) : polar q y v = 0 := by
  have h1 : y = T y + T (T y) := by
    have h : y + (T y + T (T y)) = 0 := by rw [← add_assoc]; exact hy
    exact (eq_neg_of_add_eq_zero_left h).trans (neg_vec_eq (ZMod 2) _)
  have h2 : polar q (T y) v = polar q y v := by
    conv_lhs => rw [← hv]
    exact hTiso y v
  have h3 : polar q (T (T y)) v = polar q y v := by
    conv_lhs => rw [← hv]
    rw [hTiso (T y) v, h2]
  have h4 : polar q y v = polar q y v + polar q y v := by
    conv_lhs => rw [h1]
    rw [polar_add_left, h2, h3]
  rw [CharTwo.add_self_eq_zero] at h4
  exact h4

theorem polar_apply_eq_zero_of_q_eq_zero (hTq : ∀ a, q (T a) = q a) {y : V}
    (hy : y + T y + T (T y) = 0) (hqy : q y = 0) : polar q y (T y) = 0 := by
  have h1 : y + T y = T (T y) := by
    rw [eq_neg_of_add_eq_zero_left hy, neg_vec_eq (ZMod 2)]
  have h2 : q (T y) = 0 := by rw [hTq, hqy]
  have h3 : q (y + T y) = 0 := by rw [h1, hTq, h2]
  simp only [polar]
  rw [h3, hqy, h2, sub_zero, sub_zero]

theorem polar_eq_zero_of_q_eq_zero [FiniteDimensional (ZMod 2) V] {P : Submodule (ZMod 2) V}
    (hP : finrank (ZMod 2) P = 2) (hTP : ∀ y ∈ P, T y ∈ P)
    (hone : ∀ y ∈ P, y + T y + T (T y) = 0) (hfree : ∀ y ∈ P, T y = y → y = 0)
    (hT3 : ∀ y, T (T (T y)) = y) (hTq : ∀ a, q (T a) = q a) {y : V} (hyP : y ∈ P) (hy0 : y ≠ 0)
    (hqy : q y = 0) : ∀ p ∈ P, polar q y p = 0 := by
  have hb : T y ∈ P := hTP y hyP
  have hb0 : T y ≠ 0 := fun h => hy0 (by rw [← hT3 y, h, map_zero, map_zero])
  have hab : y ≠ T y := fun h => hy0 (hfree y hyP h.symm)
  intro p hp
  rw [eq_span_pair_of_finrank_two hP hyP hb hy0 hb0 hab, Submodule.mem_span_pair] at hp
  obtain ⟨a, c, rfl⟩ := hp
  rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_eq_zero q y,
    polar_apply_eq_zero_of_q_eq_zero q T hTq (hone y hyP) hqy]
  simp

end Plane

theorem exists_planes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {Γ : Type*} [Group Γ] (r : Γ →* (V ≃ₗ[ZMod 2] V)) (hr : Function.Injective r)
    {E : Subgroup Γ} (hel : IsElemAbelian 3 E) (hE : Nat.card E = 3 ^ 4)
    (hiso : ∀ γ ∈ E, ∀ v, q (r γ v) = q v) :
    ∃ (P : Fin 4 → Submodule (ZMod 2) V) (θ : Fin 4 → Γ),
      ⨆ i, P i = ⊤ ∧ (∀ i, finrank (ZMod 2) (P i) = 2) ∧
      (∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, polar q u v = 0) ∧
      (∀ i, ∀ v ∈ P i, v ≠ 0 → q v = 1) ∧ (∀ i, θ i ∈ E) ∧ (∀ i, θ i ^ 3 = 1) ∧
      (∀ i j, i ≠ j → ∀ v ∈ P j, r (θ i) v = v) ∧ (∀ i, ∀ v ∈ P i, r (θ i) v ∈ P i) ∧
      (∀ i, ∀ v ∈ P i, r (θ i) v = v → v = 0) := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3)
    (fun a b => hel.1.is_comm.comm a b) (fun a => Subtype.ext (hel.2 a a.2)) hE
  let ι : AddChar F3Vec Γ :=
    AddChar.toMonoidHomEquiv.symm (E.subtype.comp e.symm.toMonoidHom)
  have hιE : ∀ v, ι v ∈ E := fun v => (e.symm (Multiplicative.ofAdd v)).2
  have hι3 : ∀ v : F3Vec, ι v ^ 3 = 1 := by
    intro v
    rw [pow_succ, pow_two, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, three_add_self,
      AddChar.map_zero_eq_one]
  let ρ : Representation (ZMod 2) Γ V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp r
  have hρ : ∀ γ x, ρ γ x = r γ x := fun γ x => rfl
  have hpol : ∀ γ ∈ E, ∀ a b, polar q (ρ γ a) (ρ γ b) = polar q a b := by
    intro γ hγ a b
    simp only [hρ, polar, ← map_add, hiso γ hγ]
  have hfaith : ∀ v : F3Vec, (∀ x, ρ (ι v) x = x) → v = 0 := by
    intro v hv
    have h1 : r (ι v) = 1 := LinearEquiv.ext fun x => hv x
    have h2 : ι v = 1 := hr (h1.trans (map_one r).symm)
    have h3 : e.symm (Multiplicative.ofAdd v) = 1 := Subtype.ext h2
    have h4 : Multiplicative.ofAdd v = 1 := by simpa using congrArg e h3
    exact ofAdd_eq_one.mp h4
  obtain ⟨w, u, hwu, hwu', hdim, hsum⟩ := exists_blocks ρ ι hV hfaith
  have hw0 : ∀ i, w i ⬝ᵥ u i ≠ 0 := fun i => by rw [hwu i]; exact one_ne_zero
  have horth : ∀ i j, i ≠ j → ∀ y ∈ LinearMap.range (eK ρ ι (w i)),
      ∀ v ∈ LinearMap.range (eK ρ ι (w j)), polar q y v = 0 := fun i j hij y hy v hv =>
    polar_eq_zero_of_apply_eq q (ρ (ι (u i))) (hpol _ (hιE _))
      (one_add_apply_eq_zero ρ ι (hw0 i) hy)
      (fixed_of_mem_range_eK ρ ι hv (hwu' j i hij.symm))
  refine ⟨fun i => LinearMap.range (eK ρ ι (w i)), fun i => ι (u i), ?_, hdim, horth, ?_,
    fun i => hιE (u i), fun i => hι3 (u i), fun i j hij y hy =>
      fixed_of_mem_range_eK ρ ι hy (hwu' j i hij.symm), fun i y hy =>
      apply_mem_range_eK ρ ι (w i) (u i) hy, fun i y hy hfix =>
      eq_zero_of_apply_eq_self ρ ι (hw0 i) hy hfix⟩
  · rw [eq_top_iff]
    intro x _
    rw [← hsum x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
  · intro i y hy hy0
    by_contra hq1
    have hq0 : q y = 0 := by
      rcases zmod2_cases (q y) with h | h
      · exact h
      · exact absurd h hq1
    have hloc := polar_eq_zero_of_q_eq_zero q (ρ (ι (u i))) (hdim i)
      (fun y hy => apply_mem_range_eK ρ ι (w i) (u i) hy)
      (fun y hy => one_add_apply_eq_zero ρ ι (hw0 i) hy)
      (fun y hy => eq_zero_of_apply_eq_self ρ ι (hw0 i) hy)
      (fun y => apply_cube ρ ι (u i) y) (fun a => by rw [hρ]; exact hiso _ (hιE _) a) hy hy0 hq0
    apply hy0
    refine hq.1 y fun x => ?_
    conv_lhs => rw [← hsum x]
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [polarBilin_apply_apply]
    by_cases hij : j = i
    · subst hij
      exact hloc _ ⟨x, rfl⟩
    · exact horth i j (Ne.symm hij) y hy _ ⟨x, rfl⟩

section Omega83

open CFSG.LargeExtraspecial CFSG.GF2Type.Smith1979.W4O83

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_omega83Pre (hw : S.width = 4) {E : Subgroup S.O} (hEM : E ≤ S.Mbar)
    (hel : IsElemAbelian 3 E) (hE : Nat.card E = 3 ^ 4) :
    ∃ C : Omega83Pre S, ∀ i, C.theta i ∈ E := by
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hV : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨P, θ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_planes S.q S.q_nondegenerate hV
    S.O.subtype Subtype.val_injective hel hE fun γ _ v => q_apply_O γ v
  refine ⟨{ plane := P
            theta := θ
            iSup_plane := h1
            finrank_plane := h2
            polar_eq_zero := h3
            q_eq_one := h4
            theta_mem_Mbar := fun i => hEM (h5 i)
            theta_pow_three := h6
            apply_theta_of_ne := h7
            apply_theta_mem := h8
            eq_zero_of_apply_theta := h9 }, h5⟩

end Omega83

end CFSG.GF2Type.Smith1979.W4As
