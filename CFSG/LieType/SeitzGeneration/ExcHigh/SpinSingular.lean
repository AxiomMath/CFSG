module

public import CFSG.LieType.Universal.Spin.RootElements
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.LieType.Universal QuadraticMap Module

theorem exists_subgroup_mem_iff_pow_eq_one {G : Type*} [Group G] {r : ℕ} (hr : r.Prime)
    (hodd : Odd r) (P Z : Subgroup G) [Finite P] (hZ : Z ≤ Subgroup.center G)
    (hZ2 : ∀ z ∈ Z, z ^ 2 = 1) (hP : ∀ x ∈ P, x ^ r ∈ Z) :
    ∃ U : Subgroup G, ∀ y, y ∈ U ↔ y ∈ P ∧ y ^ r = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  set N : Subgroup P := Z.subgroupOf P
  have hNc : ∀ z ∈ N, ∀ x : P, Commute z x := by
    intro z hz x
    have hz' : (z : G) ∈ Subgroup.center G := hZ (Subgroup.mem_subgroupOf.mp hz)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz' x).symm
  have hNn : N.Normal := ⟨fun z hz g => by rwa [← (hNc z hz g).eq, mul_inv_cancel_right]⟩
  have hcardN : ∃ a, Nat.card N = 2 ^ a := by
    refine IsPGroup.iff_card.mp fun z => ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hZ2 _ (Subgroup.mem_subgroupOf.mp z.2)
  have hindex : ∃ b, N.index = r ^ b := by
    have hq : IsPGroup r (P ⧸ N) := by
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hP x x.2
    exact IsPGroup.iff_card.mp hq
  obtain ⟨a, ha⟩ := hcardN
  obtain ⟨b, hb⟩ := hindex
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := N)
    (by rw [ha, hb]; exact Nat.Coprime.pow a b (Nat.coprime_two_left.mpr hodd))
  have hHr : ∀ x : P, x ∈ H → x ^ r = 1 := by
    intro x hx
    refine Subgroup.disjoint_def.mp hH.disjoint ?_ (pow_mem hx r)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hP x x.2
  have hmem : ∀ x : P, x ∈ H ↔ x ^ r = 1 := by
    refine fun x => ⟨hHr x, fun hx => ?_⟩
    obtain ⟨⟨n, h⟩, hnh⟩ := hH.2 x
    have hn2 : (n : P) ^ 2 = 1 :=
      Subtype.ext (by simpa using hZ2 _ (Subgroup.mem_subgroupOf.mp n.2))
    obtain ⟨k, hk⟩ := hodd
    have hnr : (n : P) ^ r = n := by rw [hk, pow_succ, pow_mul, hn2, one_pow, one_mul]
    have hn1 : (n : P) = 1 := by
      have h1 := congrArg (· ^ r) hnh
      simp only at h1
      rw [(hNc n n.2 h).mul_pow, hHr h h.2, mul_one, hnr, hx] at h1
      exact h1
    simp only at hnh
    rw [← hnh, hn1, one_mul]
    exact h.2
  refine ⟨H.map P.subtype, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, (hmem x).mp hx, Subgroup.coe_one]⟩
  · rintro ⟨hy, hyr⟩
    exact ⟨⟨y, hy⟩, (hmem _).mpr (Subtype.ext (by rw [Subgroup.coe_pow]; exact hyr)), rfl⟩

section Flag

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def flagRadical (T W : Submodule K V) (hTW : T ≤ W) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | (∀ t ∈ T, g t = t) ∧ (∀ w ∈ W, g w - w ∈ T) ∧ ∀ v, g v - v ∈ W}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun t ht => ?_, fun w hw => ?_, fun v => ?_⟩
    · rw [LinearEquiv.mul_apply, hh1 t ht, hg1 t ht]
    · have hhw : h w ∈ W := by
        simpa using W.add_mem (hTW (hh2 w hw)) hw
      have := T.add_mem (hg2 _ hhw) (hh2 w hw)
      rwa [sub_add_sub_cancel] at this
    · have := W.add_mem (hg3 (h v)) (hh3 v)
      rwa [sub_add_sub_cancel] at this
  one_mem' := ⟨fun t _ => rfl, fun w _ => by simp, fun v => by simp⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hW : ∀ x ∈ W, g⁻¹ x ∈ W := by
      intro x hx
      simpa using W.sub_mem hx (hg3 (g⁻¹ x))
    refine ⟨fun t ht => ?_, fun w hw => ?_, fun v => ?_⟩
    · have hy : g⁻¹ t ∈ T := by
        simpa using T.sub_mem ht (hg2 _ (hW t (hTW ht)))
      have := hg1 _ hy
      simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this ⊢
      exact this.symm
    · simpa using T.neg_mem (hg2 _ (hW w hw))
    · simpa using W.neg_mem (hg3 (g⁻¹ v))

theorem pow_apply_of_mem_flagRadical {T W : Submodule K V} {hTW : T ≤ W} {g : V ≃ₗ[K] V}
    (hg : g ∈ flagRadical T W hTW) (k : ℕ) (v : V) :
    (g ^ k) v = v + (k : K) • (g v - v) + (k.choose 2 : K) • (g (g v - v) - (g v - v)) := by
  obtain ⟨a, ha⟩ : ∃ a, a = g v - v := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = g a - a := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hgv : g v = v + a := by rw [ha]; abel
  have hga : g a = a + b := by rw [hb]; abel
  have hgb : g b = b := by
    rw [hb, ha]
    exact hg.1 _ (hg.2.1 _ (hg.2.2 v))
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : (k + 1).choose 2 = k + k.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_add, map_smul, map_smul, hgv, hga, hgb,
      hc]
    push_cast
    module

theorem pow_eq_one_of_mem_flagRadical {r : ℕ} [CharP K r] (hr : r.Prime) (hr2 : r ≠ 2)
    {T W : Submodule K V} {hTW : T ≤ W} {g : V ≃ₗ[K] V} (hg : g ∈ flagRadical T W hTW) :
    g ^ r = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [pow_apply_of_mem_flagRadical hg, CharP.cast_eq_zero K r,
    (CharP.cast_eq_zero_iff K r _).mpr
      (hr.dvd_choose_self two_ne_zero (lt_of_le_of_ne hr.two_le (Ne.symm hr2)))]
  simp

theorem mul_mul_inv_mem_flagRadical {T W : Submodule K V} {hTW : T ≤ W} {g s : V ≃ₗ[K] V}
    (hg : g ∈ flagRadical T W hTW) (hsT : ∀ t ∈ T, s t ∈ T) (hsW : ∀ w ∈ W, s w ∈ W)
    (hsT' : ∀ t ∈ T, s⁻¹ t ∈ T) (hsW' : ∀ w ∈ W, s⁻¹ w ∈ W) :
    s * g * s⁻¹ ∈ flagRadical T W hTW := by
  have hss : ∀ x, s (s⁻¹ x) = x := fun x => by simp
  refine ⟨fun t ht => ?_, fun w hw => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg.1 _ (hsT' t ht), hss]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have := hsT _ (hg.2.1 _ (hsW' w hw))
    rwa [map_sub, hss] at this
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have := hsW _ (hg.2.2 (s⁻¹ v))
    rwa [map_sub, hss] at this

end Flag

section Quadratic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem le_orthogonal_of_forall_eq_zero {X : Submodule K V} (hX : ∀ x ∈ X, Q x = 0) :
    X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) X := by
  intro x hx y hy
  rw [polarBilin_apply_apply, polar, hX _ (X.add_mem hy hx), hX y hy, hX x hx, sub_zero, sub_zero]

theorem two_mul_finrank_le_of_forall_eq_zero [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {X : Submodule K V} (hX : ∀ x ∈ X, Q x = 0) :
    2 * finrank K X ≤ finrank K V := by
  have h1 := Submodule.finrank_mono (le_orthogonal_of_forall_eq_zero Q hX)
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  omega

theorem spinAction_mem_orthogonal {T : Submodule K V} {x : spinGroup Q}
    (hx : ∀ t ∈ T, Spin.spinAction Q x⁻¹ t ∈ T) {w : V}
    (hw : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) T) :
    Spin.spinAction Q x w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) T := by
  intro t ht
  have h : Spin.spinAction Q x (Spin.spinAction Q x⁻¹ t) = t := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]
  rw [polarBilin_apply_apply, ← h, Spin.polar_spinAction, ← polarBilin_apply_apply]
  exact hw _ (hx t ht)

theorem exists_ne_one_pow_ringChar_eq_one_mem_flagRadical [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ finrank K V) {T : Submodule K V}
    (hT0 : T ≠ ⊥) (hTs : ∀ v ∈ T, Q v = 0) :
    ∃ y : spinGroup Q, y ≠ 1 ∧ y ^ ringChar K = 1 ∧
      Spin.spinAction Q y ∈ flagRadical T (LinearMap.BilinForm.orthogonal (polarBilin Q) T)
        (le_orthogonal_of_forall_eq_zero Q hTs) := by
  obtain ⟨u, huT, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  have hu : Q u = 0 := hTs u huT
  have hT := two_mul_finrank_le_of_forall_eq_zero Q hQ hTs
  obtain ⟨w, hwW, hwu⟩ :
      ∃ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) T, w ∉ K ∙ u := by
    by_contra h
    push Not at h
    have h1 := Submodule.finrank_mono (show _ ≤ K ∙ u from h)
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hu0] at h1
    omega
  have hw0 : w ≠ 0 := fun h => hwu (h ▸ Submodule.zero_mem _)
  obtain ⟨a, haX, ha⟩ : ∃ a ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ u ⊔ K ∙ w),
      Q a ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := two_mul_finrank_le_of_forall_eq_zero Q hQ h
    rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (K ∙ u) (K ∙ w)
    rw [finrank_span_singleton hu0, finrank_span_singleton hw0] at h3
    omega
  have huW := le_orthogonal_of_forall_eq_zero Q hTs huT
  have huw : polar Q u w = 0 := by
    rw [← polarBilin_apply_apply]
    exact hwW u huT
  have hua : polar Q u a = 0 := by
    rw [← polarBilin_apply_apply]
    exact haX u (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
  have hwa : polar Q w a = 0 := by
    rw [← polarBilin_apply_apply]
    exact haX w (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hmem := Spin.one_add_smul_ι_mul_ι_mem_spinGroup Q hu huw hua hwa
    (isUnit_iff_ne_zero.mpr ha)
  have hli : LinearIndependent K ![w, u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, zero_add, smul_eq_zero] at hst
      exact ⟨rfl, hst.resolve_right hu0⟩
    · refine absurd ?_ hwu
      have h' : s • w = -(t • u) := eq_neg_of_add_eq_zero_left hst
      have hw : w = (-(s⁻¹ * t)) • u := by
        calc w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
          _ = _ := by rw [h', smul_neg, smul_smul, neg_smul]
      rw [hw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  refine ⟨Spin.rootHom Q hu huw hmem (Multiplicative.ofAdd 1), fun h => ?_, ?_, ?_⟩
  · have := Spin.rootHom_injective Q hu huw hmem hli (h.trans (map_one _).symm)
    exact one_ne_zero (ofAdd_eq_one.mp this)
  · rw [← map_pow, ← ofAdd_nsmul, Nat.smul_one_eq_cast, ringChar.Nat.cast_ringChar, ofAdd_zero,
      map_one]
  · have hact : ∀ v, Spin.spinAction Q (Spin.rootHom Q hu huw hmem (Multiplicative.ofAdd 1)) v =
        v + polar Q v u • w - polar Q v w • u - (Q w * polar Q v u) • u := fun v => by
      rw [Spin.spinAction_rootHom, one_smul]
    refine ⟨fun t ht => ?_, fun w' hw' => ?_, fun v => ?_⟩
    · have h1 : polar Q t u = 0 := by
        rw [← polarBilin_apply_apply]
        exact huW t ht
      have h2 : polar Q t w = 0 := by
        rw [← polarBilin_apply_apply]
        exact hwW t ht
      rw [hact, h1, h2]
      simp
    · have h1 : polar Q w' u = 0 := by
        rw [polar_comm, ← polarBilin_apply_apply]
        exact hw' u huT
      rw [hact, h1]
      simpa using T.neg_mem (T.smul_mem (polar Q w' w) huT)
    · rw [hact]
      have e : v + polar Q v u • w - polar Q v w • u - (Q w * polar Q v u) • u - v =
          polar Q v u • w - (polar Q v w + Q w * polar Q v u) • u := by module
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hwW) (Submodule.smul_mem _ _ huW)

end Quadratic

theorem exists_rGroup_normalized_of_invariant_singular_of_finrank {K : Type*} [Field K] [Finite K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (h2 : ringChar K ≠ 2) (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ finrank K V)
    (E : Subgroup (spinGroup Q)) (T : Submodule K V) (hT0 : T ≠ ⊥) (hTs : ∀ v ∈ T, Q v = 0)
    (hTi : ∀ e ∈ E, ∀ v ∈ T, Spin.spinAction Q e v ∈ T) :
    ∃ U : Subgroup (spinGroup Q), U ≠ ⊥ ∧ IsPGroup (ringChar K) U ∧
      ∀ e ∈ E, U.map (MulAut.conj e).toMonoidHom = U := by
  have hr : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  let _ : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero h2)
  have hQ' : Q.Nondegenerate := Spin.nondegenerate_of_nondegenerate_polarBilin hQ
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have : Finite V := Module.finite_of_finite K
  have : Finite (spinGroup Q) := by
    rw [MonoidHom.finite_iff_finite_ker_range (Spin.spinAction Q)]
    refine ⟨?_, ?_⟩
    · have hsub : ((Spin.spinAction Q).ker : Set (spinGroup Q)) ⊆
          {1, CliffordAlgebra.spinGroup.negOne Q hQ'.ne_zero} :=
        fun x hx => (Spin.mem_ker_spinAction_iff Q hQ' x).mp hx
      exact (((Set.finite_singleton _).insert 1).subset hsub).to_subtype
    · have : Finite (V ≃ₗ[K] V) :=
        Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) fun _ _ h => LinearEquiv.ext
          (congrFun h)
      infer_instance
  obtain ⟨W, hW⟩ : ∃ W, W = LinearMap.BilinForm.orthogonal (polarBilin Q) T := ⟨_, rfl⟩
  have hTW : T ≤ W := hW ▸ le_orthogonal_of_forall_eq_zero Q hTs
  obtain ⟨P, hP⟩ : ∃ P, P = Subgroup.comap (Spin.spinAction Q) (flagRadical T W hTW) := ⟨_, rfl⟩
  have hker2 : ∀ z ∈ (Spin.spinAction Q).ker, z ^ 2 = 1 := by
    intro z hz
    rcases (Spin.mem_ker_spinAction_iff Q hQ' z).mp hz with rfl | rfl
    · exact one_pow 2
    · rw [pow_two, CliffordAlgebra.spinGroup.negOne_mul_self]
  obtain ⟨U, hU⟩ := exists_subgroup_mem_iff_pow_eq_one hr (hr.odd_of_ne_two h2) P
    (Spin.spinAction Q).ker (Spin.ker_spinAction_le_center Q) hker2 (fun x hx => by
      rw [MonoidHom.mem_ker, map_pow]
      rw [hP, Subgroup.mem_comap] at hx
      exact pow_eq_one_of_mem_flagRadical hr h2 hx)
  refine ⟨U, ?_, fun y => ⟨1, Subtype.ext ?_⟩, fun e he => ?_⟩
  · obtain ⟨y, hy1, hyr, hyR⟩ := exists_ne_one_pow_ringChar_eq_one_mem_flagRadical Q hQ hV hT0 hTs
    intro hU0
    have hyP : y ∈ P := by
      subst hW
      rw [hP, Subgroup.mem_comap]
      exact hyR
    have := (hU y).mpr ⟨hyP, hyr⟩
    rw [hU0, Subgroup.mem_bot] at this
    exact hy1 this
  · rw [pow_one, Subgroup.coe_pow, ((hU y).mp y.2).2, Subgroup.coe_one]
  · have hconj : ∀ e ∈ E, ∀ y ∈ U, e * y * e⁻¹ ∈ U := by
      intro e he y hy
      obtain ⟨hyP, hyr⟩ := (hU y).mp hy
      refine (hU _).mpr ⟨?_, by rw [conj_pow, hyr, mul_one, mul_inv_cancel]⟩
      have hs := hTi e he
      have hs' := hTi e⁻¹ (E.inv_mem he)
      rw [hP, Subgroup.mem_comap] at hyP ⊢
      rw [map_mul, map_mul, map_inv]
      refine mul_mul_inv_mem_flagRadical hyP hs (fun w hw => ?_) ?_ (fun w hw => ?_)
      · rw [hW] at hw ⊢
        exact spinAction_mem_orthogonal Q hs' hw
      · rw [← map_inv]
        exact hs'
      · rw [hW] at hw ⊢
        rw [← map_inv]
        exact spinAction_mem_orthogonal Q (by rwa [inv_inv]) hw
    refine le_antisymm ?_ fun y hy => ⟨e⁻¹ * y * e, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hconj e he y hy
    · simpa using hconj e⁻¹ (E.inv_mem he) y hy
    · simp [mul_assoc]

theorem exists_rGroup_normalized_of_invariant_singular
    {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 3 ≤ n)
    (E : Subgroup (spinGroup (Spin.quadPlus n K)))
    (T : Submodule K (Fin n ⊕ Fin n → K)) (hT0 : T ≠ ⊥)
    (hTs : ∀ v ∈ T, Spin.quadPlus n K v = 0)
    (hTi : ∀ e ∈ E, ∀ v ∈ T, Spin.spinAction (Spin.quadPlus n K) e v ∈ T) :
    ∃ U : Subgroup (spinGroup (Spin.quadPlus n K)), U ≠ ⊥ ∧ IsPGroup (ringChar K) U ∧
      ∀ e ∈ E, U.map (MulAut.conj e).toMonoidHom = U := by
  have h2 : ringChar K ≠ 2 := by
    intro h
    have hd : ringChar K ∣ Nat.card K := ringChar.dvd (by
      have := card_nsmul_eq_zero' (G := K) (x := 1)
      rwa [nsmul_eq_mul, mul_one] at this)
    rw [h] at hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  exact exists_rGroup_normalized_of_invariant_singular_of_finrank (Spin.quadPlus n K) h2
    (Spin.nondegenerate_polarBilin_quadPlus n K)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega)
    E T hT0 hTs hTi

end CFSG.LieType.SeitzGeneration.ExcHigh
