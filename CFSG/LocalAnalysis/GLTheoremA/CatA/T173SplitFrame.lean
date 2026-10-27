module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173S

open Module QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.StandardType.TableBOrth
open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.GLTheoremA.Y10F.OmTorus
open scoped IsMulCommutative
open CFSG.GroupTheory.WeirSylow (IsPlusType)

section Defs

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

open scoped Classical in
@[expose] noncomputable def wittRank (Q : QuadraticForm F V) (l : ℕ) : ℕ :=
  if IsPlusType Q then l else l - 1

@[expose] def IsHypDiag (Q : QuadraticForm F V) {m : ℕ} (e f : Fin m → V) (c : Fin m → Fˣ)
    (g : V ≃ₗ[F] V) : Prop :=
  (∀ i, g (e i) = ((c i : Fˣ) : F) • e i) ∧ (∀ i, g (f i) = (((c i)⁻¹ : Fˣ) : F) • f i) ∧
    ∀ v, (∀ i, QuadraticMap.polar Q (e i) v = 0) → (∀ i, QuadraticMap.polar Q (f i) v = 0) → g v = v

@[expose] def InTorsionTorus (Q : QuadraticForm F V) (p : ℕ) {m : ℕ} (e f : Fin m → V)
    (g : V ≃ₗ[F] V) : Prop :=
  ∃ c : Fin m → Fˣ, (∀ i, c i ^ p = 1) ∧ IsHypDiag Q e f c g

end Defs

section Frame

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

private theorem orthDerived_le_orthogonalGroup' {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    simp only [commutatorElement_def]
    exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
      (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

instance instFiniteOrthDerived : Finite ↥(orthDerived Q) :=
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  inferInstance

theorem finrank_le_wittRank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) {T : Submodule F V} (hT : ∀ w ∈ T, Q w = 0) :
    finrank F T ≤ wittRank Q l := by
  have h2 := two_mul_finrank_le_of_singular hQ hT
  unfold wittRank
  split_ifs with hplus
  · omega
  · by_contra hlt
    exact hplus ⟨T, by omega, hT⟩

private theorem exists_isHypFamily_wittRank_aux1 {V' : Type} [AddCommGroup V'] [Module F V']
    {Q' : QuadraticForm F V'} {m : ℕ} {e f : Fin m → V'} (hef : IsHypFamily Q' e f)
    {φ : Q.IsometryEquiv Q'} :
    IsHypFamily Q (fun i => φ.symm (e i)) (fun i => φ.symm (f i)) := by
  have hpol : ∀ x y : V', polar Q (φ.symm x) (φ.symm y) = polar Q' x y := by
    intro x y
    have h1 : φ.symm (x + y) = φ.symm x + φ.symm y := map_add _ _ _
    rw [QuadraticMap.polar, QuadraticMap.polar, ← h1, ← φ.map_app, φ.apply_symm_apply,
      ← φ.map_app, φ.apply_symm_apply, ← φ.map_app, φ.apply_symm_apply]
  refine ⟨fun k => ?_, fun k => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [← φ.map_app, φ.apply_symm_apply]; exact hef.map_e k
  · rw [← φ.map_app, φ.apply_symm_apply]; exact hef.map_f k
  · exact (hpol (e i) (e j)).trans (hef.polar_ee i j)
  · exact (hpol (f i) (f j)).trans (hef.polar_ff i j)
  · exact (hpol (e i) (f j)).trans (hef.polar_ef i j)

theorem exists_isHypFamily_wittRank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) : ∃ e f : Fin (wittRank Q l) → V, IsHypFamily Q e f := by
  by_cases hl : l = 0
  · subst hl
    have hw : wittRank Q 0 = 0 := by rw [wittRank]; split_ifs <;> rfl
    rw [hw]
    exact ⟨fun i => i.elim0, fun i => i.elim0,
      ⟨fun k => k.elim0, fun k => k.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩⟩
  · have hl1 : 1 ≤ l := by omega
    by_cases hIp : IsPlusType Q
    · have hwr : wittRank Q l = l := by rw [wittRank, if_pos hIp]
      rw [hwr]
      obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus (n := l) hQ hdim hIp
      have hfam : IsHypFamily (CFSG.LieType.Universal.Spin.quadPlus l F)
          (fun k => Pi.single (Sum.inl k) 1) (fun k => Pi.single (Sum.inr k) 1) :=
        isHypFamily_single (QF := CFSG.LieType.Universal.Spin.quadPlus l F)
          (fun k => isHypCoord_qPlusForm k) Sum.inr_injective (fun i j => Sum.inl_ne_inr)
      exact ⟨fun k => φ.symm (Pi.single (Sum.inl k) 1),
        fun k => φ.symm (Pi.single (Sum.inr k) 1),
        exists_isHypFamily_wittRank_aux1 (φ := φ) hfam⟩
    · have hwr : wittRank Q l = l - 1 := by rw [wittRank, if_neg hIp]
      rw [hwr]
      rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus (n := l) Q hQ hl1
        hdim with hplus | ⟨β, γ, -, ⟨φ⟩⟩
      · obtain ⟨ψ⟩ := hplus
        exact absurd ((CFSG.GroupTheory.WeirSylow.isPlusType_congr ψ).2
          (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F l)) hIp
      · have hcoord : ∀ k : Fin (l - 1),
            CFSG.SeitzReduction.OmegaPilot.IsHypCoord (CFSG.LieType.Universal.Spin.quadMinus l F β γ)
              (Sum.inl k) (Sum.inr (Sum.inl k)) := fun k =>
          ⟨Sum.inl_ne_inr,
            by rw [CFSG.LieType.Universal.Spin.quadMinus_apply]; simp [Pi.single_apply],
            by rw [CFSG.LieType.Universal.Spin.quadMinus_apply]; simp [Pi.single_apply],
            fun v => by
              rw [QuadraticMap.polar_comm]
              exact CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl l F β γ v k,
            fun v => by
              rw [QuadraticMap.polar_comm]
              exact CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl l F β γ v k⟩
        have hfam : IsHypFamily (CFSG.LieType.Universal.Spin.quadMinus l F β γ)
            (fun k => Pi.single (Sum.inl k) 1) (fun k => Pi.single (Sum.inr (Sum.inl k)) 1) :=
          isHypFamily_single (QF := CFSG.LieType.Universal.Spin.quadMinus l F β γ)
            (fun k => hcoord k) (Sum.inr_injective.comp Sum.inl_injective)
            (fun i j => Sum.inl_ne_inr)
        exact ⟨fun k => φ.symm (Pi.single (Sum.inl k) 1),
          fun k => φ.symm (Pi.single (Sum.inr (Sum.inl k)) 1),
          exists_isHypFamily_wittRank_aux1 (φ := φ) hfam⟩

theorem exists_finrank_three_singular (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) :
    ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨e, f, hef⟩ := exists_isHypFamily_wittRank hQ hdim
  have hm : 3 ≤ wittRank Q l := by
    unfold wittRank
    split_ifs <;> omega
  have hli : LinearIndependent F (fun i : Fin 3 => e (Fin.castLE hm i)) :=
    (hef.linearIndependent.comp Sum.inl Sum.inl_injective).comp _ (Fin.castLE_injective hm)
  refine ⟨Submodule.span F (Set.range fun i : Fin 3 => e (Fin.castLE hm i)),
    by rw [finrank_span_eq_card hli]; simp, ?_⟩
  exact eq_zero_on_span (S := Set.range fun i : Fin 3 => e (Fin.castLE hm i))
    (by rintro _ ⟨i, rfl⟩; exact hef.map_e _)
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hef.polar_ee _ _)

theorem eq_zero_of_isHypFamily_wittRank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) {e f : Fin (wittRank Q l) → V} (hef : IsHypFamily Q e f) {v : V}
    (h1 : ∀ i, QuadraticMap.polar Q (e i) v = 0) (h2 : ∀ i, QuadraticMap.polar Q (f i) v = 0)
    (h3 : Q v = 0) : v = 0 := by
  by_contra hv0
  have hli : LinearIndependent F e :=
    hef.linearIndependent.comp Sum.inl Sum.inl_injective
  have hv_notmem : v ∉ Submodule.span F (Set.range e) := by
    intro hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
    have hck : ∀ k, c k = 0 := by
      intro k
      have hpk : QuadraticMap.polar Q (f k) v = c k := by
        rw [← hc, CFSG.LocalAnalysis.ComponentInitial.polar_sum_smul_right Finset.univ c e (f k)]
        rw [Finset.sum_eq_single k]
        · rw [QuadraticMap.polar_comm, hef.polar_ef, if_pos rfl, mul_one]
        · intro i _ hik
          rw [QuadraticMap.polar_comm, hef.polar_ef, if_neg hik, mul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      have hk := h2 k
      rw [hpk] at hk
      exact hk
    have hv_eq : v = 0 := by
      rw [← hc]
      simp [hck]
    exact hv0 hv_eq
  let u : Option (Fin (wittRank Q l)) → V := fun o => Option.casesOn' o v e
  have hliu : LinearIndependent F u := hli.option hv_notmem
  have hT : ∀ w ∈ Submodule.span F (Set.range u), Q w = 0 := by
    refine eq_zero_on_span (S := Set.range u) ?_ ?_
    · rintro _ ⟨o, rfl⟩
      cases o with
      | none => exact h3
      | some i => exact hef.map_e i
    · rintro _ ⟨o, rfl⟩ _ ⟨o', rfl⟩
      cases o with
      | none =>
        cases o' with
        | none =>
          rw [QuadraticMap.polar_self, nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul]
        | some j => rw [QuadraticMap.polar_comm]; exact h1 j
      | some i =>
        cases o' with
        | none => exact h1 i
        | some j => exact hef.polar_ee i j
  have hfr : finrank F (Submodule.span F (Set.range u)) = wittRank Q l + 1 := by
    rw [finrank_span_eq_card hliu]
    simp
  have hle := finrank_le_wittRank hQ hdim hT
  omega

theorem exists_decomp_of_isHypFamily {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) (v : V) :
    ∃ w : V, (∀ j, QuadraticMap.polar Q (e j) w = 0) ∧ (∀ j, QuadraticMap.polar Q (f j) w = 0) ∧
      v = ∑ i, (QuadraticMap.polar Q v (f i) • e i + QuadraticMap.polar Q v (e i) • f i) + w := by
  set s : V := ∑ i, (QuadraticMap.polar Q v (f i) • e i + QuadraticMap.polar Q v (e i) • f i)
    with hs
  have key : ∀ x : V, QuadraticMap.polar Q x s = ∑ i, (QuadraticMap.polar Q v (f i) *
      QuadraticMap.polar Q x (e i) + QuadraticMap.polar Q v (e i) * QuadraticMap.polar Q x (f i)) := by
    intro x
    rw [hs, ← QuadraticMap.polarBilin_apply_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_add, map_smul, smul_eq_mul, QuadraticMap.polarBilin_apply_apply]
  have hfe : ∀ i j, QuadraticMap.polar Q (f j) (e i) = if i = j then 1 else 0 := fun i j => by
    rw [QuadraticMap.polar_comm]
    exact hef.polar_ef i j
  refine ⟨v - s, fun j => ?_, fun j => ?_, by abel⟩
  · rw [QuadraticMap.polar_sub_right, key]
    simp [hef.polar_ee, hef.polar_ef, QuadraticMap.polar_comm (⇑Q) v (e j)]
  · rw [QuadraticMap.polar_sub_right, key]
    simp [hef.polar_ff, hfe, QuadraticMap.polar_comm (⇑Q) v (f j)]

theorem IsHypDiag.eq_of_isHypDiag {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    {c : Fin m → Fˣ} {g g' : V ≃ₗ[F] V} (hg : IsHypDiag Q e f c g) (hg' : IsHypDiag Q e f c g') :
    g = g' := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, hw1, hw2, hv⟩ := exists_decomp_of_isHypFamily hef v
  have key : ∀ k : V ≃ₗ[F] V, IsHypDiag Q e f c k → k v = ∑ i, (QuadraticMap.polar Q v (f i) •
      ((c i : Fˣ) : F) • e i + QuadraticMap.polar Q v (e i) • (((c i)⁻¹ : Fˣ) : F) • f i) + w := by
    intro k hk
    conv_lhs => rw [hv]
    rw [map_add, map_sum, hk.2.2 w hw1 hw2]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_add, map_smul, map_smul, hk.1 i, hk.2.1 i]
  rw [key g hg, key g' hg']

private theorem exists_isHypDiag_mem_orthDerived_aux1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ}
    (hcp : ∀ i, c i ^ p = 1) (j : Fin m) :
    ∃ h : ↥(orthDerived Q),
      (h : V ≃ₗ[F] V) (e j) = ((c j : Fˣ) : F) • e j ∧
      (h : V ≃ₗ[F] V) (f j) = (((c j)⁻¹ : Fˣ) : F) • f j ∧
      (∀ i, i ≠ j → (h : V ≃ₗ[F] V) (e i) = e i ∧ (h : V ≃ₗ[F] V) (f i) = f i) ∧
      (∀ v, QuadraticMap.polar Q (e j) v = 0 → QuadraticMap.polar Q (f j) v = 0 →
        (h : V ≃ₗ[F] V) v = v) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hc : c j = 1
  · refine ⟨1, ?_, ?_, ?_, ?_⟩
    · simp [hc]
    · simp [hc]
    · intro i _; exact ⟨rfl, rfl⟩
    · intro v _ _; rfl
  · let P : HypPair Q := ⟨e j, f j, hef.map_e j, hef.map_f j, by simpa using hef.polar_ef j j⟩
    have hord : orderOf (c j) = p := orderOf_eq_prime (hcp j) hc
    refine ⟨⟨hypDiag P (c j : F) (Units.ne_zero (c j)),
      hypDiag_mem_orthDerived P (c j) hp hp2 hord⟩, ?_, ?_, ?_, ?_⟩
    · change hypDiag P (c j : F) (Units.ne_zero (c j)) P.e = ((c j : Fˣ) : F) • e j
      simpa using hypDiag_apply_e P (c j : F) (Units.ne_zero (c j))
    · change hypDiag P (c j : F) (Units.ne_zero (c j)) P.f = (((c j)⁻¹ : Fˣ) : F) • f j
      simpa using hypDiag_apply_f P (c j : F) (Units.ne_zero (c j))
    · intro i hi
      have hper_e : e i ∈ P.perp := by
        rw [HypPair.mem_perp]
        exact ⟨hef.polar_ee j i, by
          rw [QuadraticMap.polar_comm, hef.polar_ef i j, if_neg hi]⟩
      have hper_f : f i ∈ P.perp := by
        rw [HypPair.mem_perp]
        exact ⟨by rw [hef.polar_ef j i, if_neg (Ne.symm hi)], hef.polar_ff j i⟩
      exact ⟨by
          change hypDiag P (c j : F) (Units.ne_zero (c j)) (e i) = e i
          exact hypDiag_apply_perp P _ _ hper_e,
        by
          change hypDiag P (c j : F) (Units.ne_zero (c j)) (f i) = f i
          exact hypDiag_apply_perp P _ _ hper_f⟩
    · intro v hv1 hv2
      exact hypDiag_apply_perp P _ _ (HypPair.mem_perp.mpr ⟨hv1, hv2⟩)

theorem exists_isHypDiag_mem_orthDerived {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    {e f : Fin m → V} (hef : IsHypFamily Q e f) {c : Fin m → Fˣ} (hcp : ∀ i, c i ^ p = 1) :
    ∃ g : ↥(orthDerived Q), IsHypDiag Q e f c (g : V ≃ₗ[F] V) := by
  classical
  have key : ∀ s : Finset (Fin m), ∃ g : ↥(orthDerived Q),
      IsHypDiag Q e f (fun i => if i ∈ s then c i else 1) (g : V ≃ₗ[F] V) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, ⟨fun i => by simp, fun i => by simp, fun v _ _ => rfl⟩⟩
    | insert j s hjs ih =>
        obtain ⟨g, hg⟩ := ih
        obtain ⟨h, he', hf', hfix, hperp⟩ :=
          exists_isHypDiag_mem_orthDerived_aux1 hp hp2 hef hcp j
        refine ⟨g * h, ?_⟩
        rw [Subgroup.coe_mul]
        refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
        · by_cases hij : i = j
          · subst i
            have hge : (g : V ≃ₗ[F] V) (e j) = e j := by simpa [hjs] using hg.1 j
            rw [LinearEquiv.mul_apply, he', map_smul, hge]
            simp
          · by_cases his : i ∈ s
            · rw [LinearEquiv.mul_apply, (hfix i hij).1, hg.1 i]
              simp [his]
            · have hmi : i ∉ insert j s := fun h =>
                his (Finset.mem_of_mem_insert_of_ne h hij)
              rw [LinearEquiv.mul_apply, (hfix i hij).1, hg.1 i]
              simp [his, hmi]
        · by_cases hij : i = j
          · subst i
            have hgf : (g : V ≃ₗ[F] V) (f j) = f j := by simpa [hjs] using hg.2.1 j
            rw [LinearEquiv.mul_apply, hf', map_smul, hgf]
            simp
          · by_cases his : i ∈ s
            · rw [LinearEquiv.mul_apply, (hfix i hij).2, hg.2.1 i]
              simp [his]
            · have hmi : i ∉ insert j s := fun h =>
                his (Finset.mem_of_mem_insert_of_ne h hij)
              rw [LinearEquiv.mul_apply, (hfix i hij).2, hg.2.1 i]
              simp [his, hmi]
        · rw [LinearEquiv.mul_apply, hperp v (hv1 j) (hv2 j)]
          exact hg.2.2 v (fun i => hv1 i) (fun i => hv2 i)
  obtain ⟨g, hg⟩ := key Finset.univ
  refine ⟨g, ?_⟩
  have hw : (fun i => if i ∈ (Finset.univ : Finset (Fin m)) then c i else 1) = c := by
    ext i; simp
  rwa [hw] at hg

theorem isHypDiag_conj {m : ℕ} {e f : Fin m → V} {c : Fin m → Fˣ} {g h : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    IsHypDiag Q e f c (g * h * g⁻¹) ↔ IsHypDiag Q (fun i => g⁻¹ (e i)) (fun i => g⁻¹ (f i)) c h := by
  have hpol : ∀ x y : V, QuadraticMap.polar Q (g.symm x) y = QuadraticMap.polar Q x (g y) := by
    intro x y
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (g.symm x) y
    rw [g.apply_symm_apply] at this
    exact this.symm
  have hc : ∀ x : V, (g * h * g⁻¹) x = g (h (g.symm x)) := fun x => rfl
  unfold IsHypDiag
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
    · apply g.injective
      have := h1 i
      rw [hc] at this
      show g (h (g.symm (e i))) = g (((c i : Fˣ) : F) • g.symm (e i))
      rw [this, map_smul, g.apply_symm_apply]
    · apply g.injective
      have := h2 i
      rw [hc] at this
      show g (h (g.symm (f i))) = g ((((c i)⁻¹ : Fˣ) : F) • g.symm (f i))
      rw [this, map_smul, g.apply_symm_apply]
    · have := h3 (g v) (fun i => (hpol (e i) v).symm.trans (hv1 i))
        (fun i => (hpol (f i) v).symm.trans (hv2 i))
      rw [hc, g.symm_apply_apply] at this
      exact g.injective this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
    · rw [hc]
      have := h1 i
      change h (g.symm (e i)) = ((c i : Fˣ) : F) • g.symm (e i) at this
      rw [this, map_smul, g.apply_symm_apply]
    · rw [hc]
      have := h2 i
      change h (g.symm (f i)) = (((c i)⁻¹ : Fˣ) : F) • g.symm (f i) at this
      rw [this, map_smul, g.apply_symm_apply]
    · have := h3 (g.symm v) (fun i => by
          show QuadraticMap.polar Q (g.symm (e i)) (g.symm v) = 0
          rw [hpol, g.apply_symm_apply]
          exact hv1 i) (fun i => by
          show QuadraticMap.polar Q (g.symm (f i)) (g.symm v) = 0
          rw [hpol, g.apply_symm_apply]
          exact hv2 i)
      rw [hc, this, g.apply_symm_apply]

theorem isHypFamily_map {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    IsHypFamily Q (fun i => g (e i)) (fun i => g (f i)) where
  map_e k := (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (e k)).trans (hef.map_e k)
  map_f k := (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg (f k)).trans (hef.map_f k)
  polar_ee i j :=
    (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (e i) (e j)).trans
      (hef.polar_ee i j)
  polar_ff i j :=
    (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (f i) (f j)).trans
      (hef.polar_ff i j)
  polar_ef i j :=
    (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg (e i) (f j)).trans
      (hef.polar_ef i j)

private theorem card_le_pow_wittRank_aux1 (m p : ℕ) (hp : p.Prime) :
    Nat.card {u : Fin m → Fˣ // ∀ k, u k ^ p = 1} ≤ p ^ m := by
  classical
  haveI : Finite Fˣ := Finite.of_injective (fun u : Fˣ => (u : F)) Units.val_injective
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin m => Fˣ)
        (p := fun _ v => v ^ p = 1)), Nat.card_pi]
  calc ∏ k : Fin m, Nat.card {v : Fˣ // v ^ p = 1}
      ≤ ∏ _k : Fin m, p :=
        Finset.prod_le_prod fun k _ => by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          exact IsCyclic.card_pow_eq_one_le (α := Fˣ) hp.pos
    _ = p ^ m := by simp [Finset.prod_const]

theorem card_le_pow_wittRank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ wittRank Q l := by
  classical
  by_cases hle : Nat.card E ≤ p ^ wittRank Q l
  · exact hle
  · exfalso
    have hcard : p ^ wittRank Q l ≤ Nat.card E := le_of_not_ge hle
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsMulCommutative E := hE.1
    haveI : Finite Fˣ := Finite.of_injective (fun u : Fˣ => (u : F)) Units.val_injective
    obtain ⟨e, f, hef⟩ := exists_isHypFamily_wittRank hQ hdim
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
    have hexp : ∀ x : E, x ^ p = 1 := fun x =>
      Subtype.ext (by simpa using hE.2 (x : ↥(orthDerived Q)) x.2)
    let ρ : E →* (V ≃ₗ[F] V) := (orthDerived Q).subtype.comp E.subtype
    have hρO : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x =>
      orthDerived_le_orthogonalGroup' x.1.2
    obtain ⟨g, hg, χ, h1, h2, h3, -⟩ := exists_orth_conj_weights hQ hp2 hζ
      (fun T hT => finrank_le_wittRank hQ hdim hT) hef ρ hρO
      (fun x y h => Subtype.ext (Subtype.ext h)) hexp hcard
    have hef' := isHypFamily_map hef (inv_mem hg)
    have hinj : Function.Injective
        (fun x : E => (⟨fun k => χ k x, fun k => by
          show (χ k x) ^ p = 1
          rw [← map_pow, hexp x, map_one]⟩ :
          {u : Fin (wittRank Q l) → Fˣ // ∀ k, u k ^ p = 1})) := by
      intro x y hxy
      have hxdiag : IsHypDiag Q (fun i => g⁻¹ (e i)) (fun i => g⁻¹ (f i)) (fun k => χ k x)
          ((x : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
        (isHypDiag_conj hg).1 ⟨fun k => h1 x k, fun k => h2 x k,
          fun v hv1 hv2 => h3 x v hv1 hv2⟩
      have hydiag : IsHypDiag Q (fun i => g⁻¹ (e i)) (fun i => g⁻¹ (f i)) (fun k => χ k y)
          ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
        (isHypDiag_conj hg).1 ⟨fun k => h1 y k, fun k => h2 y k,
          fun v hv1 hv2 => h3 y v hv1 hv2⟩
      have hxy' : (fun k => χ k x) = (fun k => χ k y) := congrArg Subtype.val hxy
      have hρ : ((x : ↥(orthDerived Q)) : V ≃ₗ[F] V) = ((y : ↥(orthDerived Q)) : V ≃ₗ[F] V) :=
        IsHypDiag.eq_of_isHypDiag hef' hxdiag (hxy'.symm ▸ hydiag)
      exact Subtype.ext (Subtype.ext hρ)
    exact hle ((Nat.card_le_card_of_injective _ hinj).trans
      (card_le_pow_wittRank_aux1 (wittRank Q l) p hp))

private theorem exists_subgroup_eq_torsionTorus_aux1 {m : ℕ} {e f : Fin m → V}
    {c c' : Fin m → Fˣ} {g : V ≃ₗ[F] V} (hef : IsHypFamily Q e f)
    (h1 : IsHypDiag Q e f c g) (h2 : IsHypDiag Q e f c' g) : c = c' := by
  funext i
  apply Units.ext
  have heq : ((c i : F) - (c' i : F)) • e i = 0 := by
    rw [sub_smul, ← h1.1 i, ← h2.1 i, sub_self]
  have he0 : e i ≠ 0 := hef.linearIndependent.ne_zero (Sum.inl i)
  exact sub_eq_zero.mp (by
    by_contra h
    exact he0 ((smul_eq_zero.mp heq).resolve_left h))

private theorem exists_subgroup_eq_torsionTorus_aux2 {m : ℕ} {e f : Fin m → V}
    {c d : Fin m → Fˣ} {g h : V ≃ₗ[F] V} (hg : IsHypDiag Q e f c g)
    (hh : IsHypDiag Q e f d h) : IsHypDiag Q e f (c * d) (g * h) := by
  refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
  · show g (h (e i)) = _
    rw [hh.1 i, map_smul, hg.1 i, smul_smul, Pi.mul_apply, Units.val_mul, mul_comm]
  · show g (h (f i)) = _
    rw [hh.2.1 i, map_smul, hg.2.1 i, smul_smul]
    have hscal : (↑(((c * d) i)⁻¹) : F) =
        (↑((d i)⁻¹) : F) * (↑((c i)⁻¹) : F) := by
      rw [Pi.mul_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev]
      simp only [Units.val_inv_eq_inv_val]
    rw [hscal]
  · show g (h v) = v
    rw [hh.2.2 v hv1 hv2, hg.2.2 v hv1 hv2]

private theorem exists_subgroup_eq_torsionTorus_aux3 {m : ℕ} {e f : Fin m → V} {c : Fin m → Fˣ}
    {g : V ≃ₗ[F] V} (hg : IsHypDiag Q e f c g) (n : ℕ) :
    IsHypDiag Q e f (c ^ n) (g ^ n) := by
  induction n with
  | zero =>
      simpa using (show IsHypDiag Q e f (1 : Fin m → Fˣ) (1 : V ≃ₗ[F] V) from
        ⟨fun i => by simp, fun i => by simp, fun v _ _ => rfl⟩)
  | succ n ih => simpa [pow_succ] using exists_subgroup_eq_torsionTorus_aux2 ih hg

private theorem exists_subgroup_eq_torsionTorus_aux4 {m : ℕ} {e f : Fin m → V} {c : Fin m → Fˣ}
    {g : V ≃ₗ[F] V} (hg : IsHypDiag Q e f c g) : IsHypDiag Q e f (c⁻¹) (g⁻¹) := by
  change IsHypDiag Q e f (c⁻¹) g.symm
  refine ⟨fun i => ?_, fun i => ?_, fun v hv1 hv2 => ?_⟩
  · change g.symm (e i) = (((c i)⁻¹ : Fˣ) : F) • e i
    rw [LinearEquiv.symm_apply_eq, map_smul, hg.1 i, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (Units.ne_zero (c i)), one_smul]
  · change g.symm (f i) = ((((c i)⁻¹)⁻¹ : Fˣ) : F) • f i
    rw [LinearEquiv.symm_apply_eq, map_smul, hg.2.1 i, smul_smul, inv_inv, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero (c i)), one_smul]
  · show g.symm v = v
    rw [← hg.2.2 v hv1 hv2, LinearEquiv.symm_apply_apply]
    exact (hg.2.2 v hv1 hv2).symm

private def exists_subgroup_eq_torsionTorus_aux5 (p : ℕ) {m : ℕ} (e f : Fin m → V) :
    Subgroup ↥(orthDerived Q) where
  carrier := {g | InTorsionTorus Q p e f (g : V ≃ₗ[F] V)}
  one_mem' := ⟨fun _ => 1, fun _ => one_pow p,
    ⟨fun _ => by simp, fun _ => by simp, fun _ _ _ => rfl⟩⟩
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c * d, fun i => by rw [Pi.mul_apply, mul_pow, hc i, hd i, one_mul],
      by simpa only [Subgroup.coe_mul] using exists_subgroup_eq_torsionTorus_aux2 ha hb⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    exact ⟨c⁻¹, fun i => by rw [Pi.inv_apply, inv_pow, hc i, inv_one],
      by simpa only [Subgroup.coe_inv] using exists_subgroup_eq_torsionTorus_aux4 ha⟩

private theorem exists_subgroup_eq_torsionTorus_aux6 {p : ℕ} {m : ℕ} {e f : Fin m → V}
    (g : ↥(orthDerived Q)) :
    g ∈ exists_subgroup_eq_torsionTorus_aux5 (Q := Q) p e f ↔
      InTorsionTorus Q p e f (g : V ≃ₗ[F] V) :=
  Iff.rfl

private theorem exists_subgroup_eq_torsionTorus_aux7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) :
    IsElemAbelian p (exists_subgroup_eq_torsionTorus_aux5 (Q := Q) p e f) := by
  refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun x hx => ?_⟩
  · obtain ⟨c, hc, ha⟩ := (exists_subgroup_eq_torsionTorus_aux6 a.1).1 a.2
    obtain ⟨d, hd, hb⟩ := (exists_subgroup_eq_torsionTorus_aux6 b.1).1 b.2
    apply Subtype.ext
    apply Subtype.ext
    have h1 : IsHypDiag Q e f (c * d) ((a : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V)) :=
      exists_subgroup_eq_torsionTorus_aux2 ha hb
    have h2 : IsHypDiag Q e f (c * d) ((b : V ≃ₗ[F] V) * (a : V ≃ₗ[F] V)) := by
      have := exists_subgroup_eq_torsionTorus_aux2 hb ha
      rwa [show d * c = c * d from funext fun i => mul_comm _ _] at this
    simpa only [Subgroup.coe_mul] using IsHypDiag.eq_of_isHypDiag hef h1 h2
  · obtain ⟨c, hc, ha⟩ := (exists_subgroup_eq_torsionTorus_aux6 x).1 hx
    apply Subtype.ext
    have h1 : IsHypDiag Q e f (c ^ p) ((x : V ≃ₗ[F] V) ^ p) :=
      exists_subgroup_eq_torsionTorus_aux3 ha p
    have h2 : IsHypDiag Q e f (c ^ p) 1 := by
      rw [show c ^ p = 1 from funext fun i => hc i]
      exact ⟨fun i => by simp, fun i => by simp, fun v _ _ => rfl⟩
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      IsHypDiag.eq_of_isHypDiag hef h1 h2

private theorem exists_subgroup_eq_torsionTorus_aux8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f) :
    Nat.card (exists_subgroup_eq_torsionTorus_aux5 (Q := Q) p e f) = p ^ m := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let W : ↥(exists_subgroup_eq_torsionTorus_aux5 (Q := Q) p e f) → (Fin m → rootsOfUnity p F) :=
    fun g i => ⟨(Classical.choose ((exists_subgroup_eq_torsionTorus_aux6 g.1).1 g.2)) i,
      (Classical.choose_spec ((exists_subgroup_eq_torsionTorus_aux6 g.1).1 g.2)).1 i⟩
  have hW : Function.Bijective W := by
    constructor
    · intro g₁ g₂ h
      apply Subtype.ext
      apply Subtype.ext
      have h1 := Classical.choose_spec ((exists_subgroup_eq_torsionTorus_aux6 g₁.1).1 g₁.2)
      have h2 := Classical.choose_spec ((exists_subgroup_eq_torsionTorus_aux6 g₂.1).1 g₂.2)
      have hw : Classical.choose ((exists_subgroup_eq_torsionTorus_aux6 g₁.1).1 g₁.2) =
          Classical.choose ((exists_subgroup_eq_torsionTorus_aux6 g₂.1).1 g₂.2) :=
        funext fun i => congrArg Subtype.val (congrFun h i)
      rw [hw] at h1
      exact IsHypDiag.eq_of_isHypDiag hef h1.2 h2.2
    · intro c
      obtain ⟨g, hg⟩ := exists_isHypDiag_mem_orthDerived hp hp2 hef (fun i => (c i).2)
      let hmem : InTorsionTorus Q p e f (g : V ≃ₗ[F] V) :=
        ⟨fun i => (c i : Fˣ), fun i => (c i).2, hg⟩
      let gA₀ : ↥(exists_subgroup_eq_torsionTorus_aux5 (Q := Q) p e f) :=
        ⟨g, (exists_subgroup_eq_torsionTorus_aux6 g).2 hmem⟩
      refine ⟨gA₀, ?_⟩
      funext i
      apply Subtype.ext
      have hspec : IsHypDiag Q e f
          (Classical.choose ((exists_subgroup_eq_torsionTorus_aux6 g).1 gA₀.2))
          (g : V ≃ₗ[F] V) :=
        (Classical.choose_spec ((exists_subgroup_eq_torsionTorus_aux6 g).1 gA₀.2)).2
      exact congrFun (exists_subgroup_eq_torsionTorus_aux1 hef hspec hg) i
  have hcard := Nat.card_congr (Equiv.ofBijective W hW)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  have hroot : Nat.card (rootsOfUnity p F) = p :=
    (IsPrimitiveRoot.iff_orderOf.2 hζ).card_rootsOfUnity'
  rw [hcard, Nat.card_fun, hroot, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_subgroup_eq_torsionTorus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) :
    ∃ A₀ : Subgroup ↥(orthDerived Q), IsElemAbelian p A₀ ∧ Nat.card A₀ = p ^ m ∧
      ∀ g : ↥(orthDerived Q), g ∈ A₀ ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V) := by
  exact ⟨exists_subgroup_eq_torsionTorus_aux5 (Q := Q) p e f,
    exists_subgroup_eq_torsionTorus_aux7 hp hp2 hef,
    exists_subgroup_eq_torsionTorus_aux8 hp hp2 hpq hef,
    fun g => exists_subgroup_eq_torsionTorus_aux6 g⟩

private theorem exists_isPGroup_two_normalized_by_torsionTorus_aux1
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {m : ℕ} {e f : Fin m → V} (hef : IsHypFamily Q e f)
    (hV : 3 ≤ finrank F V) (i₀ : Fin m) :
    ∃ w : V, QuadraticMap.polar Q (e i₀) w = 0 ∧ w ∉ F ∙ e i₀ ∧
      eichler Q (e i₀) w ∈ orthDerived Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have he0 : e i₀ ≠ 0 := hef.linearIndependent.ne_zero (Sum.inl i₀)
  have hf : (QuadraticMap.polarBilin Q) (e i₀) ≠ 0 := by
    intro h
    exact he0 (hQ.1 (e i₀) fun y => by rw [h, LinearMap.zero_apply])
  have hdim : finrank F (LinearMap.ker ((QuadraticMap.polarBilin Q) (e i₀))) + 1 = finrank F V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero (f := (QuadraticMap.polarBilin Q) (e i₀)) hf
  have hle : F ∙ e i₀ ≤ LinearMap.ker ((QuadraticMap.polarBilin Q) (e i₀)) := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [LinearMap.mem_ker, map_smul, QuadraticMap.polarBilin_apply_apply,
      polar_self_eq_zero (hef.map_e i₀), smul_zero]
  have hlt : F ∙ e i₀ < LinearMap.ker ((QuadraticMap.polarBilin Q) (e i₀)) := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have h1 : finrank F (LinearMap.ker ((QuadraticMap.polarBilin Q) (e i₀))) = 1 := by
      rw [← heq, finrank_span_singleton he0]
    rw [h1] at hdim
    omega
  obtain ⟨w, hwL, hwE⟩ := SetLike.exists_of_lt hlt
  have hwL' : QuadraticMap.polar Q (e i₀) w = 0 := by
    simpa [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] using hwL
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact hp.ne_one hu.symm
  exact ⟨w, hwL', hwE,
    CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one hQ
      (Units.ne_zero u) (by simpa using hu1) (e i₀) w⟩

private theorem exists_isPGroup_two_normalized_by_torsionTorus_aux2 {m : ℕ} {e f : Fin m → V}
    (hef : IsHypFamily Q e f) (i₀ : Fin m) {w : V} (hwL' : QuadraticMap.polar Q (e i₀) w = 0)
    (hwE : w ∉ F ∙ e i₀) (hEmem : eichler Q (e i₀) w ∈ orthDerived Q) :
    (rootGroup Q (e i₀)).subgroupOf (orthDerived Q) ≠ ⊥ := by
  intro hbot
  let y : ↥(orthDerived Q) := ⟨eichler Q (e i₀) w, hEmem⟩
  have hyU : y ∈ (rootGroup Q (e i₀)).subgroupOf (orthDerived Q) := by
    rw [Subgroup.mem_subgroupOf]
    exact mem_rootGroup.mpr ⟨w, hwL', rfl⟩
  have hy1 : y = 1 := by
    rw [← Subgroup.mem_bot, ← hbot]
    exact hyU
  have hcoe : (y : V ≃ₗ[F] V) = 1 := congrArg Subtype.val hy1
  have happ : eichler Q (e i₀) w (f i₀) = f i₀ := by
    have h := congrArg (fun z : V ≃ₗ[F] V => z (f i₀)) hcoe
    simpa [y] using h
  rw [eichler_apply (hef.map_e i₀) hwL'] at happ
  have hfe : QuadraticMap.polar Q (f i₀) (e i₀) = 1 := by
    rw [QuadraticMap.polar_comm, hef.polar_ef]; simp
  rw [hfe, one_smul, mul_one] at happ
  have hw_eq : w = (QuadraticMap.polar Q (f i₀) w + Q w) • e i₀ := by
    have h' : f i₀ + w = f i₀ + (QuadraticMap.polar Q (f i₀) w + Q w) • e i₀ :=
      sub_eq_iff_eq_add.mp happ
    exact add_left_cancel h'
  exact hwE (by
    rw [Submodule.mem_span_singleton]
    exact ⟨_, hw_eq.symm⟩)

private theorem exists_isPGroup_two_normalized_by_torsionTorus_aux3 {m : ℕ} (e : Fin m → V)
    (i₀ : Fin m) : IsPGroup 2 ((rootGroup Q (e i₀)).subgroupOf (orthDerived Q)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  have hxroot : ((x : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈ rootGroup Q (e i₀) :=
    (Subgroup.mem_subgroupOf).1 x.2
  obtain ⟨w', hw'L, hw'eq⟩ := mem_rootGroup.mp hxroot
  have hw'0 : w' + w' = 0 := by
    rw [← two_smul F w', CharTwo.two_eq_zero, zero_smul]
  have hxV : (((x : ↥(orthDerived Q)) : V ≃ₗ[F] V)) ^ 2 = 1 := by
    rw [← hw'eq, pow_two, eichler_mul hw'L hw'L, hw'0, eichler_zero_right Q (e i₀)]
  apply Subtype.ext
  apply Subtype.ext
  simpa using hxV

private theorem exists_isPGroup_two_normalized_by_torsionTorus_aux4 {m : ℕ} {e f : Fin m → V}
    {p : ℕ} (i₀ : Fin m) {g : ↥(orthDerived Q)}
    (hg : InTorsionTorus Q p e f (g : V ≃ₗ[F] V)) :
    g ∈ Subgroup.normalizer
      (((rootGroup Q (e i₀)).subgroupOf (orthDerived Q) : Subgroup ↥(orthDerived Q)) :
        Set ↥(orthDerived Q)) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hn' : (n : V ≃ₗ[F] V) ∈ rootGroup Q (e i₀) := (Subgroup.mem_subgroupOf).1 hn
  obtain ⟨c, hc, hdiag⟩ := hg
  have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup' g.2
  have hconj := conj_mem_rootGroup_of_apply_eq_smul hgO (hdiag.1 i₀) hn'
  change g * n * g⁻¹ ∈ (rootGroup Q (e i₀)).subgroupOf (orthDerived Q)
  rw [Subgroup.mem_subgroupOf]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj

theorem exists_isPGroup_two_normalized_by_torsionTorus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1) {m : ℕ} (hm : 1 ≤ m)
    (hV : 3 ≤ finrank F V) {e f : Fin m → V} (hef : IsHypFamily Q e f) :
    ∃ U : Subgroup ↥(orthDerived Q), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ g : ↥(orthDerived Q),
      InTorsionTorus Q p e f (g : V ≃ₗ[F] V) → g ∈ Subgroup.normalizer (U : Set ↥(orthDerived Q)) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  let i₀ : Fin m := 0
  obtain ⟨w, hwL', hwE, hEmem⟩ :=
    exists_isPGroup_two_normalized_by_torsionTorus_aux1 hQ hp hp2 hpq hef hV i₀
  refine ⟨(rootGroup Q (e i₀)).subgroupOf (orthDerived Q), ?_, ?_, ?_⟩
  · exact exists_isPGroup_two_normalized_by_torsionTorus_aux2 hef i₀ hwL' hwE hEmem
  · exact exists_isPGroup_two_normalized_by_torsionTorus_aux3 e i₀
  · intro g hg
    exact exists_isPGroup_two_normalized_by_torsionTorus_aux4 i₀ hg

theorem exists_hypFamily_eq_torsionTorus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {A : Subgroup ↥(orthDerived Q)} (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ wittRank Q l) :
    ∃ e f : Fin (wittRank Q l) → V, IsHypFamily Q e f ∧
      ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative A := hA.1
  obtain ⟨e, f, hef⟩ := exists_isHypFamily_wittRank hQ hdim
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rwa [Nat.card_units])
  have hexp : ∀ x : A, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using hA.2 (x : ↥(orthDerived Q)) x.2)
  let ρ : A →* (V ≃ₗ[F] V) := (orthDerived Q).subtype.comp A.subtype
  have hρO : ∀ x, ρ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun x =>
    orthDerived_le_orthogonalGroup' x.1.2
  obtain ⟨g, hg, χ, h1, h2, h3, h4⟩ := exists_orth_conj_weights hQ hp2 hζ
    (fun T hT => finrank_le_wittRank hQ hdim hT) hef ρ hρO
    (fun x y h => Subtype.ext (Subtype.ext h)) hexp hcard.ge
  have hef' := isHypFamily_map hef (inv_mem hg)
  have key : ∀ (x : A) (c : Fin (wittRank Q l) → Fˣ), (∀ k, χ k x = c k) →
      IsHypDiag Q (fun i => g⁻¹ (e i)) (fun i => g⁻¹ (f i)) c
        (((x : ↥(orthDerived Q)) : V ≃ₗ[F] V)) := fun x c hx =>
    (isHypDiag_conj hg).1 ⟨fun k => (h1 x k).trans (by rw [hx k]),
      fun k => (h2 x k).trans (by rw [hx k]), fun v hv1 hv2 => h3 x v hv1 hv2⟩
  refine ⟨fun k => g⁻¹ (e k), fun k => g⁻¹ (f k), hef', fun h => ⟨fun hh => ?_, ?_⟩⟩
  · refine ⟨fun k => χ k ⟨h, hh⟩, fun k => ?_, key ⟨h, hh⟩ _ fun k => rfl⟩
    show (χ k ⟨h, hh⟩) ^ p = 1
    rw [← map_pow, hexp, map_one]
  · rintro ⟨c, hc, hdiag⟩
    obtain ⟨x, hx⟩ := h4 c hc
    have hxh : h = (x : ↥(orthDerived Q)) :=
      Subtype.ext (IsHypDiag.eq_of_isHypDiag hef' hdiag (key x c hx))
    rw [hxh]
    exact x.2

theorem glaTwoLocalRank_eq_wittRank (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) : GLATwoLocalRank p ↥(orthDerived Q) = wittRank Q l := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, f, hef⟩ := exists_isHypFamily_wittRank hQ hdim
  obtain ⟨A₀, hA₀, hcard₀, hmem₀⟩ := exists_subgroup_eq_torsionTorus hQ hp hp2 hpq hef
  have hm : 1 ≤ wittRank Q l := by
    unfold wittRank
    split_ifs <;> omega
  obtain ⟨U, hU0, hU2, hUn⟩ :=
    exists_isPGroup_two_normalized_by_torsionTorus hQ hp hp2 hpq hm (by omega) hef
  have hle : ∀ H : Subgroup ↥(orthDerived Q), CFSG.Open.pRank p H ≤ wittRank Q l := by
    intro H
    refine csSup_le ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => ?_⟩, by simp⟩ ?_
    · rw [Subgroup.mem_bot.1 hx]
      exact one_pow p
    · rintro k ⟨E, -, hE, hk⟩
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1
        (hk ▸ card_le_pow_wittRank hQ hdim hp hp2 hpq hE)
  have hge : wittRank Q l ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set ↥(orthDerived Q))) := by
    refine le_csSup ⟨wittRank Q l, ?_⟩ ⟨A₀, ?_, hA₀, hcard₀⟩
    · rintro k ⟨E, -, hE, hk⟩
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1
        (hk ▸ card_le_pow_wittRank hQ hdim hp hp2 hpq hE)
    · intro g hg
      exact hUn g ((hmem₀ g).1 hg)
  have hloc : IsTwoLocal (Subgroup.normalizer (U : Set ↥(orthDerived Q))) := ⟨U, hU0, hU2, rfl⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup ↥(orthDerived Q), IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
    ⟨wittRank Q l, fun k ⟨H, _, hk⟩ => hk ▸ hle H⟩
  show twoLocalPrimeRank p ↥(orthDerived Q) = wittRank Q l
  refine le_antisymm (csSup_le ⟨_, _, hloc, rfl⟩ fun k ⟨H, _, hk⟩ => hk ▸ hle H) ?_
  exact le_csSup hbdd ⟨_, hloc, le_antisymm (hle _) hge⟩

theorem glaIsBmax_iff (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {A : Subgroup ↥(orthDerived Q)} :
    GLAIsBmax p A ↔ IsElemAbelian p A ∧ Nat.card A = p ^ wittRank Q l := by
  have hrank := glaTwoLocalRank_eq_wittRank hQ hdim hl hp hp2 hpq
  constructor
  · rintro ⟨hAe, hcard, -⟩
    exact ⟨hAe, by rw [hcard, hrank]⟩
  · rintro ⟨hAe, hcard⟩
    refine ⟨hAe, by rw [hcard, hrank], ?_⟩
    have hm : 1 ≤ wittRank Q l := by
      unfold wittRank
      split_ifs <;> omega
    obtain ⟨e, f, hef, hA⟩ := exists_hypFamily_eq_torsionTorus hQ hdim hp hp2 hpq hAe hcard
    obtain ⟨U, hU0, hU2, hUn⟩ :=
      exists_isPGroup_two_normalized_by_torsionTorus hQ hp hp2 hpq hm (by omega) hef
    exact ⟨U, hU0, hU2, fun g hg => hUn g ((hA g).1 hg)⟩

theorem exists_hypFamily_of_isBmax (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {l : ℕ}
    (hdim : finrank F V = 2 * l) (hl : 4 ≤ l) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {A : Subgroup ↥(orthDerived Q)} (hA : GLAIsBmax p A) :
    ∃ e f : Fin (wittRank Q l) → V, IsHypFamily Q e f ∧
      ∀ g : ↥(orthDerived Q), g ∈ A ↔ InTorsionTorus Q p e f (g : V ≃ₗ[F] V) := by
  obtain ⟨hAe, hcard⟩ := (glaIsBmax_iff hQ hdim hl hp hp2 hpq).1 hA
  exact exists_hypFamily_eq_torsionTorus hQ hdim hp hp2 hpq hAe hcard

end Frame

end CFSG.LocalAnalysis.GLTheoremA.T173S

end
