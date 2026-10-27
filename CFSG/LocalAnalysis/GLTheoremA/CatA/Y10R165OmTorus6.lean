module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus5
public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt
public import CFSG.GroupTheory.CommutingMovingElemAbelian
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2

namespace OmTorus

variable {F W : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {Q : QuadraticForm F W}

variable {q : ℕ}

theorem hypPair_polarNondegOn (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    PolarNondegOn Q (Submodule.span F {P.e, P.f}) := by
  intro x hx hxperp
  apply CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQ
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (P.isCompl_perp.sup_eq_top ▸ Submodule.mem_top : v ∈ Submodule.span F {P.e, P.f} ⊔ P.perp)
  rw [polar_add_right, hxperp u hu]
  have horth : ∀ y ∈ Submodule.span F {P.e, P.f}, ∀ z ∈ P.perp, polar Q y z = 0 := by
    intro y hy z hz
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨hz1, hz2⟩ := HypPair.mem_perp.mp hz
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hz1, hz2]
    simp
  rw [horth x hx w hw, add_zero]

theorem hypDiag_orderOf (P : HypPair Q) (mu : Fˣ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hord : orderOf mu = q) :
    orderOf (hypDiag P (mu : F) (Units.ne_zero mu)) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  apply orderOf_eq_prime
  · rw [hypDiag_pow_eq_one P _ _ (by
      rw [← hord]
      exact congrArg (fun x : Fˣ => (x : F)) (pow_orderOf_eq_one mu))]
  · intro h1
    have h2 : (hypDiag P (mu : F) (Units.ne_zero mu)) P.e = P.e := by rw [h1]; rfl
    rw [hypDiag_apply_e] at h2
    have h3 : ((mu : F) - 1) • P.e = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    have h4 : (mu : F) = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right P.e_ne_zero)
    have h5 : mu = 1 := Units.ext h4
    rw [h5, orderOf_one] at hord
    exact hq.ne_one hord.symm

theorem hypDiag_move (P : HypPair Q) (mu : Fˣ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hord : orderOf mu = q) :
    ∀ a : ℤ, (hypDiag P (mu : F) (Units.ne_zero mu) ^ a) P.e = P.e → (q : ℤ) ∣ a := by
  apply dvd_of_zpow_apply_eq_self (act := MonoidHom.id (W ≃ₗ[F] W))
    (t := hypDiag P (mu : F) (Units.ne_zero mu)) (u := P.e)
    (hypDiag_orderOf P mu hq hq2 hord)
  intro m hm hmr hfix
  have h2 : (mu : F) ^ m = 1 := by
    have h3 : ((mu : F) ^ m) • P.e = P.e := by
      simpa [hypDiag_pow_apply_e] using hfix
    have h4 : ((mu : F) ^ m - 1) • P.e = 0 := by
      rw [sub_smul, one_smul, h3, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right P.e_ne_zero)
  have hdvd : q ∣ m := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr (Units.ext h2)
  exact absurd (Nat.le_of_dvd hm hdvd) (not_le.mpr hmr)

theorem hypDiag_fix_other (P P' : HypPair Q) (h : P.Orth P') (a : F) (ha : a ≠ 0) :
    hypDiag P a ha P'.e = P'.e :=
  hypDiag_apply_perp P a ha (HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩)

theorem hypDiag_mapsTo (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    ∀ x ∈ Submodule.span F {P.e, P.f}, hypDiag P a ha x ∈ Submodule.span F {P.e, P.f} := by
  intro x hx
  rw [Submodule.mem_span_pair] at hx ⊢
  obtain ⟨α, β, rfl⟩ := hx
  rw [hypDiag_apply_formula P a ha]
  have h1 : polar Q (α • P.e + β • P.f) P.f = α := by
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef, P.polar_ff, mul_one,
      mul_zero, add_zero]
  have h2 : polar Q (α • P.e + β • P.f) P.e = β := by
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ee, P.polar_fe, mul_one,
      mul_zero, zero_add]
  rw [h1, h2]
  refine ⟨α + (a - 1) * α, β + (a⁻¹ - 1) * β, ?_⟩
  simp only [add_smul, smul_add, smul_smul]
  module

theorem hypDiag_commute (P P' : HypPair Q) (h : P.Orth P') (a : F) (ha : a ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) :
    Commute (hypDiag P a ha) (hypDiag P' a ha) := by
  have hperp : perp Q (Submodule.span F {P.e, P.f}) = P.perp := by
    ext x
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp, HypPair.mem_perp]
    constructor
    · intro h
      exact ⟨h P.e (Submodule.subset_span (Set.mem_insert _ _)),
        h P.f (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
    · rintro ⟨h1, h2⟩ y hy
      rw [Submodule.mem_span_pair] at hy
      obtain ⟨α, β, rfl⟩ := hy
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h1, h2]
      simp
  have hperp' : perp Q (Submodule.span F {P'.e, P'.f}) = P'.perp := by
    ext x
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.mem_perp, HypPair.mem_perp]
    constructor
    · intro h
      exact ⟨h P'.e (Submodule.subset_span (Set.mem_insert _ _)),
        h P'.f (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
    · rintro ⟨h1, h2⟩ y hy
      rw [Submodule.mem_span_pair] at hy
      obtain ⟨α, β, rfl⟩ := hy
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h1, h2]
      simp
  refine commute_of_orthogonal_supports (U₁ := Submodule.span F {P.e, P.f})
    (U₂ := Submodule.span F {P'.e, P'.f}) (hypPair_polarNondegOn hQ P)
    (hypPair_polarNondegOn hQ P') ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_perp]
    intro y hy
    have h1 : polar Q P'.e P.e = 0 := by rw [polar_comm]; exact h.ee
    have h2 : polar Q P'.e P.f = 0 := by rw [polar_comm]; exact h.fe
    have h3 : polar Q P'.f P.e = 0 := by rw [polar_comm]; exact h.ef
    have h4 : polar Q P'.f P.f = 0 := by rw [polar_comm]; exact h.ff
    rw [Submodule.mem_span_pair] at hx hy
    obtain ⟨α, β, rfl⟩ := hx
    obtain ⟨γ, δ, rfl⟩ := hy
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      h1, h2, h3, h4, h.ee, h.ef, h.fe, h.ff, P.polar_ee, P.polar_ff, P'.polar_ee, P'.polar_ff,
      P.polar_ef, P'.polar_ef]
    ring
  · exact fun w hw => hypDiag_apply_perp P a ha (by rwa [hperp] at hw)
  · exact fun w hw => hypDiag_apply_perp P' a ha (by rwa [hperp'] at hw)
  · exact hypDiag_mapsTo P a ha
  · exact hypDiag_mapsTo P' a ha

theorem omTorusThree_hyp (hQ : (polarBilin Q).Nondegenerate) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ Nat.card F - 1) (P : Fin 3 → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    ∃ T : Subgroup (W ≃ₗ[F] W), T ≤ orthDerived Q ∧ IsElemAbelian q T ∧
      3 ≤ CFSG.Open.pRank q T := by
  classical
  obtain ⟨mu, hmu⟩ : ∃ mu : Fˣ, orderOf mu = q :=
    CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq hqdvd
  let t : Fin 3 → (W ≃ₗ[F] W) := fun i => hypDiag (P i) (mu : F) (Units.ne_zero mu)
  have ht_mem : ∀ i, t i ∈ orthDerived Q := fun i =>
    hypDiag_mem_orthDerived (P i) mu hq hq2 hmu
  have ht_order : ∀ i, orderOf (t i) = q := fun i => hypDiag_orderOf (P i) mu hq hq2 hmu
  have ht_comm : ∀ i j, Commute (t i) (t j) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact Commute.refl _
    · exact hypDiag_commute (P i) (P j) (hP i j hij) (mu : F) (Units.ne_zero mu) hQ
  have ht_move : ∀ i (a : ℤ), (t i ^ a) (P i).e = (P i).e → (q : ℤ) ∣ a := fun i =>
    hypDiag_move (P i) mu hq hq2 hmu
  have ht_fix : ∀ i j, i ≠ j → t i (P j).e = (P j).e := fun i j hij =>
    hypDiag_fix_other (P i) (P j) (hP i j hij) (mu : F) (Units.ne_zero mu)
  obtain ⟨T, hTH, hTelem, hTcard, hTrank⟩ :=
    exists_elemAbelian_of_commuting_moving hq t (fun i => (P i).e) (MonoidHom.id _)
      ht_mem ht_order ht_comm ht_move ht_fix
  exact ⟨T, hTH, hTelem, by simpa using hTrank⟩

end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
