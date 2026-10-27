module

public import CFSG.GH74.Generic.S1.KL3Lift

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S1

theorem kl3cl_rep_of_stated (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {H : Subgroup (GL ι K)} {S : Type} [Group S] (e : S ≃* StatedProj H) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 3) {Pb : Subgroup S} (eSL : ↥Pb ≃* SL(3, F)) {yb : S}
    (hyb : yb ∈ Pb) (hyb2 : orderOf yb = 2)
    (hsolv : Group.IsSolvable ↥(centralizer ({yb} : Set S))) :
    ∃ (ρ : SL(3, F) →* GL ι K) (y : GL ι K), Function.Injective ρ ∧ (∀ g, ρ g ∈ H) ∧
      (∃ y₀ : SL(3, F), ρ y₀ = y) ∧ y * y = 1 ∧
      (∀ c : Kˣ, (y : Matrix ι ι K) ≠ (c : K) • (1 : Matrix ι ι K)) ∧
      (∀ Q : Subgroup (GL ι K), Q ≤ H → (∀ q ∈ Q, q * y = y * q) → ⁅Q, Q⁆ = Q →
        (∀ q ∈ Q, (∃ c : Kˣ, (q : Matrix ι ι K) = (c : K) • (1 : Matrix ι ι K)) → q = 1) →
        Q = ⊥) := by
  classical
  let π : ↥H →* S := e.symm.toMonoidHom.comp (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H))
  have hπ : Function.Surjective π := fun s => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e s)
    exact ⟨x, by simp [π, hx]⟩
  have hπone : ∀ x : ↥H, π x = 1 ↔ (x : GL ι K) ∈ StatedScalars ι K := by
    intro x
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x = 1 := by
        have : e.symm (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x) = 1 := hx
        simpa using this
      exact (QuotientGroup.eq_one_iff x).1 h1
    · intro hx
      have h1 : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x = 1 :=
        (QuotientGroup.eq_one_iff x).2 hx
      show e.symm (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x) = 1
      rw [h1, map_one]
  have hker : π.ker ≤ Subgroup.center ↥H := by
    intro x hx
    have h2' : (x : GL ι K) ∈ StatedScalars ι K := (hπone x).1 hx
    have h3 : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2'
      exact h2'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 h3 (g : GL ι K))
  have hscal : ∀ g : GL ι K, (∃ c : Kˣ, (g : Matrix ι ι K) = (c : K) • (1 : Matrix ι ι K)) ↔
      g ∈ StatedScalars ι K := by
    intro g
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      apply Units.ext
      rw [hc]
      simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hc]
      simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  obtain ⟨θ, hθinj, hθ⟩ := kl3_exists_lift hGA π hπ hker hF Pb eSL
  let y₀ : SL(3, F) := eSL ⟨yb, hyb⟩
  have hθy : π (θ y₀) = yb := by
    rw [hθ]
    simp [y₀]
  have hyb1 : yb ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyb2
    exact absurd hyb2 (by norm_num)
  have hybsq : yb * yb = 1 := by
    rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hyb2])
  have hy₀sq : y₀ * y₀ = 1 := by
    have : (⟨yb, hyb⟩ : ↥Pb) * ⟨yb, hyb⟩ = 1 := Subtype.ext hybsq
    rw [← map_mul, this, map_one]
  refine ⟨H.subtype.comp θ, ((θ y₀ : ↥H) : GL ι K), ?_, ?_, ⟨y₀, rfl⟩, ?_, ?_, ?_⟩
  · exact H.subtype_injective.comp hθinj
  · intro g; exact (θ g).2
  · have : θ y₀ * θ y₀ = 1 := by rw [← map_mul, hy₀sq, map_one]
    exact congrArg Subtype.val this
  · intro c hc
    have h1 : ((θ y₀ : ↥H) : GL ι K) ∈ StatedScalars ι K := (hscal _).1 ⟨c, hc⟩
    exact hyb1 (hθy ▸ (hπone (θ y₀)).2 h1)
  · intro Q hQH hQc hQp hQs
    by_contra hQne
    obtain ⟨q₀, hq₀, hq₀ne⟩ : ∃ q ∈ Q, q ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hQne ((Subgroup.eq_bot_iff_forall Q).2 hcon)
    let incl : ↥Q →* ↥H := Subgroup.inclusion hQH
    let φ : ↥Q →* S := π.comp incl
    have hperf : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQp
    let R : Subgroup S := φ.range
    have hRperf : Group.IsPerfect ↥R := Group.IsPerfect.ofSurjective φ.rangeRestrict_surjective
    have hRle : R ≤ centralizer ({yb} : Set S) := by
      rintro _ ⟨q, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hθy]
      show π (incl q) * π (θ y₀) = π (θ y₀) * π (incl q)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hQc q q.2)
    have hRsolv : Group.IsSolvable ↥R :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hRle)
        (Subgroup.inclusion_injective hRle)
    have hRtriv : R = ⊥ := by
      by_contra hne
      have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hne
      exact Group.IsPerfect.not_isSolvable ↥R hRsolv
    have hφq₀ : φ ⟨q₀, hq₀⟩ = 1 := by
      have : φ ⟨q₀, hq₀⟩ ∈ R := ⟨_, rfl⟩
      rw [hRtriv] at this
      exact this
    have : (q₀ : GL ι K) ∈ StatedScalars ι K := (hπone (incl ⟨q₀, hq₀⟩)).1 hφq₀
    exact hq₀ne (hQs q₀ hq₀ ((hscal q₀).2 this))

end CFSG.GH74.Generic.S1
