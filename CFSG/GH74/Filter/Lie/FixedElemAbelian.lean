module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.Filter.Lie

theorem exists_fixed_subgroup_card_sq {M : Type*} [Group M] (F : M ≃* M) (hFF : ∀ g, F (F g) = g)
    (R : Subgroup M) [Finite R] (hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hsq : ∀ x ∈ R, x * x = 1) (hF : ∀ x ∈ R, F x ∈ R) :
    ∃ E : Subgroup M, E ≤ R ∧ (∀ x ∈ E, F x = x) ∧ Nat.card R ≤ Nat.card E ^ 2 := by
  let θ : R →* R :=
    { toFun := fun x => ⟨x * F x, R.mul_mem x.2 (hF x x.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul, map_mul]
        have h := hcomm (F x) (hF x x.2) y y.2
        calc (x : M) * y * (F x * F y) = x * (y * F x) * F y := by group
          _ = x * (F x * y) * F y := by rw [← h]
          _ = _ := by group }
  have hθ : ∀ x : R, ((θ x : R) : M) = x * F x := fun x => rfl
  have hkerfix : ∀ x : R, x ∈ θ.ker → F x = x := by
    intro x hx
    have h1 : (x : M) * F x = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [hθ] using this
    have h2 := hsq x x.2
    calc F x = (x : M)⁻¹ * (x * F x) := by group
      _ = (x : M)⁻¹ * 1 := by rw [h1]
      _ = x := by
        rw [mul_one]
        exact inv_eq_of_mul_eq_one_right h2
  have hrange : θ.range ≤ θ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    rw [hθ, hθ]
    have h1 : F (x * F x : M) = F x * x := by rw [map_mul, hFF]
    have hFs := hsq (F x) (hF x x.2)
    have hxs := hsq x x.2
    show (x * F x) * F (x * F x) = 1
    rw [h1]
    calc (x : M) * F x * (F x * x) = x * (F x * F x) * x := by group
      _ = 1 := by rw [hFs]; simpa using hxs
  refine ⟨θ.ker.map R.subtype, fun y ⟨x, _, hx⟩ => hx ▸ x.2, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hkerfix x hx
  · have h1 := Subgroup.card_ker_mul_card_range θ
    have h2 : Nat.card θ.range ≤ Nat.card θ.ker := Subgroup.card_le_of_le hrange
    have h3 : Nat.card (θ.ker.map R.subtype) = Nat.card θ.ker :=
      Subgroup.card_map_of_injective R.subtype_injective
    rw [h3, ← h1, sq]
    exact Nat.mul_le_mul_left _ h2

theorem map_range_noncommPiCoprod_le {ι : Type} [Fintype ι] [DecidableEq ι] {N M : Type*}
    [Group N] [Group M] (f : ι → N →* M)
    (hcomm : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) (F : M ≃* M)
    (h : ∀ i y, F (f i y) ∈ (MonoidHom.noncommPiCoprod f hcomm).range) :
    ∀ x ∈ (MonoidHom.noncommPiCoprod f hcomm).range,
      F x ∈ (MonoidHom.noncommPiCoprod f hcomm).range := by
  intro x hx
  have hR : (MonoidHom.noncommPiCoprod f hcomm).range = ⨆ i, (f i).range :=
    MonoidHom.noncommPiCoprod_range f
  have key : (⨆ i, (f i).range) ≤
      ((MonoidHom.noncommPiCoprod f hcomm).range).comap F.toMonoidHom := by
    refine iSup_le fun i => ?_
    rintro _ ⟨y, rfl⟩
    exact h i y
  rw [hR] at hx
  exact key hx

theorem exists_fixed_elemAbelian_of_pi {K : Type} [AddCommGroup K] [Finite K] {M : Type*}
    [Group M] [Finite M] (F : M ≃* M) (hFF : ∀ g, F (F g) = g) (h2 : ∀ x : K, x + x = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Multiplicative K →* M)
    (hcomm : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))
    (hinj : Function.Injective (MonoidHom.noncommPiCoprod f hcomm))
    (hstab : ∀ i y, F (f i y) ∈ (MonoidHom.noncommPiCoprod f hcomm).range) :
    ∃ E : Subgroup M, (∀ x ∈ E, F x = x) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x * x = 1) ∧ Nat.card K ^ Fintype.card ι ≤ Nat.card E ^ 2 := by
  set Φ := MonoidHom.noncommPiCoprod f hcomm with hΦ
  have hRc : ∀ x ∈ Φ.range, ∀ y ∈ Φ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm a b]
  have hRs : ∀ x ∈ Φ.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    convert map_one Φ
    funext i
    apply Multiplicative.toAdd.injective
    simp only [Pi.mul_apply, toAdd_mul, toAdd_one, Pi.one_apply]
    exact h2 _
  obtain ⟨E, hER, hEF, hEcard⟩ := exists_fixed_subgroup_card_sq F hFF Φ.range hRc hRs
    (map_range_noncommPiCoprod_le f hcomm F hstab)
  refine ⟨E, hEF, fun x hx y hy => hRc x (hER hx) y (hER hy), fun x hx => hRs x (hER hx), ?_⟩
  have hcard : Nat.card Φ.range = Nat.card K ^ Fintype.card ι := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi, Finset.prod_const,
      Finset.card_univ]
    congr 1
  rw [← hcard]
  exact hEcard

end CFSG.GH74.Filter.Lie
