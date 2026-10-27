module

public import CFSG.LieType.Steinberg.PartBRankOne
public import CFSG.LieType.Steinberg.CoreBasic
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.CentralExt CFSG.LieType.Universal

namespace RankOneRels

variable {K : Type*} [Group K] {k : Type*} [Field k] (R : RankOneRels K k)

@[expose] def xHom : Multiplicative k →* K :=
  MonoidHom.mk' (fun a => R.x a.toAdd) fun a b => R.x_add a.toAdd b.toAdd

@[expose] def yHom : Multiplicative k →* K :=
  MonoidHom.mk' (fun a => R.y a.toAdd) fun a b => R.y_add a.toAdd b.toAdd

theorem x_mem_range_xHom (a : k) : R.x a ∈ R.xHom.range :=
  ⟨Multiplicative.ofAdd a, rfl⟩

theorem y_mem_range_yHom (a : k) : R.y a ∈ R.yHom.range :=
  ⟨Multiplicative.ofAdd a, rfl⟩

variable {p : ℕ} [CharP k p]

theorem isPGroup_range {f : Multiplicative k →* K} : IsPGroup p f.range := by
  rintro ⟨_, a, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change f a ^ p ^ 1 = 1
  rw [pow_one, ← map_pow, ← ofAdd_toAdd a, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero,
    zero_mul, ofAdd_zero, map_one]

variable [Fact p.Prime]

theorem exists_orderOf_x (a : k) : ∃ n : ℕ, orderOf (R.x a) = p ^ n :=
  exists_orderOf_eq_pow_of_mem (isPGroup_range (f := R.xHom)) ⟨_, R.x_mem_range_xHom a⟩

theorem exists_orderOf_y (a : k) : ∃ n : ℕ, orderOf (R.y a) = p ^ n :=
  exists_orderOf_eq_pow_of_mem (isPGroup_range (f := R.yHom)) ⟨_, R.y_mem_range_yHom a⟩

variable {E : Type*} [Group E] [Finite E] {π : E →* K}
  (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hC : ¬p ∣ Nat.card π.ker)

@[expose] noncomputable def lift : RankOneRels E k where
  x a := pLift p π (R.x a)
  y a := pLift p π (R.y a)
  x_add a b := by
    rw [R.x_add]
    exact pLift_mul hπ hcen hC (isPGroup_range (f := R.xHom)) (R.x_mem_range_xHom a)
      (R.x_mem_range_xHom b)
  y_add a b := by
    rw [R.y_add]
    exact pLift_mul hπ hcen hC (isPGroup_range (f := R.yHom)) (R.y_mem_range_yHom a)
      (R.y_mem_range_yHom b)
  conj_x t ht a := by
    have hx : ∀ c, π (pLift p π (R.x c)) = R.x c := fun c =>
      map_pLift hπ hC (R.exists_orderOf_x c)
    have hy : ∀ c, π (pLift p π (R.y c)) = R.y c := fun c =>
      map_pLift hπ hC (R.exists_orderOf_y c)
    refine eq_of_pElement hcen hC ?_ ?_ (orderOf_pLift hπ hC (R.exists_orderOf_y _))
    · simp only [map_mul, map_inv, hx, hy]
      exact R.conj_x t ht a
    · exact exists_orderOf_map_eq_pow (MulAut.conj _).toMonoidHom
        (orderOf_pLift hπ hC (R.exists_orderOf_x a))

theorem lift_x (a : k) : (R.lift hπ hcen hC).x a = pLift p π (R.x a) :=
  rfl

theorem lift_y (a : k) : (R.lift hπ hcen hC).y a = pLift p π (R.y a) :=
  rfl

theorem map_lift_x (a : k) : π ((R.lift hπ hcen hC).x a) = R.x a :=
  map_pLift hπ hC (R.exists_orderOf_x a)

theorem map_lift_y (a : k) : π ((R.lift hπ hcen hC).y a) = R.y a :=
  map_pLift hπ hC (R.exists_orderOf_y a)

theorem map_lift_w (t : k) : π ((R.lift hπ hcen hC).w t) = R.w t := by
  rw [RankOneRels.w_def, RankOneRels.w_def, map_mul, map_mul, map_lift_x, map_lift_y]

theorem map_lift_h (t : k) : π ((R.lift hπ hcen hC).h t) = R.h t := by
  rw [RankOneRels.h_def, RankOneRels.h_def, map_mul, map_inv, map_lift_w, map_lift_w]

theorem map_lift_sub : (R.lift hπ hcen hC).sub.map π = R.sub := by
  rw [RankOneRels.sub, RankOneRels.sub, MonoidHom.map_closure, Set.image_union]
  congr 2
  · ext g
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, map_lift_x]
  · ext g
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, map_lift_y]

variable [Finite k]

theorem injOn_lift_sub (hi : ∀ a t, t ≠ 0 → R.x a * R.h t = 1 → a = 0 ∧ t = 1)
    (hii : ∀ a b t, t ≠ 0 → R.x a * R.w 1 * R.x b * R.h t ≠ 1) :
    Set.InjOn π (R.lift hπ hcen hC).sub := by
  set R' := R.lift hπ hcen hC
  refine injOn_of_eq_one fun g hg h1 => ?_
  rcases R'.sub_subset_bruhat (fun s t hs ht => R'.h_mul hs ht) hg with
    ⟨a, t, ht, rfl⟩ | ⟨a, b, t, ht, rfl⟩
  · rw [map_mul, map_lift_x, map_lift_h] at h1
    obtain ⟨rfl, rfl⟩ := hi a t ht h1
    rw [R'.x_zero, R'.h_one, one_mul]
  · rw [map_mul, map_mul, map_mul, map_lift_x, map_lift_w, map_lift_x, map_lift_h] at h1
    exact absurd h1 (hii a b t ht)

include hπ hcen hC in
theorem exists_lift_of_separated (hi : ∀ a t, t ≠ 0 → R.x a * R.h t = 1 → a = 0 ∧ t = 1)
    (hii : ∀ a b t, t ≠ 0 → R.x a * R.w 1 * R.x b * R.h t ≠ 1) :
    ∃ φ : R.sub →* E, ∀ g, π (φ g) = g := by
  set L' := (R.lift hπ hcen hC).sub
  have hmap : ∀ g : L', π g ∈ R.sub := fun g => by
    rw [← R.map_lift_sub hπ hcen hC]
    exact ⟨g, g.2, rfl⟩
  let ψ : L' →* R.sub := (π.comp L'.subtype).codRestrict _ hmap
  have hψ : Function.Bijective ψ := by
    refine ⟨fun g g' h => Subtype.ext (R.injOn_lift_sub hπ hcen hC hi hii g.2 g'.2
      (congrArg Subtype.val h)), fun g => ?_⟩
    obtain ⟨g', hg', hgg'⟩ : (g : K) ∈ L'.map π := by
      rw [R.map_lift_sub hπ hcen hC]
      exact g.2
    exact ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩
  refine ⟨L'.subtype.comp (MulEquiv.ofBijective ψ hψ).symm.toMonoidHom, fun g => ?_⟩
  have h := congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply g)
  exact h

end RankOneRels

section Universal

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {k : Type*} [Field k] [Finite k] {p : ℕ} [CharP k p]
  [Fact p.Prime] {E : Type*} [Group E] [Finite E] {π : E →* K}

theorem exists_rankOne_lift_of_rankOneRels (hext : SteinbergExtras D n H) (i : Fin D.rank)
    (R : RankOneRels K k) (hx : ∀ g, g ∈ D.rootGroup (Pi.single i 1) ↔ ∃ a, R.x a = g)
    (hy : ∀ g, g ∈ D.rootGroup (-Pi.single i 1) ↔ ∃ a, R.y a = g)
    (hxinj : Function.Injective R.x) (hh : ∀ t, t ≠ 0 → R.h t = 1 → t = 1)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬p ∣ Nat.card π.ker) :
    ∃ φ : ↥(CurtisTits.rankOne D.rootGroup i) →* E, ∀ g, π (φ g) = g := by
  have hroots : Pi.single i 1 ∈ D.roots ∧ -Pi.single i 1 ∈ D.roots :=
    ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)⟩
  have hL : CurtisTits.rankOne D.rootGroup i = R.sub := by
    have hX : D.rootGroup (Pi.single i 1) = Subgroup.closure (Set.range R.x) := by
      refine le_antisymm (fun g hg => Subgroup.subset_closure
        (show g ∈ Set.range R.x from (hx g).1 hg)) ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact (hx _).2 ⟨a, rfl⟩
    have hY : D.rootGroup (-Pi.single i 1) = Subgroup.closure (Set.range R.y) := by
      refine le_antisymm (fun g hg => Subgroup.subset_closure
        (show g ∈ Set.range R.y from (hy g).1 hg)) ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact (hy _).2 ⟨a, rfl⟩
    rw [CurtisTits.rankOne, hX, hY, ← Subgroup.closure_union]
    rfl
  have hxmem : ∀ a, R.x a ∈ D.rootGroup (Pi.single i 1) := fun a => (hx _).2 ⟨a, rfl⟩
  have hymem : ∀ a, R.y a ∈ D.rootGroup (-Pi.single i 1) := fun a => (hy _).2 ⟨a, rfl⟩
  have hconj : ∀ {S : Subgroup K} {g : K}, (∀ s ∈ S, g * s * g⁻¹ ∈ S) →
      (∀ s ∈ S, g⁻¹ * s * g ∈ S) → g ∈ Subgroup.normalizer (S : Set K) := by
    intro S g h1 h2
    refine Subgroup.mem_normalizer_iff.2 fun s => ⟨h1 s, fun hs => ?_⟩
    have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    rw [← e]
    exact h2 _ hs
  have hhx : ∀ t, t ≠ 0 →
      R.h t ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) := by
    intro t ht
    refine hconj (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨c, rfl⟩ := (hx s).1 hs
      rw [R.h_conj_x ht]
      exact hxmem _
    · obtain ⟨c, rfl⟩ := (hx s).1 hs
      have e : R.h t * R.x ((t ^ 2)⁻¹ * c) * (R.h t)⁻¹ = R.x c := by
        rw [R.h_conj_x ht, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ht), one_mul]
      rw [← e]
      have e' : (R.h t)⁻¹ * (R.h t * R.x ((t ^ 2)⁻¹ * c) * (R.h t)⁻¹) * R.h t =
          R.x ((t ^ 2)⁻¹ * c) := by group
      rw [e']
      exact hxmem _
  have hhy : ∀ t, t ≠ 0 →
      R.h t ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
    intro t ht
    refine hconj (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨c, rfl⟩ := (hy s).1 hs
      rw [R.h_conj_y ht]
      exact hymem _
    · obtain ⟨c, rfl⟩ := (hy s).1 hs
      have e : R.h t * R.y (t ^ 2 * c) * (R.h t)⁻¹ = R.y c := by
        rw [R.h_conj_y ht, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 ht), one_mul]
      rw [← e]
      have e' : (R.h t)⁻¹ * (R.h t * R.y (t ^ 2 * c) * (R.h t)⁻¹) * R.h t =
          R.y (t ^ 2 * c) := by group
      rw [e']
      exact hymem _
  have hi : ∀ a t, t ≠ 0 → R.x a * R.h t = 1 → a = 0 ∧ t = 1 := by
    intro a t ht h1
    have hxa : R.x a = (R.h t)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hnorm : R.x a ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
      rw [hxa]
      exact Subgroup.inv_mem _ (hhy t ht)
    have hx1 := hext.eq_one_of_mem_normalizer i _ (hxmem a) hnorm
    have ha : a = 0 := hxinj (hx1.trans R.x_zero.symm)
    refine ⟨ha, hh t ht ?_⟩
    rw [hx1, one_mul] at h1
    exact h1
  have hii : ∀ a b t, t ≠ 0 → R.x a * R.w 1 * R.x b * R.h t ≠ 1 := by
    intro a b t htz h1
    have hw : R.w 1 = (R.x a)⁻¹ * (R.x b * R.h t)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_eq_one_iff_eq_inv, ← mul_assoc]
      exact h1
    have hwnorm : R.w 1 ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) := by
      rw [hw]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer (hxmem a)))
        (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer (hxmem b)) (hhx t htz)))
    have hle : D.rootGroup (-Pi.single i 1) ≤ D.rootGroup (Pi.single i 1) := by
      intro g hg
      obtain ⟨c, rfl⟩ := (hy g).1 hg
      rw [R.y_eq_conj]
      exact (Subgroup.mem_normalizer_iff.1 hwnorm _).1 (hxmem _)
    have hpos : D.rootGroup (Pi.single i 1) ≤
        ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ :=
      le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}) => D.rootGroup γ) _
        ⟨hroots.1, by rw [ht_single]; exact one_pos⟩ le_rfl
    have hneg : D.rootGroup (-Pi.single i 1) ≤
        ⨆ γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}, D.rootGroup γ :=
      le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}) => D.rootGroup γ) _
        ⟨hroots.2, by rw [ht_neg, ht_single]; exact neg_one_lt_zero⟩ le_rfl
    have hbot : D.rootGroup (-Pi.single i 1) = ⊥ := by
      rw [eq_bot_iff, ← hext.posPart_inf_negPart]
      exact le_inf (hle.trans hpos) hneg
    exact hext.ne_bot _ hroots.2 hbot
  rw [hL]
  exact R.exists_lift_of_separated hπ hcen hC hi hii

end Universal

end CFSG.LieType.Steinberg
