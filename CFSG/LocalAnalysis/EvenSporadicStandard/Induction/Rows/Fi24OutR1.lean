module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G]

section Normal

variable {N : Subgroup G} [N.Normal]

theorem fi24OutR_conjNormal_coe (n : N) :
    (MulAut.conjNormal (n : G) : MulAut N) = MulAut.conj n := by
  ext p
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem fi24OutR_conj_mul_conjNormal (n : N) (r : G) :
    MulAut.conj n * MulAut.conjNormal r * (MulAut.conj n)⁻¹ =
      (MulAut.conjNormal ((n : G) * r * (n : G)⁻¹) : MulAut N) := by
  rw [← fi24OutR_conjNormal_coe, ← map_inv, ← map_mul, ← map_mul]

theorem fi24OutR_mem_fixSubgroup_iff (r : G) (p : N) :
    p ∈ fixSubgroup (MulAut.conjNormal r : MulAut N) ↔ (p : G) * r = r * p := by
  show MulAut.conjNormal r p = p ↔ _
  rw [← Subtype.coe_inj, MulAut.conjNormal_apply]
  constructor
  · intro h
    calc (p : G) * r = r * p * r⁻¹ * r := by rw [h]
      _ = r * p := by group
  · intro h
    rw [← h]
    group

theorem fi24OutR_map_fixSubgroup (r : G) :
    (fixSubgroup (MulAut.conjNormal r : MulAut N)).map N.subtype = N ⊓ centralizer {r} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, mem_centralizer_singleton_iff.2 ((fi24OutR_mem_fixSubgroup_iff r p).1 hp)⟩
  · rintro ⟨hx, hxc⟩
    exact ⟨⟨x, hx⟩, (fi24OutR_mem_fixSubgroup_iff r _).2 (mem_centralizer_singleton_iff.1 hxc),
      rfl⟩

theorem fi24OutR_fixSubgroup_eq_subgroupOf (r : G) :
    fixSubgroup (MulAut.conjNormal r : MulAut N) = (N ⊓ centralizer {r}).subgroupOf N := by
  ext p
  rw [mem_subgroupOf, fi24OutR_mem_fixSubgroup_iff]
  exact ⟨fun h => ⟨p.2, mem_centralizer_singleton_iff.2 h⟩,
    fun h => mem_centralizer_singleton_iff.1 h.2⟩

noncomputable def fi24OutR_fixEquiv (r : G) :
    ↥(fixSubgroup (MulAut.conjNormal r : MulAut N)) ≃* ↥(N ⊓ centralizer {r}) :=
  (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr (fi24OutR_map_fixSubgroup r))

theorem fi24OutR_conjNormal_injective (hM : AutModel N (⊤ : Subgroup G)) :
    Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  refine hM.inj r (mem_top r) fun p hp => ?_
  have h := congrArg Subtype.val (DFunLike.congr_fun hr ⟨p, hp⟩)
  rw [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc r * p = r * p * r⁻¹ * r := by group
    _ = p * r := by rw [h]

theorem fi24OutR_conjNormal_surjective (hM : AutModel N (⊤ : Subgroup G)) :
    Function.Surjective (MulAut.conjNormal : G →* MulAut N) := by
  intro α
  obtain ⟨r, -, hr⟩ := hM.surj α
  exact ⟨r, MulEquiv.ext fun p => Subtype.ext (by rw [MulAut.conjNormal_apply, hr p])⟩

end Normal

theorem fi24OutR_map_centralizer (H : Subgroup G) (h : H) :
    (centralizer ({h} : Set H)).map H.subtype = H ⊓ centralizer {(h : G)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val
      (mem_centralizer_singleton_iff.1 hy))⟩
  · rintro ⟨hx, hxc⟩
    exact ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 hxc)), rfl⟩

theorem fi24OutR_card_centralizer_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card (centralizer ({a} : Set A)) = Nat.card (centralizer ({e a} : Set B)) :=
  Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    show x * a = a * x ↔ e x * e a = e a * e x
    rw [← map_mul, ← map_mul, e.injective.eq_iff])

theorem fi24OutR_isCoatom_map {J' R' : Subgroup G} (h : J' ≤ R') {M' : Subgroup J'}
    (hM : IsCoatom M') :
    IsCoatom ((M'.map (Subgroup.inclusion h)).subgroupOf (J'.subgroupOf R')) := by
  have e : (M'.map (Subgroup.inclusion h)).subgroupOf (J'.subgroupOf R') =
      M'.map (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom := by
    ext p
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨g, hg, hgp⟩
      exact ⟨g, hg, Subtype.ext hgp⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [e]
  exact (OrderIso.isCoatom_iff (Subgroup.subgroupOfEquivOfLe h).symm.mapSubgroup M').2 hM

theorem fi24OutR_conj_eq_of_perfect {B : Subgroup G} (hperf : ⁅B, B⁆ = B) {x₁ x₂ x₃ : G}
    (h : ∀ b ∈ B, ∀ x ∈ ({x₁, x₂, x₃} : Set G), b * x * b⁻¹ ∈ ({x₁, x₂, x₃} : Set G)) :
    ∀ b ∈ B, ∀ x ∈ ({x₁, x₂, x₃} : Set G), b * x * b⁻¹ = x := by
  let _ : MulAction ↥B ↥({x₁, x₂, x₃} : Set G) :=
    { smul := fun b x => ⟨(b : G) * x * (b : G)⁻¹, h b b.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : B) : G) * x * ((1 : B) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : B) : G) * x * ((a * b : B) : G)⁻¹ = a * (b * x * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have : Finite ↥({x₁, x₂, x₃} : Set G) :=
    (((Set.finite_singleton x₃).insert x₂).insert x₁).to_subtype
  have hcard : Nat.card ↥({x₁, x₂, x₃} : Set G) ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    have h1 := Set.ncard_insert_le x₁ ({x₂, x₃} : Set G)
    have h2 := Set.ncard_insert_le x₂ ({x₃} : Set G)
    rw [Set.ncard_singleton] at h2
    omega
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.2 hperf
  have : Group.IsSolvable (Equiv.Perm ↥({x₁, x₂, x₃} : Set G)) := Equiv.Perm.isSolvable hcard
  set φ := MulAction.toPermHom ↥B ↥({x₁, x₂, x₃} : Set G)
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro b hb x hx
  have h1 : φ ⟨b, hb⟩ = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨φ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩ : φ.range) 1)
  exact congrArg (fun σ : Equiv.Perm ↥({x₁, x₂, x₃} : Set G) => (σ ⟨x, hx⟩ : G)) h1

theorem fi24OutR_factorization_two {k m : ℕ} (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat, add_zero]

end CFSG.EvenSporadicStandard.Induction
