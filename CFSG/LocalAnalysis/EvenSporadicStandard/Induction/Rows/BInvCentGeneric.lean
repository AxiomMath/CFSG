module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FixLift

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup
open scoped commutatorElement

theorem eq_one_of_a5_comm {A : Type*} [CommGroup A] {x y : A} (hx : x * x = 1)
    (hy : y * y * y = 1) (h : (x * y) ^ 5 = 1) : x = 1 ∧ y = 1 := by
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hx
  have hy3 : y ^ 3 = 1 := by rw [pow_succ, sq]; exact hy
  rw [mul_pow] at h
  have hx5 : x ^ 5 = x := by
    rw [show 5 = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hx2, one_pow, one_mul]
  have hy5 : y ^ 5 = y ^ 2 := by
    rw [show 5 = 3 + 2 from rfl, pow_add, hy3, one_mul]
  rw [hx5, hy5] at h
  have hy2 : y ^ 2 = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy3)
  rw [hy2] at h
  have hxy : x = y := mul_inv_eq_one.1 h
  subst hxy
  have h1 : x = 1 := by
    calc x = x ^ 3 := by rw [pow_succ, hx2, one_mul]
      _ = 1 := hy3
  exact ⟨h1, h1⟩

theorem commutator_eq_top_of_a5 {P : Type*} [Group P] {a b : P}
    (hgen : closure ({a, b} : Set P) = ⊤) (ha : a * a = 1) (hb : b * b * b = 1)
    (hab : (a * b) ^ 5 = 1) : commutator P = ⊤ := by
  obtain ⟨h1, h2⟩ := eq_one_of_a5_comm (x := Abelianization.of a) (y := Abelianization.of b)
    (by rw [← map_mul, ha, map_one]) (by rw [← map_mul, ← map_mul, hb, map_one])
    (by rw [← map_mul, ← map_pow, hab, map_one])
  have hker : closure ({a, b} : Set P) ≤ (Abelianization.of : P →* Abelianization P).ker := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with h | h
    · rw [h]
      exact h1
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact h2
  rw [hgen, top_le_iff, Abelianization.ker_of] at hker
  exact hker

theorem isPerfect_closure_pair {K : Type*} [Group K] {a b : K} (ha : a * a = 1)
    (hb : b * b * b = 1) (hab : (a * b) ^ 5 = 1) :
    Group.IsPerfect ↥(closure ({a, b} : Set K)) := by
  have hamem : a ∈ closure ({a, b} : Set K) := subset_closure (Set.mem_insert _ _)
  have hbmem : b ∈ closure ({a, b} : Set K) :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hgen : closure ({⟨a, hamem⟩, ⟨b, hbmem⟩} : Set ↥(closure ({a, b} : Set K))) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (G := K) (k := ({a, b} : Set K))
    convert h using 2
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  refine Group.isPerfect_def.2 (commutator_eq_top_of_a5 hgen ?_ ?_ ?_)
  · exact Subtype.ext ha
  · exact Subtype.ext hb
  · exact Subtype.ext hab

theorem commutator_le_centralizer_of_central_twist {G : Type*} [Group G] {D : Subgroup G} {t : G}
    (hc : ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ center G) :
    ⁅D, D⁆ ≤ centralizer ({t} : Set G) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  let ψ := twistedCommHom (le_refl (center G)) hc
  have h1 := map_commutatorElement ψ ⟨a, ha⟩ ⟨b, hb⟩
  have h3 : ⁅ψ ⟨a, ha⟩, ψ ⟨b, hb⟩⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.1 (hc a ha) (ψ ⟨b, hb⟩)).symm
  rw [h3] at h1
  have h4 : ⁅a, b⁆ * t * ⁅a, b⁆⁻¹ * t⁻¹ = 1 := h1
  rw [mem_centralizer_singleton_iff]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem not_isSolvable_centralizer_of_perfect_section {G K : Type*} [Group G] [Group K]
    (π : G →* K) (hπ : Function.Surjective π) {t : G} {P : Subgroup K} [Nontrivial P]
    [Group.IsPerfect P] (hc : ∀ d : G, π d ∈ P → d * t * d⁻¹ * t⁻¹ ∈ center G) :
    ¬ Group.IsSolvable ↥(centralizer ({t} : Set G)) := by
  intro hsolv
  set D : Subgroup G := P.comap π with hD
  have hle : ⁅D, D⁆ ≤ centralizer ({t} : Set G) :=
    commutator_le_centralizer_of_central_twist (fun d hd => hc d hd)
  have himg : (⁅D, D⁆).map π = P := by
    rw [Subgroup.map_commutator, hD, Subgroup.map_comap_eq_self_of_surjective hπ,
      Subgroup.commutator_eq_self]
  have hsD : Group.IsSolvable ↥⁅D, D⁆ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  let ρ : ↥⁅D, D⁆ →* K := π.comp (⁅D, D⁆).subtype
  have hρ : ρ.range = P := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, himg]
  have hsr : Group.IsSolvable ↥ρ.range :=
    Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have hsP : Group.IsSolvable ↥P :=
    Group.isSolvable_of_surjective (f := (MulEquiv.subgroupCongr hρ).toMonoidHom)
      (MulEquiv.subgroupCongr hρ).surjective
  exact Group.IsPerfect.not_isSolvable P hsP

theorem isSolvable_centralizer_subgroup {G : Type*} [Group G] (H : Subgroup G) (t : ↥H)
    (h : Group.IsSolvable ↥(centralizer ({(t : G)} : Set G))) :
    Group.IsSolvable ↥(centralizer ({t} : Set ↥H)) := by
  let f : ↥(centralizer ({t} : Set ↥H)) →* ↥(centralizer ({(t : G)} : Set G)) :=
    { toFun := fun x => ⟨(x : ↥H), by
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(centralizer ({(t : G)} : Set G)) => (z : G))
    hxy))

theorem isSolvable_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G)
    (h : Group.IsSolvable ↥(centralizer ({g} : Set G))) :
    Group.IsSolvable ↥(centralizer ({e g} : Set H)) := by
  let f : ↥(centralizer ({e g} : Set H)) →* ↥(centralizer ({g} : Set G)) :=
    { toFun := fun x => ⟨e.symm (x : H), by
        rw [mem_centralizer_singleton_iff]
        have hx := mem_centralizer_singleton_iff.1 x.2
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hx⟩
      map_one' := Subtype.ext (map_one e.symm)
      map_mul' := fun x y => Subtype.ext (map_mul e.symm (x : H) (y : H)) }
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
  have h1 := congrArg Subtype.val hxy
  exact Subtype.ext (e.symm.injective h1)

theorem not_isSolvable_of_simple_card {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hp : ¬ (Nat.card X).Prime) : ¬ Group.IsSolvable X := by
  intro hsolv
  have hc : ∀ a b : X, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.2 hsolv
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  exact hp (IsSimpleGroup.prime_card (α := X))

end CFSG.EvenSporadicStandard.Induction.Hyp
