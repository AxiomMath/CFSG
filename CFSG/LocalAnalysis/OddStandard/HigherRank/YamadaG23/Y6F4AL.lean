module

public import CFSG.Open.Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open scoped commutatorElement

private lemma center_eq_bot_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) : Subgroup.center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hna

private lemma commutatorElement_mul_central {G : Type*} [Group G] {k k' z z' : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) :
    ⁅k * z, k' * z'⁆ = ⁅k, k'⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hz1 : ⁅z, k' * z'⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      Commute.commutator_eq (Subgroup.mem_center_iff.mp hz k').symm,
      Commute.commutator_eq (Subgroup.mem_center_iff.mp hz z').symm]
    group
  have hk1 : ⁅k, k' * z'⁆ = ⁅k, k'⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      Commute.commutator_eq (Subgroup.mem_center_iff.mp hz' k)]
    group
  rw [hz1, hk1]
  group

private lemma commutator_sup_central_le {G : Type*} [Group G] {K Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨k', hk', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  rw [commutatorElement_mul_central (hZ hz) (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

private lemma commutator_sup_central_eq {G : Type*} [Group G] {K Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅K ⊔ Z, K ⊔ Z⁆ = ⁅K, K⁆ :=
  le_antisymm (commutator_sup_central_le hZ)
    (Subgroup.commutator_mono le_sup_left le_sup_left)

private lemma isPerfect_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hna : ¬ IsMulCommutative G) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup G), ⊤⁆) with h | h
  · exact absurd ((commutator_eq_bot_iff G).mp h) hna
  · exact h

theorem y6f4a_isQuasisimple_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hna : ¬ IsMulCommutative X) : CFSG.Open.IsQuasisimple X := by
  refine ⟨(isPerfect_of_simple hs hna).commutator_eq_top, ?_⟩
  have hc : Subgroup.center X = ⊥ := center_eq_bot_of_simple hs hna
  have e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mpr hs

private lemma commutator_eq_self_of_simple_subgroup {G : Type*} [Group G] (H : Subgroup G)
    (hs : IsSimpleGroup ↥H) (hna : ¬ IsMulCommutative ↥H) : ⁅H, H⁆ = H :=
  Subgroup.isPerfect_iff.mp (isPerfect_of_simple hs hna)

variable {C Y : Type} [Group C] [Group Y] {π : C →* Y} {E : Subgroup Y}

private lemma y6f4a_lift_map_aux (hπ : Function.Surjective π) (hE : IsSimpleGroup ↥E)
    (hna : ¬ IsMulCommutative ↥E) : ⁅E.comap π, E.comap π⁆.map π = E := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ E]
  exact commutator_eq_self_of_simple_subgroup E hE hna

private lemma y6f4a_comap_eq_sup (hπ : Function.Surjective π) (hE : IsSimpleGroup ↥E)
    (hna : ¬ IsMulCommutative ↥E) :
    E.comap π = ⁅E.comap π, E.comap π⁆ ⊔ π.ker := by
  have hmap := y6f4a_lift_map_aux hπ hE hna
  apply le_antisymm
  · intro r hr
    have hrE : π r ∈ E := Subgroup.mem_comap.mp hr
    have hrK : π r ∈ (⁅E.comap π, E.comap π⁆ : Subgroup C).map π := by
      rw [hmap]; exact hrE
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hrK
    refine Subgroup.mem_sup_of_normal_right.mpr ⟨k, hk, k⁻¹ * r, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkπ]
    group
  · refine sup_le (Subgroup.commutator_le_self _) ?_
    intro r hr
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hr]
    exact E.one_mem

private lemma y6f4a_isPerfect_commutator_comap (hπ : Function.Surjective π)
    (hker : π.ker ≤ center C) (hE : IsSimpleGroup ↥E) (hna : ¬ IsMulCommutative ↥E) :
    (⁅⁅E.comap π, E.comap π⁆, ⁅E.comap π, E.comap π⁆⁆ : Subgroup C) =
      ⁅E.comap π, E.comap π⁆ := by
  have hmem : E.comap π = ⁅E.comap π, E.comap π⁆ ⊔ π.ker := y6f4a_comap_eq_sup hπ hE hna
  refine le_antisymm (Subgroup.commutator_le_self _) (le_of_eq ?_)
  calc ⁅E.comap π, E.comap π⁆
      = ⁅⁅E.comap π, E.comap π⁆ ⊔ π.ker, ⁅E.comap π, E.comap π⁆ ⊔ π.ker⁆ := by
        rw [← hmem]
    _ = ⁅⁅E.comap π, E.comap π⁆, ⁅E.comap π, E.comap π⁆⁆ :=
        commutator_sup_central_eq hker

private lemma y6f4a_ker_subgroupOf_eq_center (hπ : Function.Surjective π)
    (hker : π.ker ≤ center C) (hE : IsSimpleGroup ↥E) (hna : ¬ IsMulCommutative ↥E) :
    (π.ker).subgroupOf (⁅E.comap π, E.comap π⁆ : Subgroup C) =
      center ↥(⁅E.comap π, E.comap π⁆ : Subgroup C) := by
  have hmap := y6f4a_lift_map_aux hπ hE hna
  have hcb : Subgroup.center ↥E = ⊥ := center_eq_bot_of_simple hE hna
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker (Subgroup.mem_subgroupOf.mp hz)) (w : C)
  · intro z hz
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hzR : (z : C) ∈ E.comap π :=
      Subgroup.commutator_le_self (E.comap π) z.2
    have hzE : π (z : C) ∈ E := Subgroup.mem_comap.mp hzR
    have hcent : (⟨π (z : C), hzE⟩ : ↥E) ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro e
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact e.2)
      apply Subtype.ext
      have hcomm : k * (z : C) = (z : C) * k :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
      calc (e : Y) * π (z : C) = π k * π (z : C) := by rw [← hkπ]
        _ = π (k * (z : C)) := (map_mul π k (z : C)).symm
        _ = π ((z : C) * k) := by rw [hcomm]
        _ = π (z : C) * π k := map_mul π (z : C) k
        _ = π (z : C) * (e : Y) := by rw [← hkπ]
    rw [hcb, Subgroup.mem_bot] at hcent
    simpa using Subtype.ext_iff.mp hcent

private noncomputable def y6f4a_lift_equiv_aux (hπ : Function.Surjective π)
    (hker : π.ker ≤ center C) (hE : IsSimpleGroup ↥E) (hna : ¬ IsMulCommutative ↥E) :
    ↥(⁅E.comap π, E.comap π⁆ : Subgroup C) ⧸
        center ↥(⁅E.comap π, E.comap π⁆ : Subgroup C) ≃* ↥E := by
  let K : Subgroup C := ⁅E.comap π, E.comap π⁆
  have hmap : K.map π = E := y6f4a_lift_map_aux hπ hE hna
  let φ : ↥K →* ↥E := (π.comp K.subtype).codRestrict E fun k =>
    Subgroup.mem_comap.mp (Subgroup.commutator_le_self (E.comap π) k.2)
  have hφsurj : Function.Surjective φ := by
    intro e
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact e.2)
    exact ⟨⟨k, hk⟩, Subtype.ext hkπ⟩
  have hkerφ : φ.ker = (π.ker).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : π (x : C) = 1 := congrArg Subtype.val hx
      exact MonoidHom.mem_ker.mpr hx'
    · intro hx
      exact Subtype.ext (MonoidHom.mem_ker.mp hx)
  have hcenter : (π.ker).subgroupOf K = center ↥K :=
    y6f4a_ker_subgroupOf_eq_center hπ hker hE hna
  exact (QuotientGroup.quotientMulEquivOfEq (hkerφ.trans hcenter).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)

theorem y6f4a_lift_quasisimple (hπ : Function.Surjective π) (hker : π.ker ≤ center C)
    (hE : IsSimpleGroup ↥E) (hna : ¬ IsMulCommutative ↥E) :
    CFSG.Open.IsQuasisimple ↥⁅E.comap π, E.comap π⁆ := by
  have hperfect := y6f4a_isPerfect_commutator_comap hπ hker hE hna
  haveI : Group.IsPerfect ↥(⁅E.comap π, E.comap π⁆ : Subgroup C) :=
    Subgroup.isPerfect_iff.mpr hperfect
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  exact (MulEquiv.isSimpleGroup_congr (y6f4a_lift_equiv_aux hπ hker hE hna)).mpr hE

theorem y6f4a_lift_normal (hπ : Function.Surjective π) (hE : E.Normal) :
    (⁅E.comap π, E.comap π⁆ : Subgroup C).Normal := by
  haveI : (E.comap π).Normal := hE.comap π
  infer_instance

theorem y6f4a_lift_equiv (hπ : Function.Surjective π) (hker : π.ker ≤ center C)
    (hE : IsSimpleGroup ↥E) (hna : ¬ IsMulCommutative ↥E) :
    Nonempty (↥⁅E.comap π, E.comap π⁆ ⧸ center ↥⁅E.comap π, E.comap π⁆ ≃* ↥E) :=
  ⟨y6f4a_lift_equiv_aux hπ hker hE hna⟩

theorem y6f4a_lift_centralizer (hπ : Function.Surjective π) (hker : π.ker ≤ center C)
    (hE : IsSimpleGroup ↥E) (hna : ¬ IsMulCommutative ↥E)
    (hCE : centralizer (E : Set Y) = ⊥) :
    centralizer ((⁅E.comap π, E.comap π⁆ : Subgroup C) : Set C) = π.ker := by
  have hmap := y6f4a_lift_map_aux hπ hE hna
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hxE : π x ∈ centralizer (E : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact he)
      have hcomm : k * x = x * k := Subgroup.mem_centralizer_iff.mp hx k hk
      calc (e : Y) * π x = π k * π x := by rw [← hkπ]
        _ = π (k * x) := (map_mul π k x).symm
        _ = π (x * k) := by rw [hcomm]
        _ = π x * π k := map_mul π x k
        _ = π x * (e : Y) := by rw [← hkπ]
    rw [hCE, Subgroup.mem_bot] at hxE
    exact hxE
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_center_iff.mp (hker hx) k

theorem y6f4a_lift_perfect (hperf : ∀ B : Subgroup Y, Group.IsPerfect ↥B → B ≤ E)
    {B : Subgroup C} (hB : Group.IsPerfect ↥B) : B ≤ ⁅E.comap π, E.comap π⁆ := by
  haveI : Group.IsPerfect ↥B := hB
  have hBmap : B.map π ≤ E := hperf (B.map π) (Group.IsPerfect.map (H := B) π)
  have hBR : B ≤ E.comap π := Subgroup.map_le_iff_le_comap.mp hBmap
  calc B = ⁅B, B⁆ := (Subgroup.isPerfect_iff.mp hB).symm
    _ ≤ ⁅E.comap π, E.comap π⁆ := Subgroup.commutator_mono hBR hBR

end CFSG.OddStandard.HigherRank.YamadaG23
