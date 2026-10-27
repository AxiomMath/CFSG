module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverStd

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.PerfectAutomorphisms Cover
open scoped commutatorElement

section Char

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

omit [Finite H] in
theorem perfect_le_of_quotient (hu : u ∈ L)
    (hmax : ∀ P : Subgroup (↥L ⧸ center ↥L),
      P ≤ centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)) → Group.IsPerfect ↥P →
        P ≤ (K.subgroupOf L).map (q ↥L)) :
    ∀ P : Subgroup H, P ≤ L ⊓ centralizer ({u} : Set H) → Group.IsPerfect ↥P → P ≤ K := by
  intro P hP hPperf
  have hPL : P ≤ L := fun x hx => (hP hx).1
  have hP1 : Group.IsPerfect ↥(P.subgroupOf L) := isPerfect_subgroupOf_of_le hPL hPperf
  have hP1' : ⁅P.subgroupOf L, P.subgroupOf L⁆ = P.subgroupOf L := isPerfect_iff.mp hP1
  have hPq : (P.subgroupOf L).map (q ↥L) ≤
      centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hP (Subgroup.mem_subgroupOf.1 hx)).2)
  have hPqperf : Group.IsPerfect ↥((P.subgroupOf L).map (q ↥L)) := by
    have := hP1
    exact Group.IsPerfect.map _
  have h1 := hmax _ hPq hPqperf
  have h2 : P.subgroupOf L ≤ (K.subgroupOf L) ⊔ center ↥L := by
    rw [← comap_map_q]
    exact fun x hx => h1 ⟨x, hx, rfl⟩
  have h3 := le_of_perfect_of_le_sup_center hP1' h2
  intro x hx
  have hx' : (⟨x, hPL hx⟩ : ↥L) ∈ P.subgroupOf L := hx
  exact Subgroup.mem_subgroupOf.1 (h3 hx')

omit [Finite H] in
theorem characteristic_of_perfect_le (hKX : K ≤ L ⊓ centralizer ({u} : Set H))
    (hKperf : Group.IsPerfect ↥K)
    (hmax : ∀ P : Subgroup H, P ≤ L ⊓ centralizer ({u} : Set H) → Group.IsPerfect ↥P → P ≤ K) :
    (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  set C : Subgroup H := L ⊓ centralizer ({u} : Set H) with hC
  intro φ
  have hperfC : Group.IsPerfect (K.subgroupOf C) := isPerfect_subgroupOf_of_le hKX hKperf
  set K₂ : Subgroup H := ((K.subgroupOf C).map φ.toMonoidHom).map C.subtype with hK₂
  have hK₂C : K₂ ≤ C := fun x hx => by
    obtain ⟨z, -, rfl⟩ := hx
    exact z.2
  have hK₂perf : Group.IsPerfect ↥K₂ := by
    have := hperfC
    have h1 : Group.IsPerfect ((K.subgroupOf C).map φ.toMonoidHom) := Group.IsPerfect.map _
    have := h1
    exact Group.IsPerfect.map _
  have hle := hmax K₂ hK₂C hK₂perf
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hmem : ((φ.toMonoidHom y : C) : H) ∈ K₂ := ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact hle hmem

end Char

section AutLift

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H}

omit [Finite H] in
theorem map_autCentralizer_le_autFixing :
    (autCentralizer L K).map (centerQuotientHom ↥L) ≤ autFixing ((K.subgroupOf L).map (q ↥L)) := by
  rintro _ ⟨α, hα, rfl⟩ y ⟨k, hk, rfl⟩
  show (centerQuotientHom ↥L α) (q ↥L k) = q ↥L k
  have h1 := onCenterQuotient_apply_mk α k
  have h2 : α k = k := hα k (Subgroup.mem_subgroupOf.1 hk)
  change onCenterQuotient α (q ↥L k) = q ↥L k
  rw [h1, h2]

noncomputable def autCentralizerToFixing :
    ↥(autCentralizer L K) →* ↥(autFixing ((K.subgroupOf L).map (q ↥L))) :=
  ((centerQuotientHom ↥L).comp (autCentralizer L K).subtype).codRestrict
    (autFixing ((K.subgroupOf L).map (q ↥L)))
    (fun α => map_autCentralizer_le_autFixing ⟨α, α.2, rfl⟩)

omit [Finite H] in
theorem autCentralizerToFixing_injective (hLperf : Group.IsPerfect ↥L) :
    Function.Injective (autCentralizerToFixing (L := L) (K := K)) := by
  have := hLperf
  exact fun a b h => Subtype.ext (centerQuotientHom_injective ↥L (congrArg Subtype.val h))

omit [Finite H] in
theorem autCentralizer_solvable_of_quotient (hLperf : Group.IsPerfect ↥L)
    (hY : Group.IsSolvable ↥(autFixing ((K.subgroupOf L).map (q ↥L)))) :
    Group.IsSolvable ↥(autCentralizer L K) :=
  Group.isSolvable_of_isSolvable_injective (autCentralizerToFixing_injective hLperf)

omit [Finite H] in
theorem autCentralizer_inner_of_quotient (hLperf : Group.IsPerfect ↥L)
    (hY : ∀ β ∈ autFixing ((K.subgroupOf L).map (q ↥L)), ∃ y : ↥L ⧸ center ↥L,
      β = MulAut.conj y) :
    ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g := by
  have := hLperf
  intro α hα
  obtain ⟨y, hy⟩ := hY _ (map_autCentralizer_le_autFixing ⟨α, hα, rfl⟩)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨g, centerQuotientHom_injective ↥L ?_⟩
  rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
  exact hy

end AutLift

section Comm

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} {u : H}

omit [Finite H] in
theorem mem_commutator_of_quotient (hodd : Odd (Nat.card (center ↥L))) (hu : u ∈ L)
    (hu2 : orderOf u = 2)
    (h : q ↥L ⟨u, hu⟩ ∈ ⁅centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)),
      centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))⁆) :
    u ∈ ⁅L ⊓ centralizer ({u} : Set H), L ⊓ centralizer ({u} : Set H)⁆ := by
  have hsq : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf hu2)
  set X₁ : Subgroup ↥L := centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) with hX₁
  have h2 : X₁ = (centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))).comap (q ↥L) := by
    ext x
    exact mem_centralizer_singleton_iff_mk hodd hsq
  have hmap : X₁.map (q ↥L) = centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)) := by
    rw [h2]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  rw [← hmap, ← Subgroup.map_commutator] at h
  obtain ⟨c, hc, hcq⟩ := h
  obtain ⟨j, hj⟩ := hodd
  set r := Nat.card (center ↥L) with hr
  have hc2 : c * c ∈ center ↥L := by
    rw [← q_eq_one_iff, map_mul, hcq, ← map_mul, hsq, map_one]
  have hz : (c * c) ^ r = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨c * c, hc2⟩)
    exact congrArg Subtype.val this
  have hcr2 : c ^ r * c ^ r = 1 := by
    calc c ^ r * c ^ r = (c * c) ^ r := by rw [(Commute.refl c).mul_pow]
      _ = 1 := hz
  have hcrq : q ↥L (c ^ r) = q ↥L ⟨u, hu⟩ := by
    rw [map_pow, hcq, hj, pow_succ, pow_mul, sq, ← map_mul, hsq, map_one, one_pow, one_mul]
  have hcr : c ^ r = ⟨u, hu⟩ := Closing.eq_of_mk_eq_of_sq ⟨j, hj⟩ hcr2 hsq hcrq
  have hmem : (⟨u, hu⟩ : ↥L) ∈ ⁅X₁, X₁⁆ := by
    rw [← hcr]
    exact Subgroup.pow_mem _ hc r
  have hX : X₁.map L.subtype = L ⊓ centralizer ({u} : Set H) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val
        (mem_centralizer_singleton_iff.1 hy))⟩
    · rintro ⟨hxL, hxc⟩
      exact ⟨⟨x, hxL⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 hxc)), rfl⟩
  rw [← hX, ← Subgroup.map_commutator]
  exact ⟨_, hmem, rfl⟩

end Comm

end CFSG.EvenSporadicStandard.Induction
