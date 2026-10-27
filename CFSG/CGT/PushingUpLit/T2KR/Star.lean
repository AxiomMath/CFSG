module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev Hc (D : Subgroup G) : Subgroup G := Subgroup.centralizer (D : Set G)

abbrev Dsub (D : Subgroup G) : Subgroup ↥(Hc D) := D.subgroupOf (Hc D)

theorem Dsub_normal (D : Subgroup G) : (Dsub D).Normal :=
  ⟨fun x hx g => by
    have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.1 hx
    have h1 : (x : G) * (g : G) = (g : G) * x := Subgroup.mem_centralizer_iff.1 g.2 (x : G) hxD
    rw [Subgroup.mem_subgroupOf]
    show (g : G) * x * (g : G)⁻¹ ∈ D
    have h2 : (g : G) * x * (g : G)⁻¹ = x := by
      calc (g : G) * x * (g : G)⁻¹ = ((x : G) * g) * (g : G)⁻¹ := by rw [← h1]
        _ = x := by group
    rw [h2]
    exact hxD⟩

instance (D : Subgroup G) : (Dsub D).Normal := Dsub_normal D

abbrev Ghat (D : Subgroup G) : Type := ↥(Hc D) ⧸ Dsub D

@[expose] def pi (D : Subgroup G) : ↥(Hc D) →* Ghat D := QuotientGroup.mk' (Dsub D)

theorem pi_surjective (D : Subgroup G) : Function.Surjective (pi D) :=
  QuotientGroup.mk'_surjective _

theorem pi_eq_pi_iff (D : Subgroup G) {x y : ↥(Hc D)} :
    pi D x = pi D y ↔ ((x : G))⁻¹ * y ∈ D := by
  show QuotientGroup.mk x = QuotientGroup.mk y ↔ _
  rw [QuotientGroup.eq]
  rfl

@[expose] def star (D X : Subgroup G) : Subgroup (Ghat D) := (X.subgroupOf (Hc D)).map (pi D)

variable {D X Y : Subgroup G}

theorem mem_star_iff (hDX : D ≤ X) (x : ↥(Hc D)) : pi D x ∈ star D X ↔ (x : G) ∈ X := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyX : (y : G) ∈ X := Subgroup.mem_subgroupOf.1 hy
    have h1 : ((y : G))⁻¹ * (x : G) ∈ D := (pi_eq_pi_iff D).1 hyx
    have : (x : G) = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [this]
    exact X.mul_mem hyX (hDX h1)
  · intro hx
    exact ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem star_mono (hXY : X ≤ Y) : star D X ≤ star D Y :=
  Subgroup.map_mono (fun _ hx => Subgroup.mem_subgroupOf.2 (hXY (Subgroup.mem_subgroupOf.1 hx)))

theorem star_le_iff (hDX : D ≤ X) (hDY : D ≤ Y) (hXH : X ≤ Hc D) :
    star D X ≤ star D Y ↔ X ≤ Y := by
  constructor
  · intro h x hx
    have := h ((mem_star_iff hDX ⟨x, hXH hx⟩).2 hx)
    exact (mem_star_iff hDY ⟨x, hXH hx⟩).1 this
  · exact star_mono

theorem star_inf (hDX : D ≤ X) (hDY : D ≤ Y) : star D (X ⊓ Y) = star D X ⊓ star D Y := by
  ext a
  obtain ⟨x, rfl⟩ := pi_surjective D a
  rw [Subgroup.mem_inf, mem_star_iff hDX, mem_star_iff hDY, mem_star_iff (le_inf hDX hDY)]
  exact Subgroup.mem_inf

theorem star_self : star D D = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨x, rfl⟩ := pi_surjective D a
  have hxD : (x : G) ∈ D := (mem_star_iff le_rfl x).1 ha
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).2 (Subgroup.mem_subgroupOf.2 hxD)

theorem conj_mem_Hc {h : G} (hh : h ∈ Hc D) {x : G} (hx : x ∈ Hc D) : h * x * h⁻¹ ∈ Hc D :=
  (Hc D).mul_mem ((Hc D).mul_mem hh hx) ((Hc D).inv_mem hh)

theorem D_le_conjSubgroup (hDX : D ≤ X) (h : ↥(Hc D)) : D ≤ conjSubgroup (h : G) X := by
  intro d hd
  rw [mem_conjSubgroup]
  have : (h : G)⁻¹ * d * h = d := by
    have := Subgroup.mem_centralizer_iff.1 h.2 d hd
    calc (h : G)⁻¹ * d * h = (h : G)⁻¹ * (d * h) := by group
      _ = (h : G)⁻¹ * (h * d) := by rw [← this]
      _ = d := by group
  rw [this]
  exact hDX hd

theorem star_conj (hDX : D ≤ X) (h : ↥(Hc D)) :
    conjSubgroup (pi D h) (star D X) = star D (conjSubgroup (h : G) X) := by
  have hDc : D ≤ conjSubgroup (h : G) X := D_le_conjSubgroup hDX h
  ext a
  obtain ⟨x, rfl⟩ := pi_surjective D a
  rw [mem_conjSubgroup, show (pi D h)⁻¹ * pi D x * pi D h = pi D (h⁻¹ * x * h) by
    rw [map_mul, map_mul, map_inv], mem_star_iff hDX, mem_star_iff hDc, mem_conjSubgroup]
  rfl

theorem mem_normalizer_star_iff (hDX : D ≤ X) (hXH : X ≤ Hc D) (h : ↥(Hc D)) :
    pi D h ∈ Subgroup.normalizer ((star D X : Subgroup (Ghat D)) : Set (Ghat D)) ↔
      (h : G) ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro H x
    by_cases hx : x ∈ Hc D
    · have := H (pi D ⟨x, hx⟩)
      rw [mem_star_iff hDX, show pi D h * pi D ⟨x, hx⟩ * (pi D h)⁻¹ =
        pi D (h * ⟨x, hx⟩ * h⁻¹) by rw [map_mul, map_mul, map_inv], mem_star_iff hDX] at this
      exact this
    · have hx' : (h : G) * x * (h : G)⁻¹ ∉ Hc D := fun hh => hx (by
        have := conj_mem_Hc ((Hc D).inv_mem h.2) hh
        simpa [mul_assoc] using this)
      exact ⟨fun hxX => (hx (hXH hxX)).elim, fun hxX => (hx' (hXH hxX)).elim⟩
  · intro H a
    obtain ⟨x, rfl⟩ := pi_surjective D a
    rw [mem_star_iff hDX, show pi D h * pi D x * (pi D h)⁻¹ = pi D (h * x * h⁻¹) by
      rw [map_mul, map_mul, map_inv], mem_star_iff hDX]
    exact H x

theorem card_star (hXH : X ≤ Hc D) : Nat.card (star D X) = D.relIndex X := by
  have hker : ((pi D).comp (X.subgroupOf (Hc D)).subtype).ker =
      (Dsub D).subgroupOf (X.subgroupOf (Hc D)) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show pi D (y : ↥(Hc D)) = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hrange : ((pi D).comp (X.subgroupOf (Hc D)).subtype).range = star D X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, ← Subgroup.index_ker, hker, ← Subgroup.relIndex]
  have := Subgroup.relIndex_subgroupOf (H := D) (K := X) (L := Hc D) hXH
  exact this

theorem isElemAbelian_star (hX : IsElemAbelian 2 X) : IsElemAbelian 2 (star D X) := by
  have hc : ∀ x y : G, x ∈ X → y ∈ X → x * y = y * x := fun x y hx hy => by
    have := hX.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    change (a : Ghat D) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ _ (Subgroup.mem_subgroupOf.1 ha') (Subgroup.mem_subgroupOf.1 hb'))
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow]
    have : (y : ↥(Hc D)) ^ 2 = 1 := Subtype.ext (hX.2 (y : G) (Subgroup.mem_subgroupOf.1 hy))
    rw [this, map_one]

theorem le_of_star_eq_bot (hDX : D ≤ X) (hXH : X ≤ Hc D) (h : star D X = ⊥) : X ≤ D := by
  intro x hx
  have h1 : pi D ⟨x, hXH hx⟩ ∈ star D X := (mem_star_iff hDX _).2 hx
  rw [h, Subgroup.mem_bot] at h1
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

end CFSG.CGT.PushingUpLit.T2KR
