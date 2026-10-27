module

public import CFSG.ClassicalInvolution.AschTight.E2StarTargets

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem comm_mem_symm {H : Subgroup G} {x y : G} (h : x * y * x⁻¹ * y⁻¹ ∈ H) :
    y * x * y⁻¹ * x⁻¹ ∈ H := by
  have e : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
  rw [e]
  exact H.inv_mem h

theorem comm_mem_of_left_mem {H : Subgroup G} {x y : G} (hx : x ∈ H)
    (hy : y ∈ Subgroup.normalizer (H : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ H := by
  have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [e]
  exact H.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hy _).mp (H.inv_mem hx))

theorem comm_mem_of_right_mem {H : Subgroup G} {x y : G} (hy : y ∈ H)
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ H :=
  comm_mem_symm (comm_mem_of_left_mem hy hx)

@[expose] def modCent (H N : Subgroup G) (hN : N ≤ Subgroup.normalizer (H : Set G))
    (s : Set G) : Subgroup G where
  carrier := {x | x ∈ N ∧ ∀ y ∈ s, x * y * x⁻¹ * y⁻¹ ∈ H}
  mul_mem' := by
    rintro x x' ⟨hx, hxs⟩ ⟨hx', hx's⟩
    refine ⟨N.mul_mem hx hx', fun y hy => ?_⟩
    have e : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact H.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN hx) _).mp (hx's y hy)) (hxs y hy)
  one_mem' := ⟨N.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hxs⟩
    refine ⟨N.inv_mem hx, fun y hy => ?_⟩
    have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hN (N.inv_mem hx)) _).mp (H.inv_mem (hxs y hy))

theorem mem_modCent_iff {H N : Subgroup G} {hN : N ≤ Subgroup.normalizer (H : Set G)} {s : Set G}
    {x : G} : x ∈ modCent H N hN s ↔ x ∈ N ∧ ∀ y ∈ s, x * y * x⁻¹ * y⁻¹ ∈ H :=
  Iff.rfl

theorem normalizer_le_normalizer_centralizer (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ m ∈ Subgroup.normalizer (W : Set G), ∀ y ∈ Subgroup.centralizer (W : Set G),
      m * y * m⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    intro m hm y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) w).mp hw
    have h1 : m⁻¹ * w * m⁻¹⁻¹ * y = y * (m⁻¹ * w * m⁻¹⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hy) _ hw'
    calc w * (m * y * m⁻¹) = m * ((m⁻¹ * w * m⁻¹⁻¹) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * w * m⁻¹⁻¹)) * m⁻¹ := by rw [h1]
      _ = m * y * m⁻¹ * w := by group
  refine ⟨key n hn x, fun hx => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

theorem normalizer_le_normalizer_OCW [Finite G] (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
  fun _ hn => mem_normalizer_oddCoreOf_of_mem_normalizer (normalizer_le_normalizer_centralizer W hn)

theorem mem_normalizer_sup {A B : Subgroup G} {n : G} (hA : n ∈ Subgroup.normalizer (A : Set G))
    (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hA hB ⊢
  rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hA, hB]

theorem normalizer_le_normalizer_sup_OCW [Finite G] (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) :=
  fun _ hn => mem_normalizer_sup hn (normalizer_le_normalizer_OCW W hn)

theorem OCW_le_normalizer (W : Subgroup G) : OCW W ≤ Subgroup.normalizer (W : Set G) :=
  (oddCoreOf_le_self _).trans (Subgroup.centralizer_le_normalizer (W : Set G))

variable [Finite G]

theorem forall_comm_mem_of_generators {Ω : Set (Subgroup G)} {W : Subgroup G}
    (hcomm : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T,
      r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W) :
    ∀ x ∈ MGrp Ω W ⊔ OCW W, ∀ y ∈ MGrp Ω W ⊔ OCW W, x * y * x⁻¹ * y⁻¹ ∈ W ⊔ OCW W := by
  have hNW := normalizer_le_normalizer_sup_OCW W
  have hDN : ∀ R ∈ DSet Ω W, R ≤ Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) :=
    fun R hR => hR.2.trans hNW
  have hXN := (OCW_le_normalizer W).trans hNW
  have hXH : OCW W ≤ W ⊔ OCW W := le_sup_right
  have hMN : MGrp Ω W ⊔ OCW W ≤ Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) :=
    sup_le (iSup₂_le hDN) hXN
  have stepA : ∀ T ∈ DSet Ω W, MGrp Ω W ⊔ OCW W ≤ modCent (W ⊔ OCW W) _ le_rfl (T : Set G) := by
    intro T hT
    refine sup_le (iSup₂_le fun R hR r hr => ⟨hDN R hR hr, fun t ht => hcomm R hR T hT r hr t ht⟩)
      fun x hx => ⟨hXN hx, fun t ht => comm_mem_of_left_mem (hXH hx) (hDN T hT ht)⟩
  have stepB : MGrp Ω W ⊔ OCW W ≤
      modCent (W ⊔ OCW W) _ le_rfl ((MGrp Ω W ⊔ OCW W : Subgroup G) : Set G) := by
    refine sup_le (iSup₂_le fun R hR r hr => ⟨hDN R hR hr, fun y hy => ?_⟩)
      fun x hx => ⟨hXN hx, fun y hy => comm_mem_of_left_mem (hXH hx) (hMN hy)⟩
    exact comm_mem_symm ((stepA R hR hy).2 r hr)
  exact fun x hx y hy => (stepB hx).2 y hy

omit [Finite G] in
theorem isMulCommutative_muGroup {Ω : Set (Subgroup G)} {W : Subgroup G}
    (h : ∀ x ∈ MGrp Ω W ⊔ OCW W, ∀ y ∈ MGrp Ω W ⊔ OCW W, x * y * x⁻¹ * y⁻¹ ∈ W ⊔ OCW W) :
    IsMulCommutative ↥(muGroup Ω W) := by
  refine IsMulCommutative.of_comm fun a b => ?_
  have ha : (a : NQuot (W ⊔ OCW W)) ∈ muImage (MGrp Ω W) W := a.2
  have hb : (b : NQuot (W ⊔ OCW W)) ∈ muImage (MGrp Ω W) W := b.2
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hb
  have e1 : ∀ u v : ↥(Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G)),
      ((QuotientGroup.mk' ((W ⊔ OCW W).subgroupOf _) u : NQuot (W ⊔ OCW W)) *
        QuotientGroup.mk' ((W ⊔ OCW W).subgroupOf _) v) =
      QuotientGroup.mk' ((W ⊔ OCW W).subgroupOf _) (u * v) := fun _ _ => rfl
  have e2 : (QuotientGroup.mk' ((W ⊔ OCW W).subgroupOf _) (x * y) : NQuot (W ⊔ OCW W)) =
      QuotientGroup.mk' ((W ⊔ OCW W).subgroupOf _) (y * x) := by
    refine (QuotientGroup.eq (s := (W ⊔ OCW W).subgroupOf _)).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ MGrp Ω W ⊔ OCW W := Subgroup.mem_subgroupOf.mp hx
    have hy' : (y : G) ∈ MGrp Ω W ⊔ OCW W := Subgroup.mem_subgroupOf.mp hy
    have := h _ ((MGrp Ω W ⊔ OCW W).inv_mem hy') _ ((MGrp Ω W ⊔ OCW W).inv_mem hx')
    simpa [mul_assoc] using this
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb]
  exact (e1 x y).trans (e2.trans (e1 y x).symm)

omit [Finite G] in
theorem commutator_mem_of_relIndex_two {A R : Subgroup G} (h2 : A.relIndex R = 2) {r t : G}
    (hr : r ∈ R) (ht : t ∈ R) : r * t * r⁻¹ * t⁻¹ ∈ A := by
  have hidx : (A.subgroupOf R).index = 2 := h2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨r, hr⟩ : ↥R) * ⟨t, ht⟩)
    (b := (⟨r, hr⟩ : ↥R)⁻¹ * (⟨t, ht⟩ : ↥R)⁻¹)
  have h1 := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨r, hr⟩ : ↥R)) (b := ⟨t, ht⟩)
  have h3 := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨r, hr⟩ : ↥R)⁻¹)
    (b := (⟨t, ht⟩ : ↥R)⁻¹)
  rw [inv_mem_iff, inv_mem_iff] at h3
  have hmem : (⟨r, hr⟩ : ↥R) * ⟨t, ht⟩ * ((⟨r, hr⟩ : ↥R)⁻¹ * (⟨t, ht⟩ : ↥R)⁻¹) ∈
      A.subgroupOf R := by
    rw [key, h1, h3]
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa [mul_assoc] using this

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
