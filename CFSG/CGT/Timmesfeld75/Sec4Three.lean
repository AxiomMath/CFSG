module

public import CFSG.CGT.Timmesfeld75.Sec4Two

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Abstract

theorem range_eq_top_of_card_center_quotient_le {H K : Type*} [Group H] [Group K] [Finite H]
    [Finite K] (j : H →* K) (hj : Function.Injective j)
    (hcl : Subgroup.normalClosure (j.range : Set K) = ⊤)
    (hcard : Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card (H ⧸ Subgroup.center H)) :
    j.range = ⊤ := by
  let κ : H →* K ⧸ Subgroup.center K := (QuotientGroup.mk' (Subgroup.center K)).comp j
  have hker : κ.ker ≤ Subgroup.center H := by
    intro y hy
    have hyK : j y ∈ Subgroup.center K := (QuotientGroup.eq_one_iff (j y)).1 hy
    rw [Subgroup.mem_center_iff]
    intro h'
    apply hj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hyK (j h')
  have h1 := Subgroup.card_ker_mul_card_range κ
  have h2 := Subgroup.card_mul_index (Subgroup.center H)
  have h3 : Nat.card κ.ker ≤ Nat.card (Subgroup.center H) := Subgroup.card_le_of_le hker
  have hpos : 0 < Nat.card (Subgroup.center H) := Nat.card_pos
  have h4 : Nat.card (H ⧸ Subgroup.center H) ≤ Nat.card κ.range := by
    by_contra hlt
    rw [not_le] at hlt
    have : Nat.card κ.ker * Nat.card κ.range < Nat.card (Subgroup.center H) *
        Nat.card (H ⧸ Subgroup.center H) :=
      calc Nat.card κ.ker * Nat.card κ.range ≤ Nat.card (Subgroup.center H) * Nat.card κ.range :=
          Nat.mul_le_mul_right _ h3
        _ < Nat.card (Subgroup.center H) * Nat.card (H ⧸ Subgroup.center H) :=
          Nat.mul_lt_mul_of_pos_left hlt hpos
    rw [h1] at this
    have h2' : Nat.card (Subgroup.center H) * Nat.card (H ⧸ Subgroup.center H) = Nat.card H := by
      simpa [Subgroup.index] using h2
    omega
  have hrange : κ.range = ⊤ := Subgroup.eq_top_of_le_card _ (hcard.trans h4)
  have hnormal : (j.range).Normal := by
    refine ⟨fun y hy k => ?_⟩
    obtain ⟨y', rfl⟩ := hy
    obtain ⟨x, hx⟩ : ∃ x : H, κ x = QuotientGroup.mk k := by
      have : (QuotientGroup.mk k : K ⧸ Subgroup.center K) ∈ κ.range := by rw [hrange]; trivial
      exact this
    obtain ⟨z, hzdef⟩ : ∃ z : K, z = (j x)⁻¹ * k := ⟨_, rfl⟩
    have hz : z ∈ Subgroup.center K := hzdef ▸ QuotientGroup.eq.1 hx
    have hk : k = j x * z := by rw [hzdef]; group
    have hc := Subgroup.mem_center_iff.1 hz (j y')
    refine ⟨x * y' * x⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hk]
    have e1 : j x * z * j y' * (j x * z)⁻¹ = j x * (z * j y' * z⁻¹) * (j x)⁻¹ := by group
    have e2 : z * j y' * z⁻¹ = j y' := by rw [← hc]; group
    rw [e1, e2]
  have hle := Subgroup.normalClosure_le_normal (N := j.range) (s := (j.range : Set K))
    (fun x hx => hx)
  rw [hcl] at hle
  exact eq_top_iff.2 hle

end Abstract

section Z

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

@[expose] def sec4Z (T T₁ T₂ : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G), ∃ t ∈ T,
    x = g * t * g⁻¹}

omit [Finite G] in
theorem conj_le_sec4Z {g : G} (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) :
    conjSubgroup g T ≤ sec4Z T T₁ T₂ := by
  rintro _ ⟨t, ht, rfl⟩
  exact Subgroup.subset_closure ⟨g, hg, t, ht, rfl⟩

omit [Finite G] in
theorem left_le_sec4Z : T ≤ sec4Z T T₁ T₂ := fun t ht =>
  Subgroup.subset_closure ⟨1, Subgroup.one_mem _, t, ht, by group⟩

omit [Finite G] in
theorem sec4Z_conj_mem {g x : G} (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hx : x ∈ sec4Z T T₁ T₂) : g * x * g⁻¹ ∈ sec4Z T T₁ T₂ := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ sec4Z T T₁ T₂) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, hk, t, ht, rfl⟩
    refine Subgroup.subset_closure ⟨g * k, (Subgroup.normalizer _).mul_mem hg hk, t, ht, ?_⟩
    group
  · simp
  · intro a b _ _ ha hb
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem Sec4Hyp.sec4Z_le_normalizer (h : Sec4Hyp T T₁ a T₂) :
    sec4Z T T₁ T₂ ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := by
  rw [sec4Z, Subgroup.closure_le]
  rintro _ ⟨g, hg, t, ht, rfl⟩
  exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hg
    (h.sec4Y_le_normalizer (left_le_sec4Y ht))) ((Subgroup.normalizer _).inv_mem hg)

theorem Sec4Hyp.sec4Y_le_sec4Z (h : Sec4Hyp T T₁ a T₂) : sec4Y T T₁ T₂ ≤ sec4Z T T₁ T₂ := by
  refine sup_le (sup_le left_le_sec4Z ?_) ?_
  · obtain ⟨x, hx, hx'⟩ := h.exists_mem_sec4Y_conj₁
    intro u hu
    rw [hx'] at hu
    exact conj_le_sec4Z (h.sec4Y_le_normalizer hx) hu
  · obtain ⟨x, hx, hx'⟩ := h.exists_mem_sec4Y_conj₂
    intro u hu
    rw [hx'] at hu
    exact conj_le_sec4Z (h.sec4Y_le_normalizer hx) hu

theorem Sec4Hyp.normalClosure_sec4Z (h : Sec4Hyp T T₁ a T₂) :
    Subgroup.normalClosure
      ((T.subgroupOf (sec4Z T T₁ T₂) : Subgroup ↥(sec4Z T T₁ T₂)) : Set ↥(sec4Z T T₁ T₂)) =
        ⊤ := by
  set NC := Subgroup.normalClosure
    ((T.subgroupOf (sec4Z T T₁ T₂) : Subgroup ↥(sec4Z T T₁ T₂)) : Set ↥(sec4Z T T₁ T₂))
    with hNC
  have hZle : sec4Z T T₁ T₂ ≤ NC.map (sec4Z T T₁ T₂).subtype := by
    refine (Subgroup.closure_le (NC.map (sec4Z T T₁ T₂).subtype)).2 ?_
    rintro _ ⟨g, hg, t, ht, rfl⟩
    have hgZ : g * t * g⁻¹ ∈ sec4Z T T₁ T₂ := Subgroup.subset_closure ⟨g, hg, t, ht, rfl⟩
    obtain ⟨z, hz, hzg⟩ := exists_mem_conj_eq_of_le h.pair.wc
      (left_le_sec4Z : T ≤ sec4Z T T₁ T₂) (g := g) (conj_le_sec4Z hg)
    have hxz : g * t * g⁻¹ ∈ conjSubgroup z T := by
      rw [← hzg]
      exact conj_mem_conjSubgroup g ht
    have ht' : z⁻¹ * (g * t * g⁻¹) * z ∈ T := mem_conjSubgroup.1 hxz
    refine ⟨⟨g * t * g⁻¹, hgZ⟩, ?_, rfl⟩
    have hmem : (⟨z, hz⟩ : ↥(sec4Z T T₁ T₂)) * ⟨z⁻¹ * (g * t * g⁻¹) * z,
        (sec4Z T T₁ T₂).mul_mem ((sec4Z T T₁ T₂).mul_mem ((sec4Z T T₁ T₂).inv_mem hz) hgZ) hz⟩ *
          (⟨z, hz⟩ : ↥(sec4Z T T₁ T₂))⁻¹ ∈ NC :=
      (Subgroup.normalClosure_normal (s := ((T.subgroupOf (sec4Z T T₁ T₂) :
        Subgroup ↥(sec4Z T T₁ T₂)) : Set ↥(sec4Z T T₁ T₂)))).conj_mem _
          (Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ht')) _
    have e : (⟨z, hz⟩ : ↥(sec4Z T T₁ T₂)) * ⟨z⁻¹ * (g * t * g⁻¹) * z,
        (sec4Z T T₁ T₂).mul_mem ((sec4Z T T₁ T₂).mul_mem ((sec4Z T T₁ T₂).inv_mem hz) hgZ) hz⟩ *
          (⟨z, hz⟩ : ↥(sec4Z T T₁ T₂))⁻¹ = ⟨g * t * g⁻¹, hgZ⟩ := by
      apply Subtype.ext
      show z * (z⁻¹ * (g * t * g⁻¹) * z) * z⁻¹ = g * t * g⁻¹
      group
    rwa [e] at hmem
  rw [eq_top_iff]
  intro w _
  obtain ⟨w', hw', hww'⟩ := hZle w.2
  have : w' = w := Subtype.ext hww'
  rwa [← this]

theorem Sec4Hyp.sec4_three
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    ((sec4Y T T₁ T₂).subgroupOf (Subgroup.normalizer (sec4N T T₁ T₂ : Set G))).Normal := by
  have hYZ := h.sec4Y_le_sec4Z
  have hZN := h.sec4Z_le_normalizer
  obtain ⟨f₁, hf₁, hc₁, hN₁, ⟨e₁⟩⟩ :=
    h.sec4_two_of_le hAsc hq le_rfl h.sec4Y_le_normalizer h.normalClosure_sec4Y
  obtain ⟨f₂, hf₂, hc₂, hN₂, ⟨e₂⟩⟩ :=
    h.sec4_two_of_le hAsc hq hYZ hZN h.normalClosure_sec4Z
  have hf : f₁ = f₂ := by
    have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
    have : 2 ^ f₁ = 2 ^ f₂ := Nat.eq_of_mul_eq_mul_left hLpos (hc₁.symm.trans hc₂)
    exact Nat.pow_right_injective (le_refl 2) this
  subst hf
  have := hN₁
  have := hN₂
  let j : (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) →*
      (↥(sec4Z T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Z T T₁ T₂)) :=
    QuotientGroup.map _ _ (Subgroup.inclusion hYZ) (by
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx))
  have hjinj : Function.Injective j := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : (y' : G) ∈ sec4N T T₁ T₂ :=
      (mk_eq_one_iff_mem (Subgroup.inclusion hYZ y')).1 hy
    exact (mk_eq_one_iff_mem y').2 h1
  have hcl : Subgroup.normalClosure (j.range : Set
      (↥(sec4Z T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Z T T₁ T₂))) = ⊤ := by
    have h1 := normalClosure_img_eq_top (K := sec4Z T T₁ T₂) (N := sec4N T T₁ T₂) (T := T)
      h.normalClosure_sec4Z
    rw [eq_top_iff, ← h1]
    refine Subgroup.normalClosure_mono ?_
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨QuotientGroup.mk ⟨(u : G), left_le_sec4Y (Subgroup.mem_subgroupOf.1 hu)⟩, rfl⟩
  have hcard : Nat.card ((↥(sec4Z T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Z T T₁ T₂)) ⧸
        Subgroup.center (↥(sec4Z T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Z T T₁ T₂))) ≤
      Nat.card ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
        Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) := by
    rw [Nat.card_congr e₂.toEquiv, Nat.card_congr e₁.toEquiv]
  have hrange := range_eq_top_of_card_center_quotient_le j hjinj hcl hcard
  have hZY : sec4Z T T₁ T₂ ≤ sec4Y T T₁ T₂ := by
    intro z hz
    have hmem : QuotientGroup.mk (⟨z, hz⟩ : ↥(sec4Z T T₁ T₂)) ∈ j.range := by
      rw [hrange]
      trivial
    obtain ⟨yb, hyb⟩ := hmem
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
    have h1 := QuotientGroup.eq.1 hyb
    have h2 : (y : G)⁻¹ * z ∈ sec4N T T₁ T₂ := Subgroup.mem_subgroupOf.1 h1
    have e : z = y * ((y : G)⁻¹ * z) := by group
    rw [e]
    exact (sec4Y T T₁ T₂).mul_mem y.2 (sec4N_le_sec4Y h2)
  refine ⟨fun y hy g => ?_⟩
  have hyY : (y : G) ∈ sec4Y T T₁ T₂ := Subgroup.mem_subgroupOf.1 hy
  exact Subgroup.mem_subgroupOf.2 (hZY (sec4Z_conj_mem g.2 (hYZ hyY)))

end Z

end CFSG.CGT.Timmesfeld75
