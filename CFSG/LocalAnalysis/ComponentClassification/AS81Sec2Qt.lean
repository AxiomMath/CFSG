module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Wt
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise

namespace Sec2

variable {G : Type} [Group G]

theorem card_le_two_mul_card_inf [Finite G] {U W : Subgroup G} {g : G}
    (h : ∀ u ∈ U, u ∈ W ∨ g * u ∈ W) : Nat.card U ≤ 2 * Nat.card (U ⊓ W : Subgroup G) := by
  classical
  by_cases hU : ∃ u₀ ∈ U, u₀ ∉ W
  · obtain ⟨u₀, hu₀, hu₀W⟩ := hU
    have hgu₀ : g * u₀ ∈ W := (h u₀ hu₀).resolve_left hu₀W
    have hmem : ∀ u : U, (u : G) ∉ W → u₀⁻¹ * (u : G) ∈ U ⊓ W := fun u hu => by
      refine ⟨U.mul_mem (U.inv_mem hu₀) u.2, ?_⟩
      have hgu : g * u ∈ W := (h u u.2).resolve_left hu
      have e : u₀⁻¹ * (u : G) = (g * u₀)⁻¹ * (g * u) := by group
      rw [e]
      exact W.mul_mem (W.inv_mem hgu₀) hgu
    let f : U → (U ⊓ W : Subgroup G) ⊕ (U ⊓ W : Subgroup G) := fun u =>
      if hu : (u : G) ∈ W then Sum.inl ⟨u, u.2, hu⟩ else Sum.inr ⟨u₀⁻¹ * u, hmem u hu⟩
    have hf : Function.Injective f := by
      intro a b hab
      by_cases ha : (a : G) ∈ W <;> by_cases hb : (b : G) ∈ W
      · have h1 : f a = Sum.inl ⟨a, a.2, ha⟩ := dite_eq_left ha
        have h2 : f b = Sum.inl ⟨b, b.2, hb⟩ := dite_eq_left hb
        rw [h1, h2] at hab
        have h3 := congrArg Subtype.val (Sum.inl.inj hab)
        exact Subtype.ext h3
      · have h1 : f a = Sum.inl ⟨a, a.2, ha⟩ := dite_eq_left ha
        have h2 : f b = Sum.inr ⟨u₀⁻¹ * b, hmem b hb⟩ := dite_eq_right hb
        rw [h1, h2] at hab
        exact absurd hab Sum.inl_ne_inr
      · have h1 : f a = Sum.inr ⟨u₀⁻¹ * a, hmem a ha⟩ := dite_eq_right ha
        have h2 : f b = Sum.inl ⟨b, b.2, hb⟩ := dite_eq_left hb
        rw [h1, h2] at hab
        exact absurd hab.symm Sum.inl_ne_inr
      · have h1 : f a = Sum.inr ⟨u₀⁻¹ * a, hmem a ha⟩ := dite_eq_right ha
        have h2 : f b = Sum.inr ⟨u₀⁻¹ * b, hmem b hb⟩ := dite_eq_right hb
        rw [h1, h2] at hab
        have h3 := congrArg Subtype.val (Sum.inr.inj hab)
        exact Subtype.ext (mul_left_cancel h3)
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at this
    omega
  · push Not at hU
    rw [inf_eq_left.mpr hU]
    omega

theorem le_normalizer_of_conj {X Y : Subgroup G} (h : ∀ y ∈ Y, ∀ q ∈ X, y * q * y⁻¹ ∈ X) :
    Y ≤ normalizer (X : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro n
  refine ⟨h y hy n, fun hn => ?_⟩
  have h1 := h y⁻¹ (Y.inv_mem hy) _ hn
  have e : y⁻¹ * (y * n * y⁻¹) * y⁻¹⁻¹ = n := by group
  rwa [e] at h1

variable {S Z H : Subgroup G} {x t z : G}

theorem eq_t_mul (ht2 : t * t = 1) (q : G) : q = t * (t * q) := by
  rw [← mul_assoc, ht2, one_mul]

theorem Special.conj_t_mem_Wt (hS : Special S Z) (htS : t ∈ normalizer (S : Set G)) {w : G}
    (hw : w ∈ hS.Wt t) : t * w * t⁻¹ ∈ hS.Wt t := by
  obtain ⟨c, hc, hcw⟩ := hS.exists_conj_t hw
  rw [hcw]
  exact (hS.Wt t).mul_mem (hS.Z_le_Wt htS hc) hw

@[expose] def Special.Qt (hS : Special S Z) (htS : t ∈ normalizer (S : Set G))
    (ht2 : t * t = 1) : Subgroup G where
  carrier := {q | q ∈ hS.Wt t ∨ t * q ∈ hS.Wt t}
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl ((hS.Wt t).mul_mem ha hb)
    · right
      have e : t * (a * b) = (t * a * t⁻¹) * (t * b) := by group
      rw [e]
      exact (hS.Wt t).mul_mem (hS.conj_t_mem_Wt htS ha) hb
    · right
      have e : t * (a * b) = (t * a) * b := by group
      rw [e]
      exact (hS.Wt t).mul_mem ha hb
    · left
      have e : a * b = (t * (t * a) * t⁻¹) * (t * b) := by
        calc a * b = (t * t) * a * (t * t)⁻¹ * ((t * t) * b) := by rw [ht2]; group
          _ = (t * (t * a) * t⁻¹) * (t * b) := by group
      rw [e]
      exact (hS.Wt t).mul_mem (hS.conj_t_mem_Wt htS ha) hb
  one_mem' := Or.inl (hS.Wt t).one_mem
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl ((hS.Wt t).inv_mem ha)
    · right
      have e : t * (t * a)⁻¹ * t⁻¹ = t * a⁻¹ := by
        calc t * (t * a)⁻¹ * t⁻¹ = t * a⁻¹ * (t * t)⁻¹ := by group
          _ = t * a⁻¹ := by rw [ht2, inv_one, mul_one]
      rw [← e]
      exact hS.conj_t_mem_Wt htS ((hS.Wt t).inv_mem ha)

section Qt

variable (hS : Special S Z) (htS : t ∈ normalizer (S : Set G)) (ht2 : t * t = 1)

theorem Special.Wt_le_Qt : hS.Wt t ≤ hS.Qt htS ht2 := fun _ h => Or.inl h

theorem Special.t_mem_Qt : t ∈ hS.Qt htS ht2 := Or.inr (by rw [ht2]; exact (hS.Wt t).one_mem)

theorem Special.mem_Wt_of_mem_Qt (htnS : t ∉ S) {q : G} (hq : q ∈ hS.Qt htS ht2) (hqS : q ∈ S) :
    q ∈ hS.Wt t := by
  rcases hq with hq | hq
  · exact hq
  · exfalso
    apply htnS
    have e : t = (t * q) * q⁻¹ := by group
    rw [e]
    exact S.mul_mem hq.1 (S.inv_mem hqS)

theorem Special.card_Qt [Finite G] (htnS : t ∉ S) :
    Nat.card (hS.Qt htS ht2) = 2 * Nat.card (hS.Wt t) := by
  apply le_antisymm
  · have h := card_le_two_mul_card_inf (U := hS.Qt htS ht2) (W := hS.Wt t) (g := t)
      (fun q hq => hq)
    rwa [inf_eq_right.mpr (hS.Wt_le_Qt htS ht2)] at h
  · have hmem : ∀ w ∈ hS.Wt t, t * w ∈ hS.Qt htS ht2 := fun w hw =>
      Or.inr (by rw [← mul_assoc, ht2, one_mul]; exact hw)
    let f : (hS.Wt t) ⊕ (hS.Wt t) → hS.Qt htS ht2 := fun p =>
      match p with
      | Sum.inl w => ⟨w, hS.Wt_le_Qt htS ht2 w.2⟩
      | Sum.inr w => ⟨t * w, hmem w w.2⟩
    have hf : Function.Injective f := by
      rintro (a | a) (b | b) hab
      · have h1 := congrArg Subtype.val hab
        exact congrArg Sum.inl (Subtype.ext h1)
      · exfalso
        have h1 : (a : G) = t * b := congrArg Subtype.val hab
        apply htnS
        have e : t = (a : G) * (b : G)⁻¹ := by rw [h1]; group
        rw [e]
        exact S.mul_mem a.2.1 (S.inv_mem b.2.1)
      · exfalso
        have h1 : t * (a : G) = b := congrArg Subtype.val hab
        apply htnS
        have e : t = (b : G) * (a : G)⁻¹ := by rw [← h1]; group
        rw [e]
        exact S.mul_mem b.2.1 (S.inv_mem a.2.1)
      · have h1 : t * (a : G) = t * b := congrArg Subtype.val hab
        exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h1))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_sum, ← two_mul] at this

theorem Special.Qt_le {X : Subgroup G} (hWX : hS.Wt t ≤ X) (htX : t ∈ X) : hS.Qt htS ht2 ≤ X := by
  rintro q (hq | hq)
  · exact hWX hq
  · rw [eq_t_mul ht2 q]
    exact X.mul_mem htX (hWX hq)

end Qt

theorem Special.z_comm_Qt (hS : Special S Z) (ht : TData S H x t)
    (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) (hzZ : z ∈ Z) {b : G}
    (hb : b ∈ hS.Qt ht.normS ht.sq) : z * b = b * z := by
  rcases hb with hb | hb
  · exact hS.comm_Z hzZ hb.1
  · have htz : t * z * t⁻¹ = z := (hz z hzZ).mpr (mem_zpowers z)
    have hzt : z * t = t * z := by
      calc z * t = (t * z * t⁻¹) * t := by rw [htz]
        _ = t * z := by group
    have h1 := hS.comm_Z hzZ hb.1
    rw [eq_t_mul ht.sq b]
    calc z * (t * (t * b)) = (z * t) * (t * b) := by group
      _ = t * (z * (t * b)) := by rw [hzt]; group
      _ = t * ((t * b) * z) := by rw [h1]
      _ = t * (t * b) * z := by group

theorem Coord.comm_mem_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {a b : G}
    (ha : a ∈ hS.Qt ht.normS ht.sq) (hb : b ∈ hS.Qt ht.normS ht.sq) :
    a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  have hfix : ∀ {c : G}, c ∈ zpowers z → t * c * t⁻¹ = c := fun hc =>
    conj_eq_of_mem_zpowers hz hzZ hc
  have htw : ∀ w ∈ hS.Wt t, w * t * w⁻¹ * t⁻¹ ∈ zpowers z := fun w hw =>
    C.comm_t_mem hS hHS hx ht hzZ hz1 hz hw
  have hW : ∀ w ∈ hS.Wt t, ∀ b ∈ hS.Qt ht.normS ht.sq, w * b * w⁻¹ * b⁻¹ ∈ zpowers z := by
    intro w hw b hb
    rcases hb with hb | hb
    · exact comm_mem_zpowers hS hz hw hb
    · rw [eq_t_mul ht.sq b]
      have e : w * (t * (t * b)) * w⁻¹ * (t * (t * b))⁻¹ =
          (w * t * w⁻¹ * t⁻¹) * (t * (w * (t * b) * w⁻¹ * (t * b)⁻¹) * t⁻¹) := by group
      rw [e, hfix (comm_mem_zpowers hS hz hw hb)]
      exact mul_mem (htw w hw) (comm_mem_zpowers hS hz hw hb)
  have hT : ∀ b ∈ hS.Qt ht.normS ht.sq, t * b * t⁻¹ * b⁻¹ ∈ zpowers z := by
    intro b hb
    rcases hb with hb | hb
    · have h1 := inv_mem (htw b hb)
      rwa [Special.comm_inv] at h1
    · rw [eq_t_mul ht.sq b]
      have e : t * (t * (t * b)) * t⁻¹ * (t * (t * b))⁻¹ =
          t * (t * (t * b) * t⁻¹ * (t * b)⁻¹) * t⁻¹ := by group
      have h1 := inv_mem (htw _ hb)
      rw [Special.comm_inv] at h1
      rw [e, hfix h1]
      exact h1
  rcases ha with ha | ha
  · exact hW a ha b hb
  · rw [eq_t_mul ht.sq a]
    have e : t * (t * a) * b * (t * (t * a))⁻¹ * b⁻¹ =
        (t * ((t * a) * b * (t * a)⁻¹ * b⁻¹) * t⁻¹) * (t * b * t⁻¹ * b⁻¹) := by group
    rw [e, hfix (hW _ ha b hb)]
    exact mul_mem (hW _ ha b hb) (hT b hb)

theorem Coord.sq_mem_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {a : G}
    (ha : a ∈ hS.Qt ht.normS ht.sq) : a * a ∈ zpowers z := by
  rcases ha with ha | ha
  · exact sq_mem_zpowers hS hz ha
  · rw [eq_t_mul ht.sq a]
    have e : t * (t * a) * (t * (t * a)) =
        (t * (t * a) * t⁻¹ * (t * a)⁻¹) * ((t * a) * (t * a)) := by
      rw [ht.inv_eq]
      group
    have h1 := inv_mem (C.comm_t_mem hS hHS hx ht hzZ hz1 hz ha)
    rw [Special.comm_inv] at h1
    rw [e]
    exact mul_mem h1 (sq_mem_zpowers hS hz ha)

theorem Coord.mem_zpowers_of_central_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {a : G}
    (ha : a ∈ hS.Qt ht.normS ht.sq) (hc : ∀ b ∈ hS.Qt ht.normS ht.sq, a * b = b * a) :
    a ∈ zpowers z := by
  rcases ha with ha | ha
  · have haZ : a ∈ Z := C.mem_Z_of_comm_Wt hS hHS hx ht hzZ hz1 hz ha
      (fun w hw => hc w (hS.Wt_le_Qt _ _ hw))
    refine (hz a haZ).mp ?_
    have h1 := hc t (hS.t_mem_Qt ht.normS ht.sq)
    calc t * a * t⁻¹ = a * t * t⁻¹ := by rw [h1]
      _ = a := by group
  · exfalso
    obtain ⟨c', hc'Z, hc'z⟩ := exists_mem_Z_not_mem hS hz1 hzZ
    apply hc'z
    refine (hz c' hc'Z).mp ?_
    have h1 := hc c' (hS.Wt_le_Qt _ _ (hS.Z_le_Wt ht.normS hc'Z))
    calc t * c' * t⁻¹ = t * ((t * a) * c' * (t * a)⁻¹) * t⁻¹ := by
          rw [hS.conj_Z hc'Z ha.1]
      _ = (t * (t * a)) * c' * (t * (t * a))⁻¹ := by group
      _ = a * c' * a⁻¹ := by rw [← eq_t_mul ht.sq a]
      _ = c' := by rw [h1]; group

theorem Coord.isExtraspecial_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) :
    CFSG.IsExtraspecialPGroup 2 (hS.Qt ht.normS ht.sq) ∧
      (center (hS.Qt ht.normS ht.sq)).map (hS.Qt ht.normS ht.sq).subtype = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (hS.Qt ht.normS ht.sq) = 2 ^ 7 := by
    rw [hS.card_Qt ht.normS ht.sq ht.notS, C.card_Wt hS hx ht]
    norm_num
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hS.elem z hzZ) hz1
  have hzQ : z ∈ hS.Qt ht.normS ht.sq := hS.Wt_le_Qt _ _ (hS.Z_le_Wt ht.normS hzZ)
  refine CFSG.LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall
    (IsPGroup.of_card hcard) hzQ hz2 (fun a ha => ⟨fun hc => ?_, fun h b hb => ?_⟩)
    (fun a ha b hb => ?_) (fun a ha => ?_) ?_
  · exact C.mem_zpowers_of_central_Qt hS hHS hx ht hzZ hz1 hz ha hc
  · rcases hS.eq_one_or_eq hzZ h with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hS.z_comm_Qt ht hz hzZ hb
  · rw [commutatorElement_def]
    exact C.comm_mem_Qt hS hHS hx ht hzZ hz1 hz ha hb
  · rw [sq]
    exact C.sq_mem_Qt hS hHS hx ht hzZ hz1 hz ha
  · obtain ⟨a, ha, b, hb, hab⟩ := C.exists_not_comm_Wt hS hHS hx ht hzZ hz1 hz
    refine ⟨a, hS.Wt_le_Qt _ _ ha, b, hS.Wt_le_Qt _ _ hb, fun h => hab ?_⟩
    rw [h]
    group

theorem Coord.isQ8Cube_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) :
    IsQ8Cube (hS.Qt ht.normS ht.sq) := by
  refine ⟨(C.isExtraspecial_Qt hS hHS hx ht hzZ hz1 hz).1,
    by rw [hS.card_Qt ht.normS ht.sq ht.notS, C.card_Wt hS hx ht]; norm_num, ?_⟩
  rintro ⟨U, hUQ, hU, hU16⟩
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hU.1.1.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hUsq : ∀ a ∈ U, a * a = 1 := fun a ha => by rw [← sq]; exact hU.2 a ha
  have h1 := card_le_two_mul_card_inf (U := U) (W := hS.Wt t) (g := t) (fun u hu => hUQ hu)
  obtain ⟨h2, h3⟩ := C.card_le_eight_of_elem hS hHS hx ht hzZ hz1 hz (U := U ⊓ hS.Wt t)
    inf_le_right (fun u hu => hUsq u hu.1) (fun u hu u' hu' => hUcomm u hu.1 u' hu'.1)
  have h8 : Nat.card (U ⊓ hS.Wt t : Subgroup G) = 8 := by omega
  have hZU : Z ≤ U := (h3 h8).trans inf_le_left
  obtain ⟨u, hu, huW⟩ : ∃ u ∈ U, u ∉ hS.Wt t := by
    by_contra h
    push Not at h
    rw [inf_eq_left.mpr h] at h8
    omega
  have htu : t * u ∈ hS.Wt t := (hUQ hu).resolve_left huW
  obtain ⟨c', hc'Z, hc'z⟩ := exists_mem_Z_not_mem hS hz1 hzZ
  apply hc'z
  refine (hz c' hc'Z).mp ?_
  have h4 := hUcomm u hu c' (hZU hc'Z)
  calc t * c' * t⁻¹ = t * ((t * u) * c' * (t * u)⁻¹) * t⁻¹ := by rw [hS.conj_Z hc'Z htu.1]
    _ = (t * (t * u)) * c' * (t * (t * u))⁻¹ := by group
    _ = u * c' * u⁻¹ := by rw [← eq_t_mul ht.sq u]
    _ = c' := by rw [h4]; group

theorem Coord.conj_mem_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (ht : TData S H x t) {h q : G} (hh : h ∈ H)
    (hq : q ∈ hS.Qt ht.normS ht.sq) : h * q * h⁻¹ ∈ hS.Qt ht.normS ht.sq := by
  rcases hq with hq | hq
  · exact Or.inl (C.conj_mem_Wt hS hHS ht hh hq)
  · have hht : h * t * h⁻¹ ∈ hS.Qt ht.normS ht.sq := by
      obtain ⟨s, hs, l, hl, rfl, hlt⟩ := ht.compl h hh
      have e : s * l * t * (s * l)⁻¹ = (s * t * s⁻¹ * t⁻¹) * t := by
        calc s * l * t * (s * l)⁻¹ = s * (l * t) * l⁻¹ * s⁻¹ := by group
          _ = s * (t * l) * l⁻¹ * s⁻¹ := by rw [hlt]
          _ = (s * t * s⁻¹ * t⁻¹) * t := by group
      rw [e]
      refine Or.inr ?_
      have e2 : t * ((s * t * s⁻¹ * t⁻¹) * t) = t * (s * t * s⁻¹ * t⁻¹) * t⁻¹ := by
        rw [ht.inv_eq]
        group
      rw [e2]
      exact hS.conj_t_mem_Wt ht.normS (C.comm_t_mem_Wt hS ht hs)
    have hhw : h * (t * q) * h⁻¹ ∈ hS.Qt ht.normS ht.sq :=
      hS.Wt_le_Qt _ _ (C.conj_mem_Wt hS hHS ht hh hq)
    have e : h * q * h⁻¹ = (h * t * h⁻¹) * (h * (t * q) * h⁻¹) := by
      calc h * q * h⁻¹ = h * (t * (t * q)) * h⁻¹ := by rw [← eq_t_mul ht.sq q]
        _ = (h * t * h⁻¹) * (h * (t * q) * h⁻¹) := by group
    rw [e]
    exact (hS.Qt ht.normS ht.sq).mul_mem hht hhw

theorem Coord.le_normalizer_Qt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (ht : TData S H x t) {T : Subgroup G}
    (hTH : ∀ τ ∈ T, τ ∈ H ∨ t * τ ∈ H) :
    H ⊔ T ≤ normalizer (hS.Qt ht.normS ht.sq : Set G) := by
  have hH : H ≤ normalizer (hS.Qt ht.normS ht.sq : Set G) :=
    le_normalizer_of_conj fun h hh q hq => C.conj_mem_Qt hS hHS ht hh hq
  refine sup_le hH fun τ hτ => ?_
  rcases hTH τ hτ with h | h
  · exact hH h
  · rw [eq_t_mul ht.sq τ]
    exact mul_mem (Subgroup.le_normalizer (hS.t_mem_Qt _ _)) (hH h)

end Sec2

end CFSG.ComponentClassification.AS81
