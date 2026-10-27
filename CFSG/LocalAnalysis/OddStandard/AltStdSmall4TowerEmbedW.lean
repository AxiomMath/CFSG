module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4WF9Wreath

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup WF9

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}

theorem exists_wreath_compl (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T)
    (hW : WreathStruct z T) :
    ∃ X : Subgroup G, X ≤ normalizer (T : Set G) ∧ z ∈ X ∧
      X ⊓ centralizer (T : Set G) = ⊥ ∧
      normalizer (T : Set G) ≤ X ⊔ centralizer (T : Set G) ∧ Nat.card X = 56448 := by
  obtain ⟨K₁, F₁, hK₁N, hcomm, hinter, hE8, -, hF₁K, hF₁T, hEF, hF168, hcent, hNle, -⟩ :=
    hW.exists_factor
  have hzz : z * z = 1 := by rw [← pow_two, ← c.ot.cyc.order, pow_orderOf_eq_one]
  have hzN : z ∈ normalizer (T : Set G) := hH.n0.norm
  have hTC : T ≤ centralizer (T : Set G) := by rw [hH.cent]; exact le_sup_left
  have hOC : AltStdSec.oddCoreOf (normalizer (T : Set G)) ≤ centralizer (T : Set G) := by
    rw [hH.cent]; exact le_sup_right
  have hFzK : conjSub z F₁ ≤ conjSub z K₁ := map_mono hF₁K
  have hE1 : ∃ e ∈ K₁ ⊓ T, e ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : K₁ ⊓ T = ⊥ := eq_bot_iff.2 fun x hx => (mem_bot).2 (h x hx)
    rw [hbot, card_bot] at hE8
    omega
  have hWr : WrData F₁ z :=
    { sq := hzz
      comm := fun a ha b hb => hcomm a (hF₁K ha) b (hFzK hb)
      inf := eq_bot_iff.2 fun x hx => by
        have h : x ∈ K₁ ⊓ conjSub z K₁ := mem_inf.2 ⟨hF₁K (mem_inf.1 hx).1, hFzK (mem_inf.1 hx).2⟩
        rwa [hinter] at h
      not_mem := fun hz => by
        have hzK : z ∈ K₁ ⊔ conjSub z K₁ := sup_le_sup hF₁K hFzK hz
        have hle : K₁ ⊔ conjSub z K₁ ≤ normalizer (K₁ : Set G) :=
          sup_le le_normalizer fun b hb =>
            centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
        have hzK₁ := hle hzK
        have hKK : K₁ ≤ conjSub z K₁ := fun k hk => by
          have h1 : z⁻¹ * k * z ∈ K₁ := (mem_normalizer_iff''.1 hzK₁ k).1 hk
          have h2 := conj_mem_conjSub (z := z) h1
          rwa [show z * (z⁻¹ * k * z) * z⁻¹ = k by group] at h2
        have hbot : K₁ = ⊥ := by
          rw [eq_bot_iff, ← hinter]
          exact le_inf le_rfl hKK
        rw [hbot, bot_inf_eq, card_bot] at hE8
        omega }
  have hFE : ∀ r ∈ F₁, (∀ e ∈ K₁ ⊓ T, e * r = r * e) → r = 1 := by
    intro r hr he
    have h1 : r ∈ centralizer ((K₁ ⊓ T : Subgroup G) : Set G) ⊓ K₁ :=
      mem_inf.2 ⟨mem_centralizer_iff.2 he, hF₁K hr⟩
    rw [hcent] at h1
    have h2 : r ∈ F₁ ⊓ T := mem_inf.2 ⟨hr, (mem_inf.1 h1).2⟩
    rwa [hF₁T, mem_bot] at h2
  set X : Subgroup G := F₁ ⊔ conjSub z F₁ ⊔ zpowers z with hXdef
  have hF₁N : F₁ ≤ normalizer (T : Set G) := hF₁K.trans hK₁N
  have hFzN : conjSub z F₁ ≤ normalizer (T : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_conjSub.1 hx
    exact mul_mem (mul_mem hzN (hF₁N hy)) (inv_mem hzN)
  refine ⟨X, sup_le (sup_le hF₁N hFzN) (zpowers_le.2 hzN), mem_sup_right (mem_zpowers z), ?_, ?_,
    ?_⟩
  ·
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
    have hxC' := mem_centralizer_iff.1 hxC
    rcases hWr.mem_top_iff.1 hxX with hxB | hxB
    · obtain ⟨r, hr, s, hs, rfl⟩ := hWr.mem_base_iff.1 hxB
      have hsK := hFzK hs
      have hr1 : r = 1 := hFE r hr fun e he => by
        have h1 := hxC' e (mem_inf.1 he).2
        have h2 : e * s = s * e := hcomm e (mem_inf.1 he).1 s hsK
        have h3 : e * r * s = r * e * s := by
          calc e * r * s = e * (r * s) := by group
            _ = r * s * e := h1
            _ = r * (e * s) := by rw [mul_assoc, ← h2]
            _ = r * e * s := by group
        exact mul_right_cancel h3
      subst hr1
      obtain ⟨f, hf, rfl⟩ := mem_conjSub.1 hs
      have hf1 : f = 1 := hFE f hf fun e he => by
        have hzeT : z * e * z⁻¹ ∈ T := (mem_normalizer_iff.1 hzN e).1 (mem_inf.1 he).2
        have h1 := hxC' _ hzeT
        have h2 : z * (e * f) * z⁻¹ = z * (f * e) * z⁻¹ := by
          calc z * (e * f) * z⁻¹ = z * e * z⁻¹ * (1 * (z * f * z⁻¹)) := by group
            _ = 1 * (z * f * z⁻¹) * (z * e * z⁻¹) := h1
            _ = z * (f * e) * z⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel h2)
      rw [hf1, mul_one, one_mul, mul_inv_cancel, mem_bot]
    · exfalso
      obtain ⟨r, hr, s, hs, hrs⟩ := hWr.mem_base_iff.1 hxB
      have hx' : x = r * s * z := by rw [hrs, mul_assoc, hzz, mul_one]
      have hsK := hFzK hs
      obtain ⟨e, he, he1⟩ := hE1
      have heK := (mem_inf.1 he).1
      have hzeK : z * e * z⁻¹ ∈ conjSub z K₁ := conj_mem_conjSub heK
      have hmem : s * (z * e * z⁻¹) * s⁻¹ ∈ conjSub z K₁ :=
        mul_mem (mul_mem hsK hzeK) (inv_mem hsK)
      have hcr := hcomm r (hF₁K hr) _ hmem
      have hxe : x * e * x⁻¹ = e := by
        have h1 := hxC' e (mem_inf.1 he).2
        rw [← h1, mul_inv_cancel_right]
      have hxe' : x * e * x⁻¹ = s * (z * e * z⁻¹) * s⁻¹ := by
        calc x * e * x⁻¹ = r * (s * (z * e * z⁻¹) * s⁻¹) * r⁻¹ := by rw [hx']; group
          _ = s * (z * e * z⁻¹) * s⁻¹ := by rw [hcr, mul_inv_cancel_right]
      have hmem' : e ∈ K₁ ⊓ conjSub z K₁ := mem_inf.2 ⟨heK, by rw [← hxe, hxe']; exact hmem⟩
      rw [hinter, mem_bot] at hmem'
      exact he1 hmem'
  ·
    have hK₁le : K₁ ≤ X ⊔ centralizer (T : Set G) := by
      rw [← hEF]
      exact sup_le (inf_le_right.trans (hTC.trans le_sup_right))
        ((le_sup_left.trans le_sup_left).trans le_sup_left)
    have hKzle : conjSub z K₁ ≤ X ⊔ centralizer (T : Set G) := by
      rw [← hEF, conjSub, Subgroup.map_sup]
      refine sup_le ?_ ((le_sup_right.trans le_sup_left).trans le_sup_left)
      rintro _ ⟨e, he, rfl⟩
      refine mem_sup_right (hTC ?_)
      exact (mem_normalizer_iff.1 hzN e).1 (mem_inf.1 he).2
    exact hNle.trans (sup_le (sup_le (sup_le hK₁le hKzle) (hOC.trans le_sup_right))
      (zpowers_le.2 (mem_sup_left (mem_sup_right (mem_zpowers z)))))
  ·
    have hB : Nat.card (F₁ ⊔ conjSub z F₁ : Subgroup G) = 168 * 168 := by
      let f : F₁ × conjSub z F₁ → (F₁ ⊔ conjSub z F₁ : Subgroup G) := fun p =>
        ⟨(p.1 : G) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
      have hf : Function.Bijective f := by
        refine ⟨fun a b h => ?_, fun y => ?_⟩
        · obtain ⟨h1, h2⟩ := hWr.eq_of_mul_eq a.1.2 b.1.2 a.2.2 b.2.2 (congrArg Subtype.val h)
          exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
        · obtain ⟨r, hr, s, hs, hrs⟩ := hWr.mem_base_iff.1 y.2
          exact ⟨(⟨r, hr⟩, ⟨s, hs⟩), Subtype.ext hrs⟩
      rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, hF168]
      congr 1
      rw [conjSub, card_map_of_injective (MulAut.conj z).injective, hF168]
    have h := relIndex_mul_card (F₁ ⊔ conjSub z F₁) X
    rw [inf_of_le_left le_sup_left, hWr.relIndex_base, hB] at h
    rw [← h]

end CFSG.OddStandard.AltStdSmall4.Tower
