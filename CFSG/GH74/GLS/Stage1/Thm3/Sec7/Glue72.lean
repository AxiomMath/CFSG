module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue79

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem sq_three {a b c : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    a * b * c * (a * b * c) = 1 := by
  calc a * b * c * (a * b * c) = a * b * (c * a) * b * c := by group
    _ = a * b * (a * c) * b * c := by rw [hac]
    _ = a * (b * a) * c * b * c := by group
    _ = a * (a * b) * c * b * c := by rw [hab]
    _ = (a * a) * b * (c * b) * c := by group
    _ = (a * a) * b * (b * c) * c := by rw [hbc]
    _ = (a * a) * (b * b) * (c * c) := by group
    _ = 1 := by rw [ha, hb, hc]; simp

namespace Cfg7

theorem concl72_one (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) (hS1 : S1 S K₁ = Pz S z) :
    Concl72abcf z S K₁ K₂ t q 1 ∧ Concl72de z t u 1 := by
  have htS : t ∈ S := h.ch.t_mem
  have ht2 := h.t_sq
  have htP : t ∉ Pz S z := fun ht => h.t_nS1 (hS1 ▸ ht)
  have hY : Ysub t 1 = zpowers t := by
    unfold Ysub
    rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq]
  have hPS : Pz S z ≤ S := (h.Pz_le_S1 hII).trans S1_le_S
  have hfus := (h.ch.t_fus u h.ch.u_mem h.ch.u_ord h.ch.u_ne).symm
  refine ⟨⟨S.one_mem, Or.inl rfl, by simp, ⟨?_, ?_⟩, ?_, h.ch.t_swap, fun h1 => absurd rfl h1⟩,
    ⟨⟨h.ch.t_conj, by simpa using h.ch.t_conj⟩, ⟨hfus, by simpa using hfus⟩,
      fun h1 => absurd rfl h1⟩⟩
  · rw [hY, eq_bot_iff]
    rintro x ⟨hxP, hxt⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases B.zpow_of_sq_eq_one ht2 k with h' | h'
    · exact h'
    · exact absurd (h' ▸ hxP) htP
  · rw [hY]
    apply le_antisymm
    · intro s hs
      rcases A.relIndex_two_pigeon h.S1_relIndex htS hs with h1 | h1 | h1
      · exact absurd h1 h.t_nS1
      · exact mem_sup_left (hS1 ▸ h1)
      · have e : s = t * (t⁻¹ * s) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (hS1 ▸ h1))
    · exact sup_le hPS (zpowers_le.2 htS)
  · rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq]
    exact hS1

end Cfg7

theorem prop_7_2 (hII : II4_4_4_center) (h73 : Lemma7_3) (h74 : Lemma7_4) (h77 : Lemma7_7)
    (h78 : Lemma7_8) (h79 : Lemma7_9) (hDih : Dih_index2_invol) : Prop7_2 := by
  intro G _ _ z S K₁ K₂ t u q h
  have hc73 := h73 G z S K₁ K₂ t u q h
  obtain ⟨⟨D, hD⟩, hc74⟩ := h74 G z S K₁ K₂ t u q h hc73
  have hle := hc73.1
  have hpos := C73.relIndex_pos (Pz S z) (S1 S K₁)
  rcases (show (Pz S z).relIndex (S1 S K₁) = 1 ∨ (Pz S z).relIndex (S1 S K₁) = 2 by omega) with
    h1 | hidx
  · exact ⟨1, h.concl72_one hII
      (le_antisymm (Subgroup.relIndex_eq_one.1 h1) (h.Pz_le_S1 hII))⟩
  · obtain ⟨n, hn⟩ := h77 G z S K₁ K₂ t u q h hc73 hc74 hidx D hD
    obtain ⟨y, hyD, hyM, hyo⟩ :=
      hDih G D (D ⊓ Pz S z) n inf_le_left (hD.index_eq.trans hidx) hn hD.inter_dih
    have hyP : y ∉ Pz S z := fun hy => hyM ⟨hyD, hy⟩
    obtain ⟨⟨hyz, hyzz⟩, w, hw, hwc, hwnc⟩ :=
      h79 G z S K₁ K₂ t u q h hc73 hc74 hidx D hD ⟨n, hn⟩ y hyD hyP hyo
    have hc78 := h78 G z S K₁ K₂ t u q h hc73 hc74 hidx D hD ⟨n, hn⟩ y hyD hyP hyo w hw
    have hwS : w ∈ S := hc78.1
    have hw2 : w * w = 1 := by
      rcases hc78.2.1 with h1 | h1
      · rw [h1, mul_one]
      · exact mul_self_eq_one_of_orderOf_eq_two h1
    have hwt : t * w = w * t := hc78.2.2.1
    have hwz : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hwS)
    have htz : t * z = z * t := h.t_mul_z hII
    have hwS1 : w ∈ S1 S K₁ := hc78.2.2.2.2.1 ▸ mem_sup_right (mem_zpowers w)
    have hord : orderOf (t * w * z) = 2 := by
      refine orderOf_eq_prime (p := 2) ?_ ?_
      · rw [pow_two]
        exact sq_three h.t_sq hw2 h.z_sq hwt htz hwz
      · intro hh
        apply h.t_mul_nS1 hwS1
        have : t * w = z⁻¹ := eq_inv_of_mul_eq_one_left hh
        rw [this]
        exact (S1 S K₁).inv_mem (h.Pz_le_S1 hII (h.z_mem_Pz hII))
    have htwz : IsConj (t * z) (t * w * z) := (hc74.1 (t * w * z) hord).resolve_left hwnc
    refine ⟨w, hc78, ⟨h.ch.t_conj, hwc⟩,
      ⟨(h.ch.t_fus u h.ch.u_mem h.ch.u_ord h.ch.u_ne).symm,
        (h.ch.t_fus u h.ch.u_mem h.ch.u_ord h.ch.u_ne).symm.trans htwz⟩, fun _ => ?_⟩
    rcases (show w = y ∨ w = y * z by simpa using hw) with h1 | h1
    · rw [h1]; exact hyz
    · rw [h1]; exact hyzz

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
