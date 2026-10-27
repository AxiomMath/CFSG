module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue79
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Transport

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

theorem Oz_odd (z : G) : Odd (Nat.card ↥(Oz z)) := by
  have hc : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(Cz z))) := pPrimeCore_coprime_card
  have h1 : Nat.card ↥(Oz z) = Nat.card ↥(pPrimeCore 2 ↥(Cz z)) := by
    unfold Oz pPrimeCoreOf
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [h1]
  exact Nat.coprime_two_left.1 hc

namespace Cfg7

theorem S_inf_Oz (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) : S ⊓ Oz z = ⊥ :=
  M.inf_eq_bot_of_pgroup_odd (h.S_pgroup hII) (Oz_odd z)

theorem cls_cases (hII : II4_4_4_center) (hg : IG_10_32_P) (h31c : IVK_3_1c_lifted)
    (h : Cfg7 G z S K₁ K₂ t u q) {w : G} (hc : Concl72abcf z S K₁ K₂ t q w)
    (hd : Concl72de z t u w) {v : G} (hvS : v ∈ S) (hv2 : orderOf v = 2) :
    v ∈ Pz S z ∨ (∃ c ∈ Pz S z, c * t * c⁻¹ = v ∨ c * (t * z) * c⁻¹ = v) ∨
      (w ≠ 1 ∧ IsConj z v ∧ ∃ p ∈ Pz S z, v = p * w) ∨
      (w ≠ 1 ∧ ∃ c ∈ Pz S z, c * (t * w) * c⁻¹ = v ∨ c * (t * w * z) * c⁻¹ = v) := by
  have hc' := hc
  obtain ⟨hwS, hw12, hwt, ⟨-, hSeq⟩, hS1eq, -, -⟩ := hc
  have htS : t ∈ S := h.ch.t_mem
  have ht2 := h.t_sq
  have hw2 : w * w = 1 := by
    rcases hw12 with rfl | hw
    · exact mul_one 1
    · exact mul_self_eq_one_of_orderOf_eq_two hw
  have hYS : Ysub t w ≤ S := sup_le (zpowers_le.2 htS) (zpowers_le.2 hwS)
  have hv' : v ∈ Ysub t w ⊔ Pz S z := by rw [sup_comm, ← hSeq]; exact hvS
  obtain ⟨y₀, hy₀, p', hp', hvy⟩ :=
    A.mem_sup_of_le_normalizer (hYS.trans (h.S_le_normP hII)) hv'
  have hpP : y₀ * p' * y₀⁻¹ ∈ Pz S z := h.normP hII y₀ (hYS hy₀) p' hp'
  have hvp : v = (y₀ * p' * y₀⁻¹) * y₀ := by rw [hvy]; group
  have ig_t : ∀ p ∈ Pz S z, v = p * t →
      ∃ c ∈ Pz S z, c * t * c⁻¹ = v ∨ c * (t * z) * c⁻¹ = v := by
    intro p hp hvt
    exact hg G z S K₁ K₂ h.std.std t htS h.t_ord h.ch.t_swap v
      (by rw [hvt, mul_inv_cancel_right]; exact hp) hv2
  rcases A.mem_sup_zpowers_two ht2 hw2 hwt hy₀ with h1 | h1 | h1 | h1
  · left
    rw [hvy, h1]
    simpa using hp'
  · rw [h1] at hpP hvp
    exact Or.inr (Or.inl (ig_t _ hpP hvp))
  · by_cases hw1 : w = 1
    · left
      rw [hvy, h1, hw1]
      simpa using hp'
    · right; right; left
      rw [h1] at hpP hvp
      have hwo : orderOf w = 2 := hw12.resolve_left hw1
      obtain ⟨c, -, hcv⟩ := h31c G z S K₁ K₂ t u q w h hc' hw1 v hvS w hwS
        (by rw [hvp, mul_inv_cancel_right]; exact hpP) (by rw [mul_inv_cancel]; exact one_mem _) hv2 hwo
      exact ⟨hw1, (hd.2.2 hw1).trans (isConj_iff.2 ⟨c, hcv⟩).symm, _, hpP, hvp⟩
  · by_cases hw1 : w = 1
    · rw [h1, hw1, mul_one] at hpP hvp
      exact Or.inr (Or.inl (ig_t _ hpP hvp))
    · right; right; right
      refine ⟨hw1, ?_⟩
      rw [h1] at hpP hvp
      have hwS1 : w ∈ S1 S K₁ := by rw [hS1eq]; exact mem_sup_right (mem_zpowers w)
      have htwS : t * w ∈ S := S.mul_mem htS hwS
      have htw2 : (t * w) * (t * w) = 1 := by
        calc t * w * (t * w) = t * (w * t) * w := by group
          _ = t * (t * w) * w := by rw [hwt]
          _ = (t * t) * (w * w) := by group
          _ = 1 := by rw [ht2, hw2, mul_one]
      have htw1 : t * w ≠ 1 := by
        intro hh
        apply h.t_mul_nS1 hwS1
        rw [hh]
        exact one_mem _
      have htwo : orderOf (t * w) = 2 := orderOf_eq_prime (by simpa [pow_two] using htw2) htw1
      exact hg G z S K₁ K₂ h.std.std (t * w) htwS htwo (h.t_mul_swap hII hwS1) v
        (by rw [hvp, mul_inv_cancel_right]; exact hpP) hv2

theorem star (hII : II4_4_4_center) (hg : IG_10_32_P) (h31c : IVK_3_1c_lifted)
    (h : Cfg7 G z S K₁ K₂ t u q) {w : G} (hc : Concl72abcf z S K₁ K₂ t q w) (hd : Concl72de z t u w)
    {Gs : Type} [Group Gs] {z' t' w' : Gs} {S' E₁ E₂ : Subgroup Gs}
    (hdat : Dat410 q z' S' t' w' E₁ E₂) (hsupp : w' ≠ 1 → ¬IsConj z' (t' * w' * z'))
    (hww : w' = 1 ↔ w = 1) {f : G → Gs} (hf : Tr.FHom S f) (hfS : ∀ s ∈ S, f s ∈ S')
    (hfP : ∀ s ∈ Pz S z, f s ∈ IVK.Ez z') (hft : f t = t') (hfw : f w = w') (hfz : f z = z')
    {v : G} (hvS : v ∈ S) (hv2 : orderOf v = 2) :
    (IsConj z v ∧ IsConj z' (f v)) ∨ (IsConj (t * z) v ∧ ¬IsConj z v ∧ ¬IsConj z' (f v)) := by
  have hfv2 : orderOf (f v) = 2 := hf.orderOf_eq_two hvS hv2
  have htS : t ∈ S := h.ch.t_mem
  have hzS : z ∈ S := h.z_mem_S hII
  have hwS : w ∈ S := hc.1
  have hPS : Pz S z ≤ S := (h.Pz_le_S1 hII).trans S1_le_S
  have htz : t * z ∈ S := S.mul_mem htS hzS
  have htwS : t * w ∈ S := S.mul_mem htS hwS
  have hfmul_tz : f (t * z) = t' * z' := by rw [hf.mul t htS z hzS, hft, hfz]
  have hfmul_tw : f (t * w) = t' * w' := by rw [hf.mul t htS w hwS, hft, hfw]
  have hfmul_twz : f (t * w * z) = t' * w' * z' := by
    rw [hf.mul (t * w) htwS z hzS, hfmul_tw, hfz]
  have hnz : ¬IsConj z' (t' * z') := hdat.tz_ne
  rcases h.cls_cases hII hg h31c hc hd hvS hv2 with hvP | ⟨c, hcP, hcv | hcv⟩ |
      ⟨hw1, hzv, p, hpP, hvp⟩ | ⟨hw1, c, hcP, hcv | hcv⟩
  · by_cases hvz : v = z
    · left
      rw [hvz, hfz]
      exact ⟨IsConj.refl _, IsConj.refl _⟩
    · right
      refine ⟨h.ch.t_fus v hvP hv2 hvz, fun hzv => hvz (h.std.nonfused v hvP hzv), fun hzv' => ?_⟩
      have hfne : f v ≠ z' := by
        intro hh
        exact hvz (hf.inj v hvS z hzS (hh.trans hfz.symm))
      exact hnz (hzv'.trans (hdat.E_fus (f v) (hfP v hvP) hfv2 hfne).symm)
  · left
    have hcS : c ∈ S := hPS hcP
    refine ⟨h.ch.t_conj.trans (isConj_iff.2 ⟨c, hcv⟩), ?_⟩
    have : f v = f c * t' * (f c)⁻¹ := by rw [← hcv, hf.map_conj hcS htS, hft]
    rw [this]
    exact hdat.t_conj.trans (isConj_iff.2 ⟨f c, rfl⟩)
  · right
    have hcS : c ∈ S := hPS hcP
    have hcj : IsConj (t * z) v := isConj_iff.2 ⟨c, hcv⟩
    refine ⟨hcj, fun hzv => h.ch.tz_ne (hzv.trans hcj.symm), fun hzv' => hnz ?_⟩
    have hfv : f v = f c * (t' * z') * (f c)⁻¹ := by rw [← hcv, hf.map_conj hcS htz, hfmul_tz]
    have : IsConj (t' * z') (f v) := by rw [hfv]; exact isConj_iff.2 ⟨f c, rfl⟩
    exact hzv'.trans this.symm
  · left
    refine ⟨hzv, ?_⟩
    have hw1' : w' ≠ 1 := fun h1 => hw1 (hww.1 h1)
    have hpS : p ∈ S := hPS hpP
    have hfv : f v = f p * w' := by rw [hvp, hf.mul p hpS w hwS, hfw]
    have hmem : f p ∈ S' ⊓ IVK.Ez z' := ⟨hfS p hpS, hfP p hpP⟩
    have := (hdat.w_fus hw1').2 (f p) hmem (by rw [← hfv]; exact hfv2)
    rwa [← hfv] at this
  · left
    have hcS : c ∈ S := hPS hcP
    have hw1' : w' ≠ 1 := fun h1 => hw1 (hww.1 h1)
    refine ⟨hd.1.2.trans (isConj_iff.2 ⟨c, hcv⟩), ?_⟩
    have : f v = f c * (t' * w') * (f c)⁻¹ := by rw [← hcv, hf.map_conj hcS htwS, hfmul_tw]
    rw [this]
    exact (hdat.w_fus hw1').1.trans (isConj_iff.2 ⟨f c, rfl⟩)
  · right
    have hcS : c ∈ S := hPS hcP
    have hw1' : w' ≠ 1 := fun h1 => hw1 (hww.1 h1)
    have htwzS : t * w * z ∈ S := S.mul_mem htwS hzS
    have htwz : IsConj (t * z) (t * w * z) := hd.2.1.1.symm.trans hd.2.1.2
    have hcj : IsConj (t * w * z) v := isConj_iff.2 ⟨c, hcv⟩
    refine ⟨htwz.trans hcj, fun hzv => h.ch.tz_ne ((hzv.trans hcj.symm).trans htwz.symm),
      fun hzv' => hsupp hw1' ?_⟩
    have hfv : f v = f c * (t' * w' * z') * (f c)⁻¹ := by
      rw [← hcv, hf.map_conj hcS htwzS, hfmul_twz]
    have : IsConj (t' * w' * z') (f v) := by rw [hfv]; exact isConj_iff.2 ⟨f c, rfl⟩
    exact hzv'.trans this.symm

theorem fusion (hII : II4_4_4_center) (hg : IG_10_32_P) (h31c : IVK_3_1c_lifted)
    (h : Cfg7 G z S K₁ K₂ t u q) {w : G} (hc : Concl72abcf z S K₁ K₂ t q w) (hd : Concl72de z t u w)
    {Gs : Type} [Group Gs] {z' t' w' : Gs} {S' E₁ E₂ : Subgroup Gs}
    (hdat : Dat410 q z' S' t' w' E₁ E₂) (hsupp : w' ≠ 1 → ¬IsConj z' (t' * w' * z'))
    (hww : w' = 1 ↔ w = 1) {f : G → Gs} (hf : Tr.FHom S f) (hfS : ∀ s ∈ S, f s ∈ S')
    (hfP : ∀ s ∈ Pz S z, f s ∈ IVK.Ez z') (hft : f t = t') (hfw : f w = w') (hfz : f z = z') :
    ∀ a ∈ S, ∀ b ∈ S, orderOf a = 2 → orderOf b = 2 → (IsConj a b ↔ IsConj (f a) (f b)) := by
  intro a ha b hb ha2 hb2
  have st := fun v (hv : v ∈ S) (hv2 : orderOf v = 2) =>
    h.star hII hg h31c hc hd hdat hsupp hww hf hfS hfP hft hfw hfz hv hv2
  have hcl : ∀ x : Gs, orderOf x = 2 → ¬IsConj z' x → IsConj (t' * z') x := fun x hx hnx =>
    (hdat.classes x hx).resolve_left hnx
  rcases st a ha ha2 with ⟨ha1, ha1'⟩ | ⟨ha1, ha2n, ha2n'⟩ <;>
    rcases st b hb hb2 with ⟨hb1, hb1'⟩ | ⟨hb1, hb2n, hb2n'⟩
  · exact ⟨fun _ => ha1'.symm.trans hb1', fun _ => ha1.symm.trans hb1⟩
  · exact ⟨fun hab => absurd (ha1.trans hab) hb2n, fun hab => absurd (ha1'.trans hab) hb2n'⟩
  · exact ⟨fun hab => absurd (hb1.trans hab.symm) ha2n, fun hab => absurd (hb1'.trans hab.symm) ha2n'⟩
  · exact ⟨fun _ => (hcl _ (hf.orderOf_eq_two ha ha2) ha2n').symm.trans
        (hcl _ (hf.orderOf_eq_two hb hb2) hb2n'), fun _ => ha1.symm.trans hb1⟩

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
