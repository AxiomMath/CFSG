module

public import CFSG.GF2Type.Aschbacher1976Full.HSGL3

public section

namespace CFSG.GF2Type.Smith1979.W4As

open Equiv MulAction

theorem odd_card_fixedPoints {t : Perm (Fin 9)} (ht : t * t = 1) :
    Odd (Fintype.card (fixedBy (Fin 9) t)) := by
  classical
  have h2 : 2 ∣ t.support.card := Perm.two_dvd_card_support (by rw [sq]; exact ht)
  have hle : t.support.card ≤ 9 := by
    calc t.support.card ≤ (Finset.univ : Finset (Fin 9)).card := Finset.card_le_univ _
      _ = 9 := by simp
  have hfix : Fintype.card (fixedBy (Fin 9) t) + t.support.card = 9 := by
    have e : Fintype.card (fixedBy (Fin 9) t) = (Finset.univ.filter fun x => t x = x).card := by
      rw [← Fintype.card_subtype]
      rfl
    rw [e, ← Finset.card_union_of_disjoint]
    · rw [show (Finset.univ.filter fun x => t x = x) ∪ t.support = Finset.univ by
        ext x; simp [Perm.mem_support, em]]
      simp
    · rw [Finset.disjoint_left]
      intro x hx hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact (Perm.mem_support.mp hs) hx
  obtain ⟨k, hk⟩ := h2
  refine ⟨4 - k, ?_⟩
  omega

theorem card_fixedPoints_le_eight {t : Perm (Fin 9)} (ht : t ≠ 1) :
    Fintype.card (fixedBy (Fin 9) t) ≤ 8 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, t x ≠ x := by
    by_contra h
    push Not at h
    exact ht (Equiv.ext h)
  have hlt : Fintype.card (fixedBy (Fin 9) t) < Fintype.card (Fin 9) :=
    Fintype.card_subtype_lt (p := fun y => y ∈ fixedBy (Fin 9) t) (x := x) hx
  simpa using Nat.lt_succ_iff.mp hlt

theorem eq_one_of_uniform {T : Subgroup (Perm (Fin 9))} (hcard : Nat.card T = 8)
    (hsq : ∀ t ∈ T, t * t = 1) {f : ℕ}
    (hf : ∀ t ∈ T, t ≠ 1 → Fintype.card (fixedBy (Fin 9) t) = f) : f = 1 := by
  classical
  haveI : Fintype T := Fintype.ofFinite T
  have hT : Fintype.card T = 8 := by rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨t₀, ht₀T, ht₀⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr h
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hodd : Odd f := hf t₀ ht₀T ht₀ ▸ odd_card_fixedPoints (hsq t₀ ht₀T)
  have hle : f ≤ 8 := hf t₀ ht₀T ht₀ ▸ card_fixedPoints_le_eight ht₀
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group T (Fin 9)
  have hfix : ∀ g : T, Fintype.card (fixedBy (Fin 9) g) =
      Fintype.card (fixedBy (Fin 9) (g : Perm (Fin 9))) := fun g => rfl
  have hsum : ∑ g : T, Fintype.card (fixedBy (Fin 9) g) = 9 + 7 * f := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : T))]
    have h1 : Fintype.card (fixedBy (Fin 9) (1 : T)) = 9 := by
      rw [hfix]
      simp
    have hrest : ∀ g ∈ (Finset.univ : Finset T).erase 1, Fintype.card (fixedBy (Fin 9) g) = f := by
      intro g hg
      rw [hfix]
      exact hf g g.2 fun h => (Finset.ne_of_mem_erase hg) (Subtype.ext h)
    rw [h1, Finset.sum_congr rfl hrest, Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hT]
  rw [hsum, hT] at hB
  obtain ⟨m, rfl⟩ := hodd
  omega

theorem exists_common_fixed {T : Subgroup (Perm (Fin 9))}
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (h1 : ∀ t ∈ T, t ≠ 1 → Fintype.card (fixedBy (Fin 9) t) = 1) {t₀ : Perm (Fin 9)}
    (ht₀T : t₀ ∈ T) (ht₀ : t₀ ≠ 1) :
    ∃ p : Fin 9, ∀ t ∈ T, t p = p ∧ (t ≠ 1 → ∀ x, t x = x → x = p) := by
  classical
  obtain ⟨⟨p, hp⟩, hpu⟩ := Fintype.card_eq_one_iff.mp (h1 t₀ ht₀T ht₀)
  have hp' : t₀ p = p := hp
  have hfixT : ∀ t ∈ T, t p = p := by
    intro t htT
    have h : t₀ (t p) = t p := by
      rw [← Perm.mul_apply, hcomm t₀ ht₀T t htT, Perm.mul_apply, hp']
    have := hpu ⟨t p, h⟩
    exact congrArg Subtype.val this
  refine ⟨p, fun t htT => ⟨hfixT t htT, fun ht x hx => ?_⟩⟩
  obtain ⟨⟨q, hq⟩, hqu⟩ := Fintype.card_eq_one_iff.mp (h1 t htT ht)
  have e1 := congrArg Subtype.val (hqu ⟨x, hx⟩)
  have e2 := congrArg Subtype.val (hqu ⟨p, hfixT t htT⟩)
  simp only at e1 e2
  rw [e1, e2]

theorem normalizer_apply_eq {T : Subgroup (Perm (Fin 9))} {p : Fin 9}
    (hp : ∀ t ∈ T, t p = p ∧ (t ≠ 1 → ∀ x, t x = x → x = p)) {t₀ : Perm (Fin 9)}
    (ht₀T : t₀ ∈ T) (ht₀ : t₀ ≠ 1) {n : Perm (Fin 9)}
    (hn : n ∈ Subgroup.normalizer (T : Set (Perm (Fin 9)))) : n p = p := by
  have hmem : n⁻¹ * t₀ * n⁻¹⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) t₀).mp ht₀T
  rw [inv_inv] at hmem
  have hfix : (n⁻¹ * t₀ * n) p = p := (hp _ hmem).1
  have h : t₀ (n p) = n p := by
    have := congrArg n hfix
    simpa [Perm.mul_apply] using this
  exact (hp t₀ ht₀T).2 ht₀ (n p) h

theorem le_index_normalizer {T : Subgroup (Perm (Fin 9))} (hcard : Nat.card T = 8)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hsq : ∀ t ∈ T, t * t = 1) {f : ℕ}
    (hf : ∀ t ∈ T, t ≠ 1 → Fintype.card (fixedBy (Fin 9) t) = f) :
    270 ≤ (Subgroup.normalizer (T : Set (Perm (Fin 9)))).index := by
  classical
  have hf1 := eq_one_of_uniform hcard hsq hf
  subst hf1
  obtain ⟨t₀, ht₀T, ht₀⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr h
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨p, hp⟩ := exists_common_fixed hcomm hf ht₀T ht₀
  set N := Subgroup.normalizer (T : Set (Perm (Fin 9))) with hNdef
  obtain ⟨ω₀, hω₀⟩ : ∃ ω : Fin 9, ω ≠ p := by
    by_cases h : p = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun e => h e.symm⟩
  have hreg : ∀ t ∈ T, t ω₀ = ω₀ → t = 1 := fun t htT h => by
    by_contra ht
    exact hω₀ ((hp t htT).2 ht ω₀ h)
  have hcover : ∀ x : Fin 9, x ≠ p → ∃ t ∈ T, t ω₀ = x := by
    let F : T → {x : Fin 9 // x ≠ p} := fun t => ⟨(t : Perm (Fin 9)) ω₀, fun h => hω₀ (by
      have := congrArg (t : Perm (Fin 9)).symm h
      rw [Equiv.symm_apply_apply] at this
      rw [this]
      have hpt : (t : Perm (Fin 9)) p = p := (hp t t.2).1
      exact ((t : Perm (Fin 9)).symm_apply_eq.mpr hpt.symm))⟩
    have hFi : Function.Injective F := by
      intro a b hab
      have h1 : (a : Perm (Fin 9)) ω₀ = (b : Perm (Fin 9)) ω₀ := congrArg Subtype.val hab
      have h2 : ((b : Perm (Fin 9))⁻¹ * a) ω₀ = ω₀ := by
        rw [Perm.mul_apply, h1]
        exact (b : Perm (Fin 9)).symm_apply_apply ω₀
      have h3 := hreg _ (T.mul_mem (T.inv_mem b.2) a.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3).symm
    haveI : Fintype T := Fintype.ofFinite T
    have hc : Fintype.card T = Fintype.card {x : Fin 9 // x ≠ p} := by
      rw [← Nat.card_eq_fintype_card, hcard, Fintype.card_subtype_compl, Fintype.card_fin,
        Fintype.card_unique]
    have hFs := (Fintype.bijective_iff_injective_and_card F).mpr ⟨hFi, hc⟩
    intro x hx
    obtain ⟨t, ht⟩ := hFs.2 ⟨x, hx⟩
    exact ⟨t, t.2, congrArg Subtype.val ht⟩
  let St : Subgroup N := MulAction.stabilizer N ω₀
  let φ : St →* MulAut T := T.normalizerMonoidHom.comp St.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro n hn
    have hn' : ∀ t : T, ((n : N) : Perm (Fin 9)) * t * ((n : N) : Perm (Fin 9))⁻¹ = t := by
      intro t
      have := congrArg (fun α : MulAut T => ((α t : T) : Perm (Fin 9))) (MonoidHom.mem_ker.mp hn)
      simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    have hω : ((n : N) : Perm (Fin 9)) ω₀ = ω₀ := n.2
    have hall : ∀ x, ((n : N) : Perm (Fin 9)) x = x := by
      intro x
      by_cases hxp : x = p
      · rw [hxp]
        exact normalizer_apply_eq hp ht₀T ht₀ (n : N).2
      · obtain ⟨t, htT, rfl⟩ := hcover x hxp
        have h : ((n : N) : Perm (Fin 9)) * t * ((n : N) : Perm (Fin 9))⁻¹ = t := hn' ⟨t, htT⟩
        have h' : ((n : N) : Perm (Fin 9)) * t = t * ((n : N) : Perm (Fin 9)) :=
          mul_inv_eq_iff_eq_mul.mp h
        rw [← Perm.mul_apply, h', Perm.mul_apply, hω]
    exact Subtype.ext (Subtype.ext (Equiv.ext hall))
  have hSt : Nat.card St ≤ 168 := by
    have h168 := CFSG.GF2Type.Aschbacher1976Full.HS.card_mulAut_eq_168 hcard
      (fun a b => Subtype.ext (hcomm a a.2 b b.2)) (fun t => Subtype.ext (hsq t t.2))
    rw [← h168]
    exact Nat.card_le_card_of_injective φ hφ
  have horb : Nat.card (MulAction.orbit N ω₀) ≤ 8 := by
    have hsub : MulAction.orbit N ω₀ ⊆ {x : Fin 9 | x ≠ p} := by
      rintro _ ⟨n, rfl⟩ h
      apply hω₀
      have hnp : ((n : N) : Perm (Fin 9)) p = p := normalizer_apply_eq hp ht₀T ht₀ n.2
      have e : ((n : N) : Perm (Fin 9)) ω₀ = ((n : N) : Perm (Fin 9)) p := by
        rw [hnp]
        exact h
      exact ((n : N) : Perm (Fin 9)).injective e
    calc Nat.card (MulAction.orbit N ω₀) ≤ Nat.card {x : Fin 9 | x ≠ p} :=
          Nat.card_mono (Set.toFinite _) hsub
      _ = 8 := by
          rw [Nat.card_eq_fintype_card]
          simp [Set.coe_setOf, Fintype.card_subtype_compl]
  have hN : Nat.card N ≤ 1344 := by
    have h1 := Subgroup.card_mul_index St
    rw [MulAction.index_stabilizer] at h1
    calc Nat.card N = Nat.card St * Nat.card (MulAction.orbit N ω₀) := h1.symm
      _ ≤ 168 * 8 := Nat.mul_le_mul hSt horb
      _ = 1344 := by norm_num
  have hS9 : Nat.card (Perm (Fin 9)) = 362880 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h2 := N.card_mul_index
  rw [hS9] at h2
  by_contra hlt
  push Not at hlt
  have : Nat.card N * N.index < 362880 := by
    calc Nat.card N * N.index ≤ 1344 * N.index := Nat.mul_le_mul_right _ hN
      _ < 1344 * 270 := Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
      _ = 362880 := by norm_num
  omega

end CFSG.GF2Type.Smith1979.W4As
