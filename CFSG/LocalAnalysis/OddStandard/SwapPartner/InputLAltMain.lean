module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLAlt
import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPermSimple
import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLSchur
import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLAltSetup

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

variable {X : Type*} [Group X] [Finite X] {t : X} {Sg V K : Subgroup X}

private theorem swap_mul_swap_mem_altFixingMoved {m : ℕ} {π : Perm (Fin m)} {a b c d : Fin m} (ha : π a = a)
    (hb : π b = b) (hc : π c = c) (hd : π d = d) (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ altFixingMoved π := by
  refine mem_altFixingMoved.mpr ⟨?_, fun x hx => ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]
    decide
  · have hxa : x ≠ a := fun h => hx (by rw [h]; exact ha)
    have hxb : x ≠ b := fun h => hx (by rw [h]; exact hb)
    have hxc : x ≠ c := fun h => hx (by rw [h]; exact hc)
    have hxd : x ≠ d := fun h => hx (by rw [h]; exact hd)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

private theorem klein_four_comm {m : ℕ} {a b c d : Fin m} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d * (swap a c * swap b d) = swap a c * swap b d * (swap a b * swap c d) := by
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have hdc := hcd.symm
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    simp [swap_apply_of_ne_of_ne, *]
  by_cases hxb : x = b
  · subst hxb
    simp [swap_apply_of_ne_of_ne, *]
  by_cases hxc : x = c
  · subst hxc
    simp [swap_apply_of_ne_of_ne, *]
  by_cases hxd : x = d
  · subst hxd
    simp [swap_apply_of_ne_of_ne, *]
  simp [swap_apply_of_ne_of_ne, *]

private theorem center_eq_bot_of_fixed (hS : SwapShape t Sg V) (hKp : Group.IsPerfect K)
    (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ} (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)} (hAeq : imageAbar Sg K e = altFixingMoved π)
    (hf : Fintype.card {x : Fin m // π x = x} = 8) (h8 : 8 ≤ m) : Subgroup.center K = ⊥ := by
  obtain ⟨emb⟩ : Nonempty (Fin 4 ↪ {x : Fin m // π x = x}) :=
    Function.Embedding.nonempty_of_card_le (by simp [hf])
  have hne : ∀ i j : Fin 4, i ≠ j → (emb i : Fin m) ≠ emb j := fun i j hij h =>
    hij (emb.injective (Subtype.ext h))
  have hab := hne 0 1 (by decide)
  have hac := hne 0 2 (by decide)
  have had := hne 0 3 (by decide)
  have hbc := hne 1 2 (by decide)
  have hbd := hne 1 3 (by decide)
  have hcd := hne 2 3 (by decide)
  have h₁ : swap (emb 0 : Fin m) (emb 1) * swap (emb 2 : Fin m) (emb 3) ∈ imageAbar Sg K e := by
    rw [hAeq]
    exact swap_mul_swap_mem_altFixingMoved (emb 0).2 (emb 1).2 (emb 2).2 (emb 3).2 hab hcd
  have h₂ : swap (emb 0 : Fin m) (emb 2) * swap (emb 1 : Fin m) (emb 3) ∈ imageAbar Sg K e := by
    rw [hAeq]
    exact swap_mul_swap_mem_altFixingMoved (emb 0).2 (emb 2).2 (emb 1).2 (emb 3).2 hac hbd
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_commuting_lifts hS hA e h₁ h₂ (klein_four_comm hab hac had hbc hbd hcd)
  let q : K →* alternatingGroup (Fin m) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : ∀ k : K, q k = 1 ↔ k ∈ center K := fun k => by
    change e (QuotientGroup.mk k) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  have hker : q.ker ≤ center K := fun k hk => (hqk k).mp hk
  have hbot := ker_eq_bot_of_commuting_lifts hKp h8 q hq hker hab hac had hbc hbd hcd hx hy hxy
  refine le_antisymm (fun k hk => ?_) bot_le
  have : k ∈ q.ker := (hqk k).mpr hk
  rw [hbot] at this
  exact this

theorem eq_ten_of_alternating [K.Normal] (hS : SwapShape t Sg V) (hKq : CFSG.IsQuasisimple K)
    (hA : ⁅Sg, Sg⁆ ≤ K) (hne : ⁅Sg, Sg⁆ ≠ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    m = 10 ∧ Subgroup.center K = ⊥ := by
  have hKp : Group.IsPerfect K := hKq.1
  have hK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKp
  have ht : t * t = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hS.order_eq])
  have h8 : 8 ≤ m := eight_le hS hA e
  obtain ⟨π, hπ2, hπ⟩ := exists_perm_intertwining ht (by omega) (by omega) e
  have hπ1 : π ≠ 1 := pi_ne_one hS hK hne hA e hπ
  obtain ⟨hf, hk, hAeq⟩ := card_fixed_eq_eight hπ2 hπ1 (imageAbar_le hS e hπ)
    (card_imageAbar hS hA e) (isSimpleGroup_imageAbar hS hA e) (card_alt_inf_centralizer_le hS e hπ)
  have hsum := card_fixed_add_two_mul_card_cycleType hπ2
  have hk1 : 1 ≤ Multiset.card π.cycleType := by
    rcases Nat.eq_zero_or_pos (Multiset.card π.cycleType) with h | h
    · exact absurd (Equiv.Perm.cycleType_eq_zero.mp (Multiset.card_eq_zero.mp h)) hπ1
    · exact h
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_fixed hS hKp hA e hAeq hf h8
  refine ⟨?_, hZ⟩
  by_contra hm10
  have hm12 : m = 12 := by omega
  subst hm12
  exact false_of_twelve hS e hZ hπ2 hπ hf

end CFSG.OddStandard.AltStdSec.SwapPartner
