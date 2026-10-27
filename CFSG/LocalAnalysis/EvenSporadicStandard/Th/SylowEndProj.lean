module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}

theorem ThCyc.t_not_mem_L (H : ThCyc G L R t) : t ∉ L := by
  intro h
  exact H.not_conj_mem 1 (by simpa using h)

omit [Finite G] in
theorem le_normalizer_zpowers_of_commute {v : G} {M : Subgroup G} (hc : ∀ x ∈ M, x * v = v * x) :
    M ≤ normalizer ((zpowers v : Subgroup G) : Set G) := fun x hx =>
  centralizer_le_normalizer _ (mem_centralizer_iff.2 fun h hh => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (((show Commute x v from hc x hx).symm).zpow_left k).eq)

theorem ThCyc.centralizer_conj_eq (H : ThCyc G L R t) (c : G) :
    centralizer ({c⁻¹ * t * c} : Set G) =
      L.map (MulAut.conj c⁻¹).toMonoidHom ⊔ zpowers (c⁻¹ * t * c) := by
  have h1 := map_centralizer_singleton (MulAut.conj c⁻¹) t
  have e : (MulAut.conj c⁻¹) t = c⁻¹ * t * c := by simp
  rw [e, H.centralizer_eq_zpowers, Subgroup.map_sup] at h1
  rw [← h1, ← e]
  congr 1
  exact MonoidHom.map_zpowers _ t

section

variable (H : ThCyc G L R t) {c : G} {M : Subgroup G}

include H

theorem ThCyc.conj_sq (c : G) : (c⁻¹ * t * c) ^ 2 = 1 := by
  calc (c⁻¹ * t * c) ^ 2 = c⁻¹ * t ^ 2 * c := by simp only [sq]; group
    _ = 1 := by rw [H.sq_t]; group

theorem ThCyc.conj_orderOf (c : G) : orderOf (c⁻¹ * t * c) = 2 := by
  have := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective t
  simpa using this.trans H.order_two

theorem ThCyc.conj_not_mem (c : G) : c⁻¹ * t * c ∉ L.map (MulAut.conj c⁻¹).toMonoidHom := by
  rintro ⟨x, hx, hxv⟩
  apply H.t_not_mem_L
  have : x = t := by
    simpa [MulAut.conj_apply] using hxv
  rwa [this] at hx

theorem ThCyc.card_eq_two_mul_card_inf (hM : M ≤ centralizer ({c⁻¹ * t * c} : Set G))
    (hvM : c⁻¹ * t * c ∈ M) :
    Nat.card M = 2 * Nat.card ↥(M ⊓ L.map (MulAut.conj c⁻¹).toMonoidHom) := by
  set v := c⁻¹ * t * c with hv
  set L' := L.map (MulAut.conj c⁻¹).toMonoidHom with hL'
  have hv2 : v ^ 2 = 1 := H.conj_sq c
  have hvo : orderOf v = 2 := H.conj_orderOf c
  have hC : centralizer ({v} : Set G) = L' ⊔ zpowers v := H.centralizer_conj_eq c
  have hL'c : ∀ x ∈ L', x * v = v * x := fun x hx => by
    have : x ∈ centralizer ({v} : Set G) := by
      rw [hC]
      exact mem_sup_left hx
    exact mem_centralizer_singleton_iff.1 this
  have hcomm : zpowers v ≤ centralizer (L' : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => hL'c y hy
  have hMeq : M = (M ⊓ L') ⊔ zpowers v := by
    refine le_antisymm (fun m hm => ?_) (sup_le inf_le_left (zpowers_le.2 hvM))
    have hm' : m ∈ L' ⊔ zpowers v := by rw [← hC]; exact hM hm
    obtain ⟨l, hl, r, hr, rfl⟩ := exists_mul_of_mem_sup hcomm hm'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hrM : v ^ k ∈ M := M.zpow_mem hvM k
    have hlM : l ∈ M := by
      have := M.mul_mem hm (M.inv_mem hrM)
      simpa using this
    exact mul_mem_sup ⟨hlM, hl⟩ (mem_zpowers_iff.2 ⟨k, rfl⟩)
  have hinf : (M ⊓ L') ⊓ zpowers v = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨-, hxL⟩, hxv⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxv
    rcases zpow_eq_one_or_self hv2 k with h | h
    · rw [h]
      exact one_mem _
    · have hvL' : v ∈ L' := by rw [← h]; exact hxL
      exact absurd hvL' (H.conj_not_mem c)
  have hnorm : (M ⊓ L') ≤ normalizer ((zpowers v : Subgroup G) : Set G) :=
    le_normalizer_zpowers_of_commute fun x hx => hL'c x hx.2
  have hcard := SylowEnd.card_sup_mul_card_inf hnorm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hvo, ← hMeq] at hcard
  rw [hcard, mul_comm]

theorem ThCyc.card_le_of_le_centralizer_conj {m : ℕ}
    (hM : M ≤ centralizer ({c⁻¹ * t * c} : Set G)) (hvM : c⁻¹ * t * c ∈ M)
    (hbound : ∀ Y : Subgroup G, Y ≤ M → Y ≤ L.map (MulAut.conj c⁻¹).toMonoidHom →
      Nat.card Y ≤ m) : Nat.card M ≤ 2 * m := by
  rw [H.card_eq_two_mul_card_inf hM hvM]
  exact Nat.mul_le_mul_left 2 (hbound _ inf_le_left inf_le_right)

theorem ThCyc.card_sup_conj {K : Subgroup G} {c : G}
    (hc : ∀ x ∈ K, x * (c⁻¹ * t * c) = (c⁻¹ * t * c) * x)
    (hu : c⁻¹ * t * c ∉ K) : Nat.card ↥(K ⊔ zpowers (c⁻¹ * t * c)) = 2 * Nat.card K := by
  have h := SylowEnd.card_sup_mul_card_inf (le_normalizer_zpowers_of_commute hc)
  have hinf : K ⊓ zpowers (c⁻¹ * t * c) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxS, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    rcases zpow_eq_one_or_self (H.conj_sq c) k with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (h ▸ hxS) hu
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, H.conj_orderOf c] at h
  rw [h, mul_comm]

theorem ThCyc.card_lt_of_elementary
    (hEl : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → (∀ y ∈ Y, y ^ 2 = 1) → Nat.card Y ≤ 2 ^ 7)
    {E : Subgroup G} (hle : E ≤ centralizer ({c⁻¹ * t * c} : Set G))
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x ^ 2 = 1)
    (hvE : c⁻¹ * t * c ∉ E) : Nat.card E < 2 ^ 8 := by
  set v := c⁻¹ * t * c with hv
  have hvc : ∀ x ∈ E, x * v = v * x := fun x hx => mem_centralizer_singleton_iff.1 (hle hx)
  have hM : E ⊔ zpowers v ≤ centralizer ({v} : Set G) :=
    sup_le hle (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hvM : v ∈ E ⊔ zpowers v := mem_sup_right (mem_zpowers v)
  have hab' := SylowEnd.sup_zpowers_comm hvc hab
  have hsq' := SylowEnd.sup_zpowers_sq (H.conj_sq c) hvc hsq
  have h := H.card_le_of_le_centralizer_conj (m := 2 ^ 7) hM hvM fun Y hYM hYL =>
    hEl c⁻¹ Y hYL (fun x hx y hy => hab' x (hYM hx) y (hYM hy)) (fun y hy => hsq' y (hYM hy))
  have h2 : Nat.card ↥(E ⊔ zpowers v) = 2 * Nat.card E := H.card_sup_conj hvc hvE
  omega

theorem ThCyc.card_le_of_abelian
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hM : M ≤ centralizer ({c⁻¹ * t * c} : Set G)) (hvM : c⁻¹ * t * c ∈ M)
    (hab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (h2 : IsPGroup 2 M) : Nat.card M ≤ 2 ^ 9 := by
  have h := H.card_le_of_le_centralizer_conj (m := 2 ^ 8) hM hvM fun Y hYM hYL =>
    hAb c⁻¹ Y hYL (h2.to_le hYM) (fun x hx y hy => hab x (hYM hx) y (hYM hy))
  rw [show 2 ^ 9 = 2 * 2 ^ 8 by norm_num]
  exact h


theorem ThCyc.card_sup_zpowers {S A B : Subgroup G} {z : G} (W : ThLocalIn L S A B z) :
    Nat.card ↥(S ⊔ zpowers t) = 2 * Nat.card S := by
  have hSc : ∀ x ∈ S, x * t = t * x := fun x hx => (H.comm_of_mem_L (W.S_le hx)).symm
  have h := SylowEnd.card_sup_mul_card_inf (le_normalizer_zpowers_of_commute hSc)
  have hinf : S ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxS, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (W.S_le (h ▸ hxS)) H.t_not_mem_L
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, H.order_two] at h
  rw [h, mul_comm]

theorem ThCyc.isPGroup_zpowers_conj (c : G) : IsPGroup 2 (zpowers (c⁻¹ * t * c)) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, H.conj_orderOf c, pow_one]

end

end CFSG.EvenSporadicStandard.ThStd
