module

public import CFSG.GH74.Generic.S45.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.GH74.Generic.S45 CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
  CFSG.EvenSporadicStandard.HypOne CFSG.ComponentClassification.PerfectAutomorphisms

theorem isPGroup_zpowers_of_pow_four {X : Type*} [Group X] {x : X} (hx : x ^ 4 = 1) :
    IsPGroup 2 (zpowers x) := by
  have h : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hx)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

section KBase

variable {Y : Type} [Group Y] [Finite Y]

theorem kBase_center_eq_bot (h : KBase Y) : center Y = ⊥ := by
  obtain ⟨hs, -, hR⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have h8 : 8 ∣ Nat.card Y := by
    rw [← (hR R).2.2.1]
    exact Subgroup.card_subgroup_dvd_card (R : Subgroup Y)
  refine center_eq_bot_of_isSimpleGroup (fun hp => ?_)
  rcases hp.eq_one_or_self_of_dvd 8 h8 with h1 | h1
  · omega
  · rw [← h1] at hp
    exact absurd hp (by norm_num)

theorem kBase_pow_two_eq_one (h : KBase Y) {x : Y} (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := (isPGroup_zpowers_of_pow_four hx).exists_le_sylow
  have hsq := (h.2.2 R).2.1 ⟨x, hR (mem_zpowers x)⟩
  rw [pow_two]
  exact congrArg Subtype.val hsq

theorem kBase_mulAut_pow_two_eq_one (h : KBase Y) {α : MulAut Y} (hα : α ^ 4 = 1) :
    α ^ 2 = 1 := by
  obtain ⟨g, rfl⟩ := h.2.1 α (isPGroup_zpowers_of_pow_four hα)
  have hinj := conj_injective_of_center_eq_bot (kBase_center_eq_bot h)
  have h4 : g ^ 4 = 1 := hinj (by rw [map_pow, hα, map_one])
  rw [← map_pow, kBase_pow_two_eq_one h h4, map_one]

theorem hypothesisOne_of_kBase (h : KBase Y) : HypothesisOne Y := by
  intro M _ x _ _ B hB hiso
  have : Finite (MulAut Y) := MulEquiv.finite_left
  exact SmallNormalFree.of_forall_pow_four (C := ↥(M ⊓ centralizer ({x} : Set (MulAut Y))))
    (fun c hc => Subtype.ext (kBase_mulAut_pow_two_eq_one h (by
      simpa using congrArg Subtype.val hc))) B hB hiso

theorem odd_index_conj_range_of_kBase (h : KBase Y) :
    Odd (MulAut.conj : Y →* MulAut Y).range.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Y) := MulEquiv.finite_left
  obtain ⟨P⟩ : Nonempty (Sylow 2 (MulAut Y)) := inferInstance
  have hle : (P : Subgroup (MulAut Y)) ≤ (MulAut.conj : Y →* MulAut Y).range := fun α hα => by
    have hα' : IsPGroup 2 (zpowers α) :=
      IsPGroup.to_le P.isPGroup' (zpowers_le.2 hα)
    exact h.2.1 α hα'
  have hnd : ¬ 2 ∣ (MulAut.conj : Y →* MulAut Y).range.index :=
    fun hd => P.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hle))
  exact Nat.not_even_iff_odd.1 fun he => hnd (even_iff_two_dvd.1 he)

end KBase

theorem foursGroupCondition_of_kBase {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (h : KBase (L ⧸ center L)) : CFSG.EvenSmallLie.FoursGroupCondition L := by
  intro φ hφ hout
  exfalso
  have h4 : centerQuotientHom L φ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ← map_mul, hφ, map_one, one_mul]
  obtain ⟨q, hq⟩ := h.2.1 _ (isPGroup_zpowers_of_pow_four h4)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  refine hout m (centerQuotientHom_injective L ?_)
  rw [← hq]
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  change _ = onCenterQuotient (MulAut.conj m) (QuotientGroup.mk' (center L) x)
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply]
  rfl

end CFSG.OddStandard.L2Ree
