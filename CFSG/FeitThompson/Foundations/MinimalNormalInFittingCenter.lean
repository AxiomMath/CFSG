module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open MulAction Subgroup

variable {G : Type*} [Group G]

theorem map_center_subtype_eq_inf_centralizer (H : Subgroup G) :
    (center ↥H).map H.subtype = H ⊓ centralizer (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.2 fun h hh => by
      simpa [Subtype.ext_iff] using mem_center_iff.1 hy ⟨h, hh⟩⟩
  · rintro ⟨hx, hxc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.2 fun g => by
      simpa [Subtype.ext_iff] using mem_centralizer_iff.1 hxc g g.2, rfl⟩

theorem le_map_center_subtype_iff {H K : Subgroup G} :
    K ≤ (center ↥H).map H.subtype ↔ K ≤ H ∧ K ≤ centralizer (H : Set G) := by
  rw [map_center_subtype_eq_inf_centralizer, le_inf_iff]

theorem subgroupOf_le_center_iff {H K : Subgroup G} (hKH : K ≤ H) :
    K.subgroupOf H ≤ center ↥H ↔ K ≤ centralizer (H : Set G) := by
  constructor
  · intro h x hx
    have h2 : (⟨x, hKH hx⟩ : ↥H) ∈ center ↥H := h (mem_subgroupOf.2 hx)
    exact mem_centralizer_iff.2 fun y hy => by
      simpa [Subtype.ext_iff] using mem_center_iff.1 h2 ⟨y, hy⟩
  · intro h x hx
    exact mem_center_iff.2 fun g => by
      simpa [Subtype.ext_iff] using mem_centralizer_iff.1 (h (mem_subgroupOf.1 hx)) g g.2

theorem inf_centralizer_ne_bot_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime)
    {M R : Subgroup G} [M.Normal] (hR : IsPGroup p R) (hM : p ∣ Nat.card M) :
    M ⊓ centralizer (R : Set G) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, hRcard⟩ := IsPGroup.iff_card.1 hR
  let _act : MulAction ↥R ↥M :=
    MulAction.compHom _ (ConjAct.toConjAct.toMonoidHom.comp R.subtype)
  have hsmul : ∀ (r : ↥R) (m : ↥M), ((r • m : ↥M) : G) = (r : G) * (m : G) * (r : G)⁻¹ :=
    fun _ _ => rfl
  have hone : (1 : ↥M) ∈ fixedPoints ↥R ↥M := fun r => Subtype.ext (by simp [hsmul])
  have : Nonempty (fixedPoints ↥R ↥M) := ⟨⟨1, hone⟩⟩
  have hcong : Nat.card ↥M ≡ Nat.card (fixedPoints ↥R ↥M) [MOD p] :=
    natCard_modEq_natCard_fixedPoints (a := a) hRcard
  have hdvd : p ∣ Nat.card (fixedPoints ↥R ↥M) :=
    Nat.modEq_zero_iff_dvd.1 (hcong.symm.trans (Nat.modEq_zero_iff_dvd.2 hM))
  have hpos : 0 < Nat.card (fixedPoints ↥R ↥M) := Nat.card_pos
  have h1 : 1 < Nat.card (fixedPoints ↥R ↥M) := by
    rcases hdvd with ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp [hk] at hpos
    · calc 1 < p := hp.one_lt
        _ ≤ p * k := Nat.le_mul_of_pos_right p hk'
        _ = _ := hk.symm
  have : Nontrivial (fixedPoints ↥R ↥M) := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨m, hm⟩, hmne⟩ := exists_ne (⟨(1 : ↥M), hone⟩ : fixedPoints ↥R ↥M)
  have hm1 : (m : G) ≠ 1 := fun h => hmne (by ext; simpa using h)
  intro hbot
  have hmem : (m : G) ∈ M ⊓ centralizer (R : Set G) := by
    refine ⟨m.2, mem_centralizer_iff.2 fun r hr => ?_⟩
    have h2 := congrArg (Subtype.val (p := fun x => x ∈ M)) (hm ⟨r, hr⟩)
    rw [hsmul] at h2
    simpa using mul_inv_eq_iff_eq_mul.1 h2
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hm1 hmem

theorem le_centralizer_fittingRaw [Finite G] {M : Subgroup G} [M.Normal] [Group.IsSolvable ↥M]
    (hM : M ≠ ⊥) (hmin : ∀ K : Subgroup G, K.Normal → K < M → K = ⊥) :
    M ≤ centralizer (fittingRaw G : Set G) := by
  obtain ⟨r, d, hr, hd, hcard⟩ :=
    exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot hM hmin
  have hrdvd : r ∣ Nat.card ↥M := by
    rw [hcard]; exact dvd_pow_self r (by omega)
  have := pCore_normal r G
  have hcR : M ⊓ centralizer ((pCore r G : Subgroup G) : Set G) = M := by
    have hne := inf_centralizer_ne_bot_of_isPGroup hr (M := M) (isPGroup_pCore hr G) hrdvd
    rcases lt_or_eq_of_le (inf_le_left : M ⊓ centralizer ((pCore r G : Subgroup G) : Set G) ≤ M)
      with h | h
    · exact absurd (hmin _ inferInstance h) hne
    · exact h
  have hMcR : M ≤ centralizer ((pCore r G : Subgroup G) : Set G) := hcR ▸ inf_le_right
  rw [le_centralizer_iff]
  refine fittingRaw_le fun N hN hN' => ?_
  obtain ⟨q, hq, hNq⟩ := isPrimePowerOrder_iff_isPGroup.1 hN'
  by_cases hqr : q = r
  · subst hqr
    have hNle : N ≤ pCore q G := le_pCore hq hN hNq
    exact le_centralizer_iff.1 (hMcR.trans (centralizer_le (by exact_mod_cast hNle)))
  ·
    have := hN
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨a, hNcard⟩ := IsPGroup.iff_card.1 hNq
    have hcop : (Nat.card ↥N).Coprime (Nat.card ↥M) := by
      rw [hNcard, hcard]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hr).2 hqr)
    intro x hx
    exact mem_centralizer_iff.2 fun y hy =>
      (mul_comm_of_normal_of_coprime_natCard N M hcop hx hy).symm

theorem le_map_center_fittingRaw [Finite G] {M : Subgroup G} [M.Normal] [Group.IsSolvable ↥M]
    (hM : M ≠ ⊥) (hmin : ∀ K : Subgroup G, K.Normal → K < M → K = ⊥) :
    M ≤ (center ↥(fittingRaw G)).map (fittingRaw G).subtype := by
  obtain ⟨r, _, hr, _, hcard⟩ :=
    exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot hM hmin
  rw [map_center_subtype_eq_inf_centralizer]
  exact le_inf (le_fittingRaw_of_isPGroup hr ‹M.Normal› (IsPGroup.of_card hcard))
    (le_centralizer_fittingRaw hM hmin)

theorem subgroupOf_fittingRaw_le_center [Finite G] {M : Subgroup G} [M.Normal]
    [Group.IsSolvable ↥M] (hM : M ≠ ⊥) (hmin : ∀ K : Subgroup G, K.Normal → K < M → K = ⊥) :
    M.subgroupOf (fittingRaw G) ≤ center ↥(fittingRaw G) := by
  obtain ⟨r, _, hr, _, hcard⟩ :=
    exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot hM hmin
  exact (subgroupOf_le_center_iff
    (le_fittingRaw_of_isPGroup hr ‹M.Normal› (IsPGroup.of_card hcard))).2
    (le_centralizer_fittingRaw hM hmin)

theorem le_fittingRaw_of_isSolvable_of_forall_normal_lt_eq_bot [Finite G] {M : Subgroup G}
    [M.Normal] [Group.IsSolvable ↥M] (hM : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K < M → K = ⊥) : M ≤ fittingRaw G :=
  (le_map_center_subtype_iff.1 (le_map_center_fittingRaw hM hmin)).1

end

end CFSG.FeitThompson
