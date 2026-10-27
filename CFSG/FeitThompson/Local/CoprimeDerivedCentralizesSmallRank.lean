module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Local.RankTwoSectionChiefFactorCentralization
import CFSG.FeitThompson.Local.PrimePowerActionFromNormalFactors
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

private theorem card_lt_card_of_lt [Finite G] {H K : Subgroup G} (h : H < K) :
    Nat.card ↥H < Nat.card ↥K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun he =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le he.ge)

theorem commutator_eq_bot_of_commutator_le_of_commutator_eq_bot [Finite G] {N Y D : Subgroup G}
    [N.Normal] [Y.Normal] [Group.IsSolvable ↥N]
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥N)) (hDN : ⁅D, N⁆ ≤ Y) (hDY : ⁅D, Y⁆ = ⊥) :
    ⁅D, N⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hDY ⊢
  intro g hg
  have hYNnormal : (Y.subgroupOf N).Normal := (‹Y.Normal›).subgroupOf _
  set c : MulAut ↥N := MulAut.conjNormal g with hc
  have hord : orderOf c ∣ Nat.card ↥D :=
    (orderOf_map_dvd _ g).trans (Subgroup.orderOf_dvd_natCard D hg)
  have hfix : ∀ v ∈ Y.subgroupOf N, c v = v := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    refine Subtype.ext ?_
    rw [hc, MulAut.conjNormal_apply]
    have hcomm := (Subgroup.mem_centralizer_iff.1 (hDY hg)) _ hv
    calc g * (v : G) * g⁻¹ = ((v : G) * g) * g⁻¹ := by rw [hcomm]
      _ = (v : G) := by group
  have hquot : ∀ v : ↥N, v⁻¹ * c v ∈ Y.subgroupOf N := by
    intro v
    rw [Subgroup.mem_subgroupOf]
    have hmem : (v : G)⁻¹ * g * (v : G) * g⁻¹ ∈ ⁅D, N⁆ := by
      have h := Subgroup.commutator_mem_commutator (H₁ := N) (H₂ := D) (N.inv_mem v.2) hg
      rw [Subgroup.commutator_comm] at h
      rwa [commutatorElement_def, inv_inv] at h
    have hval : ((v⁻¹ * c v : ↥N) : G) = (v : G)⁻¹ * g * (v : G) * g⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hc, MulAut.conjNormal_apply]
      group
    rw [hval]
    exact hDN hmem
  have hc1 : c = 1 :=
    eq_one_of_pointwise_fixing_of_trivial_on_quotient (Nat.Coprime.coprime_dvd_left hord hcop)
      hfix hquot
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hgx : g * x * g⁻¹ = x := by
    have := congrArg (fun (f : MulAut ↥N) => (f ⟨x, hx⟩ : G)) hc1
    simpa [hc] using this
  calc x * g = (g * x * g⁻¹) * g := by rw [hgx]
    _ = g * x := by group

theorem commutator_eq_bot_of_le_commutator_of_coprime [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {N D : Subgroup G} [N.Normal]
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥N ≤ 2)
    (hD : D ≤ _root_.commutator G) (hcop : (Nat.card ↥D).Coprime (Nat.card ↥N)) :
    ⁅D, N⁆ = ⊥ := by
  suffices H : ∀ n : ℕ, ∀ M : Subgroup G, M.Normal → Nat.card ↥M ≤ n →
      (∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥M ≤ 2) →
      (Nat.card ↥D).Coprime (Nat.card ↥M) → ⁅D, M⁆ = ⊥ from
    H (Nat.card ↥N) N ‹N.Normal› le_rfl hrank hcop
  intro n
  induction n with
  | zero =>
    intro M _ hle _ _
    have : 0 < Nat.card ↥M := Nat.card_pos
    omega
  | succ n ih =>
    intro M hM hle hrankM hcopM
    have := hM
    rcases eq_or_ne M ⊥ with rfl | hMbot
    · simp
    · obtain ⟨Y, hY⟩ := exists_isChiefFactor M hMbot
      have := hY.normal_den
      obtain ⟨q, hq, k, hk⟩ := exists_prime_relIndex_eq_pow_of_isChiefFactor hY
      have h1 : ⁅_root_.commutator G, M⁆ ≤ Y :=
        commutator_le_of_isChiefFactor_of_elementaryAbelianPRank_le_two hodd hq (hrankM q hq) hY
          ⟨k, hk⟩ le_rfl
      have hYM : Y ≤ M := hY.le
      have hcardY : Nat.card ↥Y ≤ n := by
        have := card_lt_card_of_lt hY.lt
        omega
      have hDY : ⁅D, Y⁆ = ⊥ := ih Y hY.normal_den hcardY
        (fun r hr => (elementaryAbelianPRank_le_of_le hr.one_lt hYM).trans (hrankM r hr))
        (hcopM.coprime_dvd_right (Subgroup.card_dvd_of_le hYM))
      exact commutator_eq_bot_of_commutator_le_of_commutator_eq_bot hcopM
        ((Subgroup.commutator_mono hD le_rfl).trans h1) hDY

theorem le_centralizer_of_le_commutator_of_coprime [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {N D : Subgroup G} [N.Normal]
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥N ≤ 2)
    (hD : D ≤ _root_.commutator G) (hcop : (Nat.card ↥D).Coprime (Nat.card ↥N)) :
    D ≤ Subgroup.centralizer (N : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (commutator_eq_bot_of_le_commutator_of_coprime hodd hrank hD hcop)

theorem commutator_eq_bot_of_le_commutator_of_coprime' [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {N D : Subgroup G} [N.Normal]
    (hrank : ∀ q : ℕ, q.Prime → elementaryAbelianPRank q ↥N ≤ 2)
    (hD : D ≤ Subgroup.closure {g : G | ∃ a ∈ (⊤ : Subgroup G), ∃ b ∈ (⊤ : Subgroup G),
      a⁻¹ * b⁻¹ * a * b = g})
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥N)) :
    Subgroup.closure {g : G | ∃ a ∈ D, ∃ b ∈ N, a⁻¹ * b⁻¹ * a * b = g} = ⊥ := by
  rw [closure_setOf_inv_mul_inv_mul_mul] at hD ⊢
  rw [← _root_.commutator_def] at hD
  exact commutator_eq_bot_of_le_commutator_of_coprime hodd hrank hD hcop

end

end CFSG.FeitThompson
