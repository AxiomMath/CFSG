module

public import CFSG.GH74.QTGen4.Leaves.Rank5
public import CFSG.Quasithin.Vol2.Ch12Sec4N6Ctx

public section

namespace CFSG.Quasithin.H13.N1246.Ctx

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]
  (c : Ctx T L V E z v)
include c

theorem T_le_normalizer_L : T ≤ Subgroup.normalizer (L : Set G) := by
  rw [c.f.MN]
  exact c.f.T_le

theorem R_le_Q : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have hnorm : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.le_normalizer (H := L)).trans (normalizer_le_normalizer_pCoreOf 2 L)
    · exact c.T_le_normalizer_L.trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hp : IsPGroup 2 (pCoreOf 2 L) := pCoreOf_isPGroup 2 L
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) hnorm hp

theorem comm_of_gen4 (hG : CFSG.GH74.Gen4 G) (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) :
    ⁅pCoreOf 2 L, pCoreOf 2 (L ⊔ T)⁆ = ⊥ := by
  classical
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set R := pCoreOf 2 L with hRdef
  have hRQ : R ≤ Q := c.R_le_Q
  have hRL : R ≤ L := pCoreOf_le 2 L
  have hQC : ∀ q ∈ Q, ∀ w ∈ V, q * w = w * q := fun q hq w hw => by
    have : q ∈ T ⊓ Subgroup.centralizer (V : Set G) := c.Q ▸ hq
    exact (Subgroup.mem_centralizer_iff.1 this.2 w hw).symm
  have hLQ : ⁅L, Q⁆ = V := by rw [Subgroup.commutator_comm, hcomm]
  have hVQ : V ≤ Q := c.V_le_Q
  have h1 : ⁅⁅Q, L⁆, R⁆ = ⊥ := by
    rw [hcomm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hQC r (hRQ hr) w hw
  have h2 : ⁅⁅L, R⁆, Q⁆ = ⊥ := by
    have hLR : ⁅L, R⁆ ≤ V := by
      rw [← hLQ]
      exact Subgroup.commutator_mono le_rfl hRQ
    refine le_bot_iff.1 ((Subgroup.commutator_mono hLR le_rfl).trans ?_)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hQC q hq w hw
  have h3 : ⁅⁅R, Q⁆, L⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hcentRQ : ∀ r ∈ R, ∀ q ∈ Q, ∀ l ∈ L, l * ⁅r, q⁆ = ⁅r, q⁆ * l := by
    intro r hr q hq l hl
    have hmem : ⁅r, q⁆ ∈ ⁅R, Q⁆ := Subgroup.commutator_mem_commutator hr hq
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3) hmem
    exact Subgroup.mem_centralizer_iff.1 this l hl
  have hsq : ∀ x ∈ Q, x ^ 2 ∈ Subgroup.centralizer (L : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hw : ⁅l, x⁆ ∈ V := hLQ ▸ Subgroup.commutator_mem_commutator hl hx
    have hxw : x * ⁅l, x⁆ = ⁅l, x⁆ * x := hQC x hx _ hw
    have hww : ⁅l, x⁆ * ⁅l, x⁆ = 1 := by
      rw [← pow_two]
      exact c.f.sq _ hw
    have e : l * x = ⁅l, x⁆ * (x * l) := by
      rw [commutatorElement_def]; group
    calc l * x ^ 2 = (l * x) * x := by rw [pow_two, mul_assoc]
      _ = ⁅l, x⁆ * (x * l) * x := by rw [e]
      _ = ⁅l, x⁆ * x * (l * x) := by simp only [mul_assoc]
      _ = ⁅l, x⁆ * x * (⁅l, x⁆ * (x * l)) := by rw [e]
      _ = ⁅l, x⁆ * (x * ⁅l, x⁆) * (x * l) := by simp only [mul_assoc]
      _ = ⁅l, x⁆ * (⁅l, x⁆ * x) * (x * l) := by rw [hxw]
      _ = (⁅l, x⁆ * ⁅l, x⁆) * (x * x) * l := by simp only [mul_assoc]
      _ = x ^ 2 * l := by rw [hww, one_mul, pow_two]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hcV : ⁅r, q⁆ ∈ V := hLQ ▸ Subgroup.commutator_mem_commutator (hRL hr) hq
  have hcC : ⁅r, q⁆ ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => hcentRQ r hr q hq l hl
  have hcz : ⁅r, q⁆ ∈ Subgroup.zpowers z := c.f.zV ▸ ⟨hcV, hcC⟩
  have hz2 : z ^ 2 = 1 := c.f.order ▸ pow_orderOf_eq_one z
  by_cases h1' : ⁅r, q⁆ = 1
  · exact (commutatorElement_eq_one_iff_mul_comm.1 h1').symm
  · exfalso
    have hrq : ⁅r, q⁆ = z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcz
      rw [← hk] at h1' ⊢
      have hk2 : z ^ k = z ^ (k % 2) := by
        have := zpow_mod_orderOf z k
        rw [c.f.order] at this
        exact_mod_cast this.symm
      rw [hk2] at h1' ⊢
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [h] at h1'; simp at h1'
      · rw [h]; simp
    refine CFSG.GH74.QTGen4.Leaves.rank5_false hG (Q := Q) (V := V) (C := Subgroup.centralizer (L : Set G)) (z := z)
      (r := r) (q := q) (pCoreOf_isPGroup 2 (L ⊔ T)) hVQ
      (fun a ha b hb => congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩))
      c.f.sq c.card16 c.f.order c.f.zV (hRQ hr) hq (hQC r (hRQ hr)) (hQC q hq)
      (hsq r (hRQ hr)) (hsq q hq) ?_
    rw [← commutatorElement_def]
    exact hrq

end CFSG.Quasithin.H13.N1246.Ctx
