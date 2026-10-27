module

public import CFSG.ClassicalInvolution.AschTight.Hall196Wr3
public import CFSG.ClassicalInvolution.AschTight.S1911Eta3

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem isSL2ModOdd_member (hd : Sec19Data p f K z S W) : IsSL2ModOdd K (p ^ f) := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      have h5 := hd.tight.branch.five
      rw [h, pow_zero] at h5
      omega
    · exact h
  exact ⟨p, f, inferInstance, hd.tight.branch.odd, hf, rfl, hd.tight.branch.member.nonempty_equiv⟩

variable [IsSimpleGroup G]

theorem sup_member_eq (hd : Sec19DataT p f K z S W L t V) : W ⊔ K = K ⊔ V := by
  conv_lhs => rw [sup_eq_inf_sup hd]
  apply le_antisymm
  · exact sup_le (sup_le (inf_le_left.trans le_sup_left) le_sup_right) le_sup_left
  · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)

theorem exists_eq_zpowers_V (hd : Sec19DataT p f K z S W L t V) :
    ∃ v ∈ V, V = Subgroup.zpowers v := by
  obtain ⟨-, -, -, -, -, -, hVcyc, -, -⟩ :=
    (hypOmegaMod_of_tightD hd.tight).exists_data_of_mem_USet hd.tight.branch.odd hd.memV
  obtain ⟨a, ha⟩ := hVcyc.exists_generator
  exact ⟨a, a.2, Hall196.eq_zpowers_of_generator ha⟩

theorem isSL2Three_sup_member (hd : Sec19DataT p f K z S W L t V) :
    IsSL2Three (W ⊔ K) K (p ^ f) where
  le := le_sup_right
  normal := sup_le (fun w hw => mem_normalizer_of_mem_W hd.toSec19Data hw)
    Subgroup.le_normalizer
  sl2 := isSL2ModOdd_member hd.toSec19Data
  cyclic := by
    obtain ⟨v, hvV, hV⟩ := exists_eq_zpowers_V hd
    refine ⟨v, (le_sup_left : W ≤ W ⊔ K) (hd.leW hvV), ?_, ?_⟩
    · exact S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hd.hWS (hd.leW hvV)))
    · rw [sup_member_eq hd, hV]
  wreathed := fun P hP => by
    have h₀ : IsSylow2In ((S : Subgroup G) ⊓ K ⊔ V) (W ⊔ K) := by
      rw [sup_member_eq hd]
      exact Hall196.isSylow2In_sup_of_sec19DataT hd (isSylow2In_inf hd.toSec19Data)
        (fun v hv => le_normalizer_inf hd.toSec19Data (hd.hWS (hd.leW hv)))
    exact Hall196.IsWreathed.of_isSylow2In h₀ (Hall196.isWreathed_inf_sup hd) hP

omit [Finite G] [IsSimpleGroup G] in
theorem exists_pow_eq_mul {N : Subgroup G} (hNK : N ≤ Subgroup.normalizer (K : Set G))
    {k n : G} (hk : k ∈ K) (hn : n ∈ N) : ∀ j : ℕ, ∃ c ∈ K, (k * n) ^ j = c * n ^ j := by
  intro j
  induction j with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc, hj⟩ := ih
    have hnk : n ^ j * k * (n ^ j)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hNK hn) j) k).mp hk
    refine ⟨c * (n ^ j * k * (n ^ j)⁻¹), K.mul_mem hc hnk, ?_⟩
    rw [pow_succ, hj, pow_succ]
    group

omit [IsSimpleGroup G] in
theorem mem_of_isPGroup_of_mem_sup {N : Subgroup G} (hNK : N ≤ Subgroup.normalizer (K : Set G))
    (hN : Odd (Nat.card N)) {x : G} (hx : x ∈ K ⊔ N) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ K := by
  have hx' : x ∈ ((K ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K N hNK] at hx'
  obtain ⟨k, hk, n, hn, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨c, hc, hj⟩ := exists_pow_eq_mul hNK hk hn (Nat.card N)
  have hnN : n ^ Nat.card N = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥N) (x := ⟨n, hn⟩))
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  rw [hnN, mul_one] at hj
  obtain ⟨a, ha⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at ha
  have hcop : Nat.Coprime (Nat.card N) (orderOf (k * n)) := by
    rw [ha]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hN)
  have hb := Nat.gcd_eq_gcd_ab (Nat.card N) (orderOf (k * n))
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have e : k * n = ((k * n) ^ (Nat.card N)) ^ (Nat.gcdA (Nat.card N) (orderOf (k * n))) *
      ((k * n) ^ orderOf (k * n)) ^ (Nat.gcdB (Nat.card N) (orderOf (k * n))) := by
    rw [← zpow_natCast, ← zpow_natCast (k * n) (orderOf (k * n)), ← zpow_mul, ← zpow_mul,
      ← zpow_add, ← hb, zpow_one]
  rw [e, pow_orderOf_eq_one, one_zpow, mul_one, hj]
  exact K.zpow_mem hc _

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
