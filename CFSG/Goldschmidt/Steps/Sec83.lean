module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec81b
import CFSG.Goldschmidt.Steps.Sec83a
import CFSG.Goldschmidt.Steps.AxB
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter Sec8

theorem G83_of (h64 : S_G64) (h31 : S_G31) (h82 : S_G82) : S_G83 := by
  intro G _ _ S A hset h4 a ha ha1 H hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hset.isSimpleGroup
  obtain ⟨-, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have hAH : A ≤ H := hset.le.trans (le_of_mem_benderM hset h4 ha hH)
  have hCH : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)).trans
      (Walter.centralizer_le_of_mem_benderM hH)
  have hE : ⁅componentLayerOf H, A⁆ = ⊥ := by
    obtain ⟨hQ, -⟩ := eq_oddCoreOf_sup hset h4 ha ha1 hH
    have hEQ := componentLayerOf_centralizes_solvable_of_le_normalizer H _
      (normalClosureIn_le_self H A) (isSolvable_of_eq_oddCoreOf_sup hset.elem.1 hQ)
      ((componentLayerOf_isNormalIn H).1.trans (le_normalizer_normalClosureIn H A))
    exact le_bot_iff.mp (hEQ ▸ Subgroup.commutator_mono le_rfl (le_normalClosureIn hAH))
  refine ⟨fun a₁ ha₁ ha₁1 p hp => ?_, hE⟩
  have hcentr : qCoreOf H p ≤ Subgroup.centralizer (A : Set G) →
      (∀ x ∈ qCoreOf H p, a₁⁻¹ * x * a₁ = x) ∨ ∀ x ∈ qCoreOf H p, a₁⁻¹ * x * a₁ = x⁻¹ :=
    fun h => Or.inl fun x hx => by
      rw [mul_assoc, ← (Subgroup.mem_centralizer_iff.mp (h hx)) a₁ ha₁, ← mul_assoc,
        inv_mul_cancel, one_mul]
  by_cases hp2 : p = 2
  · subst hp2
    refine hcentr fun x hx => ?_
    have hR : IsPGroup 2 (A ⊔ qCoreOf H 2 : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (S.isPGroup'.to_le hset.le) (qCoreOf_isPGroup H 2)
        (hAH.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H 2)))
    exact pGroup_le_centralizer hset h4 hR le_sup_left (Subgroup.mem_sup_right hx)
  set P := qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) with hPdef
  by_cases hP : P = ⊥
  ·
    by_cases ha₁a : a₁ = a
    · refine Or.inl fun x hx => ?_
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp
        (hHa ▸ (qCoreOf_le H p hx) : x ∈ Subgroup.centralizer ({a} : Set G))
      rw [ha₁a, mul_assoc, hx', ← mul_assoc, inv_mul_cancel, one_mul]
    refine Or.inr fun x hx => ?_
    have hfix : qCoreOf H p ⊓ Subgroup.centralizer ({a₁} : Set G) = ⊥ := by
      refine eq_bot_iff.mpr fun y hy => ?_
      have hya : y ∈ Subgroup.centralizer ({a} : Set G) := hHa ▸ qCoreOf_le H p hy.1
      have hyA := mem_centralizer_of_mem_two hset h4 ha ha₁ ha1 ha₁1 (Ne.symm ha₁a) hya hy.2
      exact hP ▸ ⟨hy.1, hyA⟩
    have h1 := inv_of_inf_eq_bot (mul_self_eq_one hset.elem ha₁)
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hAH ha₁)) hfix hx
    have hai : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right (mul_self_eq_one hset.elem ha₁)
    rw [hai] at h1 ⊢
    exact h1
  refine hcentr ?_
  have hPp : IsPGroup p P := (qCoreOf_isPGroup H p).to_le inf_le_left
  have hNtop : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro htop
    have : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
    · exact hP h
    · obtain ⟨k, hk⟩ := hPp ⟨a, h ▸ Subgroup.mem_top a⟩
      have h1 : orderOf a ∣ p ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      rw [orderOf_eq_prime (hset.elem.2 a ha) ha1] at h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow h1)).symm
  obtain ⟨M, hM, hPM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (Subgroup.normalizer (P : Set G))).resolve_left hNtop
  obtain ⟨n, hn, hnc⟩ := exists_not_mem_centralizer hset h4
  obtain ⟨hba, -⟩ := conj_conj_eq_mul hset h4 hn hnc ha ha1
  set b := n * a * n⁻¹ with hb
  have hbA : b ∈ A := conj_mem hn ha
  have hb1 : b ≠ 1 := conj_ne_one ha1
  set Q := qCoreOf (Subgroup.centralizer ({b} : Set G)) p with hQ
  have hQN := le_normalizer_of_isNormalIn (qCoreOf_normal_in (Subgroup.centralizer ({b} : Set G)) p)
  have haCb : a ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm hset.elem ha hbA)
  have hPCb : P ≤ Subgroup.centralizer ({b} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA))
  have hPa : P ≤ Subgroup.centralizer ({a} : Set G) := hHa ▸ inf_le_left.trans (qCoreOf_le H p)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers a)) p := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hset.elem.2 a ha))
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have : Fact p.Prime := ⟨hp⟩
  have hfixQ : Q ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro y hy
    refine mem_centralizer_zpowers ?_
    refine le_centralizer_of_isPGroup h64 h31 h82 hset h4 ha ha1 hH hp hp2 hP hM hPM
      (P₁ := Q ⊓ Subgroup.centralizer (P : Set G)) ?_ ((qCoreOf_isPGroup _ p).to_le inf_le_left)
      (mem_normalizer_inf (hQN haCb) ?_) hy
    · exact fun z hz => hPM (Subgroup.centralizer_le_normalizer _ hz.2)
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.mp (hPa hz))
  have hQa := N10 G Q (Subgroup.zpowers a) P (qCoreOf_isPGroup _ p) hcop hPp
    (Subgroup.zpowers_le.mpr (hQN haCb)) (hPCb.trans hQN)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hPa hz))))) hfixQ
  have hQA : Q ≤ Subgroup.centralizer (A : Set G) := fun y hy =>
    mem_centralizer_of_mem_two hset h4 ha hbA ha1 hb1 (Ne.symm hba)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers a)) (hQa hy))
      (qCoreOf_le _ p hy)
  intro x hx
  have hxQ : n * x * n⁻¹ ∈ Q := by
    have h1 : qCoreOf (H.map (MulAut.conj n).toMonoidHom) p =
        (qCoreOf H p).map (MulAut.conj n).toMonoidHom := qCoreOf_conjugateSubgroup H n p
    rw [hHa, Walter.map_conj_centralizer_singleton] at h1
    rw [hQ, h1]
    exact ⟨x, hHa ▸ hx, rfl⟩
  have := hQA hxQ
  exact mem_centralizer_of_conj_mem (Subgroup.inv_mem _ hn) (by simpa using this)

end CFSG.Goldschmidt
