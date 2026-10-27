module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11_relIndex_sup_mul_card [Finite G] {A N K : Subgroup G} (hNK : N ≤ K)
    (hAK : A ≤ K) (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hsup : K = A ⊔ N) :
    A.relIndex K * Nat.card ↥(N ⊓ A) = Nat.card ↥N := by
  have hNnormal : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr
      (Subgroup.le_normalizer_iff.mpr hNn)
  have hrelNK : N.relIndex K = N.relIndex A := by
    haveI : (N.subgroupOf K).Normal := hNnormal
    have h := Subgroup.relIndex_sup_right (H := A.subgroupOf K) (K := N.subgroupOf K)
    rw [← Subgroup.subgroupOf_sup hAK hNK, ← hsup, Subgroup.subgroupOf_self,
      Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hAK] at h
    exact h
  have h1 : A.relIndex K * Nat.card ↥A = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card A K
    rwa [inf_eq_left.mpr hAK] at h
  have h2 : N.relIndex K * Nat.card ↥N = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card N K
    rwa [inf_eq_left.mpr hNK] at h
  have h3 : N.relIndex A * Nat.card ↥(N ⊓ A) = Nat.card ↥A :=
    Subgroup.relIndex_mul_card N A
  have hpos : N.relIndex A ≠ 0 :=
    (Subgroup.finiteIndex_of_finite (H := N.subgroupOf A)).index_ne_zero
  have eq1 : A.relIndex K * Nat.card ↥A = N.relIndex A * Nat.card ↥N := by
    rw [h1, ← h2, hrelNK]
  have eq2 : A.relIndex K * (N.relIndex A * Nat.card ↥(N ⊓ A)) =
      N.relIndex A * Nat.card ↥N := by
    rw [h3]; exact eq1
  have eq3 : (A.relIndex K * Nat.card ↥(N ⊓ A)) * N.relIndex A =
      Nat.card ↥N * N.relIndex A := by
    calc (A.relIndex K * Nat.card ↥(N ⊓ A)) * N.relIndex A
        = A.relIndex K * (N.relIndex A * Nat.card ↥(N ⊓ A)) := by ring
      _ = N.relIndex A * Nat.card ↥N := eq2
      _ = Nat.card ↥N * N.relIndex A := by ring
  exact Nat.mul_right_cancel (Nat.pos_iff_ne_zero.mpr hpos) eq3

theorem sec11_card_sup_dvd [Finite G] {A B : Subgroup G}
    (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) :
    Nat.card ↥(A ⊔ B) ∣ Nat.card ↥A * Nat.card ↥B := by
  have hKnorm : (A ⊔ B : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    sup_le A.le_normalizer (Subgroup.le_normalizer_iff.mpr hn)
  have hnA : ∀ k ∈ (A ⊔ B : Subgroup G), ∀ n ∈ A, k * n * k⁻¹ ∈ A :=
    Subgroup.le_normalizer_iff.mp hKnorm
  have hcount := sec11_relIndex_sup_mul_card (A := B) (N := A) (K := A ⊔ B)
    le_sup_left le_sup_right hnA (sup_comm A B)
  have h2 : B.relIndex (A ⊔ B) * Nat.card ↥B = Nat.card ↥(A ⊔ B) := by
    have h := Subgroup.relIndex_mul_card B (A ⊔ B)
    rwa [inf_eq_left.mpr (le_sup_right : B ≤ A ⊔ B)] at h
  have hcard : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
    rw [← h2, ← hcount]
    ring
  exact ⟨_, hcard.symm⟩

theorem sec11_isPGroup_sup [Finite G] {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) : IsPGroup 2 ↥(A ⊔ B) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp hA
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2) (G := ↥B)).mp hB
  have hdvd : Nat.card ↥(A ⊔ B) ∣ 2 ^ (a + b) := by
    have h := sec11_card_sup_dvd (A := A) (B := B) hn
    rw [ha, hb, ← pow_add] at h
    exact h
  obtain ⟨c, _, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact (IsPGroup.iff_card (p := 2) (G := ↥(A ⊔ B))).mpr ⟨c, hc⟩

theorem sec11_odd_card_sup [Finite G] {A B : Subgroup G} (hA : Odd (Nat.card ↥A))
    (hB : Odd (Nat.card ↥B)) (hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) :
    Odd (Nat.card ↥(A ⊔ B)) :=
  (hA.mul hB).of_dvd_nat (sec11_card_sup_dvd hn)

theorem sec11_isSylow2Of_of_sup_odd [Finite G] {P N X : Subgroup G} (hP : IsPGroup 2 P)
    (hPX : P ≤ X) (hNX : N ≤ X) (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card ↥N)) (hsup : X = P ⊔ N) : IsSylow2Of P X := by
  have hcount := sec11_relIndex_sup_mul_card (A := P) (N := N) (K := X) hNX hPX hNn hsup
  have hdiv : P.relIndex X ∣ Nat.card ↥N := ⟨Nat.card ↥(N ⊓ P), hcount.symm⟩
  have hoddP : Odd (P.relIndex X) := hodd.of_dvd_nat hdiv
  refine ⟨hPX, hP, ?_⟩
  intro h2
  exact (Nat.not_even_iff_odd.mpr hoddP) (even_iff_two_dvd.mpr h2)

theorem sec11_oddCore_le_of_decomp [Finite G] {H C K : Subgroup G}
    (hdec : ∀ h ∈ H, ∃ o ∈ oddCoreIn H, ∃ c ∈ C, h = o * c) (hCH : C ≤ H) (hK : K ≤ C)
    (hKn : ∀ c ∈ C, ∀ x ∈ K, c * x * c⁻¹ ∈ K) : oddCoreIn K ≤ oddCoreIn H := by
  have hOKH : oddCoreIn H ≤ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H
  have hOKK : oddCoreIn K ≤ K := CFSG.ClassicalInvolution.Balance.oddCoreIn_le K
  have hKH : K ≤ H := hK.trans hCH
  have hBH : K ⊔ oddCoreIn H ≤ H := sup_le hKH hOKH
  have hSB : oddCoreIn K ⊔ oddCoreIn H ≤ K ⊔ oddCoreIn H :=
    sup_le (hOKK.trans (le_sup_left : K ≤ K ⊔ oddCoreIn H))
      (le_sup_right : oddCoreIn H ≤ K ⊔ oddCoreIn H)
  have hHnB : H ≤ Subgroup.normalizer ((K ⊔ oddCoreIn H : Subgroup G) : Set G) := by
    intro h hh
    obtain ⟨o, ho, c, hc, rfl⟩ := hdec h hh
    have hoB : o ∈ Subgroup.normalizer ((K ⊔ oddCoreIn H : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (H := K ⊔ oddCoreIn H)
        (Subgroup.mem_sup_right (S := K) (T := oddCoreIn H) ho)
    have hcK : c ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer_iff.mpr hKn hc
    have hcO : c ∈ Subgroup.normalizer (oddCoreIn H : Set G) :=
      CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn H (hCH hc)
    have hcB : c ∈ Subgroup.normalizer ((K ⊔ oddCoreIn H : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup K (oddCoreIn H)
        (Subgroup.mem_inf.mpr ⟨hcK, hcO⟩)
    exact mul_mem hoB hcB
  have hBnormal : ((K ⊔ oddCoreIn H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).mpr hHnB
  have hBnS : K ⊔ oddCoreIn H ≤
      Subgroup.normalizer ((oddCoreIn K ⊔ oddCoreIn H : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · intro k hk
      have hkOK : k ∈ Subgroup.normalizer (oddCoreIn K : Set G) :=
        CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn K hk
      have hkO : k ∈ Subgroup.normalizer (oddCoreIn H : Set G) :=
        CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn H (hKH hk)
      exact Subgroup.inf_normalizer_le_normalizer_sup (oddCoreIn K) (oddCoreIn H)
        (Subgroup.mem_inf.mpr ⟨hkOK, hkO⟩)
    · intro o ho
      exact Subgroup.le_normalizer (H := oddCoreIn K ⊔ oddCoreIn H)
        (Subgroup.mem_sup_right (S := oddCoreIn K) (T := oddCoreIn H) ho)
  have hSnB : ((oddCoreIn K ⊔ oddCoreIn H).subgroupOf (K ⊔ oddCoreIn H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBnS
  have hsub : CFSG.Open.IsSubnormal (oddCoreIn K ⊔ oddCoreIn H) H :=
    CFSG.Open.IsSubnormal.step hSB hSnB
      (CFSG.Open.IsSubnormal.step hBH hBnormal (CFSG.Open.IsSubnormal.refl H))
  have hSodd : Odd (Nat.card ↥(oddCoreIn K ⊔ oddCoreIn H)) := by
    rw [sup_comm]
    refine sec11_odd_card_sup (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn H)
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn K) ?_
    intro b hb a ha
    exact CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H)
      (hOKK.trans hKH hb) ha
  exact le_sup_left.trans
    (CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_isSubnormal hsub hSodd)

end CFSG.OddStandard.SmallF3.Omega
