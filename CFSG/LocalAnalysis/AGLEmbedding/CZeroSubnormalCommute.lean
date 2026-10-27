module

import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.Open.StatedDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Subgroup

namespace SubnormalCommute

variable {Y : Type} [Group Y]

theorem commutator_zpowers_le_of_isSubnormal {T W D : Subgroup Y} (hT : IsSubnormal T W)
    {t : Y} (hE : ⁅⁅D, zpowers t⁆, zpowers t⁆ = ⁅D, zpowers t⁆) :
    t ∈ T → ⁅D, zpowers t⁆ ≤ W → ⁅D, zpowers t⁆ ≤ T := by
  induction hT with
  | refl => exact fun _ h => h
  | @step H M K hHM hn _ ih =>
    intro htH hEK
    have hEM := ih (hHM htH) hEK
    rw [← hE, commutator_le]
    intro e he s hs
    have hsH : s ∈ H := (zpowers_le.mpr htH) hs
    have h1 : e * s * e⁻¹ ∈ H := by
      have := hn.conj_mem ⟨s, hHM hsH⟩ (mem_subgroupOf.mpr hsH) ⟨e, hEM he⟩
      simpa [mem_subgroupOf] using this
    rw [commutatorElement_def]
    exact H.mul_mem h1 (H.inv_mem hsH)

variable [Finite Y]

theorem le_pCoreOf_of_isSubnormal {p : ℕ} [Fact p.Prime] {X H : Subgroup Y}
    (h : IsSubnormal X H) (hX : IsPGroup p X) : X ≤ pCoreOf p H := by
  suffices key : ∀ Z : Subgroup Y, IsPGroup p Z → Z ≤ X → X ≤ normalizer (Z : Set Y) →
      Z ≤ pCoreOf p H from key X hX le_rfl le_normalizer
  clear hX
  induction h with
  | refl K =>
    intro Z hZ hZK hKN
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hZK hKN hZ
  | @step Mb M1 Ktop hMM1 hnorm _ ih =>
    intro Z hZ hZM hMN
    have hZZ : Z ≤ pCoreOf p Mb :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hZM hMN hZ
    have hM1 : M1 ≤ normalizer (pCoreOf p Mb : Set Y) :=
      ((normal_subgroupOf_iff_le_normalizer hMM1).1 hnorm).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p Mb)
    exact hZZ.trans (ih _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup p Mb)
      ((CFSG.LieType.BorelTits.pCoreOf_le p Mb).trans hMM1) hM1)

private def c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private def s3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private theorem perm3_facts :
    c3 ^ 3 = 1 ∧ c3 ≠ 1 ∧ s3 ^ 2 = 1 ∧ s3 * c3 * s3⁻¹ = c3⁻¹ ∧
      ∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 → x = 1 ∨ x = c3 ∨ x = c3 ^ 2 := by
  decide

private theorem dvd_three_of_dvd_six {n : ℕ} (h6 : n ∣ 6) (hn : Odd n) : n ∣ 3 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases n <;> simp_all <;> contradiction

theorem commute_oUpperTwo_of_symThree {T B : Subgroup Y} (hT : IsSubnormal T ⊤)
    (hS : Nonempty (↥T ≃* Equiv.Perm (Fin 3))) (hB : IsPGroup 3 B) (hBs : IsSubnormal B ⊤) :
    ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo T, ∀ b ∈ B, b * x = x * b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hS
  obtain ⟨hc3, hc1, hs2, hsc, hcases⟩ := perm3_facts
  set a : Y := ((e.symm c3 : ↥T) : Y) with ha
  set t : Y := ((e.symm s3 : ↥T) : Y) with ht
  have haT : a ∈ T := (e.symm c3).2
  have htT : t ∈ T := (e.symm s3).2
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Subgroup.coe_pow, ← map_pow, hc3, map_one, Subgroup.coe_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hc1
    have : e.symm c3 = 1 := Subtype.ext h
    simpa using congrArg e this
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← Subgroup.coe_pow, ← map_pow, hs2, map_one, Subgroup.coe_one]
  have hta : t * a * t⁻¹ = a⁻¹ := by
    have := congrArg (fun g => ((e.symm g : ↥T) : Y)) hsc
    simpa [ha, ht] using this
  have hcube : ∀ x ∈ T, x ^ 3 = 1 → x ∈ zpowers a := by
    intro x hx hx3
    have h3 : e ⟨x, hx⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : ↥T) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hxe : (⟨x, hx⟩ : ↥T) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
    rcases hcases _ h3 with h | h | h
    · rw [h, map_one] at hxe
      have : x = 1 := congrArg Subtype.val hxe
      rw [this]
      exact one_mem _
    · rw [h] at hxe
      have : x = a := congrArg Subtype.val hxe
      rw [this]
      exact mem_zpowers a
    · rw [h, map_pow] at hxe
      have : x = a ^ 2 := by simpa [ha] using congrArg Subtype.val hxe
      rw [this]
      exact pow_mem (mem_zpowers a) 2
  have hcard : Nat.card ↥T = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hodd : ∀ x ∈ T, Odd (orderOf x) → x ^ 3 = 1 := by
    intro x hx hxo
    have h6 : orderOf x ∣ 6 := by
      rw [← hcard, ← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_three_of_dvd_six h6 hxo)
  have h3el : ∀ x ∈ T, (∃ k : ℕ, x ^ (3 ^ k) = 1) → x ∈ zpowers a := by
    rintro x hx ⟨k, hk⟩
    refine hcube x hx (hodd x hx ?_)
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk)
  have hO2 : CFSG.ComponentClassification.AS76b.oUpperTwo T ≤ zpowers a :=
    (closure_le _).mpr fun x hx => hcube x hx.1 (hodd x hx.1 hx.2)
  set D : Subgroup Y := pCoreOf 3 (⊤ : Subgroup Y) with hDdef
  have hD3 : IsPGroup 3 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 ⊤
  have hDN : ∀ g : Y, g ∈ normalizer (D : Set Y) := fun g =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 ⊤ (le_normalizer (mem_top g))
  have hDn : ∀ g d : Y, d ∈ D → g * d * g⁻¹ ∈ D := fun g d hd => (mem_normalizer_iff.mp (hDN g) d).mp hd
  have hBD : B ≤ D := le_pCoreOf_of_isSubnormal hBs hB
  have hAn : ((zpowers a).subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    have hconj : (g : Y) * a * (g : Y)⁻¹ ∈ zpowers a := by
      refine hcube _ (T.mul_mem (T.mul_mem g.2 haT) (T.inv_mem g.2)) ?_
      rw [conj_pow, ha3, mul_one, mul_inv_cancel]
    have : ((g * n * g⁻¹ : ↥T) : Y) = ((g : Y) * a * (g : Y)⁻¹) ^ k := by
      rw [conj_zpow, hk]
      simp
    rw [this]
    exact zpow_mem hconj k
  have hA3 : IsPGroup 3 (zpowers a) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (a ^ k) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hAD : zpowers a ≤ D :=
    le_pCoreOf_of_isSubnormal (IsSubnormal.step (zpowers_le.mpr haT) hAn hT) hA3
  have haD : a ∈ D := hAD (mem_zpowers a)
  have h2t : IsPGroup 2 (zpowers t) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (t ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hD2 : ¬ 2 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD3
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hE := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
    Nat.prime_two (zpowers t) D h2t hD2 (fun g _ => hDN g)
  have hET := commutator_zpowers_le_of_isSubnormal hT hE htT le_top
  have hcomm : ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ zpowers a := by
    intro d hd
    have hmem : d * t * d⁻¹ * t⁻¹ ∈ D := by
      have := D.mul_mem hd (hDn t d⁻¹ (D.inv_mem hd))
      simpa [mul_assoc] using this
    refine h3el _ (hET ?_) ?_
    · have := commutator_mem_commutator hd (mem_zpowers t)
      rwa [commutatorElement_def] at this
    · obtain ⟨k, hk⟩ := hD3 ⟨_, hmem⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hba : ∀ b ∈ B, b * a = a * b := by
    intro b hb
    have hbD := hBD hb
    set α := b⁻¹ * t * b * t⁻¹ with hα
    have hαa : α ∈ zpowers a := by
      have := hcomm b⁻¹ (D.inv_mem hbD)
      simpa [hα] using this
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hαa
    have hαc : α * a⁻¹ * α⁻¹ = a⁻¹ := by
      rw [← hm, mul_assoc, ← zpow_neg_one, ← zpow_neg, ← zpow_add, ← zpow_add]
      congr 1
      ring
    set x := b * a * b⁻¹ with hx
    have hxD : x ∈ D := D.mul_mem (D.mul_mem hbD haD) (D.inv_mem hbD)
    have htx : t * x * t⁻¹ = x⁻¹ := by
      have h1 : t * b * t⁻¹ = b * α := by rw [hα]; group
      calc t * x * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹) * (t * b * t⁻¹)⁻¹ := by rw [hx]; group
        _ = b * (α * a⁻¹ * α⁻¹) * b⁻¹ := by rw [h1, hta]; group
        _ = x⁻¹ := by rw [hαc, hx]; group
    have hx2 : x ^ 2 ∈ zpowers a := by
      have := hcomm x hxD
      have heq : x * t * x⁻¹ * t⁻¹ = x ^ 2 := by
        have : t * x⁻¹ * t⁻¹ = x := by
          rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, htx, inv_inv]
        calc x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
          _ = x ^ 2 := by rw [this, sq]
      rwa [heq] at this
    have hx3 : x ^ 3 = 1 := by rw [hx, conj_pow, ha3, mul_one, mul_inv_cancel]
    have hxa : x ∈ zpowers a := by
      have : x = (x ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hx3, one_mul]
      rw [this]
      exact pow_mem hx2 2
    have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    rw [mem_zpowers_iff_mem_range_orderOf, hoa] at hxa
    simp only [Finset.mem_image, Finset.mem_range] at hxa
    obtain ⟨k, hk3, hk⟩ := hxa
    interval_cases k
    · exfalso
      apply ha1
      have : b * a * b⁻¹ = 1 := by rw [← hx, ← hk, pow_zero]
      have := congrArg (fun g => b⁻¹ * g * b) this
      simpa [mul_assoc] using this
    · rw [pow_one, hx] at hk
      calc b * a = b * a * b⁻¹ * b := by group
        _ = a * b := by rw [← hk]
    · exfalso
      have hinv : b * a * b⁻¹ = a⁻¹ := by
        rw [← hx, ← hk, eq_inv_iff_mul_eq_one, ← pow_succ, ha3]
      have hb2 : b ^ 2 * a = a * b ^ 2 := by
        have : b ^ 2 * a * (b ^ 2)⁻¹ = a := by
          calc b ^ 2 * a * (b ^ 2)⁻¹ = b * (b * a * b⁻¹) * b⁻¹ := by rw [sq]; group
            _ = b * a⁻¹ * b⁻¹ := by rw [hinv]
            _ = (b * a * b⁻¹)⁻¹ := by group
            _ = a := by rw [hinv, inv_inv]
        calc b ^ 2 * a = b ^ 2 * a * (b ^ 2)⁻¹ * b ^ 2 := by group
          _ = a * b ^ 2 := by rw [this]
      obtain ⟨n, hn⟩ := hD3 ⟨b, hbD⟩
      have hbn : b ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hcop : Nat.Coprime 2 (orderOf b) :=
        (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right
          (orderOf_dvd_of_pow_eq_one hbn)
      obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
      have hbc : b * a = a * b := by
        rw [← hr]
        exact ((Commute.pow_left hb2 r : Commute ((b ^ 2) ^ r) a)).eq
      have : a⁻¹ = a := by
        rw [← hinv]
        calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [hbc]
          _ = a := by group
      apply ha1
      have h2 : a ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← this]; exact inv_mul_cancel a
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [ha3, h2]; group
  intro x hx b hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hO2 hx)
  exact ((Commute.zpow_right (hba b hb) k : Commute b (a ^ k))).eq

end SubnormalCommute

@[expose] def SubnormalSUThreeTwoCommute : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.pCore 2 Y = ⊥ →
    ∀ T₁ T₂ : Subgroup Y, IsSubnormal T₁ ⊤ → IsSubnormal T₂ ⊤ →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
        Nonempty (↥T₁ ≃* ↥(StatedSU 3 2 K))) →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
        Nonempty (↥T₂ ≃* ↥(StatedSU 3 2 K))) →
      CFSG.ComponentClassification.AS76b.oUpperTwo T₁ ≠
        CFSG.ComponentClassification.AS76b.oUpperTwo T₂ →
      ⁅CFSG.ComponentClassification.AS76b.oUpperTwo T₁,
        CFSG.ComponentClassification.AS76b.oUpperTwo T₂⁆ = ⊥

end CFSG.AGLEmbedding
