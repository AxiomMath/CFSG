module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AE17E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41GPh

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem e17_step1 {S T : Subgroup G} {t : G} (ht2 : t * t = 1) (htT : t ∉ T)
    (htc : ∀ s ∈ T, s * t = t * s) (hS : S = zpowers t ⊔ T) {s : G} (hs : s ∈ S) :
    s ∈ T ∨ t * s ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := fun h => htT (h ▸ T.one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hN : zpowers t ≤ normalizer (T : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem (fun y hy => ?_)
    rw [← htc y hy]
    simpa using hy
  have hs' : s ∈ ((zpowers t ⊔ T : Subgroup G) : Set G) := by
    rw [← hS]
    exact hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hs'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hs'
  rcases pt_eq_one_or_of_mem_zpowers hord ha with h1 | h1
  · left
    rw [h1, one_mul]
    exact hb
  · right
    rw [h1, ← mul_assoc, ht2, one_mul]
    exact hb

private theorem e17_abs_aux {S T E : Subgroup G} {t w w' : G} (ht2 : t * t = 1)
    (htT : t ∉ T) (htc : ∀ s ∈ T, s * t = t * s) (hS : S = zpowers t ⊔ T)
    (hT : ∀ u ∈ T, 16 ≤ Nat.card ↥(T ⊓ centralizer ({u} : Set G)) → u ^ 4 = 1)
    (hwS : w ∈ S) (hES : E ≤ S) (hEw : ∀ e ∈ E, e * w = w * e) (hE : 32 ≤ Nat.card E)
    (hw'T : w' ∈ T) (hw' : w' = w ∨ w = t * w') : w ^ 4 = 1 := by
  have hcomm : Commute t w' := (htc w' hw'T).symm
  have ht4 : t ^ 4 = 1 := by
    have h2 : t ^ 2 = 1 := by rw [pow_two]; exact ht2
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, one_pow]
  have hwpow : w ^ 4 = w' ^ 4 := by
    rcases hw' with h | h
    · rw [h]
    · rw [h, hcomm.mul_pow, ht4, one_mul]
  have hle : E ⊓ T ≤ T ⊓ centralizer ({w'} : Set G) := by
    intro e he
    have heE : e ∈ E := he.1
    have heT : e ∈ T := he.2
    refine ⟨heT, ?_⟩
    have hew : e * w = w * e := hEw e heE
    have het : e * t = t * e := htc e heT
    rcases hw' with h | h
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [h]
      exact hew
    · have hwt : w' = t * w := by
        rw [h, ← mul_assoc, ht2, one_mul]
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [hwt]
      calc e * (t * w) = (e * t) * w := (mul_assoc _ _ _).symm
        _ = (t * e) * w := by rw [het]
        _ = t * (e * w) := mul_assoc _ _ _
        _ = t * (w * e) := by rw [hew]
        _ = (t * w) * e := (mul_assoc _ _ _).symm
  have hrelS : T.relIndex S = 2 := by
    rw [Subgroup.relIndex_eq_two_iff']
    refine ⟨t, ?_, fun b hb => ?_⟩
    · rw [hS]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    · have hb_or : b ∈ T ∨ t * b ∈ T := e17_step1 ht2 htT htc hS hb
      rw [xor_iff_or_and_not_and]
      refine ⟨?_, ?_⟩
      · rcases hb_or with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro ⟨htbT, hbT⟩
        exact htT (by
          have : t = (t * b) * b⁻¹ := by group
          rw [this]
          exact Subgroup.mul_mem _ htbT (Subgroup.inv_mem _ hbT))
  have hrelE : T.relIndex E ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := T) (K := E) (L := S) hES
      (by rw [hrelS]; norm_num)
    simpa [hrelS] using h
  have hcardET : 16 ≤ Nat.card ↥(E ⊓ T) := by
    have hmul : T.relIndex E * Nat.card ↥(T ⊓ E) = Nat.card E :=
      Subgroup.relIndex_mul_card T E
    have h2 : 32 ≤ 2 * Nat.card ↥(T ⊓ E) := by
      calc 32 ≤ Nat.card E := hE
        _ = T.relIndex E * Nat.card ↥(T ⊓ E) := hmul.symm
        _ ≤ 2 * Nat.card ↥(T ⊓ E) := Nat.mul_le_mul_right _ hrelE
    have : 16 ≤ Nat.card ↥(T ⊓ E) := by omega
    simpa [inf_comm] using this
  have hcard : 16 ≤ Nat.card ↥(T ⊓ centralizer ({w'} : Set G)) :=
    le_trans hcardET (Subgroup.card_le_of_le hle)
  rw [hwpow]
  exact hT w' hw'T hcard

theorem e17_S_lemma_abs {S T E : Subgroup G} {t w : G} (ht2 : t * t = 1) (htT : t ∉ T)
    (htc : ∀ s ∈ T, s * t = t * s) (hS : S = zpowers t ⊔ T)
    (hT : ∀ w' ∈ T, 16 ≤ Nat.card ↥(T ⊓ centralizer ({w'} : Set G)) → w' ^ 4 = 1)
    (hwS : w ∈ S) (hES : E ≤ S) (hEw : ∀ e ∈ E, e * w = w * e) (hE : 32 ≤ Nat.card E) :
    w ^ 4 = 1 := by
  by_cases hwT : w ∈ T
  · exact e17_abs_aux ht2 htT htc hS hT hwS hES hEw hE hwT (Or.inl rfl)
  · have htwT : t * w ∈ T := (e17_step1 ht2 htT htc hS hwS).resolve_left hwT
    exact e17_abs_aux ht2 htT htc hS hT hwS hES hEw hE htwT
      (Or.inr (by rw [← mul_assoc, ht2, one_mul]))

variable {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem e17_S_lemma (h : L41GPh16 t L S x₁ x₂ lam rho) {E : Subgroup G} {w : G} (hwS : w ∈ S)
    (hES : E ≤ S) (hEw : ∀ e ∈ E, e * w = w * e) (hE : 32 ≤ Nat.card E) : w ^ 4 = 1 := by
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have hTS : wreathGrp x₁ x₂ lam ≤ S := by
    rw [h.basic.S_eq]
    exact le_sup_right
  have htT : t ∉ wreathGrp x₁ x₂ lam := fun ht =>
    t_not_mem_L h.hyp (pt_wreath_le_L h.toCtx0 ht)
  have htc : ∀ s ∈ wreathGrp x₁ x₂ lam, s * t = t * s := fun s hs =>
    mem_invCent_iff.mp (h.le_invCent (hTS hs))
  have hS : S = zpowers t ⊔ wreathGrp x₁ x₂ lam := by
    rw [h.basic.S_eq, show twoCore t = zpowers t from h.p2]
  exact e17_S_lemma_abs ht2 htT htc hS
    (fun u hu hc => z18_Tcent_lemma h.wreath hu hc) hwS hES hEw hE

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
