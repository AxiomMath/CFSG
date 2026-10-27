module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DPhase1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p ↥E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem card_centralizerQuot_le {B K₀ S₀ : Subgroup G}
    (hBel : IsElemAbelian 3 B) (hBc : Nat.card B = 81) (hSC : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K₀ : Set G)) (hBS : B ≤ Subgroup.normalizer (S₀ : Set G))
    (hSK : S₀ ≤ K₀) (hSel : IsElemAbelian 3 S₀)
    (hSc : Nat.card S₀ = 3 ^ (Nat.card K₀).factorization 3) (hS3 : 3 < Nat.card S₀)
    (hcen : ∀ g ∈ K₀, (∀ k ∈ K₀, k * g * k⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 K₀) →
      g ∈ GLAPPrimeCoreOf 3 K₀) :
    Nat.card ↥(B ⊓ centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀)) ≤ 9 ∧ B ⊓ K₀ ≠ ⊥ ∧
      (B ⊓ K₀) ⊓ (B ⊓ centralizerQuot K₀ (GLAPPrimeCoreOf 3 K₀)) = ⊥ := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := isPGroup_of_isElemAbelian hBel
  have hSp : IsPGroup 3 ↥S₀ := isPGroup_of_isElemAbelian hSel
  set O₀ := GLAPPrimeCoreOf 3 K₀ with hO₀
  set Cq := B ⊓ centralizerQuot K₀ O₀ with hCq
  have hBc' : B ≤ Subgroup.normalizer (S₀ : Set G) := hBS
  have hP := card_sup_mul_card_inf hBc'
  have hPp : IsPGroup 3 ↥(S₀ ⊔ B) := by
    obtain ⟨a, ha⟩ := exists_card_eq_pow hSp
    obtain ⟨b, hb⟩ := exists_card_eq_pow hBp
    have hdvd : Nat.card ↥(S₀ ⊔ B) ∣ 3 ^ (a + b) := by
      rw [pow_add, ← ha, ← hb, ← hP]
      exact Dvd.intro _ rfl
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card hc
  have hE₀S : B ⊓ K₀ ≤ S₀ := by
    have hS' : S₀ = (S₀ ⊔ B) ⊓ K₀ :=
      eq_of_le_sylow (le_inf le_sup_left hSK) inf_le_right (hPp.to_inf_left) hSc
    intro g hg
    rw [hS']
    exact ⟨Subgroup.mem_sup_right hg.1, hg.2⟩
  have hSne : S₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hS3
    omega
  have hE₀ne : B ⊓ K₀ ≠ ⊥ := by
    have hPn : S₀ ⊔ B ≤ Subgroup.normalizer (S₀ : Set G) :=
      sup_le Subgroup.le_normalizer hBS
    obtain ⟨n, hn, hn1, hnc⟩ := exists_fixed_ne_one hPp hPn hSne hSp
    have hn3 : n ^ 3 = 1 := hSel.2 n hn
    have hcentr : B ≤ Subgroup.centralizer (Subgroup.zpowers n : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute n b from (hnc b (Subgroup.mem_sup_right hb)).symm) m).eq
    have hE : IsElemAbelian 3 (B ⊔ Subgroup.zpowers n) :=
      isElemAbelian_sup_of_commute hBel (isElemAbelian_zpowers hn3) hcentr
    have hEB : B ⊔ Subgroup.zpowers n = B := hSC.2.2 _ le_top hE le_sup_left
    have hnB : n ∈ B := by
      rw [← hEB]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
    intro h
    have : n ∈ B ⊓ K₀ := ⟨hnB, hSK hn⟩
    rw [h, Subgroup.mem_bot] at this
    exact hn1 this
  have hBK0 : (B ⊓ K₀) ⊓ Cq = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨⟨hgB, hgK⟩, -, hgC⟩ := hg
    have hgO : g ∈ O₀ := hcen g hgK (fun k hk => hgC.2.2 k hk)
    have : g ∈ B ⊓ GLAPPrimeCoreOf 3 K₀ := ⟨hgB, hgO⟩
    rw [pgroup_inf_core_eq_bot K₀ hBp, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 this
  refine ⟨?_, hE₀ne, hBK0⟩
  have hCqB : Cq ≤ B := inf_le_left
  have hCqS : Cq ≤ Subgroup.centralizer (S₀ : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hcB : c ∈ B := hCqB hc
    have h1 : s * c * s⁻¹ * c⁻¹ ∈ O₀ := hc.2.2.2 s (hSK hs)
    have h2 : s * c * s⁻¹ * c⁻¹ ∈ S₀ := by
      have := (Subgroup.mem_normalizer_iff.1 (hBS hcB) s⁻¹).1 (S₀.inv_mem hs)
      have h4 : s * (c * s⁻¹ * c⁻¹) ∈ S₀ := S₀.mul_mem hs this
      simpa [mul_assoc] using h4
    have h3 : s * c * s⁻¹ * c⁻¹ ∈ S₀ ⊓ GLAPPrimeCoreOf 3 K₀ := ⟨h2, h1⟩
    rw [pgroup_inf_core_eq_bot K₀ hSp, Subgroup.mem_bot] at h3
    have := commutatorElement_eq_one_iff_mul_comm.1 h3
    exact this
  have hfinC : Finite ↥Cq := inferInstance
  have hCqp : IsPGroup 3 ↥Cq := hBp.to_le hCqB
  have hE₀B : B ⊓ K₀ ≤ B := inf_le_left
  have hE₀p : IsPGroup 3 ↥(B ⊓ K₀) := hBp.to_le hE₀B
  have hBnormCq : B ≤ Subgroup.normalizer (Cq : Set G) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (elemAbelian_comm hBel hb (hCqB hc)).symm
  by_contra hbig
  push Not at hbig
  obtain ⟨j, hj⟩ := exists_card_eq_pow hCqp
  have hj3 : 3 ≤ j := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ := exists_card_eq_pow hE₀p
  have hk1 : 1 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hk0 : k = 0 := by omega
    apply hE₀ne
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0]; simp)
  have hprod := card_sup_mul_card_inf (A := Cq) (B := B ⊓ K₀) (hBnormCq.trans' hE₀B)
  have hinfbot : Cq ⊓ (B ⊓ K₀) = ⊥ := by rw [inf_comm]; exact hBK0
  rw [hinfbot, Subgroup.card_bot, mul_one] at hprod
  have hle81 : Nat.card ↥(Cq ⊔ (B ⊓ K₀)) ≤ 81 := by
    rw [← hBc]
    exact Subgroup.card_le_of_le (sup_le hCqB hE₀B)
  rw [hprod, hj, hk] at hle81
  have hk3 : k = 1 := by
    by_contra hk2
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
    have h4 : 3 ^ j * 3 ^ k ≥ 3 ^ 3 * 3 ^ 2 := Nat.mul_le_mul ‹_› ‹_›
    omega
  have hj4 : j = 3 := by
    by_contra hj'
    have : 3 ^ 4 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk3] at hle81
    omega
  have hCqE : Cq ⊔ (B ⊓ K₀) = B := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hCqB hE₀B)
    rw [hBc, hprod, hj, hk, hj4, hk3]
    norm_num
  have hEel : IsElemAbelian 3 (Cq ⊔ S₀) :=
    isElemAbelian_sup_of_commute (isElemAbelian_mono hBel hCqB) hSel hCqS
  have hBle : B ≤ Cq ⊔ S₀ := by
    rw [← hCqE]
    exact sup_le_sup le_rfl hE₀S
  have hEB : Cq ⊔ S₀ = B := hSC.2.2 _ le_top hEel hBle
  have hS₀B : S₀ ≤ B ⊓ K₀ := fun g hg => ⟨hEB ▸ Subgroup.mem_sup_right hg, hSK hg⟩
  have : Nat.card S₀ ≤ Nat.card ↥(B ⊓ K₀) := Subgroup.card_le_of_le hS₀B
  rw [hk, hk3] at this
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
