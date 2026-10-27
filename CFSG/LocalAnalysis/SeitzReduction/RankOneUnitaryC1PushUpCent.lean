module

public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NcycBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem pushUp_sq_mem_of_conj_szA₁ (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {y : G} (hyT : y ∈ T)
    (hyA : ∀ a ∈ szA₁ (szT₁ L T), y * a = a * y) : y ^ 2 ∈ szT₁ L T ⊔ zpowers t := by
  classical
  obtain ⟨-, -, -, -, -, -, hinner⟩ := h.start_of_card_sylow hS2
  obtain ⟨e, Q, hB, -, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨D', hinf, hsup, hnorm, hcard, -⟩ := hB.lemma_3_6_c_unitary Q
  set I := Subgroup.map (MulAut.conj : L →* MulAut L) (Q : Subgroup L) with hI
  set C := autCentralizer (rootCenter (Q : Subgroup L)) with hC
  have hyN : y ∈ normalizer (L : Set G) := h.le_normalizer hyT
  set σ := L.normalizerMonoidHom ⟨y, hyN⟩ with hσ
  have hσapp : ∀ x : L, ((σ x : L) : G) = y * x * y⁻¹ := fun x =>
    normalizerMonoidHom_apply_apply_coe L _ x
  have hσC : σ ∈ C := by
    rw [hC, mem_autCentralizer_iff]
    intro z hz
    apply Subtype.ext
    rw [hσapp, hyA _ ((hmemZ z).mp hz), mul_inv_cancel_right]
  have hD'C : D' ≤ C := hsup ▸ le_sup_right
  have hIC : I ≤ C := hsup ▸ le_sup_left
  have hD'N : D' ≤ normalizer (I : Set (MulAut L)) := by
    intro d hd
    refine mem_normalizer_iff.mpr fun i => ⟨fun hi => ?_, fun hi => ?_⟩
    · have := hnorm.conj_mem ⟨i, hIC hi⟩ (mem_subgroupOf.mpr hi) ⟨d, hD'C hd⟩
      exact mem_subgroupOf.mp this
    · have hi' : d * i * d⁻¹ ∈ C := hIC hi
      have := hnorm.conj_mem ⟨d * i * d⁻¹, hi'⟩ (mem_subgroupOf.mpr hi) ⟨d⁻¹, inv_mem (hD'C hd)⟩
      have h2 := mem_subgroupOf.mp this
      simp only [coe_mul, coe_inv, inv_inv] at h2
      rwa [show d⁻¹ * (d * i * d⁻¹) * d = i by group] at h2
  have hσ' : σ ∈ D' ⊔ I := by rw [sup_comm, hsup]; exact hσC
  obtain ⟨d', hd', i, hi, hdi⟩ := ncyc_exists_mul_of_mem_sup hD'N hσ'
  have hpow : ∀ n : ℕ, ∃ j ∈ I, (d' * i) ^ n = d' ^ n * j := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨j, hj, hj'⟩ := ih
      refine ⟨(d'⁻¹ * j * d') * i,
        mul_mem ((mem_normalizer_iff''.mp (hD'N hd') j).mp hj) hi, ?_⟩
      rw [pow_succ, hj', pow_succ]
      group
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp h.isPGroup ⟨y, hyT⟩
  have hy2m : y ^ 2 ^ m = 1 := by
    have := pow_orderOf_eq_one (⟨y, hyT⟩ : T)
    rw [hm] at this
    exact congrArg Subtype.val this
  have hσ2m : σ ^ 2 ^ m = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨y, hyN⟩ : normalizer (L : Set G)) ^ 2 ^ m = 1 := Subtype.ext hy2m
    rw [this, map_one]
  obtain ⟨j, hj, hj'⟩ := hpow (2 ^ m)
  rw [hdi, hσ2m] at hj'
  have hd'm : d' ^ 2 ^ m = 1 := by
    have h1 : d' ^ 2 ^ m = j⁻¹ := eq_inv_of_mul_eq_one_left hj'.symm
    have h2 : d' ^ 2 ^ m ∈ I ⊓ D' := mem_inf.mpr ⟨h1 ▸ inv_mem hj, pow_mem hd' _⟩
    rw [hinf, mem_bot] at h2
    exact h2
  have hord : orderOf d' ∣ 2 := by
    have h1 : orderOf d' ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hd'm
    have h2 : orderOf d' ∣ Nat.card D' := Subgroup.orderOf_dvd_natCard D' hd'
    rw [hcard] at h2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rw [hk] at h2 ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ 2 * (2 ^ f + 1) :=
        (pow_dvd_pow 2 (show 2 ≤ k + 2 by omega)).trans h2
      have hf : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := h.two_le; omega)
      omega
  have hd'2 : d' ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  obtain ⟨j₂, hj₂, hj₂'⟩ := hpow 2
  rw [hd'2, one_mul, hdi] at hj₂'
  have hσ2I : σ ^ 2 ∈ I := hj₂' ▸ hj₂
  obtain ⟨l, -, hl⟩ := hσ2I
  refine hinner (y ^ 2) (pow_mem hyT 2) (l : G) l.2 fun x hx => ?_
  have h1 := congrArg (fun τ : MulAut L => ((τ ⟨x, hx⟩ : L) : G)) hl
  have h2 : σ ^ 2 = L.normalizerMonoidHom ⟨y ^ 2, pow_mem hyN 2⟩ := by
    rw [hσ, ← map_pow]
    rfl
  rw [h2, normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] at h1
  simpa using h1.symm

end U3Start

end CFSG.SeitzReduction.RankOne
