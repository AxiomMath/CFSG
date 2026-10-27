module

public import CFSG.ClassicalInvolution.Asc77.AscT3R10aInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Pure

variable {G : Type} [Group G]

theorem isQuatSub_not_isCyclic {P : Subgroup G} (h : IsQuatSub P) : ¬ IsCyclic ↥P := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  intro hc
  have hc' : IsCyclic (QuaternionGroup (2 ^ k)) := isCyclic_of_surjective e.toMonoidHom
    (MulEquiv.surjective _)
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcomm := hc'.isMulCommutative
  have h1 := hcomm.is_comm.comm (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
  have h2 : (0 : ZMod (2 * 2 ^ k)) - 1 = 0 + 1 := QuaternionGroup.xa.inj h1
  have h3 : ((2 : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by
    have : (2 : ZMod (2 * 2 ^ k)) = 0 := by linear_combination -h2
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h3
  have h4 : 2 * 2 ^ k ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.w_conj_into_S (d : Std20 p f K K' J S R R' W V z t) {T : Subgroup G}
    (hTC : T ≤ Subgroup.centralizer ({z} : Set G)) (hT2 : IsPGroup 2 ↥T) :
    ∃ n ∈ Subgroup.centralizer ({z} : Set G), conjSub n K = K ∧
      conjSub n T ≤ (S : Subgroup G) := by
  obtain ⟨c, hcC, hcT⟩ := exists_conj_le_of_sylow_le S d.hSz hTC hT2
  rcases d.late_conj_K hcC with h | h
  · exact ⟨c, hcC, h, hcT⟩
  · obtain ⟨u₀, hu₀S, hu₀K⟩ := d.late_exists_swap
    obtain ⟨-, -, -, hu₀S'⟩ := d.late_swap_data hu₀S hu₀K
    refine ⟨u₀⁻¹ * c, Subgroup.mul_mem _ (Subgroup.inv_mem _ (d.hSz hu₀S)) hcC, ?_, ?_⟩
    · rw [conjSub_mul, h, ← hu₀K, conjSub_inv_conjSub]
    · rw [conjSub_mul]
      refine (conjSub_mono hcT).trans ?_
      rw [Sec7.conjSub_inv_eq hu₀S']

theorem Std20.w_good (d : Std20 p f K K' J S R R' W V z t) {a₀ : G}
    (haS : a₀ ∈ (S : Subgroup G)) (ha2 : a₀ * a₀ = 1)
    (haX : a₀ ∉ sec20X (CoreAssembly.conjClass K) z K K')
    (hFK : InducesFAut K R a₀) (hFK' : InducesFAut K' R' a₀) :
    ∃ b ∈ (S : Subgroup G), b * b = 1 ∧ b ∉ sec20X (CoreAssembly.conjClass K) z K K' ∧
      InducesFAut K R b ∧ InducesFAut K' R' b ∧
      ∃ Q : Subgroup G, Q ≤ R ∧ Q ≤ Subgroup.centralizer ({b} : Set G) ∧ IsQuatSub Q ∧
        2 * Nat.card Q = Nat.card R := by
  classical
  obtain ⟨haN, ha2c, P, hP, hq, hc⟩ := id hFK
  have hPK : P ≤ K := hP.1.trans inf_le_left
  have hPC : P ≤ Subgroup.centralizer ({a₀} : Set G) := hP.1.trans inf_le_right
  have haNP : a₀ ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hPC hy))
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers a₀ ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS))
      hP.2.1 (Subgroup.zpowers_le.mpr haNP)
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_sec20X_left.trans d.r10a_X_le_C
  have hTC : Subgroup.zpowers a₀ ⊔ P ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (d.hSz haS)) (hPK.trans hKz)
  obtain ⟨n, hnC, hnK, hnT⟩ := d.w_conj_into_S hTC hT2
  have hnK' : conjSub n K' = K' := (d.late_conj_iff hnC).mp hnK
  set b : G := n * a₀ * n⁻¹ with hb
  have hbT : b ∈ conjSub n (Subgroup.zpowers a₀ ⊔ P) :=
    conj_mem_conjSub (Subgroup.mem_sup_left (Subgroup.mem_zpowers a₀))
  have hbS : b ∈ (S : Subgroup G) := hnT hbT
  have hb2 : b * b = 1 := by
    calc b * b = n * (a₀ * a₀) * n⁻¹ := by rw [hb]; group
      _ = 1 := by rw [ha2]; group
  have hbX : b ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
    intro h
    apply haX
    have hn := le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins
      (Subgroup.inv_mem _ hnC)
    have h1 := (Subgroup.mem_normalizer_iff.mp hn _).mp h
    have e : n⁻¹ * b * n⁻¹⁻¹ = a₀ := by rw [hb]; group
    rwa [e] at h1
  have hcR : Nat.card R = Nat.card R' :=
    Sec6Gen.natCard_isSylow2In_eq d.late_hΩ d.late_mem_K d.late_mem_K' d.hR d.hR'
  have hFKb : InducesFAut K R b := by
    have h := hFK.conj n
    rw [hnK] at h
    exact h.congr_card (late_natCard_conjSub n R)
  have hFKb' : InducesFAut K' R' b := by
    have h := hFK'.conj n
    rw [hnK'] at h
    exact h.congr_card (late_natCard_conjSub n R')
  refine ⟨b, hbS, hb2, hbX, hFKb, hFKb', conjSub n P, ?_, ?_, ?_, ?_⟩
  · rw [d.late_R_eq]
    refine le_inf ?_ ?_
    · rw [← hnK]
      exact conjSub_mono hPK
    · exact (conjSub_mono (le_sup_right : P ≤ Subgroup.zpowers a₀ ⊔ P)).trans hnT
  · rw [← Balance.conjSub_centralizer_singleton]
    exact conjSub_mono hPC
  · obtain ⟨k, hk, ⟨e⟩⟩ := hq
    exact ⟨k, hk, ⟨(Subgroup.equivMapOfInjective P (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective).symm.trans e⟩⟩
  · rw [late_natCard_conjSub]
    exact hc

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
