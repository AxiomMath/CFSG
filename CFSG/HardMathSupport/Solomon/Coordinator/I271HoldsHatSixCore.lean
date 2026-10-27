module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCON
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510ii
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

section Inner

variable {K : Type} [Group K] [Finite K]

theorem i271h_card_hatSix (hK : IsHatSix K) : Nat.card K = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := hK
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), hc,
    Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem i271h_inner_index_dvd_four (hK : IsHatSix K) :
    (MulAut.conj : K →* MulAut K).range.index ∣ 4 := by
  have h1080 := i271h_card_hatSix hK
  obtain ⟨hc, hZ, ⟨e⟩⟩ := hK
  have hinj : Function.Injective (autCenterQuot K) := autCenterQuot_injective_of_perfect hc
  have hd1 : Nat.card (MulAut K) ∣ Nat.card (MulAut (K ⧸ Subgroup.center K)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have hd2 : Nat.card (MulAut (K ⧸ Subgroup.center K)) = 1440 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact Proving.AutSixBalance.card_mulAut_alt6
  have hker : (MulAut.conj : K →* MulAut K).ker = Subgroup.center K := by
    ext g
    rw [MonoidHom.mem_ker]
    exact i2326o_conj_eq_one_iff
  have hrange : Nat.card (MulAut.conj : K →* MulAut K).range = 360 := by
    have := Subgroup.card_ker_mul_card_range (MulAut.conj : K →* MulAut K)
    rw [hker, hZ, h1080] at this
    omega
  have hidx := Subgroup.index_mul_card (MulAut.conj : K →* MulAut K).range
  rw [hrange] at hidx
  have : (MulAut.conj : K →* MulAut K).range.index * 360 ∣ 1440 := by
    rw [hidx, ← hd2]
    exact hd1
  have h360 : 360 * (MulAut.conj : K →* MulAut K).range.index ∣ 360 * 4 := by
    rw [mul_comm 360]
    simpa using this
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h360

theorem i271h_mem_inner_of_pow_three (hK : IsHatSix K) {α : MulAut K} (h3 : α ^ 3 = 1) :
    α ∈ (MulAut.conj : K →* MulAut K).range := by
  have hdvd := i271h_inner_index_dvd_four hK
  have : (MulAut.conj : K →* MulAut K).range.Normal := i2326o_normal_inner
  have h1 := Subgroup.pow_index_mem (MulAut.conj : K →* MulAut K).range α
  have h4 : (MulAut.conj : K →* MulAut K).range.index ∈ ({1, 2, 4} : Set ℕ) := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show _ ∣ 2 ^ 2 by simpa using hdvd)
    interval_cases m <;> simp [hm']
  rcases h4 with h | h | h
  · rwa [h, pow_one] at h1
  · rw [h] at h1
    have h4 : α ^ 2 = α⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact h3
    rw [h4] at h1
    simpa using inv_mem h1
  · rw [h] at h1
    have h4 : α ^ 4 = α := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    rwa [h4] at h1

end Inner

section Core

variable {K : Type} [Group K] [Finite K]

theorem i271h_hatSix_core (hK : IsHatSix K) (H : Subgroup (MulAut K)) (hH3 : ∀ φ ∈ H, φ ^ 3 = 1)
    (hcl : ∀ x : K, x ^ 3 = 1 → (∀ φ ∈ H, φ x * x⁻¹ ∈ Subgroup.center K) →
      (MulAut.conj x : MulAut K) ∈ H) :
    9 ≤ Nat.card H := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hZ : Nat.card (Subgroup.center K) = 3 := hK.2.1
  have hinn : H ≤ (MulAut.conj : K →* MulAut K).range := fun α hα =>
    i271h_mem_inner_of_pow_three hK (hH3 α hα)
  set G : Subgroup K := H.comap (MulAut.conj : K →* MulAut K) with hG
  have hGcard : Nat.card G = 3 * Nat.card H := by
    rw [hG, LocalBalance.Lemma510iiNs.card_comap_conj H hinn, hZ]
  have hHp : IsPGroup 3 H := fun φ => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hH3 φ φ.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hHp
  have hGp : IsPGroup 3 G :=
    IsPGroup.of_card (n := a + 1) (by rw [hGcard, ha, pow_succ]; ring)
  obtain ⟨R, hGR⟩ := hGp.exists_le_sylow
  obtain ⟨hR27, -, hRexp⟩ := t112m_sylow_hatSix hK R
  have hZp : IsPGroup 3 (Subgroup.center K) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hZR : Subgroup.center K ≤ (R : Subgroup K) := hZp.le_sylow_of_normal R
  have hRZ : ∀ r ∈ (R : Subgroup K), ∀ s ∈ (R : Subgroup K),
      r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center K := by
    intro r hr s hs
    let f : ↥(R : Subgroup K) →* K ⧸ Subgroup.center K :=
      (QuotientGroup.mk' (Subgroup.center K)).comp (R : Subgroup K).subtype
    have hker : f.ker = (Subgroup.center K).subgroupOf (R : Subgroup K) := by
      ext ⟨g, hg⟩
      simp [f, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hkcard : Nat.card f.ker = 3 := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, hZ]
    have hrange : Nat.card f.range = 3 ^ 2 := by
      have := Subgroup.card_ker_mul_card_range f
      rw [hkcard, hR27] at this
      omega
    have hcomm : IsMulCommutative ↥f.range :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hrange
    have h1 : (⟨f ⟨r, hr⟩, ⟨_, rfl⟩⟩ : ↥f.range) * ⟨f ⟨s, hs⟩, ⟨_, rfl⟩⟩ =
        ⟨f ⟨s, hs⟩, ⟨_, rfl⟩⟩ * ⟨f ⟨r, hr⟩, ⟨_, rfl⟩⟩ := mul_comm' _ _
    have h2 : f ⟨r, hr⟩ * f ⟨s, hs⟩ = f ⟨s, hs⟩ * f ⟨r, hr⟩ := congrArg Subtype.val h1
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h3 : (QuotientGroup.mk r : K ⧸ Subgroup.center K) * QuotientGroup.mk s =
        QuotientGroup.mk s * QuotientGroup.mk r := h2
    rw [h3]
    group
  have hRG : (R : Subgroup K) ≤ G := by
    intro x hx
    refine hcl x (hRexp x hx) (fun φ hφ => ?_)
    obtain ⟨g, hg⟩ := hinn hφ
    have hgG : g ∈ G := by
      show (MulAut.conj : K →* MulAut K) g ∈ H
      rw [hg]
      exact hφ
    rw [← hg]
    simp only [MulAut.conj_apply]
    exact hRZ g (hGR hgG) x hx
  have hle : Nat.card (R : Subgroup K) ≤ Nat.card G := Subgroup.card_le_of_le hRG
  rw [hR27, hGcard] at hle
  omega

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
