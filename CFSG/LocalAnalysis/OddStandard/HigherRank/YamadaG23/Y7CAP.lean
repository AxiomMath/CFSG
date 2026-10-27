module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_P_le_N (c : K7Abs ρ t J Q P M6 M7) : P ≤ Subgroup.normalClosure (J : Set Γ) := by
  let N : Subgroup Γ := Subgroup.normalClosure (J : Set Γ)
  change P ≤ N
  haveI : N.Normal := Subgroup.normalClosure_normal
  have hJN : J ≤ N := fun x hx => Subgroup.subset_normalClosure hx
  have hcomm (K : Subgroup Γ) : ⁅J, K⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro j hj k _
    have hjN : j ∈ N := hJN hj
    have hmem : k * j⁻¹ * k⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem (j⁻¹) (N.inv_mem hjN) k
    have hjk : ⁅j, k⁆ = j * (k * j⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hjk]
    exact N.mul_mem hjN hmem
  have hM6 : M6 ≤ N := c.M6_gen.trans (hcomm M6)
  have hM7 : M7 ≤ N := c.M7_gen.trans (hcomm M7)
  rw [c.P_sup]
  exact sup_le hM6 hM7

theorem y7c_inv_fixed_nontriv {R : Subgroup Γ} (hR : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥) (ht : t ^ 2 = 1)
    (hn : ∀ x ∈ R, t * x * t⁻¹ ∈ R) : ∃ r ∈ R, r ≠ 1 ∧ t * r = r * t := by
  classical
  let f : Function.End ↥R := fun x => ⟨t * (x : Γ) * t⁻¹, hn x x.2⟩
  have ht2 : t * t = 1 := by simpa [pow_two] using ht
  have hf2 : f ^ 2 = 1 := by
    funext x
    apply Subtype.ext
    show t * (t * (x : Γ) * t⁻¹) * t⁻¹ = (x : Γ)
    calc t * (t * (x : Γ) * t⁻¹) * t⁻¹ = (t * t) * (x : Γ) * (t * t)⁻¹ := by group
      _ = (x : Γ) := by rw [ht2]; group
  haveI : Fintype ↥R := Fintype.ofFinite _
  have hmod : Fintype.card ↥R ≡ Fintype.card (Function.fixedPoints f) [MOD 2] :=
    Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) (by simpa using hf2)
  have hdvdR : 2 ∣ Fintype.card ↥R := by
    have hdvd : 2 ∣ Nat.card ↥R := by
      rcases hR.card_eq_or_dvd with h1 | h2
      · exact absurd ((Subgroup.card_le_one_iff_eq_bot R).mp (le_of_eq h1)) hR1
      · exact h2
    simpa [Nat.card_eq_fintype_card] using hdvd
  have hdvdFp : 2 ∣ Fintype.card (Function.fixedPoints f) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvdR))
  have h1fix : (1 : ↥R) ∈ Function.fixedPoints f := by
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    simp [f]
  have h1lt : 1 < Fintype.card (Function.fixedPoints f) := by
    have h2le : 2 ≤ Fintype.card (Function.fixedPoints f) :=
      Nat.le_of_dvd (Fintype.card_pos_iff.mpr ⟨⟨1, h1fix⟩⟩) hdvdFp
    omega
  obtain ⟨r, hr⟩ :=
    Fintype.exists_ne_of_one_lt_card h1lt (⟨1, h1fix⟩ : ↥(Function.fixedPoints f))
  refine ⟨(r.1 : Γ), r.1.2, ?_, ?_⟩
  · intro h
    exact hr (Subtype.ext (Subtype.ext h))
  · have hfix : f r.1 = r.1 := Function.mem_fixedPoints_iff.mp r.2
    have hval : t * (r.1 : Γ) * t⁻¹ = (r.1 : Γ) := congrArg Subtype.val hfix
    calc t * (r.1 : Γ) = t * (r.1 : Γ) * t⁻¹ * t := by group
      _ = (r.1 : Γ) * t := by rw [hval]

theorem y7c_P_inf_center (c : K7Abs ρ t J Q P M6 M7) {z : Γ} (hzP : z ∈ P)
    (hzN : z ∈ Subgroup.normalClosure (J : Set Γ))
    (hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z) : z = 1 := by
  let N : Subgroup Γ := Subgroup.normalClosure (J : Set Γ)
  let R : Subgroup Γ := (P ⊓ N) ⊓ Subgroup.centralizer (N : Set Γ)
  haveI : N.Normal := Subgroup.normalClosure_normal
  have hzR : z ∈ R := by
    have hz'' : z ∈ (P ⊓ N) ⊓ Subgroup.centralizer (N : Set Γ) := by
      refine ⟨Subgroup.mem_inf.mpr ⟨hzP, hzN⟩, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun n hn => (hzc n hn).symm)
    exact hz''
  have hRtwo : IsPGroup 2 ↥R := c.P_two.to_le (le_trans inf_le_left inf_le_left)
  have htR : ∀ x ∈ R, t * x * t⁻¹ ∈ R := by
    intro x hx
    have hx'' : x ∈ (P ⊓ N) ⊓ Subgroup.centralizer (N : Set Γ) := hx
    rw [Subgroup.mem_inf] at hx''
    obtain ⟨hxPN, hxC⟩ := hx''
    rw [Subgroup.mem_inf] at hxPN
    obtain ⟨hxP, hxN⟩ := hxPN
    have hxcomm : ∀ n ∈ N, n * x = x * n := Subgroup.mem_centralizer_iff.mp hxC
    refine ⟨Subgroup.mem_inf.mpr ⟨c.P_norm_t x hxP, ?_⟩, ?_⟩
    · exact (inferInstance : N.Normal).conj_mem x hxN t
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro n hn
      have hnN : t⁻¹ * n * t ∈ N := by
        simpa using (inferInstance : N.Normal).conj_mem n hn t⁻¹
      have hcomm := hxcomm (t⁻¹ * n * t) hnN
      calc n * (t * x * t⁻¹) = t * ((t⁻¹ * n * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * n * t)) * t⁻¹ := by rw [hcomm]
        _ = (t * x * t⁻¹) * n := by group
  have hRbot : R = ⊥ := by
    by_contra hRne
    obtain ⟨r, hrR, hrne, hrt⟩ := y7c_inv_fixed_nontriv hRtwo hRne c.t_sq htR
    have hr'' : r ∈ (P ⊓ N) ⊓ Subgroup.centralizer (N : Set Γ) := hrR
    rw [Subgroup.mem_inf] at hr''
    obtain ⟨hrPN, hrcen⟩ := hr''
    rw [Subgroup.mem_inf] at hrPN
    obtain ⟨hrP, _hrN⟩ := hrPN
    have hrJ : r ∈ J := c.P_cent_t r hrP hrt.symm
    have hrcomm : ∀ n ∈ N, n * r = r * n := Subgroup.mem_centralizer_iff.mp hrcen
    have hcommJ : ∀ y ∈ J, r * y = y * r := by
      intro y hy
      exact (hrcomm y (Subgroup.subset_normalClosure hy)).symm
    exact hrne (y7c_J_center c hrJ hcommJ)
  rw [hRbot] at hzR
  exact Subgroup.mem_bot.mp hzR

theorem y7c_two_pow_six_dvd (c : K7Abs ρ t J Q P M6 M7) :
    2 ^ 6 ∣ Nat.card (↥(Subgroup.normalClosure (J : Set Γ)) ⧸
      Subgroup.center ↥(Subgroup.normalClosure (J : Set Γ))) := by
  let N : Subgroup Γ := Subgroup.normalClosure (J : Set Γ)
  change 2 ^ 6 ∣ Nat.card (↥N ⧸ Subgroup.center ↥N)
  have hPN : P ≤ N := y7c_P_le_N c
  let φ : ↥N →* (↥N ⧸ Subgroup.center ↥N) := QuotientGroup.mk' (Subgroup.center ↥N)
  let η : ↥P →* (↥N ⧸ Subgroup.center ↥N) := φ.comp (Subgroup.inclusion hPN)
  have hηinj : Function.Injective η := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : QuotientGroup.mk' (Subgroup.center ↥N) (Subgroup.inclusion hPN x) = 1 := hx
    have hxcenter : Subgroup.inclusion hPN x ∈ Subgroup.center ↥N := by
      have hmem : Subgroup.inclusion hPN x ∈
          MonoidHom.ker (QuotientGroup.mk' (Subgroup.center ↥N)) :=
        MonoidHom.mem_ker.mpr hx'
      simpa only [QuotientGroup.ker_mk' (Subgroup.center ↥N)] using hmem
    have hxP : (x : Γ) ∈ P := x.2
    have hxN : (x : Γ) ∈ N := hPN x.2
    have hxc : ∀ n ∈ N, (x : Γ) * n = n * (x : Γ) := by
      intro n hn
      have hcomm := Subgroup.mem_center_iff.mp hxcenter ⟨n, hn⟩
      have hval : n * ((Subgroup.inclusion hPN x : ↥N) : Γ)
          = ((Subgroup.inclusion hPN x : ↥N) : Γ) * n := congrArg Subtype.val hcomm
      simpa using hval.symm
    exact Subtype.ext (y7c_P_inf_center c hxP hxN hxc)
  have hcard : Nat.card ↥η.range = 2 ^ 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hηinj).toEquiv, c.P_card]
  have hdvd := Subgroup.card_subgroup_dvd_card η.range
  rw [hcard] at hdvd
  exact hdvd

end CFSG.OddStandard.HigherRank.YamadaG23
