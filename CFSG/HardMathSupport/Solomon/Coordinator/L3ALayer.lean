module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
open scoped commutatorElement

section Lift

variable {G G' : Type*} [Group G] [Group G']

theorem lift_fixed {φ : G →* G'} (hker : ∀ c, φ c = 1 → c ∈ Subgroup.center G) {αt : MulAut G}
    {αb : MulAut G'} (hc : ∀ x, φ (αt x) = αb (φ x)) {x : G} (hx : αb (φ x) = φ x) :
    x⁻¹ * αt x ∈ Subgroup.center G := by
  apply hker
  rw [map_mul, map_inv, hc, hx, inv_mul_cancel]

theorem fixSub_commutator_le_map {φ : G →* G'} (hφ : Function.Surjective φ)
    (hker : ∀ c, φ c = 1 → c ∈ Subgroup.center G) {αt : MulAut G} {αb : MulAut G'}
    (hc : ∀ x, φ (αt x) = αb (φ x)) :
    ⁅fixSub αb, fixSub αb⁆ ≤ (fixSub αt).map φ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, rfl⟩ := hφ a
  obtain ⟨y, rfl⟩ := hφ b
  have hx := lift_fixed hker hc ha
  have hy := lift_fixed hker hc hb
  refine ⟨⁅x, y⁆, ?_, by rw [map_commutatorElement]⟩
  show αt ⁅x, y⁆ = ⁅x, y⁆
  have e1 : αt x = x * (x⁻¹ * αt x) := by group
  have e2 : αt y = y * (y⁻¹ * αt y) := by group
  rw [map_commutatorElement, e1, e2]
  generalize x⁻¹ * αt x = z at hx
  generalize y⁻¹ * αt y = w at hy
  have hz := Subgroup.mem_center_iff.1 hx
  have hw := Subgroup.mem_center_iff.1 hy
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * z * (y * w) * (z⁻¹ * x⁻¹) * (w⁻¹ * y⁻¹)
      = x * (z * (y * w) * z⁻¹) * x⁻¹ * (w⁻¹ * y⁻¹) := by group
    _ = x * (y * w) * x⁻¹ * (w⁻¹ * y⁻¹) := by
        rw [← hz (y * w), mul_inv_cancel_right]
    _ = x * y * x⁻¹ * y⁻¹ := by
        have := hw (x⁻¹)
        calc x * (y * w) * x⁻¹ * (w⁻¹ * y⁻¹) = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by group
          _ = x * y * x⁻¹ * y⁻¹ := by rw [← this]; group

theorem exists_pow_mem_map_fixSub {φ : G →* G'} (hφ : Function.Surjective φ)
    (hker : ∀ c, φ c = 1 → c ∈ Subgroup.center G) (h3 : ∀ c, φ c = 1 → ∃ n : ℕ, c ^ 3 ^ n = 1)
    {αt : MulAut G} {αb : MulAut G'} (hc : ∀ x, φ (αt x) = αb (φ x)) {a : G'} (ha : a ∈ fixSub αb) :
    ∃ n : ℕ, a ^ 3 ^ n ∈ (fixSub αt).map φ := by
  obtain ⟨x, rfl⟩ := hφ a
  have hx := lift_fixed hker hc ha
  have hzker : φ (x⁻¹ * αt x) = 1 := by rw [map_mul, map_inv, hc, mem_fixSub.1 ha, inv_mul_cancel]
  obtain ⟨n, hn⟩ := h3 _ hzker
  refine ⟨n, x ^ 3 ^ n, ?_, by rw [map_pow]⟩
  show αt (x ^ 3 ^ n) = x ^ 3 ^ n
  have e1 : αt x = x * (x⁻¹ * αt x) := by group
  have hcm : Commute x (x⁻¹ * αt x) := Subgroup.mem_center_iff.1 hx x
  rw [map_pow, e1, hcm.mul_pow, hn, mul_one]

end Lift

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem glaPComponent_self_of_quasisimple {S : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥S)
    (hO : GLAPPrimeCore 3 ↥S = ⊥) : GLAPComponent 3 S S := by
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hO]
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hL : (S.subgroupOf S).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  refine ⟨le_rfl, IsSubnormal.refl S, ⟨le_top, ?_, ?_⟩, ?_⟩
  · rw [hL]; exact IsSubnormal.refl _
  · rw [hL]
    let e : ↥S ≃* ↥(⊤ : Subgroup (↥S ⧸ GLAPPrimeCore 3 ↥S)) :=
      (MulEquiv.ofBijective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S))
        ⟨hinj, QuotientGroup.mk'_surjective _⟩).trans Subgroup.topEquiv.symm
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq
  · intro J hJ _ h
    have h1 : J.subgroupOf S = S.subgroupOf S := Subgroup.map_injective hinj h
    rw [Subgroup.subgroupOf_self] at h1
    exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hJ)

theorem normal_of_commutator_le {F S : Subgroup Y} (hSF : S ≤ F) (hcomm : ⁅F, F⁆ ≤ S) :
    (S.subgroupOf F).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSF]
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have h1 : ⁅g, n⁆ ∈ S := hcomm (Subgroup.commutator_mem_commutator hg (hSF hn))
  have : g * n * g⁻¹ = ⁅g, n⁆ * n := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact S.mul_mem h1 hn

theorem layer_of_normal_quasisimple {F S : Subgroup Y} (hSF : S ≤ F) (hcomm : ⁅F, F⁆ ≤ S)
    (hpow : ∀ a ∈ F, ∃ n : ℕ, a ^ 3 ^ n ∈ S) (hq : CFSG.Open.IsQuasisimple ↥S)
    (hO : GLAPPrimeCore 3 ↥S = ⊥) :
    GLAPPrimeCore 3 ↥F = ⊥ ∧ (∀ J : Subgroup Y, GLAPComponent 3 F J ↔ J = S) ∧
      GLAPLayer 3 F = S := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hnorm := normal_of_commutator_le hSF hcomm
  have hOS : GLAPPrimeCoreOf 3 S = ⊥ := by
    rw [GLAPPrimeCoreOf, hO, Subgroup.map_bot]
  have hOF : GLAPPrimeCoreOf 3 F = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyF : y ∈ F := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 F) hy
    obtain ⟨n, hn⟩ := hpow y hyF
    have hyn : y ^ 3 ^ n ∈ GLAPPrimeCoreOf 3 F := Subgroup.pow_mem _ hy _
    have h1 : y ^ 3 ^ n ∈ GLAPPrimeCoreOf 3 (F ⊓ S) :=
      gLAPPrimeCoreOf_inf_le hp F S ⟨hyn, hn⟩
    rw [inf_eq_right.2 hSF, hOS, Subgroup.mem_bot] at h1
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 F)) := by
      have h2 : Nat.card (GLAPPrimeCoreOf 3 F) = Nat.card (GLAPPrimeCore 3 ↥F) :=
        Subgroup.card_map_of_injective F.subtype_injective
      rw [h2]; exact coprime_card_gLAPPrimeCore_aux 3 ↥F
    have h3 : orderOf y ∣ Nat.card (GLAPPrimeCoreOf 3 F) := by
      have := Subgroup.orderOf_dvd_natCard (GLAPPrimeCoreOf 3 F) hy
      exact this
    have h4 : orderOf y ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
    have h5 : Nat.Coprime (orderOf y) (3 ^ n) :=
      Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left h3 hcop.symm)
    have h6 := Nat.Coprime.eq_one_of_dvd h5 h4
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h6)
  have hOF' : GLAPPrimeCore 3 ↥F = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).1 hOF
  have hself := glaPComponent_self_of_quasisimple hq hO
  have comp : ∀ J : Subgroup Y, GLAPComponent 3 F J ↔ J = S := by
    intro J
    constructor
    · intro hJ
      have hJF : J ≤ F := hJ.1
      have hperf := glaPComponent_perfect hJ
      have hJS : J ≤ S := by
        calc J = ⁅J, J⁆ := hperf.symm
          _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hJF hJF
          _ ≤ S := hcomm
      have hsn : IsSubnormal J S := isSubnormal_of_le_of_le hJ.2.1 hJS hSF
      exact eq_of_isSubnormal_of_quasisimple hq hsn hperf (glaPComponent_ne_bot hJ)
    · rintro rfl
      exact glaPComponent_of_normal_sub hp hSF hnorm hself
  refine ⟨hOF', comp, le_antisymm (sSup_le fun A hA => ?_) (le_sSup ((comp S).2 rfl))⟩
  exact ((comp A).1 hA).le

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator
