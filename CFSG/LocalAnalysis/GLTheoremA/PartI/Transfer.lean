module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.BaseCase

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Coprime

variable {A Q : Type*} [Group A] [Group Q]

theorem exists_mem_ker_mul_commute {p : ℕ} (hp : p.Prime) (π : A →* Q)
    (hN : ¬ p ∣ Nat.card π.ker) {y : A} (hy : IsPGroup p (Subgroup.zpowers y)) {k : A}
    (hk : π k * π y = π y * π k) : ∃ n ∈ π.ker, k * n * y = y * (k * n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ g ∈ Subgroup.zpowers y, π k * π g = π g * π k := by
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [map_zpow]
    exact Commute.zpow_right (show Commute (π k) (π y) from hk) m
  have hmem : ∀ g ∈ Subgroup.zpowers y, ∀ o ∈ π.ker, k⁻¹ * (g * (k * o) * g⁻¹) ∈ π.ker := by
    intro g hg o ho
    rw [MonoidHom.mem_ker] at ho ⊢
    have h1 : π g * π k * (π g)⁻¹ = π k := by
      rw [← hcomm g hg, mul_inv_cancel_right]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ho, mul_one, h1, inv_mul_cancel]
  letI act : MulAction (Subgroup.zpowers y) π.ker :=
    { smul := fun g o => ⟨k⁻¹ * ((g : A) * (k * (o : A)) * (g : A)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show k⁻¹ * (((1 : Subgroup.zpowers y) : A) * (k * (o : A)) *
          ((1 : Subgroup.zpowers y) : A)⁻¹) = (o : A) by simp)
      mul_smul := fun g h o => Subtype.ext (show k⁻¹ * (((g * h : Subgroup.zpowers y) : A) *
          (k * (o : A)) * ((g * h : Subgroup.zpowers y) : A)⁻¹) = k⁻¹ * ((g : A) * (k * (k⁻¹ *
          ((h : A) * (k * (o : A)) * (h : A)⁻¹))) * (g : A)⁻¹) by
        simp only [Subgroup.coe_mul]; group) }
  obtain ⟨o, ho⟩ := hy.nonempty_fixed_point_of_prime_not_dvd_card π.ker hN
  have hfa : k⁻¹ * (y * (k * (o : A)) * y⁻¹) = o :=
    congrArg Subtype.val (ho ⟨y, Subgroup.mem_zpowers y⟩)
  refine ⟨o, o.2, ?_⟩
  have h2 : y * (k * (o : A)) * y⁻¹ = k * o := by
    calc y * (k * (o : A)) * y⁻¹ = k * (k⁻¹ * (y * (k * (o : A)) * y⁻¹)) := by group
      _ = k * o := by rw [hfa]
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

end Coprime

section Hom

variable {A Q : Type} [Group A] [Finite A] [Group Q] {p : ℕ}

omit [Finite A] in
private theorem coprime_card_inf_ker (hp : p.Prime) {ψ : A →* Q} (hN : ¬ p ∣ Nat.card ψ.ker)
    (X : Subgroup A) : Nat.Coprime p (Nat.card ↥(X ⊓ ψ.ker)) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
    hN (hd.trans (Subgroup.card_dvd_of_le inf_le_right))

omit [Finite A] in
theorem map_inf_centralizer_of_ker_le (hp : p.Prime) {ψ : A →* Q} (hN : ¬ p ∣ Nat.card ψ.ker)
    {K : Subgroup A} (hK : ψ.ker ≤ K) {y : A} (hy : IsPGroup p (Subgroup.zpowers y)) :
    K.map ψ ⊓ Subgroup.centralizer ({ψ y} : Set Q) =
      (K ⊓ Subgroup.centralizer ({y} : Set A)).map ψ := by
  apply le_antisymm
  · rintro _ ⟨⟨k, hk, rfl⟩, hC⟩
    obtain ⟨n, hn, hkn⟩ := exists_mem_ker_mul_commute hp ψ hN hy
      (Subgroup.mem_centralizer_singleton_iff.1 hC)
    refine ⟨k * n, ⟨K.mul_mem hk (hK hn), Subgroup.mem_centralizer_singleton_iff.2 hkn⟩, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.1 hn, mul_one]
  · rintro _ ⟨c, ⟨hcK, hcC⟩, rfl⟩
    refine ⟨⟨c, hcK, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hcC]

theorem glaPComponent_map_of_ker_le (hp : p.Prime) {ψ : A →* Q} (hN : ¬ p ∣ Nat.card ψ.ker)
    {K : Subgroup A} (hK : ψ.ker ≤ K) {y : A} (hy : IsPGroup p (Subgroup.zpowers y))
    {J : Subgroup A} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set A)) J) :
    GLAPComponent p (K.map ψ ⊓ Subgroup.centralizer ({ψ y} : Set Q)) (J.map ψ) := by
  have h := glaPComponent_map hp ψ
    (coprime_card_inf_ker hp hN (K ⊓ Subgroup.centralizer ({y} : Set A))) hJ
  rwa [← map_inf_centralizer_of_ker_le hp hN hK hy] at h

theorem nonempty_pQuot_equiv_map (hp : p.Prime) {ψ : A →* Q} (hN : ¬ p ∣ Nat.card ψ.ker)
    (J : Subgroup A) : Nonempty (PQuot p J ≃* PQuot p (J.map ψ)) :=
  ⟨lcEquiv hp ψ J (coprime_card_inf_ker hp hN J)⟩

omit [Finite A] in
theorem nonempty_pQuot_equiv_map_self {ψ : A →* Q} {K : Subgroup A}
    (hcore : GLAPPrimeCoreOf p K = ψ.ker ⊓ K) : Nonempty (PQuot p K ≃* ↥(K.map ψ)) := by
  have hker : (ψ.subgroupMap K).ker = GLAPPrimeCore p ↥K := by
    rw [Subgroup.ker_subgroupMap, ← Subgroup.inf_subgroupOf_right, ← hcore]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (ψ.subgroupMap_surjective K))⟩

end Hom

section Ambient

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem glaPComponent_subgroupOf (hp : p.Prime) {H X K : Subgroup G} (hXH : X ≤ H)
    (hK : GLAPComponent p X K) :
    GLAPComponent p (X.subgroupOf H) (K.subgroupOf H) := by
  have hker : Nat.Coprime p (Nat.card ↥(X.subgroupOf H ⊓ H.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hK' : GLAPComponent p ((X.subgroupOf H).map H.subtype) K := by
    rw [Subgroup.map_subgroupOf_eq_of_le hXH]
    exact hK
  obtain ⟨K₀, hK₀, hmap⟩ := exists_glaPComponent_map_eq hp H.subtype hker hK'
  have hK₀eq : K₀ = K.subgroupOf H := by
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective K₀).symm
  rwa [← hK₀eq]

theorem nonempty_pQuot_equiv_subgroupOf (p : ℕ) {H K : Subgroup G} (hKH : K ≤ H) :
    Nonempty (PQuot p (K.subgroupOf H) ≃* PQuot p K) :=
  ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hKH)
    (glaPPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hKH))⟩

theorem map_subtype_glaPPrimeCoreOf_subgroupOf (p : ℕ) {H K : Subgroup G} (hKH : K ≤ H) :
    (GLAPPrimeCoreOf p (K.subgroupOf H)).map H.subtype = GLAPPrimeCoreOf p K := by
  have h := glaPPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hKH)
  unfold GLAPPrimeCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

theorem isPGroup_zpowers_of_pow_eq_one {y : G} (h : y ^ p = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, h, one_zpow]
  rfl

theorem isPGroup_zpowers_mk {H : Subgroup G} {y : G} (hyH : y ∈ H)
    (hy : IsPGroup p (Subgroup.zpowers y)) :
    IsPGroup p (Subgroup.zpowers (⟨y, hyH⟩ : ↥H)) := by
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow (p := p)).1 hy
  refine IsPGroup.of_card_dvd_pow (n := n) ?_
  rwa [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]

theorem subgroupOf_inf_centralizer {H K : Subgroup G} {y : G} (hyH : y ∈ H) :
    (K ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf H =
      K.subgroupOf H ⊓ Subgroup.centralizer ({(⟨y, hyH⟩ : ↥H)} : Set ↥H) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr Iff.rfl ⟨fun hc => Subtype.ext hc, fun hc => congrArg Subtype.val hc⟩

theorem exists_pQuot_transfer (hp : p.Prime) {K : Subgroup G} {y : G}
    (hy : IsPGroup p (Subgroup.zpowers y)) (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (K' : Subgroup Q) (y' : Q),
      Nonempty (↥K' ≃* PQuot p K) ∧ y' ∈ Subgroup.normalizer (K' : Set Q) ∧
      (∀ n : ℕ, y ^ n = 1 → y' ^ n = 1) ∧
      (K' ≤ Subgroup.centralizer ({y'} : Set Q) → CentMod p K y) ∧
      ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
        ∃ J' : Subgroup Q, GLAPComponent p (K' ⊓ Subgroup.centralizer ({y'} : Set Q)) J' ∧
          Nonempty (PQuot p J ≃* PQuot p J') := by
  classical
  set H : Subgroup G := K ⊔ Subgroup.zpowers y
  have hKH : K ≤ H := le_sup_left
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  set y₀ : ↥H := ⟨y, hyH⟩
  set K₀ : Subgroup ↥H := K.subgroupOf H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hyK)
  haveI hK₀n : K₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK
  set N₀ : Subgroup ↥H := GLAPPrimeCoreOf p K₀
  haveI hN₀n : N₀.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p K₀
    rw [Subgroup.normalizer_eq_top_iff.2 hK₀n, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  have hker : (QuotientGroup.mk' N₀).ker = N₀ := QuotientGroup.ker_mk' N₀
  have hN₀K : N₀ ≤ K₀ := Subgroup.map_subtype_le _
  have hN : ¬ p ∣ Nat.card (QuotientGroup.mk' N₀).ker := by
    rw [hker]
    exact not_dvd_card_glaPPrimeCoreOf hp K₀
  have hK : (QuotientGroup.mk' N₀).ker ≤ K₀ := by
    rw [hker]
    exact hN₀K
  have hy₀p : IsPGroup p (Subgroup.zpowers y₀) := isPGroup_zpowers_mk hyH hy
  refine ⟨↥H ⧸ N₀, inferInstance, inferInstance, K₀.map (QuotientGroup.mk' N₀),
    QuotientGroup.mk' N₀ y₀, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := QuotientGroup.mk' N₀) (K := K₀)
      (by rw [hker, inf_eq_left.2 hN₀K])
    obtain ⟨e₂⟩ := nonempty_pQuot_equiv_subgroupOf p hKH
    exact ⟨e₁.symm.trans e₂⟩
  · have hKbar : (K₀.map (QuotientGroup.mk' N₀)).Normal :=
      hK₀n.map _ (QuotientGroup.mk'_surjective N₀)
    rw [Subgroup.normalizer_eq_top_iff.2 hKbar]
    exact Subgroup.mem_top _
  · intro n hn
    have h : y₀ ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [← map_pow, h, map_one]
  · intro hle
    rw [centMod_iff]
    refine ⟨hyK, fun l hl => ?_⟩
    have hlH : l ∈ H := hKH hl
    have hl₀ : (⟨l, hlH⟩ : ↥H) ∈ K₀ := Subgroup.mem_subgroupOf.2 hl
    have hc : QuotientGroup.mk' N₀ ⟨l, hlH⟩ * QuotientGroup.mk' N₀ y₀ =
        QuotientGroup.mk' N₀ y₀ * QuotientGroup.mk' N₀ ⟨l, hlH⟩ :=
      Subgroup.mem_centralizer_singleton_iff.1 (hle ⟨⟨l, hlH⟩, hl₀, rfl⟩)
    have hmem : ⁅(⟨l, hlH⟩ : ↥H), y₀⁆ ∈ N₀ := by
      rw [← QuotientGroup.ker_mk' N₀, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul,
        map_mul, map_inv, map_inv, hc]
      group
    have h2 : (⁅(⟨l, hlH⟩ : ↥H), y₀⁆ : ↥H).val ∈ GLAPPrimeCoreOf p K := by
      rw [← map_subtype_glaPPrimeCoreOf_subgroupOf p hKH]
      exact ⟨_, hmem, rfl⟩
    exact h2
  · intro J hJ
    have hKCH : K ⊓ Subgroup.centralizer ({y} : Set G) ≤ H := inf_le_left.trans hKH
    have h1 := glaPComponent_subgroupOf hp hKCH hJ
    rw [subgroupOf_inf_centralizer hyH] at h1
    refine ⟨(J.subgroupOf H).map (QuotientGroup.mk' N₀),
      glaPComponent_map_of_ker_le hp hN hK hy₀p h1, ?_⟩
    obtain ⟨e₁⟩ := nonempty_pQuot_equiv_subgroupOf p (hJ.1.trans hKCH)
    obtain ⟨e₂⟩ := nonempty_pQuot_equiv_map hp hN (J.subgroupOf H)
    exact ⟨e₁.symm.trans e₂⟩

end Ambient

end CFSG.LocalAnalysis.GLTheoremA
