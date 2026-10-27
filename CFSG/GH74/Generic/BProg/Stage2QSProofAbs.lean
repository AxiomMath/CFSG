module

public import CFSG.GH74.Generic.BProg.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic Subgroup
open scoped commutatorElement MatrixGroups

theorem exists_pow_two_power_lift {A B : Type*} [Group A] [Group B] [Finite A]
    (φ : A →* B) (g : A) {k : ℕ} (hk : (φ g) ^ (2 ^ k) = 1) :
    ∃ n e : ℕ, (g ^ n) ^ (2 ^ e) = 1 ∧ φ (g ^ n) = φ g := by
  obtain ⟨e, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hco : Nat.Coprime (orderOf (φ g)) r :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hr)).coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨N, hN1, hN2⟩ := Nat.chineseRemainder hco 1 0
  refine ⟨N, e, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := (Nat.modEq_zero_iff_dvd).1 hN2
    have hNe : N * 2 ^ e = orderOf g * s := by rw [hs, hord]; ring
    rw [← pow_mul, hNe, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow]
    conv_rhs => rw [← pow_one (φ g)]
    exact pow_eq_pow_iff_modEq.2 hN1

theorem mem_of_two_pow_eq_one_of_odd_normalizing {X : Type*} [Group X] [Finite X]
    {K O : Subgroup X} (hO : O ≤ normalizer (K : Set X)) (hodd : Odd (Nat.card O))
    {g k m : X} (hk : k ∈ K) (hm : m ∈ O) (hg : g = k * m) {e : ℕ} (hge : g ^ (2 ^ e) = 1) :
    g ∈ K := by
  classical
  set N : Subgroup X := normalizer (K : Set X) with hN
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hmN : m ∈ N := hO hm
  have hkN : k ∈ N := hKN hk
  have hgN : g ∈ N := hg ▸ N.mul_mem hkN hmN
  let q : ↥N →* ↥N ⧸ K.subgroupOf N := QuotientGroup.mk' _
  have hqk : q ⟨k, hkN⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (by
    rw [Subgroup.mem_subgroupOf]; exact hk)
  have h1 : q ⟨g, hgN⟩ = q ⟨m, hmN⟩ := by
    have : (⟨g, hgN⟩ : ↥N) = ⟨k, hkN⟩ * ⟨m, hmN⟩ := Subtype.ext hg
    rw [this, map_mul, hqk, one_mul]
  have hd1 : orderOf (q ⟨g, hgN⟩) ∣ 2 ^ e := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (⟨g, hgN⟩ : ↥N) ^ (2 ^ e) = 1 := Subtype.ext (by simpa using hge)
    rw [this, map_one]
  have hd2 : orderOf (q ⟨g, hgN⟩) ∣ Nat.card O := by
    rw [h1]
    have h3 := orderOf_map_dvd q (⟨m, hmN⟩ : ↥N)
    rw [Subgroup.orderOf_mk] at h3
    exact h3.trans (Subgroup.orderOf_dvd_natCard O hm)
  have hco : Nat.Coprime (2 ^ e) (Nat.card O) :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.2 hodd)
  have h4 : orderOf (q ⟨g, hgN⟩) = 1 := (hco.coprime_dvd_left hd1).eq_one_of_dvd hd2
  have h5 := (QuotientGroup.eq_one_iff (⟨g, hgN⟩ : ↥N)).1 (orderOf_eq_one_iff.1 h4)
  rwa [Subgroup.mem_subgroupOf] at h5

theorem mem_of_two_pow_eq_one_of_map_mem {X : Type*} [Group X] [Finite X] {K₀ : Subgroup X}
    (hK : IsPComponent 2 K₀) {g : X} {e : ℕ} (hg : g ^ (2 ^ e) = 1)
    (hmem : QuotientGroup.mk' (pPrimeCore 2 X) g ∈ K₀.map (QuotientGroup.mk' (pPrimeCore 2 X))) :
    g ∈ K₀ := by
  obtain ⟨k, hk, hkg⟩ := hmem
  have hm : k⁻¹ * g ∈ pPrimeCore 2 X := by
    have : QuotientGroup.mk' (pPrimeCore 2 X) (k⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hkg, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  exact mem_of_two_pow_eq_one_of_odd_normalizing (K := K₀) (O := pPrimeCore 2 X)
    (CFSG.ComponentClassification.UnbalancedLayer.pPrimeCore_le_normalizer hK)
    (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))) hk hm (by group) hg

theorem isQuasisimple_of_perfect_of_central_ker {K Q : Type*} [Group K] [Group Q]
    (hperf : Group.IsPerfect K) (ψ : K →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center K) (hQ : IsQuasisimple Q) : IsQuasisimple K := by
  have hq := CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_extension_derived
    (A := ψ.ker) hker
    ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).2 hQ)
  have htop : commutator K = ⊤ := hperf.commutator_eq_top
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).1 hq

theorem isQuasisimple_of_isPComponent_of_noncomm {X : Type*} [Group X] [Finite X]
    {K₀ : Subgroup X} (hK : IsPComponent 2 K₀) {l₁ l₂ : X} (h₁ : l₁ ∈ K₀) (h₂ : l₂ ∈ K₀)
    (hc : ∀ w ∈ pPrimeCore 2 X, l₁ * w = w * l₁)
    (hnc : QuotientGroup.mk' (pPrimeCore 2 X) l₁ * QuotientGroup.mk' (pPrimeCore 2 X) l₂ ≠
      QuotientGroup.mk' (pPrimeCore 2 X) l₂ * QuotientGroup.mk' (pPrimeCore 2 X) l₁) :
    K₀ ≤ centralizer (pPrimeCore 2 X : Set X) ∧ IsQuasisimple ↥K₀ := by
  classical
  have hperf : Group.IsPerfect ↥K₀ :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hK
  set O : Subgroup X := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  obtain ⟨Kb, hKbc, hsub, hmap, hmin⟩ := hK
  subst hmap
  set D : Subgroup X := K₀ ⊓ centralizer (O : Set X) with hD
  have hDK : D ≤ K₀ := inf_le_left
  have hDnorm : (D.subgroupOf K₀).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hDK).2 fun d k hd hk =>
      Subgroup.mem_inf.2 ⟨K₀.mul_mem (K₀.mul_mem hk (Subgroup.mem_inf.1 hd).1) (K₀.inv_mem hk), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : k⁻¹ * w * k ∈ O := by
      have := (inferInstance : O.Normal).conj_mem w hw k⁻¹
      simpa using this
    have hdw : (k⁻¹ * w * k) * d = d * (k⁻¹ * w * k) :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hd).2 _ hw'
    calc w * (k * d * k⁻¹) = k * ((k⁻¹ * w * k) * d) * k⁻¹ := by group
      _ = k * (d * (k⁻¹ * w * k)) * k⁻¹ := by rw [hdw]
      _ = (k * d * k⁻¹) * w := by group
  have hNnorm : ((D.map π).subgroupOf (K₀.map π)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d, hd, hdn⟩ := hn
    obtain ⟨k, hk, hkg⟩ := g.2
    refine ⟨k * d * k⁻¹, (Subgroup.normal_subgroupOf_iff hDK).1 hDnorm d k hd hk, ?_⟩
    rw [map_mul, map_mul, map_inv, hkg, hdn]
    rfl
  have hQ : IsQuasisimple ↥(K₀.map π) := hKbc.1
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hQ hNnorm with
    htop | hcen
  · have hle : K₀.map π ≤ D.map π := fun a ha => by
      have : (⟨a, ha⟩ : ↥(K₀.map π)) ∈ (D.map π).subgroupOf (K₀.map π) := by
        rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    have heq : D.map π = K₀.map π := le_antisymm (Subgroup.map_mono hDK) hle
    have hDeq : D = K₀ := by
      by_contra hne
      exact hmin D (lt_of_le_of_ne hDK hne)
        (Subgroup.IsSubnormal.trans hDK hDnorm.isSubnormal hsub) heq
    have hKC : K₀ ≤ centralizer (O : Set X) := fun k hk => by
      rw [← hDeq] at hk
      exact (Subgroup.mem_inf.1 hk).2
    refine ⟨hKC, ?_⟩
    let ψ : ↥K₀ →* ↥(K₀.map π) :=
      (π.comp K₀.subtype).codRestrict (K₀.map π) (fun k => ⟨k, k.2, rfl⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    have hker : ψ.ker ≤ center ↥K₀ := by
      intro z hz
      have hz1 : π (z : X) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hz)
      have hzO : (z : X) ∈ O := (QuotientGroup.eq_one_iff _).1 hz1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKC g.2) z hzO).symm
    exact isQuasisimple_of_perfect_of_central_ker hperf ψ hψ hker hQ
  · exfalso
    apply hnc
    have hl₁ : (⟨π l₁, Subgroup.mem_map_of_mem π h₁⟩ : ↥(K₀.map π)) ∈
        (D.map π).subgroupOf (K₀.map π) := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem π
        (Subgroup.mem_inf.2 ⟨h₁, Subgroup.mem_centralizer_iff.2 fun w hw => (hc w hw).symm⟩)
    have := Subgroup.mem_center_iff.1 (hcen hl₁) ⟨π l₂, Subgroup.mem_map_of_mem π h₂⟩
    exact (congrArg Subtype.val this).symm

theorem exists_noncomm_two_elements_of_perfect {M : Type*} [Group M] [Finite M]
    [Group.IsPerfect M] [Nontrivial M] :
    ∃ a b : M, (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ (∃ k : ℕ, b ^ (2 ^ k) = 1) ∧ a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have htop : oPrimeResidual 2 M = ⊤ := oPrimeResidual_eq_top_of_isPerfect
  have h1 : (⊤ : Subgroup M) ≤ centralizer {x : M | ∃ k : ℕ, x ^ (2 ^ k) = 1} := by
    rw [← htop]
    refine (Subgroup.closure_le _).2 fun a ha => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun b hb => (hcon b a hb ha)
  have h2 : {x : M | ∃ k : ℕ, x ^ (2 ^ k) = 1} ⊆ (center M : Set M) := fun a ha => by
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.1 (h1 (Subgroup.mem_top g)) a ha).symm
  have h3 : (⊤ : Subgroup M) ≤ center M := by
    rw [← htop]
    exact (Subgroup.closure_le _).2 h2
  have hcomm : IsMulCommutative M :=
    ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h3 (Subgroup.mem_top a)) b).symm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative M hcomm

theorem exists_noncomm_sl23 : ∃ s t : SL(2, ZMod 3), s ^ 4 = 1 ∧ t ^ 4 = 1 ∧ s * t ≠ t * s := by
  refine ⟨⟨!![0, 1; 2, 0], by decide⟩, ⟨!![1, 1; 1, 2], by decide⟩, ?_, ?_, ?_⟩ <;> decide

end CFSG.GH74.Generic.BProg
