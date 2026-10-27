module

public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

omit [Finite G] in
theorem le_normalizer_glaPPrimeCoreOf_of_le_normalizer {p : ℕ} {X M : Subgroup G}
    (h : M ≤ Subgroup.normalizer (X : Set G)) :
    M ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := by
  intro g hg
  have h1 := mem_normalizer_iff_gLBConj_eq.1 (h hg)
  rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, h1]

omit [Finite G] in
theorem isComponentOf_map_of_ker {p : ℕ} {X M J : Subgroup G} {Q : Type} [Group Q]
    (π : ↥M →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = (GLAPPrimeCoreOf p X).subgroupOf M) (hXM : X ≤ M)
    (hXn : M ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X)
    (hJ : IsComponentOf (barX p X J) ⊤) : IsComponentOf ((J.subgroupOf M).map π) ⊤ := by
  set C := GLAPPrimeCore p ↥X with hC
  let ψ : ↥X →* Q := π.comp (Subgroup.inclusion hXM)
  have hψ : ∀ x : ↥X, ψ x = 1 ↔ x ∈ C := by
    intro x
    have h1 : ψ x = 1 ↔ Subgroup.inclusion hXM x ∈ π.ker := (MonoidHom.mem_ker).symm
    rw [h1, hker, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem X.subtype_injective
  let ψbar : (↥X ⧸ C) →* Q := QuotientGroup.lift C ψ (fun x hx => (hψ x).2 hx)
  have hinj : Function.Injective ψbar := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have h1 : ψ x = ψ y := hab
    have h2 : ψ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact (QuotientGroup.eq).2 ((hψ _).1 h2)
  have hmap : (barX p X J).map ψbar = (J.subgroupOf M).map π := by
    ext q
    simp only [barX, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Subgroup.inclusion hXM x, hx, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨QuotientGroup.mk' C ⟨m, hJX hm⟩, ⟨⟨m, hJX hm⟩, hm, rfl⟩, rfl⟩
  have hXN : (X.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hXn
  have hrange : (⊤ : Subgroup (↥X ⧸ C)).map ψbar = (X.subgroupOf M).map π := by
    ext q
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨a, rfl⟩
      induction a using QuotientGroup.induction_on with | H x => ?_
      exact ⟨Subgroup.inclusion hXM x, x.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨QuotientGroup.mk' C ⟨m, hm⟩, rfl⟩
  rw [← hmap]
  refine ⟨le_top, ?_, ?_⟩
  · have h1 := isSubnormal_map' ψbar hJ.2.1
    have h2 : IsSubnormal ((⊤ : Subgroup (↥X ⧸ C)).map ψbar) ⊤ := by
      rw [hrange]
      exact isSubnormal_of_normal (hXN.map π hπ)
    exact isSubnormal_trans' h1 h2
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      ((barX p X J).equivMapOfInjective ψbar hinj) hJ.2.2

theorem lemma82 (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessSubgroup p B M₀) {N : Subgroup G} (hN : IsTwoLocal N) (hBN : B ≤ N)
    {J : Subgroup G} (hJ : GLAPComponent 2 (GLAPPrimeCoreOf p M₀) J) :
    ¬ J ≤ (N ⊓ GLAPPrimeCoreOf p M₀) ⊔ GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀) := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := GLAPPrimeCoreOf p M₀ with hX
  set T := GLAPPrimeCoreOf 2 X with hT
  set R := pCoreOf 2 N with hR
  obtain ⟨hJX, -, hJcomp, -⟩ := hJ
  have hXM : X ≤ M₀ := Subgroup.map_subtype_le _
  have hTX : T ≤ X := Subgroup.map_subtype_le _
  have hXn : M₀ ≤ Subgroup.normalizer (X : Set G) := le_normalizer_glaPPrimeCoreOf p M₀
  have hTn : M₀ ≤ Subgroup.normalizer (T : Set G) :=
    le_normalizer_glaPPrimeCoreOf_of_le_normalizer hXn
  have hRM : R ≤ M₀ := hM.pCoreOf_two_le hS hB hBN
  have hTM : T ≤ M₀ := hTX.trans hXM
  have hTm : (T.subgroupOf M₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).2 hTn
  let π : ↥M₀ →* ↥M₀ ⧸ T.subgroupOf M₀ := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = T.subgroupOf M₀ := QuotientGroup.ker_mk' _
  have hcomp : IsComponentOf ((J.subgroupOf M₀).map π) ⊤ :=
    isComponentOf_map_of_ker π hπ hker hXM hXn hJX hJcomp
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hRq : IsPGroup 2 ((R.subgroupOf M₀).map π) :=
    (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm).map π
  have hKn : ((N ⊓ X).subgroupOf M₀).map π ≤
      Subgroup.normalizer (((R.subgroupOf M₀).map π : Subgroup _) : Set _) := by
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map π)
    rw [normalizer_subgroupOf_eq hRM]
    intro k hk
    have hkN : (k : G) ∈ N := (Subgroup.mem_subgroupOf.1 hk).1
    exact (Subgroup.mem_subgroupOf).2 (le_normalizer_pCoreOf 2 N hkN)
  have hJK : (J.subgroupOf M₀).map π ≤ ((N ⊓ X).subgroupOf M₀).map π := by
    have h1 : J.subgroupOf M₀ ≤ ((N ⊓ X) ⊔ T).subgroupOf M₀ := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx))
    rw [Subgroup.subgroupOf_sup (inf_le_right.trans hXM) hTM] at h1
    have h2 := Subgroup.map_mono (f := π) h1
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 hker.ge, sup_bot_eq] at h2
  have hcomm := commutator_eq_bot_of_normalizes hcomp hRq (hJK.trans hKn)
  have hRT : R ⊓ T = ⊥ := by
    have hP : IsPGroup 2 ↥(R ⊓ T) := hR2.to_inf_left
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
    have h2 : 2 ∣ Nat.card ↥(R ⊓ T) := hn ▸ dvd_pow_self 2 hn0
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_two X
      (h2.trans (Subgroup.card_dvd_of_le inf_le_right))
  have key : ∀ q ∈ (J.subgroupOf M₀).map π, ∃ k : G, ∃ hk : k ∈ M₀, k ∈ R ∧ π ⟨k, hk⟩ = q := by
    intro q hq
    obtain ⟨⟨k, hkM⟩, hk, rfl⟩ := hJK hq
    have hkNX : k ∈ N ⊓ X := Subgroup.mem_subgroupOf.1 hk
    refine ⟨k, hkM, ?_, rfl⟩
    have hcent : k ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hrM : r ∈ M₀ := hRM hr
      have hπr : π ⟨r, hrM⟩ ∈ (R.subgroupOf M₀).map π := ⟨_, Subgroup.mem_subgroupOf.2 hr, rfl⟩
      have h1 := Subgroup.commutator_mem_commutator hq hπr
      rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement] at h1
      rw [commutatorElement_def] at h1
      have h2 := MonoidHom.mem_ker.2 h1
      rw [hker] at h2
      have h3 : k * r * k⁻¹ * r⁻¹ ∈ T := Subgroup.mem_subgroupOf.1 h2
      have h4 : k * r * k⁻¹ * r⁻¹ ∈ R := by
        have hkn := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 N hkNX.1) r).1 hr
        exact R.mul_mem hkn (R.inv_mem hr)
      have h5 : k * r * k⁻¹ * r⁻¹ ∈ R ⊓ T := ⟨h4, h3⟩
      rw [hRT, Subgroup.mem_bot] at h5
      have : k * r = r * k := by
        have := congrArg (· * (r * k)) h5
        simpa [mul_assoc] using this
      exact this.symm
    exact hS.charTwo N hN ⟨hkNX.1, hcent⟩
  have hJ2 : IsPGroup 2 ↥((J.subgroupOf M₀).map π) := by
    rintro ⟨q, hq⟩
    obtain ⟨k, hkM, hkR, rfl⟩ := key q hq
    obtain ⟨n, hn⟩ := hR2 ⟨k, hkR⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : k ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h2 : (⟨k, hkM⟩ : ↥M₀) ^ (2 ^ n) = 1 := Subtype.ext h1
    show (π ⟨k, hkM⟩) ^ (2 ^ n) = 1
    rw [← map_pow, h2, map_one]
  have hnil := hJ2.isNilpotent
  have hperf : Group.IsPerfect ↥((J.subgroupOf M₀).map π) := ⟨hcomp.2.2.1⟩
  have hsimple := hcomp.2.2.2
  have : Nontrivial ↥((J.subgroupOf M₀).map π) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥((J.subgroupOf M₀).map π))).nontrivial
  exact Group.IsPerfect.not_isNilpotent _ hnil

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
