module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnLink

public section

namespace CFSG.ClassicalInvolution.Asc77.ExactLayer

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfectResidualOf_normalizer_contains)
open scoped commutatorElement MatrixGroups

section Core

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {K : Subgroup G} {z c : G}

abbrev exactCore (c : G) (K : Subgroup G) : Subgroup G :=
  triangleResidual K c

theorem exactCore_def (c : G) (K : Subgroup G) :
    exactCore c K = perfectResidualOf (K ⊓ Subgroup.centralizer ({c} : Set G)) := rfl

theorem exactCore_le (c : G) (K : Subgroup G) :
    exactCore c K ≤ K ⊓ Subgroup.centralizer ({c} : Set G) :=
  Subgroup.map_subtype_le _

theorem exactCore_le_left (c : G) (K : Subgroup G) : exactCore c K ≤ K :=
  (exactCore_le c K).trans inf_le_left

theorem exactCore_le_centralizer (c : G) (K : Subgroup G) :
    exactCore c K ≤ Subgroup.centralizer ({c} : Set G) :=
  (exactCore_le c K).trans inf_le_right

theorem isPGroup_zpowers_of_sq_eq_one (hc : c * c = 1) : IsPGroup 2 (Subgroup.zpowers c) := by
  refine isPGroup_two_of_sq_eq_one fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← (Commute.refl c).mul_zpow, hc, one_zpow]

theorem isPGroup_zpowers_of_mem_isElemAbelian {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hc : c ∈ B) : IsPGroup 2 (Subgroup.zpowers c) :=
  isPGroup_zpowers_of_sq_eq_one (by simpa only [pow_two] using hB.2 c hc)

variable [Finite G]

theorem cover_centralizer (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) :
    ∀ x ∈ K, ∃ h ∈ K ⊓ Subgroup.centralizer ({c} : Set G), ∃ n ∈ oddCoreIn K, x = h * n := by
  intro x hx
  obtain ⟨h, hh, n, hn, hxhn⟩ :=
    exists_mem_inf_centralizer_mul hc2 (Subgroup.zpowers_le.mpr hcK) hx
  exact ⟨h, by rwa [centralizer_zpowers_eq_singleton'] at hh, n, hn, hxhn⟩

theorem axisResidual_exactCore (hK : IsClassicalMember p f K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K) :
    AxisResidual K (Subgroup.zpowers c) (exactCore c K) z := by
  have cK := isCentralInvolution_of_isClassicalMember hK
  have h := axisResidual_perfectResidual hK.perfect hK.mem cK.sq
    (fun x hx => (cK.central x hx).symm) hK.subnormal hc2 (Subgroup.zpowers_le.mpr hcK)
  simpa only [exactCore, triangleResidual, centralizer_zpowers_eq_singleton'] using h

variable (hK : IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
  (hcK : c ∈ trivialOnQuot K)
include hK hc2 hcK

theorem exactCore_cover : ∀ x ∈ K, ∃ i ∈ exactCore c K, ∃ n ∈ oddCoreIn K, x = i * n :=
  (axisResidual_exactCore hK hc2 hcK).cover

theorem mem_exactCore : z ∈ exactCore c K :=
  (axisResidual_exactCore hK hc2 hcK).mem

theorem oddCoreIn_exactCore : oddCoreIn (exactCore c K) = exactCore c K ⊓ oddCoreIn K :=
  (axisResidual_exactCore hK hc2 hcK).oddCoreIn_eq

theorem nonempty_equiv_exactCore :
    Nonempty (↥(exactCore c K) ⧸ classicalInvolutionOddCore ↥(exactCore c K) ≃*
      ↥K ⧸ classicalInvolutionOddCore ↥K) :=
  (axisResidual_exactCore hK hc2 hcK).nonempty_equiv

theorem nonempty_equiv_sl2_exactCore :
    Nonempty (↥(exactCore c K) ⧸ classicalInvolutionOddCore ↥(exactCore c K) ≃*
      SL(2, GaloisField p f)) := by
  obtain ⟨e⟩ := nonempty_equiv_exactCore hK hc2 hcK
  obtain ⟨e'⟩ := hK.nonempty_equiv
  exact ⟨e.trans e'⟩

omit hK hc2 hcK in
theorem perfect_exactCore (c : G) (K : Subgroup G) : Group.IsPerfect ↥(exactCore c K) :=
  finite_perfectResidualOf_isPerfect _

theorem isSectionMember_exactCore :
    IsSectionMember p f (Subgroup.centralizer ({c} : Set G)) (exactCore c K) z := by
  have h := (axisResidual_exactCore hK hc2 hcK).isSectionMember hK (perfect_exactCore c K)
  simpa only [centralizer_zpowers_eq_singleton'] using h

theorem isClassicalMember_exactCore_subgroupOf {Y : Subgroup G} (hY : exactCore c K ≤ Y)
    (hYc : Y ≤ Subgroup.centralizer ({c} : Set G)) :
    IsClassicalMember p f ((exactCore c K).subgroupOf Y)
      (⟨z, hY (mem_exactCore hK hc2 hcK)⟩ : Y) := by
  have h := ((isSectionMember_exactCore hK hc2 hcK).restrict hYc hY).toIn
  obtain ⟨hz, h⟩ := h
  exact h

omit hc2 hcK in
theorem eq_one_or_eq_of_mem_exactCore (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {x : G}
    (hx : x ∈ exactCore c K) (hx2 : x * x = 1) : x = 1 ∨ x = z :=
  eq_one_or_eq_of_isClassicalMember hp2 hq hK (exactCore_le_left c K hx) hx2

end Core

section Action

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z c : G}

theorem exactCore_conjSub (g c : G) (K : Subgroup G) :
    exactCore (g * c * g⁻¹) (conjSub g K) = conjSub g (exactCore c K) := by
  unfold exactCore triangleResidual
  have h2 : conjSub g (K ⊓ Subgroup.centralizer ({c} : Set G)) =
      conjSub g K ⊓ conjSub g (Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.map_inf_eq _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [conjSub_centralizer_singleton] at h2
  rw [← h2, perfectResidualOf_conjSub]

omit [Finite G] in
theorem exactCore_eq_self (hK : Group.IsPerfect ↥K) (hKc : K ≤ Subgroup.centralizer ({c} : Set G)) :
    exactCore c K = K := by
  have hinf : K ⊓ Subgroup.centralizer ({c} : Set G) = K := inf_eq_left.mpr hKc
  unfold exactCore triangleResidual
  rw [hinf]
  exact le_antisymm (Subgroup.map_subtype_le _) (le_perfectResidualOf_of_perfect le_rfl hK)

theorem mem_trivialOnQuot_of_le_centralizer (hKc : K ≤ Subgroup.centralizer ({c} : Set G)) :
    c ∈ trivialOnQuot K :=
  mem_trivialOnQuot_of_centralizes fun _ hj =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKc hj)).symm

theorem mem_trivialOnQuot_exactCore_self (c : G) (K : Subgroup G) :
    c ∈ trivialOnQuot (exactCore c K) :=
  mem_trivialOnQuot_of_le_centralizer (exactCore_le_centralizer c K)

variable (hK : IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
  (hcK : c ∈ trivialOnQuot K)
include hK hc2 hcK

theorem mem_trivialOnQuot_exactCore {b : G} (hb : b ∈ trivialOnQuot K)
    (hbc : b ∈ Subgroup.centralizer ({c} : Set G)) : b ∈ trivialOnQuot (exactCore c K) := by
  refine ⟨?_, fun l hl => commutator_mem_oddCoreIn_triangleResidual hb hbc
    (axisResidual_exactCore hK hc2 hcK) hl⟩
  have hnorm : b ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf hb.1 (Subgroup.le_normalizer hbc)
  exact perfectResidualOf_normalizer_contains _ hnorm

theorem le_trivialOnQuot_exactCore {B : Subgroup G} (hBc : B ≤ Subgroup.centralizer ({c} : Set G))
    (hB : B ≤ trivialOnQuot K) : B ≤ trivialOnQuot (exactCore c K) := fun _ hb =>
  mem_trivialOnQuot_exactCore hK hc2 hcK (hB hb) (hBc hb)

end Action

section Family

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
  {K K' : Subgroup G}

@[expose] def tqMembers (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  {K | K ∈ Ω ∧ c ∈ trivialOnQuot K}

@[expose] def exactFamily (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  residualFamily c (tqMembers Ω c)

theorem mem_tqMembers_iff : K ∈ tqMembers Ω c ↔ K ∈ Ω ∧ c ∈ trivialOnQuot K := Iff.rfl

theorem mem_exactFamily_iff :
    K' ∈ exactFamily Ω c ↔ ∃ K ∈ tqMembers Ω c, K' = exactCore c K := Iff.rfl

theorem exactCore_mem_exactFamily (hK : K ∈ tqMembers Ω c) : exactCore c K ∈ exactFamily Ω c :=
  ⟨K, hK, rfl⟩

theorem le_centralizer_of_mem_exactFamily (hK' : K' ∈ exactFamily Ω c) :
    K' ≤ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨K, -, rfl⟩ := hK'
  exact exactCore_le_centralizer c K

theorem mem_tqMembers_of_le_trivialOnQuot {B : Subgroup G} (hcB : c ∈ B)
    (hB : B ≤ trivialOnQuot K) (hK : K ∈ Ω) : K ∈ tqMembers Ω c :=
  ⟨hK, hB hcB⟩

theorem mem_tqMembers_of_isClassicalMember {M : Subgroup G} (hM : M ∈ Ω)
    (hMc : IsClassicalMember p f M c) : M ∈ tqMembers Ω c :=
  ⟨hM, mem_trivialOnQuot_of_le_centralizer (isSubnormal_le hMc.subnormal)⟩

theorem mem_exactFamily_of_isClassicalMember {M : Subgroup G} (hM : M ∈ Ω)
    (hMc : IsClassicalMember p f M c) : M ∈ exactFamily Ω c :=
  ⟨M, mem_tqMembers_of_isClassicalMember hM hMc,
    (exactCore_eq_self hMc.perfect (isSubnormal_le hMc.subnormal)).symm⟩

theorem conjSub_mem_tqMembers (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) (hK : K ∈ tqMembers Ω c) :
    conjSub n K ∈ tqMembers Ω c := by
  refine ⟨hΩ n K hK.1, ?_⟩
  have h := trivialOnQuot_conjSub hK.2 n
  rwa [conj_eq_of_mem_centralizer_singleton hn] at h

theorem conjSub_mem_exactFamily (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({c} : Set G)) (hK' : K' ∈ exactFamily Ω c) :
    conjSub n K' ∈ exactFamily Ω c := by
  obtain ⟨K, hK, rfl⟩ := hK'
  exact ⟨conjSub n K, conjSub_mem_tqMembers hΩ hn hK, (triangleResidual_conjSub K hn).symm⟩

theorem secData_exactFamily (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers Ω c).Nonempty) : SecData p f c (exactFamily Ω c) := by
  refine ⟨?_, fun K' hK' => le_centralizer_of_mem_exactFamily hK', fun n hn K' hK' =>
    conjSub_mem_exactFamily hΩ hn hK', ?_⟩
  · obtain ⟨K, hK⟩ := hne
    exact ⟨exactCore c K, exactCore_mem_exactFamily hK⟩
  · rintro K' ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := hcls K hK.1
    exact ⟨z, isSectionMember_exactCore hz hc2 hK.2⟩

theorem secData_exactFamily_of_inClass (hΩ : InClass p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers Ω c).Nonempty) : SecData p f c (exactFamily Ω c) :=
  secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 hne

theorem exactFamily_eq_linkFamily (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) :
    exactFamily Ω c = linkFamily p f Ω c := by
  have h : tqMembers Ω c = Ω ∩ linkMembers p f c := by
    ext K
    exact ⟨fun hK => ⟨hK.1, hcls K hK.1, hK.2⟩, fun hK => ⟨hK.1, hK.2.2⟩⟩
  unfold exactFamily linkFamily
  rw [h]

end Family

end CFSG.ClassicalInvolution.Asc77.ExactLayer
