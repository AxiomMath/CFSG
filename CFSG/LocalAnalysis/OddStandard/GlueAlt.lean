module

public import CFSG.Foundations.Basic
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.OddStandard.GlueAlt

open Subgroup

theorem isStandardSubgroup_of_standardComponentIsStandard {G : Type*} [Group G]
    {L : Subgroup G} (h : CFSG.Open.standardComponentIsStandard L) :
    CFSG.IsStandardSubgroup L :=
  CFSG.isStandardSubgroup_iff_standardComponentIsStandard.2 h

theorem card_ker_le_two_of_alt {P : Type*} [Group P] [Finite P] [Group.IsPerfect P] {n : ℕ}
    (hn : 8 ≤ n) (η : P →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) : Nat.card η.ker ≤ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 η.ker) := inferInstance
  set S' : Subgroup P := (S : Subgroup η.ker).map η.ker.subtype with hS'
  have hS'K : S' ≤ η.ker := Subgroup.map_subtype_le _
  have hSn : S'.Normal := Subgroup.normal_of_le_center (hS'K.trans hK)
  let η' : P ⧸ S' →* alternatingGroup (Fin (m + 2)) := QuotientGroup.lift S' η hS'K
  have hη'mk : ∀ p : P, η' (QuotientGroup.mk p) = η p := fun p => QuotientGroup.lift_mk S' hS'K p
  have hη' : Function.Surjective η' := by
    intro a
    obtain ⟨p, rfl⟩ := hη a
    exact ⟨QuotientGroup.mk p, hη'mk p⟩
  have hker' : ∀ x ∈ η'.ker, ∃ p ∈ η.ker, QuotientGroup.mk p = x := by
    intro x hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨p, by rwa [MonoidHom.mem_ker, ← hη'mk], rfl⟩
  have hK' : η'.ker ≤ center (P ⧸ S') := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hker' x hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hK hp) q]
  let φ : η.ker →* P ⧸ S' := (QuotientGroup.mk' S').comp η.ker.subtype
  have hmem : ∀ k : η.ker, (k : P) ∈ S' ↔ k ∈ (S : Subgroup η.ker) := fun k =>
    Subgroup.mem_map_iff_mem η.ker.subtype_injective
  have hφker : φ.ker = (S : Subgroup η.ker) := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hmem]
  have hφrange : φ.range = η'.ker := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      rw [MonoidHom.mem_ker]
      change η' (QuotientGroup.mk (k : P)) = 1
      rw [hη'mk]
      exact k.2
    · intro hx
      obtain ⟨p, hp, rfl⟩ := hker' x hx
      exact ⟨⟨p, hp⟩, rfl⟩
  have hodd : Odd (Nat.card η'.ker) := by
    have hcard : Nat.card η'.ker = (S : Subgroup η.ker).index := by
      rw [← hφrange, ← hφker, Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
    rw [hcard]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (S.not_dvd_index))
  have h1 : Nat.card η'.ker = 1 :=
    Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η' hη' hK' hodd
  have hKS : ∀ k : η.ker, k ∈ S := by
    intro k
    have hk : (QuotientGroup.mk (k : P) : P ⧸ S') ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'mk]
      exact k.2
    have hbot : η'.ker = ⊥ := Subgroup.card_eq_one.1 h1
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hk
    exact (hmem k).1 hk
  have h2 : IsPGroup 2 η.ker := by
    intro k
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨k, hKS k⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  exact LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
    (by omega) η hη hK h2

theorem card_center_le_two_of_alt {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {n : ℕ}
    (hn : 8 ≤ n) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    Nat.card (center L) ≤ 2 := by
  let η : L →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have := card_ker_le_two_of_alt hn η hη hker.le
  rwa [hker] at this

theorem pPrimeCore_eq_bot_of_card_center_two {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hZ : Nat.card (center L) = 2) : CFSG.pPrimeCore 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := L)
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (CFSG.pPrimeCore_normal (p := 2) (G := L)) with htop | hle
  · exfalso
    rw [htop, Subgroup.card_top] at hc
    have h2 : 2 ∣ Nat.card L := by
      have := Subgroup.card_subgroup_dvd_card (center L)
      rwa [hZ] at this
    exact absurd (Nat.Coprime.eq_one_of_dvd hc h2) (by norm_num)
  · have hd : Nat.card (CFSG.pPrimeCore 2 L) ∣ 2 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hZ] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact Subgroup.card_eq_one.1 h
    · rw [h] at hc
      exact absurd hc (by norm_num)

theorem coreQuotient_of_pPrimeCore_eq_bot {L : Type*} [Group L] [Group.IsPerfect L] {A : Type*}
    [Group A] (hP : CFSG.pPrimeCore 2 L = ⊥) (e : L ⧸ center L ≃* A) :
    Group.IsPerfect (L ⧸ CFSG.pPrimeCore 2 L) ∧
      Nat.card (center (L ⧸ CFSG.pPrimeCore 2 L)) = Nat.card (center L) ∧
      Nonempty ((L ⧸ CFSG.pPrimeCore 2 L) ⧸ center (L ⧸ CFSG.pPrimeCore 2 L) ≃* A) := by
  let ψ : L ≃* L ⧸ CFSG.pPrimeCore 2 L :=
    MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.pPrimeCore 2 L))
      ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hP),
        QuotientGroup.mk'_surjective _⟩
  refine ⟨inferInstance, (Nat.card_congr (Subgroup.centerCongr ψ).toEquiv).symm, ⟨?_⟩⟩
  exact (QuotientGroup.congr (center L) (center (L ⧸ CFSG.pPrimeCore 2 L)) ψ
    (Subgroup.map_center_eq ψ)).symm.trans e

theorem isPComponent_two_centralizer_of_standard {G : Type*} [Group G] [Finite G]
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (heven : 2 ∣ Nat.card L)
    {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    L ≤ centralizer ({t} : Set G) ∧
      CFSG.IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))) := by
  obtain ⟨-, hLT, -, hcomp, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL ht ht2
  refine ⟨hLT, ?_⟩
  have hK := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLT).1 hcomp
  refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hK fun hle => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : Nat.card (L.subgroupOf (centralizer ({t} : Set G))) ∣
      Nat.card (CFSG.pPrimeCore 2 (centralizer ({t} : Set G))) := Subgroup.card_dvd_of_le hle
  have hcard : Nat.card (L.subgroupOf (centralizer ({t} : Set G))) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLT).toEquiv
  rw [hcard] at hd
  have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := centralizer ({t} : Set G))
  exact absurd (Nat.Coprime.eq_one_of_dvd hc (heven.trans hd)) (by norm_num)

end CFSG.OddStandard.GlueAlt
