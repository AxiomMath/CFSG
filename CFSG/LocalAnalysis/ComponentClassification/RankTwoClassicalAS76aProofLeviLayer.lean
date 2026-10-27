module

public import CFSG.RankThree.PartOne.KF.LayerGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Commute

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] {θ : ↥A →* P}
  (hker : θ.ker = center ↥A) (hZ : Odd (Nat.card (center ↥A)))
include hker hZ

theorem commute_of_theta_commute {x y : G} (hx : x ∈ A) (hy : y ∈ A) {j : ℕ}
    (hyj : y ^ 2 ^ j = 1) (h : θ ⟨x, hx⟩ * θ ⟨y, hy⟩ = θ ⟨y, hy⟩ * θ ⟨x, hx⟩) :
    x * y = y * x := by
  set z : ↥A := ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥A)⁻¹ * (⟨y, hy⟩ : ↥A)⁻¹ with hz
  have hzZ : z ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hzy : (⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥A)⁻¹ = z * ⟨y, hy⟩ := by rw [hz]; group
  have hyj' : (⟨y, hy⟩ : ↥A) ^ 2 ^ j = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyj)
  have hzj : z ^ 2 ^ j = 1 := by
    have h1 : ((⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥A)⁻¹) ^ 2 ^ j = 1 := by
      rw [conj_pow, hyj', mul_one, mul_inv_cancel]
    rw [hzy, (show Commute z ⟨y, hy⟩ from mem_center_iff.mp hzZ _ |>.symm).mul_pow, hyj',
      mul_one] at h1
    exact h1
  have hodd : Odd (orderOf z) := by
    have h := orderOf_dvd_natCard (⟨z, hzZ⟩ : center ↥A)
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hZ h
  have hz1 : z = 1 := eq_one_of_odd_of_pow hodd hzj
  have h2 : (⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    have := hzy
    rw [hz1, one_mul] at this
    calc (⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ = (⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥A)⁻¹) * ⟨x, hx⟩ := by group
      _ = ⟨y, hy⟩ * ⟨x, hx⟩ := by rw [this]
  exact congrArg Subtype.val h2

end Commute

section LayerGen

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] {θ : ↥A →* P}
  (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
include hker hθ

theorem layerCentralizer_eq_levLift {S : Subgroup P} (hperf : ⁅S, S⁆ = S)
    (hS : CFSG.IsQuasisimple ↥S) {Y : Subgroup G}
    (hLY : levLift θ S ≤ A ⊓ centralizer (Y : Set G))
    (hnorm : ∀ m ∈ A ⊓ centralizer (Y : Set G), ∀ hm : m ∈ A,
      θ ⟨m, hm⟩ ∈ normalizer (S : Set P))
    (hcomm : ∀ a ∈ A ⊓ centralizer (Y : Set G), ∀ b ∈ A ⊓ centralizer (Y : Set G),
      ∀ (ha : a ∈ A) (hb : b ∈ A), ⁅θ ⟨a, ha⟩, θ ⟨b, hb⟩⁆ ∈ S) :
    AS76b.layerCentralizer A Y = levLift θ S := by
  set M := A ⊓ centralizer (Y : Set G) with hM
  have hLM : levLift θ S ≤ M := hLY
  set L' : Subgroup ↥M := (levLift θ S).subgroupOf M with hL'
  have hnorm' : L'.Normal := by
    refine ⟨fun l hl g => ?_⟩
    rw [hL', mem_subgroupOf] at hl ⊢
    have hgA := (mem_inf.mp g.2).1
    have hN := mem_normalizer_levLift (θ := θ) (S := S) hgA (hnorm g g.2 hgA)
    exact (mem_normalizer_iff.mp hN l).mp hl
  have hq : CFSG.IsQuasisimple ↥L' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLM).symm
      (isQuasisimple_levLift hker hθ hperf hS)
  have hcen : ∀ a b : ↥M, (QuotientGroup.mk ⁅a, b⁆ : ↥M ⧸ L') ∈ center (↥M ⧸ L') := by
    intro a b
    have haA := (mem_inf.mp a.2).1
    have hbA := (mem_inf.mp b.2).1
    have hmem : ((⁅a, b⁆ : ↥M) : G) ∈ liftSub θ S := by
      refine mem_liftSub.mpr ⟨(mem_inf.mp (⁅a, b⁆ : ↥M).2).1, ?_⟩
      have h1 : (⟨((⁅a, b⁆ : ↥M) : G), (mem_inf.mp (⁅a, b⁆ : ↥M).2).1⟩ : ↥A) =
          ⁅(⟨a, haA⟩ : ↥A), ⟨b, hbA⟩⁆ := rfl
      rw [h1, map_commutatorElement]
      exact hcomm a a.2 b b.2 haA hbA
    obtain ⟨l, hl, hzA, hz⟩ := exists_mem_levLift_inv_mul_mem hker hθ hperf hmem
    have hzM : l⁻¹ * ((⁅a, b⁆ : ↥M) : G) ∈ M := mul_mem (inv_mem (hLM hl)) (⁅a, b⁆ : ↥M).2
    have hab : (⁅a, b⁆ : ↥M) = ⟨l, hLM hl⟩ * ⟨_, hzM⟩ := Subtype.ext (by
      change ((⁅a, b⁆ : ↥M) : G) = l * (l⁻¹ * ((⁅a, b⁆ : ↥M) : G))
      group)
    have hl1 : (QuotientGroup.mk (⟨l, hLM hl⟩ : ↥M) : ↥M ⧸ L') = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by rw [hL', mem_subgroupOf]; exact hl)
    rw [hab, QuotientGroup.mk_mul, hl1, one_mul, mem_center_iff]
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have h5 := congrArg (Subtype.val : ↥A → G) (mem_center_iff.mp hz ⟨m, (mem_inf.mp m.2).1⟩)
    exact Subtype.ext h5
  have hsolv : Group.IsSolvable (↥M ⧸ L') := by
    have hle : commutator (↥M ⧸ L') ≤ center (↥M ⧸ L') := by
      rw [commutator_def, commutator_le]
      intro a _ b _
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      have h := hcen a b
      rwa [← QuotientGroup.mk'_apply, map_commutatorElement] at h
    rw [Group.isSolvable_def]
    refine ⟨2, ?_⟩
    rw [derivedSeries_succ, derivedSeries_one, eq_bot_iff]
    refine (commutator_mono hle hle).trans ?_
    rw [(commutator_eq_bot_iff_le_centralizer).mpr (center_le_centralizer _)]
  have hlayer := CFSG.RankThree.PartOne.KFU.layer_eq_of_normal hnorm' hq hsolv
  rw [AS76b.layerCentralizer, hlayer, hL', subgroupOf_map_subtype, inf_of_le_left hLM]

end LayerGen

section Layer

variable {K : Type} [Field K] [CharP K 2] {k : ℕ}
variable {G : Type} [Group G] {A : Subgroup G} {θ : ↥A →* projectiveSL (2 + k) K}

variable (θ) in
@[expose] noncomputable def leviW : Subgroup G := levLift θ (barW K k)

variable (θ) in
@[expose] noncomputable def leviL : Subgroup G := levLift θ (barL K k)

variable (hker : θ.ker = center ↥A)
include hker

omit [CharP K 2] in
theorem liftSub_le_centralizer_leviL {S : Subgroup (projectiveSL (2 + k) K)}
    (hS : ∀ s ∈ S, ∀ l ∈ barL K k, s * l = l * s) :
    liftSub θ S ≤ centralizer (leviL θ : Set G) := by
  intro x hx
  obtain ⟨hxA, hxS⟩ := mem_liftSub.mp hx
  have hle := levLift_le_centralizer hker hxA (S := barL K k) fun l hl => hS _ hxS l hl
  rw [mem_centralizer_iff]
  intro l hl
  exact mem_centralizer_singleton_iff.mp (hle hl)

omit [CharP K 2] in
theorem leviW_le_centralizer_leviL : leviW θ ≤ centralizer (leviL θ : Set G) :=
  levLift_le_liftSub.trans (liftSub_le_centralizer_leviL hker fun _ hs _ hl =>
    barW_commute_barL hs hl)

variable (hθ : Function.Surjective θ) (h4 : ∃ s : Finset K, s.card = 4) (hk : 2 ≤ k)
include hθ h4 hk

theorem layerCentralizer_eq_leviL {Y : Subgroup G} (hWY : leviW θ ≤ Y)
    (hLY : leviL θ ≤ A ⊓ centralizer (Y : Set G)) :
    AS76b.layerCentralizer A Y = leviL θ := by
  have hcommW : ∀ m ∈ A ⊓ centralizer (Y : Set G), ∀ hm : m ∈ A, ∀ w ∈ barW K k,
      θ ⟨m, hm⟩ * w = w * θ ⟨m, hm⟩ := by
    intro m hmM hm w hw
    obtain ⟨w', hw', rfl⟩ := exists_mem_levLift hθ (commutator_barW h4) hw
    have hc : m * w' = w' * m :=
      (mem_centralizer_iff.mp (mem_inf.mp hmM).2 w' (hWY hw')).symm
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hc)
  exact layerCentralizer_eq_levLift hker hθ (commutator_barL hk h4) (isQuasisimple_barL hk h4) hLY
    (fun m hmM hm => mem_normalizer_barL (hcommW m hmM hm))
    (fun a ha b hb haA hbA => commutatorElement_mem_barL (hcommW a ha haA) (hcommW b hb hbA))

end Layer

end CFSG.ComponentClassification.RankTwoClassical
