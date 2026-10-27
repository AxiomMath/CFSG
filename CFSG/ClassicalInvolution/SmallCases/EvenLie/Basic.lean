module

public import CFSG.ClassicalInvolution.SmallCases.Exclusion
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
public import CFSG.Foundations.Basic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
  (parabolic_containing_subgroup_local_characteristic_transfer)

theorem inf_centralizer_pCoreOf_le_of_isCharacteristicP {F : Type*} [Group F] {H : Subgroup F}
    (h : CFSG.IsCharacteristicP 2 H) :
    H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set F) ≤ pCoreOf 2 H := by
  rintro g ⟨hgH, hgC⟩
  have hmem : (⟨g, hgH⟩ : H) ∈ Subgroup.centralizer (CFSG.pCore 2 H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : F) ∈ pCoreOf 2 H := by
      refine ⟨y, ?_, rfl⟩
      assumption
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC _ hy')
  have hcore := h hmem
  exact ⟨_, hcore, rfl⟩

theorem NoNonsolvableClassicalAt.of_isCharacteristicP {F : Type*} [Group F] [Finite F] {z : F}
    (h : CFSG.IsCharacteristicP 2 (Subgroup.centralizer {z})) : NoNonsolvableClassicalAt z :=
  NoNonsolvableClassicalAt.of_twoConstrained (inf_centralizer_pCoreOf_le_of_isCharacteristicP h)

theorem NoNonsolvableClassical.of_isCharacteristicP {F : Type*} [Group F] [Finite F]
    (h : ∀ z : F, orderOf z = 2 → CFSG.IsCharacteristicP 2 (Subgroup.centralizer {z})) :
    NoNonsolvableClassical F :=
  fun z hz => NoNonsolvableClassicalAt.of_isCharacteristicP (h z hz) hz

theorem centralizer_zpowers_eq {F : Type*} [Group F] (z : F) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup F) : Set F) =
      Subgroup.centralizer ({z} : Set F) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hg
    exact hg z (Subgroup.mem_zpowers z)
  · intro hg y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_left (show Commute z g from hg) n

theorem isPGroup_zpowers_of_orderOf_eq_two {F : Type*} [Group F] {z : F} (hz : orderOf z = 2) :
    IsPGroup 2 (Subgroup.zpowers z) ∧ Subgroup.zpowers z ≠ ⊥ := by
  refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), ?_⟩
  intro h
  have hz1 : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rw [h, Subgroup.mem_bot] at hz1
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

@[expose] def HasParabolicOvergroup {F : Type*} [Group F] (z : F) : Prop :=
  ∃ P U : Subgroup F, Subgroup.centralizer {z} ≤ P ∧ U ≤ P ∧ (U.subgroupOf P).Normal ∧
    IsPGroup 2 U ∧ Subgroup.centralizer (U : Set F) ⊓ P ≤ U

theorem isCharacteristicP_centralizer_of_hasParabolicOvergroup {F : Type*} [Group F] [Finite F]
    {z : F} (hz : orderOf z = 2) (h : HasParabolicOvergroup z) :
    CFSG.IsCharacteristicP 2 (Subgroup.centralizer {z}) := by
  obtain ⟨P, U, hCP, hUP, hUn, hUp, hCU⟩ := h
  have hzp := (isPGroup_zpowers_of_orderOf_eq_two hz).1
  have heq := centralizer_zpowers_eq z
  have hzP : Subgroup.zpowers z ≤ P := by
    rw [Subgroup.zpowers_le]
    exact hCP (Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh])
  have := parabolic_containing_subgroup_local_characteristic_transfer
    (p := 2) (H := Subgroup.centralizer ({z} : Set F)) hUP hUn hUp hCU hzP hzp
    (Or.inr heq.symm) hCP
  exact this.2.1

theorem NoNonsolvableClassicalAt.of_hasParabolicOvergroup {F : Type*} [Group F] [Finite F] {z : F}
    (h : HasParabolicOvergroup z) : NoNonsolvableClassicalAt z :=
  fun hz => NoNonsolvableClassicalAt.of_isCharacteristicP
    (isCharacteristicP_centralizer_of_hasParabolicOvergroup hz h) hz

theorem isSolvable_sup_of_cyclic {G : Type*} [Group G] [Finite G] {Q D : Subgroup G}
    (hQ : IsPGroup 2 Q) (hD : IsCyclic D) (hsup : Q ⊔ D = Subgroup.normalizer (Q : Set G)) :
    Group.IsSolvable ↥(Q ⊔ D) := by
  set M : Subgroup G := Q ⊔ D with hM
  have hQM : Q ≤ M := le_sup_left
  have hDM : D ≤ M := le_sup_right
  have hnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).2 hsup.le
  have hQp : IsPGroup 2 (Q.subgroupOf M) := hQ.comap_of_injective M.subtype M.subtype_injective
  have : Group.IsSolvable ↥(Q.subgroupOf M) := by
    have := hQp.isNilpotent
    infer_instance
  have hcyc : IsCyclic (↥M ⧸ Q.subgroupOf M) := by
    let f : D →* ↥M ⧸ Q.subgroupOf M :=
      (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hDM)
    have hf : Function.Surjective f := by
      have htop : Q.subgroupOf M ⊔ D.subgroupOf M = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQM hDM, ← hM, Subgroup.subgroupOf_self]
      intro x
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
      have hm : m ∈ Q.subgroupOf M ⊔ D.subgroupOf M := by rw [htop]; exact Subgroup.mem_top m
      obtain ⟨y, hy, d, hd, hyd⟩ := Subgroup.mem_sup_of_normal_left.1 hm
      refine ⟨⟨(d : G), hd⟩, ?_⟩
      rw [← hyd]
      change QuotientGroup.mk (Subgroup.inclusion hDM ⟨(d : G), hd⟩) = QuotientGroup.mk (y * d)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul]
      rfl
    exact isCyclic_of_surjective f hf
  have : Group.IsSolvable (↥M ⧸ Q.subgroupOf M) := inferInstance
  exact Group.isSolvable_of_ker_le_range (Q.subgroupOf M).subtype
    (QuotientGroup.mk' (Q.subgroupOf M)) (by simp)

theorem isSolvable_centralizer_of_fusionBenderBorel {G : Type*} [Group G] [Finite G] {q k : ℕ}
    (h : fusionBenderBorel G q k) {z : G} (hz : orderOf z = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) := by
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz, pow_one]
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hzp
  have hzQ : z ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers z)
  obtain ⟨⟨-, -, hodd⟩, ⟨D, hDc, -, -, hsup⟩, -, -, -⟩ := h Q
  have hzM : z ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := Subgroup.le_normalizer hzQ
  have hCM : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro g hg
    by_contra hgM
    have h1 := hodd g hgM
    have hg' : z * g = g * z := Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)
    have hzi : z ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
        (Subgroup.normalizer ((Q : Subgroup G) : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
      refine ⟨hzM, z, hzM, ?_⟩
      change g⁻¹ * z * g⁻¹⁻¹ = z
      rw [inv_inv, mul_assoc, hg', ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 := Subgroup.orderOf_dvd_natCard _ hzi
    rw [hz] at h2
    exact (Nat.not_even_iff_odd.mpr h1) (even_iff_two_dvd.mpr h2)
  have hsolv : Group.IsSolvable ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [← hsup]
    exact isSolvable_sup_of_cyclic Q.isPGroup' hDc hsup
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCM)

theorem NoNonsolvableClassical.of_fusionBenderBorel {G : Type*} [Group G] [Finite G] {q k : ℕ}
    (h : fusionBenderBorel G q k) : NoNonsolvableClassical G :=
  fun _ hz => NoNonsolvableClassicalAt.of_isSolvable_centralizer
    (isSolvable_centralizer_of_fusionBenderBorel h hz) hz

theorem NoNonsolvableClassicalAt.of_normal_pGroup_le {F : Type*} [Group F] [Finite F] {z : F}
    {Q : Subgroup F} (hQC : Q ≤ Subgroup.centralizer {z}) (hQp : IsPGroup 2 Q)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({z} : Set F), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hcen : ∀ c ∈ Subgroup.centralizer ({z} : Set F), (∀ q ∈ Q, c * q = q * c) → c ∈ Q) :
    NoNonsolvableClassicalAt z := by
  refine NoNonsolvableClassicalAt.of_normal_pGroup_self_centralizing Q hQp hQC ?_ ?_
  · intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hnorm c hc q hq, fun hq => ?_⟩
    have h1 := hnorm c⁻¹ (inv_mem hc) _ hq
    have h2 : c⁻¹ * (c * q * c⁻¹) * c⁻¹⁻¹ = q := by group
    rwa [h2] at h1
  · rintro c ⟨hc, hcQ⟩
    exact hcen c hc fun q hq => (Subgroup.mem_centralizer_iff.mp hcQ q hq).symm

theorem NoNonsolvableClassicalAt.of_two_radical {F M : Type*} [Group F] [Finite F] [Group M]
    (φ : F →* M) (hφ : Function.Injective φ) {z : F} (R : Subgroup M)
    (hRX : R ≤ φ.range ⊓ Subgroup.centralizer ({φ z} : Set M))
    (hnorm : ∀ x ∈ φ.range ⊓ Subgroup.centralizer ({φ z} : Set M),
      x ∈ Subgroup.normalizer (R : Set M))
    (hR : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k = 1)
    (hcent : ∀ x ∈ φ.range ⊓ Subgroup.centralizer ({φ z} : Set M),
      x ∈ Subgroup.centralizer (R : Set M) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    NoNonsolvableClassicalAt z := by
  let U : Subgroup F := R.comap φ
  have hmem : ∀ u : F, u ∈ U ↔ φ u ∈ R := fun u => Iff.rfl
  have hUp : IsPGroup 2 U := by
    intro u
    obtain ⟨k, hk⟩ := hR (φ u) u.2
    refine ⟨k, Subtype.ext (hφ ?_)⟩
    change φ ((u : F) ^ 2 ^ k) = φ 1
    rw [map_pow, hk, map_one]
  have hφC : ∀ x : F, x ∈ Subgroup.centralizer ({z} : Set F) →
      φ x ∈ φ.range ⊓ Subgroup.centralizer ({φ z} : Set M) := by
    intro x hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    change φ x ∈ Subgroup.centralizer ({φ z} : Set M)
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul, hx z (Set.mem_singleton z)]
  have hUC : U ≤ Subgroup.centralizer {z} := by
    intro u hu
    have h := (Subgroup.mem_centralizer_iff.mp (hRX hu).2) (φ z) (Set.mem_singleton _)
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    subst hh'
    exact hφ (by rw [map_mul, map_mul]; exact h)
  have hUn : Subgroup.centralizer {z} ≤ Subgroup.normalizer (U : Set F) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hmem, hmem, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hnorm _ (hφC c hc)) (φ q)
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F)) := by
    have hp : IsPGroup 2 ↥(Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F)) := by
      intro x
      have hx := x.2
      have hxc : φ x ∈ Subgroup.centralizer (R : Set M) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        obtain ⟨u, hu⟩ := (hRX hr).1
        have hu' : u ∈ U := by rw [hmem, hu]; exact hr
        have := Subgroup.mem_centralizer_iff.mp hx.2 u hu'
        rw [← hu, ← map_mul, ← map_mul, this]
      obtain ⟨k, hk⟩ := hcent _ (hφC _ hx.1) hxc
      refine ⟨k, Subtype.ext (hφ ?_)⟩
      change φ ((x : F) ^ 2 ^ k) = φ 1
      rw [map_pow, map_one]
      exact hk
    have := hp.isNilpotent
    infer_instance
  exact NoNonsolvableClassicalAt.of_normal_pGroup_centralizer_solvable U hUp hUC hUn hsolv

end CFSG.ClassicalInvolution
