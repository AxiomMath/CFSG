module

public import CFSG.ClassicalInvolution.Q3.TL3S8Std
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDSetup

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

variable (hd : TightDatum R S t)
include hd

theorem mem_of_isSylow2Of_core {P : Subgroup G} (hP : IsSylow2Of P (tightCore R)) : t ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := hd.isUniqueInvolution_core
  have h2K : 2 ∣ Nat.card (tightCore R) := by
    have h := Subgroup.orderOf_dvd_natCard (tightCore R) hU.mem
    rwa [hd.order] at h
  have h2P : 2 ∣ Nat.card P := by
    rw [hP.card_eq]
    have hpos : 0 < (Nat.card (tightCore R)).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2K
    exact dvd_pow_self 2 hpos.ne'
  obtain ⟨⟨x, hxP⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2P
  have hx2' : orderOf x = 2 := by rw [← Subgroup.orderOf_mk x hxP]; exact hx2
  rw [← hd.eq_of_orderOf_eq_two (tightCore_le R (hP.1 hxP)) hx2']
  exact hxP

theorem nonempty_quat_sylow_core (Q : Sylow 2 (tightCore R)) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((Q : Subgroup (tightCore R)) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
  refine ⟨r, hr, ?_⟩
  obtain ⟨e2⟩ := (isSylow2Of_map_subtype Q).nonempty_mulEquiv hd.sylow_core
  exact ⟨(Subgroup.equivMapOfInjective (Q : Subgroup (tightCore R)) (tightCore R).subtype
    (tightCore R).subtype_injective).trans (e2.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        e))⟩

theorem mem_omegaNbr_of_commuting_sylow {g : G}
    (hg : g ∉ Subgroup.normalizer (tightCore R : Set G)) {P₁ P₂ : Subgroup G}
    (hP₁ : IsSylow2Of P₁ (tightCore R)) (hP₂ : IsSylow2Of P₂ (conjSubgroup g (tightCore R)))
    (hcomm : ∀ x ∈ P₁, ∀ y ∈ P₂, x * y = y * x) :
    conjSubgroup g (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  have hzP₁ := hd.mem_of_isSylow2Of_core hP₁
  obtain ⟨T, hT⟩ := hP₂.exists_sylow
  refine ⟨⟨g, rfl⟩, fun h => hg (conjSubgroup_eq_self_iff.mp h), P₂,
    ⟨conjSubgroup g (tightCore R), ⟨g, rfl⟩, T, hT.symm⟩, hP₂.1, ?_⟩
  intro y hy
  rw [hd.normalizer_core_eq, Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm t hzP₁ y hy).symm

theorem sylow_eq (he : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)))
    (Q : Sylow 2 (tightCore R)) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hQP : (Q : Subgroup (tightCore R)).map (tightCore R).subtype ≤ P) {g : G}
    (hgP : conjSubgroup g ((Q : Subgroup (tightCore R)).map (tightCore R).subtype) ≤ P) :
    conjSubgroup g ((Q : Subgroup (tightCore R)).map (tightCore R).subtype) =
      (Q : Subgroup (tightCore R)).map (tightCore R).subtype := by
  set Q' : Subgroup G := (Q : Subgroup (tightCore R)).map (tightCore R).subtype with hQ'
  have hzQ : t ∈ Q' := hd.mem_of_isSylow2Of_core (isSylow2Of_map_subtype Q)
  have hQq := hd.nonempty_quat_sylow_core Q
  by_contra hne
  have h1 : conjSubgroup 1 Q' ≤ P := by
    rw [conjSubgroup_one]
    exact hQP
  have hne' : conjSubgroup 1 Q' ≠ conjSubgroup g Q' := by
    rw [conjSubgroup_one]
    exact fun h => hne h.symm
  obtain ⟨hbot, hcomm⟩ := quaternion_conjugates_commute Q hQq hzQ hd.order
    hd.le_centralizer_core hd.normal_core hP hQP h1 hgP hne'
  rw [conjSubgroup_one] at hbot hcomm
  by_cases hg : g ∈ Subgroup.normalizer (tightCore R : Set G)
  · have hgz : g ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [← hd.normalizer_core_eq]
      exact hg
    have hz' : t ∈ conjSubgroup g Q' := by
      have h := mem_conjSubgroup_of_mem (g := g) hzQ
      rwa [show g * t * g⁻¹ = t by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hgz]; group] at h
    have hz1 : t ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_inf.mpr ⟨hzQ, hz'⟩
    rw [Subgroup.mem_bot] at hz1
    have h2 := hd.order
    rw [hz1, orderOf_one] at h2
    omega
  · exact absurd (Or.inl (hd.mem_omegaNbr_of_commuting_sylow hg (isSylow2Of_map_subtype Q)
      ((isSylow2Of_map_subtype Q).conj g) hcomm))
      (he (tightCore R) (CoreAssembly.mem_conjClass_self (tightCore R)) _ ⟨g, rfl⟩)

theorem setup194 (he : Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))) :
    Q3T6.SD.Setup194Three (tightCore R) t where
  uniqueInvolutionNormal :=
    ⟨hd.order, hd.isUniqueInvolution_core.mem,
      fun _ hu hu2 => hd.eq_of_orderOf_eq_two (tightCore_le R hu) hu2,
      hd.le_centralizer_core, hd.normal_core⟩
  nonabelian := hd.nonabelian
  normEq := hd.normalizer_core_eq
  quat := fun hR => Sec6Gen.isQuatSub_of_mem_RSet hd.hypOmegaGen hR
  sylow_eq := fun Q _ hP hQP _ hgP => hd.sylow_eq he Q hP hQP hgP

end TightDatum

namespace TightSylowStd

variable {T : Sylow 2 G} (h : TightSylowStd R S t T)
include h

theorem setup194 : Q3T6.SD.Setup194Three (tightCore R) t :=
  h.datum.setup194 h.edgeless

end TightSylowStd

end CFSG.ClassicalInvolution.Q3
