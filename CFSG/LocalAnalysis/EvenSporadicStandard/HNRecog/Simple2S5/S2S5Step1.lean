module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

theorem step1 {G : Type*} [Group G] [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Q.relIndex P = 2) {a : G} (haQ : a ∈ Q) (ha2 : orderOf a = 2)
    (hac : ∀ g ∈ P, a * g = g * a) {S : Subgroup G} (hSP : S ≤ P) [IsSimpleGroup ↥S]
    (hS : 2 < Nat.card ↥S) :
    S ≤ Q ∧ S ⊓ Subgroup.zpowers a = ⊥ ∧ 2 * Nat.card ↥S ∣ Nat.card ↥Q := by
  have hQnorm : (Q.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hQ
  have hconjP : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q := by
    intro p hp q hq
    have hm : (⟨q, hQP hq⟩ : ↥P) ∈ Q.subgroupOf P := hq
    have h := hQnorm.conj_mem (⟨q, hQP hq⟩ : ↥P) hm (⟨p, hp⟩ : ↥P)
    simpa [Subgroup.mem_subgroupOf] using h
  have hSQ : S ≤ Q := by
    let K : Subgroup ↥S := Q.subgroupOf S
    have hKnormal : K.Normal := by
      refine ⟨fun k hk g => ?_⟩
      have hkQ : (k : G) ∈ Q := hk
      have hgP : (g : G) ∈ P := hSP g.2
      have h := hconjP (g : G) hgP (k : G) hkQ
      show (g * k * g⁻¹ : ↥S) ∈ K
      rw [Subgroup.mem_subgroupOf]
      simpa using h
    haveI : K.Normal := hKnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hKbot | hKtop
    · exfalso
      have hKcard : Nat.card K = 1 := Subgroup.card_eq_one.mpr hKbot
      have hSindex : Nat.card ↥S = K.index := by
        have h := K.index_mul_card
        rw [hKcard, mul_one] at h
        exact h.symm
      have hle : K.index ≤ 2 := by
        have hne : Q.relIndex P ≠ 0 := by rw [hQ]; decide
        have h := Subgroup.relIndex_le_of_le_right (H := Q) hSP hne
        rw [hQ] at h
        exact h
      rw [hSindex] at hS
      omega
    · exact Subgroup.subgroupOf_eq_top.mp hKtop
  have hdisj : S ⊓ Subgroup.zpowers a = ⊥ := by
    let L : Subgroup ↥S := (Subgroup.zpowers a).subgroupOf S
    have hLnormal : L.Normal := by
      refine ⟨fun k hk g => ?_⟩
      have hkA : (k : G) ∈ Subgroup.zpowers a := hk
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkA
      have hgP : (g : G) ∈ P := hSP g.2
      have hc : Commute (g : G) (k : G) := by
        rw [← hn]
        have hcag : Commute a (g : G) := hac (g : G) hgP
        exact hcag.symm.zpow_right n
      have hconj : (g : G) * (k : G) * (g : G)⁻¹ = (k : G) := by
        rw [hc.eq]
        simp [mul_assoc]
      show (g * k * g⁻¹ : ↥S) ∈ L
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((g * k * g⁻¹ : ↥S) : G) = (g : G) * (k : G) * (g : G)⁻¹ := rfl
      rw [hcoe, hconj]
      exact hkA
    haveI : L.Normal := hLnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hLbot | hLtop
    · have hd : Disjoint (Subgroup.zpowers a) S := Subgroup.subgroupOf_eq_bot.mp hLbot
      exact disjoint_iff.mp (disjoint_comm.mp hd)
    · exfalso
      have hleA : S ≤ Subgroup.zpowers a := Subgroup.subgroupOf_eq_top.mp hLtop
      have hcardle : Nat.card ↥S ≤ Nat.card ↥(Subgroup.zpowers a) :=
        Subgroup.card_le_of_le hleA
      rw [Nat.card_zpowers, ha2] at hcardle
      omega
  have hAQ : Subgroup.zpowers a ≤ Q := Subgroup.zpowers_le_of_mem haQ
  let fS : ↥S →* ↥Q := Subgroup.inclusion hSQ
  let fA : ↥(Subgroup.zpowers a) →* ↥Q := Subgroup.inclusion hAQ
  have hcomm : ∀ (x : ↥S) (y : ↥(Subgroup.zpowers a)), Commute (fS x) (fA y) := by
    intro x y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    have hxP : (x : G) ∈ P := hSP x.2
    have hc : Commute (x : G) (y : G) := by
      rw [← hk]
      have hcax : Commute a (x : G) := hac (x : G) hxP
      exact hcax.symm.zpow_right k
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact hc.eq
  let F : ↥S × ↥(Subgroup.zpowers a) →* ↥Q := fS.noncommCoprod fA hcomm
  have hFinj : Function.Injective F := by
    intro p q hpq
    have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := by
      have h := congrArg (fun z : ↥Q => (z : G)) hpq
      simpa [F, fS, fA, MonoidHom.noncommCoprod_apply, Subgroup.coe_inclusion] using h
    have hkey : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc (q.1 : G)⁻¹ * (p.1 : G)
          = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by
            simp [mul_assoc]
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hval]
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by simp [mul_assoc]
    have hmemS : (q.1 : G)⁻¹ * (p.1 : G) ∈ S :=
      S.mul_mem (S.inv_mem q.1.2) p.1.2
    have hmemA : (q.1 : G)⁻¹ * (p.1 : G) ∈ Subgroup.zpowers a := by
      rw [hkey]
      exact (Subgroup.zpowers a).mul_mem q.2.2 ((Subgroup.zpowers a).inv_mem p.2.2)
    have hone : (q.1 : G)⁻¹ * (p.1 : G) = 1 := by
      have hmem : (q.1 : G)⁻¹ * (p.1 : G) ∈ S ⊓ Subgroup.zpowers a := ⟨hmemS, hmemA⟩
      rw [hdisj] at hmem
      simpa using hmem
    have hp1 : (p.1 : ↥S) = q.1 := by
      apply Subtype.ext
      have h := congrArg (fun z : G => (q.1 : G) * z) hone
      simpa [mul_assoc] using h
    have hp2 : (p.2 : ↥(Subgroup.zpowers a)) = q.2 := by
      apply Subtype.ext
      have hval' := hval
      rw [show (p.1 : G) = (q.1 : G) from congrArg Subtype.val hp1] at hval'
      exact mul_left_cancel hval'
    exact Prod.ext hp1 hp2
  have hcarddvd : Nat.card (↥S × ↥(Subgroup.zpowers a)) ∣ Nat.card ↥Q :=
    Subgroup.card_dvd_of_injective F hFinj
  rw [Nat.card_prod, Nat.card_zpowers, ha2] at hcarddvd
  exact ⟨hSQ, hdisj, by simpa [mul_comm] using hcarddvd⟩

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
