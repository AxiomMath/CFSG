module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseGroup

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

section CaseA

variable {X : Type} [Group X] [Finite X]

theorem false_of_case_a (d : ThreeLocalData X) (kd : KernelData d) (hM10 : Nat.card M10 = 720)
    {A B : Subgroup (X ⧸ CFSG.oddCore X)} (hAn : A.Normal) (hBn : B.Normal)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAp : ⁅A, A⁆ = A) (hA9 : 9 ∣ Nat.card A)
    (hB : Nat.card B = 360) (hAK : A ≤ kd.Kt) (hBK : B ⊓ kd.Kt = ⊥) : False := by
  set tt : X ⧸ CFSG.oddCore X := QuotientGroup.mk d.t with htt
  set ft : X ⧸ CFSG.oddCore X := QuotientGroup.mk d.f with hft
  have hπs := proj_surjective X
  have hBCt : B ≤ centralizer ({tt} : Set (X ⧸ CFSG.oddCore X)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ⁅b, tt⁆ ∈ B := by
      have h1 := hBn.conj_mem b⁻¹ (B.inv_mem hb) tt
      have h2 := B.mul_mem hb h1
      convert h2 using 1
      simp [commutatorElement_def, mul_assoc]
    have h3 : ⁅b, tt⁆ ∈ B ⊓ kd.Kt := ⟨h1, kd.commutator_mem b⟩
    rw [hBK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hftCt : ft ∈ centralizer ({tt} : Set (X ⧸ CFSG.oddCore X)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, htt, hft, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, d.tf_comm]
  have hftB : ft ∈ B := by
    set Ct := centralizer ({tt} : Set (X ⧸ CFSG.oddCore X)) with hCt
    have : (B.subgroupOf Ct).Normal := hBn.subgroupOf Ct
    have hcardCt : Nat.card Ct = 1440 := card_centralizer_mk_t d hM10
    have hcardB' : Nat.card (B.subgroupOf Ct) = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBCt).toEquiv, hB]
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf Ct)
    rw [hcardCt, hcardB'] at hq
    have hq4 : Nat.card (Ct ⧸ B.subgroupOf Ct) = 4 := by omega
    set z : Ct := ⟨ft, hftCt⟩ with hz
    have hf5 : d.f ^ 5 = 1 := by
      have := pow_orderOf_eq_one d.f
      rwa [d.f_ord] at this
    have hz5 : z ^ 5 = 1 := by
      apply Subtype.ext
      change ft ^ 5 = 1
      rw [hft, ← QuotientGroup.mk_pow, hf5, QuotientGroup.mk_one]
    have h4 : orderOf (QuotientGroup.mk z : Ct ⧸ B.subgroupOf Ct) ∣ 4 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk z : Ct ⧸ B.subgroupOf Ct)
      rwa [hq4] at this
    have h5 : orderOf (QuotientGroup.mk z : Ct ⧸ B.subgroupOf Ct) ∣ 5 :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hz5, QuotientGroup.mk_one])
    have h1 : orderOf (QuotientGroup.mk z : Ct ⧸ B.subgroupOf Ct) = 1 := by
      have := Nat.dvd_gcd h4 h5
      rw [show Nat.gcd 4 5 = 1 by norm_num] at this
      exact Nat.dvd_one.1 this
    have hz1 : (QuotientGroup.mk z : Ct ⧸ B.subgroupOf Ct) = 1 := orderOf_eq_one_iff.1 h1
    exact (QuotientGroup.eq_one_iff z).1 hz1
  have hπA : (A.comap (proj X)).map (proj X) = A :=
    Subgroup.map_comap_eq_self_of_surjective hπs A
  obtain ⟨Q, hQL, hQW, hQA, hQp⟩ := exists_perfect_core (W := ⊤) (L := A.comap (proj X))
    (proj X) (fun w _ l hl => by
      rw [Subgroup.mem_comap] at hl ⊢
      rw [map_mul, map_mul, map_inv]
      exact hAn.conj_mem _ hl _) (by rw [hπA]; exact hAp)
  have hLK : A.comap (proj X) ≤ kd.K := kd.comap_le hAK
  have hQcen : Q ≤ centralizer (CFSG.oddCore X : Set X) := by
    have h1 : ⁅Q, Q⁆ ≤ ⁅kd.K, kd.K⁆ :=
      Subgroup.commutator_mono (hQL.trans hLK) (hQL.trans hLK)
    rw [hQp] at h1
    exact h1.trans kd.comm_le
  have hcomm : ∀ q ∈ Q, Commute d.f q := by
    apply commute_of_perfect_of_central hQp (O := CFSG.oddCore X)
    · intro z _ hzO q hq
      exact (Subgroup.mem_centralizer_iff.1 (hQcen hq) z hzO)
    · intro q hq
      exact hQW d.f (Subgroup.mem_top _) q hq
    · intro q hq
      have hqA : proj X q ∈ A := hQL hq
      have e : proj X ⁅d.f, q⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (hAB _ hqA ft hftB).symm
      exact (QuotientGroup.eq_one_iff _).1 e
  have hQf : Q ≤ centralizer ({d.f} : Set X) := fun q hq => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm q hq).eq.symm
  have h9 : 9 ∣ Nat.card ↥(centralizer ({d.f} : Set X)) := by
    have h1 : Nat.card A ∣ Nat.card Q := by
      have := Subgroup.card_map_dvd (H := Q) (proj X)
      rwa [hQA, hπA] at this
    exact (hA9.trans h1).trans (Subgroup.card_dvd_of_le hQf)
  exact d.f_nine h9

end CaseA

end CFSG.EvenSporadicStandard.RuStd.S2.Close
