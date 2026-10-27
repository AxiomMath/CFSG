module

public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Th2.P85.Sp

open Subgroup CFSG CFSG.ABGLocalTools

theorem false_of_seven {X : Type} [Group X] [Finite X] {N H : Subgroup X}
    (hHN : H ≤ N) (hcard : Nat.card ↥N = 2 * Nat.card ↥H) {y : X}
    (hZ : Nat.card ↥(centralizer ({y} : Set X) ⊓ N) = 672)
    (h7 : ∀ t ∈ H, orderOf t = 2 → ¬ 7 ∣ Nat.card ↥(centralizer ({t} : Set X) ⊓ N))
    {R : Subgroup X} (hRZ : R ≤ centralizer ({y} : Set X) ⊓ N)
    (hRn : ∀ z ∈ centralizer ({y} : Set X) ⊓ N, ∀ r ∈ R, z * r * z⁻¹ ∈ R)
    (hRodd : Odd (Nat.card ↥R)) (hR7 : 7 ∣ Nat.card ↥R) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup X := centralizer ({y} : Set X) ⊓ N with hZdef
  have hRN : R ≤ N := hRZ.trans inf_le_right
  have hRle : Nat.card ↥R ≤ 21 := by
    have h1 : Nat.card ↥R ∣ 32 * 21 := by
      have := Subgroup.card_dvd_of_le hRZ
      rw [hZ] at this
      simpa using this
    have hcop : Nat.Coprime (Nat.card ↥R) 32 := by
      have h2 : Nat.Coprime (Nat.card ↥R) 2 := (Nat.coprime_two_left.2 hRodd).symm
      simpa using Nat.Coprime.pow_right 5 h2
    exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_left h1)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 7 hR7
  set ζ' : X := (ζ : X) with hζ'
  have hζ7 : orderOf ζ' = 7 := (Subgroup.orderOf_coe ζ).trans hζ
  have hζR : ζ' ∈ R := ζ.2
  set A : Subgroup X := zpowers ζ' with hA
  have hAcard : Nat.card ↥A = 7 := by rw [hA, Nat.card_zpowers, hζ7]
  have hAR : A ≤ R := (Subgroup.zpowers_le).2 hζR
  have hclaim : ∀ r ∈ R, orderOf r = 7 → r ∈ A := by
    intro r hr hr7
    by_contra hnot
    have hBcard : Nat.card ↥(zpowers r) = 7 := by rw [Nat.card_zpowers, hr7]
    have hBR : zpowers r ≤ R := (Subgroup.zpowers_le).2 hr
    have hinf : A ⊓ zpowers r = ⊥ := by
      by_contra hne
      have hdvd : Nat.card ↥(A ⊓ zpowers r) ∣ 7 := hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h1 | h1
      · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
      · have h2 : A ⊓ zpowers r = A :=
          Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ zpowers r ≤ A) (by rw [h1, hAcard])
        have hAB : A ≤ zpowers r := by
          rw [← h2]
          exact inf_le_right
        have h3 : A = zpowers r := Subgroup.eq_of_le_of_card_ge hAB (by rw [hAcard, hBcard])
        exact hnot (h3 ▸ Subgroup.mem_zpowers r)
    have hinj : Function.Injective (fun p : ↥A × ↥(zpowers r) =>
        (⟨(p.1 : X) * p.2, R.mul_mem (hAR p.1.2) (hBR p.2.2)⟩ : ↥R)) := by
      intro p q h
      have h1 : (p.1 : X) * p.2 = q.1 * q.2 := congrArg Subtype.val h
      have h2 : (q.1 : X)⁻¹ * p.1 = q.2 * (p.2 : X)⁻¹ := by
        calc (q.1 : X)⁻¹ * p.1 = (q.1 : X)⁻¹ * (p.1 * p.2) * (p.2 : X)⁻¹ := by group
          _ = (q.1 : X)⁻¹ * (q.1 * q.2) * (p.2 : X)⁻¹ := by rw [h1]
          _ = q.2 * (p.2 : X)⁻¹ := by group
      have hmem : (q.1 : X)⁻¹ * p.1 ∈ A ⊓ zpowers r :=
        ⟨A.mul_mem (A.inv_mem q.1.2) p.1.2, h2 ▸ (zpowers r).mul_mem q.2.2 ((zpowers r).inv_mem p.2.2)⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hp1 : p.1 = q.1 := Subtype.ext (inv_mul_eq_one.1 hmem).symm
      have hp2 : p.2 = q.2 := by
        have : (p.2 : X) = q.2 := by
          have h3 : (p.1 : X) * p.2 = p.1 * q.2 := by rw [h1, ← hp1]
          exact mul_left_cancel h3
        exact Subtype.ext this
      exact Prod.ext hp1 hp2
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hAcard, hBcard] at hle
    omega
  have hZA : ∀ z ∈ Z, ∀ h ∈ A, z * h * z⁻¹ ∈ A := by
    intro z hz h hh
    have hz' : z * ζ' * z⁻¹ ∈ A := by
      refine hclaim _ (hRn z hz ζ' hζR) ?_
      have := MulEquiv.orderOf_eq (MulAut.conj z) ζ'
      simpa [MulAut.conj_apply] using this.trans hζ7
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hconj : z * ζ' ^ k * z⁻¹ = (z * ζ' * z⁻¹) ^ k := by
      simp
    rw [hconj]
    exact A.zpow_mem hz' k
  have hZnorm : Z ≤ normalizer (A : Set X) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hZA z hz h hh, fun hh => ?_⟩
    have := hZA z⁻¹ (Z.inv_mem hz) _ hh
    simpa [mul_assoc] using this
  have hA6 : Nat.card (MulAut ↥A) = 6 := by
    have : IsCyclic ↥A := Subgroup.isCyclic_zpowers ζ'
    rw [IsCyclic.card_mulAut, hAcard]
    simp [Nat.totient_prime (by norm_num : Nat.Prime 7)]
  have hd1 : (centralizer (A : Set X)).relIndex (normalizer (A : Set X)) ∣ 6 := by
    have key := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective A.normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex, hA6] at key
    exact key
  have hd1ne : (centralizer (A : Set X)).relIndex (normalizer (A : Set X)) ≠ 0 := fun h0 => by
    rw [h0] at hd1
    exact absurd (Nat.eq_zero_of_zero_dvd hd1) (by norm_num)
  have hd2 : (centralizer (A : Set X)).relIndex Z ≤ 6 :=
    (Subgroup.relIndex_le_of_le_right hZnorm hd1ne).trans (Nat.le_of_dvd (by norm_num) hd1)
  set C : Subgroup X := centralizer (A : Set X) ⊓ Z with hC
  have hmul : (centralizer (A : Set X)).relIndex Z * Nat.card ↥C = 672 := by
    rw [← hZ]
    exact Subgroup.relIndex_mul_card _ _
  have hC4 : 4 ∣ Nat.card ↥C := by
    generalize (centralizer (A : Set X)).relIndex Z = d at hd2 hmul
    generalize Nat.card ↥C = c at hmul ⊢
    interval_cases d <;> omega
  have hCN : C ≤ N := inf_le_right.trans inf_le_right
  have hrel : H.relIndex N = 2 := by
    have h1 := Subgroup.relIndex_mul_card H N
    rw [inf_eq_left.2 hHN, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥H)) h1
  have hCH : 2 ∣ Nat.card ↥(C ⊓ H) := by
    by_cases hall : C ≤ H
    · rw [inf_eq_left.2 hall]
      exact (by norm_num : 2 ∣ 4).trans hC4
    · obtain ⟨u, huC, huH⟩ := Set.not_subset.1 hall
      have hr := EvenSporTransfer.relIndex_inf_eq_two hCN hrel huC huH
      have h1 := Subgroup.relIndex_mul_card (C ⊓ H) C
      rw [hr, inf_eq_left.2 (inf_le_left : C ⊓ H ≤ C)] at h1
      have h2 : Nat.card ↥(C ⊓ H) * 2 = Nat.card ↥C := by rw [mul_comm]; exact h1
      omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ H)) 2 hCH
  have htH : (t : X) ∈ H := t.2.2
  have ht2 : orderOf (t : X) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htC : (t : X) ∈ centralizer (A : Set X) := t.2.1.1
  have hcomm : (t : X) * ζ' = ζ' * t := by
    have := Subgroup.mem_centralizer_iff.1 htC ζ' (Subgroup.mem_zpowers ζ')
    exact this.symm
  have hζC : ζ' ∈ centralizer ({(t : X)} : Set X) ⊓ N :=
    ⟨mem_centralizer_singleton_iff.2 hcomm.symm, hRN hζR⟩
  have hdvd := Subgroup.orderOf_dvd_natCard _ hζC
  rw [hζ7] at hdvd
  exact h7 _ htH ht2 hdvd

end CFSG.GH74.GLS.Th2.P85.Sp
