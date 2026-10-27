module

public import CFSG.ClassicalInvolution.Asc77.AscE186Basic
public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.AscThmAFitting
public import CFSG.ClassicalInvolution.Asc77.AscThmAFstar

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

theorem center_isPGroup_two [Finite G] (hO : classicalInvolutionOddCore G = ⊥) :
    IsPGroup 2 ↥(Subgroup.center G) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  have hxo : orderOf (x : G) ≠ 0 := orderOf_pos _ |>.ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hxo
  refine ⟨a, ?_⟩
  have hdvd : 2 ^ a ∣ orderOf (x : G) := ⟨m, by rw [hn]⟩
  set y : G := (x : G) ^ 2 ^ a with hy
  have hyo : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (by positivity) hdvd, hn]
    simp
  have hycent : y ∈ Subgroup.center G := Subgroup.pow_mem _ x.2 _
  have hnorm : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * y ^ k * g⁻¹ = y ^ k := by
      have hc : g * y = y * g := (Subgroup.mem_center_iff.mp hycent g)
      have : g * y ^ k = y ^ k * g := (Commute.zpow_right (show Commute g y from hc) k).eq
      rw [this]
      group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) _
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hyo]
    exact hm
  have hle : Subgroup.zpowers y ≤ classicalInvolutionOddCore G :=
    CFSG.ComponentClassification.OddCore.maximal G _ hnorm hodd
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hyo
  have h1 : m = 1 := hyo.symm
  rw [h1, mul_one] at hn
  rw [← Subgroup.orderOf_coe]
  exact hn

theorem e18_6 (p f : ℕ) [Fact p.Prime] (hq1 : E186QuotOdd p f) (hq2 : E186QuotCent p f)
    (h2 : Thm2 p f) : E18_6 p f := by
  intro G _ _ Ω K S R W H c
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have h67 : L6_7 p f := l6_7_proved p f
  have h69 : L6_9 p f := l6_9_proved p f
  have h611 : L6_11 p f := l6_11_proved p f
  have h3 : E18_3 p f := e18_3 p f h67
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := h3 G Ω K S R W H c
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := e18_5_of_layer p f h3 h69 h611 G Ω K S R W H c
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  have hA : EtaAbelian Ω := EtaAbelian.of_l6_9 h69 hp hq hΩ
  have hM : EtaMeet Ω := EtaMeet.of_l6_11 h611 hp hq hΩ
  have hOH : classicalInvolutionOddCore G ≤ H := by
    obtain ⟨U, hUR, -, hcomm, hsq, hU4, hC⟩ :=
      c.exists_fourGroup hA hM hK'tw hK'ne hR' hR'K' hR'S
    have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
    exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U)
      (N := classicalInvolutionOddCore G) (J := H) this
      (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
      (fun u _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top u)
      (CFSG.ComponentClassification.OddCore.odd_card G)
      (fun e he he1 => inf_le_right.trans (hC e he he1))
  have hO : classicalInvolutionOddCore G = ⊥ :=
    hq1 G Ω K S R W H c _ (CFSG.ComponentClassification.OddCore.odd_card G) hOH
  have hmiss : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → ∀ J ∈ Ω, J ⊓ Q = ⊥ := by
    intro Q hQn hQ2 J hJ
    have hzQ : z ∉ Q := by
      intro hzQ
      have hKn : K.Normal := h2 hp hq G Ω hΩ hO hgen K hK htrans z hz ⟨Q, hQn, hQ2, hzQ⟩
      apply hK'ne
      obtain ⟨g, hg⟩ := htrans K' hK'tw.1
      rw [← hg]
      exact AscThmA.conjSub_eq_of_normal K g
    obtain ⟨g, hg⟩ := htrans J hJ
    by_contra hne
    have hzJ : IsUniqueInvolution J (g * z * g⁻¹) := by
      rw [← hg]
      exact hz.conj g
    have hA2 : IsPGroup 2 ↥(J ⊓ Q) := hQ2.to_inf_right
    have hcard : 2 ≤ Nat.card ↥(J ⊓ Q) := by
      have := (Subgroup.one_lt_card_iff_ne_bot (J ⊓ Q)).mpr hne
      omega
    have hmem : g * z * g⁻¹ ∈ J ⊓ Q :=
      AscL62.mem_of_uniqueInvolution_of_pGroup hzJ inf_le_left hA2 hcard
    apply hzQ
    have := hQn.conj_mem _ hmem.2 g⁻¹
    simpa [mul_assoc] using this
  have hcent : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → Q ≤ Subgroup.center G := by
    intro Q hQn hQ2
    have hOQ : oddCoreOf Q = ⊥ := oddCoreOf_eq_bot_of_normal Q hO
    have hQK : ∀ J ∈ Ω, Odd (Nat.card ↥(Q ⊓ J)) := by
      intro J hJ
      rw [inf_comm, hmiss Q hQn hQ2 J hJ]
      simp
    obtain ⟨hRcomm, -⟩ := l6_14' h67 (l6_2 p f) h69 h611 hp hq G Ω hΩ Q hOQ hQK
    have hJc : ∀ J ∈ Ω, J ≤ Subgroup.centralizer (Q : Set G) := by
      intro J hJ
      refine AscQuot.le_of_forall_isSylow2In hp hq hΩ hJ
        (M := Subgroup.centralizer (Q : Set G)) ?_
      intro V hV x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hRcomm V (mem_RSet_of_isSylow2In hJ hV) x hx y hy).symm
    have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer (Q : Set G) := iSup₂_le hJc
    intro q hq'
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ ⨆ J ∈ Ω, J := by rw [hgen]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp (hle hg) q hq').symm
  have hZ2 : IsPGroup 2 ↥(Subgroup.center G) := center_isPGroup_two hO
  have hZH : Subgroup.center G ≤ H := by
    obtain ⟨z', hz', hcz'⟩ := c.exists_centralizer_le p f
    intro x hx
    apply hcz'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hx z').symm
  have hZbot : Subgroup.center G = ⊥ :=
    hq2 G Ω K S R W H c (Subgroup.center G) le_rfl hZ2 hZH
      (fun J hJ => hmiss _ inferInstance hZ2 J hJ)
  have h2triv : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → Q = ⊥ := by
    intro Q hQn hQ2
    have := hcent Q hQn hQ2
    rw [hZbot] at this
    exact le_bot_iff.mp this
  have hsolv := AscThmA.solvable_normal_eq_bot_of_oddCore hO h2triv
  exact ⟨hO, exists_normal_simple_of_l6_2 (l6_2 p f) hp hq hΩ hsolv hgen hK htrans⟩

end CFSG.ClassicalInvolution.Asc77
