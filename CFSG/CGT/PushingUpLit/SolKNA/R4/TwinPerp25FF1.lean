module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)

section Sylow


variable {Y : Type} [Group Y] [Finite Y]

theorem exists_oddCore_mul_sylow {K R : Subgroup Y} (hR : IsSylow2In R K)
    (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) :
    ∀ k ∈ K, ∃ n ∈ oddCoreOf K, ∃ x ∈ R, k = n * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp h2
  have hNidx : (classicalInvolutionOddCore ↥K).index = 2 ^ e := by
    rw [Subgroup.index_eq_card]
    exact he
  have hnd : ¬ 2 ∣ (R.subgroupOf K).index := Sylow.not_dvd_index (TwinEdge.sylowOf hR)
  have hcop : Nat.Coprime (2 ^ e) (R.subgroupOf K).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd)
  have htop : classicalInvolutionOddCore ↥K ⊔ R.subgroupOf K = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have h1 : (classicalInvolutionOddCore ↥K ⊔ R.subgroupOf K).index ∣
        (classicalInvolutionOddCore ↥K).index := Subgroup.index_dvd_of_le le_sup_left
    have h2' : (classicalInvolutionOddCore ↥K ⊔ R.subgroupOf K).index ∣
        (R.subgroupOf K).index := Subgroup.index_dvd_of_le le_sup_right
    rw [hNidx] at h1
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2'
  intro k hk
  have hmem : (⟨k, hk⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K ⊔ R.subgroupOf K := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(y : Y), ⟨y, hy, rfl⟩, (z : Y), Subgroup.mem_subgroupOf.mp hz, ?_⟩
  have := congrArg Subtype.val hyz
  simpa using this.symm

theorem natCard_le_inf_centralizer {K R : Subgroup Y} (hR : IsSylow2In R K)
    (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) {b : Y}
    (hbK : b ∈ Subgroup.normalizer (K : Set Y)) (hbR : b ∈ Subgroup.normalizer (R : Set Y))
    {V : Subgroup Y} (hVK : V ≤ K) (hVb : V ≤ Subgroup.centralizer ({b} : Set Y))
    (hV : IsPGroup 2 ↥V) :
    Nat.card V ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({b} : Set Y)) := by
  classical
  have hdec := exists_oddCore_mul_sylow hR h2
  have hN : Odd (Nat.card ↥(oddCoreOf K)) := oddCoreOf_odd_natCard K
  have hbN : b ∈ Subgroup.normalizer (oddCoreOf K : Set Y) :=
    mem_normalizer_oddCore_of_mem_normalizer hbK
  have hNR : oddCoreOf K ⊓ R = ⊥ := by
    rw [inf_comm]
    exact inf_odd_two_eq_bot hR.2.1 hN
  have hNV : V ⊓ oddCoreOf K = ⊥ := inf_odd_two_eq_bot hV hN
  have key : ∀ v : ↥V, ∃ x : ↥(R ⊓ Subgroup.centralizer ({b} : Set Y)),
      ∃ n ∈ oddCoreOf K, (v : Y) = n * (x : Y) := by
    intro v
    obtain ⟨n, hn, x, hx, hvx⟩ := hdec v (hVK v.2)
    have hvb : (v : Y) * b = b * (v : Y) := Subgroup.mem_centralizer_singleton_iff.mp (hVb v.2)
    have h1 : b * n * b⁻¹ ∈ oddCoreOf K := (Subgroup.mem_normalizer_iff.mp hbN n).mp hn
    have h2' : b * x * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hbR x).mp hx
    have h3 : (b * n * b⁻¹) * (b * x * b⁻¹) = n * x := by
      rw [← hvx]
      calc (b * n * b⁻¹) * (b * x * b⁻¹) = b * (n * x) * b⁻¹ := by group
        _ = b * (v : Y) * b⁻¹ := by rw [hvx]
        _ = (v : Y) := by rw [← hvb]; group
    have h4 : n⁻¹ * (b * n * b⁻¹) = x * (b * x * b⁻¹)⁻¹ := by
      have : n⁻¹ * ((b * n * b⁻¹) * (b * x * b⁻¹)) * (b * x * b⁻¹)⁻¹ = x * (b * x * b⁻¹)⁻¹ := by
        rw [h3]
        group
      rw [← this]
      group
    have h5 : x * (b * x * b⁻¹)⁻¹ ∈ oddCoreOf K ⊓ R :=
      ⟨h4 ▸ (oddCoreOf K).mul_mem ((oddCoreOf K).inv_mem hn) h1, R.mul_mem hx (R.inv_mem h2')⟩
    rw [hNR, Subgroup.mem_bot] at h5
    have hbx : b * x * b⁻¹ = x := (mul_inv_eq_one.mp h5).symm
    refine ⟨⟨x, hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, n, hn, hvx⟩
    have : b * x = x * b := by
      calc b * x = (b * x * b⁻¹) * b := by group
        _ = x * b := by rw [hbx]
    exact this.symm
  choose f n hn hvf using key
  have hinj : Function.Injective f := by
    intro v w hvw
    have hvw' : (v : Y) * (w : Y)⁻¹ = n v * (n w)⁻¹ := by
      rw [hvf v, hvf w, hvw]
      group
    have hmem : (v : Y) * (w : Y)⁻¹ ∈ V ⊓ oddCoreOf K :=
      ⟨V.mul_mem v.2 (V.inv_mem w.2), hvw' ▸ (oddCoreOf K).mul_mem (hn v) ((oddCoreOf K).inv_mem (hn w))⟩
    rw [hNV, Subgroup.mem_bot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp hmem)
  exact Nat.card_le_card_of_injective f hinj

theorem isSylow2In_coreAt_of_isFAut {K R : Subgroup Y} (hR : IsSylow2In R K)
    (h2 : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) {b : Y}
    (hbK : b ∈ Subgroup.normalizer (K : Set Y)) (hF : IsFAut R b) :
    ∃ Q : Subgroup Y, IsSylow2In Q (coreAt b K) ∧ IsQuatSub Q ∧ Nat.card Q * 2 = Nat.card R := by
  classical
  obtain ⟨hbR, -, Q, R', hQ, hqQ, hR', hcard⟩ := hF
  have hRR : R' = R := (hR'.eq_of_le (hR.2.1.to_le le_rfl) le_rfl hR'.1).symm
  have hQeq : R ⊓ Subgroup.centralizer ({b} : Set Y) = Q :=
    hQ.eq_of_le (hR.2.1.to_le inf_le_left) le_rfl hQ.1
  have hQK : Q ≤ K ⊓ Subgroup.centralizer ({b} : Set Y) := by
    rw [← hQeq]
    exact inf_le_inf_right _ hR.1
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have hQM : Q ≤ coreAt b K := le_tightCore_of_isPGroup hQK hQ2
  refine ⟨Q, ⟨hQM, hQ2, fun V' hV'M hV'2 hQV' => ?_⟩, hqQ, by rw [← hRR]; omega⟩
  have hV'K : V' ≤ K := hV'M.trans (TwinADescent.coreAt_le_left b K)
  have hV'b : V' ≤ Subgroup.centralizer ({b} : Set Y) :=
    hV'M.trans (TwinADescent.coreAt_le_centralizer b K)
  have hle := natCard_le_inf_centralizer hR h2 hbK hbR hV'K hV'b hV'2
  rw [hQeq] at hle
  exact (Subgroup.eq_of_le_of_card_ge hQV' hle).symm

end Sylow

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
