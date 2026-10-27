module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmECent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Sev1

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Sev1


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.center_eq_bot (h6 : E18_6 r) (c : MinCex r Ω K S R W H) :
    Subgroup.center G = ⊥ := by
  obtain ⟨-, F, -, -, -, hF⟩ := h6 G Ω K S R W H c
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp hx y)
  rw [hF] at this
  exact this

theorem MinCex.centralizer_ne_top (h6 : E18_6 r) (c : MinCex r Ω K S R W H) {x : G}
    (hx : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro h
  apply hx
  have hc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have : y ∈ Subgroup.centralizer ({x} : Set G) := by rw [h]; exact Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [c.center_eq_bot h6] at hc
  exact Subgroup.mem_bot.mp hc

theorem MinCex.exists_z (c : MinCex r Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz, hzW⟩ := c.exists_zW
  exact ⟨z, hz, hzW, c.centralizer_le hz⟩

theorem MinCex.inf_W_mem_USet (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {M R' : Subgroup G} (hMΩ : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, hWη, hηU, -, -⟩ := c.exists_eta hA
  have h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have h8 := c.stand.hyp.eight_le_of_mem_RSet hR'
    have := Subgroup.card_le_of_le (le_inf hR'M hR'S)
    omega
  have hmem := hM S η hη (fun V hV => (hηU V hV).2) M hMΩ h2
  rw [← hWη] at hmem
  exact (hηU _ hmem).1

theorem MinCex.exists_order_four_of_inf_W (c : MinCex r Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {M R' : Subgroup G} (hMΩ : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) :
    IsCyclic ↥(M ⊓ W) ∧ ∃ u ∈ M ⊓ W, orderOf u = 4 := by
  have hU := c.inf_W_mem_USet hA hM hMΩ hR' hR'M hR'S
  obtain ⟨R'', -, J, -, hRJ, hUR, hcyc, -, h4⟩ :=
    c.stand.hyp.exists_data_of_mem_USet hU
  refine ⟨hcyc, ?_⟩
  obtain ⟨u, hu, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic
    (c.stand.hyp.isPGroup_of_mem_USet hU) hcyc h4
  exact ⟨u, hu, hu4⟩

theorem MinCex.hbad_of_conj (c : MinCex r Ω K S R W H) {z g : G}
    (hz : IsUniqueInvolution K z) (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M (g * z * g⁻¹) → ∀ u ∈ M, orderOf u = 4 → u ∉ H :=
  E187C.hbad_of_conj_of c.stand.hyp.conjInvariant
    (fun hM => mem_dstarComp_of_twin_gen c.stand.hyp c.stand.mem hM)
    (fun hMS hu hu4 hx => c.mem_of_conj_mem_dstar hMS hu hu4 hx) hz hg

theorem MinCex.hC_of_conj (c : MinCex r Ω K S R W H) {z g : G}
    (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 →
      (g * z * g⁻¹) * x ≠ x * (g * z * g⁻¹) :=
  E187C.hC_of_conj_of (fun hM => mem_dstarComp_of_twin_gen c.stand.hyp c.stand.mem hM)
    (fun hMS hu hu4 hx => c.mem_of_conj_mem_dstar hMS hu hu4 hx) hz hzH hg

theorem inf_S_eq_of_mem_RSet' (hΩ : HypOmegaGen Ω) {S : Sylow 2 G}
    {M R' : Subgroup G} (hM : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ (S : Subgroup G) = R' :=
  TwinThmE.inf_S_eq_of_mem_RSet hΩ hM hR' hR'M hR'S


theorem MinCex.conjSub_mem_omegaNbr (c : MinCex r Ω K S R W H) {z t : G}
    (hz : IsUniqueInvolution K z) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    conjSub t K ∈ omegaNbr Ω K := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK : K ∈ Ω := c.stand.mem
  have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hRR
  have hR2 : IsPGroup 2 R := (Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK).2.1
  have hnK : conjSub t K ≠ K := by
    intro hK'
    apply hnc
    have := hz.conj_eq hK'
    calc t * z = (t * z * t⁻¹) * t := by group
      _ = z * t := by rw [this]
  have hK'Ω : conjSub t K ∈ Ω := hΩ.conjInvariant t K hK
  have hR'mem : conjSub t R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRR t
  have hR'K' : conjSub t R ≤ conjSub t K := conjSub_mono hRK
  have hR'S : conjSub t R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : t⁻¹ * x * t ∈ (S : Subgroup G) := hRS hx
    have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [this]
    exact S.mul_mem (S.mul_mem htS h1) (S.inv_mem htS)
  have hne : R ≠ conjSub t R := by
    intro hRR'
    have := hΩ.card_le_two_of_le_inf hK hK'Ω (Ne.symm hnK) hR2 hRK (hRR' ▸ hR'K')
    omega
  have hcomm : Commutes R (conjSub t R) :=
    Q3T8.Asc77.l6_7_proved G Ω hΩ S R hRR _ hR'mem hRS hR'S hne
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
  have hR'syl : IsSylow2In (conjSub t R) (conjSub t K) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR'mem hR'K'
  refine ⟨hK'Ω, hnK, conjSub t R, hR'mem, hR'K', ?_⟩
  refine hΩ.le_normalizer_of_le_centralizer hK hK'Ω (Ne.symm hnK) hz hR'K' hR'syl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hR'mem; omega) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hcomm z hzR x hx).symm

theorem MinCex.exists_delta (c : MinCex r Ω K S R W H) {z t : G}
    (hz : IsUniqueInvolution K z) (hzW : z ∈ W) (ht2 : t * t = 1)
    (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    ∃ B : Subgroup G, ∃ b : G, B ≤ (S : Subgroup G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
      IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧ b = z * (t * z * t⁻¹) ∧ b ∈ W ∧
      Subgroup.centralizer ({b} : Set G) ≤ H := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨B, b, hBS, hBt, hBb, hB8, hbdef, hbW, -⟩ :=
    E187C.exists_delta_of (H := ⊤) hΩ.conjInvariant (fun hR => hΩ.eight_le_of_mem_RSet hR)
      (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
      (fun hK hR hRK => Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK)
      (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
        hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hz hAJ hA2 hA3 hAc)
      (fun hR' hR'S hne => Q3T8.Asc77.l6_7_proved G Ω hΩ S R hRR _ hR' hRS hR'S hne)
      (fun _ _ _ _ _ _ _ _ _ => le_top)
      c.stand.mem hRR hRK hRS c.stand.hW.2.2 hz hzW ht2 htS hnc
  refine ⟨B, b, hBS, hBt, hBb, hB8, hbdef, hbW, ?_⟩
  have hJ : conjSub t K ∈ omegaNbr Ω K := c.conjSub_mem_omegaNbr hz htS hnc
  have hz' : IsUniqueInvolution (conjSub t K) (t * z * t⁻¹) := hz.conj t
  rw [hbdef]
  refine TwinThmEW.centralizer_le_mul_of_omegaNbr hΩ c.stand.mem c.hyp.trans hz (c.centralizer_le hz)
    hRR hRK hRS c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hJ hz' ?_ ?_
  · rw [← hbdef]; exact hBb.ne_one
  · rw [← hbdef]; exact hBb.sq

theorem centralizes_conj_of_mem_RSet' (hΩ : HypOmegaGen Ω) {S₁ : Sylow 2 G} {K₁ R₁ T : Subgroup G}
    {z₁ β : G} (hz₁ : IsUniqueInvolution K₁ z₁) (hR₁ : R₁ ∈ RSet Ω) (hR₁K₁ : R₁ ≤ K₁)
    (hR₁S : R₁ ≤ (S₁ : Subgroup G)) (hβ : β ∈ (S₁ : Subgroup G)) (hT : T ∈ RSet Ω)
    (hTS : T ≤ (S₁ : Subgroup G)) : ∀ y ∈ T, y * (β * z₁ * β⁻¹) = (β * z₁ * β⁻¹) * y :=
  E187C.centralizes_conj_of_mem_RSet_of hΩ.conjInvariant
    (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun S₁ X hX Y hY hXS hYS hXY => Q3T8.Asc77.l6_7_proved G Ω hΩ S₁ X hX Y hY hXS hYS hXY)
    hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS

end Sev1

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
