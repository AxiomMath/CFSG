module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOdd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Sec


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e189_section_normalizes {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hq : ∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hO : classicalInvolutionOddCore X = ⊥) (hA : ∀ J ∈ Φ, AEmpty Φ J)
    (hgen : omegaGen Φ = ⊤) (htr : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (htw : ∃ K ∈ Φ, ∃ K' ∈ twinSet Φ K, K' ≠ K) :
    ∀ J ∈ Φ, ∀ L ∈ Φ, ∀ v : X, IsUniqueInvolution L v → v ∈ Subgroup.normalizer (J : Set X) := by
  obtain ⟨K, hK, K', hK', hne⟩ := htw
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΦ hK
  have htc := tightCore_eq_self_of_twoGroup_quot hΦ h2
  have hΦeq : CoreAssembly.conjClass K = Φ := by
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact hΦ.conjInvariant g K hK
    · intro hL
      obtain ⟨g, hg⟩ := htr K hK L hL
      exact ⟨g, hg⟩
  obtain S : Sylow 2 ↥K := Classical.choice inferInstance
  have hPs : IsSylow2In ((S : Subgroup K).map K.subtype) K := Asc77.isSylow2In_map_subtype K S
  obtain ⟨e0⟩ := hq K hK _ hPs
  have eS : ↥(S : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans e0
  have hcardP : Nat.card ↥((S : Subgroup K).map K.subtype) = 2 ^ r := by
    rw [Nat.card_congr e0.toEquiv]
    exact card_quaternion_pow (by omega)
  have hd : Q8TwinDatum K S z :=
    ⟨⟨r, by omega, ⟨eS⟩⟩,
      mem_of_isUniqueInvolution_of_isPGroup hz hPs.1 hPs.2.1 (by
        rw [hcardP]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)),
      orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one,
      le_centralizer_of_unique hz, h2 K hK⟩
  have hgenK : TightSelfGen K := by
    unfold TightSelfGen
    rw [htc K hK, eq_top_iff, ← hgen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, hg⟩ := htr K hK L hL
    rw [← hg]
    exact le_iSup (fun g : X => conjSub g K) g
  have hE2 : TightInO2 z := by
    refine hT X hlt K S z hd ⟨eS⟩ hgenK hO ?_ ?_ ?_
    · rw [htc K hK, hΦeq]; exact hΦ
    · rw [htc K hK, hΦeq]; exact hA K hK
    · rw [htc K hK, hΦeq]; exact ⟨K', hK', hne⟩
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hE2
  have hθ : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ :=
    TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal hO hQn hQ2 hzQ
  have hK2 : IsPGroup 2 ↥K := isPGroup_of_oddCent hΦ hK hz hθ (h2 K hK)
  have h2' : ∀ J ∈ Φ, IsPGroup 2 ↥J := by
    intro J hJ
    obtain ⟨g, hg⟩ := htr K hK J hJ
    rw [← hg]
    exact isPGroup_conjSub g hK2
  have h8 : ∀ J ∈ Φ, Nat.card ↥J = 2 ^ r := by
    intro J hJ
    obtain ⟨e⟩ := hq J hJ J ⟨le_rfl, h2' J hJ, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_quaternion_pow (by omega)
  have hinO2 : ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u →
      ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 ↥Q ∧ u ∈ Q := by
    intro L hL u hu
    obtain ⟨g, hg⟩ := htr K hK L hL
    have hzg : IsUniqueInvolution L (g * z * g⁻¹) := hg ▸ hz.conj g
    have hug : u = g * z * g⁻¹ := hu.eq hzg
    exact ⟨Q, hQn, hQ2, hug ▸ hQn.conj_mem z hzQ g⟩
  intro J hJ L hL v hv
  exact mem_normalizer_of_four_le hr hΦ h2' h8 hinO2 hJ hL hv

theorem e189_section_no_swap {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n) {Y : Type} [Group Y]
    [Finite Y] (hlt : Nat.card Y < n) {Λ : Set (Subgroup Y)} (hΛ : HypOmegaGen Λ)
    (h2 : ∀ L ∈ Λ, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hq : ∀ L ∈ Λ, ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ L ∈ Λ, AEmpty Λ L) (hgen : (⨆ L ∈ Λ, L) = ⊤) {K : Subgroup Y} (hK : K ∈ Λ)
    (htr : ∀ L ∈ Λ, ∃ y : Y, conjSub y K = L) {z t : Y} (hz : IsUniqueInvolution K z)
    {J : Subgroup Y} (hJ : J ∈ Λ) (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) :
    conjSub t K = K := by
  classical
  by_contra hne
  set N₀ : Subgroup Y := classicalInvolutionOddCore Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card Y
  set mk := QuotientGroup.mk' N₀ with hmk
  have hΛ' : HypOmegaGen (quotFamily Λ N₀) := TwinEdge.hypOmegaGen_quotFamily_odd hΛ hN₀odd
  have hq' : ∀ M ∈ quotFamily Λ N₀, ∀ P : Subgroup (Y ⧸ N₀), IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := fun M hM =>
    TwinDisc.forall_sylow_iso_of_exists (quat_quot_odd hN₀odd hq M hM)
  have h2' := TwinThmE.two_quot_odd h2 hN₀odd
  have hA' := TwinThmE.aEmpty_quot_odd hΛ hN₀odd hA
  have hOq : classicalInvolutionOddCore (Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hcard' : Nat.card (Y ⧸ N₀) < n := by
    have h1 : Nat.card (Y ⧸ N₀) ≤ Nat.card Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hgen' : omegaGen (quotFamily Λ N₀) = ⊤ := by
    have h1 : (⨆ L ∈ Λ, L).map mk = ⨆ L ∈ Λ, L.map mk := by
      rw [Subgroup.map_iSup]
      congr 1
      funext L
      rw [Subgroup.map_iSup]
    have h2 : (⊤ : Subgroup Y).map mk = ⊤ :=
      Subgroup.map_top_of_surjective mk (QuotientGroup.mk'_surjective N₀)
    apply top_le_iff.mp
    rw [← h2, ← hgen, h1]
    exact iSup₂_le fun L hL => le_iSup₂ (f := fun L' (_ : L' ∈ quotFamily Λ N₀) => L')
      (L.map mk) (map_mem_quotFamily hL)
  have hTb : ∀ L ∈ quotFamily Λ N₀, ∃ y : Y ⧸ N₀, conjSub y (K.map mk) = L := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨y, hy⟩ := htr L hL
    exact ⟨mk y, by
      show conjSub (mk y) (K.map mk) = L.map mk
      rw [← hy, AscQuot.map_conjSub]⟩
  have htr' : ∀ A ∈ quotFamily Λ N₀, ∀ B ∈ quotFamily Λ N₀, ∃ g : Y ⧸ N₀, conjSub g A = B := by
    intro A hA B hB
    obtain ⟨a, rfl⟩ := hTb A hA
    obtain ⟨b, rfl⟩ := hTb B hB
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have hzK' : IsUniqueInvolution (conjSub t K) z := by
    have := hz.conj t
    rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
  have hK'tw : conjSub t K ∈ twinSet Λ K := ⟨hΛ.conjInvariant t K hK, z, hz, hzK'⟩
  have hmne : (conjSub t K).map mk ≠ K.map mk :=
    TwinThmE.map_ne_of_twin hΛ hN₀odd hK hK'tw hne
  have htw' : ∃ M ∈ quotFamily Λ N₀, ∃ M' ∈ twinSet (quotFamily Λ N₀) M, M' ≠ M :=
    ⟨K.map mk, map_mem_quotFamily hK, (conjSub t K).map mk,
      ⟨map_mem_quotFamily (hΛ.conjInvariant t K hK), mk z,
        isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd K) hz,
        isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd (conjSub t K)) hzK'⟩, hmne⟩
  have hnorm := e189_section_normalizes hr hT hcard' hΛ' h2' hq' hOq hA' hgen' htr' htw'
    (K.map mk) (map_mem_quotFamily hK) (J.map mk) (map_mem_quotFamily hJ) (mk t)
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN₀odd J) ht)
  apply hmne
  rw [AscQuot.map_conjSub]
  exact mem_normalizer_iff_conjSub_eq.mp hnorm

end Sec

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
