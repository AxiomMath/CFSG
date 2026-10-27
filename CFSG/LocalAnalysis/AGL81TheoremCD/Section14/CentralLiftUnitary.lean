module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftBorel
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftUnitaryAut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryCover
import CFSG.Walter.Cited.OddQuotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.AGLEmbedding
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G]

private theorem mem_image_of_fixed {q f : ℕ} {F : Type} [Field F] (K : Subgroup G) {b : G}
    (ψ : unitarySU q f F 3 ≃* ↥K) (φ : MulAut ↥K)
    (hφ : ∀ k : ↥K, ((φ k : ↥K) : G) = b * k * b⁻¹)
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hle : ((K ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf K).map
      (QuotientGroup.mk' (Subgroup.center ↥K)) ≤ H)
    {a : unitarySU q f F 3} (ha : ((ψ.trans φ).trans ψ.symm) a = a) :
    (QuotientGroup.mk' (Subgroup.center ↥K)) (ψ a) ∈ H := by
  classical
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  have hφa : φ (ψ a) = ψ a := by
    have h := congrArg (⇑ψ) ha
    simpa [π, MulEquiv.trans_apply] using h
  have hcommb : b * (ψ a : G) = (ψ a : G) * b := by
    have h := congrArg (fun k : ↥K => (k : G)) hφa
    rw [hφ] at h
    calc b * (ψ a : G) = (b * (ψ a : G) * b⁻¹) * b := by group
      _ = (ψ a : G) * b := by rw [h]
  have hcent : (ψ a : G) ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcommb.symm
  have hx : (ψ a : G) ∈ K ⊓ Subgroup.centralizer ({b} : Set G) := ⟨(ψ a).2, hcent⟩
  let w : (K ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf K := ⟨ψ a, hx⟩
  have hw : π w ∈ H := hle (Subgroup.mem_map_of_mem π w.2)
  simpa [w, π] using hw

private theorem not_fixes_kleinFour {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {K : Subgroup G}
    [Finite G] {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex q d)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* CatGroup d)
    (S : Sylow q (↥K ⧸ Subgroup.center ↥K))
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hHN : H = Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _))
    (hZ : Nat.card (Subgroup.center ↥K) = 3) {F : Type} [Field F]
    {ψ : unitarySU q d.1.fieldExponent F 3 ≃* ↥K} {φ : MulAut ↥K}
    (hmemH : ∀ a : unitarySU q d.1.fieldExponent F 3,
      ((ψ.trans φ).trans ψ.symm) a = a →
        (QuotientGroup.mk' (Subgroup.center ↥K)) (ψ a) ∈ H)
    (hfix : FixesKleinFour ((ψ.trans φ).trans ψ.symm)) : False := by
  classical
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  obtain ⟨a1, a2, hθa1, hθa2, ha1sq, ha2sq, hcomm, ha1ne, ha2ne, hneq⟩ := hfix
  have h1H : π (ψ a1) ∈ H := hmemH a1 hθa1
  have h2H : π (ψ a2) ∈ H := hmemH a2 hθa2
  have h1N : π (ψ a1) ∈ Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) := by
    rw [← hHN]; exact h1H
  have h2N : π (ψ a2) ∈ Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) := by
    rw [← hHN]; exact h2H
  have hψa1sq : (ψ a1) ^ 2 = 1 := by rw [← map_pow, ha1sq, map_one]
  have hψa2sq : (ψ a2) ^ 2 = 1 := by rw [← map_pow, ha2sq, map_one]
  have hπ1sq : π (ψ a1) ^ 2 = 1 := by rw [← map_pow, hψa1sq, map_one]
  have hπ2sq : π (ψ a2) ^ 2 = 1 := by rw [← map_pow, hψa2sq, map_one]
  have hψcomm : ψ a1 * ψ a2 = ψ a2 * ψ a1 := by rw [← map_mul, ← map_mul, hcomm]
  have hπcomm : π (ψ a1) * π (ψ a2) = π (ψ a2) * π (ψ a1) := by
    calc π (ψ a1) * π (ψ a2) = π (ψ a1 * ψ a2) := by rw [map_mul]
      _ = π (ψ a2 * ψ a1) := by rw [hψcomm]
      _ = π (ψ a2) * π (ψ a1) := by rw [map_mul]
  have hres := eq_of_mem_normalizer_sylow_unitary (L := ↥K ⧸ Subgroup.center ↥K) hq2 hd ⟨e⟩ S
    h1N h2N hπ1sq hπ2sq hπcomm
  have hZ1 : ∀ x : ↥K, π x = 1 → x ^ 2 = 1 → x = 1 := fun x hx h2 =>
    CFSG.Walter.Suzuki.eq_one_of_pow_two_pow_eq_one (Subgroup.center ↥K) (by rw [hZ]; decide)
      ((QuotientGroup.eq_one_iff x).mp hx) (k := 1) (by simpa using h2)
  rcases hres with h1 | h2 | h12
  · exact ha1ne (ψ.injective (by rw [hZ1 _ h1 hψa1sq, map_one]))
  · exact ha2ne (ψ.injective (by rw [hZ1 _ h2 hψa2sq, map_one]))
  · refine hneq (ψ.injective (mul_inv_eq_one.mp (hZ1 _ ?_ ?_)))
    · rw [map_mul, map_inv, h12, mul_inv_cancel]
    · rw [(show Commute (ψ a1) (ψ a2) from hψcomm).inv_right.mul_pow, inv_pow, hψa1sq, hψa2sq,
        inv_one, mul_one]

private theorem not_fixes_torusPrime {q : ℕ} [Fact q.Prime] {K : Subgroup G} [Finite G]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex q d)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* CatGroup d)
    (S : Sylow q (↥K ⧸ Subgroup.center ↥K))
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hHN : H = Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _))
    (hZ : Nat.card (Subgroup.center ↥K) = 3) {F : Type} [Field F]
    {ψ : unitarySU q d.1.fieldExponent F 3 ≃* ↥K} {φ : MulAut ↥K}
    (hmemH : ∀ a : unitarySU q d.1.fieldExponent F 3,
      ((ψ.trans φ).trans ψ.symm) a = a →
        (QuotientGroup.mk' (Subgroup.center ↥K)) (ψ a) ∈ H)
    (hfix : FixesTorusPrime (q ^ d.1.fieldExponent) ((ψ.trans φ).trans ψ.symm)) : False := by
  classical
  let π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K)
  obtain ⟨y, hθy, r, hr, hr3, hrdvd, hordy⟩ := hfix
  have hyN : π (ψ y) ∈ Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) := by
    rw [← hHN]; exact hmemH y hθy
  have hψyord : orderOf (ψ y) = r := by rw [MulEquiv.orderOf_eq, hordy]
  have hne1 : orderOf (π (ψ y)) ≠ 1 := by
    intro h1
    have hmemZ : ψ y ∈ Subgroup.center ↥K :=
      (QuotientGroup.eq_one_iff (ψ y)).mp (orderOf_eq_one_iff.mp h1)
    have hdvd3 : orderOf (ψ y) ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hmemZ
      rwa [hZ] at this
    rw [hψyord] at hdvd3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact hr.ne_one h
    · exact hr3 h
  have hdvd : orderOf (π (ψ y)) ∣ r := by
    rw [← hψyord]; exact orderOf_map_dvd π (ψ y)
  have horder : orderOf (π (ψ y)) = r := by
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hdvdN : r ∣ Nat.card (Subgroup.normalizer
      ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set (↥K ⧸ Subgroup.center ↥K))) := by
    rw [← horder]
    exact Subgroup.orderOf_dvd_natCard _ hyN
  have hdvd' := hdvdN.trans (card_normalizer_sylow_unitary_dvd
    (L := ↥K ⧸ Subgroup.center ↥K) hd ⟨e⟩ S)
  exact hrdvd hdvd'

private theorem exists_unitarySU_mulEquiv
    {q : ℕ} (hq : q.Prime)
    [Finite G] (K : Subgroup G) (hK : CFSG.IsQuasisimple ↥K) {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hd : d.1 = .twistedA 2 Q) (hQq : Q.p = q) (h3 : 3 ∣ Q.card + 1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hZ : Nat.card (Subgroup.center ↥K) = 3) :
    ∃ (F : Type) (_ : Field F) (hU : UnitaryFieldData q d.1.fieldExponent F),
      2 < q ^ d.1.fieldExponent ∧ 3 ∣ q ^ d.1.fieldExponent + 1 ∧
        Nonempty (unitarySU q d.1.fieldExponent F 3 ≃* ↥K) := by
  have hfe : d.1.fieldExponent = Q.exponent := by
    rw [hd]
    exact TauCeti.LieTypeIndex.fieldExponent_twistedA 2 Q
  have hQcard : q ^ d.1.fieldExponent = Q.card := by
    rw [hfe, ← hQq, ← TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  rw [hd] at hrange
  have hQ3 : 3 ≤ Q.card := hrange.2 rfl
  have hq3 : 2 < q ^ d.1.fieldExponent := by rw [hQcard]; omega
  have hdU : IsUnitaryIndex q d := ⟨Q, hQq, hd⟩
  obtain ⟨-, F, _, _, hFcard, ⟨e'⟩⟩ := UnitaryModel.statedClassicalModel hdU ⟨e⟩
  have hU : UnitaryFieldData q d.1.fieldExponent F :=
    ⟨hq, by rw [hfe]; exact Q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hcenne : Subgroup.center ↥K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ
    omega
  refine ⟨F, inferInstance, hU, hq3, by rw [hQcard]; exact h3, ?_⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary.exists_mulEquiv_unitarySU_three hU hq3
    (Group.isPerfect_def.mp hK.1) (e'.trans (unitaryPSUEquiv hU (by norm_num)).symm) hcenne

section Certificates


theorem not_le_of_unitary {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {X : Type} [Group X] [Finite X] (K : Subgroup X) (hK : CFSG.IsQuasisimple ↥K)
    (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower) (hd : d.1 = .twistedA 2 Q)
    (hQq : Q.p = q) (h3 : 3 ∣ Q.card + 1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hZ : Nat.card (Subgroup.center ↥K) = 3)
    {b : X} (hbN : b ∈ Subgroup.normalizer (K : Set X)) (hb : orderOf b = 3)
    {H : Subgroup (↥K ⧸ Subgroup.center ↥K)} (hH : H ≠ ⊤)
    (hS : ∃ S : Sylow q (↥K ⧸ Subgroup.center ↥K),
      Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) ≤ H) :
    ¬ ((K ⊓ Subgroup.centralizer ({b} : Set X)).subgroupOf K).map
        (QuotientGroup.mk' (Subgroup.center ↥K)) ≤ H := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  intro hle
  obtain ⟨S, hSH⟩ := hS
  have hdU : IsUnitaryIndex q d := ⟨Q, hQq, hd⟩
  have hHN : H = Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) :=
    ((kFactUnitaryBorelMaximal _ q d hdU ⟨e⟩ S).le_iff_eq hH).mp hSH
  obtain ⟨F, _, hU, hq3, h3', ⟨ψ⟩⟩ := exists_unitarySU_mulEquiv hq K hK hd hQq h3 e hZ
  let φ : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbN⟩
  let θ : MulAut (unitarySU q d.1.fieldExponent F 3) := (ψ.trans φ).trans ψ.symm
  have hθ : θ ^ 3 = 1 := by
    have hb3 : b ^ 3 = 1 := by simpa [hb] using pow_orderOf_eq_one b
    have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 := Subtype.ext hb3
    change MulAut.congr ψ.symm (K.normalizerMonoidHom ⟨b, hbN⟩) ^ 3 = 1
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hmemH : ∀ a : unitarySU q d.1.fieldExponent F 3, θ a = a →
      (QuotientGroup.mk' (Subgroup.center ↥K)) (ψ a) ∈ H :=
    fun a ha => mem_image_of_fixed K ψ φ (fun _ => rfl) hle (by simpa [θ] using ha)
  rcases fixesKleinFour_or_fixesTorusPrime hU hq2 hq3 h3' hθ with hK4 | hTP
  · exact not_fixes_kleinFour hq2 hdU e S hHN hZ hmemH (by simpa [θ] using hK4)
  · exact not_fixes_torusPrime hdU e S hHN hZ hmemH (by simpa [θ] using hTP)

end Certificates

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
