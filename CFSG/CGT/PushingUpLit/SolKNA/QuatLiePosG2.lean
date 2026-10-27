module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLiePosG2Check
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import Certificates.Certificate77002
import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.SolKNA.Quaternion
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.RankThree.PartTwo.Census.Carrier
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  (dec14 dec14_one14 dec14_mul14 dec14_sq14 dec14_injective canon14 canon14_one14 canon14_mul14
    sq14 elemsS)
open CFSG.Quasithin.G2U (allCheck allCheck_spec)

section Abstract

theorem exists_q16Rel {N : ℕ} [NeZero N] (h4 : 4 ∣ N) :
    ∃ x y : QuaternionGroup N, x ^ 8 = 1 ∧ x ^ 4 ≠ 1 ∧ y ^ 2 = x ^ 4 ∧ x * y * x = y := by
  obtain ⟨M, rfl⟩ := h4
  have hM : 0 < M := by
    have := NeZero.ne (4 * M)
    omega
  refine ⟨(QuaternionGroup.a 1) ^ M, QuaternionGroup.xa 0, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, show M * 8 = 2 * (4 * M) by ring]
    exact QuaternionGroup.a_one_pow_n
  · rw [← pow_mul, show M * 4 = 4 * M by ring, QuaternionGroup.a_one_pow, QuaternionGroup.one_def]
    intro h
    have h' := QuaternionGroup.a.inj h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by omega) h'
    omega
  · rw [QuaternionGroup.xa_sq, ← pow_mul, show M * 4 = 4 * M by ring, QuaternionGroup.a_one_pow]
  · rw [QuaternionGroup.a_one_pow, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
    simp

theorem isPGroup_two_of_quaternion {X : Type*} [Group X] {Q : Subgroup X} {n : ℕ}
    (e : ↥Q ≃* QuaternionGroup (2 ^ (n - 2))) (hn : 3 ≤ n) : IsPGroup 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h4 : (4 : ℕ) * 2 ^ (n - 2) = 2 ^ n := by
    calc (4 : ℕ) * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2) := by norm_num
      _ = 2 ^ (2 + (n - 2)) := (pow_add 2 2 (n - 2)).symm
      _ = 2 ^ n := by congr 1; omega
  exact h4

theorem exists_conj_mem_of_isPGroup {H : Type*} [Group H] [Finite H] {S : Subgroup H}
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) {Q : Subgroup H} (hQ : IsPGroup 2 Q) :
    ∃ c : H, ∀ q ∈ Q, c * q * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  let SS : Sylow 2 H := hSp.toSylow hSi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H SS P
  have hPeq : (P : Subgroup H) = S.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • SS : Sylow 2 H) : Subgroup H) = (P : Subgroup H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    exact h1.symm
  refine ⟨g⁻¹, fun q hq => ?_⟩
  have hqP : q ∈ (P : Subgroup H) := hP hq
  rw [hPeq] at hqP
  obtain ⟨s, hs, rfl⟩ := hqP
  have e : g⁻¹ * (MulAut.conj g).toMonoidHom s * g⁻¹⁻¹ = s := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hs

theorem nonempty_quaternion_two_of_sylow {X : Type} {H : Type*} [Group X] [Group H] [Finite H]
    (ψ : X →* H) (hψ : Function.Injective ψ) {S : Subgroup H} (hSp : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index)
    (hfree : ∀ x ∈ S, ∀ y ∈ S, x ^ 8 = 1 → x ^ 4 ≠ 1 → y ^ 2 = x ^ 4 → x * y * x = y → False)
    {Q : Subgroup X} (hQ : IsQuaternionTwoGroup Q) : Nonempty (↥Q ≃* QuaternionGroup 2) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hQ
  by_cases h3 : n = 3
  · subst h3
    exact ⟨e⟩
  exfalso
  have h4N : 4 ∣ 2 ^ (n - 2) := by
    have := pow_dvd_pow 2 (show 2 ≤ n - 2 by omega)
    simpa using this
  obtain ⟨x₀, y₀, h8, h4, hy, hxy⟩ := exists_q16Rel h4N
  let φ : QuaternionGroup (2 ^ (n - 2)) →* H := (ψ.comp Q.subtype).comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := (hψ.comp Q.subtype_injective).comp e.symm.injective
  have hQp : IsPGroup 2 (Q.map ψ) := (isPGroup_two_of_quaternion e hn).map ψ
  obtain ⟨c, hc⟩ := exists_conj_mem_of_isPGroup hSp hSi hQp
  have hmem : ∀ z : QuaternionGroup (2 ^ (n - 2)), c * φ z * c⁻¹ ∈ S := fun z =>
    hc _ ⟨((e.symm z : ↥Q) : X), (e.symm z).2, rfl⟩
  refine hfree (c * φ x₀ * c⁻¹) (hmem x₀) (c * φ y₀ * c⁻¹) (hmem y₀) ?_ ?_ ?_ ?_
  · rw [conj_pow, ← map_pow, h8, map_one]
    group
  · intro h
    rw [conj_pow, ← map_pow] at h
    apply h4
    apply hφ
    rw [map_one]
    calc φ (x₀ ^ 4) = c⁻¹ * (c * φ (x₀ ^ 4) * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rw [conj_pow, conj_pow, ← map_pow, ← map_pow, hy]
  · calc c * φ x₀ * c⁻¹ * (c * φ y₀ * c⁻¹) * (c * φ x₀ * c⁻¹)
        = c * φ (x₀ * y₀ * x₀) * c⁻¹ := by simp only [map_mul]; group
      _ = c * φ y₀ * c⁻¹ := by rw [hxy]

theorem chevalley_g2_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .G2 0 3 1) :
    CFSG.Blueprint.ChevalleyExceptionalModel X .G2 3 1 :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide)

end Abstract

section Soundness

theorem q16FreeAt_sound {es : Array (List ℕ)} {x y : List ℕ} (hyc : canon14 y = true)
    (hy : ∃ k < es.size, es.getD k [] = y) (h : q16FreeAt es x = true)
    (h8 : dec14 x ^ 8 = 1) (h4 : dec14 x ^ 4 ≠ 1) (hy2 : dec14 y ^ 2 = dec14 x ^ 4)
    (hxy : dec14 x * dec14 y * dec14 x = dec14 y) : False := by
  have e4 : dec14 (sq14 (sq14 x)) = dec14 x ^ 4 := by
    rw [dec14_sq14 (sq14 x), dec14_sq14 x, ← pow_mul]
  have e8 : dec14 (sq14 (sq14 (sq14 x))) = dec14 x ^ 8 := by
    rw [dec14_sq14 (sq14 (sq14 x)), e4, ← pow_mul]
  simp only [q16FreeAt, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with (h | h) | h
  · exact h4 (by rw [← e4, h, dec14_one14])
  · exact h (dec14_injective (canon14_mul14 _ _) canon14_one14 (by rw [e8, h8, dec14_one14]))
  · obtain ⟨k, hk, rfl⟩ := hy
    have h' := allCheck_spec h hk
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h'
    rcases h' with h1 | h1
    · exact h1 (dec14_injective (canon14_mul14 _ _) (canon14_mul14 _ _)
        (by rw [dec14_sq14 (es.getD k []), e4, hy2]))
    · exact h1 (dec14_injective (canon14_mul14 _ _) hyc
        (by rw [dec14_mul14, dec14_mul14, hxy]))

end Soundness

section Sylow


theorem S2H_q16Free : ∀ x ∈ G2Three.S2H, ∀ y ∈ G2Three.S2H, x ^ 8 = 1 → x ^ 4 ≠ 1 →
    y ^ 2 = x ^ 4 → x * y * x = y → False := by
  intro x hx y hy h8 h4 hy2 hxy
  obtain ⟨k, hk, hkx⟩ := G2Three.exists_code_S2 (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨k', hk', hky⟩ := G2Three.exists_code_S2 (Subgroup.mem_subgroupOf.mp hy)
  have hcan : allCheck canon14 elemsS = true := G2Three.certS.2.2.2
  have hfree : allCheck (q16FreeAt elemsS) elemsS = true :=
    Certificates.certificate77002
  let ρ : G2Three.H3 →* Matrix (Fin 14) (Fin 14) (ZMod 3) :=
    (Units.coeHom _).comp G2Three.R3.subtype
  have hρ : Function.Injective ρ := Units.val_injective.comp G2Three.R3.subtype_injective
  refine q16FreeAt_sound (x := elemsS.getD k []) (y := elemsS.getD k' [])
    (allCheck_spec hcan hk') ⟨k', hk', rfl⟩ (allCheck_spec hfree hk) ?_ ?_ ?_ ?_
  · rw [hkx]
    show ρ x ^ 8 = 1
    rw [← map_pow, h8, map_one]
  · rw [hkx]
    show ρ x ^ 4 ≠ 1
    intro h
    apply h4
    apply hρ
    rw [map_pow, h, map_one]
  · rw [hkx, hky]
    show ρ y ^ 2 = ρ x ^ 4
    rw [← map_pow, ← map_pow, hy2]
  · rw [hkx, hky]
    show ρ x * ρ y * ρ x = ρ y
    rw [← map_mul, ← map_mul, hxy]

end Sylow

section Transport


theorem exists_equiv_H3 {X : Type} [Group X]
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 3 1) : Nonempty (X ≃* G2Three.H3) := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hm
  have : Fintype K := Fintype.ofFinite K
  have hFc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  exact ⟨(e.trans (CFSG.TauCetiBridge.adjointQuotientCongr
    (FiniteField.ringEquivOfCardEq hFc))).trans G2Three.adjointQuotientEquivR3⟩


theorem posModel_G2 : PosModel .G2 0 := by
  intro X _ _ hm Q hQ
  obtain ⟨ψ⟩ := exists_equiv_H3 (chevalley_g2_of_lieModel hm)
  have hS : Nat.card G2Three.S2H = 64 := G2Three.card_S2H
  refine nonempty_quaternion_two_of_sylow (ψ : X →* G2Three.H3) ψ.injective
    (S := G2Three.S2H) ?_ ?_ S2H_q16Free hQ
  · exact IsPGroup.of_card (n := 6) (hS.trans (by norm_num))
  · have h := Subgroup.card_mul_index G2Three.S2H
    rw [hS, G2Three.card_R3] at h
    omega

end Transport

end CFSG.CGT.PushingUpLit.SolKNA
