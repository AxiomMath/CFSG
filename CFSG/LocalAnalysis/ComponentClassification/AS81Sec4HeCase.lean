module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step46
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4End
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Held
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step49

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial Hexa
open Matrix
open scoped MatrixGroups

@[expose] def Sec4HeCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z → IsSimpleGroup G →
    pCoreOf 2 (centralizer ({z} : Set G)) = Q →
    iX z E ⊔ iX z F = centralizer ({z} : Set G) →
    ((∀ X ∈ ({E, F} : Set (Subgroup G)),
        X ≤ iX z X ∧
        (∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
          Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X)) ∧
        ¬ iX z X ≤ normalizer (R : Set G) ∧
        Nat.card (Q ⊓ X : Subgroup G) = 16) ∧
      iX z E ⊔ iX z F ≤ normalizer (Q : Set G)) →
    (∀ X ∈ ({E, F} : Set (Subgroup G)),
      ∃ (ι : ↥X ≃* ↥hexaT) (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM),
        Function.Surjective ψ ∧
        ψ.ker = X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))) ∧
        (∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
          (y : G) = ℓ * x * (ℓ : G)⁻¹ →
            (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹) ∧
        ∀ x : ↥X, (x : G) ∈ R ↔ (ι x : Equiv.Perm (Fin 64)) ∈ hexaR0) →
    (∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) →
    Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))) →
    IsSporadic G .He

theorem step49_of''
    (h16 : Step16) (h18 : Step18) (h44 : Step44ii) (h46 : Step46) (h47 : Step47) (h48 : Step48)
    (hGold : Step49Goldschmidt) (hNX : Sec4NXModel) (hHe : Sec4HeCase) : Step49 := by
  intro G _ _ A R g E F S₁ Q z hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := hQ.setting
  have hF := hset.frame
  have hS₁C := hQ.le_centralizer
  have hQC := hQ.Q_le_centralizer
  have hG := hGold G A R g E F S₁ Q z hQ (h48 G A R g E F S₁ Q z hQ)
  have hnot := hQ.not_mem_rightConjugate h16 h44 hG
  have hcardS : Nat.card S₁ = 2 ^ (Nat.card G).factorization 2 := by
    have := hQ.sylow.card_eq
    rwa [card_top] at this
  have hzS : z ∈ S₁ := (show z ∈ centerIn S₁ by rw [hQ.center_S₁]; exact mem_zpowers z).1
  have hO1 := h18 G A R g E F hF hset.type hset.below z (hQ.z_mem_E h46) hQ.order_z
    ⟨Sylow.ofCard S₁ hcardS, by rw [Sylow.coe_ofCard]; exact hzS,
      by rw [Sylow.coe_ofCard]; exact hS₁C⟩ hnot
  rw [hO1, sup_bot_eq] at hG
  have hNC : normalizer (Q : Set G) = centralizer ({z} : Set G) :=
    le_antisymm hQ.normalizer_le_centralizer hG
  obtain ⟨⟨hQY, ψ, hψ, hψker⟩, ⟨V₁, V₂, hV₁Q, hV₂Q, hV₁, hV₂, hV₁16, -, hV12, hV12', hYV₁,
    hYV₂, hirr⟩, hiii⟩ := h47 G A R g E F S₁ Q z hQ
  rw [hNC, hO1, sup_bot_eq] at hiii hψker
  have hYC : iX z E ⊔ iX z F ≤ centralizer ({z} : Set G) :=
    sup_le ((iX_le z E).trans inf_le_left) ((iX_le z F).trans inf_le_left)
  have hcardY : Nat.card (iX z E ⊔ iX z F : Subgroup G) = Nat.card Q * 168 := by
    rw [card_eq_card_ker_mul ψ hψ, hψker, card_GL32,
      Nat.card_congr (subgroupOfEquivOfLe hQY).toEquiv]
  have hcardC : Nat.card (centralizer ({z} : Set G)) = Nat.card Q * 168 ∨
      Nat.card (centralizer ({z} : Set G)) = Nat.card Q * 336 := by
    rcases hiii with ⟨φ, hφ, hφker⟩ | ⟨φ, hφ, hφker⟩
    · left
      rw [card_eq_card_ker_mul φ hφ, hφker, card_GL32,
        Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
    · right
      rw [card_eq_card_ker_mul φ hφ, hφker, card_PGL27,
        Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
  have hY2 : (iX z E ⊔ iX z F).relIndex (centralizer ({z} : Set G)) ≤ 2 := by
    have h := Subgroup.relIndex_mul_card (iX z E ⊔ iX z F) (centralizer ({z} : Set G))
    rw [inf_eq_left.mpr hYC, hcardY] at h
    have hQ0 := Nat.card_pos (α := Q)
    rcases hcardC with hc | hc <;> rw [hc] at h <;> nlinarith
  obtain ⟨X, _, φ, hφ, hφker, hcX⟩ : ∃ (X : Type) (_ : Group X)
      (φ : ↥(centralizer ({z} : Set G)) →* X), Function.Surjective φ ∧
        φ.ker = Q.subgroupOf (centralizer ({z} : Set G)) ∧ center X = ⊥ := by
    rcases hiii with ⟨φ, hφ, hφker⟩ | ⟨φ, hφ, hφker⟩
    · exact ⟨_, _, φ, hφ, hφker, center_GL32⟩
    · exact ⟨_, _, φ, hφ, hφker, center_PGL27⟩
  have hzV : zpowers z ≤ V₁ := hV12 ▸ inf_le_left
  have hzc : ∀ q ∈ Q, q * z = z * q := fun q hq =>
    mem_centralizer_iff.mp hQ.z_mem_centerIn_Q.2 q hq
  have hcl := centralizer_le_of_quot hcX φ hφ hφker hYC hY2 ψ hψ hψker hQC hG hYC hQ.order_z
    hzc (fun q hq v hv => hQ.commutator_mem hq hv) hV₁Q hV₁ hV₁16 hzV (hirr V₁ (by simp))
  have hon := le_of_normal_of_quot hcX φ hφ hφker hYC hY2 ψ hψ hψker hQC hG
    (hQ.sylow.of_le hS₁C le_top) hQ.le
  let S : LargeExtraspecial.Setting G :=
    { z := z
      orderOf_z := hQ.order_z
      Q := Q.subgroupOf (centralizer ({z} : Set G))
      normal := (normal_subgroupOf_iff_le_normalizer hQC).mpr hG
      extraspecial := CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
        (subgroupOfEquivOfLe hQC).symm hQ.extraspecial
      centralizer_le := hcl
      le_of_normal := fun P hP h2 => hon P hP h2 }
  have hFstar : CFSG.generalizedFitting ↥(centralizer ({z} : Set G)) =
      Q.subgroupOf (centralizer ({z} : Set G)) := by
    rw [LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar]
    exact (LargeExtraspecial.Bridge.Q_eq_timmesfeldFStar S).symm
  refine ⟨by rw [hFstar, subgroupOf_map_subtype, inf_eq_left.mpr hQC], ?_⟩
  rcases hiii with ⟨φ', hφ', hφ'ker⟩ | hP
  swap
  · exact Or.inl hP
  right
  have hYeq : iX z E ⊔ iX z F = centralizer ({z} : Set G) := by
    refine Subgroup.eq_of_le_of_card_ge hYC ?_
    rw [hcardY, card_eq_card_ker_mul φ' hφ', hφ'ker, card_GL32,
      Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
  have htop := hset.rankTwoX_eq_top (h16 G A R g E F hF hset.even).1
  have hsimple : IsSimpleGroup G := by
    obtain ⟨hXF, hXs⟩ := AS76b.asc08Lemma34 G A hF.base.hyp31
    have hFt : CFSG.generalizedFitting G = ⊤ := hXF ▸ htop
    rw [hFt] at hXs
    exact Subgroup.topEquiv.symm.isSimpleGroup
  have hw : S.width = 3 := S.width_eq (by
    change Nat.card (Q.subgroupOf (centralizer ({z} : Set G))) = _
    rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ.card])
  have hQG : S.QG = Q := by
    change (Q.subgroupOf (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype = Q
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hQC]
  obtain ⟨hEI, -, -, hEQ⟩ := (h46 G A R g E F S₁ Q z hQ).1 E (by simp)
  have hEM : E ≤ centralizer ({z} : Set G) := hEI.trans ((iX_le z E).trans inf_le_left)
  have hidx : Nat.card S.M = 168 * Nat.card S.Q := by
    change Nat.card (centralizer ({z} : Set G)) =
      168 * Nat.card (Q.subgroupOf (centralizer ({z} : Set G)))
    rw [card_eq_card_ker_mul φ' hφ', hφ'ker, card_GL32, mul_comm]
  have hC := nonempty_centralizer_mulEquiv_sl5 S hw (by rw [hQG]; exact hV₁Q)
    (by rw [hQG]; exact hV₂Q) hV₁ hV₂ hV12 (by rw [hQG]; exact hV12')
    (fun m hm => hYV₁ (by rw [hYeq]; exact hm)) (fun m hm => hYV₂ (by rw [hYeq]; exact hm)) hidx
    hEM hF.elemE hF.cardE (by rw [hQG]; exact hEQ)
  have hO2 : pCoreOf 2 (centralizer ({z} : Set G)) = Q := (pCoreOf_two_eq_QG S).trans hQG
  have hS₁ : ∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P) := by
    rcases h44 G A R g E F hset S₁ hQ.sylowN with ⟨-, hP⟩ | ⟨h11, -⟩
    · exact hP
    · exfalso
      have hdvd : Nat.card S₁ ∣ Nat.card (centralizer ({z} : Set G)) := by
        have h := Subgroup.card_dvd_of_le hS₁C
        exact h
      rw [h11, card_eq_card_ker_mul φ' hφ', hφ'ker, card_GL32,
        Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQ.card] at hdvd
      norm_num at hdvd
  have hHe' := hHe G A R g E F S₁ Q z hQ hsimple hO2 hYeq (h46 G A R g E F S₁ Q z hQ)
    (hNX G A R g E F hset) hS₁ hC
  obtain ⟨e⟩ := hHe'
  exact ⟨(MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv.trans e)⟩

end CFSG.ComponentClassification.AS81
