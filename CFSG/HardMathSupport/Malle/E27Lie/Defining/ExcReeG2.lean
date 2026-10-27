module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
public import CFSG.HardMathSupport.Foote.E27.SporKill
public import CFSG.HardMathSupport.Foote.E27.SporSylowBound

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding.ReeModel CFSG.LieType.Ree TauCeti

theorem false_of_reeGamma_charThree {X : Type} [Group X] [Finite X]
    {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {a : ℕ} (ha : 1 ≤ a)
    (ψ : ↥K ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) : False := by
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨P, hP⟩ := (std_facts hK).1
  have hT : Nat.card (stdU a (GaloisField 3 (2 * a + 1))) =
      3 ^ (Nat.card (ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)).factorization 3 := by
    rw [← hP]
    exact Sylow.card_eq_multiplicity P
  have h81q : 81 ∣ (3 ^ (2 * a + 1)) ^ 2 := by
    rw [← pow_mul, show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact pow_dvd_pow 3 (by omega)
  have hprop : ∀ w ∈ stdU a (GaloisField 3 (2 * a + 1)), orderOf w = 3 →
      81 ∣ Nat.card ↥(stdU a (GaloisField 3 (2 * a + 1)) ⊓
        Subgroup.centralizer ({w} : Set ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a))) := by
    intro w hw hw3
    have hw1 : w ^ 3 = 1 := by
      have h := pow_orderOf_eq_one w
      rwa [hw3] at h
    have hwU1 : w ∈ stdU1 a (GaloisField 3 (2 * a + 1)) := mem_stdU1_of_pow_three hK hw hw1
    have hle : stdU1 a (GaloisField 3 (2 * a + 1)) ≤
        stdU a (GaloisField 3 (2 * a + 1)) ⊓
          Subgroup.centralizer ({w} : Set ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) := by
      intro u hu
      refine Subgroup.mem_inf.2 ⟨stdU1_le_stdU hK hu, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      have := ReeTag.isElementaryAbelian_smallReeU1 (a := a) (K := GaloisField 3 (2 * a + 1))
      have hc := IsMulCommutative.is_comm.comm
        (⟨(w : CFSG.Blueprint.Chevalley.ModGL ReeTag.G2.tag (GaloisField 3 (2 * a + 1))), Subgroup.mem_subgroupOf.1 hwU1⟩ :
          ↥(ReeTag.smallReeU1 a (GaloisField 3 (2 * a + 1))))
        ⟨(u : CFSG.Blueprint.Chevalley.ModGL ReeTag.G2.tag (GaloisField 3 (2 * a + 1))), Subgroup.mem_subgroupOf.1 hu⟩
      have h2 := congrArg Subtype.val hc
      apply Subtype.ext
      exact h2
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [card_stdU1 hK] at hdvd
    exact h81q.trans hdvd
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  refine h.false_of_sylow_kill hz S₀ fun s hs hs3 => Or.inl ?_
  exact dvd81_card_sylow_inf_centralizer_of_equiv ψ (stdU a (GaloisField 3 (2 * a + 1))) hT hprop
    S₀ hs hs3

@[expose] def InnerCoveredReeG2 (i : LieTypeIndex) : Prop :=
  ∃ m : ℕ, i = .reeG2 m

theorem false_of_innerCoveredReeG2 {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (d : ValidLieTypeIndex)
    (hd : InnerCoveredReeG2 d.1) (e : Nonempty (↥K ≃* (CFSGIndex.lie d).Group)) : False := by
  obtain ⟨a, ha, -, ⟨f⟩⟩ := exists_equiv_reeGamma (L := ↥K) (d := d) ⟨rfl, hd⟩ e
  exact false_of_reeGamma_charThree h hz ha f

end CFSG.HardMathSupport.Malle.E27Lie
