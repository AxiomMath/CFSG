module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L51Final
public import CFSG.CGT.PushingUpLit.LIT.Foote.Shapes
public import CFSG.CGT.PushingUpLit.LIT.Foote.Blocks2

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement Hyp3 Thm3Conclusion
  SylowFrame oTwoPrime IsQuaternionTwoGroup IsDihedralTwoGroup)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure relative_weak_closure_le)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoIn_eq_pCoreOf' (E : Subgroup G) : oTwoIn E = CFSG.Open.pCoreOf 2 E := by
  unfold oTwoIn CFSG.Open.pCoreOf inSubgroup
  show Subgroup.map E.subtype (CFSG.pCore 2 ↥E) = Subgroup.map E.subtype (CFSG.Open.pCore 2 ↥E)
  try with_reducible rfl

namespace QBlock

variable {K : Subgroup G}

theorem false_of_relIndex_two (h : QBlock K) {S T W : Subgroup G}
    (hSK : IsSylowOf 2 S (K ⊔ T)) (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hWS : W ≤ S)
    (hWnorm : K ⊔ T ≤ Subgroup.normalizer (W : Set G)) (hidx : W.relIndex S = 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKT : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hB : IsSylowOf 2 (S ⊓ K) K := IsSylowOf.inf_of_le_normalizer hSK le_sup_left hKT
  have hO2 : IsPGroup 2 (oTwoIn K) := SixThree.isPGroup_oTwoIn K
  have hOB : oTwoIn K ≤ S ⊓ K :=
    le_of_isPGroup_normal' hB (oTwoIn_le K) (SixThree.le_normalizer_oTwoIn K) hO2
  have hW2 : IsPGroup 2 W := hSK.isPGroup.to_le hWS
  have hWKO : W ⊓ K ≤ oTwoIn K := by
    refine SixThree.le_oTwoIn_of_isPGroup inf_le_right (hW2.to_le inf_le_left) ?_
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hW := Subgroup.mem_normalizer_iff.1 (hWnorm (Subgroup.mem_sup_left hk)) y
    have hK' := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hk : k ∈
      Subgroup.normalizer (K : Set G)) y
    exact ⟨fun hy => ⟨hW.1 hy.1, hK'.1 hy.2⟩, fun hy => ⟨hW.2 hy.1, hK'.2 hy.2⟩⟩
  have h4 := h.four_mul_card_le_sylow hB
  have hcard := Subgroup.relIndex_mul_card W (S ⊓ K)
  have hle : W.relIndex (S ⊓ K) ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := W) (K := S ⊓ K) (L := S) inf_le_left
      (by rw [hidx]; norm_num)
    rwa [hidx] at this
  have hWB : Nat.card ↥(W ⊓ (S ⊓ K)) ≤ Nat.card ↥(oTwoIn K) := by
    refine Subgroup.card_le_of_le ?_
    exact (inf_le_inf_left W inf_le_right).trans hWKO
  have hpos : 0 < Nat.card ↥(oTwoIn K) := Nat.card_pos
  have h5 : Nat.card ↥(S ⊓ K) ≤ 2 * Nat.card ↥(oTwoIn K) := by
    rw [← hcard]
    exact Nat.mul_le_mul hle hWB
  omega

end QBlock

theorem lemma_5_1 (h3 : Theorem3Statement) {K T P S : Subgroup G} (hK : QBlock K) (hT : T ≠ ⊥)
    (hfr : SylowFrame K T S) (hP : IsSylowOf 2 T P) (hPK : P ≤ K ⊔ T)
    (htight : TightlyEmbedded (P.subgroupOf (K ⊔ T)))
    (hidx : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T) : ⁅T, K⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKT : K ⊔ T ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hfr.le_normalizer
  have hHyp : Hyp3 K T P S := ⟨hT, hfr, hP, hPK, htight, hidx, hK.oddCore_eq_bot⟩
  have hconc := h3 G K T P S hHyp
  by_contra hne
  rcases hconc with ⟨-, hshape, -⟩ | h2 | ⟨n, -, -, hinf, -⟩ |
    ⟨x, hx, hWdef, hTx, hcomm, hWN, hWnorm, hTab, -⟩ | ⟨hWnorm, -, -, -, -, -, hidx2⟩
  ·
    have hB : IsSylowOf 2 (S ⊓ K) K := IsSylowOf.inf_of_le_normalizer hfr.sylow le_sup_left hKT
    have hUB : blockU K ≤ S ⊓ K :=
      QBlock.le_of_isPGroup_normal' hB (blockU_le K) (le_normalizer_blockU K) hK.isPGroup_blockU
    exact hK.not_shape hUB hshape hB.isPGroup
  ·
    apply hne
    refine le_bot_iff.1 ((Subgroup.commutator_le.2 fun t ht k hk => ?_).trans le_rfl)
    have h1 : k * t⁻¹ * k⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 (h2 (Subgroup.mem_sup_left hk)) t⁻¹).1 (T.inv_mem ht)
    have h2' : t * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hfr.le_normalizer ht) k).1 hk
    have h3' : ⁅t, k⁆ ∈ T ⊓ K := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have : ⁅t, k⁆ = t * (k * t⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
        rw [this]
        exact T.mul_mem ht h1
      · rw [commutatorElement_def]
        exact K.mul_mem h2' (K.inv_mem hk)
    rw [hfr.inf_eq_bot] at h3'
    exact h3'
  ·
    have hO2 : IsPGroup 2 (oTwoIn K) := SixThree.isPGroup_oTwoIn K
    have hle1 : oTwoIn K ≤ oTwoIn (K ⊔ T) :=
      SixThree.le_oTwoIn_of_isPGroup (le_sup_left.trans' (oTwoIn_le K)) hO2
        (hKT.trans (SixThree.normalizer_le_normalizer_oTwoIn K))
    have hle2 : oTwoIn K ≤ oTwoPrime K := by
      intro y hy
      refine Subgroup.subset_closure ⟨oTwoIn_le K hy, ?_⟩
      obtain ⟨k, hk⟩ := hO2 ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hle1' : oTwoIn K ≤ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
      rw [← oTwoIn_eq_pCoreOf']
      exact hle1
    have hbot : oTwoIn K ≤ ⊥ := hinf ▸ le_inf hle1' hle2
    exact blockU_ne_bot_of_short hK.short (le_bot_iff.1 ((blockU_le_oTwoIn K).trans hbot))
  ·
    have hcomm' : ∀ a ∈ T, ∀ b ∈ rightConjugate T x, a * b = b * a := by
      intro a ha b hb
      have : T ≤ Subgroup.centralizer (rightConjugate T x : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
      exact (Subgroup.mem_centralizer_iff.1 (this ha) b hb).symm
    have hTab' : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hTab.is_comm.comm (⟨a, ha⟩ : ↥T) ⟨b, hb⟩)
    exact (Case4.mk hK hfr.le_normalizer hfr.inf_eq_bot hP hPK htight hfr.sylow
      hfr.sylow_normalizer hx hWdef hTx hcomm' hWN hWnorm hTab').false_of_ne hne
  ·
    exact hK.false_of_relIndex_two hfr.sylow hfr.le_normalizer
      (relative_weak_closure_le K T S) hWnorm hidx2

end CFSG.CGT.PushingUpLit.LIT.Foote
