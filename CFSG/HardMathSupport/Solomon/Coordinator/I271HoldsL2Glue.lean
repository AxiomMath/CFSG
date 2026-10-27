module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.I271Defs202
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import Certificates.Data.ExceptionalSL3

public section

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  GL83 GL83.CompFam

namespace CFSG.HardMathSupport.Solomon.Coordinator

section Glue

variable {X : Type} [Group X] [Finite X]

theorem pRank_sub_one_le_of_card {A C E : Subgroup X} (hAel : IsElemAbelian 3 A)
    (hCE : C ≤ E) (hEA : E ≤ A) (hCE' : E ≠ C) (hAC : Nat.card A = 9 * Nat.card C) :
    CFSG.Open.pRank 3 A - 1 ≤ CFSG.Open.pRank 3 E := by
  have hCel : IsElemAbelian 3 C := elem_mono hAel (hCE.trans hEA)
  have hEel : IsElemAbelian 3 E := elem_mono hAel hEA
  obtain ⟨c, hc⟩ := exists_card_eq_pow hCel
  obtain ⟨j, hj⟩ := exists_card_eq_pow hEel
  have hA : Nat.card A = 3 ^ (c + 2) := by rw [hAC, hc]; ring
  have hlt : Nat.card C < Nat.card E := by
    by_contra h
    exact hCE' (Subgroup.eq_of_le_of_card_ge hCE (not_lt.1 h)).symm
  have hcj : c < j := by
    rw [hc, hj] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  rw [i271_pRank_eq Nat.prime_three hAel hA, i271_pRank_eq Nat.prime_three hEel hj]
  omega

theorem apply_eq_of_mem_fixSub {S : Type*} [Group S] {a : MulAut S} {s : S}
    (hs : s ∈ fixSubAut (Subgroup.zpowers a)) : a s = s := by
  unfold fixSubAut at hs
  simp only [Subgroup.mem_iInf] at hs
  exact hs a (Subgroup.mem_zpowers a)

theorem hyperplane_gen_of_plane (hP : L2FieldPlane) {K B : Subgroup X} (hBel : IsElemAbelian 3 B)
    (hS : IsLTwoTwentySeven ↥K ∨ (IsLTwoOddPow ↥K ∧ ¬ IsLTwoEight ↥K))
    (hnin : ¬ InducesInnerIn B K) (h9 : 9 ≤ autOrderIn B K) :
    K ≤ gammaPrimeIn 3 (CFSG.Open.pRank 3 (B ⊓ Subgroup.normalizer (K : Set X)) - 1)
      (B ⊓ Subgroup.normalizer (K : Set X)) K := by
  classical
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set A : Subgroup X := B ⊓ N with hA
  set C : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hC
  have hAB : A ≤ B := inf_le_left
  have hAN : A ≤ N := inf_le_right
  have hCN : Subgroup.centralizer (K : Set X) ≤ N := Subgroup.centralizer_le_normalizer _
  have hCA : C ≤ A := inf_le_inf_left _ hCN
  have hAel : IsElemAbelian 3 A := elem_mono hBel hAB
  let θ : ↥N →* MulAut ↥K := K.normalizerMonoidHom
  let Ā : Subgroup (MulAut ↥K) := (A.subgroupOf N).map θ
  have hĀel : IsElemAbelian 3 Ā :=
    CFSG.SectionRank.isElemAbelian_map (i271_isElemAbelian_subgroupOf N hAel) θ
  have hker : θ.ker = (Subgroup.centralizer (K : Set X)).subgroupOf N :=
    Subgroup.normalizerMonoidHom_ker (H := K)
  have hcardĀ : Nat.card Ā = autOrderIn B K := by
    show Nat.card ((A.subgroupOf N).map θ) = _
    rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hAN]
    rfl
  have hninĀ : ¬ Ā ≤ innerAut ↥K := by
    intro hle
    apply hnin
    intro b hb
    have hbN : b ∈ N := hb.2
    have hmem : θ ⟨b, hbN⟩ ∈ Ā := ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
    obtain ⟨k, hk⟩ := hle hmem
    refine ⟨k, k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥K => (φ ⟨y, hy⟩ : X)) hk
    simp only [MulAut.conj_apply] at h1
    have h3 : ((θ ⟨b, hbN⟩) ⟨y, hy⟩ : X) = b * y * b⁻¹ := rfl
    rw [h3] at h1
    have h2 : (k : X) * y * (k : X)⁻¹ = b * y * b⁻¹ := h1
    calc y * ((k : X)⁻¹ * b) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * b := by group
      _ = (k : X)⁻¹ * (b * y * b⁻¹) * b := by rw [h2]
      _ = (k : X)⁻¹ * b * y := by group
  obtain ⟨hle9, hgen⟩ := hP ↥K hS Ā hĀel hninĀ
  have h9' : Nat.card Ā = 9 := le_antisymm hle9 (hcardĀ ▸ h9)
  have hAut : autOrderIn B K = 9 := hcardĀ ▸ h9'
  have hAC : Nat.card A = 9 * Nat.card C := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X)) (K := A)
    have hinf : Subgroup.centralizer (K : Set X) ⊓ A = C := by
      ext x
      constructor
      · rintro ⟨hx1, hx2, hx3⟩
        exact ⟨hx2, hx1⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx2, hx1, hCN hx2⟩
    rw [hinf] at h
    have h' : autOrderIn B K = (Subgroup.centralizer (K : Set X)).relIndex A := rfl
    rw [← h', hAut] at h
    exact h.symm
  obtain ⟨a₁, ha₁, a₂, ha₂, h1, h2, h3, h4⟩ := hgen h9'
  obtain ⟨b₁, hb₁, hb₁θ⟩ := ha₁
  obtain ⟨b₂, hb₂, hb₂θ⟩ := ha₂
  have hb₁A : (b₁ : X) ∈ A := Subgroup.mem_subgroupOf.1 hb₁
  have hb₂A : (b₂ : X) ∈ A := Subgroup.mem_subgroupOf.1 hb₂
  have key : ∀ (b : ↥N) (hbA : (b : X) ∈ A) (a : MulAut ↥K), θ b = a → a ≠ 1 →
      (C ⊔ Subgroup.zpowers (b : X) ≤ A) ∧
      (CFSG.Open.pRank 3 A - 1 ≤ CFSG.Open.pRank 3 (C ⊔ Subgroup.zpowers (b : X))) ∧
      ((fixSubAut (Subgroup.zpowers a)).map K.subtype ≤
        K ⊓ Subgroup.centralizer ((C ⊔ Subgroup.zpowers (b : X) : Subgroup X) : Set X)) := by
    intro b hbA a hba ha1
    have hEA : C ⊔ Subgroup.zpowers (b : X) ≤ A :=
      sup_le hCA ((Subgroup.zpowers_le).2 hbA)
    refine ⟨hEA, ?_, ?_⟩
    · refine pRank_sub_one_le_of_card hAel le_sup_left hEA ?_ hAC
      intro hEC
      apply ha1
      have hbC : (b : X) ∈ C := by
        rw [← hEC]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      have hbker : b ∈ θ.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        exact hbC.2
      rw [← hba]
      exact hbker
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := hx
      refine ⟨s.2, ?_⟩
      have hfix : (b : X) * (s : X) * (b : X)⁻¹ = s := by
        have h5 : ((θ b) s : X) = s := by
          rw [hba]
          exact congrArg Subtype.val (apply_eq_of_mem_fixSub hs)
        exact h5
      have hle : C ⊔ Subgroup.zpowers (b : X) ≤ Subgroup.centralizer {(s : X)} := by
        apply sup_le
        · intro c hc
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hc.2 s s.2).symm
        · refine (Subgroup.zpowers_le).2 ?_
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact mul_inv_eq_iff_eq_mul.1 hfix
      show (s : X) ∈ Subgroup.centralizer ((C ⊔ Subgroup.zpowers (b : X) : Subgroup X) : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  obtain ⟨hE1A, hE1r, hE1f⟩ := key b₁ hb₁A a₁ hb₁θ h1
  obtain ⟨hE2A, hE2r, hE2f⟩ := key b₂ hb₂A a₂ hb₂θ h2
  have hK : (K : Subgroup X) ≤ (fixSubAut (Subgroup.zpowers a₁)).map K.subtype ⊔
      (fixSubAut (Subgroup.zpowers a₂)).map K.subtype := by
    rw [← Subgroup.map_sup, h4, Subgroup.map_top, Subgroup.range_subtype]
  refine hK.trans (sup_le ?_ ?_)
  · exact hE1f.trans (i224_le_gammaPrimeIn hE1A hE1r)
  · exact hE2f.trans (i224_le_gammaPrimeIn hE2A hE2r)

theorem one_le_pRank_inf_normalizer {K B : Subgroup X} (hH : I271Hyp 3 K B) :
    1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.normalizer (K : Set X)) := by
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hC : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := hH.centralized
  have hCA : B ⊓ Subgroup.centralizer (K : Set X) ≤ B ⊓ Subgroup.normalizer (K : Set X) :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) := elem_mono hBel inf_le_left
  obtain ⟨j, hj⟩ := exists_card_eq_pow hCel
  have hj1 : 1 ≤ j := by
    by_contra h0
    have : j = 0 := by omega
    rw [this, pow_zero] at hj
    exact hC (Subgroup.eq_bot_of_card_eq _ hj)
  exact hj1.trans (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hCA hCel hj)

end Glue

end CFSG.HardMathSupport.Solomon.Coordinator
