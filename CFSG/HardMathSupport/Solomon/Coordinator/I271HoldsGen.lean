module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.HardMathSupport.Solomon.Coordinator.C25ON
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Complement

variable {X : Type} [Group X] [Finite X]

theorem i271h_exists_faithful_complement {r : ℕ} {B K : Subgroup X}
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hr : autOrderIn B K = 3 ^ r) :
    ∃ B₁ : Subgroup X, B₁ ≤ B ∧ B₁ ⊓ (B ⊓ Subgroup.centralizer (K : Set X)) = ⊥ ∧
      Nat.card B₁ = 3 ^ r := by
  obtain ⟨B₁, hB₁B, hdisj, hsup⟩ :=
    SignalizerFunctorTheorem.McBride.Near.Lemma212.exists_complement_of_isElemAbelian
      Nat.prime_three hBel (inf_le_left : B ⊓ Subgroup.centralizer (K : Set X) ≤ B)
  have hcard := SignalizerFunctorTheorem.card_mul_card_complement hBel inf_le_left hB₁B hdisj hsup
  have hrel := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X)) (K := B)
  rw [← i271h_autOrderIn_eq_relIndex hBN, hr, inf_comm] at hrel
  refine ⟨B₁, hB₁B, by rw [inf_comm]; exact hdisj, ?_⟩
  have hpos : 0 < Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := Nat.card_pos
  have : Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) * Nat.card B₁ =
      Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) * 3 ^ r := by
    rw [hcard, ← hrel, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem i271h_isInGOne_of_generation {r : ℕ} {B K B₁ : Subgroup X}
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hr : autOrderIn B K = 3 ^ r) (hB₁B : B₁ ≤ B)
    (hdisj : B₁ ⊓ (B ⊓ Subgroup.centralizer (K : Set X)) = ⊥)
    (hm : r + 2 ≤ CFSG.Open.pRank 3 B)
    (hgen : K ≤ ⨆ (e : X) (_ : e ∈ B₁) (_ : e ≠ 1), K ⊓ Subgroup.centralizer ({e} : Set X)) :
    IsInGOne 3 B K := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  set C : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hC
  have hCB : C ≤ B := inf_le_left
  have hCel : IsElemAbelian 3 C := i271_isElemAbelian_of_le hBel hCB
  have hC2 : 2 ≤ CFSG.Open.pRank 3 C := by
    have := pRank_le_centralizer_add hp hBel hBN (r := r) (hr ▸ le_rfl)
    rw [← hC] at this
    omega
  obtain ⟨j, hj⟩ := i271_exists_card_eq hp hCel
  have hjr : CFSG.Open.pRank 3 C = j := i271_pRank_eq hp hCel hj
  refine i271h_isInGOne_of_le hBN (hgen.trans (iSup_le fun e => iSup_le fun he => iSup_le fun hne => ?_))
  set Q : Subgroup X := Subgroup.zpowers e ⊔ C with hQ
  have heB : e ∈ B := hB₁B he
  have he3 : e ^ 3 = 1 := hBel.2 e heB
  have heC : e ∈ Subgroup.centralizer (C : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact CFSG.Open.IsElemAbelian.comm hBel (hCB hc) heB
  have hQel : IsElemAbelian 3 Q := c25_isElemAbelian_sup_zpowers hCel he3 heC
  have hzB : Subgroup.zpowers e ≤ B := Subgroup.zpowers_le.2 heB
  have hzB₁ : Subgroup.zpowers e ≤ B₁ := Subgroup.zpowers_le.2 he
  have hzdisj : Subgroup.zpowers e ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ B₁ ⊓ C := ⟨hzB₁ hx.1, hx.2⟩
    rw [hdisj] at this
    exact this
  have hzcard : Nat.card (Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 hne]
  have hQcard : Nat.card Q = 3 ^ (j + 1) := by
    rw [hQ, SignalizerFunctorTheorem.card_sup_of_le_elemAbelian hBel hzB hCB hzdisj, hzcard, hj,
      pow_succ, mul_comm]
  have hQrank : j + 1 ≤ CFSG.Open.pRank 3 Q :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hQel hQcard
  have hQB : Q ≤ B := sup_le hzB hCB
  refine i271h_le_coreIn_of_le_centralizer (E := Q) hQB (by omega) ?_
  intro s hs
  refine ⟨hs.1, ?_⟩
  have hs2 : s ∈ Subgroup.centralizer ({e} : Set X) := hs.2
  have hQs : Q ≤ Subgroup.centralizer ({s} : Set X) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hs2).symm
    · intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hc.2 s hs.1).symm
  refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
  exact Subgroup.mem_centralizer_singleton_iff.1 (hQs hq)

end Complement

end CFSG.HardMathSupport.Solomon.Coordinator
