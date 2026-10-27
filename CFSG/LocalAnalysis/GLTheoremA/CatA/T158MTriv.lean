module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K156Norm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Basic

variable {X : Type} [Group X] [Finite X] {p : ℕ} {K B : Subgroup X} {x₁ x₂ : X} {L₁ L₂ : Subgroup X}

theorem t158m_unpack (h : T158Hyp p K B x₁ x₂ L₁ L₂) :
    GLAPComponent p (⊤ : Subgroup X) K ∧ IsElemAbelian p B ∧ x₁ ∈ B ∧ x₂ ∈ B ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧
      GLAPComponent p (K ⊓ Subgroup.centralizer ({x₁} : Set X)) L₁ ∧ IsChevSimple 2 (PSimple p L₁) ∧
      GLAPComponent p (K ⊓ Subgroup.centralizer ({x₂} : Set X)) L₂ ∧ IsChevSimple 2 (PSimple p L₂) ∧
      FGOn p x₁ L₂ ∧ FGOn p x₂ L₁ := by
  obtain ⟨⟨hKG, hK, hBel, hBX, hrk, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2⟩, hn12, hn21⟩ := h.hyp
  exact ⟨hK, hBel, hx1B, hx2B, hx1, hx2, hL1, hc1, hL2, hc2, hn12, hn21⟩

theorem t158m_fgOn_normalizer {g : X} {L : Subgroup X} (h : FGOn p g L) :
    g ∈ Subgroup.normalizer (L : Set X) := by
  rcases h with ⟨hN, -⟩ | ⟨⟨hN, -⟩, -, -⟩
  · exact hN
  · exact hN

theorem t158m_normalizer (h : T158Hyp p K B x₁ x₂ L₁ L₂) :
    x₁ ∈ Subgroup.normalizer (K : Set X) ∧ x₂ ∈ Subgroup.normalizer (K : Set X) := by
  obtain ⟨hK, -, -, -, -, -, hL1, -, hL2, -, hn12, hn21⟩ := t158m_unpack h
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalAnalysis.GLTheoremA.K156.normalizer_of_normalizes_component h.prime hK
      (Subgroup.mem_top _) (inf_le_left.trans hK.1) inf_le_left hL2 (t158m_fgOn_normalizer hn12)
  · exact CFSG.LocalAnalysis.GLTheoremA.K156.normalizer_of_normalizes_component h.prime hK
      (Subgroup.mem_top _) (inf_le_left.trans hK.1) inf_le_left hL1 (t158m_fgOn_normalizer hn21)

theorem t158m_pow (h : T158Hyp p K B x₁ x₂ L₁ L₂) : x₁ ^ p = 1 ∧ x₂ ^ p = 1 := by
  obtain ⟨-, hBel, hx1B, hx2B, -⟩ := t158m_unpack h
  exact ⟨hBel.2 x₁ hx1B, hBel.2 x₂ hx2B⟩

theorem t158m_elemAbelian_zpowers {G : Type} [Group G] {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hm, ← hn]
    exact ((Commute.refl x).zpow_zpow m n).eq
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem t158m_centralizer_zpowers {G : Type} [Group G] (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hg
    exact hg x (Subgroup.mem_zpowers x)
  · intro hg z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (show Commute x g from hg) m).eq

theorem t158m_fixSubgroup_one {S : Type} [Group S] : fixSubgroup (1 : MulAut S) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

end Basic

theorem t158m_falseOn_cyc : T158FalseOn t158FamCyc := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hh
  obtain ⟨hK, -⟩ := t158m_unpack hh
  obtain ⟨-, c, d, hcd⟩ := chev_pSimple_simple_nonabelian hh.prime hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | cyclic r hr =>
    apply hcd
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T158

end
