module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Design
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

namespace Prop1116Design

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_eq_of_zpowers {a : G} {L : Subgroup G} (hL : GLBConj a L = L) {g : G}
    (hg : g ∈ Subgroup.zpowers a) : GLBConj g L = L := by
  have ha : a ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hL] at hx
      exact mem_gLBConj.1 hx
    · intro hx
      rw [← hL]
      exact mem_gLBConj.2 hx
  exact gLBConj_eq_of_mem_normalizer ((Subgroup.zpowers_le.mpr ha) hg)

theorem gLBConj_pow_cycle {p : ℕ} [Fact p.Prime] {a : G} {L : ZMod p → Subgroup G}
    (hL : ∀ i, GLBConj a (L i) = L (i + 1)) (k : ℕ) : GLBConj (a ^ k) (L 0) = L (k : ZMod p) := by
  induction k with
  | zero => simp [gLBConj_one]
  | succ k ih =>
    rw [pow_succ, ← gLBConj_gLBConj, ih, hL]
    simp

theorem exists_J1_of_input18_3 (hI : Prop115.Input18_3Gen) {m p : ℕ} {B M E A : Subgroup G}
    (h : Sec11 G m p B M E A) {a e : G} (ha : a ∈ A) (ha1 : a ≠ 1) (he : e ∈ E ⊓ A) (he1 : e ≠ 1)
    {J0 : Subgroup G} (hJ0 : GLAPComponent p (Cg2 e a) J0) :
    ∃ J1 : Subgroup G, GLAPComponent p (Cg e) J1 ∧
      Kx p J0 e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J1 := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hAel : IsElemAbelian p A := sec11_isElemAbelian_A h
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have hae : a * e = e * a := elemAbelian_comm hAel ha heA
  have hordA : orderOf a = p := orderOf_eq_prime (hAel.2 a ha) ha1
  have hordE : orderOf e = p := orderOf_eq_prime (hAel.2 e heA) he1
  have hJ0' : GLAPComponent p (Subgroup.centralizer ({a, e} : Set G)) J0 := by
    have : ({a, e} : Set G) = {e, a} := Set.pair_comm a e
    rw [this]
    exact hJ0
  rcases hI p hp hS.ne_two G hS.simple hS.nonabelian hS.kProper a e hordA hordE hae J0 hJ0' with
    ⟨L, hL, hKx, haL⟩ | ⟨L, hL, hinj, hcyc, hKx⟩
  · refine ⟨L, hL, ?_⟩
    change (⨆ g ∈ GLAPLayer p (Cg e), GLBConj g J0) = _
    rw [hKx]
    apply le_antisymm
    · exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (le_of_eq (gLBConj_one L).symm)
    · exact iSup₂_le fun g hg => le_of_eq (gLBConj_eq_of_zpowers haL hg)
  · refine ⟨L 0, hL 0, ?_⟩
    change (⨆ g ∈ GLAPLayer p (Cg e), GLBConj g J0) = _
    rw [hKx]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      have h1 := gLBConj_pow_cycle hcyc i.val
      rw [ZMod.natCast_zmod_val] at h1
      rw [← h1]
      exact le_iSup₂_of_le (a ^ i.val) (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _) le_rfl
    · refine iSup₂_le fun g hg => ?_
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g a).1 ((mem_powers_iff_mem_zpowers).2 hg)
      rw [← hn, gLBConj_pow_cycle hcyc n]
      exact le_iSup L _

end Prop1116Design

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
