module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.HardMathSupport.Solomon.LocalBalance.FStarTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

theorem le_normalizer_gLADelta [Finite G] {p : ℕ} {B D : Subgroup G} (hB : IsElemAbelian p B)
    (hDB : D ≤ B) : B ≤ Subgroup.normalizer (GLADelta p D : Set G) := by
  have hconj : ∀ e ∈ B, ∀ w ∈ GLADelta p D, e * w * e⁻¹ ∈ GLADelta p D := by
    intro e he w hw
    simp only [GLADelta, Subgroup.mem_iInf] at hw ⊢
    intro d hd hd1
    have hec : e ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact elemAbelian_comm hB (hDB hd) he
    exact mem_gLAPPrimeCoreOf_conj (hw d hd hd1) hec
  exact fun e he => Subgroup.mem_normalizer_fintype fun n hn => hconj e he n hn

theorem delta2At_le_gLADelta [Finite G] {p : ℕ} {B D : Subgroup G} (hB : IsElemAbelian p B)
    (hDB : D ≤ B) (b : G) : delta2At p B D b ≤ GLADelta p D := by
  have hN := le_normalizer_gLADelta hB hDB
  refine Subgroup.commutator_le.2 fun w hw e he => ?_
  have h1 : e * w⁻¹ * e⁻¹ ∈ GLADelta p D :=
    (Subgroup.mem_normalizer_iff.1 (hN he) w⁻¹).1 ((GLADelta p D).inv_mem hw.1)
  have h2 := (GLADelta p D).mul_mem hw.1 h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using h2

theorem isElemAbelian_map {p : ℕ} {H : Type*} [Group H] {A : Subgroup G} (hA : IsElemAbelian p A)
    (f : G →* H) : IsElemAbelian p (A.map f) := CFSG.SectionRank.isElemAbelian_map hA _

theorem isPGroup_autBar {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B) (L : Subgroup G) :
    IsPGroup p (autBar p B L) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨y, hy, hyx⟩ := x.2
  rw [pow_one]
  apply Subtype.ext
  show (x : MulAut (barOf p L)) ^ p = 1
  rw [← hyx, ← map_pow]
  have hy' : (y : G) ∈ B := (Subgroup.mem_subgroupOf.1 hy).1
  have : y ^ p = 1 := by
    apply Subtype.ext
    show (y : G) ^ p = 1
    exact hB.2 _ hy'
  rw [this, map_one]

theorem two_pow_mod_nine {n : ℕ} (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    2 ^ n % 9 = 2 ∨ 2 ^ n % 9 = 5 := by
  have h6 : n % 6 = 1 ∨ n % 6 = 5 := by omega
  have key : ∀ k : ℕ, 2 ^ (6 * k + 1) % 9 = 2 ∧ 2 ^ (6 * k + 5) % 9 = 5 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      constructor
      · have : 2 ^ (6 * (k + 1) + 1) = 64 * 2 ^ (6 * k + 1) := by ring
        omega
      · have : 2 ^ (6 * (k + 1) + 5) = 64 * 2 ^ (6 * k + 5) := by ring
        omega
  obtain ⟨k, hk⟩ : ∃ k, n = 6 * k + 1 ∨ n = 6 * k + 5 :=
    ⟨n / 6, by omega⟩
  rcases hk with rfl | rfl
  · exact Or.inl (key k).1
  · exact Or.inr (key k).2

theorem IsSUThreeTwoPow.isSUThreeExc {X : Type*} [Group X] (h : IsSUThreeTwoPow X) :
    IsSUThreeExc X := by
  obtain ⟨K, _, _, n, h2, -, h3, hK, ⟨e⟩⟩ := h
  refine ⟨K, inferInstance, inferInstance, 2 ^ n, hK, ?_, ⟨e⟩⟩
  exact two_pow_mod_nine h2 h3

theorem isElemAbelian_subgroupOf {p : ℕ} {B C : Subgroup G} (hB : IsElemAbelian p B) :
    IsElemAbelian p (B.subgroupOf C) := CFSG.Open.IsElemAbelian.subgroupOf hB C

theorem lemma24_of_inputs (h23 : Lemma23) (h1910 : Input19_10) (h193 : Input19_3_1)
    (h112 : Input11_2Full) (h195 : Input19_5_2) : Lemma24 := by
  intro G _ _ m p hS B hB hnwb D hD b hb hb1 hX
  have := hS.simple
  have hp : p.Prime := hS.prime
  have hBel : IsElemAbelian p B := hB.1.1
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := le_centralizer_of_mem hBel hb
  have hCne : C ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hb1
  have hrk : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p B :=
    (glaTwoLocalRank_subgroup_le hp C).trans (hS.rank_eq.le.trans (hS.le_pRank' hB))
  have h2rk : 2 ≤ CFSG.Open.pRank p B :=
    le_trans (by have := hS.four_le; omega) (hS.le_pRank' hB)
  have hweak : ∀ L, GLAPComponent p C L → IsCompWeaklyLocallyBalanced p 2 B L := fun L hL =>
    (h1910 G hS.nonabelian hS.kProper p hp hS.ne_two C hCne B hBC hBel hrk L hL).2.1 h2rk
  have h193' := h193 G hS.nonabelian hS.kProper p hp B hBel 2 (by norm_num) D hD b hb hb1 hweak
  have hDne : D ≠ ⊥ := by
    intro h
    have h1 := hD.2.2
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hXle : delta2At p B D b ≤ GLADelta p D := delta2At_le_gLADelta hBel hD.1 b
  have hXC : delta2At p B D b ≤ C := by
    refine Subgroup.commutator_le.2 fun w hw e he => ?_
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hw.2 (hBC he)) (C.inv_mem hw.2)) (C.inv_mem (hBC he))
  have hXcop : Nat.Coprime p (Nat.card (delta2At p B D b)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXle)
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp hDne)
  have hexL : ∃ L : Subgroup G, GLAPComponent p C L ∧ ¬ ⁅L, delta2At p B D b⁆ ≤ GLAPPrimeCoreOf p C := by
    by_contra hno
    push Not at hno
    exact hX (le_gLAPPrimeCoreOf_of_centralizes_layer hp hXC hXcop h193'.1.1 hno)
  obtain ⟨L₀, hL₀, hnc₀⟩ := hexL
  have hp3 : p = 3 :=
    (h112 G m p hS C B L₀ hBel hBC hrk hL₀ (h193'.2 L₀ hL₀ hnc₀).2.2.1).1
  subst hp3
  refine ⟨rfl, ⟨L₀, hL₀, hnc₀⟩, ?_⟩
  intro L hsetup
  have hcomp := hsetup.isComp
  have h193b := h193'.2 L hcomp hsetup.not_centralizes
  have h112' := h112 G m 3 hS C B L hBel hBC hrk hcomp h193b.2.2.1
  obtain ⟨-, hidx, -, hZ, hcases⟩ := h112'
  refine ⟨hidx, ?_, ⟨h193b.2.2.2.1, h193'.1.2 L hcomp, h193b.2.2.2.2⟩, hZ, ?_⟩
  · have hq := isQuasisimple_quotient_of_glaPComponent hcomp
    have hbal : ¬ IsCompLocallyBalanced 3 2 B L := h193b.1
    have hA := isPGroup_autBar hBel L
    rcases hcases with h | h | h | h | h | h | h
    · exact absurd (h195 _ hq (Or.inl h) _ hA) hbal
    · exact absurd (h195 _ hq (Or.inr (Or.inl h)) _ hA) hbal
    · exact absurd (h195 _ hq (Or.inr (Or.inr (Or.inl h))) _ hA) hbal
    · exact absurd (h195 _ hq (Or.inr (Or.inr (Or.inr h))) _ hA) hbal
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h.isSUThreeExc
  · intro z ⟨hz1, hz2⟩
    obtain ⟨w, hw, rfl⟩ := hz1
    have hz3 : ((w : ↥(barImageAt 3 b (bClosure B L))) : CBar 3 b) ^ 3 = 1 := by
      have h := hZ.1.2 w hw
      exact congrArg Subtype.val h
    have hBbar : IsElemAbelian 3 (barImageAt 3 b B) :=
      isElemAbelian_map (isElemAbelian_subgroupOf hBel) _
    have hcomm : ∀ a ∈ barImageAt 3 b B, a * (w : CBar 3 b) = (w : CBar 3 b) * a := fun a ha =>
      (Subgroup.mem_centralizer_iff.1 hz2 a ha)
    have hE := isElemAbelian_sup_zpowers hBbar hz3 hcomm
    have heq := eq_barX_of_isSCp hp hBC (h23 G m 3 hS B hB) hE le_sup_left
    have : (w : CBar 3 b) ∈ barX 3 C B := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact this

end CFSG.HardMathSupport.Solomon.LocalBalance
