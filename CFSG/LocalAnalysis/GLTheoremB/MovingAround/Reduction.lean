module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

section Glue
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem eq_of_le_plane [Fact p.Prime] {X Y D : Subgroup G} (hD : IsPPlane p D)
    (hY : IsNoncyclicElemAbelianIn p X Y) (hYD : Y ≤ D) : Y = D := by
  have hp : p.Prime := Fact.out
  refine Subgroup.eq_of_le_of_card_ge hYD ?_
  rw [hD.2]
  have hdvd : Nat.card Y ∣ p ^ 2 := hD.2 ▸ Subgroup.card_dvd_of_le hYD
  obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  rw [hi]
  refine Nat.pow_le_pow_right hp.pos ?_
  by_contra hlt
  apply hY.2.2
  interval_cases i
  · have : Subsingleton Y := (Nat.card_eq_one_iff_unique.1 (by simpa using hi)).1
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (p := p) (by simpa using hi)


theorem exists_elemAbelian_above_of_isTwoConnectedIn [Fact p.Prime] {M D B : Subgroup G}
    (hD : IsPPlane p D) (hB3 : p ^ 3 ≤ Nat.card B) (hconn : IsTwoConnectedIn p M D B) :
    ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian p E ∧ D ≤ E ∧ p ^ 3 ≤ Nat.card E := by
  have hp : p.Prime := Fact.out
  obtain ⟨hDnc, -, hchain⟩ := hconn
  suffices h : ∀ X : Subgroup G, Relation.ReflTransGen (IsConnectingStep p M) X B → X ≤ D →
      ∃ E : Subgroup G, E ≤ M ∧ IsElemAbelian p E ∧ D ≤ E ∧ p ^ 3 ≤ Nat.card E from
    h D hchain le_rfl
  intro X hX
  induction hX using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hBD
    have h1 := Subgroup.card_le_of_le hBD
    rw [hD.2] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  | head hXY hYB ih =>
    rename_i X Y
    intro hXD
    by_cases hYD : Y ≤ D
    · exact ih hYD
    · have hXeq : X = D := eq_of_le_plane hD hXY.1 hXD
      subst hXeq
      obtain ⟨-, hYnc, hXC⟩ := hXY
      have hEel : IsElemAbelian p (X ⊔ Y) := isElemAbelian_sup_of_commute hD.1 hYnc.2.1 hXC
      refine ⟨X ⊔ Y, sup_le hDnc.1 hYnc.1, hEel, le_sup_left, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card (X ⊔ Y : Subgroup G) = p ^ k :=
        exists_card_eq_pow (fun x => ⟨1, Subtype.ext (by simpa using hEel.2 x x.2)⟩)
      have hdvd : p ^ 2 ∣ p ^ k := hk ▸ hD.2 ▸ Subgroup.card_dvd_of_le (le_sup_left : X ≤ X ⊔ Y)
      have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
      have hne : k ≠ 2 := by
        rintro rfl
        have := Subgroup.eq_of_le_of_card_ge (le_sup_left : X ≤ X ⊔ Y) (by rw [hk, hD.2])
        exact hYD (this ▸ (le_sup_right : Y ≤ X ⊔ Y))
      rw [hk]
      exact Nat.pow_le_pow_right hp.pos (by omega)


theorem exists_isSCstar_above [Fact p.Prime] {M E : Subgroup G} (hEM : E ≤ M)
    (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E) :
    ∃ A : Subgroup G, IsSCstar p M A ∧ E ≤ A := by
  have hp : p.Prime := Fact.out
  obtain ⟨A, hEA, hAmax⟩ :=
    (Set.toFinite {X : Subgroup G | X ≤ M ∧ IsElemAbelian p X}).exists_le_maximal
      (show E ∈ {X : Subgroup G | X ≤ M ∧ IsElemAbelian p X} from ⟨hEM, hE⟩)
  refine ⟨A, ⟨⟨hAmax.1.1, hAmax.1.2, fun E' hE'M hE' hAE' =>
    le_antisymm (hAmax.2 ⟨hE'M, hE'⟩ hAE') hAE'⟩, ?_⟩, hEA⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.card E = p ^ k :=
    exists_card_eq_pow (fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩)
  have h3 : 3 ≤ k := by
    rw [hk] at hE3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hE3
  exact h3.trans (CFSG.SectionRank.le_pRank hp.one_lt hEA hE hk)


theorem exists_sylowIn_above {X P : Subgroup G} (hPX : P ≤ X) (hP : IsPGroup p ↥P) :
    ∃ Q : Subgroup G, IsSylowIn p X Q ∧ P ≤ Q := by
  obtain ⟨Q, hPQ, hQmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ X ∧ IsPGroup p ↥R}).exists_le_maximal ⟨hPX, hP⟩
  exact ⟨Q, ⟨hQmax.1.1, hQmax.1.2, fun R' hR'X hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'X, hR'p⟩ hQR') hQR'⟩, hPQ⟩


end Glue


theorem theoremTwo_of_theoremTwoStar (h98 : Prop98) (hstar : TheoremTwoStar) : TheoremTwo := by
  intro G _ _ _ hnonab hK hchar he m hm ha p hp hrank hΔ B M hB hMmax hΛ hΓ
  have hS : GLStanding G m p := ⟨inferInstance, hnonab, hK, hchar, he, hm, ha, hp, hrank, hΔ⟩
  have hM : IsPreUniquenessTwoLocal p B M := ⟨hMmax, hΛ, hΓ⟩
  rcases hstar G m p hS B M hB hM (h98 G m p hS B M hB hM).1 with h | h
  · exact Or.inl h
  · refine Or.inr ⟨gammaStar p, fun D hD => ⟨isPGroup_gammaStar p D,
      fun g => gammaStar_gLBConj p g D, fun _ hconn => ?_⟩⟩
    have : Fact p.Prime := ⟨hS.prime⟩
    have hB3 : p ^ 3 ≤ Nat.card B := by
      rw [hS.card_eq hB]
      exact Nat.pow_le_pow_right hS.prime.pos (by have := hS.four_le; omega)
    obtain ⟨E, hEM, hE, hDE, hE3⟩ := exists_elemAbelian_above_of_isTwoConnectedIn hD hB3 hconn
    obtain ⟨A, hA, hEA⟩ := exists_isSCstar_above hEM hE hE3
    obtain ⟨hc1, hc2⟩ := (h A hA).clause_c D (hDE.trans hEA) hD
    exact ⟨hc1, Subgroup.le_normalizer.trans (hc2 _ hc1 le_rfl), hc2⟩


theorem movingAround_of_theoremTwoStar (hstar : Prop98 → TheoremTwoStar) :
    CFSG.Yardstones.M67c2c3e09a6b.MovingAround :=
  fun h98 => theoremTwo_of_theoremTwoStar h98 (hstar h98)


section Sec10Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G}
theorem lemma101_iii (h : Sec10Fails G m p B M) : ∃ F : Subgroup G, inDp p M F := by
  obtain ⟨A, hA, hn⟩ := h.notStar
  exact ⟨A, hA, hn⟩


theorem lemma104_exists (h : MovingAroundLeaves) (hs : Sec10Fails G m p B M) : ∃ E A : Subgroup G, IsDDpStar p M E A := by
  classical
  obtain ⟨E0, A0, h0⟩ := h.lemma103 hs
  let S : Set (Subgroup G × Subgroup G) := {x | inDDp p M x.1 x.2}
  have hfin : S.Finite := Set.toFinite S
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image S (fun x => ddKey p x.1 x.2) hfin ⟨(E0, A0), h0⟩
  exact ⟨x.1, x.2, hx, fun E' A' h' => hmax (E', A') h'⟩


end Sec10Statements

section Sec11Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
theorem lemma113_ii (h : MovingAroundLeaves) (hs : Sec11 G m 3 B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hna : ¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1) (h4 : CFSG.Open.pRank 3 E = 4) (h3 : CFSG.Open.pRank 3 A = 3) :
    ∀ e ∈ E ⊓ A, e ≠ 1 → ∀ K : Subgroup G, GLAPComponent 3 (Cg e) K →
      ¬ IsLTwoTwentySeven (barOf 3 K) := by
  intro e he he1 K hK hL
  have hp4 : IsPGroup 3 ↥(E ⊔ A) := h.lemma104_i hs.toSec10Fails hs.pair
  have hEA : E ⊔ A ≤ Cg e := by
    have hee : e ∈ E := (Subgroup.mem_inf.1 he).1
    have hea : e ∈ A := (Subgroup.mem_inf.1 he).2
    have hEc : IsMulCommutative E := hs.pair.1.1.1.1.2.1.1
    have hAc : IsMulCommutative A := hs.pair.1.2.1.1.1.2.1.1
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact congrArg Subtype.val (hEc.is_comm.comm ⟨e, hee⟩ ⟨x, hx⟩)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact congrArg Subtype.val (hAc.is_comm.comm ⟨e, hea⟩ ⟨x, hx⟩)
  obtain ⟨Q, hQ⟩ := exists_sylowIn_above hEA hp4
  have hcfg : Cfg113 G m B M E A a e K Q :=
    ⟨hs, ⟨ha, ha1⟩, hna, h4, h3, ⟨he, he1⟩, ⟨hK, hL⟩, hQ⟩
  have h0 := h.lemma113_ii_piece0 hcfg
  have hA := h.lemma113_ii_pieceA hcfg h0
  have hB := h.lemma113_ii_pieceB hcfg hA
  exact h.lemma113_ii_pieceD hcfg (h.lemma113_ii_pieceC hcfg hA hB)


theorem prop117 (h : MovingAroundLeaves) (hs : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K)
    (ht : Type117a p E A K ∨ Type117b p K ∨ Type117c p A K) :
    K ≤ M ∨ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := by
  by_contra hcon
  rw [not_or] at hcon
  by_cases hex : ∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a'
  · obtain ⟨E', A', a', K', hb', hnn⟩ := hex
    exact h.prop117_cex_false (⟨hb', fun _ => hnn⟩ : Cex117 G m p B M E' A' a' K')
  · exact h.prop117_cex_false
      (⟨⟨hs, ⟨ha, ha1⟩, hK, ht, hcon.1, hcon.2⟩, fun hex' => absurd hex' hex⟩ :
        Cex117 G m p B M E A a K)


end Sec11Statements

section Sec12Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
theorem prop121 (h : MovingAroundLeaves) (hs : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    pCoreOf 2 (alphaOf p M ⊓ Cg a) ≤ pCoreOf 2 (Cg a) := by
  by_contra hc
  exact h.prop121_of_cex (⟨hs, ⟨ha, ha1⟩, hc⟩ : Cex121 G m p B M E A a)


theorem prop127 (h : MovingAroundLeaves) (hs : Sec11 G m p B M E A) {N D : Subgroup G} (hN : IsTwoLocal N)
    (hD : IsEkIn p 2 A D) (h1 : pCoreOf 2 M ≤ N) (h2 : Subgroup.normalizer (D : Set G) ≤ N) :
    pCoreOf 2 M ≤ pCoreOf 2 N := by
  by_contra hc
  exact h.prop127_of_cex (⟨hs, hN, hD, h1, h2, hc⟩ : Cex127 G m p B M E A N D)


end Sec12Statements

section Sec13Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
theorem prop134 (h : MovingAroundLeaves) {D T : Subgroup G} (hs : Sec13 G m p B M E A D T) {L : Subgroup G}
    (hL : GLAPComponent p (Iof p M D) L) : Prop95Alpha p M D L ∨ Prop95Beta p M D L := by
  by_contra hc
  exact h.prop134_of_cex (⟨hs, hL, hc⟩ : Cex134 G m p B M E A D T L)


theorem prop1310_of_cex (h : MovingAroundLeaves) {D T R L0 : Subgroup G} {d : G} (hs : Cex1310 G m p B M E A D T R L0 d) :
    False := by
  rcases hs.h139 with ha | hb
  · exact h.lemma1316 hs ha
  · exact h.prop1310_a5 hs hb


end Sec13Statements

section Assembly
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}

theorem main_contradiction (h : MovingAroundLeaves) {D T : Subgroup G} (hs : Sec13 G m p B M E A D T) : False :=
  h.final_of_prop1310 hs (h.prop1310 hs)


theorem exists_good_conj (h : MovingAroundLeaves) (hs : Sec10Fails G m p B M) {A N : Subgroup G} (hA : IsElemAbelian p A)
    (hAM : A ≤ M) :
    ∃ B₁ : Subgroup G, (∃ y ∈ M, B₁ = GLBConj y B) ∧ IsPGroup p ↥(A ⊔ B₁) ∧
      ∀ B₂ : Subgroup G, (∃ y ∈ M, B₂ = GLBConj y B₁) → IsPGroup p ↥(A ⊔ B₂) → B₂ ≤ N →
        B₁ ≤ N := by
  classical
  by_cases hex : ∃ B₂ : Subgroup G, (∃ y ∈ M, B₂ = GLBConj y B) ∧ IsPGroup p ↥(A ⊔ B₂) ∧ B₂ ≤ N
  · obtain ⟨B₂, hB₂, hp, hN⟩ := hex
    exact ⟨B₂, hB₂, hp, fun _ _ _ _ => hN⟩
  · obtain ⟨y, hy, hp⟩ := h.exists_conj_pGroup hs hA hAM
    refine ⟨GLBConj y B, ⟨y, hy, rfl⟩, hp, fun B₃ hB₃ hp₃ hN₃ => ?_⟩
    exfalso
    apply hex
    obtain ⟨y', hy', rfl⟩ := hB₃
    exact ⟨GLBConj y' (GLBConj y B), ⟨y * y', M.mul_mem hy hy', by rw [gLBConj_gLBConj]⟩, hp₃, hN₃⟩


theorem theoremTwoStar_of_leaves (h : MovingAroundLeaves) : TheoremTwoStar := by
  intro G _ _ m p hS B M hB hM hU
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnB, hnA⟩ := hcon
  push Not at hnA
  have h10 : Sec10Fails G m p B M := ⟨⟨hS, hB, hM, hU⟩, fun hs => hnB (Or.inl hs), hnA⟩
  obtain ⟨E, A, hEA⟩ := lemma104_exists h h10
  obtain ⟨D, T, hD, hT1, hT2, hN⟩ := h.prop132 (⟨h10, hEA⟩ : Sec11 G m p B M E A)
  have hSC : IsSCp p M A := hEA.1.2.1.1.1
  obtain ⟨B₁, ⟨y, hy, rfl⟩, hAB, hch⟩ :=
    exists_good_conj h h10 (N := Subgroup.normalizer (T : Set G)) hSC.2.1 hSC.1
  exact main_contradiction h (⟨⟨h.sec10Fails_conj h10 hy, hEA⟩, hD, hT1, hT2, hN, hAB, hch⟩ :
    Sec13 G m p (GLBConj y B) M E A D T)


theorem movingAround_of_leaves (h : MovingAroundLeaves) : CFSG.Yardstones.M67c2c3e09a6b.MovingAround :=
  movingAround_of_theoremTwoStar (fun _ => theoremTwoStar_of_leaves h)


end Assembly


end CFSG.LocalAnalysis.GLTheoremB.MovingAround
