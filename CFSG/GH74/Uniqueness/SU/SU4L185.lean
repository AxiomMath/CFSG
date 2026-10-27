module

public import CFSG.GH74.Uniqueness.SU.SU4L183

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Hyp184Core.S_le {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184Core S U M) :
    (S : Subgroup G) ≤ M := by
  have hU2 : 2 ≤ Open.pRank 2 U := SU1.le_pRank (by norm_num) le_rfl h.four.2.1 h.four.2.2
  have hC : 3 ≤ Open.pRank 2 (centralizer (U : Set G) ⊓ (S : Subgroup G)) := by
    rw [(SU1.ig10_20_ii Nat.prime_two h.isPGroup h.isNormalEp2).2.2]
    exact h.rank
  exact h.normal.trans ((normalizer_le_gammaElem h.four.1 h.four.2.1 hU2 hC).trans h.gamma_le)

theorem Hyp184.S_le {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184 S U M) :
    (S : Subgroup G) ≤ M :=
  Hyp184Core.S_le h.toHyp184Core

theorem Hyp184Core.isSylowIn_M {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184Core S U M) :
    IsSylowIn M (S : Subgroup G) :=
  (sylow_isSylowIn_top S).of_le h.S_le le_top

theorem Hyp184.isSylowIn_M {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184 S U M) :
    IsSylowIn M (S : Subgroup G) :=
  Hyp184Core.isSylowIn_M h.toHyp184Core

theorem normalizer_le_of_isFour {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184Core S U M)
    (hb : Concl184b M) {E : Subgroup G} (hE : IsFour M E) : normalizer (E : Set G) ≤ M := by
  obtain ⟨E', hE'4, hc, hne⟩ : ∃ B, IsFour M B ∧ (∀ a ∈ E, ∀ b ∈ B, a * b = b * a) ∧ B ≠ E := by
    by_contra hcon
    push Not at hcon
    exact hb E (isIsolatedVertex_iff.mpr ⟨hE, hcon⟩)
  have hFel : Open.IsElemAbelian 2 (E ⊔ E') := SU1.IsElemAbelian.sup hE.2.1 hE'4.2.1 hc
  have hFM : E ⊔ E' ≤ M := sup_le hE.1 hE'4.1
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hFel
  have hFp : IsPGroup 2 ↥(E ⊔ E') := IsPGroup.of_card hk
  have hFcard : 2 ^ 3 ≤ Nat.card ↥(E ⊔ E') :=
    (SU1.sup_isElemAbelian_card Nat.prime_two hE.2.1 hE.2.2 hE'4.2.1 hE'4.2.2 hne.symm hc).2
  obtain ⟨S₁, hS₁, hFS₁⟩ := exists_isSylowIn_ge hFM hFp
  obtain ⟨m, hmM, hS₁eq⟩ := h.isSylowIn_M.exists_conj_eq hS₁
  have hES₁ : E ≤ S₁ := le_sup_left.trans hFS₁
  have hFS : conjSub m⁻¹ (E ⊔ E') ≤ (S : Subgroup G) := by
    have := conjSub_mono (g := m⁻¹) hFS₁
    rwa [hS₁eq, conjSub_inv_conjSub] at this
  have hE''S : conjSub m⁻¹ E ≤ (S : Subgroup G) := (conjSub_mono le_sup_left).trans hFS
  have hE''rk : 2 ≤ Open.pRank 2 (conjSub m⁻¹ E) := by
    rw [pRank_conjSub (by norm_num)]
    exact SU1.le_pRank (by norm_num) le_rfl hE.2.1 hE.2.2
  have hF''C : conjSub m⁻¹ (E ⊔ E') ≤ centralizer ((conjSub m⁻¹ E : Subgroup G) : Set G) := by
    have h1 : E ⊔ E' ≤ centralizer (E : Set G) := fun f hf =>
      Subgroup.mem_centralizer_iff.mpr (fun e he =>
        (SU1.isElemAbelian_iff.mp hFel).1 e (Subgroup.mem_sup_left he) f hf)
    have := conjSub_mono (g := m⁻¹) h1
    rwa [conjSub_centralizer] at this
  have hC3 : 3 ≤ Open.pRank 2
      (centralizer ((conjSub m⁻¹ E : Subgroup G) : Set G) ⊓ (S : Subgroup G)) := by
    have hk3 : 3 ≤ k := by
      rw [hk] at hFcard
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hFcard
    exact hk3.trans (SU1.le_pRank (by norm_num) (le_inf hF''C hFS)
      (isElemAbelian_conjSub hFel) (by rw [card_conjSub]; exact hk))
  have hN : normalizer ((conjSub m⁻¹ E : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_gammaElem hE''S (isElemAbelian_conjSub hE.2.1) hE''rk hC3).trans h.gamma_le
  intro g hg
  have hconjE : conjSub m (conjSub m⁻¹ E) = E := conjSub_conjSub_inv m E
  have h1 : g ∈ conjSub m (normalizer ((conjSub m⁻¹ E : Subgroup G) : Set G)) := by
    rw [conjSub_normalizer, hconjE]; exact hg
  rw [mem_conjSub] at h1
  have hgM : m⁻¹ * g * m ∈ M := hN h1
  have : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hmM hgM) (M.inv_mem hmM)

theorem compSet_M_eq {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184Core S U M) (hb : Concl184b M)
    {A : Subgroup G} (hA : IsFour M A) : compSet M A = compSet ⊤ A := by
  ext E
  constructor
  · exact mem_compSet_mono le_top
  · intro hE
    obtain ⟨hA', hE4, hreach⟩ := hE
    have key : ∀ E : SU1.Ep2Vertex 2 (⊤ : Subgroup G),
        (SU1.Ep2Graph 2 ⊤).Reachable ⟨A, hA'⟩ E →
          ∃ hEM : E.1 ≤ M, (SU1.Ep2Graph 2 M).Reachable ⟨A, hA⟩ ⟨E.1, hEM, E.2.2.1, E.2.2.2⟩ := by
      intro E hr
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl => exact ⟨hA.1, SimpleGraph.Reachable.refl _⟩
      | tail hab hbc ih =>
        rename_i b c
        obtain ⟨hbM, hrb⟩ := ih
        have hb4 : IsFour M b.1 := ⟨hbM, b.2.2.1, b.2.2.2⟩
        have hcN : c.1 ≤ normalizer (b.1 : Set G) := fun y hy =>
          Subgroup.centralizer_le_normalizer (b.1 : Set G) (Subgroup.mem_centralizer_iff.mpr
            (fun x hx => hbc.2 x hx y hy))
        have hcM : c.1 ≤ M := hcN.trans (normalizer_le_of_isFour h hb hb4)
        refine ⟨hcM, hrb.trans (SimpleGraph.Adj.reachable ⟨fun e => hbc.1 (Subtype.ext ?_), hbc.2⟩)⟩
        have e' := congrArg Subtype.val e
        exact e'
    obtain ⟨hEM, hr⟩ := key ⟨E, hE4⟩ hreach
    exact ⟨hA, ⟨hEM, hE4.2.1, hE4.2.2⟩, hr⟩

theorem exists_isFour_not_mem_compSet {S : Sylow 2 G} {U M : Subgroup G} (h : Hyp184Core S U M)
    (hb : Concl184b M) : ∃ E : Subgroup G, IsFour ⊤ E ∧ E ∉ compSet ⊤ U := by
  have hU4M : IsFour M U := ⟨h.four.1.trans h.S_le, h.four.2.1, h.four.2.2⟩
  by_contra hcon
  push Not at hcon
  have hall : ∀ E : Subgroup G, IsFour ⊤ E → E ≤ M := by
    intro E hE
    have := hcon E hE
    rw [← compSet_M_eq h hb hU4M] at this
    exact (isFour_of_mem_compSet this).1
  have hN : Subgroup.normalClosure (U : Set G) ≤ M := by
    unfold Subgroup.normalClosure
    refine (Subgroup.closure_le M).mpr ?_
    intro y hy
    obtain ⟨u, hu, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hUc : IsFour ⊤ (conjSub c U) :=
      isFour_conjSub (g := c) (X := ⊤) (Y := ⊤) le_top ⟨le_top, h.four.2.1, h.four.2.2⟩
    exact hall _ hUc (hc ▸ mem_conjSub_of_mem hu)
  have hUbot : U ≠ ⊥ := by
    intro hU
    have := h.four.2.2
    rw [hU, Subgroup.card_bot] at this
    omega
  rcases h.simple.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (U : Set G)) with h0 | h0
  · apply hUbot
    rw [eq_bot_iff, ← h0]
    exact Subgroup.subset_normalClosure
  · rw [h0] at hN
    exact h.maximal.1 (top_le_iff.mp hN)

theorem lemma186_core :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M : Subgroup G), Hyp184Core S U M →
      Concl184b M → Concl184a S M := by
  intro G _ _ S U M h hb
  have hdisc := exists_isFour_not_mem_compSet h hb
  have hU4M : IsFour M U := ⟨h.four.1.trans h.S_le, h.four.2.1, h.four.2.2⟩
  have htrans : ∀ A, IsFour M A → ∃ m ∈ M, conjSub m A ∈ compSet M U := fun A hA =>
    exists_conj_mem_compSet h.isSylowIn_M h.rank h.isNormalEp2 hA (hb A)
  unfold Concl184a gammaTwo Open.properTwoGenCoreGamma
  refine iSup_le fun R => iSup_le fun hRS => iSup_le fun hR2 => ?_
  intro x hx
  obtain ⟨A, hAR, hAel, hAcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hR2
  have hRM : R ≤ M := hRS.trans h.S_le
  have hA : IsFour M A := ⟨hAR.trans hRM, hAel, hAcard⟩
  have hxR : conjSub x⁻¹ R = R := conjSub_eq_of_mem_normalizer (inv_mem hx)
  have hA' : IsFour M (conjSub x⁻¹ A) := by
    refine ⟨?_, isElemAbelian_conjSub hAel, by rw [card_conjSub]; exact hAcard⟩
    exact ((conjSub_mono hAR).trans hxR.le).trans hRM
  obtain ⟨y, hyM, hy⟩ := htrans A hA
  obtain ⟨z, hzM, hz⟩ := htrans _ hA'
  have hy' := mem_compSet_mono le_top (X := M) hy
  have hz' := mem_compSet_mono le_top (X := M) hz
  have hperm : PermutesComp U (z * x⁻¹ * y⁻¹) := by
    refine permutesComp_of_mem (A := conjSub y A) hy' ?_
    rw [← conjSub_mul, show z * x⁻¹ * y⁻¹ * y = z * x⁻¹ by group, conjSub_mul]
    exact hz'
  have hwM := h.disconn_le hdisc _ hperm
  have : x = (z⁻¹ * (z * x⁻¹ * y⁻¹) * y)⁻¹ := by group
  rw [this]
  exact M.inv_mem (M.mul_mem (M.mul_mem (M.inv_mem hzM) hwM) hyM)

theorem lemma186 : Lemma186Stmt := by
  intro G _ _ S U M h hb
  exact lemma186_core G S U M h.toHyp184Core hb

end CFSG.GH74.Uniqueness.SU.SU4
