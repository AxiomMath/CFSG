module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ConjPowInjective
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section Core

variable {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G} {M H R Np Z : Subgroup G}

theorem D1OneLieMData.pRank_plus_le_one (h : D1OneLieMData p n e P M H R Np Z) :
    Open.pRank p Np ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEN, hE, hEcard⟩ := pRank_attained p hp Np
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have : IsCyclic E := h.plus_cyclic E hEN hEp
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hle : Nat.card E ≤ p := by
    rw [← hg]
    exact Nat.le_of_dvd hp.pos
      (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2)))
  rw [hEcard] at hle
  by_contra h2
  have h3 := Nat.pow_lt_pow_right hp.one_lt (show 1 < Open.pRank p Np by omega)
  rw [pow_one] at h3
  omega

theorem D1OneLieMData.isCyclic_pCore (h : D1OneLieMData p n e P M H R Np Z)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hYZ : pCorePreimage p M ⊓ Z = ⊥) :
    IsCyclic (CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ph3.ne_two
  set O := CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) with hO
  have hYK := h.ph3.pCorePreimage_le_inf h84 hD2
  have hYN : H ⊓ M ≤ Subgroup.normalizer (pCorePreimage p M : Set G) :=
    inf_le_right.trans (le_normalizer_pCorePreimage p M)
  have hYNp : pCorePreimage p M ≤ Np := by
    rcases h.dichotomy _ hYK hYN with hZY | hY
    · exfalso
      have hZ : Z = ⊥ := le_bot_iff.mp (hYZ ▸ le_inf hZY le_rfl)
      have h1 := h.two_le_card
      rw [hZ, Subgroup.card_bot] at h1
      have h2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    · exact hY
  have hOle : O ≤ barM M Np := (barM_preimage O).symm.le.trans (barM_mono hYNp)
  by_contra hnc
  have : Fact (IsPGroup p O) := ⟨CFSG.pCore_isPGroup⟩
  obtain ⟨S, -, hScard, hSelem⟩ := lemma_4_5_a hp2 hnc
  have hQ : IsElemAbelian p (S.map O.subtype) :=
    elementary_abelian_map p ⟨hSelem.toIsMulCommutative,
      fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩ _
  have hQcard : Nat.card (S.map O.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective O.subtype_injective, hScard]
  have h2 : 2 ≤ Open.pRank p (barM M Np) :=
    le_csSup (pRank_bddAbove p hp _)
      ⟨S.map O.subtype, (Subgroup.map_subtype_le S).trans hOle, hQ, hQcard⟩
  have h3 := pRank_barM_le hp hp2 M Np (h.plus_le.trans inf_le_right)
  have h4 := h.pRank_plus_le_one
  omega

end Core

section Conjugates

omit [Finite G] in
theorem injective_map_conj_pow {L : Subgroup G} {t : G} {m : ℕ}
    (hmove : ∀ a : ℕ, 0 < a → a < m → t ^ a ∉ Subgroup.normalizer (L : Set G)) :
    Function.Injective fun i : Fin m => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom :=
  injective_map_conj_pow_of_forall_lt hmove

omit [Finite G] in
theorem conj_mem_blockCentralizer_map {M L : Subgroup G} {g x : G} (hg : g ∈ M)
    (hx : x ∈ blockCentralizer M L) :
    g * x * g⁻¹ ∈ blockCentralizer M (L.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨m, hm, rfl⟩ := hx
  refine ⟨⟨g, hg⟩ * m * (⟨g, hg⟩)⁻¹, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨g, hg⟩ * m * (⟨g, hg⟩)⁻¹) ∈
    Subgroup.centralizer (barM M (L.map (MulAut.conj g).toMonoidHom) : Set _)
  rw [barM_map_conj hg, map_mul, map_mul, map_inv, Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hm z hz
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc _ = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ *
        (z * QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩)⁻¹ := by group
    _ = QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m * z) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩)⁻¹ := by rw [hc]
    _ = _ := by group

omit [Finite G] in
theorem map_conj_inf_blockCentralizer {M L Z : Subgroup G} {g : G} (hg : g ∈ M)
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    (Z ⊓ blockCentralizer M L).map (MulAut.conj g).toMonoidHom =
      Z ⊓ blockCentralizer M (L.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxZ, hxC⟩, rfl⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hgZ x).mp hxZ, conj_mem_blockCentralizer_map hg hxC⟩
  · rintro x ⟨hxZ, hxC⟩
    have hL : (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = L := by
      rw [← map_conj_mul_eq, inv_mul_cancel]
      ext y
      simp
    have h1 := conj_mem_blockCentralizer_map (M.inv_mem hg) hxC
    rw [hL] at h1
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, ⟨?_, h1⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgZ) x).mp hxZ

end Conjugates

section Blocks

theorem D1PhaseThree.le_pRank_three_of_injective_conj_of_le {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {A : Subgroup G} (hAM : A ≤ M)
    (hA : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ A) {m : ℕ} (g : Fin m → G)
    (hgK : ∀ j, g j ∈ H ⊓ M)
    (hinj : Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom) :
    m ≤ Open.pRank 3 A := by
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have h1 := h.toTwoLocalPair.card_le_pRank_three_of_blocks_of_le hB3 hAM
    (fun j => L.map (MulAut.conj (g j)).toMonoidHom)
    (fun j => hL.map_conj (hgK j).2 (hKeq ▸ hgK j).2) hinj fun j _ hx =>
      hA ⟨hx.1, Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (g j)
        (Subgroup.mem_iSup_of_mem (hgK j) hx.2))⟩
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h1

variable {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G} {M H R Np Z : Subgroup G}

theorem D1OneLieMData.le_blockClosure_or_le_normalizer (h : D1OneLieMData p n e P M H R Np Z)
    (hB3 : StmtBlockThree) (hp3 : p = 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    Z ≤ blockClosure M (H ⊓ M) L ∨ H ⊓ M ≤ Subgroup.normalizer (L : Set G) := by
  set Y : Subgroup G := (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L with hY
  have hYn : H ⊓ M ≤ Subgroup.normalizer (Y : Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases h.dichotomy Y inf_le_left hYn with hZY | hYN
  · exact Or.inl (hZY.trans inf_le_right)
  · right
    intro g hg
    by_contra hgL
    have hL1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by ext x; simp
    have hinj : Function.Injective fun j : Fin 2 =>
        L.map (MulAut.conj (![1, g] j)).toMonoidHom := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] at hij
        exact hgL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hij.symm.trans hL1))
      · exfalso
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
          Matrix.cons_val_one, Matrix.cons_val_fin_one] at hij
        exact hgL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hij.trans hL1))
      · rfl
    have hgK : ∀ j, ![1, g] j ∈ H ⊓ M := by
      intro j
      fin_cases j
      · exact (H ⊓ M).one_mem
      · exact hg
    have h2 := h.ph3.le_pRank_three_of_injective_conj_of_le (fun L' hL' => hB3 h.ph3 hL') hL
      (h.plus_le.trans inf_le_right) hYN ![1, g] hgK hinj
    have h1 := h.pRank_plus_le_one
    subst hp3
    omega

theorem D1OneLieMData.le_normalizer_block (h : D1OneLieMData p n e P M H R Np Z)
    (hB3 : StmtBlockThree) (hp3 : p = 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : Z ≤ Subgroup.normalizer (L : Set G) := by
  have hKM : H ⊓ M ≤ M := inf_le_right
  rcases h.le_blockClosure_or_le_normalizer hB3 hp3 hL with hZE | hKL
  · have hT : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) ≤
        Subgroup.normalizer (barM M L : Set _) := by
      intro k hk z hz
      have hLk := hL.toIsTwoPrimeComponent.map_conj (hKM hk)
      by_cases he : barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L
      · rw [he] at hz
        exact Subgroup.le_normalizer hz
      · have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLk.component
          hL.component he
        exact Subgroup.centralizer_le_normalizer _
          ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hz)
    have hZN := barM_le_of_le_preimage (hZE.trans
      (blockClosure_le_preimage hKM hL.toIsTwoPrimeComponent hT))
    exact hL.toIsTwoPrimeComponent.le_normalizer hZN (h.le_R.trans h.ph3.le_M)
  · exact (h.le_R.trans h.ph3.le_inf).trans hKL

end Blocks

end CFSG.AGLEmbedding
