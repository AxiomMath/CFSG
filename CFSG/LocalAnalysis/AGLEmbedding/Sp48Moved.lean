module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Orbit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_of_relIndex_dvd {Y : Type*} [Group Y] {q : Y} {C : Subgroup Y} {n : ℕ}
    (hn : C.relIndex (Subgroup.zpowers q) ∣ n) : q ^ n ∈ C := by
  set g : Subgroup.zpowers q := ⟨q, Subgroup.mem_zpowers q⟩ with hg
  have h1 := Subgroup.pow_index_mem (C.subgroupOf (Subgroup.zpowers q)) g
  obtain ⟨m, hm⟩ := hn
  have h2 : g ^ n ∈ C.subgroupOf (Subgroup.zpowers q) := by
    rw [hm, pow_mul]
    exact Subgroup.pow_mem _ h1 m
  rw [Subgroup.mem_subgroupOf] at h2
  simpa [hg] using h2

omit [Finite G] in
theorem mem_of_sq_mem {Y : Type*} [Group Y] {N : Subgroup Y} {g : Y} {a : ℕ}
    (hg : g ^ 3 ^ a = 1) (hg2 : g ^ 2 ∈ N) : g ∈ N := by
  obtain ⟨t, ht⟩ : Odd (3 ^ a) := Odd.pow (by decide)
  have e : g ^ (2 * (t + 1)) = g := by
    rw [show 2 * (t + 1) = 3 ^ a + 1 by omega, pow_succ, hg, one_mul]
  rw [← e, pow_mul]
  exact N.pow_mem hg2 _

omit [Finite G] in
theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom =
      (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem D1PhaseThree.relIndex_centralizer_dvd' {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}
    (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hb : StmtBlockInnerNormalizer) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {k : G} (hk : k ∈ H ⊓ M) {I : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hIS : I ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)))
    (hIN : I ≤ Subgroup.normalizer
      (barM M (L.map (MulAut.conj k).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hILC : I ≤ barM M (L.map (MulAut.conj k).toMonoidHom) ⊔ Subgroup.centralizer
      (barM M (L.map (MulAut.conj k).toMonoidHom) : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    (Subgroup.centralizer (barM M (L.map (MulAut.conj k).toMonoidHom) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex I ∣
      Nat.card (blockParabolic M (pCoreOf 2 H) L) := by
  have hkS : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h3.inf_eq_inf_normalizer_twoCore ▸ hk).2
  have hLk := h3.isWeakSBlock_map_conj hL hk
  have hJN : blockParabolic M (pCoreOf 2 H) (L.map (MulAut.conj k).toMonoidHom) ≤
      Subgroup.normalizer (barM M (L.map (MulAut.conj k).toMonoidHom) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (blockParabolic_le_barM' _ _ _).trans Subgroup.le_normalizer
  have hdvd := relIndex_dvd_of_inner hIN hJN fun x hx =>
    h3.exists_mem_blockParabolic h84 h86 hD2 hb hLk (hIS hx) (hILC hx)
  rw [blockParabolic_map_conj hk.2 hkS,
    Subgroup.card_map_of_injective (MulAut.conj _).injective] at hdvd
  exact hdvd

omit [Finite G] in
theorem blockParabolic_conj_le_barPi {M H L : Subgroup G}
    (hKeq : H ⊓ M = M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) (hLM : L ≤ M) {k : G}
    (hk : k ∈ H ⊓ M) :
    blockParabolic M (pCoreOf 2 H) (L.map (MulAut.conj k).toMonoidHom) ≤
      barM M ((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L) := by
  refine Subgroup.map_mono (Subgroup.comap_mono (fun x hx => ⟨?_, ?_⟩))
  · have hxM : x ∈ M := by
      obtain ⟨y, hy, rfl⟩ := hx.2
      exact M.mul_mem (M.mul_mem hk.2 (hLM hy)) (M.inv_mem hk.2)
    exact hKeq ▸ ⟨hxM, hx.1⟩
  · exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem k
      (Subgroup.mem_iSup_of_mem hk hx.2))

end Tools

end CFSG.AGLEmbedding
