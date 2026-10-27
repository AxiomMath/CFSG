module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideBlocksThreeAux
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
import CFSG.LocalAnalysis.AGLEmbedding.RankRefinedBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem pow_not_mem_normalizer {L : Subgroup G} {r : ℕ} (hr : r.Prime) {t : G}
    (htr : IsPGroup r (Subgroup.zpowers t)) (htL : t ∉ Subgroup.normalizer (L : Set G)) :
    ∀ a : ℕ, 0 < a → a < r → t ^ a ∉ Subgroup.normalizer (L : Set G) := by
  intro a ha har hta
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp htr
  rw [Nat.card_zpowers] at hk
  have hcop : a.Coprime (orderOf t) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd hr).mpr (Nat.not_dvd_of_pos_of_lt ha har)))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact htL (hm ▸ Subgroup.pow_mem _ hta m)

omit [Finite G] in
theorem exists_addSubgroup_of_le {p n : ℕ} [Fact p.Prime] {X W : Subgroup G}
    (φ : Multiplicative (GaloisField p n) ≃* X) (hWX : W ≤ X) :
    ∃ W' : AddSubgroup (GaloisField p n),
      (∀ c, c ∈ W' ↔ (φ (Multiplicative.ofAdd c) : G) ∈ W) ∧ Nat.card W' = Nat.card W := by
  let W' : AddSubgroup (GaloisField p n) :=
    { carrier := {c | (φ (Multiplicative.ofAdd c) : G) ∈ W}
      zero_mem' := by
        change (φ (Multiplicative.ofAdd 0) : G) ∈ W
        rw [ofAdd_zero, map_one, Subgroup.coe_one]
        exact W.one_mem
      add_mem' := fun {a b} ha hb => by
        change (φ (Multiplicative.ofAdd (a + b)) : G) ∈ W
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        exact W.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        change (φ (Multiplicative.ofAdd (-a)) : G) ∈ W
        rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
        exact W.inv_mem ha }
  refine ⟨W', fun c => Iff.rfl, Nat.card_congr ?_⟩
  exact
    { toFun := fun c => ⟨(φ (Multiplicative.ofAdd c.1) : G), c.2⟩
      invFun := fun w => ⟨Multiplicative.toAdd (φ.symm ⟨w.1, hWX w.2⟩), by
        change (φ (Multiplicative.ofAdd (Multiplicative.toAdd (φ.symm ⟨w.1, hWX w.2⟩))) : G) ∈ W
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
        exact w.2⟩
      left_inv := fun c => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }

section Orbits

variable {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G} {M H R Np Z : Subgroup G}

theorem D1OneLieMData.le_blockClosure_map_conj_pow (h : D1OneLieMData p n e P M H R Np Z)
    (hB3 : StmtBlockThree) (hp3 : p = 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : G} (htK : t ∈ H ⊓ M)
    (htL : t ∉ Subgroup.normalizer (L : Set G)) (i : ℕ) :
    Z ≤ blockClosure M (H ⊓ M) (L.map (MulAut.conj (t ^ i)).toMonoidHom) := by
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have hti : t ^ i ∈ H ⊓ M := (H ⊓ M).pow_mem htK i
  rcases h.le_blockClosure_or_le_normalizer hB3 hp3 (hL.map_conj hti.2 (hKeq ▸ hti).2) with
    hZ | hK
  · exact hZ
  · exfalso
    apply htL
    have h1 : (L.map (MulAut.conj (t ^ i)).toMonoidHom).map (MulAut.conj t).toMonoidHom =
        L.map (MulAut.conj (t ^ i)).toMonoidHom :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK htK)
    rw [← map_conj_mul_eq, ← pow_succ', pow_succ, map_conj_mul_eq] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.map_injective (MulAut.conj (t ^ i)).injective h1)

theorem D1OneLieMData.le_pRank_of_five (h : D1OneLieMData p n e P M H R Np Z)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hp3 : p = 3) (hcyc : IsCyclic (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M))) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : G} (htK : t ∈ H ⊓ M)
    (htZ : t ∈ Subgroup.normalizer (Z : Set G))
    (hmove : ∀ a : ℕ, 0 < a → a < 5 → t ^ a ∉ Subgroup.normalizer (L : Set G)) {d : ℕ}
    (hd : 1 ≤ d) (hidx : 3 ^ d ≤ (Z ⊓ blockCentralizer M L).relIndex Z) :
    5 * d / 2 + 1 ≤ Open.pRank 3 (H ⊓ M) := by
  have hKeq := h.ph3.inf_eq_inf_normalizer_twoCore
  have htL : t ∉ Subgroup.normalizer (L : Set G) := by
    simpa using hmove 1 one_pos (by norm_num)
  have hti : ∀ i : ℕ, t ^ i ∈ H ⊓ M := fun i => (H ⊓ M).pow_mem htK i
  have hZel : IsElemAbelian 3 Z := hp3 ▸ h.isElemAbelian
  refine stmtOneLieRRBlocks h.ph3 h84 h86 hD2 hp3 hcyc (h.le_R.trans h.ph3.le_inf) hZel 5 d
    (fun i : Fin 5 => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom)
    (injective_map_conj_pow hmove) (fun i => hL.map_conj (hti i).2 (hKeq ▸ hti i).2)
    (fun i => h.le_blockClosure_map_conj_pow hB3 hp3 hL htK htL i) (fun i => ?_) (by omega)
  have hZi : Z.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom = Z :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.pow_mem _ htZ _)
  calc 3 ^ d ≤ (Z ⊓ blockCentralizer M L).relIndex Z := hidx
    _ = ((Z ⊓ blockCentralizer M L).map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom).relIndex
          (Z.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom) :=
        (Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective).symm
    _ = _ := by rw [map_conj_inf_blockCentralizer (hti i).2 (Subgroup.pow_mem _ htZ _), hZi]

theorem D1OneLieMData.exists_eq_map_conj_pow (h : D1OneLieMData p n e P M H R Np Z)
    (hB3 : StmtBlockThree) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : G}
    (htK : t ∈ H ⊓ M) {m : ℕ} (hrank : Open.pRank 3 (H ⊓ M) ≤ m)
    (hmove : ∀ a : ℕ, 0 < a → a < m → t ^ a ∉ Subgroup.normalizer (L : Set G)) {k : G}
    (hk : k ∈ H ⊓ M) :
    ∃ i : ℕ, i < m ∧
      L.map (MulAut.conj k).toMonoidHom = L.map (MulAut.conj (t ^ i)).toMonoidHom := by
  by_contra hne
  push Not at hne
  set f : Fin m → G := fun i => t ^ (i : ℕ) with hf
  set g : Fin (m + 1) → G := Fin.cons k f with hg
  have hfun : (fun j : Fin (m + 1) => L.map (MulAut.conj (g j)).toMonoidHom) =
      Fin.cons (L.map (MulAut.conj k).toMonoidHom)
        (fun i : Fin m => L.map (MulAut.conj (f i)).toMonoidHom) := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [hg]
  have hinj : Function.Injective fun j : Fin (m + 1) => L.map (MulAut.conj (g j)).toMonoidHom := by
    rw [hfun]
    refine Fin.cons_injective_of_injective ?_ (injective_map_conj_pow hmove)
    rintro ⟨i, hi⟩
    exact hne i i.2 hi.symm
  have hgK : ∀ j, g j ∈ H ⊓ M := fun j =>
    Fin.cases (by simpa [hg] using hk) (fun i => by simpa [hg, hf] using (H ⊓ M).pow_mem htK _) j
  have h1 := h.ph3.le_pRank_three_of_injective_conj (fun L' hL' => hB3 h.ph3 hL') hL g hgK hinj
  omega

end Orbits

end CFSG.AGLEmbedding
