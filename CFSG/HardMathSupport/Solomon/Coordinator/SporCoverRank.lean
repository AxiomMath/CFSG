module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverModule
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlpha

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.AGLEmbedding

theorem exists_elemAbelian_succ_of_datum {K X : Type} [Group K] [Finite K] [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hZ1 : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (D : ModuleSpec X p) (hA : D.NoAlt) (hF : D.NoFun) (P : Sylow p X)
    (hP : (P : Subgroup X) ≤ Subgroup.normalizer (D.span : Set X)) (T : Sylow p K) :
    ∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧ Open.IsElemAbelian p A ∧
      p ^ (D.n + 1) ≤ Nat.card A := by
  have := Fact.mk hp
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P (T.mapSurjective hπ)
  let D' := D.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hPg : ((g • P : Sylow p X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hTN : (T : Subgroup K).map π ≤ Subgroup.normalizer (D'.span : Set X) := by
    rw [← Sylow.coe_mapSurjective hπ, ← hg, hPg, show D'.span = _ from D.map_span _ _]
    exact (Subgroup.map_mono hP).trans (Subgroup.le_normalizer_map _)
  have hcomm := D'.commute_of_noAlt π hp hp2 hπ hker hZp hZc hA
  have hTÂ : (T : Subgroup K) ≤ Subgroup.normalizer ((D'.span.comap π : Subgroup K) : Set K) :=
    fun t ht => Subgroup.le_normalizer_comap π (hTN (Subgroup.mem_map_of_mem π ht))
  have hÂp : IsPGroup p (D'.span.comap π) := by
    refine IsPGroup.comap_of_ker_isPGroup (fun u => ⟨1, ?_⟩) π (hker ▸ hZp)
    rw [pow_one]
    exact Subtype.ext (D'.pow_eq_one_of_mem u.2)
  have hÂT : D'.span.comap π ≤ T :=
    sup_eq_right.mp (T.is_maximal' (hÂp.to_sup_of_normal_left' T.isPGroup' hTÂ) le_sup_right)
  exact ⟨omegaOf (D'.span.comap π) hcomm p, omegaOf_le.trans hÂT, isElemAbelian_omegaOf,
    D'.pow_succ_le_card_omegaOf π hp hp2 hπ hker hZ1 hZp hZc hcomm hF⟩

theorem succ_le_pRank_of_datum {K X : Type} [Group K] [Finite K] [Group X]
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup 3 (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (D : ModuleSpec X 3) (hA : D.NoAlt) (hF : D.NoFun)
    (P : Sylow 3 X) (hP : (P : Subgroup X) ≤ Subgroup.normalizer (D.span : Set X)) :
    D.n + 1 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 3 K))
  obtain ⟨A, hAT, hAe, hcard⟩ := exists_elemAbelian_succ_of_datum Nat.prime_three (by norm_num) π
    hπ hker hZ1 hZp hZc D hA hF P hP T
  have hAp : IsPGroup 3 A := T.isPGroup'.to_le hAT
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hAp
  rw [hk] at hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hcard
  exact this.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hAe hk)

theorem succ_le_pRank_of_spec {K X : Type} [Group K] [Finite K] [Group X]
    (π : K →* X) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center K)
    (hZ1 : Subgroup.center K ≠ ⊥) (hZp : IsPGroup 3 (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) (D : ModuleSpec X 3) (hA : D.NoAlt) (hF : D.NoFun) :
    D.n + 1 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have hcomm := D.commute_of_noAlt π Nat.prime_three (by norm_num) hπ hker hZp hZc hA
  have hcard := D.pow_succ_le_card_omegaOf π Nat.prime_three (by norm_num) hπ hker hZ1 hZp hZc
    hcomm hF
  have hAp : IsPGroup 3 (omegaOf (D.span.comap π) hcomm 3) := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext g.2.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hAp
  rw [hk] at hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hcard
  exact this.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top isElemAbelian_omegaOf hk)

theorem succ_le_pRank_of_center_three {L X : Type} [Group L] [Finite L] [Group X]
    (hZ : Nat.card (Subgroup.center L) = 3) (e : L ⧸ Subgroup.center L ≃* X)
    (D : ModuleSpec X 3) (hA : D.NoAlt) (hF : D.NoFun) :
    D.n + 1 ≤ Open.pRank 3 (⊤ : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ1 : Subgroup.center L ≠ ⊥ := by
    intro h
    rw [h] at hZ
    simp at hZ
  have hZp : IsPGroup 3 (Subgroup.center L) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have : Fact (Nat.Prime (Nat.card (Subgroup.center L))) := ⟨by rw [hZ]; exact Nat.prime_three⟩
  have hZc : IsCyclic (Subgroup.center L) := isCyclic_of_prime_card rfl
  refine succ_le_pRank_of_spec ((e : L ⧸ Subgroup.center L →* X).comp
    (QuotientGroup.mk' (Subgroup.center L))) ?_ ?_ hZ1 hZp hZc D hA hF
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    simp

theorem four_le_pRank_of_moduleDatum {L X : Type} [Group L] [Finite L] [Group X]
    (hZ : Nat.card (Subgroup.center L) = 3) (e : L ⧸ Subgroup.center L ≃* X)
    (hD : ModuleDatum X 3) : 4 ≤ Open.pRank 3 (⊤ : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ1 : Subgroup.center L ≠ ⊥ := by
    intro h
    rw [h] at hZ
    simp at hZ
  have hZp : IsPGroup 3 (Subgroup.center L) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have : Fact (Nat.Prime (Nat.card (Subgroup.center L))) := ⟨by rw [hZ]; exact Nat.prime_three⟩
  have hZc : IsCyclic (Subgroup.center L) := isCyclic_of_prime_card rfl
  obtain ⟨D, hn, hA, hF, P, hP⟩ := ModuleDatum.of_mulEquiv e.symm hD
  have := succ_le_pRank_of_datum (QuotientGroup.mk' (Subgroup.center L)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hZ1 hZp hZc D hA hF P hP
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
