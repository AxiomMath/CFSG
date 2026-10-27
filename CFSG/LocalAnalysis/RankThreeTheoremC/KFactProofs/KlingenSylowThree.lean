module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenWreath
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU42Tools
import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec4.Item434Kit Subgroup

namespace KlingenSylowThree

section Transport

variable {p : ℕ} [Fact p.Prime] {K H : Type*} [Group K] [Group H]

theorem coe_smul_sylow_eq_map (g : H) (P : Sylow p H) :
    ((g • P : Sylow p H) : Subgroup H) = (P : Subgroup H).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, smul_inv_smul]
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]
    exact hy

theorem exists_mulEquiv_map_eq [Finite K] [Finite H] (e : K ≃* H) (T : Sylow p K)
    (W : Sylow p H) :
    ∃ φ : K ≃* H, (T : Subgroup K).map φ.toMonoidHom = (W : Subgroup H) := by
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (T.mapSurjective hs) W
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h1 := congrArg (fun P : Sylow p H => (P : Subgroup H)) hg
  simp only [coe_smul_sylow_eq_map, Sylow.coe_mapSurjective] at h1
  rw [← h1, Subgroup.map_map]
  rfl

theorem card_le_of_normal_cyclic_map (φ : K ≃* H) {T N : Subgroup K} {W : Subgroup H}
    (hTW : T.map φ.toMonoidHom = W) {n : ℕ}
    (hW : ∀ N' : Subgroup H, N' ≤ W → W ≤ normalizer (N' : Set H) → IsCyclic N' →
      Nat.card N' ≤ n)
    (hN : N ≤ T) (hnorm : T ≤ normalizer (N : Set K)) (hcyc : IsCyclic N) : Nat.card N ≤ n := by
  have hinj : Function.Injective φ.toMonoidHom := φ.injective
  have hbij : Function.Bijective φ.toMonoidHom := φ.bijective
  have h1 : N.map φ.toMonoidHom ≤ W := hTW ▸ Subgroup.map_mono hN
  have h2 : W ≤ normalizer ((N.map φ.toMonoidHom : Subgroup H) : Set H) := by
    rw [← hTW, ← Subgroup.map_normalizer_eq_of_bijective N hbij]
    exact Subgroup.map_mono hnorm
  have h3 : IsCyclic (N.map φ.toMonoidHom) :=
    ((N.equivMapOfInjective φ.toMonoidHom hinj).isCyclic).mp hcyc
  have h4 := hW _ h1 h2 h3
  rwa [Subgroup.card_map_of_injective hinj] at h4

end Transport

theorem card_le_three_of_wreath {K H : Type*} [Group K] [Group H] [Finite K] [Finite H]
    {z : Fin 3 → H} {t : H} (hf : WreathFacts z t) (hcard : Nat.card (wreathW z t) = 81)
    (hfac : (Nat.card H).factorization 3 = 4) (e : K ≃* H) (T : Sylow 3 K) {N : Subgroup K}
    (hN : N ≤ T) (hT : T ≤ normalizer (N : Set K)) (hc : IsCyclic N) : Nat.card N ≤ 3 := by
  have hW : Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3 := by
    rw [hcard, hfac]
    norm_num
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq e T (Sylow.ofCard (wreathW z t) hW)
  exact card_le_of_normal_cyclic_map φ hφ
    (fun N' h1 h2 h3 => KlingenWreath.card_le_three_of_normal_cyclic hf h1 h2 h3) hN hT hc

theorem nonempty_mulEquiv_SU42 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 1) :
    Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩ ≃*
      CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.SU42) := by
  obtain ⟨p, f, hp, hf⟩ := q
  simp only at hqp hqe
  subst hqp hqe
  obtain ⟨e₁⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.nonempty_mulEquiv
  exact ⟨((CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 _ hv).trans
    (CFSG.RankThree.PartTwo.Sec4.projSUEquivStatedProj 4 2 1).symm).trans e₁⟩

end KlingenSylowThree

theorem kFactKlingenSylowNormalCyclic_three (d : TauCeti.ValidLieTypeIndex)
    (hd : IsKlingenIndex 3 d) (K : Type) [Group K] [Finite K] (e : K ≃* CatGroup d)
    (T : Sylow 3 K) (N : Subgroup K) (hN : N ≤ (T : Subgroup K))
    (hT : (T : Subgroup K) ≤ normalizer (N : Set K)) (hc : IsCyclic N) : Nat.card N ≤ 3 := by
  rcases hd with ⟨q, ⟨hqp, hqe, hdq⟩ | ⟨-, hqp, hqe, hdq⟩⟩ | ⟨-, q, hqp, hqe, hdq⟩
  ·
    exfalso
    have hv := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).2
    rw [hdq, TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
    have hcard : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    exact hv ⟨rfl, hcard⟩
  ·
    obtain ⟨i, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨e₂⟩ := KlingenSylowThree.nonempty_mulEquiv_SU42 q hv hqp hqe
    exact KlingenSylowThree.card_le_three_of_wreath
      CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.wreathFacts
      CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.card_wreathW
      CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.factorization_card_SU42
      (e.trans e₂) T hN hT hc
  ·
    obtain ⟨i, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨e₂⟩ := CFSG.RankThree.PartTwo.Census.nonempty_typeBGroupEquiv_sp6 q hv hqp hqe
    exact KlingenSylowThree.card_le_three_of_wreath
      CFSG.RankThree.PartTwo.Sec4.Res417Four.wreathFacts_sp6
      CFSG.RankThree.PartTwo.Sec4.Res417Four.card_W6
      CFSG.RankThree.PartTwo.Sec4.Res417Four.factorization_card_H6' (e.trans e₂) T hN hT hc

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
