module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bQ8
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bRed

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem autData_conjNormal_aux_equiv {G P : Type*} [Group G] [Group P] (ρ : G →* P)
    {A : Subgroup G} (h : A ⊓ ρ.ker = ⊥) :
    ∃ e : A ≃* A.map ρ, ∀ a : A, ((e a : A.map ρ) : P) = ρ a := by
  have hinj : Function.Injective (ρ.comp A.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : (a : G) ∈ A ⊓ ρ.ker := ⟨a.2, ha⟩
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  refine ⟨MulEquiv.ofBijective ((ρ.comp A.subtype).codRestrict (A.map ρ) (fun a => ⟨a, a.2, rfl⟩))
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), ?_⟩, fun a => rfl⟩
  rintro ⟨_, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

theorem autData_conjNormal_aux_hasQ8 {G P : Type} [Group G] [Group P] (ρ : G →* P)
    {T A : Subgroup G} (e : A ≃* A.map ρ) (he : ∀ a : A, ((e a : A.map ρ) : P) = ρ a)
    (h : HasQ8 (autInduced T A)) : HasQ8 (autInduced (T.map ρ) (A.map ρ)) := by
  obtain ⟨Q, hQ, ⟨f⟩⟩ := h
  refine ⟨Q.map (MulAut.congr e).toMonoidHom, ?_,
    ⟨(Q.equivMapOfInjective _ (MulAut.congr e).injective).symm.trans f⟩⟩
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨m, hm, rfl⟩ := hQ hφ
  refine ⟨⟨ρ m, Subgroup.le_normalizer_map ρ ⟨m, m.2, rfl⟩⟩, ⟨m, hm, rfl⟩, ?_⟩
  ext y
  obtain ⟨a, rfl⟩ := e.surjective y
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [K21bRedProof.normalizerMonoidHom_coe, he, he, K21bRedProof.normalizerMonoidHom_coe]
  simp

theorem autData_conjNormal_aux_isSylowOf_map {G G' : Type*} [Group G] [Group G'] [Finite G] {p : ℕ}
    [Fact p.Prime] (φ : G →* G') {P K : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p P K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem autData_conjNormal {Y : Type} [Group Y] [Finite Y] (π : X →* Y) {Jn : Subgroup X}
    (hJn : Jn.Normal) [hN : (Jn.map π).Normal] {T R A : Subgroup X} (hA : AConfig T R A)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hnc : ⁅Jn.map π, A.map π⁆ ≠ ⊥) :
    AutData ↥(Jn.map π)
      (A.map ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π))
      (T.map ((MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π)) := by
  set ρ : X →* MulAut ↥(Jn.map π) := (MulAut.conjNormal : Y →* MulAut ↥(Jn.map π)).comp π
  have hker : ρ.ker = (Subgroup.centralizer ((Jn.map π : Subgroup Y) : Set Y)).comap π :=
    ker_conjNormal_comp π
  have hkerN : T ≤ Subgroup.normalizer (ρ.ker : Set X) := by
    rw [Subgroup.normalizer_eq_top (H := ρ.ker)]
    exact le_top
  have hinf : A ⊓ ρ.ker = ⊥ := by
    rcases hA.inf_eq_bot_or_le hkerN with h | h
    · exact h
    · exfalso
      apply hnc
      have h1 : A.map π ≤ Subgroup.centralizer ((Jn.map π : Subgroup Y) : Set Y) := by
        rw [Subgroup.map_le_iff_le_comap, ← hker]
        exact h
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 h1
  obtain ⟨e, he⟩ := autData_conjNormal_aux_equiv ρ hinf
  refine ⟨CFSG.SectionRank.isElemAbelian_map hA.elemAbelian ρ,
    (Nat.card_congr e.toEquiv).symm.trans hA.card_eq, hT.2.1.map ρ, ?_,
    permutable_map ρ hA.perm, autData_conjNormal_aux_hasQ8 ρ e he hA.quaternion, ?_⟩
  · have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hT.1, hT.2.1, hT.2.2⟩
    have hmap := autData_conjNormal_aux_isSylowOf_map ρ hSyl
    haveI := K21bRedProof.finite_mulAut ↥(Jn.map π)
    haveI := K21bRedProof.innAut_normal ↥(Jn.map π)
    refine CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hmap ?_ ?_
    · rintro _ ⟨k, rfl⟩
      obtain ⟨j, hj, hjk⟩ := k.2
      refine ⟨j, trivial, ?_⟩
      show MulAut.conjNormal (π j) = MulAut.conj k
      have h1 : π j = (k : Y) := hjk
      rw [h1, MulAut.conjNormal_val]
    · rw [Subgroup.normalizer_eq_top (H := innAut ↥(Jn.map π))]
      exact le_top
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hx hy
    have ha1 : a ≠ 1 := fun h => hx (by rw [h, map_one])
    have hb1 : b ≠ 1 := fun h => hy (by rw [h, map_one])
    obtain ⟨t, ht, htab⟩ := hA.transitive a ha ha1 b hb hb1
    exact isConj_iff.2 ⟨ρ t, by rw [← map_mul, ← map_inv, ← map_mul, htab]⟩

theorem false_of_autData_outer (k420 : K420) {J : Type} [Group J] [Finite J]
    (hJ : CFSG.Open.IsQuasisimple J) (hS : IsClassicalTwoOrG2 (J ⧸ Subgroup.center J))
    {E T' : Subgroup (MulAut J)} (h : AutData J E T') (hE : E ⊓ innAut J = ⊥) : False := by
  haveI := K21bRedProof.innAut_normal J
  obtain ⟨a, ha, b, hb, hab⟩ := hasQ8_exists_noncomm h.quaternion
  refine hab (K21bRedProof.autInduced_comm T' E ?_ a ha b hb)
  intro s hs t ht hsN htN e he
  have hst : ⁅s, t⁆ ∈ innAut J := k420 J hJ hS T' h.pgroup s hs t ht
  exact K21bRedProof.commute_of_inf_eq_bot (innAut J) E hE hst
    ((Subgroup.normalizer (E : Set (MulAut J))).mul_mem
      ((Subgroup.normalizer (E : Set (MulAut J))).mul_mem
        ((Subgroup.normalizer (E : Set (MulAut J))).mul_mem hsN htN)
        ((Subgroup.normalizer (E : Set (MulAut J))).inv_mem hsN))
      ((Subgroup.normalizer (E : Set (MulAut J))).inv_mem htN)) he

end CFSG.LocalAnalysis.RankThreeUC.S15
