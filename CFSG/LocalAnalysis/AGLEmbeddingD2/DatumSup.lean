module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.FreeCases
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.RankThree.PartOne.KP.SporadicDefs

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

theorem glbCore_map_le_of_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    {p : ℕ} (hp : p.Prime) (k : ℕ) (e : K ≃* L) (P : Subgroup K) :
    (GLBCore p k P).map e.toMonoidHom ≤ GLBCore p k (P.map e.toMonoidHom) := by
  unfold GLBCore
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hQk, rfl⟩
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_equiv_normalizer_eq]
  exact le_sSup ⟨Q.map e.toMonoidHom, Subgroup.map_mono hQP,
    hQk.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp e.toMonoidHom
      e.injective Q).ge, rfl⟩

theorem D2IndexDatum.of_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (e : L ≃* K) (h : D2IndexDatum K p) : D2IndexDatum L p := by
  obtain ⟨hout, h⟩ := h
  refine ⟨by rwa [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e], ?_⟩
  rcases h with h2 | h3 | ⟨h3, hgen⟩ | hcore
  · exact Or.inl (by rwa [Nat.card_congr e.toEquiv])
  · refine Or.inr (Or.inl ?_)
    rwa [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp e.toMonoidHom
      e.injective ⊤, Subgroup.map_top_of_surjective _ e.surjective]
  · exact Or.inr (Or.inr (Or.inl ⟨by rwa [Nat.card_congr e.toEquiv],
      CFSG.AGLEmbedding.fusionGenerationOf_of_mulEquiv e.symm hgen⟩))
  · refine Or.inr (Or.inr (Or.inr fun S => ?_))
    have : Fact p.Prime := ⟨hp⟩
    have hS : GLBCore p 2 ((S : Subgroup L).map e.toMonoidHom) = ⊤ :=
      hcore (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    have h1 := glbCore_map_le_of_mulEquiv hp 2 e.symm ((S : Subgroup L).map e.toMonoidHom)
    have h2 : ((S : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom = (S : Subgroup L) := by
      rw [Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L :=
        MonoidHom.ext fun x => e.symm_apply_apply x
      rw [this, Subgroup.map_id]
    rw [h2, hS, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
    exact top_le_iff.1 h1

@[expose] def D2IndexDatumSup (K : Type*) [Group K] [Finite K] (p : ℕ) : Prop :=
  ¬ p ∣ Nat.card (Outer K) ∧ ∀ S : Sylow p K, ∀ A : Subgroup K, A ≤ (S : Subgroup K) →
    IsElemAbelian p A → Nat.card A = p ^ 2 → GLBCore p 2 (S : Subgroup K) ⊔ GLBCore p 1 A = ⊤

theorem D2AlmostSimple.false_of_coreSup {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (h : D2IndexDatumSup K p) : False := by
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨hout, hsup⟩ := h
  have hRK := hK.sylow_le_of_not_dvd_card_outer hout
  have hAK : A ≤ K := hK.A_le.trans hRK
  have hAT : A.subgroupOf K ≤ ((R.subtype hRK : Sylow p K) : Subgroup K) := by
    intro a ha
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hK.A_le (Subgroup.mem_subgroupOf.mp ha)
  have hAcard : Nat.card (A.subgroupOf K) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hK.card_A
  have hAel : IsElemAbelian p (A.subgroupOf K) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val
        (hK.elem.1.is_comm.comm (⟨((a : K) : X), a.2⟩ : A) ⟨((b : K) : X), b.2⟩)
      exact h
    · simpa using hK.elem.2 (x : X) hx
  have htop := hsup (R.subtype hRK) _ hAT hAel hAcard
  have h2 : GLBCore p 2 ((R.subtype hRK : Sylow p K) : Subgroup K) ≤ X₀.subgroupOf K := by
    refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mpr fun Q hQ hrank => ?_
    have hQX : Q.map K.subtype ≤ (R : Subgroup X) := by
      rintro _ ⟨q, hq, rfl⟩
      have := hQ hq
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at this
      exact this
    have hrank' : 2 ≤ Open.pRank p (Q.map K.subtype) := by
      rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hK.prime K.subtype
        K.subtype_injective Q]
    have hN := hK.normalizer_le_of_rank _ (hQX.trans hK.sylow_le) (R.isPGroup'.to_le hQX) hrank'
    intro n hn
    exact Subgroup.mem_subgroupOf.mpr (hN (Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩))
  have h1 : GLBCore p 1 (A.subgroupOf K) ≤ X₀.subgroupOf K := by
    refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 1 _ _).mpr fun Q hQ hrank => ?_
    have hQX : Q.map K.subtype ≤ A := by
      rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hQ hq)
    have hQne : Q.map K.subtype ≠ ⊥ := by
      intro hbot
      obtain ⟨E, hE, -, hEcard⟩ :=
        CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hK.prime Q
      rw [(Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hbot, le_bot_iff] at hE
      rw [hE, Subgroup.card_bot] at hEcard
      have := Nat.one_lt_pow (by omega : Open.pRank p Q ≠ 0) hK.prime.one_lt
      omega
    have hN := hK.normalizer_le_of_le_A _ hQX hQne
    intro n hn
    exact Subgroup.mem_subgroupOf.mpr (hN (Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩))
  refine hK.not_le fun k hk => ?_
  have hmem : (⟨k, hk⟩ : K) ∈ X₀.subgroupOf K := (sup_le h2 h1) (htop ▸ Subgroup.mem_top _)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem D2IndexDatumSup.of_mulEquiv {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    {p : ℕ} (hp : p.Prime) (e : L ≃* K) (h : D2IndexDatumSup K p) : D2IndexDatumSup L p := by
  obtain ⟨hout, hsup⟩ := h
  refine ⟨by rwa [CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv e], fun S A hAS hA hcard => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hinv : ∀ B : Subgroup L, (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
    intro B
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L :=
      MonoidHom.ext fun x => e.symm_apply_apply x
    rw [this, Subgroup.map_id]
  have hAel : IsElemAbelian p (A.map e.toMonoidHom) := by
    have := hA.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', hae⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hbe⟩ := Subgroup.mem_map.mp b.2
      have hc := congrArg Subtype.val (this.1.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      apply Subtype.ext
      change (a : K) * b = b * a
      rw [← hae, ← hbe, ← map_mul, ← map_mul]
      exact congrArg e.toMonoidHom hc
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_pow, hA.2 x hx, map_one]
  have hAcard : Nat.card (A.map e.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard]
  have htop : GLBCore p 2 ((S : Subgroup L).map e.toMonoidHom) ⊔
      GLBCore p 1 (A.map e.toMonoidHom) = ⊤ :=
    hsup (S.mapSurjective (f := e.toMonoidHom) e.surjective) _ (Subgroup.map_mono hAS) hAel hAcard
  have h2 := glbCore_map_le_of_mulEquiv hp 2 e.symm ((S : Subgroup L).map e.toMonoidHom)
  have h1 := glbCore_map_le_of_mulEquiv hp 1 e.symm (A.map e.toMonoidHom)
  rw [hinv] at h1 h2
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) htop
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
  rw [eq_top_iff, ← hmap]
  exact sup_le_sup h2 h1

@[expose] def D2IndexDatumPlus (K : Type*) [Group K] [Finite K] (p : ℕ) : Prop :=
  D2IndexDatum K p ∨ D2IndexDatumSup K p

theorem D2AlmostSimple.false_of_datum {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (h : D2IndexDatum K p) : False := by
  have : Fact p.Prime := ⟨hK.prime⟩
  obtain ⟨hout, hd⟩ := h
  rcases hd with h2 | h3 | ⟨h3, hgen⟩ | hcore
  · exact h2 (hK.sq_dvd_card hout)
  · exact hK.false_of_three_le_pRank h3
  · exact hK.false_of_fusion_of_card hout h3 hgen
  · exact hK.false_of_core hout hcore

theorem D2AlmostSimple.false_of_datumPlus {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (h : D2IndexDatumPlus K p) : False :=
  h.elim hK.false_of_datum hK.false_of_coreSup

theorem d2FreeCaseAt_of_datumPlus {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) → ∀ p, p.Prime → p ≠ 2 →
      Pp p → D2IndexDatumPlus L p) : D2FreeCaseAt i Pp := by
  intro X _ _ p hpc R A X₀ K hK he
  exact hK.false_of_datumPlus (h K he p hK.prime hK.ne_two hpc)

end CFSG.AGLEmbeddingD2
