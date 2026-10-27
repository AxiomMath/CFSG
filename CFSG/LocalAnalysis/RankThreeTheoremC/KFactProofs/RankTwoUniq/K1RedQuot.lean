module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Reduced
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1Red

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_le_sylow (P : Sylow p G) {H S : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (hSH : S ≤ H) (hS : IsPGroup p S) :
    ∃ h ∈ H, S.map (MulAut.conj h).toMonoidHom ≤ P := by
  obtain ⟨T, hT⟩ := (hS.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H T (P.subtype hPH)
  refine ⟨h, h.2, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (⟨s, hSH hs⟩ : H) ∈ (T : Subgroup H) := hT hs
  have hmem := Subgroup.smul_mem_pointwise_smul (⟨s, hSH hs⟩ : H) (MulAut.conj h) _ hs'
  rw [← Sylow.coe_subgroup_smul, hh] at hmem
  exact hmem

theorem normalizer_le_of_conj {H S : Subgroup G} {h : G} (hh : h ∈ H)
    (hN : normalizer ((S.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) ≤ H) :
    normalizer (S : Set G) ≤ H := by
  rw [← Subgroup.map_equiv_normalizer_eq] at hN
  intro n hn
  have h1 : h * n * h⁻¹ ∈ H := by
    have := hN ⟨n, hn, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have h2 : n = h⁻¹ * (h * n * h⁻¹) * h := by group
  rw [h2]
  exact H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh

end Sylow

section Reduced

variable {A : Type} [Group A] [Finite A]

theorem pRank_eq_two {X Q U : Subgroup A} (hrk : Open.pRank 3 X = 2) (hQX : Q ≤ X) (hUQ : U ≤ Q)
    (hUel : IsElemAbelian 3 U) (hUc : Nat.card U = 9) : Open.pRank 3 Q = 2 :=
  le_antisymm ((SU1.pRank_mono (by norm_num) hQX).trans hrk.le)
    (SU1.le_pRank (by norm_num) hUQ hUel (k := 2) (by rw [hUc]; norm_num))

theorem le_of_gammaTwo {X Q Y : Subgroup A} (hQX : Q ≤ X) (hQ2 : 2 ≤ Open.pRank 3 Q)
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y) :
    Q ≤ Y :=
  fun q hq => hΓ2 Q le_rfl hQ2 ⟨Subgroup.le_normalizer hq, hQX hq⟩

theorem normalizer_le_of_le_plane {X Y U : Subgroup A} (hUp : IsPGroup 3 (U.subgroupOf X))
    (hUel : IsElemAbelian 3 ((U.subgroupOf X).map (P64Asm.XBar.mk 3 X)))
    (hΓU : ∀ S : Subgroup A, S ≤ U → 1 ≤ Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y)
    {Vb : Subgroup (P64Asm.XBar 3 X)} (hVb : Vb ≤ (U.subgroupOf X).map (P64Asm.XBar.mk 3 X))
    (hV1 : Vb ≠ ⊥) :
    normalizer (Vb : Set (P64Asm.XBar 3 X)) ≤ (Y.subgroupOf X).map (P64Asm.XBar.mk 3 X) := by
  refine P64Asm.normalizer_le_map_of_gamma Nat.prime_three (primeComplementCore (G := ↥X) 3)
    (P64Asm.XBar.coprime 3 X) hUp (k := 1) ?_ hVb ?_
  · intro S hSU hS1
    refine P64Asm.normalizer_subgroupOf_le S (hΓU _ ?_ ?_)
    · rintro _ ⟨s, hs, rfl⟩
      exact hSU hs
    · rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
        X.subtype_injective S]
      exact hS1
  · obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    have hvp : (v : P64Asm.XBar 3 X) ^ 3 = 1 := hUel.2 _ (hVb v.2)
    have hv1' : (v : P64Asm.XBar 3 X) ≠ 1 := fun h => hv1 (Subtype.ext h)
    exact (P64Free.one_le_pRank_zpowers Nat.prime_three hvp hv1').trans
      (SU1.pRank_mono (by norm_num) (Subgroup.zpowers_le.mpr v.2))

theorem normalizer_le_of_rank_two {X Y Q : Subgroup A} (hQp : IsPGroup 3 (Q.subgroupOf X))
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y)
    (Qb : Sylow 3 (P64Asm.XBar 3 X))
    (hQb : (Qb : Subgroup (P64Asm.XBar 3 X)) = (Q.subgroupOf X).map (P64Asm.XBar.mk 3 X))
    (hQbY : (Qb : Subgroup (P64Asm.XBar 3 X)) ≤ (Y.subgroupOf X).map (P64Asm.XBar.mk 3 X))
    {Sb : Subgroup (P64Asm.XBar 3 X)} (hSbY : Sb ≤ (Y.subgroupOf X).map (P64Asm.XBar.mk 3 X))
    (hSb : IsPGroup 3 Sb) (hrk : 2 ≤ Open.pRank 3 Sb) :
    normalizer (Sb : Set (P64Asm.XBar 3 X)) ≤ (Y.subgroupOf X).map (P64Asm.XBar.mk 3 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hhY, hle⟩ := exists_conj_le_sylow Qb hQbY hSbY hSb
  have hrk' : 2 ≤ Open.pRank 3 (Sb.map (MulAut.conj h).toMonoidHom) := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
      (MulAut.conj h).injective]
    exact hrk
  exact normalizer_le_of_conj hhY
    (P64Asm.XBar.gamma2 Nat.prime_three hQp hΓ2 (hle.trans hQb.le) hrk')

theorem reduced {X Q U Y : Subgroup A} (hrk : Open.pRank 3 X = 2) (hQX : Q ≤ X) (hQp : IsPGroup 3 Q)
    (hUQ : U ≤ Q) (hUel : IsElemAbelian 3 U) (hUc : Nat.card U = 9) (hYX : Y ≤ X)
    (hYne : Y ≠ X)
    (hΓU : ∀ S : Subgroup A, S ≤ U → 1 ≤ Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y)
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y)
    (Qb : Sylow 3 (P64Asm.XBar 3 X))
    (hQb : (Qb : Subgroup (P64Asm.XBar 3 X)) = (Q.subgroupOf X).map (P64Asm.XBar.mk 3 X)) :
    CFSG.AGLEmbeddingD2.D2Reduced 3 (P64Asm.XBar 3 X) Qb
      ((U.subgroupOf X).map (P64Asm.XBar.mk 3 X)) ((Y.subgroupOf X).map (P64Asm.XBar.mk 3 X)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hUX : U ≤ X := hUQ.trans hQX
  have hU9 : Nat.card U = 3 ^ 2 := by rw [hUc]; norm_num
  have hQ2 : Open.pRank 3 Q = 2 := pRank_eq_two hrk hQX hUQ hUel hUc
  have hQY : Q ≤ Y := le_of_gammaTwo hQX hQ2.ge hΓ2
  have hOY : rankThreePrimeCore 3 X ≤ Y :=
    P64Free.rankThreePrimeCore_le_of_gammaOne_plane hp hUX hUel hU9 hΓU
  have hXY : ¬ X ≤ Y := fun h => hYne (le_antisymm hYX h)
  have hQ'p : IsPGroup 3 (Q.subgroupOf X) := hQp.comap_subtype
  have hUpl := P64Asm.XBar.plane hp hQX hQp hUQ hUel hU9
  have hQbY : (Qb : Subgroup (P64Asm.XBar 3 X)) ≤ (Y.subgroupOf X).map (P64Asm.XBar.mk 3 X) := by
    rw [hQb]
    exact Subgroup.map_mono fun q hq => hQY hq
  refine
    { prime := hp
      ne_two := by norm_num
      core_eq_bot := primeComplementCore_quotient_eq_bot 3
      pRank_eq := ?_
      elem := hUpl.2.1
      card_A := hUpl.2.2
      A_le := by rw [hQb]; exact hUpl.1
      sylow_le := hQbY
      ne_top := fun htop => P64Asm.XBar.not_top_le hOY hXY htop.ge
      normalizer_le_of_le_A := fun Vb hVb hV1 =>
        normalizer_le_of_le_plane (hQ'p.to_le fun u hu => hUQ hu) hUpl.2.1 hΓU hVb hV1
      normalizer_le_of_rank := fun Sb hSbY hSb hrk =>
        normalizer_le_of_rank_two hQ'p hΓ2 Qb hQb hQbY hSbY hSb hrk }
  rw [hQb, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hp _ (P64Asm.XBar.coprime 3 X),
    Subgroup.map_subgroupOf_eq_of_le hQX]
  exact hQ2

end Reduced

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1Red
