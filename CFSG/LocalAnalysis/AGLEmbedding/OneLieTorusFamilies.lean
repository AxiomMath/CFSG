module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutRank
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Families

variable {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem center_ne_of_unitary_of_kFact (hKU2 : KFactUnitarySylowStructure) (hp2 : p ≠ 2)
    (T : Sylow p K) (hU : IsUnitaryGroup p K) :
    (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≠ T := by
  obtain ⟨d, hd, he⟩ := hU
  obtain ⟨hcard, hcomm, -, -⟩ := hKU2 K p d hp2 hd he T
  obtain ⟨q, -, -, hfe, hq⟩ := hd.exists_eq
  intro heq
  have hTC : (T : Subgroup K) ≤ Subgroup.centralizer ((T : Subgroup K) : Set K) :=
    fun x hx => (heq.ge hx).2
  rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hTC, heq] at hcomm
  have h1 : Nat.card (T : Subgroup K) = 1 := by rw [← hcomm, Subgroup.card_bot]
  rw [hcard] at h1
  exact (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt).ne' h1

theorem oneLieTorusFacts_of_psl2GF (hKU2 : KFactUnitarySylowStructure) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) (f : K ≃* PSL2GF p n) (T : Sylow p K) : OneLieTorusFacts p K T n 2 := by
  have hn1 : 1 ≤ n := by omega
  have hfs : Function.Surjective (f : K →* PSL2GF p n) := f.surjective
  set U : Sylow p (PSL2GF p n) := T.mapSurjective hfs with hU
  have hUT : (U : Subgroup (PSL2GF p n)) = (T : Subgroup K).map (f : K →* PSL2GF p n) :=
    Sylow.coe_mapSurjective hfs T
  have hcard : Nat.card (T : Subgroup K) = p ^ n := by
    rw [← (psl2GF_sylow p n hn1 U).2, hUT,
      Subgroup.card_map_of_injective (show Function.Injective (f : K →* PSL2GF p n) from
        f.injective)]
  obtain ⟨ψ, hψ, hψT, hc⟩ := exists_torus_param_of_mulEquiv_psl2GF hp2 hn1
    (Subgroup.topEquiv.trans f) (T : Subgroup K) le_top hcard
  have hTC : (T : Subgroup K) ≤ Subgroup.centralizer ((T : Subgroup K) : Set K) := by
    rw [← hψT]
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  let F : MulAut K →* MulAut (PSL2GF p n) := (MulAut.congr f).toMonoidHom
  have hF : Function.Injective F := (MulAut.congr f).injective
  refine ⟨by omega, Or.inr ⟨rfl, hn⟩, ⟨ψ, hψ, by rw [inf_eq_left.mpr hTC, hψT], fun μ => ?_⟩,
    center_ne_of_unitary_of_kFact hKU2 hp2 T, ?_, fun A hA => ?_, fun E hE => ?_,
    fun h2 => absurd h2 (by omega)⟩
  · obtain ⟨c, -, hcψ⟩ := hc μ
    refine ⟨c, ?_, hcψ⟩
    rw [← hψT]
    exact mem_normalizer_range_of_torus ψ μ.ne_zero hcψ
  · have h := psl2GF_borelCoatom p n hp2 hn1 U
    rw [hUT, ← MulEquiv.toMonoidHom_eq_coe, ← Subgroup.map_equiv_normalizer_eq] at h
    exact (OrderIso.isCoatom_iff f.mapSubgroup _).mp h
  · have hFA : ∀ β ∈ A.map F,
        (U : Subgroup (PSL2GF p n)).map (β : PSL2GF p n ≃* PSL2GF p n).toMonoidHom = U := by
      rintro _ ⟨α, hα, rfl⟩
      rw [hUT, Subgroup.map_map]
      conv_rhs => rw [← hA α hα, Subgroup.map_map]
      congr 1
      ext x
      simp [F]
    have := kFactL2SylowNormalizerSolvable p n hp2 hn1 U (A.map F) hFA
    exact Group.isSolvable_of_isSolvable_injective
      (f := (A.equivMapOfInjective F hF).toMonoidHom) (A.equivMapOfInjective F hF).injective
  · have h := kFactL2AutElemRank p n hp2 hn1 (E.map F) (elementary_abelian_map p hE F)
    rw [Subgroup.card_map_of_injective hF] at h
    simpa using h

theorem oneLieTorusFacts_of_unitary (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (hn : 2 ≤ d.1.fieldExponent) (he : Nonempty (K ≃* CatGroup d))
    (T : Sylow p K) : OneLieTorusFacts p K T d.1.fieldExponent 1 := by
  obtain ⟨ψ, hψ, hψT, hc⟩ := hKU3 K p d hd he T
  obtain ⟨hcard, hcomm, hpow, -⟩ := hKU2 K p d hp2 hd he T
  refine ⟨hn, Or.inl rfl, ⟨ψ, hψ, hψT, fun μ => ?_⟩, center_ne_of_unitary_of_kFact hKU2 hp2 T,
    hKU6 K p d hd he T, hKU8 K p d hd he T, fun E hE => by simpa using hKU9 K p d hd he E hE,
    fun h2 => ?_⟩
  · obtain ⟨c, hcN, hcψ⟩ := hc μ
    exact ⟨c, hcN, fun a => by rw [pow_one]; exact hcψ a⟩
  · have h4 : 2 * d.1.fieldExponent = 4 := by omega
    refine ⟨by rw [hcard, h2], hcomm, hpow, fun r hr hr4 hprim => ?_⟩
    exact hKU4 K p d hd hn he T r hr (by rw [h4]; exact hr4) (by rw [h4]; exact hprim)

end Families

theorem oneLieTorusFacts_of_ree {K : Type} [Group K] [Finite K]
    (hKU2 : KFactUnitarySylowStructure) (hKR2 : KFactReeSylowCenterTorus)
    (hKR4 : KFactReeBorelMaximal) (hKR5 : KFactReeSylowNormalizerSolvable)
    (hKR6 : KFactReeAutElemRank) {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d)
    (he : Nonempty (K ≃* CatGroup d)) (T : Sylow 3 K) :
    OneLieTorusFacts 3 K T d.1.fieldExponent 1 := by
  have hn := hd.three_le_fieldExponent
  obtain ⟨ψ, hψ, hψT, hc⟩ := hKR2 K d hd he T
  refine ⟨by omega, Or.inl rfl, ⟨ψ, hψ, hψT, fun μ => ?_⟩,
    center_ne_of_unitary_of_kFact hKU2 (by decide) T, hKR4 K d hd he T, hKR5 K d hd he T,
    fun E hE => by simpa using hKR6 K d hd he E hE, fun h2 => absurd h2 (by omega)⟩
  obtain ⟨c, hcN, hcψ⟩ := hc μ
  exact ⟨c, hcN, fun a => by rw [pow_one]; exact hcψ a⟩

theorem kFactOneLieTorus_of (hId : KFactOneLieIdent) (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (hKR2 : KFactReeSylowCenterTorus)
    (hKR4 : KFactReeBorelMaximal) (hKR5 : KFactReeSylowNormalizerSolvable)
    (hKR6 : KFactReeAutElemRank) : KFactOneLieTorus := by
  intro K _ _ hs hnab hcat p _ hp2 T hnc hcore hbig
  obtain ⟨d, hfam, he⟩ := hId K hs hnab hcat p Fact.out hp2 T hnc hcore hbig
  rcases hfam with ⟨n, hn, hdn⟩ | ⟨hdU, hn⟩ | hdR
  · obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdn
    obtain ⟨e⟩ := he
    exact ⟨n, 2, oneLieTorusFacts_of_psl2GF hKU2 hp2 hn (e.trans f) T⟩
  · exact ⟨_, 1, oneLieTorusFacts_of_unitary hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 hp2 hdU hn he T⟩
  · have hp3 : p = 3 := hdR.1
    subst hp3
    exact ⟨_, 1, oneLieTorusFacts_of_ree hKU2 hKR2 hKR4 hKR5 hKR6 hdR he T⟩

end CFSG.AGLEmbedding
