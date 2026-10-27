module

import CFSG.Adapters.CatalogueFieldBridges.Linear
import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
import CFSG.LieType.SeitzGeneration.OuterSpData
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCSp
import CFSG.LocalAnalysis.SectionRank.PRankIndex
import CFSG.Quasithin.Background.A318PL3Iso
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.RankThree.PartTwo.Sec13.K135OutTwoLin
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog

private theorem index_linearAutGroup_three_dvd_two {K : Type} [Field K] [Finite K] {q : ℕ}
    (hq : q.Prime) (hK : Nat.card K = q) : (linearAutGroup 3 K).index ∣ 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hsub : Subsingleton (K ≃+* K) :=
    CFSG.RankThree.PartOne.CTP.subsingleton_ringEquiv_of_card_eq_prime hK
  have hEeq : semilinearAutGroup 3 K = linearAutGroup 3 K :=
    le_antisymm (CFSG.RankThree.PartTwo.Sec13.F135Last.ot_semilinear_le_linear hsub)
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup_le_semilinearAutGroup
  have hR := (automorphism_generation (K := K) (n := 3) le_rfl).1
  obtain ⟨-, -, -, -, -, -, -, hRE, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  rw [hR] at hRE
  have hidxeq : (semilinearAutGroup 3 K).index =
      ((semilinearAutGroup 3 K).subgroupOf
        (⊤ : Subgroup (MulAut (projectiveSL 3 K)))).index := by
    rw [← Subgroup.relIndex_mul_index
      (H := semilinearAutGroup 3 K)
      (K := (⊤ : Subgroup (MulAut (projectiveSL 3 K)))) le_top,
      Subgroup.index_top, mul_one]
    rfl
  have hle : (linearAutGroup 3 K).index ≤ 2 := by
    rw [← hEeq, hidxeq]
    exact hRE
  have hne : (linearAutGroup 3 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : (linearAutGroup 3 K).index = 1 ∨
    (linearAutGroup 3 K).index = 2) with h | h <;> rw [h] <;> norm_num

private theorem pRank_linearAutGroup_three_le_two_of_dvd {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ∣ Nat.card Kˣ) :
    CFSG.Open.pRank p (linearAutGroup 3 K) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt (fun E hE hEea => ?_)
  set U := (⊤ : Subgroup (GL (Fin 3) K))
  set ρ : U →* MulAut (projectiveSL 3 K) := (conjAut 3 K).comp U.subtype
  have hρrange : ρ.range = linearAutGroup 3 K := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact conjAut_mem_linearAutGroup a.1
    · intro hx
      rw [linearAutGroup_eq_range] at hx
      obtain ⟨A, rfl⟩ := hx
      exact ⟨⟨A, Subgroup.mem_top A⟩, rfl⟩
  have hker : ∀ A : U, ρ A = 1 ↔
      (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]
    exact conjAut_eq_one_iff (le_refl 3) (A : GL (Fin 3) K)
  have hEρ : E ≤ ρ.range := by rw [hρrange]; exact hE
  have hcard := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
    (n := 3) (K := K) hp hp2 hdiv (by norm_num : 0 < 3) U ρ hker E hEρ hEea
  simpa using hcard

private theorem pRank_linearAutGroup_three_le_two_of_not_dvd {K : Type} [Field K] [Finite K]
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hK : Nat.card K = q)
    (hpq : q ≠ p) (hndiv : ¬ p ∣ Nat.card Kˣ) :
    CFSG.Open.pRank p (linearAutGroup 3 K) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have hndvd : ¬ p ∣ Nat.card K - 1 := by
    rwa [← Nat.card_units]
  have he2 : 2 ≤ orderOf (Nat.card K : ZMod p) :=
    CFSG.RankThree.PartOne.KCLinComm.two_le_orderOf_natCast hp
      (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α := K)).ne') hpK hndvd
  have hgl : CFSG.Open.pRank p (⊤ : Subgroup (GL (Fin 3) K)) ≤ 2 := by
    rw [CFSG.GroupTheory.WeirSylow.pRank_top_gl_eq (ι := Fin 3) hpodd hpK,
      Fintype.card_fin]
    have h1 : 3 / orderOf (Nat.card K : ZMod p) ≤ 3 / 2 :=
      Nat.div_le_div_left he2 (by norm_num)
    norm_num at h1
    omega
  have hstated : CFSG.Open.pRank p
      (⊤ : Subgroup (StatedProj (⊤ : Subgroup (GL (Fin 3) K)))) ≤ 2 := by
    rw [CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_eq (ι := Fin 3) (K := K)
      (H := ⊤) (d := Nat.card K - 1) hndvd (fun c _ => by
        rw [← Nat.card_units]; exact pow_card_eq_one')]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (Subgroup.topEquiv (G := GL (Fin 3) K))]
    exact hgl
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (CFSG.Quasithin.A318P.pglEquivLinearAut K)
  calc CFSG.Open.pRank p (linearAutGroup 3 K)
      = CFSG.Open.pRank p (⊤ : Subgroup (linearAutGroup 3 K)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
    _ = CFSG.Open.pRank p
        (⊤ : Subgroup (StatedProj (⊤ : Subgroup (GL (Fin 3) K)))) := heq.symm
    _ ≤ 2 := hstated

private theorem pRank_mulAut_projectiveSL_three_le_two {K : Type} [Field K] [Finite K]
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hK : Nat.card K = q)
    (hpq : q ≠ p) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut (projectiveSL 3 K))) ≤ 2 := by
  have hidx := index_linearAutGroup_three_dvd_two hq hK
  have hnotdvd : ¬ p ∣ (linearAutGroup 3 K).index := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · rw [h]; exact hp.not_dvd_one
    · rw [h]; exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  refine (CFSG.SectionRank.pRank_top_le_of_not_dvd_index hp (linearAutGroup 3 K)
    hnotdvd).trans ?_
  by_cases hdiv : p ∣ Nat.card Kˣ
  · exact pRank_linearAutGroup_three_le_two_of_dvd hp hp2 hdiv
  · exact pRank_linearAutGroup_three_le_two_of_not_dvd hp hp2 hq hK hpq hdiv

private theorem index_inner_statedProj_statedSp_two_dvd_two {K : Type} [Field K] [Finite K]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hK : Nat.card K = q) :
    (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 K))).index ∣ 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = q ^ 1 := by rw [hK, pow_one]
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP K q := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have h2 : (2 : K) ≠ 0 := by
    refine Ring.two_ne_zero ?_
    rw [ringChar.eq K q]
    exact hq2
  obtain ⟨hgenTop, -⟩ := CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two
    (K := K) h2
  haveI : Subsingleton (K ≃+* K) :=
    CFSG.RankThree.PartOne.CTP.subsingleton_ringEquiv_of_card_eq_prime hK
  have hDtop : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup 2 K = ⊤ := by
    rw [eq_top_iff]
    intro x hx
    have hxE : x ∈
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup 2 K := by
      rw [hgenTop]; exact Subgroup.mem_top x
    obtain ⟨σ, hσ⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.exists_fieldAut_inv_mul_mem
        (r := 2) (K := K) (x := x) hxE
    rw [Subsingleton.elim σ 1, map_one, inv_one, one_mul] at hσ
    exact hσ
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.relIndex_inner_spLinearAutGroup_dvd
    (r := 2) (p := q) (f := 1) hq (by norm_num) hK'
  have hidxeq : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 K))).index =
      (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 K))).relIndex
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup 2 K) := by
    rw [hDtop, ← Subgroup.relIndex_mul_index
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 K)))
      (K := (⊤ : Subgroup (MulAut (StatedProj (StatedSp 2 K))))) le_top,
      Subgroup.index_top, mul_one]
  rw [hidxeq]
  exact h.trans (Nat.gcd_dvd_left 2 _)

private theorem pRank_statedProj_statedSp_two_le_two {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp 2 K))) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsp := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_Sp_formula
    (n := 2) (F := K) hp hp2 hpK
  rw [hsp]
  have hmain : ∀ e : ℕ, (if Even e then 2 * 2 else 2) / e ≤ 2 := by
    intro e
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he]; norm_num
    · rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr he.ne') with he1 | he2
      · rw [← he1]; norm_num
      · have hnum : (if Even e then 2 * 2 else 2) ≤ 4 := by split_ifs <;> omega
        calc (if Even e then 2 * 2 else 2) / e ≤ 4 / e := Nat.div_le_div_right hnum
          _ ≤ 4 / 2 := Nat.div_le_div_left (by omega : 2 ≤ e) (by norm_num)
          _ = 2 := by norm_num
  exact hmain _

private theorem pRank_mulAut_statedSp_two_le_two {K : Type} [Field K] [Finite K]
    {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (hK : Nat.card K = q) (hpq : q ≠ p) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut (StatedProj (StatedSp 2 K)))) ≤ 2 := by
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have hdvd := index_inner_statedProj_statedSp_two_dvd_two hq hq2 hK
  have hnotdvd : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 K))).index := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · rw [h]; exact hp.not_dvd_one
    · rw [h]; exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  refine (CFSG.SectionRank.pRank_top_le_of_not_dvd_index hp
    (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 K))) hnotdvd).trans ?_
  have hZ := CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot
    (r := 2) (k := K) (by norm_num)
  have hinner : CFSG.Open.pRank p
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp 2 K))) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.innerAutEquiv hZ)).symm
  rw [hinner]
  exact pRank_statedProj_statedSp_two_le_two hp hp2 hpK

theorem card_lt_of_elemAbelian_mulAut_linThree {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : q ≠ p) {S : Type} [Group S] [Finite S]
    {d : TauCeti.ValidLieTypeIndex} (e : S ≃* CFSG.AGLEmbedding.CatGroup d)
    {Q : TauCeti.PrimePower} (hQ : Q.p = q) (hQ1 : Q.exponent = 1) (hd : d.1 = .A 2 Q)
    {A : Subgroup (MulAut S)} (hA : CFSG.Open.IsElemAbelian p A) :
    Nat.card A < p ^ 3 := by
  classical
  have hq : q.Prime := hQ ▸ Q.prime_p
  haveI : Fact q.Prime := ⟨hq⟩
  have hv : (TauCeti.LieTypeIndex.A 2 Q).Valid := hd ▸ d.2
  have hdeq : d = ⟨TauCeti.LieTypeIndex.A 2 Q, hv⟩ := by
    cases d
    simp only at hd
    subst hd
    rfl
  subst hdeq
  have hk : Nat.card (GaloisField q 1) = Q.card := by
    rw [GaloisField.card q 1 (by norm_num), TauCeti.PrimePower.card_def, hQ, hQ1, pow_one]
  obtain ⟨e₁⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := 2) (k := GaloisField q 1) Q hv hk
  let e' : S ≃* projectiveSL 3 (GaloisField q 1) := e.trans e₁.symm
  let A' : Subgroup (MulAut (projectiveSL 3 (GaloisField q 1))) :=
    A.map (MulAut.congr e').toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian p A' :=
    CFSG.SectionRank.isElemAbelian_map hA (MulAut.congr e').toMonoidHom
  have hcard' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e').injective
  have hKq : Nat.card (GaloisField q 1) = q := by
    rw [GaloisField.card q 1 (by norm_num), pow_one]
  have hrank := pRank_mulAut_projectiveSL_three_le_two (K := GaloisField q 1)
    hp hp2 hq hKq hpq
  have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le
    (G := MulAut (projectiveSL 3 (GaloisField q 1))) hp hrank A' hA'
  rw [← hcard']
  calc Nat.card A' ≤ p ^ 2 := hbound
    _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

theorem card_lt_of_elemAbelian_mulAut_spFour {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : q ≠ p) {S : Type} [Group S] [Finite S]
    {d : TauCeti.ValidLieTypeIndex} (e : S ≃* CFSG.AGLEmbedding.CatGroup d)
    {Q : TauCeti.PrimePower} (hQ : Q.p = q) (hQ1 : Q.exponent = 1) (hd : d.1 = .B 2 Q)
    {A : Subgroup (MulAut S)} (hA : CFSG.Open.IsElemAbelian p A) :
    Nat.card A < p ^ 3 := by
  classical
  have hq : q.Prime := hQ ▸ Q.prime_p
  haveI : Fact q.Prime := ⟨hq⟩
  have hv : (TauCeti.LieTypeIndex.B 2 Q).Valid := hd ▸ d.2
  have hdeq : d = ⟨TauCeti.LieTypeIndex.B 2 Q, hv⟩ := by
    cases d
    simp only at hd
    subst hd
    rfl
  subst hdeq
  have hk : Nat.card (GaloisField q 1) = Q.card := by
    rw [GaloisField.card q 1 (by norm_num), TauCeti.PrimePower.card_def, hQ, hQ1, pow_one]
  obtain ⟨e₁⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
    (q := Q) hv (k := GaloisField q 1) hk
  let e' : S ≃* StatedProj (StatedSp 2 (GaloisField q 1)) := e.trans e₁.symm
  let A' : Subgroup (MulAut (StatedProj (StatedSp 2 (GaloisField q 1)))) :=
    A.map (MulAut.congr e').toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian p A' :=
    CFSG.SectionRank.isElemAbelian_map hA (MulAut.congr e').toMonoidHom
  have hcard' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.congr e').injective
  have hKq : Nat.card (GaloisField q 1) = q := by
    rw [GaloisField.card q 1 (by norm_num), pow_one]
  have hrank := pRank_mulAut_statedSp_two_le_two (K := GaloisField q 1)
    hp hp2 hq hq2 hKq hpq
  have hbound := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_pRank_le
    (G := MulAut (StatedProj (StatedSp 2 (GaloisField q 1)))) hp hrank A' hA'
  rw [← hcard']
  calc Nat.card A' ≤ p ^ 2 := hbound
    _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.H248
