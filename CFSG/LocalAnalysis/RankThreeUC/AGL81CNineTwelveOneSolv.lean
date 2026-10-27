module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

@[expose] def KFactAutRankThreeSolvable : Prop :=
  ∀ (r : ℕ) (R : Type) [Group R] [Finite R], r.Prime → r ≠ 2 → IsPGroup r R →
    CFSG.Open.pRank r (⊤ : Subgroup R) ≤ 3 →
    ∀ B : Subgroup (MulAut R), Nat.Coprime 3 (Nat.card B) → Group.IsSolvable ↥B

private lemma ker_conjNormal_eq_centralizer {G : Type*} [Group G] {H : Subgroup G} [H.Normal] :
    (MulAut.conjNormal (H := H)).ker = Subgroup.centralizer (H : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg x hx
    have h1 : (MulAut.conjNormal (H := H) g) ⟨x, hx⟩ = (1 : MulAut H) ⟨x, hx⟩ := by rw [hg]
    have h2 : g * x * g⁻¹ = x := by
      simpa using congrArg Subtype.val h1
    calc x * g = (g * x * g⁻¹) * g := by rw [h2]
      _ = g * x := by simp [mul_assoc]
  · intro hg
    ext v
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    have hv := hg v v.2
    rw [← hv, mul_assoc, mul_inv_cancel, mul_one]

theorem isSolvable_of_layer_eq_bot (hK3 : KFactAutRankThreeSolvable) {Z : Type} [Group Z]
    [Finite Z] (h2 : CFSG.pCore 2 Z = ⊥) (hE : CFSG.layer Z = ⊥)
    (h3 : Nat.Coprime 3 (Nat.card Z))
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup Z) ≤ 3) :
    Group.IsSolvable Z := by
  classical
  let V : ℕ → Subgroup Z := fun r => CFSG.pCore r Z
  let C : ℕ → Subgroup Z := fun r => (MulAut.conjNormal (H := V r)).ker
  let K : Subgroup Z := ⨅ r : (Nat.card Z).primeFactors, C (r : ℕ)
  have hker : ∀ r : ℕ, C r = Subgroup.centralizer (V r : Set Z) := by
    intro r
    dsimp only [C, V]
    exact ker_conjNormal_eq_centralizer
  have hquot : ∀ r : (Nat.card Z).primeFactors,
      Group.IsSolvable (Z ⧸ C (r : ℕ)) := by
    intro r
    by_cases hr2 : (r : ℕ) = 2
    · rw [hr2]
      have hC2 : C 2 = ⊤ := by
        rw [hker 2, show V 2 = ⊥ from h2]
        exact Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
      have he : Z ⧸ C 2 ≃* Z ⧸ (⊤ : Subgroup Z) := QuotientGroup.quotientMulEquivOfEq hC2
      haveI : Subsingleton (Z ⧸ (⊤ : Subgroup Z)) := QuotientGroup.subsingleton_quotient_top
      exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv he.symm
    · have hr : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.2
      have hV : IsPGroup (r : ℕ) ↥(V (r : ℕ)) := CFSG.pCore_isPGroup
      have hrank : CFSG.Open.pRank (r : ℕ) (⊤ : Subgroup ↥(V (r : ℕ))) ≤ 3 := by
        have hmap : (⊤ : Subgroup ↥(V (r : ℕ))).map (V (r : ℕ)).subtype = V (r : ℕ) := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
        calc CFSG.Open.pRank (r : ℕ) (⊤ : Subgroup ↥(V (r : ℕ)))
            ≤ CFSG.Open.pRank (r : ℕ)
                ((⊤ : Subgroup ↥(V (r : ℕ))).map (V (r : ℕ)).subtype) :=
              CFSG.SectionRank.pRank_le_map hr.one_lt (V (r : ℕ)).subtype
                (V (r : ℕ)).subtype_injective ⊤
          _ = CFSG.Open.pRank (r : ℕ) (V (r : ℕ)) := by rw [hmap]
          _ ≤ CFSG.Open.pRank (r : ℕ) (⊤ : Subgroup Z) :=
              CFSG.SectionRank.pRank_mono hr.one_lt le_top
          _ ≤ 3 := hrk (r : ℕ) hr hr2
      let B : Subgroup (MulAut ↥(V (r : ℕ))) := (MulAut.conjNormal (H := V (r : ℕ))).range
      have he : Z ⧸ C (r : ℕ) ≃* B :=
        QuotientGroup.quotientKerEquivRange (MulAut.conjNormal (H := V (r : ℕ)))
      have hBcop : Nat.Coprime 3 (Nat.card B) := by
        have hcard : Nat.card B = Nat.card (Z ⧸ C (r : ℕ)) :=
          (Nat.card_congr he.toEquiv).symm
        rw [hcard]
        exact h3.of_dvd_right (Subgroup.card_quotient_dvd_card (C (r : ℕ)))
      haveI hBsolv : Group.IsSolvable ↥B :=
        hK3 (r : ℕ) ↥(V (r : ℕ)) hr hr2 hV hrank B hBcop
      exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv he.symm
  have hKleC : ∀ r : (Nat.card Z).primeFactors, K ≤ C (r : ℕ) := fun r => iInf_le _ r
  have hcentV : ∀ r : (Nat.card Z).primeFactors,
      V (r : ℕ) ≤ Subgroup.centralizer (K : Set Z) := by
    intro r
    rw [Subgroup.le_centralizer_iff, ← hker (r : ℕ)]
    exact hKleC r
  have hcentFit : K ≤ Subgroup.centralizer (CFSG.fittingSubgroup Z : Set Z) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact (Subgroup.le_centralizer_iff).mpr (iSup_le hcentV)
  have hbender : Subgroup.centralizer (CFSG.fittingSubgroup Z : Set Z) ≤
      CFSG.fittingSubgroup Z := by
    have hgen : CFSG.generalizedFitting Z = CFSG.fittingSubgroup Z := by
      rw [CFSG.generalizedFitting.eq_sup, hE, sup_bot_eq]
    rw [← hgen]
    exact CFSG.centralizer_generalizedFitting_le Z
  have hKfit : K ≤ CFSG.fittingSubgroup Z := hcentFit.trans hbender
  haveI hKsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKfit)
  haveI hKnormal : K.Normal := by
    dsimp only [K]
    exact Subgroup.normal_iInf_normal (fun r => by
      dsimp only [C]
      exact MonoidHom.normal_ker _)
  haveI hKquot : Group.IsSolvable (Z ⧸ K) := by
    have hderiv : ∀ r : (Nat.card Z).primeFactors,
        ∃ n, derivedSeries Z n ≤ C (r : ℕ) := by
      intro r
      obtain ⟨n, hn⟩ := (Group.isSolvable_def _).mp (hquot r)
      refine ⟨n, ?_⟩
      have hmap : (derivedSeries Z n).map (QuotientGroup.mk' (C (r : ℕ))) = ⊥ := by
        rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective (C (r : ℕ))) n, hn]
      simpa [QuotientGroup.ker_mk'] using
        (Subgroup.map_eq_bot_iff (derivedSeries Z n)).mp hmap
    let n : (Nat.card Z).primeFactors → ℕ := fun r => Classical.choose (hderiv r)
    have hn : ∀ r, derivedSeries Z (n r) ≤ C (r : ℕ) :=
      fun r => Classical.choose_spec (hderiv r)
    let N : ℕ := Finset.univ.sup n
    have hNle : derivedSeries Z N ≤ K := by
      refine le_iInf (fun r => ?_)
      exact (derivedSeries_antitone Z (Finset.le_sup (f := n) (Finset.mem_univ r))).trans
        (hn r)
    refine (Group.isSolvable_def (Z ⧸ K)).mpr ⟨N, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective K) N, Subgroup.map_eq_bot_iff]
    simpa [QuotientGroup.ker_mk'] using hNle
  exact Group.isSolvable_of_subgroup_quotient K

theorem isSolvable_pPrimeCore_three (hK3 : KFactAutRankThreeSolvable) {Y : Type} [Group Y]
    [Finite Y] (h2 : CFSG.pCore 2 Y = ⊥) (hE : CFSG.layer ↥(CFSG.pPrimeCore 3 Y) = ⊥)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (CFSG.pPrimeCore 3 Y) ≤ 3) :
    Group.IsSolvable ↥(CFSG.pPrimeCore 3 Y) := by
  let X : Subgroup Y := CFSG.pPrimeCore 3 Y
  have h2' : CFSG.pCore 2 ↥X = ⊥ := by
    let P : Subgroup ↥X := CFSG.pCore 2 ↥X
    have hPmap_normal : (P.map X.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal (H := X) (K := P)
    have hPmap_pgroup : IsPGroup 2 (P.map X.subtype) :=
      IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) X.subtype
    have hle : P.map X.subtype ≤ CFSG.pCore 2 Y := le_sSup ⟨hPmap_normal, hPmap_pgroup⟩
    have hbot : P.map X.subtype = ⊥ := le_antisymm (hle.trans (le_of_eq h2)) bot_le
    exact (Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).mp hbot
  have hrk' : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r (⊤ : Subgroup ↥X) ≤ 3 := by
    intro r hr hr2
    have hmap : (⊤ : Subgroup ↥X).map X.subtype = X := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    calc CFSG.Open.pRank r (⊤ : Subgroup ↥X)
        ≤ CFSG.Open.pRank r ((⊤ : Subgroup ↥X).map X.subtype) :=
          CFSG.SectionRank.pRank_le_map hr.one_lt X.subtype X.subtype_injective ⊤
      _ = CFSG.Open.pRank r X := by rw [hmap]
      _ ≤ 3 := hrk r hr hr2
  exact isSolvable_of_layer_eq_bot hK3 h2' hE
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := Y)) hrk'

theorem nonempty_quot_solvableRadical_mulEquiv {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    [N.Normal] (hN : Group.IsSolvable ↥N) (hq : CFSG.IsQuasisimple (Y ⧸ N)) {S : Type*} [Group S]
    (e : ((Y ⧸ N) ⧸ center (Y ⧸ N)) ≃* S) :
    Nonempty ((Y ⧸ CFSG.solvableRadical Y) ≃* S) := by
  classical
  let Q := Y ⧸ N
  let P : Subgroup Y := (center Q).comap (QuotientGroup.mk' N)
  let R : Subgroup Y := CFSG.solvableRadical Y
  haveI : Group.IsSolvable ↥N := hN
  haveI hPnormal : P.Normal :=
    Subgroup.Normal.comap (inferInstance : (center Q).Normal) (QuotientGroup.mk' N)
  have hPsolv : Group.IsSolvable ↥P :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_comap_mk' (R := N) (N := center Q)
  have hPleR : P ≤ R :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hPnormal hPsolv
  have hRmap_normal : (R.map (QuotientGroup.mk' N)).Normal :=
    (inferInstance : R.Normal).map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  haveI hRsolv : Group.IsSolvable ↥R :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hRmap_le : R.map (QuotientGroup.mk' N) = ⊤ ∨ R.map (QuotientGroup.mk' N) ≤ center Q :=
    CFSG.LocalCores.quasisimple_normal_subgroups hq hRmap_normal
  haveI hqperf : Group.IsPerfect Q := hq.1
  have hRleP : R ≤ P := by
    rcases hRmap_le with htop | hle
    · exfalso
      let f : R →* Q := (QuotientGroup.mk' N).comp R.subtype
      have hrange : f.range = R.map (QuotientGroup.mk' N) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨y, y.2, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
      haveI hQsolv : Group.IsSolvable Q :=
        Group.isSolvable_of_surjective (f := f) (MonoidHom.range_eq_top.mp (hrange.trans htop))
      have hQsolvQ : Group.IsSolvable (Q ⧸ center Q) := inferInstance
      haveI : Nontrivial (Q ⧸ center Q) := by
        obtain ⟨a, b, hab⟩ := hq.2.2
        exact ⟨a, b, fun h => hab (by rw [h])⟩
      exact (Group.IsPerfect.not_isSolvable (Q ⧸ center Q)) hQsolvQ
    · rwa [Subgroup.map_le_iff_le_comap] at hle
  have hRP : R = P := le_antisymm hRleP hPleR
  have hNP : N ≤ P := by
    rw [← Subgroup.map_le_iff_le_comap]
    have hkerN : N ≤ (QuotientGroup.mk' N).ker := by rw [QuotientGroup.ker_mk']
    rw [show N.map (QuotientGroup.mk' N) = ⊥ from (Subgroup.map_eq_bot_iff N).mpr hkerN]
    exact bot_le
  have hPmap : P.map (QuotientGroup.mk' N) = center Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) (center Q)
  haveI : (P.map (QuotientGroup.mk' N)).Normal :=
    hPnormal.map (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hRP).trans
    ((QuotientGroup.quotientQuotientEquivQuotient N P hNP).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hPmap).trans e))⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
