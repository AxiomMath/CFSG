module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeYTransportCore
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3Quot
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.DResidualSimple
import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCPar
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreBasic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
import CFSG.LocalAnalysis.AGL81I.Section3.SL3BorelOvergroups
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.LocalAnalysis.AGL81I.Section3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem oPPrimeHull_mono {X : Type*} [Group X] {d : ℕ} {A B : Subgroup X}
    (h : A ≤ B) : oPPrimeHull d A ≤ oPPrimeHull d B := by
  rw [oPPrimeHull, oPPrimeHull]
  exact Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

private theorem oPPrimeHull_top_le_of_normal_of_isSylowOf {A : Type} [Group A] [Finite A]
    {d : ℕ} [Fact d.Prime] {I D : Subgroup A} (hI : I.Normal)
    (hD : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hDI : D ≤ I) :
    oPPrimeHull d (⊤ : Subgroup A) ≤ I := by
  classical
  haveI : I.Normal := hI
  have hDindex : ¬ d ∣ D.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hD).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hIindex : ¬ d ∣ I.index := fun h =>
    hDindex (h.trans (Subgroup.index_dvd_of_le hDI))
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨-, k, hk⟩
  have hx : QuotientGroup.mk' I x = 1 := by
    have hdvd1 : orderOf (QuotientGroup.mk' I x) ∣ d ^ k := hk ▸ orderOf_map_dvd _ x
    have hdvd2 : orderOf (QuotientGroup.mk' I x) ∣ I.index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (d ^ k) I.index :=
      ((Fact.out : d.Prime).coprime_iff_not_dvd.mpr hIindex).pow_left k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  exact (QuotientGroup.eq_one_iff x).mp hx

private theorem oPPrimeHull_inf_eq_of_isSylowOf {A : Type} [Group A] [Finite A] {d : ℕ}
    [Fact d.Prime] {I D : Subgroup A} (hI : I.Normal)
    (hD : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hDI : D ≤ I) (X : Subgroup A) :
    oPPrimeHull d (X ⊓ I) = oPPrimeHull d X := by
  have hXI : oPPrimeHull d X ≤ I :=
    (oPPrimeHull_mono le_top).trans (oPPrimeHull_top_le_of_normal_of_isSylowOf hI hD hDI)
  refine le_antisymm (oPPrimeHull_mono inf_le_left) ?_
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxX, k, hk⟩
  have hxmem : x ∈ oPPrimeHull d X := Subgroup.subset_closure ⟨hxX, k, hk⟩
  exact Subgroup.subset_closure ⟨⟨hxX, hXI hxmem⟩, k, hk⟩

private theorem not_dvd_sub_one_of_dvd_add_one {p d : ℕ} (hp : p.Prime) (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) : ¬ d ∣ p - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  intro h
  have h2 : d ∣ (p + 1) - (p - 1) := Nat.dvd_sub hdp h
  rw [show p + 1 - (p - 1) = 2 by omega] at h2
  exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp h2)

private theorem not_dvd_card_inf_center_sl3 {p d : ℕ} [Fact p.Prime] (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1)
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) :
    ¬ d ∣ Nat.card ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) ⊓ X) := by
  have hdvd : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) ∣ p - 1 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    simpa [Nat.card_zmod] using
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd (K := ZMod p) (n := 3)
        (by norm_num))
  refine fun h => not_dvd_sub_one_of_dvd_add_one Fact.out hd hd2 hdp ?_
  exact (h.trans (Subgroup.card_dvd_of_le
    (H := Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) ⊓ X)
    (K := Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) inf_le_left)).trans hdvd

private theorem isMaxParabolicP_map_subgroupOf {A : Type} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] {I P : Subgroup A}
    (e : ↥I ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (hP : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p I P) :
    CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))
      ((P.subgroupOf I).map e.toMonoidHom) := by
  classical
  obtain ⟨⟨U, hUnorm⟩, hP₀ne, hP₀max⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC.parData_of_isMaxParabolicP hP
  let U₁ : Sylow p (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :=
    U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hU₁coe : (U₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) =
      (U : Subgroup ↥I).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective U
  have hnorm : Subgroup.normalizer (U₁ : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) ≤
      (P.subgroupOf I).map e.toMonoidHom := by
    have h := Subgroup.map_mono (f := e.toMonoidHom) hUnorm
    rwa [Subgroup.map_equiv_normalizer_eq (U : Subgroup ↥I) e, ← hU₁coe] at h
  have hpar : CFSG.GH74.GLS.Stage2.Signalizer.IsParabolicP p
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))
      ((P.subgroupOf I).map e.toMonoidHom) := by
    refine ⟨le_top, U₁, ?_, by simpa using hnorm⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, U₁.isPGroup', by simpa using U₁.not_dvd_index⟩
  have hne : (P.subgroupOf I).map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hP₀ne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [htop, Subgroup.map_top_of_surjective _ e.surjective]
  refine ⟨hpar, hne, ?_⟩
  intro Q _ hQne hPQ
  have hQ' : Q.comap e.toMonoidHom = P.subgroupOf I := by
    refine hP₀max _ ?_ ?_
    · intro x hx
      exact hPQ (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    · intro htop
      apply hQne
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q, htop,
        Subgroup.map_top_of_surjective _ e.surjective]
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q, hQ']

private theorem exists_conj_eq_flagStabilizer_of_isMaxParabolicP {p : ℕ} [Fact p.Prime]
    {P₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))}
    (hP₁ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) P₁) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) (i : ℕ), (i = 1 ∨ i = 2) ∧
      P₁.map (MulAut.conj g⁻¹).toMonoidHom =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 3 (ZMod p)
          ({i} : Set ℕ) := by
  classical
  obtain ⟨-, U, hU, hUnorm⟩ := hP₁.1
  have hnorm : Subgroup.normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) ≤ P₁ := by
    simpa using hUnorm
  let Q : Sylow p (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :=
    hU.isPGroup.toSylow (by
      rw [← Subgroup.relIndex_top_right]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hU).2.2)
  have hQcoe : (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) = U :=
    hU.isPGroup.toSylow_coe (by
      rw [← Subgroup.relIndex_top_right]
      exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hU).2.2)
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.AGL81I.Section3.exists_conj_borel_eq_normalizer Q
  have hg' : Subgroup.normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) =
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 (ZMod p)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hQcoe]; exact hg
  have hle : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 (ZMod p)).map
      (MulAut.conj g).toMonoidHom ≤ P₁ := by
    rw [← hg']; exact hnorm
  have hBle : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 3 (ZMod p) ≤
      P₁.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rwa [Subgroup.map_map,
      show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
        = MonoidHom.id _ from MonoidHom.ext fun x => by
          change (MulAut.conj g⁻¹) ((MulAut.conj g) x) = x
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group,
      Subgroup.map_id] at h2
  have hP₂ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))
      (P₁.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.isMaxParabolicP_map
      (MulAut.conj g⁻¹) p hP₁
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h
  rcases (CFSG.LocalAnalysis.AGL81I.Section3.isMaxParabolicP_sl3_zmod_iff
    (Y := P₁.map (MulAut.conj g⁻¹).toMonoidHom) hBle).mp hP₂ with h | h
  · exact ⟨g, 1, Or.inl rfl, h⟩
  · exact ⟨g, 2, Or.inr rfl, h⟩

theorem isPSLType_two_modPrimeComplement_oPPrimeHull_of_isMaxParabolicP {A : Type}
    [Group A] [Finite A] {p d : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) {I P : Subgroup A}
    (e : ↥I ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (hP : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p I P) :
    IsPSLType 2 (ZMod p) (modPrimeComplement d (oPPrimeHull d P)) := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  have hPI : P ≤ I := hP.1.1
  let P₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :=
    (P.subgroupOf I).map e.toMonoidHom
  have hP₁ : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))) P₁ :=
    isMaxParabolicP_map_subgroupOf e hP
  obtain ⟨g, i, hi, hP₂eq⟩ := exists_conj_eq_flagStabilizer_of_isMaxParabolicP hP₁
  let P₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :=
    P₁.map (MulAut.conj g⁻¹).toMonoidHom
  let Y : Subgroup (PSL(3, ZMod p)) := P₂.map
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))))
  have hZle : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) ≤ P₂ := by
    dsimp only [P₂]
    rw [hP₂eq, ← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_flagStabilizer 3 (ZMod p) _
  have hYcomap : Y.comap (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 3 (ZMod p) ({i} : Set ℕ) := by
    rw [show Y = P₂.map _ from rfl,
      Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hZle)]
    exact hP₂eq
  have hPSL : IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d Y) :=
    isPSLType_two_oPrimeModPrimeComplement_of_comap_eq_flagStabilizer hp5 hd hd2 hdp hi hYcomap
  obtain ⟨e₁⟩ := nonempty_oPrimeModPrimeComplement_mulEquiv (G := PSL(3, ZMod p)) hd Y
  have hmap : (oPPrimeHull d P₂).map (QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))) = oPPrimeHull d Y := by
    rw [show Y = P₂.map _ from rfl, S631.map_oPPrimeHull]
  have hkerπ : ¬ d ∣ Nat.card ↥((QuotientGroup.mk' (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 3) (ZMod p)))).ker ⊓ oPPrimeHull d P₂) := by
    rw [QuotientGroup.ker_mk']
    exact not_dvd_card_inf_center_sl3 hd hd2 hdp _
  obtain ⟨e₂⟩ := nonempty_modPrimeComplement_mulEquiv_of_map hd
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod p))))
    hmap hkerπ
  obtain ⟨e₃⟩ := nonempty_oPrimeModPrimeComplement_mulEquiv
    (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) hd P₂
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.AGL81I.Section3.oPrimeModPrimeComplement_congr d
    (Subgroup.equivMapOfInjective P₁ (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm
  obtain ⟨e₅⟩ := CFSG.LocalAnalysis.AGL81I.Section3.oPrimeModPrimeComplement_congr d
    ((Subgroup.equivMapOfInjective (P.subgroupOf I) e.toMonoidHom e.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hPI))
  obtain ⟨e₆⟩ := nonempty_oPrimeModPrimeComplement_mulEquiv (G := A) hd P
  exact ⟨(e₁.trans (e₂.symm.trans (e₃.symm.trans (e₄.trans (e₅.trans e₆))))).symm.trans
    hPSL.some⟩

theorem twelveThreeYQuotient_of_isMaxParabolicP {M H : Subgroup G} {p d : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1)
    {A : Type} [Group A] [Finite A] (π : ↥H →* A) (hN : ¬ d ∣ Nat.card π.ker)
    {I P D : Subgroup A} (hI : I.Normal)
    (e : ↥I ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (hP : CFSG.GH74.GLS.Stage2.Signalizer.IsMaxParabolicP p I P)
    (hPeq : P = ((M ⊓ H).subgroupOf H).map π ⊓ I)
    (hD : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hDI : D ≤ I) :
    TwelveThreeYQuotient G M H p d := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let X : Subgroup A := ((M ⊓ H).subgroupOf H).map π
  have hPeq' : P = X ⊓ I := hPeq
  have hHull_eq : oPPrimeHull d X = oPPrimeHull d P := by
    rw [hPeq']
    exact (oPPrimeHull_inf_eq_of_isSylowOf hI hD hDI X).symm
  have hPSL : IsPSLType 2 (ZMod p) (modPrimeComplement d (oPPrimeHull d P)) :=
    isPSLType_two_modPrimeComplement_oPPrimeHull_of_isMaxParabolicP (A := A)
      hp5 hd hd2 hdp e hP
  let A₀ : Subgroup ↥H := oPPrimeHull d ((M ⊓ H).subgroupOf H)
  have hAmap : A₀.map H.subtype = oPPrimeHull d (M ⊓ H) := by
    dsimp only [A₀]
    rw [S631.map_oPPrimeHull,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : M ⊓ H ≤ H)]
  let eA : ↥A₀ ≃* ↥(oPPrimeHull d (M ⊓ H)) :=
    (Subgroup.equivMapOfInjective A₀ H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hAmap)
  have hmapA : A₀.map π = oPPrimeHull d X := by
    dsimp only [A₀, X]
    rw [S631.map_oPPrimeHull]
  have hkerA : ¬ d ∣ Nat.card ↥(π.ker ⊓ A₀) := fun h => hN
    (h.trans (Subgroup.card_dvd_of_le (H := π.ker ⊓ A₀) (K := π.ker) inf_le_left))
  obtain ⟨eNat⟩ := nonempty_modPrimeComplement_mulEquiv_of_map (G := ↥H) hd π hmapA hkerA
  obtain ⟨eSub⟩ := nonempty_modPrimeComplement_congr (d := d) eA.symm
  have hgoalM : IsPSLType 2 (ZMod p)
      (modPrimeComplement d (oPPrimeHull d (M ⊓ H))) := by
    refine ⟨eSub.trans (eNat.trans ?_)⟩
    rw [hHull_eq]
    exact hPSL.some
  have hHM : oPPrimeHull d (H ⊓ M) = oPPrimeHull d (M ⊓ H) := by rw [inf_comm H M]
  obtain ⟨eHM⟩ := nonempty_modPrimeComplement_congr (d := d) (MulEquiv.subgroupCongr hHM)
  exact ⟨eHM.trans hgoalM.some⟩

theorem oPPrimeHull_subgroupOf_of_le {X : Type*} [Group X] [Finite X] {d : ℕ} [Fact d.Prime]
    {A K : Subgroup X} (hAK : A ≤ K) :
    (oPPrimeHull d A).subgroupOf K = oPPrimeHull d (A.subgroupOf K) := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr ((oPPrimeHull_le d A).trans hAK),
    S631.map_oPPrimeHull, Subgroup.map_subgroupOf_eq_of_le hAK]

private theorem factorization_card_starImg_eq {M H : Subgroup G} {p d : ℕ} (hd : d.Prime)
    (hO : ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p))
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    (Nat.card (starImg p H D)).factorization d =
      (Nat.card (starImg p H M)).factorization d := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  have hDle : D ≤ H ⊓ M := hD.le
  have hfact1 : (Nat.card (starImg p H D)).factorization d =
      (Nat.card (D.subgroupOf H)).factorization d := by
    have hker : ¬ d ∣ Nat.card ↥(π.subgroupMap (D.subgroupOf H)).ker := by
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
      exact fun h => hO (h.trans (CFSG.OddStandard.SmallF3.Omega.card_subgroupOf_dvd _ _))
    exact CFSG.GroupTheory.factorization_eq_of_surjective_ker_not_dvd
      (π.subgroupMap (D.subgroupOf H)) (MonoidHom.subgroupMap_surjective π _) hker
  have hfact2 : (Nat.card (D.subgroupOf H)).factorization d =
      (Nat.card (starImg p H M)).factorization d := by
    have h1 : (Nat.card (D.subgroupOf H)).factorization d = (Nat.card D).factorization d := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDle.trans inf_le_left)).toEquiv]
    have h2 : (Nat.card D).factorization d = (Nat.card ↥(H ⊓ M)).factorization d := by
      rw [hD.card_eq, Nat.factorization_pow_self hd]
    have h3 : (Nat.card ↥(H ⊓ M)).factorization d =
        (Nat.card (starImg p H M)).factorization d := by
      have hker : ¬ d ∣ Nat.card ↥(π.subgroupMap ((H ⊓ M).subgroupOf H)).ker := by
        rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
        exact fun h => hO (h.trans (CFSG.OddStandard.SmallF3.Omega.card_subgroupOf_dvd _ _))
      have h := CFSG.GroupTheory.factorization_eq_of_surjective_ker_not_dvd
        (p := d) (f := π.subgroupMap ((H ⊓ M).subgroupOf H))
        (MonoidHom.subgroupMap_surjective π _) hker
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : H ⊓ M ≤ H)).toEquiv] at h
      rw [show ((H ⊓ M).subgroupOf H).map π = starImg p H M from by
        rw [Subgroup.inf_subgroupOf_left]; rfl] at h
      exact h.symm
    exact h1.trans (h2.trans h3)
  exact hfact1.trans hfact2

private theorem isSylowOf_starImg {M H : Subgroup G} {p d : ℕ} (hd : d.Prime)
    (hO : ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p))
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf d (starImg p H D) (starImg p H M) := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hle : starImg p H D ≤ starImg p H M := by
    dsimp only [starImg]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (hD.le.trans inf_le_right))
  have hDp : IsPGroup d (starImg p H D) := by
    have h1 : IsPGroup d (D.subgroupOf H) :=
      hD.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe (hD.le.trans inf_le_left)).symm
    exact h1.map _
  have hcardDstar : Nat.card (starImg p H D) = d ^ (Nat.card (starImg p H M)).factorization d := by
    obtain ⟨n, hn⟩ := hDp.exists_card_eq
    have hcardEq : Nat.card (starImg p H D) =
        d ^ (Nat.card (starImg p H D)).factorization d := by
      rw [hn, Nat.factorization_pow_self hd]
    exact hcardEq.trans (by rw [factorization_card_starImg_eq hd hO hD])
  exact CFSG.ABGLocalTools.isSylowOf_of_card hle hcardDstar

theorem oPPrimeHull_inf_eq_of_isSylowOf_starImg {M H : Subgroup G} {p d : ℕ}
    (hd : d.Prime) (hO : ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p))
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M))
    {C : Subgroup (StarGroup p H)} (hDC : starImg p H D ≤ C)
    (hCn : starImg p H M ≤ Subgroup.normalizer (C : Set (StarGroup p H))) :
    oPPrimeHull d (starImg p H M ⊓ C) = oPPrimeHull d (starImg p H M) := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf d (starImg p H D) (starImg p H M) :=
    isSylowOf_starImg hd hO hD
  have hDS : CFSG.ABGLocalTools.IsSylowOf d ((starImg p H D).subgroupOf (starImg p H M)) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDsyl.le).toEquiv, Subgroup.card_top]
    exact hDsyl.card_eq
  have hCI : (C.subgroupOf (starImg p H M)).Normal := by
    have hN : starImg p H M ≤
        Subgroup.normalizer ((C ⊓ starImg p H M : Subgroup (StarGroup p H)) : Set _) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxC, hxM⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hCn hg) x).mp hxC,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x).mp hxM⟩
      · rintro ⟨hxC, hxM⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hCn hg) x).mpr hxC,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x).mpr hxM⟩
    rw [← Subgroup.inf_subgroupOf_right C (starImg p H M)]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hN
  have hHull_le : oPPrimeHull d (starImg p H M) ≤ C := by
    have h := Subgroup.map_mono (f := (starImg p H M).subtype)
      (oPPrimeHull_top_le_of_normal_of_isSylowOf hCI hDS
        (Subgroup.subgroupOf_mono (starImg p H M) hDC))
    rw [map_subtype_oPPrimeHull_top, Subgroup.subgroupOf_map_subtype] at h
    exact h.trans inf_le_left
  refine le_antisymm (oPPrimeHull_mono inf_le_left) ?_
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxM, k, hk⟩
  have hxmem : x ∈ oPPrimeHull d (starImg p H M) := Subgroup.subset_closure ⟨hxM, k, hk⟩
  exact Subgroup.subset_closure ⟨⟨hxM, hHull_le hxmem⟩, k, hk⟩

theorem nonempty_oPrimeModPrimeComplement_starImg_mulEquiv {M H : Subgroup G} {p d : ℕ}
    (hd : d.Prime) (hO : ¬ d ∣ Nat.card (primeComplementCore (G := ↥H) p))
    {D : Subgroup G} (hD : CFSG.ABGLocalTools.IsSylowOf d D (H ⊓ M))
    {C : Subgroup (StarGroup p H)} (hDC : starImg p H D ≤ C)
    (hCn : starImg p H M ≤ Subgroup.normalizer (C : Set (StarGroup p H))) :
    Nonempty (oPrimeModPrimeComplement d (starImg p H M ⊓ (C ⊔ starImg p H D)) ≃*
      modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := by
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let Y : Subgroup (StarGroup p H) := starImg p H M ⊓ (C ⊔ starImg p H D)
  have hHull := oPPrimeHull_inf_eq_of_isSylowOf_starImg hd hO hD hDC hCn
  let A : Subgroup ↥H := (oPPrimeHull d (H ⊓ M)).subgroupOf H
  have hAmap : A.map π = oPPrimeHull d (starImg p H M) := by
    dsimp only [A]
    rw [oPPrimeHull_subgroupOf_of_le (inf_le_left : H ⊓ M ≤ H),
      S631.map_oPPrimeHull, Subgroup.inf_subgroupOf_left]
    rfl
  have hkerA : ¬ d ∣ Nat.card ↥(π.ker ⊓ A) := by
    rw [QuotientGroup.ker_mk']
    exact fun h => hO (h.trans (Subgroup.card_dvd_of_le (inf_le_left : _ ⊓ A ≤ _)))
  obtain ⟨f₁⟩ := nonempty_oPrimeModPrimeComplement_mulEquiv (G := StarGroup p H) hd Y
  have hY' : oPPrimeHull d Y = oPPrimeHull d (starImg p H M ⊓ C) := by
    dsimp only [Y]
    rw [sup_eq_left.mpr hDC]
  obtain ⟨f₂⟩ := nonempty_modPrimeComplement_congr (d := d) (MulEquiv.subgroupCongr hY')
  obtain ⟨f₃⟩ := nonempty_modPrimeComplement_congr (d := d) (MulEquiv.subgroupCongr hHull)
  obtain ⟨f₄⟩ := nonempty_modPrimeComplement_mulEquiv_of_map (G := ↥H) hd π hAmap hkerA
  obtain ⟨f₅⟩ := nonempty_modPrimeComplement_congr (d := d)
    (Subgroup.subgroupOfEquivOfLe
      ((oPPrimeHull_le d (H ⊓ M)).trans (inf_le_left : H ⊓ M ≤ H)))
  have hgoalM : oPrimeModPrimeComplement d Y ≃*
      modPrimeComplement d (oPPrimeHull d (H ⊓ M)) :=
    f₁.trans (f₂.trans (f₃.trans (f₄.symm.trans f₅)))
  exact ⟨hgoalM⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
