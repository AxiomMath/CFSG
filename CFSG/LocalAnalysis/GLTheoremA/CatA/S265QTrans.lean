module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Rank
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Lift
public import CFSG.LocalAnalysis.GLTheoremA.S12.Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensusTools
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Quot
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Quot

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem normal_glaPPrimeCoreOf {S : Subgroup A} (hS : S.Normal) : (GLAPPrimeCoreOf p S).Normal := by
  have h := normalizer_le_normalizer_glaPPrimeCoreOf p S
  rw [Subgroup.normalizer_eq_top_iff.2 hS, top_le_iff] at h
  exact Subgroup.normalizer_eq_top_iff.1 h

theorem cycModSylow_map (hp : p.Prime) {S : Subgroup A} (hS : S.Normal) (N : Subgroup A) [N.Normal]
    (hN : N = GLAPPrimeCoreOf p S) (hcyc : CycModSylow p S) :
    CycModSylow p (S.map (QuotientGroup.mk' N)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : ¬ p ∣ Nat.card (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk', hN]
    exact not_dvd_card_glaPPrimeCoreOf hp _
  intro E hE hEp
  obtain ⟨Et, hEtp, hEtmap, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1020_frattini_lift
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hEp
  have hcyc' : IsCyclic Et := by
    refine hcyc _ (fun g hg => ?_) hEtp
    have hgE : QuotientGroup.mk' N g ∈ E := by rw [← hEtmap]; exact ⟨g, hg, rfl⟩
    have h1 := hE _ hgE
    rw [centMod_iff] at h1 ⊢
    have hgS : g ∈ Subgroup.normalizer (S : Set A) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hS]; exact Subgroup.mem_top g
    exact (S267.mem_centModSubgroup_map_iff hp (QuotientGroup.mk' N) hker hgS).2 h1
  let f : ↥Et →* ↥E := ((QuotientGroup.mk' N).comp Et.subtype).codRestrict E (fun x => by
    rw [← hEtmap]; exact ⟨x, x.2, rfl⟩)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : A ⧸ N) ∈ Et.map (QuotientGroup.mk' N) := by rw [hEtmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact isCyclic_of_surjective f hsurj

theorem twoLocalRank_quot_le (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) : GLATwoLocalRank p (A ⧸ N) ≤ GLATwoLocalRank p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  show CFSG.Open.twoLocalPrimeRank p (A ⧸ N) ≤ CFSG.Open.twoLocalPrimeRank p A
  unfold twoLocalPrimeRank
  apply csSup_le'
  rintro k ⟨K, ⟨Pb, hP, hP2, rfl⟩, rfl⟩
  apply csSup_le'
  rintro j ⟨Eb, hEbK, hEb, hj⟩
  obtain ⟨T, E, hT, hT2, hE, hEcard, hEN⟩ := T263.lift_normalizing hp hp2 N hN hP hP2 hEb hEbK
  have h1 : j ≤ CFSG.Open.pRank p (Subgroup.normalizer (T : Set A)) :=
    T263.le_pRank hEN hE (hEcard.trans hj)
  exact h1.trans (T263.pRank_normalizer_le hT hT2)

end Quot

section Maps

variable {A Ω : Type} [Group A] [Finite A] [Group Ω] [Finite Ω] {p : ℕ}

theorem card2_map (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) (Y : Subgroup A) :
    card2 p (Y.map π) = card2 p Y := by
  unfold card2
  rw [Nat.card_congr (T156.pquotMap hp π hN Y).toEquiv]

theorem centCard2_map (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker) {Y : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (Y : Set A)) : centCard2 p (Y.map π) (π g) = centCard2 p Y g := by
  unfold centCard2
  congr 1
  exact (Nat.card_congr (Equiv.subtypeEquiv (T156.pquotMap hp π hN Y).toEquiv
    (fun q => (T156.indRel_pquotMap hp π hN hg q q).symm))).symm

end Maps

section Layer

variable {A Q : Type} [Group A] [Group Q]

theorem glaLayer_le_map_layer (C : Subgroup A) : GLALayer C ≤ (CFSG.layer ↥C).map C.subtype := by
  refine I142N.GLALayer_le_of fun J hJ => ?_
  have h1 : IsComponentOf (J.subgroupOf C) ⊤ := S12.isComponentOf_top_subgroupOf hJ
  have h2 : CFSG.IsComponent (J.subgroupOf C) := (CFSG.isComponent_iff_open _).2 h1
  have h3 := CFSG.LocalCores.component_le_layer h2
  calc J = (J.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hJ.1).symm
    _ ≤ _ := Subgroup.map_mono h3

theorem glaLayer_map_le_central (π : A →* Q) {Y : Subgroup A}
    (hker : ∀ n ∈ Y, π n = 1 → ∀ y ∈ Y, y * n = n * y) :
    GLALayer (Y.map π) ≤ (GLALayer Y).map π := by
  let f : ↥Y →* ↥(Y.map π) := π.subgroupMap Y
  have hf : Function.Surjective f := π.subgroupMap_surjective Y
  have hfker : f.ker ≤ Subgroup.center ↥Y := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : π (n : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hn)
    exact Subtype.ext (hker n n.2 h1 y y.2)
  have key := CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof.map_layer_of_surjective f hf hfker
  have hcomp : (Y.map π).subtype.comp f = π.comp Y.subtype := by
    ext x
    rfl
  calc GLALayer (Y.map π) ≤ (CFSG.layer ↥(Y.map π)).map (Y.map π).subtype := glaLayer_le_map_layer _
    _ = ((CFSG.layer ↥Y).map f).map (Y.map π).subtype := by rw [key]
    _ = ((CFSG.layer ↥Y).map Y.subtype).map π := by
        rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    _ ≤ (GLALayer Y).map π :=
        Subgroup.map_mono (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.map_layer_le_glaLayer Y)

end Layer

section Cases

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem maxc_of_cases (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup A} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {B T : Subgroup A} (hB : IsElemAbelian p B) (hrank : p ^ GLATwoLocalRank p A ≤ Nat.card B)
    (hT2 : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set A)) (hne : (⁅T, B⁆ : Subgroup A) ≠ ⊥) :
    (⁅T.map (QuotientGroup.mk' N), B.map (QuotientGroup.mk' N)⁆ : Subgroup (A ⧸ N)) ≠ ⊥ ∨
      (⁅T, B⁆ : Subgroup A) ≤ N ∧ ∀ E : Subgroup (A ⧸ N), IsElemAbelian p E →
        Nat.card E ≤ Nat.card (B.map (QuotientGroup.mk' N)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hle : (⁅T, B⁆ : Subgroup A) ≤ N
  · right
    refine ⟨hle, fun E hE => ?_⟩
    obtain ⟨Et, hEtel, -, hEtcard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift N hN hE
    have hcomm2 : IsPGroup 2 (⁅T, B⁆ : Subgroup A) := hT2.to_le (commutator_le_left_of_normalizes hBT)
    obtain ⟨k, hk⟩ := hcomm2.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      apply hne
      rw [h0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    have h2N : 2 ∣ Nat.card N := by
      have h := Subgroup.card_dvd_of_le hle
      rw [hk] at h
      exact (dvd_pow_self 2 hk0).trans h
    obtain ⟨R, -, hR0, hR2, hER⟩ := exists_two_subgroup_of_even hp hN h2N
      (isPGroup_of_isElemAbelian hEtel) (by
        intro a _
        rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
        exact Subgroup.mem_top a)
    have h1 := card_le_pow_glaTwoLocalRank hp hEtel hR0 hR2 hER
    have hker : ¬ p ∣ Nat.card (QuotientGroup.mk' N).ker := by
      rw [QuotientGroup.ker_mk']
      exact hN
    rw [S267.card_map_of_isPGroup hp (QuotientGroup.mk' N) hker (isPGroup_of_isElemAbelian hB), ← hEtcard]
    exact h1.trans hrank
  · left
    rw [← Subgroup.map_commutator]
    intro hbot
    exact hle (by
      have := (Subgroup.map_eq_bot_iff _).1 hbot
      rwa [QuotientGroup.ker_mk'] at this)

end Cases

section Central

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem glaPPrimeCoreOf_central {S : Subgroup A} (hq : CFSG.Open.IsQuasisimple ↥S)
    (hq' : CFSG.Open.IsQuasisimple (PQuot p S)) :
    ∀ n ∈ GLAPPrimeCoreOf p S, ∀ s ∈ S, s * n = n * s := by
  have hne : GLAPPrimeCore p ↥S ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup (PQuot p S ⧸ Subgroup.center (PQuot p S)) := hq'.2
    have hsub : Subsingleton (PQuot p S) := by
      unfold PQuot
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hsub2 : Subsingleton (PQuot p S ⧸ Subgroup.center (PQuot p S)) :=
      (QuotientGroup.mk_surjective).subsingleton
    exact not_subsingleton _ hsub2
  have hle := le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal p ↥S) hne
  intro n hn s hs
  obtain ⟨n', hn', rfl⟩ := hn
  have := Subgroup.mem_center_iff.1 (hle hn') ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem not_le_of_isQuasisimple_central {K Z : Subgroup A} (hK : CFSG.Open.IsQuasisimple ↥K) (hKZ : K ≤ Z)
    (hZ : ∀ z ∈ Z, ∀ k ∈ K, k * z = z * k) : False := by
  have hc : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    rw [Subgroup.mem_center_iff]
    intro k'
    exact Subtype.ext (hZ k (hKZ k.2) k' k'.2)
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2
  have hsub : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ hsub

end Central

end CFSG.LocalAnalysis.GLTheoremA.S265

end
