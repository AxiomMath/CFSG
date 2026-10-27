module

public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.CentralizerSup
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.GroupTheory.QuasisimplePSolvable
import CFSG.Quasithin.Vol2.Ch11SecA12Cop
import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {p : ℕ}

private lemma core_le (K : Subgroup X) :
    (CFSG.pPrimeCore p ↥K).map K.subtype ≤ K :=
  Subgroup.map_subtype_le _

theorem le_normalizer_map_pPrimeCore (K : Subgroup X) :
    K ≤ Subgroup.normalizer (((CFSG.pPrimeCore p ↥K).map K.subtype : Subgroup X) : Set X) := by
  have h := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore p ↥K) K.subtype
  simpa [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] using h

private lemma dvd_card_quotient_core_of_isPComponent (hp : p.Prime) {K : Subgroup X}
    (hK : CFSG.IsPComponent p K) :
    p ∣ Nat.card (K ⧸ CFSG.pPrimeCore p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  have hq :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
      p K hK
  have htop : (⊤ : Subgroup (K ⧸ CFSG.pPrimeCore p K)) ≤
      CFSG.pPrimeCore p (K ⧸ CFSG.pPrimeCore p K) :=
    le_sSup ⟨inferInstance, by
      rw [Subgroup.card_top]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd⟩
  rw [CFSG.pPrimeCore_quotient_eq_bot hp, le_bot_iff] at htop
  have hnt : Nontrivial (K ⧸ CFSG.pPrimeCore p K) := by
    haveI : IsSimpleGroup
        ((K ⧸ CFSG.pPrimeCore p K) ⧸
          Subgroup.center (K ⧸ CFSG.pPrimeCore p K)) := hq.2.1
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center (K ⧸ CFSG.pPrimeCore p K))).nontrivial
  haveI := hnt
  exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup (K ⧸ CFSG.pPrimeCore p K))).mp
    inferInstance htop

private lemma not_isPSolvable_coreQuotient_of_isPComponent (hp : p.Prime) {K : Subgroup X}
    (hK : CFSG.IsPComponent p K) :
    ¬ CFSG.HallHigman.IsPSolvable p (K ⧸ CFSG.pPrimeCore p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
      p K hK
  exact CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.not_isPSolvable_of_isQuasisimple
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
    (dvd_card_quotient_core_of_isPComponent hp hK)

private lemma coreQuotient_surjective_of_covers {K H : Subgroup X} (hHK : H ≤ K)
    (hcov : ∀ b ∈ K, ∃ c ∈ H, c⁻¹ * b ∈ (CFSG.pPrimeCore p ↥K).map K.subtype) :
    Function.Surjective
      ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)).comp (Subgroup.inclusion hHK)) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore p ↥K) y
  obtain ⟨c, hcH, hc⟩ := hcov b b.2
  obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hc
  refine ⟨⟨c, hcH⟩, ?_⟩
  change QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)
      (Subgroup.inclusion hHK ⟨c, hcH⟩) = QuotientGroup.mk' (CFSG.pPrimeCore p ↥K) b
  refine QuotientGroup.eq.mpr ?_
  rw [show (Subgroup.inclusion hHK ⟨c, hcH⟩)⁻¹ * b = k from
    Subtype.ext (by simpa using hk_eq.symm)]
  exact hk

private lemma commutator_mem_inf_centralizer {B₁ B₂ K N : Subgroup X}
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hcomm : ⁅B₂, K⁆ ≤ N) {a : X} (ha : a ∈ B₂) {d : X}
    (hd : d ∈ K ⊓ Subgroup.centralizer (B₁ : Set X)) :
    a * d * a⁻¹ * d⁻¹ ∈ N ⊓ Subgroup.centralizer (B₁ : Set X) := by
  refine ⟨?_, ?_⟩
  · simpa [commutatorElement_def, mul_assoc] using
      (Subgroup.commutator_le.mp hcomm a ha d hd.1)
  · change a * d * a⁻¹ * d⁻¹ ∈ Subgroup.centralizer (B₁ : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxa : Commute a x := (hc x hx a ha).symm
    have hxd : Commute d x := (Subgroup.mem_centralizer_iff.mp hd.2 x hx).symm
    have h1 : Commute (a * d) x := Commute.mul_left hxa hxd
    have h2 : Commute a⁻¹ x := hxa.inv_left
    have h3 : Commute d⁻¹ x := hxd.inv_left
    exact (Commute.mul_left (Commute.mul_left h1 h2) h3).symm

theorem not_isPSolvable_of_covers (hp : p.Prime) {K H : Subgroup X}
    (hK : CFSG.IsPComponent p K) (hHK : H ≤ K)
    (hcov : ∀ b ∈ K, ∃ c ∈ H, c⁻¹ * b ∈ (CFSG.pPrimeCore p ↥K).map K.subtype) :
    ¬ CFSG.HallHigman.IsPSolvable p ↥H := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hH
  let φ : ↥H →* ↥K ⧸ CFSG.pPrimeCore p ↥K :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥K)).comp (Subgroup.inclusion hHK)
  have hsurj : Function.Surjective φ := coreQuotient_surjective_of_covers hHK hcov
  have htop : CFSG.HallHigman.IsPSolvable p ↥(⊤ : Subgroup ↥H) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.topEquiv (G := ↥H)).symm hH
  have himg :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      (p := p) φ (N := ⊤) htop
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj] at himg
  exact not_isPSolvable_coreQuotient_of_isPComponent hp hK
    (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv himg)

theorem dvd_card_of_covers (hp : p.Prime) {K H : Subgroup X}
    (hK : CFSG.IsPComponent p K) (hHK : H ≤ K)
    (hcov : ∀ b ∈ K, ∃ c ∈ H, c⁻¹ * b ∈ (CFSG.pPrimeCore p ↥K).map K.subtype) :
    p ∣ Nat.card H := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnd
  exact not_isPSolvable_of_covers hp hK hHK hcov
    (CFSG.LocalAnalysis.UniquenessCase.UCK.isPSolvable_of_not_dvd_card (Q := ↥H) hnd)

theorem exists_mem_inf_centralizer_sup {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    {K N B₁ B₂ : Subgroup X} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set X))
    (hB₁ : IsPGroup q₁ B₁) (hB₂ : IsPGroup q₂ B₂)
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hB₂K : B₂ ≤ Subgroup.normalizer (K : Set X))
    (hcomm₁ : ⁅B₁, K⁆ ≤ N) (hcomm₂ : ⁅B₂, K⁆ ≤ N)
    (hcop₁ : ¬ q₁ ∣ Nat.card N) (hcop₂ : ¬ q₂ ∣ Nat.card N) {b : X} (hb : b ∈ K) :
    ∃ c ∈ K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup X) : Set X), c⁻¹ * b ∈ N := by
  classical
  have hcomm₁' : ∀ a ∈ B₁, ∀ d ∈ K, a * d * a⁻¹ * d⁻¹ ∈ N := by
    intro a ha d hd
    simpa [commutatorElement_def, mul_assoc] using
      (Subgroup.commutator_le.mp hcomm₁ a ha d hd)
  obtain ⟨d, hd, hdb⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime hq₁ hB₁ hB₁K hNK hKN
      ((Nat.Prime.coprime_iff_not_dvd hq₁).2 hcop₁) hcomm₁' hb
  have hB₂C₁ : B₂ ≤ Subgroup.centralizer (B₁ : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hc x hx y hy
  have hC_NC : Subgroup.centralizer (B₁ : Set X) ≤
      Subgroup.normalizer ((Subgroup.centralizer (B₁ : Set X)) : Set X) :=
    (Subgroup.centralizer_le_normalizer (B₁ : Set X)).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (B₁ : Set X))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (B₁ : Set X)))
  have hB₂D : B₂ ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (B₁ : Set X) : Subgroup X) : Set X) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_inf_of_le hB₂K (hB₂C₁.trans hC_NC)
  have hDN' : K ⊓ Subgroup.centralizer (B₁ : Set X) ≤
      Subgroup.normalizer
        ((N ⊓ Subgroup.centralizer (B₁ : Set X) : Subgroup X) : Set X) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_inf_of_le
      (inf_le_left.trans hKN) (inf_le_right.trans hC_NC)
  have hN'D : N ⊓ Subgroup.centralizer (B₁ : Set X) ≤
      K ⊓ Subgroup.centralizer (B₁ : Set X) :=
    le_inf (inf_le_left.trans hNK) inf_le_right
  have hcomm₂' : ∀ a ∈ B₂,
      ∀ e ∈ K ⊓ Subgroup.centralizer (B₁ : Set X),
      a * e * a⁻¹ * e⁻¹ ∈ N ⊓ Subgroup.centralizer (B₁ : Set X) :=
    fun a ha e he => commutator_mem_inf_centralizer hc hcomm₂ ha he
  have hcopN' : Nat.Coprime q₂
      (Nat.card ↥(N ⊓ Subgroup.centralizer (B₁ : Set X))) :=
    (Nat.Prime.coprime_iff_not_dvd hq₂).2 fun h =>
      hcop₂ (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨c, hc', hce⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime hq₂ hB₂ hB₂D hN'D hDN'
      hcopN' hcomm₂' hd
  refine ⟨c, ?_, ?_⟩
  · rw [CFSG.centralizer_sup_eq]
    exact ⟨hc'.1.1, hc'.1.2, hc'.2⟩
  · rw [show c⁻¹ * b = (c⁻¹ * d) * (d⁻¹ * b) by group]
    exact N.mul_mem hce.1 hdb

theorem not_isPSolvable_inf_centralizer_sup (hp : p.Prime) {K : Subgroup X}
    (hK : CFSG.IsPComponent p K) {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    {B₁ B₂ : Subgroup X} (hB₁ : IsPGroup q₁ B₁) (hB₂ : IsPGroup q₂ B₂)
    (hc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x)
    (hB₁K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hB₂K : B₂ ≤ Subgroup.normalizer (K : Set X))
    (hcomm₁ : ⁅B₁, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcomm₂ : ⁅B₂, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcop₁ : ¬ q₁ ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hcop₂ : ¬ q₂ ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    ¬ CFSG.HallHigman.IsPSolvable p
      ↥(K ⊓ Subgroup.centralizer ((B₁ ⊔ B₂ : Subgroup X) : Set X)) := by
  have hcop₁' : ¬ q₁ ∣ Nat.card ((CFSG.pPrimeCore p ↥K).map K.subtype) := by
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hcop₂' : ¬ q₂ ∣ Nat.card ((CFSG.pPrimeCore p ↥K).map K.subtype) := by
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  refine not_isPSolvable_of_covers hp hK inf_le_left ?_
  intro b hb
  exact exists_mem_inf_centralizer_sup hq₁ hq₂ (core_le K)
    (le_normalizer_map_pPrimeCore K) hB₁ hB₂ hc hB₁K hB₂K hcomm₁ hcomm₂ hcop₁' hcop₂' hb

theorem not_isPSolvable_inf_centralizer_of_isPComponent (hp : p.Prime) {K : Subgroup X}
    (hK : CFSG.IsPComponent p K) {q : ℕ} (hq : q.Prime) {B : Subgroup X}
    (hB : IsPGroup q B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hcomm : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hcop : ¬ q ∣ Nat.card (CFSG.pPrimeCore p ↥K)) :
    ¬ CFSG.HallHigman.IsPSolvable p
      ↥(K ⊓ Subgroup.centralizer (B : Set X)) := by
  have hcop' : ¬ q ∣ Nat.card ((CFSG.pPrimeCore p ↥K).map K.subtype) := by
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hcomm' : ∀ a ∈ B, ∀ d ∈ K, a * d * a⁻¹ * d⁻¹ ∈
      (CFSG.pPrimeCore p ↥K).map K.subtype := by
    intro a ha d hd
    simpa [commutatorElement_def, mul_assoc] using
      (Subgroup.commutator_le.mp hcomm a ha d hd)
  refine not_isPSolvable_of_covers hp hK inf_le_left ?_
  intro b hb
  exact CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime hq hB hBK (core_le K)
    (le_normalizer_map_pPrimeCore K) ((Nat.Prime.coprime_iff_not_dvd hq).2 hcop') hcomm' hb

end CFSG.GroupTheory
