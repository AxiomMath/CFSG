module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterSymplectic
public import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.GroupTheory.SteinbergCBFTPSolvable
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Walter.AStar.N1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCSpFull
open CFSG.Adapters.CatalogueFieldBridges

private theorem idxCoreAt_fieldAut_C {r p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hr : 3 ≤ r) (hK : Nat.card K = q.p ^ q.exponent)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hk : ∃ k ∈ subfieldFixedGroup K r σ, orderOf k = p) :
    IdxCoreAt p (.C r q) (fieldAut r K σ) := by
  classical
  obtain ⟨hpf, hkcard, -, -, hinj, hfix, -, hsimple, -, -, -, -, -, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) q.prime_p hp hp2
      hpq q.exponent_pos (by omega : 2 ≤ r) hK σ hσ
  obtain ⟨hHs, hHnc⟩ := hsimple (by omega)
  have hHq : CFSG.IsQuasisimple ↥(subfieldFixedGroup K r σ) :=
    isQuasisimple_of_simple_nonabelian fun h => by
      obtain ⟨a, b, hab⟩ := hHnc
      exact hab (h a b)
  have hHp : p ∣ Nat.card ↥(subfieldFixedGroup K r σ) := by
    obtain ⟨k, hkH, hkord⟩ := hk
    have h1 : orderOf (⟨k, hkH⟩ : subfieldFixedGroup K r σ) = p := by
      rw [Subgroup.orderOf_mk]
      exact hkord
    rw [← h1]
    exact orderOf_dvd_natCard _
  let q₀ : TauCeti.PrimePower :=
    ⟨q.p, q.exponent / p, q.prime_p,
      Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos⟩
  have hq₀card : q₀.card =
      Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) := by
    rw [TauCeti.PrimePower.card_def, hkcard]
  have hv₀ : (TauCeti.LieTypeIndex.C r q₀).Valid := by
    have hqodd : q.p ≠ 2 :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨hr, hqodd⟩, by simp⟩
  haveI : Finite ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) := Subtype.finite
  let eH : StatedProj (StatedSp r
      ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ)) ≃*
      ↥(subfieldFixedGroup K r σ) := MonoidHom.ofInjective hinj
  obtain ⟨eCat⟩ := nonempty_mulEquiv_lie_C_of_statedProj (r := r) hv₀
    (k := ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ)) hq₀card.symm
  have hTeq : subfieldFixedGroup K r σ = fixSubgroup (fieldAut r K σ) :=
    Subgroup.ext fun x => (hfix x).trans (mem_fixSubgroup).symm
  refine ⟨subfieldFixedGroup K r σ, ?_, ?_, hHq, hHp, .lie ⟨.C r q₀, hv₀⟩, ?_, ?_⟩
  · intro x hx
    exact (mem_fixSubgroup).2 ((hfix x).1 hx)
  · intro f hf t ht
    rw [hTeq] at ht ⊢
    exact mul_mem (mul_mem hf ht) (inv_mem hf)
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (CFSG.Walter.center_eq_bot_of_isSimpleGroup ⟨hHnc.choose, hHnc.choose_spec.choose,
        hHnc.choose_spec.choose_spec⟩)).trans QuotientGroup.quotientBot |>.trans
      (eH.symm.trans eCat)⟩
  · refine Or.inl ⟨rfl, ?_⟩
    change q₀.card ^ p = q.card
    rw [TauCeti.PrimePower.card_def q₀, ← pow_mul, Nat.div_mul_cancel hpf]
    exact (TauCeti.PrimePower.card_def q).symm

private theorem idxCoreAt_of_subfield_simple {p : ℕ} {d : TauCeti.LieTypeIndex} {r : ℕ}
    {K : Type} [Field K]
    {σ : K ≃+* K}
    (hHs : IsSimpleGroup ↥(subfieldFixedGroup K r σ))
    (hHnc : ∃ a b : ↥(subfieldFixedGroup K r σ), a * b ≠ b * a)
    (hfix : ∀ x, x ∈ subfieldFixedGroup K r σ ↔ fieldAut r K σ x = x)
    (hHp : p ∣ Nat.card ↥(subfieldFixedGroup K r σ))
    {i : TauCeti.CFSGIndex}
    (hiso : Nonempty (↥(subfieldFixedGroup K r σ) ⧸
      Subgroup.center ↥(subfieldFixedGroup K r σ) ≃* i.Group))
    (hrel : subRelC p d i) :
    IdxCoreAt p d (fieldAut r K σ) := by
  obtain ⟨eIso⟩ := hiso
  haveI := hHs
  have hHq : CFSG.IsQuasisimple ↥(subfieldFixedGroup K r σ) :=
    isQuasisimple_of_simple_nonabelian fun h => by
      obtain ⟨a, b, hab⟩ := hHnc
      exact hab (h a b)
  have hTeq : subfieldFixedGroup K r σ = fixSubgroup (fieldAut r K σ) :=
    Subgroup.ext fun x => (hfix x).trans (mem_fixSubgroup).symm
  refine ⟨subfieldFixedGroup K r σ, ?_, ?_, hHq, hHp, i, ⟨eIso⟩, hrel⟩
  · intro x hx
    exact (mem_fixSubgroup).2 ((hfix x).1 hx)
  · intro f hf t ht
    rw [hTeq] at ht ⊢
    exact mul_mem (mul_mem hf ht) (inv_mem hf)

private theorem idxCoreAt_fieldAut_B_two_two {p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} {σ : K ≃+* K}
    (hfix : ∀ x, x ∈ subfieldFixedGroup K 2 σ ↔ fieldAut 2 K σ x = x)
    (eT6 : ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ ≃*
      alternatingGroup (Fin 6))
    (hp35 : p = 3 ∨ p = 5) (hqcard : q.card = 2 ^ p) :
    IdxCoreAt p (.B 2 q) (fieldAut 2 K σ) := by
  classical
  have hA6s : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hA6nc : ¬ ∀ a b : ↥(alternatingGroup (Fin 6)), a * b = b * a := by
    intro hcomm
    haveI : IsMulCommutative ↥(alternatingGroup (Fin 6)) := ⟨⟨hcomm⟩⟩
    have hp' := (Group.is_simple_iff_prime_card).1 hA6s
    rw [nat_card_alternatingGroup, Nat.card_fin] at hp'
    norm_num at hp'
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := hA6s
  haveI : IsSimpleGroup ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ :=
    eT6.isSimpleGroup
  have hTnc : ¬ ∀ a b : ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆,
      a * b = b * a := by
    intro h
    exact hA6nc fun a b => by
      obtain ⟨x, rfl⟩ := eT6.surjective a
      obtain ⟨y, rfl⟩ := eT6.surjective b
      simpa only [map_mul] using congrArg eT6 (h x y)
  have hTq : CFSG.IsQuasisimple ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ :=
    isQuasisimple_of_simple_nonabelian hTnc
  have hcardT : Nat.card ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ = 360 := by
    rw [Nat.card_congr eT6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hTp : p ∣ Nat.card ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ := by
    rw [hcardT]
    rcases hp35 with rfl | rfl <;> norm_num
  have hTle : (⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ :
      Subgroup (StatedProj (StatedSp 2 K))) ≤ fixSubgroup (fieldAut 2 K σ) :=
    fun x hx => (mem_fixSubgroup).2
      ((hfix x).1 (Subgroup.commutator_le_of_le le_rfl le_rfl hx))
  have hTcenter : Subgroup.center
      ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center
      ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆) with h | h
    · exact h
    · exfalso
      push Not at hTnc
      obtain ⟨a, b, hab⟩ := hTnc
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  let hn6 : 5 ≤ 6 := by norm_num
  have hiso : ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ ⧸
      Subgroup.center ↥⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ ≃*
      (TauCeti.CFSGIndex.alternating 6 hn6).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hTcenter).trans QuotientGroup.quotientBot).trans eT6
  have hrel : subRelC p (.B 2 q) (.alternating 6 hn6) := by
    refine Or.inr (Or.inl ⟨rfl, Or.inr ⟨⟨q, rfl⟩, ?_⟩⟩)
    exact hqcard
  have hcommnorm : ∀ f ∈ fixSubgroup (fieldAut 2 K σ),
      ∀ t ∈ ⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆,
        f * t * f⁻¹ ∈ ⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ := by
    have hJN : subfieldFixedGroup K 2 σ = fixSubgroup (fieldAut 2 K σ) :=
      Subgroup.ext fun x => (hfix x).trans (mem_fixSubgroup).symm
    have hle : fixSubgroup (fieldAut 2 K σ) ≤
        Subgroup.normalizer (subfieldFixedGroup K 2 σ : Set (StatedProj (StatedSp 2 K))) := by
      rw [hJN]
      exact Subgroup.le_normalizer
    have h := CFSG.GroupTheory.FT63ChII.le_normalizer_commutator
      (H₁ := subfieldFixedGroup K 2 σ) (H₂ := subfieldFixedGroup K 2 σ)
      (K := fixSubgroup (fieldAut 2 K σ)) hle hle
    intro f hf t ht
    exact (Subgroup.mem_normalizer_iff.1 (h hf) t).1 ht
  exact ⟨⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆, hTle,
    hcommnorm, hTq, hTp, .alternating 6 hn6, ⟨hiso⟩, hrel⟩

private theorem idxCoreAt_fieldAut_B_two_three {p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} {σ : K ≃+* K}
    (hfix : ∀ x, x ∈ subfieldFixedGroup K 2 σ ↔ fieldAut 2 K σ x = x)
    (hHs : IsSimpleGroup ↥(subfieldFixedGroup K 2 σ))
    (hHnc : ∃ a b : ↥(subfieldFixedGroup K 2 σ), a * b ≠ b * a)
    (hHp : p ∣ Nat.card ↥(subfieldFixedGroup K 2 σ))
    (hk3 : Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) = 3)
    (hqcard : q.card = 3 ^ p) :
    IdxCoreAt p (.B 2 q) (fieldAut 2 K σ) := by
  haveI : Finite ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) :=
    Subtype.finite
  let eH : StatedProj (StatedSp 2
      ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ)) ≃*
      ↥(subfieldFixedGroup K 2 σ) :=
    MonoidHom.ofInjective (subfieldSpProj_injective (r := 2) (by norm_num) _)
  obtain ⟨eCat⟩ := nonempty_mulEquiv_lie_u42 hk3
  have hcenter : Subgroup.center ↥(subfieldFixedGroup K 2 σ) = ⊥ :=
    CFSG.Walter.center_eq_bot_of_isSimpleGroup hHnc
  have hiso : ↥(subfieldFixedGroup K 2 σ) ⧸
      Subgroup.center ↥(subfieldFixedGroup K 2 σ) ≃*
      (TauCeti.CFSGIndex.lie u42Index).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans
      (eH.symm.trans eCat)
  have hrel : subRelC p (.B 2 q) (.lie u42Index) := by
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ⟨q, rfl⟩, ?_⟩))))
    · exact ⟨u42q, rfl, by norm_num [u42q, TauCeti.PrimePower.card_def]⟩
    · exact hqcard
  exact idxCoreAt_of_subfield_simple hHs hHnc hfix hHp ⟨hiso⟩ hrel

private theorem idxCoreAt_fieldAut_B_two_generic {p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} {σ : K ≃+* K} (hp : p.Prime)
    (hfix : ∀ x, x ∈ subfieldFixedGroup K 2 σ ↔ fieldAut 2 K σ x = x)
    (hHs : IsSimpleGroup ↥(subfieldFixedGroup K 2 σ))
    (hHnc : ∃ a b : ↥(subfieldFixedGroup K 2 σ), a * b ≠ b * a)
    (hHp : p ∣ Nat.card ↥(subfieldFixedGroup K 2 σ))
    (hkcard : Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) =
      q.p ^ (q.exponent / p))
    (hpf : p ∣ q.exponent)
    (hk2 : Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) ≠ 2)
    (hk3 : Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) ≠ 3) :
    IdxCoreAt p (.B 2 q) (fieldAut 2 K σ) := by
  let q₀ : TauCeti.PrimePower :=
    ⟨q.p, q.exponent / p, q.prime_p,
      Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos⟩
  have hq₀card : q₀.card =
      Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) := by
    rw [TauCeti.PrimePower.card_def, hkcard]
  have hv₀ : (TauCeti.LieTypeIndex.B 2 q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨le_rfl, ?_⟩, ?_⟩
    · rintro ⟨-, h2⟩
      exact hk2 (hq₀card.symm.trans h2)
    · rintro ⟨-, h3⟩
      exact hk3 (hq₀card.symm.trans h3)
  haveI : Finite ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) :=
    Subtype.finite
  let eH : StatedProj (StatedSp 2
      ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ)) ≃*
      ↥(subfieldFixedGroup K 2 σ) :=
    MonoidHom.ofInjective (subfieldSpProj_injective (r := 2) (by norm_num) _)
  obtain ⟨eCat⟩ := nonempty_mulEquiv_lie_B2_of_statedProj hv₀ hq₀card.symm
  have hcenter : Subgroup.center ↥(subfieldFixedGroup K 2 σ) = ⊥ :=
    CFSG.Walter.center_eq_bot_of_isSimpleGroup hHnc
  have hiso : ↥(subfieldFixedGroup K 2 σ) ⧸
      Subgroup.center ↥(subfieldFixedGroup K 2 σ) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q₀, hv₀⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans
      (eH.symm.trans eCat)
  have hrel : subRelC p (.B 2 q) (.lie ⟨TauCeti.LieTypeIndex.B 2 q₀, hv₀⟩) := by
    refine Or.inl ⟨rfl, ?_⟩
    change q₀.card ^ p = q.card
    rw [TauCeti.PrimePower.card_def q₀, ← pow_mul, Nat.div_mul_cancel hpf]
    exact (TauCeti.PrimePower.card_def q).symm
  exact idxCoreAt_of_subfield_simple hHs hHnc hfix hHp ⟨hiso⟩ hrel

private theorem idxCoreAt_fieldAut_B_three {r p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} {σ : K ≃+* K} (hp : p.Prime) (hr3 : 3 ≤ r)
    (hfix : ∀ x, x ∈ subfieldFixedGroup K r σ ↔ fieldAut r K σ x = x)
    (hHs : IsSimpleGroup ↥(subfieldFixedGroup K r σ))
    (hHnc : ∃ a b : ↥(subfieldFixedGroup K r σ), a * b ≠ b * a)
    (hHp : p ∣ Nat.card ↥(subfieldFixedGroup K r σ))
    (hq2 : q.p = 2)
    (hkcard : Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) =
      q.p ^ (q.exponent / p))
    (hpf : p ∣ q.exponent) :
    IdxCoreAt p (.B r q) (fieldAut r K σ) := by
  let q₀ : TauCeti.PrimePower :=
    ⟨q.p, q.exponent / p, q.prime_p,
      Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos⟩
  have hq₀card : q₀.card =
      Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) := by
    rw [TauCeti.PrimePower.card_def, hkcard]
  have hv₀ : (TauCeti.LieTypeIndex.B r q₀).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨⟨by omega, by rintro ⟨h, -⟩; omega⟩, by rintro ⟨h, -⟩; omega⟩
  have hq₀2 : q₀.p = 2 := hq2
  haveI : Finite ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) :=
    Subtype.finite
  let eH : StatedProj (StatedSp r
      ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ)) ≃*
      ↥(subfieldFixedGroup K r σ) :=
    MonoidHom.ofInjective (subfieldSpProj_injective (r := r) (by omega) _)
  obtain ⟨eCat⟩ := nonempty_mulEquiv_lie_B_of_statedProj hv₀ hq₀2 hr3 hq₀card.symm
  have hcenter : Subgroup.center ↥(subfieldFixedGroup K r σ) = ⊥ :=
    CFSG.Walter.center_eq_bot_of_isSimpleGroup hHnc
  have hiso : ↥(subfieldFixedGroup K r σ) ⧸
      Subgroup.center ↥(subfieldFixedGroup K r σ) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B r q₀, hv₀⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans
      (eH.symm.trans eCat)
  have hrel : subRelC p (.B r q) (.lie ⟨TauCeti.LieTypeIndex.B r q₀, hv₀⟩) := by
    refine Or.inl ⟨rfl, ?_⟩
    change q₀.card ^ p = q.card
    rw [TauCeti.PrimePower.card_def q₀, ← pow_mul, Nat.div_mul_cancel hpf]
    exact (TauCeti.PrimePower.card_def q).symm
  exact idxCoreAt_of_subfield_simple hHs hHnc hfix hHp ⟨hiso⟩ hrel

private theorem idxCoreAt_fieldAut_B {r p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hr : 2 ≤ r) (hK : Nat.card K = q.p ^ q.exponent)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hB : r = 2 ∨ q.p = 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hk : ∃ k ∈ subfieldFixedGroup K r σ, orderOf k = p) :
    IdxCoreAt p (.B r q) (fieldAut r K σ) := by
  classical
  obtain ⟨hpf, hkcard, -, -, -, hfix, -, hsimple, hexc, -, -, -, -, hlast⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) q.prime_p hp hp2
      hpq q.exponent_pos hr hK σ hσ
  have hHp : p ∣ Nat.card ↥(subfieldFixedGroup K r σ) := by
    obtain ⟨k, hkH, hkord⟩ := hk
    have h1 : orderOf (⟨k, hkH⟩ : subfieldFixedGroup K r σ) = p := by
      rw [Subgroup.orderOf_mk]
      exact hkord
    rw [← h1]
    exact orderOf_dvd_natCard _
  by_cases hr2 : r = 2
  · by_cases hk2 : Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) = 2
    · have hpow2 : q.p ^ (q.exponent / p) = 2 := hkcard.symm.trans hk2
      obtain ⟨-, ⟨eT6⟩, -⟩ := hexc ⟨hr2, hpow2⟩
      obtain ⟨-, hp35, -, -⟩ := hlast ⟨hr2, hpow2⟩ hk
      have hqcard : q.card = 2 ^ p := by
        rw [TauCeti.PrimePower.card_def, ← Nat.div_mul_cancel hpf, pow_mul, hpow2]
      subst hr2
      exact idxCoreAt_fieldAut_B_two_two hfix eT6 hp35 hqcard
    · by_cases hk3 :
        Nat.card ↥(CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) = 3
      · have hqcard : q.card = 3 ^ p := by
          rw [TauCeti.PrimePower.card_def, ← Nat.div_mul_cancel hpf, pow_mul,
            hkcard.symm.trans hk3]
        have hHs : IsSimpleGroup ↥(subfieldFixedGroup K r σ) :=
          (hsimple (by rintro ⟨-, h3⟩; exact hk2 (hkcard.trans h3))).1
        have hHnc := (hsimple (by rintro ⟨-, h3⟩; exact hk2 (hkcard.trans h3))).2
        subst hr2
        exact idxCoreAt_fieldAut_B_two_three hfix hHs hHnc hHp hk3 hqcard
      · have hHs : IsSimpleGroup ↥(subfieldFixedGroup K r σ) :=
          (hsimple (by rintro ⟨-, h3⟩; exact hk2 (hkcard.trans h3))).1
        have hHnc := (hsimple (by rintro ⟨-, h3⟩; exact hk2 (hkcard.trans h3))).2
        subst hr2
        exact idxCoreAt_fieldAut_B_two_generic hp hfix hHs hHnc hHp hkcard hpf hk2 hk3
  · have hr3 : 3 ≤ r := by omega
    have hq2 : q.p = 2 := by
      rcases hB with h | h
      · omega
      · exact h
    have hHs : IsSimpleGroup ↥(subfieldFixedGroup K r σ) := (hsimple (by omega)).1
    have hHnc := (hsimple (by omega)).2
    exact idxCoreAt_fieldAut_B_three hp hr3 hfix hHs hHnc hHp hq2 hkcard hpf

private theorem idxCoreAt_psp_of_outer_C {r p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hr : 2 ≤ r) (hK : Nat.card K = q.p ^ q.exponent)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) (hr3 : 3 ≤ r)
    {x : MulAut (StatedProj (StatedSp r K))} (hxp : x ^ p = 1)
    (hxo : x ∉ innAutDerived (StatedProj (StatedSp r K)))
    (hpdvd : p ∣ Nat.card (StatedProj (StatedSp r K))) :
    IdxCoreAt p (.C r q) x := by
  have hrq : ¬ (r = 2 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨rfl, -⟩
    omega
  have hxH : x ∉ inner (StatedProj (StatedSp r K)) := fun h => hxo (inner_le_innAutDerived _ h)
  obtain ⟨σ, h, hσ, -, hxh, hk⟩ :=
    exists_conj_fieldAut_psp q.prime_p hp hp2 hpq q.exponent_pos hr hK hrq hxp hxH hpdvd
  have hδ : IdxCoreAt p (.C r q) (fieldAut r K σ) :=
    idxCoreAt_fieldAut_C hp hp2 hpq hr3 hK hv hσ hk
  exact idxCoreAt_of_conj hδ h⁻¹ (by rw [hxh]; group)

theorem outerIdxAt_C {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.C r q, hv⟩).Group)
    (hpq : p ≠ q.p) (hpdvd : p ∣ Nat.card S) : OuterIdxAt p (.C r q) S := by
  have hr3 : 3 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hSC : StatedClassicalModel S .PSp r q.p q.exponent := by
    rcases (CFSG.Models.lieModel_C r q hv e).2 with h | ⟨h0, -⟩
    · exact h
    · omega
  obtain ⟨-, K, hfield, hfinite, hK, ⟨eK⟩⟩ := hSC
  let _ := hfield
  let _ := hfinite
  haveI : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv S eK.toEquiv
  have hpdvdK : p ∣ Nat.card (StatedProj (StatedSp r K)) := by
    rw [← Nat.card_congr eK.toEquiv]
    exact hpdvd
  have houter : OuterIdxAt p (.C r q) (StatedProj (StatedSp r K)) := by
    refine outerIdxAt_of_idxCoreAt hp fun x hxp hxo => ?_
    exact idxCoreAt_psp_of_outer_C hp hp2 hpq (by omega) hK hv hr3 hxp hxo hpdvdK
  exact outerIdxAt_of_mulEquiv hp eK.symm houter

private theorem idxCoreAt_psp_of_outer_B {r p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hr : 2 ≤ r) (hK : Nat.card K = q.p ^ q.exponent)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hB : r = 2 ∨ q.p = 2)
    {x : MulAut (StatedProj (StatedSp r K))} (hxp : x ^ p = 1)
    (hxo : x ∉ innAutDerived (StatedProj (StatedSp r K)))
    (hpdvd : p ∣ Nat.card (StatedProj (StatedSp r K))) :
    IdxCoreAt p (.B r q) x := by
  have hrq : ¬ (r = 2 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨h1, h2⟩
    have h2' : q.card = 2 := by
      rw [TauCeti.PrimePower.card_def]
      exact h2
    exact ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 ⟨h1, h2'⟩
  have hxH : x ∉ inner (StatedProj (StatedSp r K)) := fun h => hxo (inner_le_innAutDerived _ h)
  obtain ⟨σ, h, hσ, -, hxh, hk⟩ :=
    exists_conj_fieldAut_psp q.prime_p hp hp2 hpq q.exponent_pos hr hK hrq hxp hxH hpdvd
  have hδ : IdxCoreAt p (.B r q) (fieldAut r K σ) :=
    idxCoreAt_fieldAut_B hp hp2 hpq hr hK hv hB hσ hk
  exact idxCoreAt_of_conj hδ h⁻¹ (by rw [hxh]; group)

private theorem outerIdxAt_B_of_statedProj {r p : ℕ} {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (hr : 2 ≤ r) (hK : Nat.card K = q.p ^ q.exponent)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hB : r = 2 ∨ q.p = 2)
    (hpdvd : p ∣ Nat.card (StatedProj (StatedSp r K))) :
    OuterIdxAt p (.B r q) (StatedProj (StatedSp r K)) := by
  refine outerIdxAt_of_idxCoreAt hp fun x hxp hxo => ?_
  exact idxCoreAt_psp_of_outer_B hp hp2 hpq hr hK hv hB hxp hxo hpdvd

theorem outerIdxAt_B_PSp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hB : r = 2 ∨ q.p = 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B r q, hv⟩).Group)
    (hpq : p ≠ q.p) (hpdvd : p ∣ Nat.card S) : OuterIdxAt p (.B r q) S := by
  have hKcard : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .B r q →
      Nat.card ↥d.fixedField = q.card := by
    intro d hd
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    rw [hd, TauCeti.LieTypeIndex.characteristic_B, TauCeti.LieTypeIndex.fieldExponent_B]
    exact (TauCeti.PrimePower.card_def q).symm
  by_cases hr2 : r = 2
  · subst hr2
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩
    let K := ↥d.fixedField
    haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
    let eT := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
    let eN := e.trans eT
    haveI : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv S eN.toEquiv
    have hK' : Nat.card K = q.card := hKcard d rfl
    have hpdvdN : p ∣ Nat.card (StatedProj (StatedSp 2 K)) := by
      rw [← Nat.card_congr eN.toEquiv]
      exact hpdvd
    have houter := outerIdxAt_B_of_statedProj hp hp2 hpq (by omega) hK' hv (Or.inl rfl) hpdvdN
    exact outerIdxAt_of_mulEquiv hp eN.symm houter
  · have hr : 2 ≤ r :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    have hr3 : 3 ≤ r := by omega
    have hq2 : q.p = 2 := by
      rcases hB with h | h
      · omega
      · exact h
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.B r q, hv⟩
    let K := ↥d.fixedField
    haveI : Finite K := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
    let eT := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv
      hq2 hr3
    let eN := e.trans eT
    haveI : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv S eN.toEquiv
    have hK' : Nat.card K = q.card := hKcard d rfl
    have hpdvdN : p ∣ Nat.card (StatedProj (StatedSp r K)) := by
      rw [← Nat.card_congr eN.toEquiv]
      exact hpdvd
    have houter := outerIdxAt_B_of_statedProj hp hp2 hpq (by omega) hK' hv (Or.inr hq2) hpdvdN
    exact outerIdxAt_of_mulEquiv hp eN.symm houter

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
