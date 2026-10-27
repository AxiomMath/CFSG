module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812FieldAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Cases
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812CaseTwoSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Five
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812OmegaElem
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812GlueB
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Literature.GL52Group
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

private theorem mem_normalizer_of_acts {A : Subgroup G} {a : Fin 3 → G} {g : G}
    (hgen : Subgroup.closure {a 0, a 1, a 2} = A)
    (h0 : g * a 0 * g⁻¹ ∈ A) (h1 : g * a 1 * g⁻¹ ∈ A) (h2 : g * a 2 * g⁻¹ ∈ A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  have h : ∀ x ∈ ({a 0, a 1, a 2} : Set G), g * x * g⁻¹ ∈ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [h0, h1, h2]
  have hle : Subgroup.closure ({a 0, a 1, a 2} : Set G) ≤
      A.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    change (MulAut.conj g) x ∈ A
    simpa [MulAut.conj_apply] using h x hx
  refine Subgroup.mem_normalizer_fintype (S := (A : Set G)) (fun x hx => ?_)
  have hx' := hle (hgen ▸ hx)
  simpa [MulAut.conj_apply] using hx'

private theorem normalizer_le_of_caseTwo_data
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hAS : A ≤ S)
    (hA₁A : A₁ ≤ A) (hA₂A : A₂ ≤ A) (hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9)
    {a : Fin 3 → G} {y t₁ t₂ : G} {k : Fin 3} (hk : k ≠ 0) (hk12 : k = 1 ∨ k = 2)
    (haA : ∀ i, a i ∈ A) (hgen : Subgroup.closure {a 0, a 1, a 2} = A)
    (hz₁ : Subgroup.zpowers (a 1) = A₁) (hz₂ : Subgroup.zpowers (a 2) = A₂)
    (hyN : y ∈ Subgroup.normalizer (A : Set G))
    (ht₁N : t₁ ∈ Subgroup.normalizer (A : Set G))
    (ht₂N : t₂ ∈ Subgroup.normalizer (A : Set G))
    (h₁ : t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧
      t₁ * a 2 * t₁⁻¹ = a 2)
    (h₂ : t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧
      t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹)
    (hyk : y * a 0 * y⁻¹ = a 0 * a k ∧ y * a 1 * y⁻¹ = a 1 ∧
      y * a 2 * y⁻¹ = a 2) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy =>
    h.commute_of_isPGroup hSch hS.isPGroup ⟨hA₁S hx, hA₁ hx⟩ ⟨hA₂S hy, hA₂ hy⟩
  have hN1 : Subgroup.normalizer (Subgroup.zpowers (a 1) : Set G) ≤ M := by
    rw [hz₁]
    exact h.normalizer_le_of_le₁ hSch hA₁ hA₁3
  have hN2 : Subgroup.normalizer (Subgroup.zpowers (a 2) : Set G) ≤ M := by
    rw [hz₂]
    exact h.normalizer_le_of_le₂ hSch hA₂ hA₂3
  have hN12 : Subgroup.normalizer
      ((Subgroup.zpowers (a 1) ⊔ Subgroup.zpowers (a 2) : Subgroup G) : Set G) ≤ M := by
    rw [hz₁, hz₂]
    exact h.normalizer_sup_le hSch hA₁ hA₂ hA₁3 hA₂3 hcomm
  have hNM : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ M →
      g ∈ Subgroup.normalizer (Subgroup.zpowers (a 1) : Set G) ∧
        g ∈ Subgroup.normalizer (Subgroup.zpowers (a 2) : Set G) := by
    intro g hgA hgM
    have := h.mem_normalizer_of_mem_normalizer hAel hAS hA₁ hA₁A hA₁3 hA₂ hA₂A hA₂3
      hC hgA hgM
    simpa [hz₁, hz₂] using this
  exact CFSG.LocalAnalysis.RankThreeUC.S15.P812.caseII_normalizer_le (M := M) (A := A)
    (a := a) (t₁ := t₁) (t₂ := t₂) (x := y) (k := k) hk hk12 hAel h27 haA hgen
    ht₁N ht₂N hyN h₁ h₂ hyk hN1 hN2 hN12 hNM

private theorem exists_generator_of_card_three {A : Subgroup G} (hA3 : Nat.card A = 3) :
    ∃ b : G, Subgroup.zpowers b = A := by
  have hne : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA3
    omega
  obtain ⟨b, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hbA : (b : G) ∈ A := b.2
  have hb1 : (b : G) ≠ 1 := fun h => hbne (Subtype.ext h)
  exact ⟨(b : G),
    (CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_three hA3 hbA hb1).symm⟩

private theorem generator_data {A A₁ A₂ : Subgroup G} {a : Fin 3 → G} {a₀ b₁ b₂ : G}
    (ha0 : a 0 = a₀) (ha1 : a 1 = b₁) (ha2 : a 2 = b₂)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    (hA₁A : A₁ ≤ A) (hA₂A : A₂ ≤ A) (hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9)
    (ha₀A : a₀ ∈ A) (ha₀' : a₀ ∉ A₁ ⊔ A₂)
    (hz₁ : Subgroup.zpowers b₁ = A₁) (hz₂ : Subgroup.zpowers b₂ = A₂) :
    (∀ i, a i ∈ A) ∧ Subgroup.closure {a 0, a 1, a 2} = A := by
  have haA : ∀ i, a i ∈ A := by
    intro i
    fin_cases i
    · simpa [ha0] using ha₀A
    · simpa [ha1] using hA₁A (hz₁ ▸ Subgroup.mem_zpowers b₁)
    · simpa [ha2] using hA₂A (hz₂ ▸ Subgroup.mem_zpowers b₂)
  refine ⟨haA, ?_⟩
  have hset : ({a 0, a 1, a 2} : Set G) = {a₀, b₁, b₂} := by rw [ha0, ha1, ha2]
  rw [hset]
  exact closure_eq_of_not_mem_sup hAel h27 hA₁A hA₂A hA₁₂ ha₀A ha₀' hz₁ hz₂

private theorem elemAbelian_comm_data {Abig A B : Subgroup G} {a₀ : G}
    (hAel : CFSG.Open.IsElemAbelian 3 Abig) (ha₀ : a₀ ∈ Abig)
    (hAA : A ≤ Abig) (hBA : B ≤ Abig) :
    (∀ z ∈ A, ∀ b ∈ B, z * b = b * z) ∧
      (∀ z ∈ A, a₀ * z = z * a₀) ∧ (∀ b ∈ B, a₀ * b = b * a₀) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz b hb
    exact CFSG.Open.IsElemAbelian.comm hAel (hAA hz) (hBA hb)
  · intro z hz
    exact CFSG.Open.IsElemAbelian.comm hAel ha₀ (hAA hz)
  · intro b hb
    exact CFSG.Open.IsElemAbelian.comm hAel ha₀ (hBA hb)

private theorem le_centralizer_sup_of_elemAbelian {Abig A B : Subgroup G} {a₀ : G}
    (hAel : CFSG.Open.IsElemAbelian 3 Abig) (ha₀ : a₀ ∈ Abig)
    (hAA : A ≤ Abig) (hBA : B ≤ Abig) :
    A ≤ Subgroup.centralizer ((Subgroup.zpowers a₀ ⊔ B : Subgroup G) : Set G) := by
  rw [CFSG.centralizer_sup_eq]
  refine le_inf ?_ ?_
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact CFSG.Open.IsElemAbelian.comm hAel (Subgroup.zpowers_le.mpr ha₀ hw) (hAA hz)
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact CFSG.Open.IsElemAbelian.comm hAel (hBA hw) (hAA hz)

private theorem exists_y_left
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree)
    {S A A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (hA₁A : A₁ ≤ A)
    {a₀ : G} (ha₀A : a₀ ∈ A) (ha₀S : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1)
    (ha₀notL₁ : a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)) :
    ∃ y c : G, y ∈ S ⊓ L₁ ∧ Subgroup.zpowers c = A₁ ∧
      y * a₀ * y⁻¹ = a₀ * c ∧
      (∀ z ∈ A₁, y * z = z * y) ∧ (∀ z ∈ A₂, y * z = z * y) := by
  obtain ⟨y, hyS, hcA₁, hyne⟩ :=
    h.exists_mem_inf_conj_mul_inv_mem₁ hSch hK hFA hS hA₁ hA₁S hA₁3 ha₀S ha₀3 ha₀notL₁
  let c : G := y * a₀ * y⁻¹ * a₀⁻¹
  have hcA₁' : c ∈ A₁ := hcA₁
  have hcne : c ≠ 1 := by
    intro hc1
    apply hyne
    have h : y * a₀ * y⁻¹ = c * a₀ := by dsimp [c]; group
    rw [h, hc1, one_mul]
  have hzc : Subgroup.zpowers c = A₁ :=
    (CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_three hA₁3 hcA₁' hcne).symm
  have hyS' : y ∈ S := hyS.1
  have hyA₁ : ∀ z ∈ A₁, y * z = z * y := fun z hz =>
    (h.central₁ hS.le hS.isPGroup hA₁ hA₁S hA₁3 z hz y hyS').symm
  have hyA₂ : ∀ z ∈ A₂, y * z = z * y := fun z hz =>
    (h.central₂ hSch hS.le hS.isPGroup hA₂ hA₂S hA₂3 z hz y hyS').symm
  have hca : y * a₀ * y⁻¹ = c * a₀ := by dsimp [c]; group
  have hconv : y * a₀ * y⁻¹ = a₀ * c := by
    rw [hca]
    exact (CFSG.Open.IsElemAbelian.comm hAel ha₀A (hA₁A hcA₁')).symm
  exact ⟨y, c, hyS, hzc, hconv, hyA₁, hyA₂⟩

private theorem exists_y_right
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree)
    {S A A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (hA₂A : A₂ ≤ A)
    {a₀ : G} (ha₀A : a₀ ∈ A) (ha₀S : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1)
    (ha₀notL₂ : a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) :
    ∃ y c : G, y ∈ S ⊓ L₂ ∧ Subgroup.zpowers c = A₂ ∧
      y * a₀ * y⁻¹ = a₀ * c ∧
      (∀ z ∈ A₁, y * z = z * y) ∧ (∀ z ∈ A₂, y * z = z * y) := by
  obtain ⟨y, hyS, hcA₂, hyne⟩ :=
    h.exists_mem_inf_conj_mul_inv_mem₂ hSch hK hFA hS hA₂ hA₂S hA₂3 ha₀S ha₀3 ha₀notL₂
  let c : G := y * a₀ * y⁻¹ * a₀⁻¹
  have hcA₂' : c ∈ A₂ := hcA₂
  have hcne : c ≠ 1 := by
    intro hc1
    apply hyne
    have h : y * a₀ * y⁻¹ = c * a₀ := by dsimp [c]; group
    rw [h, hc1, one_mul]
  have hzc : Subgroup.zpowers c = A₂ :=
    (CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_three hA₂3 hcA₂' hcne).symm
  have hyS' : y ∈ S := hyS.1
  have hyA₁ : ∀ z ∈ A₁, y * z = z * y := fun z hz =>
    (h.central₁ hS.le hS.isPGroup hA₁ hA₁S hA₁3 z hz y hyS').symm
  have hyA₂ : ∀ z ∈ A₂, y * z = z * y := fun z hz =>
    (h.central₂ hSch hS.le hS.isPGroup hA₂ hA₂S hA₂3 z hz y hyS').symm
  have hca : y * a₀ * y⁻¹ = c * a₀ := by dsimp [c]; group
  have hconv : y * a₀ * y⁻¹ = a₀ * c := by
    rw [hca]
    exact (CFSG.Open.IsElemAbelian.comm hAel ha₀A (hA₂A hcA₂')).symm
  exact ⟨y, c, hyS, hzc, hconv, hyA₁, hyA₂⟩

private theorem inverting_join
    (h : P812Hyp G M p L₁ L₂)
    {K B A : Subgroup G} {a₀ : G} (hKM : K ≤ M)
    (hKcomp : CFSG.IsPComponent p (K.subgroupOf M))
    (hr : CFSG.Open.pRank 3 K = 1) (hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore p ↥K))
    (hAK : A ≤ K) (hA3 : Nat.card A = 3)
    (hB : IsPGroup 3 B) (hBM : B ≤ M)
    (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hcommB : ⁅B, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype)
    (hAc : A ≤ Subgroup.centralizer ((Subgroup.zpowers a₀ ⊔ B : Subgroup G) : Set G))
    (ha₀C : a₀ ∈ CFSG.GH74.GLS.centralizerSection K
      ((CFSG.pPrimeCore p ↥K).map K.subtype))
    (ha₀M : a₀ ∈ M) (ha₀1 : a₀ ≠ 1) (ha₀3 : a₀ ^ 3 = 1)
    (hc : ∀ x ∈ Subgroup.zpowers a₀, ∀ y ∈ B, x * y = y * x) :
    ∃ t ∈ K, t * a₀ = a₀ * t ∧ (∀ b ∈ B, t * b = b * t) ∧
      ∀ z ∈ A, t * z * t⁻¹ = z⁻¹ := by
  have hcomm₁ : ⁅Subgroup.zpowers a₀, K⁆ ≤ (CFSG.pPrimeCore p ↥K).map K.subtype :=
    commutator_le_of_le_centralizerSection (Subgroup.zpowers_le.mpr ha₀C)
  have hB₁ : IsPGroup 3 (Subgroup.zpowers a₀) :=
    IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime ha₀3 ha₀1]; norm_num)
  have hB₁M : Subgroup.zpowers a₀ ≤ M := Subgroup.zpowers_le.mpr ha₀M
  have hB₁K : Subgroup.zpowers a₀ ≤ Subgroup.normalizer (K : Set G) :=
    fun z hz => (Subgroup.zpowers_le.mpr ha₀C hz).1
  obtain ⟨t, ht, htinv⟩ :=
    exists_inv_mem_inf_centralizer_sup_of_le h.prime hKM hKcomp hr hcop hB₁ hB hB₁M hBM
      hc hB₁K hBK hcomm₁ hcommB hAK hA3 hAc
  have htC₀ : t ∈ Subgroup.centralizer (Subgroup.zpowers a₀ : Set G) :=
    (CFSG.centralizer_sup_eq (Subgroup.zpowers a₀) B ▸ ht.2).1
  have htCB : t ∈ Subgroup.centralizer (B : Set G) :=
    (CFSG.centralizer_sup_eq (Subgroup.zpowers a₀) B ▸ ht.2).2
  refine ⟨t, ht.1, ?_, ?_, htinv⟩
  · exact (Subgroup.mem_centralizer_iff.mp htC₀ a₀ (Subgroup.mem_zpowers a₀)).symm
  · intro b hb
    exact (Subgroup.mem_centralizer_iff.mp htCB b hb).symm

private theorem inverting_simple_left
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFI : KFactFieldAutInvert)
    {S A B : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA : A ≤ L₁) (hAS : A ≤ S) (hA3 : Nat.card A = 3)
    (hBS : B ≤ S) (hBL : ⁅B, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
    (hAB : ∀ z ∈ A, ∀ b ∈ B, z * b = b * z)
    {a₀ : G} (ha₀S : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1)
    (ha₀notL₁ : a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (haA : ∀ z ∈ A, a₀ * z = z * a₀) (haB : ∀ b ∈ B, a₀ * b = b * a₀) :
    ∃ t ∈ L₁, t * a₀ = a₀ * t ∧ (∀ b ∈ B, t * b = b * t) ∧
      ∀ z ∈ A, t * z * t⁻¹ = z⁻¹ :=
  h.exists_inv_mem_centralizer₁ hSch hK hFI hSM hS3 hA hAS hA3 hBS hBL hAB
    ha₀S ha₀3 ha₀notL₁ haA haB

private theorem inverting_simple_right
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFI : KFactFieldAutInvert)
    {S A B : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA : A ≤ L₂) (hAS : A ≤ S) (hA3 : Nat.card A = 3)
    (hBS : B ≤ S) (hBL : ⁅B, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
    (hAB : ∀ z ∈ A, ∀ b ∈ B, z * b = b * z)
    {a₀ : G} (ha₀S : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1)
    (ha₀notL₂ : a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))
    (haA : ∀ z ∈ A, a₀ * z = z * a₀) (haB : ∀ b ∈ B, a₀ * b = b * a₀) :
    ∃ t ∈ L₂, t * a₀ = a₀ * t ∧ (∀ b ∈ B, t * b = b * t) ∧
      ∀ z ∈ A, t * z * t⁻¹ = z⁻¹ :=
  h.exists_inv_mem_centralizer₂ hSch hK hFI hSM hS3 hA hAS hA3 hBS hBL hAB
    ha₀S ha₀3 ha₀notL₂ haA haB

private theorem action_data {A : Subgroup G} {a : Fin 3 → G} {a₀ b₁ b₂ y t₁ t₂ : G} {k : Fin 3}
    (ha0 : a 0 = a₀) (ha1 : a 1 = b₁) (ha2 : a 2 = b₂)
    (haA : ∀ i, a i ∈ A) (hgen : Subgroup.closure {a 0, a 1, a 2} = A)
    (hy0 : y * a₀ * y⁻¹ = a₀ * a k)
    (hy1 : y * b₁ = b₁ * y) (hy2 : y * b₂ = b₂ * y)
    (ht₁a : t₁ * a₀ = a₀ * t₁) (ht₁inv : t₁ * b₁ * t₁⁻¹ = b₁⁻¹)
    (ht₁fix : t₁ * b₂ * t₁⁻¹ = b₂)
    (ht₂a : t₂ * a₀ = a₀ * t₂) (ht₂fix : t₂ * b₁ * t₂⁻¹ = b₁)
    (ht₂inv : t₂ * b₂ * t₂⁻¹ = b₂⁻¹) :
    (y * a 0 * y⁻¹ = a 0 * a k ∧ y * a 1 * y⁻¹ = a 1 ∧ y * a 2 * y⁻¹ = a 2) ∧
    (t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧
      t₁ * a 2 * t₁⁻¹ = a 2) ∧
    (t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧
      t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹) ∧
    y ∈ Subgroup.normalizer (A : Set G) ∧
      t₁ ∈ Subgroup.normalizer (A : Set G) ∧
      t₂ ∈ Subgroup.normalizer (A : Set G) := by
  have hyk : y * a 0 * y⁻¹ = a 0 * a k ∧ y * a 1 * y⁻¹ = a 1 ∧
      y * a 2 * y⁻¹ = a 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha0]; exact hy0
    · rw [ha1]; exact Commute.mul_inv_cancel hy1
    · rw [ha2]; exact Commute.mul_inv_cancel hy2
  have h₁ : t₁ * a 0 * t₁⁻¹ = a 0 ∧ t₁ * a 1 * t₁⁻¹ = (a 1)⁻¹ ∧
      t₁ * a 2 * t₁⁻¹ = a 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha0]; exact Commute.mul_inv_cancel ht₁a
    · rw [ha1]; exact ht₁inv
    · rw [ha2]; exact ht₁fix
  have h₂ : t₂ * a 0 * t₂⁻¹ = a 0 ∧ t₂ * a 1 * t₂⁻¹ = a 1 ∧
      t₂ * a 2 * t₂⁻¹ = (a 2)⁻¹ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha0]; exact Commute.mul_inv_cancel ht₂a
    · rw [ha1]; exact ht₂fix
    · rw [ha2]; exact ht₂inv
  have hyN : y ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_acts hgen ?_ ?_ ?_
    · rw [hyk.1]; exact A.mul_mem (haA 0) (haA k)
    · rw [hyk.2.1]; exact haA 1
    · rw [hyk.2.2]; exact haA 2
  have ht₁N : t₁ ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_acts hgen ?_ ?_ ?_
    · rw [h₁.1]; exact haA 0
    · rw [h₁.2.1]; exact A.inv_mem (haA 1)
    · rw [h₁.2.2]; exact haA 2
  have ht₂N : t₂ ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_acts hgen ?_ ?_ ?_
    · rw [h₂.1]; exact haA 0
    · rw [h₂.2.1]; exact haA 1
    · rw [h₂.2.2]; exact A.inv_mem (haA 2)
  exact ⟨hyk, h₁, h₂, hyN, ht₁N, ht₂N⟩

private theorem case_one_normalizer_le
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree) (hFI : KFactFieldAutInvert)
    {S A A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hAS : A ≤ S)
    (hA₁A : A₁ ≤ A) (hA₂A : A₂ ≤ A) (hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9)
    {a₀ : G} (ha₀A : a₀ ∈ A) (ha₀' : a₀ ∉ A₁ ⊔ A₂)
    (ha₀C₁ : a₀ ∈ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (ha₀notL₂ : a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha₀S : a₀ ∈ S := hAS ha₀A
  have ha₀3 : a₀ ^ 3 = 1 := hAel.2 a₀ ha₀A
  have ha₀1 : a₀ ≠ 1 := by
    intro h1
    exact ha₀' (h1 ▸ (A₁ ⊔ A₂).one_mem)
  obtain ⟨y, c, -, hzc, hconv, hyA₁, hyA₂⟩ :=
    exists_y_right h hSch hK hFA hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hAel hA₂A
      ha₀A ha₀S ha₀3 ha₀notL₂
  obtain ⟨b₁, hz₁⟩ := exists_generator_of_card_three hA₁3
  let a : Fin 3 → G := ![a₀, b₁, c]
  have ha0 : a 0 = a₀ := by simp [a]
  have ha1 : a 1 = b₁ := by simp [a]
  have ha2 : a 2 = c := by simp [a]
  obtain ⟨haA, hgen⟩ :=
    generator_data ha0 ha1 ha2 hAel h27 hA₁A hA₂A hA₁₂ ha₀A ha₀' hz₁ hzc
  have hb₁A₁ : b₁ ∈ A₁ := hz₁ ▸ Subgroup.mem_zpowers b₁
  have hcA₂ : c ∈ A₂ := hzc ▸ Subgroup.mem_zpowers c
  have hy0 : y * a₀ * y⁻¹ = a₀ * a 2 := by rw [ha2]; exact hconv
  have hA₂C₁ : A₂ ≤ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :=
    hA₂.trans (le_centralizerSection_of_ne h.prime ⟨h.le₂, h.comp₂⟩ ⟨h.le₁, h.comp₁⟩
      h.ne.symm)
  have hB₂K : A₂ ≤ Subgroup.normalizer (L₁ : Set G) := fun z hz => (hA₂C₁ hz).1
  have hcomm₂ : ⁅A₂, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype :=
    commutator_le_of_le_centralizerSection hA₂C₁
  have hB₂ : IsPGroup 3 A₂ := IsPGroup.of_card (n := 1) (by rw [hA₂3]; norm_num)
  have hAc₁ : A₁ ≤ Subgroup.centralizer
      ((Subgroup.zpowers a₀ ⊔ A₂ : Subgroup G) : Set G) :=
    le_centralizer_sup_of_elemAbelian hAel ha₀A hA₁A hA₂A
  have hc₁ : ∀ x ∈ Subgroup.zpowers a₀, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hAel (Subgroup.zpowers_le.mpr ha₀A hx) (hA₂A hy)
  obtain ⟨t₁, -, ht₁a, ht₁B, ht₁inv⟩ :=
    inverting_join h h.le₁ h.comp₁ h.rank_three₁
      (h.not_three_dvd_card_pPrimeCore₁ hSch) hA₁ hA₁3 hB₂ (hA₂.trans h.le₂) hB₂K
      hcomm₂ hAc₁ ha₀C₁ (hS.le ha₀S) ha₀1 ha₀3 hc₁
  have hA₁C₂ : A₁ ≤ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :=
    hA₁.trans (le_centralizerSection_of_ne h.prime ⟨h.le₁, h.comp₁⟩ ⟨h.le₂, h.comp₂⟩ h.ne)
  have hBL : ⁅A₁, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype :=
    commutator_le_of_le_centralizerSection hA₁C₂
  obtain ⟨hAB, haA₂, haA₁⟩ := elemAbelian_comm_data hAel ha₀A hA₂A hA₁A
  obtain ⟨t₂, -, ht₂a, ht₂B, ht₂inv⟩ :=
    inverting_simple_right h hSch hK hFI hS.le hS.isPGroup hA₂ hA₂S hA₂3 hA₁S hBL hAB
      ha₀S ha₀3 ha₀notL₂ haA₂ haA₁
  obtain ⟨hyk, h₁, h₂, hyN, ht₁N, ht₂N⟩ :=
    action_data ha0 ha1 ha2 haA hgen hy0 (hyA₁ b₁ hb₁A₁) (hyA₂ c hcA₂)
      ht₁a (ht₁inv b₁ hb₁A₁) (Commute.mul_inv_cancel (ht₁B c hcA₂))
      ht₂a (Commute.mul_inv_cancel (ht₂B b₁ hb₁A₁)) (ht₂inv c hcA₂)
  exact normalizer_le_of_caseTwo_data h hSch hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
    hAel h27 hAS hA₁A hA₂A hA₁₂ (a := a) (y := y) (t₁ := t₁) (t₂ := t₂) (k := 2)
    (by norm_num) (Or.inr rfl) haA hgen hz₁ hzc hyN ht₁N ht₂N h₁ h₂ hyk

private theorem case_two_normalizer_le
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree) (hFI : KFactFieldAutInvert)
    {S A A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hAS : A ≤ S)
    (hA₁A : A₁ ≤ A) (hA₂A : A₂ ≤ A) (hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9)
    {a₀ : G} (ha₀A : a₀ ∈ A) (ha₀' : a₀ ∉ A₁ ⊔ A₂)
    (ha₀C₂ : a₀ ∈ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))
    (ha₀notL₁ : a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha₀S : a₀ ∈ S := hAS ha₀A
  have ha₀3 : a₀ ^ 3 = 1 := hAel.2 a₀ ha₀A
  have ha₀1 : a₀ ≠ 1 := by
    intro h1
    exact ha₀' (h1 ▸ (A₁ ⊔ A₂).one_mem)
  obtain ⟨y, c, -, hzc, hconv, hyA₁, hyA₂⟩ :=
    exists_y_left h hSch hK hFA hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hAel hA₁A
      ha₀A ha₀S ha₀3 ha₀notL₁
  obtain ⟨b₂, hz₂⟩ := exists_generator_of_card_three hA₂3
  let a : Fin 3 → G := ![a₀, c, b₂]
  have ha0 : a 0 = a₀ := by simp [a]
  have ha1 : a 1 = c := by simp [a]
  have ha2 : a 2 = b₂ := by simp [a]
  obtain ⟨haA, hgen⟩ :=
    generator_data ha0 ha1 ha2 hAel h27 hA₁A hA₂A hA₁₂ ha₀A ha₀' hzc hz₂
  have hcA₁ : c ∈ A₁ := hzc ▸ Subgroup.mem_zpowers c
  have hb₂A₂ : b₂ ∈ A₂ := hz₂ ▸ Subgroup.mem_zpowers b₂
  have hy0 : y * a₀ * y⁻¹ = a₀ * a 1 := by rw [ha1]; exact hconv
  have hA₂C₁ : A₂ ≤ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :=
    hA₂.trans (le_centralizerSection_of_ne h.prime ⟨h.le₂, h.comp₂⟩ ⟨h.le₁, h.comp₁⟩
      h.ne.symm)
  have hBL₁ : ⁅A₂, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype :=
    commutator_le_of_le_centralizerSection hA₂C₁
  obtain ⟨hAB, haA₁, haA₂⟩ := elemAbelian_comm_data hAel ha₀A hA₁A hA₂A
  obtain ⟨t₁, -, ht₁a, ht₁B, ht₁inv⟩ :=
    inverting_simple_left h hSch hK hFI hS.le hS.isPGroup hA₁ hA₁S hA₁3 hA₂S hBL₁ hAB
      ha₀S ha₀3 ha₀notL₁ haA₁ haA₂
  have hA₁C₂ : A₁ ≤ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :=
    hA₁.trans (le_centralizerSection_of_ne h.prime ⟨h.le₁, h.comp₁⟩ ⟨h.le₂, h.comp₂⟩ h.ne)
  have hB₂K : A₁ ≤ Subgroup.normalizer (L₂ : Set G) := fun z hz => (hA₁C₂ hz).1
  have hcomm₂ : ⁅A₁, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype :=
    commutator_le_of_le_centralizerSection hA₁C₂
  have hB₂ : IsPGroup 3 A₁ := IsPGroup.of_card (n := 1) (by rw [hA₁3]; norm_num)
  have hAc₂ : A₂ ≤ Subgroup.centralizer
      ((Subgroup.zpowers a₀ ⊔ A₁ : Subgroup G) : Set G) :=
    le_centralizer_sup_of_elemAbelian hAel ha₀A hA₂A hA₁A
  have hc₂ : ∀ x ∈ Subgroup.zpowers a₀, ∀ y ∈ A₁, x * y = y * x := fun x hx y hy =>
    CFSG.Open.IsElemAbelian.comm hAel (Subgroup.zpowers_le.mpr ha₀A hx) (hA₁A hy)
  obtain ⟨t₂, -, ht₂a, ht₂B, ht₂inv⟩ :=
    inverting_join h h.le₂ h.comp₂ h.rank_three₂
      (h.not_three_dvd_card_pPrimeCore₂ hSch) hA₂ hA₂3 hB₂ (hA₁.trans h.le₁) hB₂K
      hcomm₂ hAc₂ ha₀C₂ (hS.le ha₀S) ha₀1 ha₀3 hc₂
  obtain ⟨hyk, h₁, h₂, hyN, ht₁N, ht₂N⟩ :=
    action_data ha0 ha1 ha2 haA hgen hy0 (hyA₁ c hcA₁) (hyA₂ b₂ hb₂A₂)
      ht₁a (ht₁inv c hcA₁) (Commute.mul_inv_cancel (ht₁B b₂ hb₂A₂))
      ht₂a (Commute.mul_inv_cancel (ht₂B c hcA₁)) (ht₂inv b₂ hb₂A₂)
  exact normalizer_le_of_caseTwo_data h hSch hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
    hAel h27 hAS hA₁A hA₂A hA₁₂ (a := a) (y := y) (t₁ := t₁) (t₂ := t₂) (k := 1)
    (by norm_num) (Or.inl rfl) haA hgen hzc hz₂ hyN ht₁N ht₂N h₁ h₂ hyk

private theorem case_three_normalizer_le
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M) (hFA : KFactFieldAutThree) (hFI : KFactFieldAutInvert)
    {S A A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hAel : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hAS : A ≤ S)
    (hA₁A : A₁ ≤ A) (hA₂A : A₂ ≤ A) (hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9)
    {a₀ : G} (ha₀A : a₀ ∈ A) (ha₀' : a₀ ∉ A₁ ⊔ A₂)
    (ha₀notL₁ : a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (ha₀notL₂ : a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha₀S : a₀ ∈ S := hAS ha₀A
  have ha₀3 : a₀ ^ 3 = 1 := hAel.2 a₀ ha₀A
  obtain ⟨y, c, -, hzc, hconv, hyA₁, hyA₂⟩ :=
    exists_y_left h hSch hK hFA hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hAel hA₁A
      ha₀A ha₀S ha₀3 ha₀notL₁
  obtain ⟨b₂, hz₂⟩ := exists_generator_of_card_three hA₂3
  let a : Fin 3 → G := ![a₀, c, b₂]
  have ha0 : a 0 = a₀ := by simp [a]
  have ha1 : a 1 = c := by simp [a]
  have ha2 : a 2 = b₂ := by simp [a]
  obtain ⟨haA, hgen⟩ :=
    generator_data ha0 ha1 ha2 hAel h27 hA₁A hA₂A hA₁₂ ha₀A ha₀' hzc hz₂
  have hcA₁ : c ∈ A₁ := hzc ▸ Subgroup.mem_zpowers c
  have hb₂A₂ : b₂ ∈ A₂ := hz₂ ▸ Subgroup.mem_zpowers b₂
  have hy0 : y * a₀ * y⁻¹ = a₀ * a 1 := by rw [ha1]; exact hconv
  have hA₂C₁ : A₂ ≤ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :=
    hA₂.trans (le_centralizerSection_of_ne h.prime ⟨h.le₂, h.comp₂⟩ ⟨h.le₁, h.comp₁⟩
      h.ne.symm)
  have hBL₁ : ⁅A₂, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype :=
    commutator_le_of_le_centralizerSection hA₂C₁
  obtain ⟨hAB, haA₁, haA₂⟩ := elemAbelian_comm_data hAel ha₀A hA₁A hA₂A
  obtain ⟨t₁, -, ht₁a, ht₁B, ht₁inv⟩ :=
    inverting_simple_left h hSch hK hFI hS.le hS.isPGroup hA₁ hA₁S hA₁3 hA₂S hBL₁ hAB
      ha₀S ha₀3 ha₀notL₁ haA₁ haA₂
  have hA₁C₂ : A₁ ≤ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :=
    hA₁.trans (le_centralizerSection_of_ne h.prime ⟨h.le₁, h.comp₁⟩ ⟨h.le₂, h.comp₂⟩ h.ne)
  have hBL₂ : ⁅A₁, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype :=
    commutator_le_of_le_centralizerSection hA₁C₂
  obtain ⟨hAB₂, haA₂, haA₁⟩ := elemAbelian_comm_data hAel ha₀A hA₂A hA₁A
  obtain ⟨t₂, -, ht₂a, ht₂B, ht₂inv⟩ :=
    inverting_simple_right h hSch hK hFI hS.le hS.isPGroup hA₂ hA₂S hA₂3 hA₁S hBL₂ hAB₂
      ha₀S ha₀3 ha₀notL₂ haA₂ haA₁
  obtain ⟨hyk, h₁, h₂, hyN, ht₁N, ht₂N⟩ :=
    action_data ha0 ha1 ha2 haA hgen hy0 (hyA₁ c hcA₁) (hyA₂ b₂ hb₂A₂)
      ht₁a (ht₁inv c hcA₁) (Commute.mul_inv_cancel (ht₁B b₂ hb₂A₂))
      ht₂a (Commute.mul_inv_cancel (ht₂B c hcA₁)) (ht₂inv b₂ hb₂A₂)
  exact normalizer_le_of_caseTwo_data h hSch hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
    hAel h27 hAS hA₁A hA₂A hA₁₂ (a := a) (y := y) (t₁ := t₁) (t₂ := t₂) (k := 1)
    (by norm_num) (Or.inl rfl) haA hgen hzc hz₂ hyN ht₁N ht₂N h₁ h₂ hyk

theorem normalizer_le_of_caseTwo (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    (hFA : KFactFieldAutThree) (hFI : KFactFieldAutInvert)
    {S A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1) (hx : x ∉ A₁ ⊔ A₂) :
    Subgroup.normalizer ((Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := P812Hyp.isElemAbelian_zpowers_sup h hSch hK h714 hS.le hS.isPGroup hA₁ hA₁S hA₁3
    hA₂ hA₂S hA₂3 hC hxS hx3 hx
  have hAel : CFSG.Open.IsElemAbelian 3
      (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) := hE.1
  have h27 : Nat.card (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) = 27 := hE.2
  have hAS : (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) ≤ S := by
    refine sup_le ?_ hA₂S
    exact sup_le (Subgroup.zpowers_le.mpr hxS) hA₁S
  have hA₁A : A₁ ≤ (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) := by
    intro a ha
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ha)
  have hA₂A : A₂ ≤ (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) := by
    intro a ha
    exact Subgroup.mem_sup_right ha
  have hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9 :=
    P812Hyp.card_sup_eq_nine h hSch hS.isPGroup hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3
  have hxA : x ∈ (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  obtain ⟨a₀, ha₀A, ha₀', hcases⟩ :=
    h.exists_outer_mem (S := S) (A := Subgroup.zpowers x ⊔ A₁ ⊔ A₂)
      (A₁ := A₁) (A₂ := A₂) hSch hS.le hS.isPGroup hAel hAS hA₁ hA₁A hA₁3 hA₂ hA₂A
      hA₂3 hC hxA hx
  rcases hcases with ⟨ha₀C₁, ha₀notL₂⟩ | ⟨ha₀C₂, ha₀notL₁⟩ | ⟨ha₀notL₁, ha₀notL₂⟩
  · exact case_one_normalizer_le (S := S) (A := Subgroup.zpowers x ⊔ A₁ ⊔ A₂)
      (A₁ := A₁) (A₂ := A₂) h hSch hK hFA hFI hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
      hAel h27 hAS hA₁A hA₂A hA₁₂ ha₀A ha₀' ha₀C₁ ha₀notL₂
  · exact case_two_normalizer_le (S := S) (A := Subgroup.zpowers x ⊔ A₁ ⊔ A₂)
      (A₁ := A₁) (A₂ := A₂) h hSch hK hFA hFI hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
      hAel h27 hAS hA₁A hA₂A hA₁₂ ha₀A ha₀' ha₀C₂ ha₀notL₁
  · exact case_three_normalizer_le (S := S) (A := Subgroup.zpowers x ⊔ A₁ ⊔ A₂)
      (A₁ := A₁) (A₂ := A₂) h hSch hK hFA hFI hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
      hAel h27 hAS hA₁A hA₂A hA₁₂ ha₀A ha₀' ha₀notL₁ ha₀notL₂

theorem mem_uniqueSet_of_caseTwo (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    (hFA : KFactFieldAutThree) (hFI : KFactFieldAutInvert)
    {S A₁ A₂ : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1) (hx : x ∉ A₁ ⊔ A₂) :
    A₁ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M ∧
      A₂ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := P812Hyp.isElemAbelian_zpowers_sup h hSch hK h714 hS.le hS.isPGroup hA₁ hA₁S hA₁3
    hA₂ hA₂S hA₂3 hC hxS hx3 hx
  have hAel : CFSG.Open.IsElemAbelian 3
      (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) := hE.1
  have hAS : (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) ≤ S := by
    refine sup_le ?_ hA₂S
    exact sup_le (Subgroup.zpowers_le.mpr hxS) hA₁S
  have hA₁A : A₁ ≤ (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) := by
    intro a ha
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ha)
  have hA₂A : A₂ ≤ (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) := by
    intro a ha
    exact Subgroup.mem_sup_right ha
  have hΩ : ∀ y ∈ S, y ^ 3 = 1 → y ∈ (Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) :=
    fun y hyS hy3 =>
      h.mem_sup_of_pow_three_eq_one hSch hK h714 hS.le hS.isPGroup hA₁ hA₁S hA₁3
        hA₂ hA₂S hA₂3 hC hxS hx3 hx hyS hy3
  have hNA : Subgroup.normalizer
      ((Subgroup.zpowers x ⊔ A₁ ⊔ A₂ : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_caseTwo h hSch hK h714 hFA hFI hS hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3
      hC hxS hx3 hx
  exact ⟨mem_uniqueSet_of_normalizer_le_of_omega (S := S)
      (A := Subgroup.zpowers x ⊔ A₁ ⊔ A₂) hS hAS hAel hΩ hNA hA₁A
      (h.normalizer_le_of_le₁ hSch hA₁ hA₁3),
    mem_uniqueSet_of_normalizer_le_of_omega (S := S)
      (A := Subgroup.zpowers x ⊔ A₁ ⊔ A₂) hS hAS hAel hΩ hNA hA₂A
      (h.normalizer_le_of_le₂ hSch hA₂ hA₂3)⟩

theorem mem_uniqueSet
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    (hFA : KFactFieldAutThree) (hFI : KFactFieldAutInvert)
    {A : Subgroup G} (hA3 : Nat.card A = 3) (hA : A ≤ L₁ ∨ A ≤ L₂) :
    A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  classical
  rcases h.mem_uniqueSet_or_caseTwo hSch hA3 hA with hUA |
    ⟨S, A₁, A₂, hS, hA₁, hA₁S, hA₁3, hA₂, hA₂S, hA₂3, hAA, hC, hx⟩
  · exact hUA
  · obtain ⟨x, hxS, hx3, hxnot⟩ := hx
    rcases hAA with rfl | rfl
    · exact (mem_uniqueSet_of_caseTwo h hSch hK h714 hFA hFI hS hA₁ hA₁S hA₁3
        hA₂ hA₂S hA₂3 hC hxS hx3 hxnot).1
    · exact (mem_uniqueSet_of_caseTwo h hSch hK h714 hFA hFI hS hA₁ hA₁S hA₁3
        hA₂ hA₂S hA₂3 hC hxS hx3 hxnot).2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

theorem p812Gen_of_inputs
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    (hFA : Section8.KFactFieldAutThree) (hFI : Section8.KFactFieldAutInvert) :
    P812Gen := by
  intro G _ _ hC M hM hne hstrong
  haveI : IsSimpleGroup G := hC.simple
  have hMne : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.nonab M hM.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hC.kProper hMne
  have hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M :=
    CFSG.LocalAnalysis.RankThreeUC.S15.KSch.schreierSections
      (CFSG.LocalAnalysis.RankThreeUC.S15.kSch_of_catalog
        CFSG.AGLEmbedding.kFactCatalogSchreier) hK
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.p812At_of_hyp
    (fun p L₁ L₂ h A hA3 hA =>
      CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet (A := A) h hSch hK h714
        hFA hFI hA3 hA)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
