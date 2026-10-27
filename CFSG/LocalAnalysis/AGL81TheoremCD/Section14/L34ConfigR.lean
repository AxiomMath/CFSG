module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KCapM
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.RankThree.PartOne.S11d.FinalLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped Pointwise

variable {G : Type} [Group G]

private def commutatorModPCore (A T : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ T ∧ ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T)}
  one_mem' := ⟨T.one_mem, fun a _ => by simp⟩
  mul_mem' := by
    intro x y hx hy
    have hTR : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
      (le_sup_right : T ≤ A ⊔ T).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
    refine ⟨T.mul_mem hx.1 hy.1, fun a ha => ?_⟩
    have h1 : x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hTR hx.1) _).mp (hy.2 a ha)
    have h2 : x * a * x⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := hx.2 a ha
    have e : x * y * a * (x * y)⁻¹ * a⁻¹ =
        x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    intro x hx
    have hTR : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
      (le_sup_right : T ≤ A ⊔ T).trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
    refine ⟨T.inv_mem hx.1, fun a ha => ?_⟩
    have h1 : x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
      have h := (Subgroup.mem_normalizer_iff.mp (hTR (T.inv_mem hx.1)) _).mp
        (Subgroup.inv_mem _ (hx.2 a ha))
      simpa using h
    have e : x⁻¹ * a * (x⁻¹)⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x := by group
    rwa [e]

private theorem commutatorModPCore_le (A T : Subgroup G) :
    commutatorModPCore A T ≤ A ⊔ T :=
  fun _ hx => Subgroup.mem_sup_right hx.1

private theorem conj_mem_commutatorModPCore_A {A T : Subgroup G}
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T) {a₀ d : G} (ha₀ : a₀ ∈ A)
    (hd : d ∈ commutatorModPCore A T) : a₀ * d * a₀⁻¹ ∈ commutatorModPCore A T := by
  have hTR : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_right : T ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  refine ⟨?_, fun a ha => ?_⟩
  · have h1 : d⁻¹ * a₀ * d * a₀⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
      have hmem : (d * a₀ * d⁻¹ * a₀⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) :=
        Subgroup.inv_mem _ (hd.2 a₀ ha₀)
      have hconj := (Subgroup.mem_normalizer_iff.mp (hTR (T.inv_mem hd.1)) _).mp hmem
      have e : d⁻¹ * a₀ * d * a₀⁻¹ = d⁻¹ * (d * a₀ * d⁻¹ * a₀⁻¹)⁻¹ * d := by group
      rw [e]
      simpa using hconj
    have e : a₀ * d * a₀⁻¹ = d * (d⁻¹ * a₀ * d * a₀⁻¹) := by group
    rw [e]
    exact T.mul_mem hd.1 (hRT h1)
  · have h1 : d * (a₀⁻¹ * a * a₀) * d⁻¹ * (a₀⁻¹ * a * a₀)⁻¹ ∈
        CFSG.Open.pCoreOf 2 (A ⊔ T) :=
      hd.2 _ (A.mul_mem (A.mul_mem (A.inv_mem ha₀) ha) ha₀)
    have hconj := (Subgroup.mem_normalizer_iff.mp (hAR ha₀) _).mp h1
    have e : a₀ * d * a₀⁻¹ * a * (a₀ * d * a₀⁻¹)⁻¹ * a⁻¹ =
        a₀ * (d * (a₀⁻¹ * a * a₀) * d⁻¹ * (a₀⁻¹ * a * a₀)⁻¹) * a₀⁻¹ := by group
    rwa [e]

private theorem conj_mem_commutatorModPCore_T {A T : Subgroup G}
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G)) {s d : G} (hs : s ∈ T)
    (hd : d ∈ commutatorModPCore A T) : s * d * s⁻¹ ∈ commutatorModPCore A T := by
  have hTR : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_right : T ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  refine ⟨T.mul_mem (T.mul_mem hs hd.1) (T.inv_mem hs), fun a ha => ?_⟩
  have hmem : s⁻¹ * a * s ∈ A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hTAR (T.inv_mem hs)) a).mp
      (Subgroup.mem_sup_left ha)
  have e₂ : s * d * s⁻¹ * a * (s * d * s⁻¹)⁻¹ * a⁻¹ =
      s * (d * (s⁻¹ * a * s) * d⁻¹ * (s⁻¹ * a * s)⁻¹) * s⁻¹ := by group
  rw [e₂]
  have hset : ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G) =
      (A : Set G) * (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A _ hAR
  have hmem' : s⁻¹ * a * s ∈ (A : Set G) * (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) := by
    rw [← hset]
    exact hmem
  obtain ⟨a', ha', r', hr', heq⟩ := hmem'
  rw [← heq]
  have hdr1 : d * r' * d⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp (hTR hd.1) r').mp hr'
  have hdr : d * r' * d⁻¹ * r'⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) :=
    (CFSG.Open.pCoreOf 2 (A ⊔ T)).mul_mem hdr1
      ((CFSG.Open.pCoreOf 2 (A ⊔ T)).inv_mem hr')
  have hinner : d * (a' * r') * d⁻¹ * (a' * r')⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
    have e : d * (a' * r') * d⁻¹ * (a' * r')⁻¹ =
        (d * a' * d⁻¹ * a'⁻¹) * (a' * (d * r' * d⁻¹ * r'⁻¹) * a'⁻¹) := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 (A ⊔ T)).mul_mem (hd.2 a' ha')
      ((Subgroup.mem_normalizer_iff.mp (hAR ha') _).mp hdr)
  exact (Subgroup.mem_normalizer_iff.mp (hTR hs) _).mp hinner

private theorem le_normalizer_commutatorModPCore_A {A T : Subgroup G}
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T) :
    A ≤ Subgroup.normalizer (commutatorModPCore A T : Set G) := by
  intro a₀ ha₀
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact conj_mem_commutatorModPCore_A hRT ha₀
  · intro hd
    have h := conj_mem_commutatorModPCore_A hRT (A.inv_mem ha₀) hd
    have e : a₀⁻¹ * (a₀ * d * a₀⁻¹) * (a₀⁻¹)⁻¹ = d := by group
    rwa [e] at h

private theorem le_normalizer_commutatorModPCore_T {A T : Subgroup G}
    (hTAR : T ≤ Subgroup.normalizer
      ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G)) :
    T ≤ Subgroup.normalizer (commutatorModPCore A T : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact conj_mem_commutatorModPCore_T hTAR hs
  · intro hd
    have h := conj_mem_commutatorModPCore_T hTAR (T.inv_mem hs) hd
    have e : s⁻¹ * (s * d * s⁻¹) * (s⁻¹)⁻¹ = d := by group
    rwa [e] at h

theorem mem_pCoreOf_sup_of_forall_commutator_mem {A T : Subgroup G} (hT : IsPGroup 2 T)
    (hRT : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ T)
    (hTAR : T ≤ Subgroup.normalizer ((A ⊔ CFSG.Open.pCoreOf 2 (A ⊔ T) : Subgroup G) : Set G))
    {t : G} (ht : t ∈ T)
    (htA : ∀ a ∈ A, t * a * t⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (A ⊔ T)) :
    t ∈ CFSG.Open.pCoreOf 2 (A ⊔ T) := by
  have hD2 : IsPGroup 2 (commutatorModPCore A T) := hT.to_le fun _ hx => hx.1
  have hDle : commutatorModPCore A T ≤ A ⊔ T := commutatorModPCore_le A T
  have hnorm : A ⊔ T ≤ Subgroup.normalizer (commutatorModPCore A T : Set G) :=
    sup_le (le_normalizer_commutatorModPCore_A hRT) (le_normalizer_commutatorModPCore_T hTAR)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDle hnorm hD2 ⟨ht, htA⟩

section

variable [Finite G]

private theorem commutator_mem_pPrimeCore_kSub
    {M A H : Subgroup G}
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H) (hK : KNormalAt M) (hL : PLayerNotLeAt M)
    (hAK : A ≤ kSub 3 M H) (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M)
    {T S : Subgroup G} (hNR : Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) ≤ H)
    (hS : IsPGroup 2 S) (hES : A ≤ Subgroup.normalizer (S : Set G)) :
    ∀ s ∈ S ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G),
      ∀ a ∈ A, s * a * s⁻¹ * a⁻¹ ∈
        (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let B : Subgroup G := A ⊔ O
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [K] using h.isSylowOf_three_E hC3 hAK
  have hNB : H ⊓ M ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B, O, K] using h.inf_le_normalizer_sup_pPrimeCore hC3 hK hL hAsyl hNA
  have hEO : A ≤ Subgroup.normalizer (O : Set G) := by
    refine (hAK.trans (Subgroup.le_normalizer (H := K))) |>.trans ?_
    simpa [O, K] using
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := K) (K := CFSG.pPrimeCore 3 ↥K))
  have hER : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  have hSM : S ≤ M := h.invariant_two_le_M hS hES
  have hS'B : S ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) ⊓ B ≤ O := by
    simpa [B] using CFSG.LocalAnalysis.RankThreeTheoremC.e9_inf_sup_le
      (O := O) (K := A)
      (Y := S ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G))
      hEO h.elem.2 (hS.to_le inf_le_left)
  intro s hs a ha
  have hcommS : s * a * s⁻¹ * a⁻¹ ∈ S := by
    have h1 : a * s⁻¹ * a⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hES ha) s⁻¹).mp (S.inv_mem hs.1)
    have h2 : s * (a * s⁻¹ * a⁻¹) ∈ S := S.mul_mem hs.1 h1
    simpa [mul_assoc] using h2
  have hcommNR : s * a * s⁻¹ * a⁻¹ ∈
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) := by
    have h1 : s * a * s⁻¹ ∈
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) := by
      have h := (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)).mul_mem
        ((Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)).mul_mem hs.2 (hER ha))
        ((Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)).inv_mem hs.2)
      simpa [mul_assoc] using h
    have h2 : s * a * s⁻¹ * a⁻¹ ∈
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
      (Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)).mul_mem h1
        ((Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G)).inv_mem (hER ha))
    exact h2
  have hcommB : s * a * s⁻¹ * a⁻¹ ∈ B := by
    have h1 : s * a * s⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hNB ⟨hNR hs.2, hSM hs.1⟩) a).mp
        (Subgroup.mem_sup_left ha)
    exact B.mul_mem h1 (B.inv_mem (Subgroup.mem_sup_left ha))
  have hcommS' : s * a * s⁻¹ * a⁻¹ ∈
      S ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) :=
    ⟨hcommS, hcommNR⟩
  exact hS'B ⟨hcommS', hcommB⟩

private theorem exists_conj_pCoreOf_eq
    {M A H : Subgroup G}
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M)
    (hK : KNormalAt M) (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M)) {T' : Subgroup G}
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' (H ⊓ M)) :
    ∃ y ∈ H ⊓ M, CFSG.Open.pCoreOf 2 (A ⊔ T') =
      (CFSG.Open.pCoreOf 2 (A ⊔ T)).map (MulAut.conj y).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subgroup G := kSub 3 M H
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let B : Subgroup G := A ⊔ O
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A K := by
    simpa [K] using h.isSylowOf_three_E hC3 hAK
  have hNB : H ⊓ M ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B, O, K] using h.inf_le_normalizer_sup_pPrimeCore hC3 hK hL hAsyl hNA
  have hOleT : O ≤ T := by
    simpa [O, K] using h.pPrimeCore_kSub_le_of_isSylowOf hC3 hTwo hK hT
  have hOleT' : O ≤ T' := by
    simpa [O, K] using h.pPrimeCore_kSub_le_of_isSylowOf hC3 hTwo hK hT'
  obtain ⟨y, hyHM, hyconj⟩ := hT.exists_mem_conj hT'
  have hT'eq : T' = T.map (MulAut.conj y).toMonoidHom := by
    ext x
    rw [hyconj x]
    constructor
    · intro hx
      refine ⟨y⁻¹ * x * y, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨t, ht, rfl⟩
      have h2 : y⁻¹ * (y * t * y⁻¹) * y = t := by group
      simpa [MulAut.conj_apply, h2] using ht
  have hAOT : A ⊔ T = B ⊔ T := by
    show A ⊔ T = (A ⊔ O) ⊔ T
    rw [sup_assoc, sup_eq_right.mpr hOleT]
  have hAOT' : A ⊔ T' = B ⊔ T' := by
    show A ⊔ T' = (A ⊔ O) ⊔ T'
    rw [sup_assoc, sup_eq_right.mpr hOleT']
  have hBmap : B.map (MulAut.conj y).toMonoidHom = B := by
    have hyNB : y ∈ Subgroup.normalizer (B : Set G) := hNB hyHM
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      have h := (Subgroup.mem_normalizer_iff.mp hyNB b).mp hb
      simpa [MulAut.conj_apply] using h
    · intro hx
      refine ⟨y⁻¹ * x * y, ?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (B : Set G)).inv_mem hyNB) x).mp hx
        simpa using h
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hsupConj : A ⊔ T' = (A ⊔ T).map (MulAut.conj y).toMonoidHom := by
    rw [hAOT', hT'eq, ← hBmap, ← Subgroup.map_sup, hAOT]
  exact ⟨y, hyHM, by rw [hsupConj, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]⟩

private theorem eq_inf_normalizer_pCoreOf
    {M A H : Subgroup G}
    (h : HypCGen G M 3 A H) (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M)
    (hK : KNormalAt M) (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M))
    (hNR : Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) ≤ H)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hES : A ≤ Subgroup.normalizer (S : Set G))
    (hRS : CFSG.Open.pCoreOf 2 (A ⊔ T) ≤ S) :
    S ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) =
      CFSG.Open.pCoreOf 2 (A ⊔ T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let S' : Subgroup G := S ⊓ Subgroup.normalizer (R : Set G)
  have hAH : A ≤ H := hAK.trans (kSub_le 3 M H)
  have hSM : S ≤ M := h.invariant_two_le_M hS hES
  have hS'2 : IsPGroup 2 S' := hS.to_le fun _ hx => hx.1
  have hS'M : S' ≤ M := fun _ hx => hSM hx.1
  have hS'H : S' ≤ H := fun _ hx => hNR hx.2
  have hRS' : R ≤ S' := fun x hx => ⟨hRS hx, Subgroup.le_normalizer hx⟩
  obtain ⟨T', hT'syl, hS'T'⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (p := 2) (K := H ⊓ M) (Q := S')
      (le_inf hS'H hS'M) hS'2
  have hS'le : S' ≤ CFSG.Open.pCoreOf 2 (A ⊔ T') := by
    intro s hs
    refine mem_pCoreOf_sup_of_forall_commutator_mem (A := A) (T := T') hT'syl.isPGroup
      (h.pCoreOf_sup_le_of_isSylowOf hAH hT'syl)
      (h.sylowTwo_le_normalizer_sup_pCoreOf hC3 hTwo hK hL hAK hNA hT'syl)
      (hS'T' hs) (fun a ha => ?_)
    exact (h.pPrimeCore_kSub_le_pCoreOf hC3 hTwo hK hAH hT'syl)
      (commutator_mem_pPrimeCore_kSub h hC3 hK hL hAK hNA hNR hS hES s hs a ha)
  obtain ⟨y, hyHM, hconj⟩ := exists_conj_pCoreOf_eq h hC3 hTwo hK hL hAK hNA hT hT'syl
  have hcardR : Nat.card (CFSG.Open.pCoreOf 2 (A ⊔ T')) = Nat.card R := by
    rw [hconj, Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hcardS' : Nat.card S' = Nat.card R := by
    refine le_antisymm ?_ (Subgroup.card_le_of_le hRS')
    calc Nat.card S' ≤ Nat.card (CFSG.Open.pCoreOf 2 (A ⊔ T')) :=
          Subgroup.card_le_of_le hS'le
      _ = Nat.card R := hcardR
  exact (Subgroup.eq_of_le_of_card_ge hRS' (le_of_eq hcardS')).symm

theorem HypCGen.isMaxInvariantTwo_pCoreOf
    {M A H : Subgroup G} (h : HypCGen G M 3 A H)
    (hC3 : CaseThree M H) (hTwo : KTwoComponentAt M) (hK : KNormalAt M)
    (hL : PLayerNotLeAt M) (hAK : A ≤ kSub 3 M H)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M))
    (hNR : Subgroup.normalizer (CFSG.Open.pCoreOf 2 (A ⊔ T) : Set G) ≤ H) :
    CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo A (CFSG.Open.pCoreOf 2 (A ⊔ T)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hER : A ≤ Subgroup.normalizer (R : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (A ⊔ T))
  refine ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (A ⊔ T), hER, ?_⟩
  intro S hS hES hRS
  have hS'eq : S ⊓ Subgroup.normalizer (R : Set G) = R := by
    simpa [R] using eq_inf_normalizer_pCoreOf h hC3 hTwo hK hL hAK hNA hT hNR hS hES hRS
  let S' : Subgroup G := S ⊓ Subgroup.normalizer (R : Set G)
  have hS'eq' : S' = R := by simpa [S'] using hS'eq
  by_contra hSR
  have hlt : (R.subgroupOf S) ≠ ⊤ := by
    intro htop
    exact hSR (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hRS)
  haveI : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨x, hxN, hxR⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf S) (lt_top_iff_ne_top.mpr hlt))
  have hmapR : (R.subgroupOf S).map S.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRS]
  have hxN' : (x : G) ∈ Subgroup.normalizer (R : Set G) := by
    have := Subgroup.le_normalizer_map S.subtype ⟨x, hxN, rfl⟩
    rwa [hmapR] at this
  have hxS' : (x : G) ∈ S' := ⟨x.2, hxN'⟩
  rw [hS'eq'] at hxS'
  exact hxR (Subgroup.mem_subgroupOf.mpr hxS')

end

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
