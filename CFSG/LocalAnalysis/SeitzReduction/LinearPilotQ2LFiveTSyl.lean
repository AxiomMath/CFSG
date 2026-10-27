module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGrFusion

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift)

section TypeFree

variable {G : Type} [Group G]

theorem exists_mem_normalizer_notMem_of_lt_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ Subgroup.normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem not_two_dvd_index_of_normalizer_mem [Finite G] {S S₁ W : Subgroup G}
    (hS : IsPGroup 2 S) (hS₁S : S₁ ≤ S) (hS₁W : S₁ ≤ normalizer (W : Set G))
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S₁ ≤ P → P ≤ normalizer (W : Set G) → P = S₁)
    {d : G} (hdS : d ∈ S)
    (hW : ∀ s ∈ normalizer (S : Set G), IsPGroup 2 (zpowers s) →
      s ∈ normalizer (W : Set G) ∨ d⁻¹ * s ∈ normalizer (W : Set G)) :
    ¬ 2 ∣ S.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  have hne : S ≠ (T : Subgroup G) := fun h => T.not_dvd_index (h ▸ h2)
  obtain ⟨s, hsT, hsS, hsN⟩ :=
    exists_mem_normalizer_notMem_of_lt_isPGroup T.isPGroup' (lt_of_le_of_ne hST hne)
  have hsp : IsPGroup 2 (zpowers s) := T.isPGroup'.to_le (zpowers_le.2 hsT)
  obtain ⟨x, hxT, hxS, hxN⟩ : ∃ x ∈ (T : Subgroup G), x ∉ S ∧ x ∈ normalizer (W : Set G) := by
    rcases hW s hsN hsp with h | h
    · exact ⟨s, hsT, hsS, h⟩
    · refine ⟨d⁻¹ * s, mul_mem (inv_mem (hST hdS)) hsT, fun h' => hsS ?_, h⟩
      have h3 : s = d * (d⁻¹ * s) := by group
      rw [h3]
      exact mul_mem hdS h'
  have hP : IsPGroup 2 (S₁ ⊔ zpowers x : Subgroup G) :=
    T.isPGroup'.to_le (sup_le (hS₁S.trans hST) (zpowers_le.2 hxT))
  have hPN : S₁ ⊔ zpowers x ≤ normalizer (W : Set G) := sup_le hS₁W (zpowers_le.2 hxN)
  have hPeq := hmax _ hP le_sup_left hPN
  have hxS₁ : x ∈ S₁ := by
    rw [← hPeq]
    exact mem_sup_right (mem_zpowers x)
  exact hxS (hS₁S hxS₁)

end TypeFree

section NOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem blockSL_le_seitzTilde {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* projectiveSL 5 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (c : Fin 5)
    {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc) :
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ seitzTilde W₁ Kc := by
  set N := normalizer (W₁ : Set G) with hNdef
  set ν := QuotientGroup.mk' (W₁.subgroupOf N) with hν
  set L₁ := modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) with hL₁
  set Lb := (L₁.subgroupOf N).map ν with hLbdef
  obtain ⟨hLq, -, -, -, -⟩ := leviBar_facts e hK htC hW₁c hLN htN
  obtain ⟨-, hLKc, -⟩ := hfield
  have hLp : ⁅Lb, Lb⁆ = Lb := isPerfect_iff.mp ⟨hLq.1⟩
  have hLK : Lb ≤ oddCoreLift Kc := by
    refine F4Pilot.le_oddCoreLift_of_perfect hLp ?_
    have h1 := hLKc.le
    rw [seitzLeviHat_eq_map_map] at h1
    exact h1
  intro l hl
  refine mem_seitzTilde_iff.2 ⟨hLN hl, hLK ?_⟩
  exact mem_map_of_mem _ (mem_subgroupOf.2 hl)

theorem eq_of_le_normalizer_wOne
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ : Subgroup G} (hS₀N : S₀ ≤ seitzTilde W₁ Kc)
    (hS₀syl : ¬ 2 ∣ S₀.relIndex (seitzTilde W₁ Kc)) (htS₀ : t ∈ normalizer (S₀ : Set G))
    {P : Subgroup G} (hP : IsPGroup 2 P) (hSP : S₀ ⊔ zpowers t ≤ P)
    (hPN : P ≤ normalizer (W₁ : Set G)) : P = S₀ ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW₁Nt, htNt, htNNt, hfus⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  set Nt := seitzTilde W₁ Kc with hNtdef
  set M := Nt ⊔ zpowers t with hMdef
  set S₁ := S₀ ⊔ zpowers t with hS₁def
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htS₀' : t ∉ S₀ := fun h => htNt (hS₀N h)
  have hMN : M ≤ normalizer (W₁ : Set G) :=
    sup_le (seitzTilde_le_normalizer W₁ Kc) ((zpowers_le).2 htN)
  have hS₁M : S₁ ≤ M := sup_le_sup_right hS₀N _
  have hMc : Nat.card M = 2 * Nat.card Nt := card_sup_zpowers_eq_two_mul htNt htNNt ht2
  have hS₁c : Nat.card S₁ = 2 * Nat.card S₀ := card_sup_zpowers_eq_two_mul htS₀' htS₀ ht2
  have hNtc : Nat.card Nt = S₀.relIndex Nt * Nat.card S₀ := by
    have h := Subgroup.relIndex_mul_card (H := S₀) (K := Nt)
    rw [inf_of_le_left hS₀N] at h
    exact h.symm
  have hsylM : ∀ Q : Subgroup G, IsPGroup 2 Q → S₁ ≤ Q → Q ≤ M → Q = S₁ := by
    intro Q hQ hSQ hQM
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ
    have hdvd : Nat.card Q ∣ Nat.card M := Subgroup.card_dvd_of_le hQM
    rw [hMc, hNtc, hk] at hdvd
    have hr : Nat.Coprime (2 ^ k) (S₀.relIndex Nt) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hS₀syl)
    have h2 : 2 ^ k ∣ 2 * Nat.card S₀ := by
      have h3 : 2 * (S₀.relIndex Nt * Nat.card S₀) = S₀.relIndex Nt * (2 * Nat.card S₀) := by
        ring
      rw [h3] at hdvd
      exact hr.dvd_of_dvd_mul_left hdvd
    have hle : Nat.card Q ≤ Nat.card S₁ := by
      rw [hk, hS₁c]
      exact Nat.le_of_dvd (Nat.mul_pos (by norm_num) Nat.card_pos) h2
    exact (Subgroup.eq_of_le_of_card_ge hSQ hle).symm
  by_contra hne
  obtain ⟨x, hxP, hxS, hxN⟩ :=
    exists_mem_normalizer_notMem_of_lt_isPGroup hP (lt_of_le_of_ne hSP (Ne.symm hne))
  have htS₁ : t ∈ S₁ := mem_sup_right (mem_zpowers t)
  have hxt : x * t * x⁻¹ ∈ M := hS₁M ((mem_normalizer_iff.1 hxN t).1 htS₁)
  obtain ⟨m, hmM, hm⟩ := hfus x hxt
  set y := m⁻¹ * x with hydef
  have hyC : y ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc y * t = m⁻¹ * (x * t * x⁻¹) * x := by rw [hydef]; group
      _ = m⁻¹ * (m * t * m⁻¹) * x := by rw [hm]
      _ = t * y := by rw [hydef]; group
  have hyN : y ∈ normalizer (W₁ : Set G) := mul_mem (inv_mem (hMN hmM)) (hPN hxP)
  have hyV : y ∈ normalizer (modelToG e (pointRadical (K := K) c) : Set G) := by
    rw [← hW₁t, mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      obtain ⟨hvW, hvC⟩ := mem_inf.1 hv
      exact mem_inf.2 ⟨(mem_normalizer_iff.1 hyN v).1 hvW, mul_mem (mul_mem hyC hvC) (inv_mem hyC)⟩
    · intro hv
      obtain ⟨hvW, hvC⟩ := mem_inf.1 hv
      refine mem_inf.2 ⟨(mem_normalizer_iff.1 hyN v).2 hvW, ?_⟩
      have h1 : v = y⁻¹ * (y * v * y⁻¹) * y := by group
      rw [h1]
      exact mul_mem (mul_mem (inv_mem hyC) hvC) hyC
  have h1 := lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c (mem_inf.2 ⟨hyV, hyC⟩)
  have hV₁M : modelToG e (pointRadical (K := K) c) ≤ M := by
    rw [← hW₁t]
    exact inf_le_left.trans (hW₁Nt.trans le_sup_left)
  have hL₁M : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ M :=
    (blockSL_le_seitzTilde hK e htC c hW₁c htN hLN hfield).trans le_sup_left
  have hyM : y ∈ M := sup_le (sup_le hV₁M hL₁M) le_sup_right h1
  have hxM : x ∈ M := by
    have h2 : x = m * y := by rw [hydef]; group
    rw [h2]
    exact mul_mem hmM hyM
  have hQ : IsPGroup 2 (S₁ ⊔ zpowers x : Subgroup G) :=
    hP.to_le (sup_le hSP (zpowers_le.2 hxP))
  have hQeq := hsylM _ hQ le_sup_left (sup_le hS₁M (zpowers_le.2 hxM))
  exact hxS (hQeq ▸ mem_sup_right (mem_zpowers x))

end NOne

end CFSG.SeitzReduction.LinearPilot
