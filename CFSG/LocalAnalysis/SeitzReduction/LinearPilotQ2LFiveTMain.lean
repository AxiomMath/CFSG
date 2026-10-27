module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveTSyl
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGrMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def IsLFiveGraphSylowData {G : Type} [Group G] (L : Subgroup G) (t : G)
    (Nt S₀ : Subgroup G) (d : G) : Prop :=
  IsPGroup 2 S₀ ∧ S₀ ≤ Nt ∧ ¬ 2 ∣ S₀.relIndex Nt ∧ t ∈ normalizer (S₀ : Set G) ∧
    d ∈ normalizer (S₀ : Set G) ∧ d * t = t * d ∧ d * d ∈ S₀ ∧
    ∀ l ∈ L, ∃ x ∈ L, d * x * d⁻¹ ≠ l * x * l⁻¹

@[expose] def LFiveGraphSylowDataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
      ∃ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d ∧
        ∀ s ∈ normalizer ((S₀ ⊔ zpowers d ⊔ zpowers t : Subgroup G) : Set G),
          IsPGroup 2 (zpowers s) →
            s ∈ normalizer (W₁ : Set G) ∨ d⁻¹ * s ∈ normalizer (W₁ : Set G)

@[expose] def LFiveGraphCosetInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧ ∀ g : G, ∀ s ∈ S₀, g⁻¹ * t * g ≠ s * d₁

section Helpers

variable {G : Type} [Group G]

theorem mem_normalizer_sup_of_mem_of_mem_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_zpowers_of_mul_eq_mul {d t : G} (h : d * t = t * d) :
    t ∈ normalizer ((zpowers d : Subgroup G) : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  exact ((Commute.zpow_left (show Commute d t from h) k)).eq

theorem mem_normalizer_inf_centralizer_singleton_of_mem {W : Subgroup G} {t y : G}
    (hyN : y ∈ normalizer (W : Set G)) (hyC : y ∈ centralizer ({t} : Set G)) :
    y ∈ normalizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
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

theorem sup_zpowers_mul_sup_zpowers_eq {S : Subgroup G} {d t : G} (ht2 : t * t = 1) :
    S ⊔ zpowers (d * t) ⊔ zpowers t = S ⊔ zpowers d ⊔ zpowers t := by
  have htR : t ∈ S ⊔ zpowers d ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hdR : d ∈ S ⊔ zpowers d ⊔ zpowers t := mem_sup_left (mem_sup_right (mem_zpowers d))
  have htL : t ∈ S ⊔ zpowers (d * t) ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hdtL : d * t ∈ S ⊔ zpowers (d * t) ⊔ zpowers t :=
    mem_sup_left (mem_sup_right (mem_zpowers (d * t)))
  refine le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left)
    (zpowers_le.2 (mul_mem hdR htR))) le_sup_right) (sup_le (sup_le
    (le_sup_left.trans le_sup_left) (zpowers_le.2 ?_)) le_sup_right)
  have h1 := mul_mem hdtL htL
  rwa [mul_assoc, ht2, mul_one] at h1

theorem inv_mul_mul_mem_of_mem_normalizer {S : Subgroup G} {u : G}
    (huN : u ∈ normalizer (S : Set G)) {s : G} (hs : s ∈ S) : u⁻¹ * s * u ∈ S := by
  have h := (mem_normalizer_iff.1 (inv_mem huN) s).1 hs
  rwa [inv_inv] at h

theorem mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem {S : Subgroup G} {u : G}
    (huN : u ∈ normalizer (S : Set G)) (huu : u * u ∈ S) {h : G}
    (hh : h ∈ S ⊔ zpowers u) : h ∈ S ∨ h * u ∈ S := by
  have hc := fun s (hs : s ∈ S) => inv_mul_mul_mem_of_mem_normalizer huN hs
  let K : Subgroup G :=
    { carrier := {h | h ∈ S ∨ h * u ∈ S}
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (mul_mem ha hb)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact mul_mem ha hb
        · refine Or.inr ?_
          have h1 : a * b * u = (a * u) * (u⁻¹ * b * u) := by group
          rw [h1]
          exact mul_mem ha (hc b hb)
        · refine Or.inl ?_
          have h1 : a * b = (a * u) * (u⁻¹ * (b * u) * u) * (u * u)⁻¹ := by group
          rw [h1]
          exact mul_mem (mul_mem ha (hc _ hb)) (inv_mem huu)
      one_mem' := Or.inl S.one_mem
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ?_
          have h1 : a⁻¹ * u = (u * u) * (u⁻¹ * (a * u)⁻¹ * u) := by group
          rw [h1]
          exact mul_mem huu (hc _ (inv_mem ha)) }
  have hle : S ⊔ zpowers u ≤ K := sup_le (fun s hs => Or.inl hs) (zpowers_le.2 (Or.inr huu))
  exact hle hh

theorem isPGroup_sup_zpowers_of_mul_self_mem {S : Subgroup G} (hS : IsPGroup 2 S) {u : G}
    (huN : u ∈ normalizer (S : Set G)) (huu : u * u ∈ S) :
    IsPGroup 2 (S ⊔ zpowers u : Subgroup G) := by
  rintro ⟨h, hh⟩
  have hsq : h * h ∈ S := by
    rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem huN huu hh with h1 | h1
    · exact mul_mem h1 h1
    · have h2 : h * h = (h * u) * (u⁻¹ * (h * u) * u) * (u * u)⁻¹ := by group
      rw [h2]
      exact mul_mem (mul_mem h1 (inv_mul_mul_mem_of_mem_normalizer huN h1)) (inv_mem huu)
  obtain ⟨k, hk⟩ := hS ⟨h * h, hsq⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have h2 := congrArg Subtype.val hk
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2 ⊢
  rw [pow_succ', pow_mul, sq]
  exact h2

end Helpers

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_mem_normalizer_wOne_of_outer (hset : SeitzSetting G L) {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (c : Fin 5)
    {W₁ : Subgroup G} (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    {d : G} (hdC : d ∈ centralizer ({t} : Set G))
    (hdo : ∀ l ∈ L, ∃ x ∈ L, d * x * d⁻¹ ≠ l * x * l⁻¹) :
    d ∉ normalizer (W₁ : Set G) := by
  intro hdN
  have hdV : d ∈ normalizer (modelToG e (pointRadical (K := K) c) : Set G) := by
    rw [← hW₁t]
    exact mem_normalizer_inf_centralizer_singleton_of_mem hdN hdC
  have h1 := lFiveNormalizerPointRadicalInput G L hset K hK e t ht hKt c (mem_inf.2 ⟨hdV, hdC⟩)
  have h2 : d ∈ L ⊔ zpowers t := (sup_le (sup_le ((modelToG_le e _).trans le_sup_left)
    ((modelToG_le e _).trans le_sup_left)) le_sup_right) h1
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 htC) l hl)
  have htNL : t ∈ normalizer (L : Set G) := cKind_mem_normalizer hLt
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers ht2 htNL h2 with h3 | h3
  · obtain ⟨x, -, hx⟩ := hdo d h3
    exact hx rfl
  · obtain ⟨x, hxL, hx⟩ := hdo (d * t) h3
    apply hx
    have hxt : x * t = t * x := (mem_centralizer_iff.1 htC) x hxL
    calc d * x * d⁻¹ = d * (x * t) * t⁻¹ * d⁻¹ := by group
      _ = d * (t * x) * t⁻¹ * d⁻¹ := by rw [hxt]
      _ = d * t * x * (d * t)⁻¹ := by group

theorem exists_transfer_of_graphSylowData
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ : Subgroup G} {d : G} (hdata : IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d)
    (hWinv : ∀ s ∈ normalizer ((S₀ ⊔ zpowers d ⊔ zpowers t : Subgroup G) : Set G),
      IsPGroup 2 (zpowers s) → s ∈ normalizer (W₁ : Set G) ∨ d⁻¹ * s ∈ normalizer (W₁ : Set G))
    {d₁ : G} (hd₁ : d₁ = d ∨ d₁ = d * t) (hcos : ∀ g : G, ∀ s ∈ S₀, g⁻¹ * t * g ≠ s * d₁) :
    ¬ 2 ∣ (S₀ ⊔ zpowers d₁ ⊔ zpowers t).index ∧
      (S₀ ⊔ zpowers d₁).relIndex (S₀ ⊔ zpowers d₁ ⊔ zpowers t) = 2 ∧
      t ∈ S₀ ⊔ zpowers d₁ ⊔ zpowers t ∧ t ∉ S₀ ⊔ zpowers d₁ ∧
      ∀ g : G, g⁻¹ * t * g ∈ S₀ ⊔ zpowers d₁ → g⁻¹ * t * g ∈ seitzTilde W₁ Kc := by
  obtain ⟨hS₀p, hS₀N, hS₀syl, htS₀, hdS₀, hdt, hd2, hdo⟩ := hdata
  obtain ⟨-, htNt, -, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hdC : d ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hdt
  have hdW : d ∉ normalizer (W₁ : Set G) :=
    not_mem_normalizer_wOne_of_outer hset hK e ht hKt c hW₁t hdC hdo
  have hNtW := seitzTilde_le_normalizer W₁ Kc
  have hd₁t : d₁ * t = t * d₁ := by
    rcases hd₁ with rfl | rfl
    · exact hdt
    · calc d * t * t = t * d * t := by rw [hdt]
        _ = t * (d * t) := by group
  have hd₁2 : d₁ * d₁ ∈ S₀ := by
    rcases hd₁ with rfl | rfl
    · exact hd2
    · have h1 : d * t * (d * t) = d * d := by
        calc d * t * (d * t) = d * (t * d) * t := by group
          _ = d * (d * t) * t := by rw [← hdt]
          _ = (d * d) * (t * t) := by group
          _ = d * d := by rw [ht2, mul_one]
      rw [h1]
      exact hd2
  have hd₁N : d₁ ∈ normalizer (S₀ : Set G) := by
    rcases hd₁ with rfl | rfl
    · exact hdS₀
    · exact mul_mem hdS₀ htS₀
  have hd₁W : d₁ ∉ normalizer (W₁ : Set G) := by
    rcases hd₁ with rfl | rfl
    · exact hdW
    · intro h
      apply hdW
      have h3 := mul_mem h htN
      rwa [mul_assoc, ht2, mul_one] at h3
  have htY : t ∉ S₀ ⊔ zpowers d₁ := by
    intro h
    rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem hd₁N hd₁2 h with h1 | h1
    · exact htNt (hS₀N h1)
    · apply hd₁W
      have h2 := mul_mem (inv_mem htN) (hNtW (hS₀N h1))
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
  have htNY : t ∈ normalizer ((S₀ ⊔ zpowers d₁ : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer htS₀
      (mem_normalizer_zpowers_of_mul_eq_mul hd₁t)
  have hrel := relIndex_sup_zpowers_eq_two_of_not_mem htY htNY ht2
  have hYp : IsPGroup 2 (S₀ ⊔ zpowers d₁ : Subgroup G) :=
    isPGroup_sup_zpowers_of_mul_self_mem hS₀p hd₁N hd₁2
  have hHp : IsPGroup 2 (S₀ ⊔ zpowers d₁ ⊔ zpowers t : Subgroup G) :=
    isPGroup_sup_zpowers hYp htY htNY ht2
  have hHeq : S₀ ⊔ zpowers d₁ ⊔ zpowers t = S₀ ⊔ zpowers d ⊔ zpowers t := by
    rcases hd₁ with h | h
    · rw [h]
    · rw [h]
      exact sup_zpowers_mul_sup_zpowers_eq ht2
  have hdH : d ∈ S₀ ⊔ zpowers d₁ ⊔ zpowers t := by
    rw [hHeq]
    exact mem_sup_left (mem_sup_right (mem_zpowers d))
  have hodd : ¬ 2 ∣ (S₀ ⊔ zpowers d₁ ⊔ zpowers t).index := by
    refine not_two_dvd_index_of_normalizer_mem hHp (S₁ := S₀ ⊔ zpowers t) (W := W₁) ?_ ?_ ?_
      hdH ?_
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · exact sup_le (hS₀N.trans hNtW) (zpowers_le.2 htN)
    · intro P hP hSP hPN
      exact eq_of_le_normalizer_wOne hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield hS₀N
        hS₀syl htS₀ hP hSP hPN
    · rw [hHeq]
      exact hWinv
  refine ⟨hodd, hrel, mem_sup_right (mem_zpowers t), htY, fun g hg => ?_⟩
  rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem hd₁N hd₁2 hg with h1 | h1
  · exact hS₀N h1
  · exfalso
    refine hcos g _ (mul_mem h1 (inv_mem hd₁2)) ?_
    group

end Setting

theorem lFiveGraphTransferInput_of_sylowData_of_coset
    (hS : LFiveGraphSylowDataInput)
    (hC : LFiveGraphCosetInput) : LFiveGraphTransferInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc
  obtain ⟨S₀, d, hdata, hWinv⟩ :=
    hS G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc
  obtain ⟨d₁, hd₁, hcos⟩ :=
    hC G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨hodd, hrel, htH, htY, hfus⟩ := exists_transfer_of_graphSylowData hset hK e ht hKt c
    hW₁c hW₁2 hW₁t htN hLN hKc hdata hWinv hd₁ hcos
  exact ⟨_, _, hodd, hrel, htH, htY, hfus⟩

end CFSG.SeitzReduction.LinearPilot
