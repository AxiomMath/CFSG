module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductN2Char
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
  (centerMod centralizerMod IsQuotientIso zc mem_centerMod_iff mem_centralizerMod_iff)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (Sl2Pair sylow_prod mem_conj_iff conj_eq_of_mem_normalizer conj_conj_of_mul_self conj_inf
    conj_sup mem_normalizer_of_pow_mem conj_mono mem_normalizer_of_conj_eq card_conj)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux
  (le_normalizer_D D_le_left D_le_right left_le right_le mem_D_of_comm mem_right_of_comm
    eq_or_eq_left exists_mul_of_mem_sup mem_normalizer_sup)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1Aux
  (mem_normalizer_map_upperCentralSeries)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductN1Aux

section Generic

variable {G : Type} [Group G]

def commSub (U : Subgroup G) (z : G) : Subgroup G where
  carrier := {c | c ∈ normalizer (U : Set G) ∧ z * c * z⁻¹ * c⁻¹ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : z * (a * b) * z⁻¹ * (a * b)⁻¹ =
        (z * a * z⁻¹ * a⁻¹) * (a * (z * b * z⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact mul_mem ha' ((mem_normalizer_iff.1 ha _).1 hb')
  one_mem' := ⟨one_mem _, by simpa using one_mem U⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : z * a⁻¹ * z⁻¹ * a⁻¹⁻¹ = a⁻¹ * (z * a * z⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem ha) _).1 (inv_mem ha')

theorem mem_centerMod_iff_of_le {U A : Subgroup G} (hUA : U ≤ A)
    (hAN : A ≤ normalizer (U : Set G)) {z : G} :
    z ∈ centerMod U A ↔ z ∈ A ∧ ∀ a ∈ A, z * a * z⁻¹ * a⁻¹ ∈ U := by
  rw [mem_centerMod_iff hUA]
  constructor
  · rintro ⟨hz, -, hc⟩
    exact ⟨hz, fun a ha => hc a ha (hAN ha)⟩
  · rintro ⟨hz, hc⟩
    exact ⟨hz, hAN hz, fun a ha _ => hc a ha⟩


theorem centerMod_conj {U A : Subgroup G} {g : G} (hg : g ∈ normalizer (U : Set G))
    (hUA : U ≤ A) : centerMod U (Aᵍ[g]) = (centerMod U A)ᵍ[g] := by
  have hUg : U ≤ Aᵍ[g] := by
    intro u hu
    rw [mem_conj_iff]
    exact hUA ((mem_normalizer_iff.1 hg u).1 hu)
  ext x
  have hx1 := mem_centerMod_iff hUg (g := x)
  have hx2 : x ∈ (centerMod U A)ᵍ[g] ↔ g * x * g⁻¹ ∈ centerMod U A := mem_conj_iff
  have hx3 := mem_centerMod_iff hUA
    (g := g * x * g⁻¹)
  rw [hx1, hx2, hx3]
  have hN : ∀ y, y ∈ normalizer (U : Set G) ↔ g * y * g⁻¹ ∈ normalizer (U : Set G) := by
    intro y
    constructor
    · intro hy
      exact mul_mem (mul_mem hg hy) (inv_mem hg)
    · intro hy
      have := mul_mem (mul_mem (inv_mem hg) hy) hg
      simpa [mul_assoc] using this
  have hA : x ∈ Aᵍ[g] ↔ g * x * g⁻¹ ∈ A := mem_conj_iff
  refine and_congr hA (and_congr (hN x) ?_)
  constructor
  · intro H a ha han
    have := H (g⁻¹ * a * g) (by rw [mem_conj_iff]; simpa [mul_assoc] using ha)
      ((hN _).2 (by simpa [mul_assoc] using han))
    have e : g * (x * (g⁻¹ * a * g) * x⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * a * (g * x * g⁻¹)⁻¹ * a⁻¹ := by group
    have h2 := (mem_normalizer_iff.1 hg _).1 this
    rwa [e] at h2
  · intro H a ha han
    rw [mem_conj_iff] at ha
    have := H (g * a * g⁻¹) ha ((hN a).1 han)
    have e : g * (x * a * x⁻¹ * a⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ := by group
    apply (mem_normalizer_iff.1 hg _).2
    rwa [e]

theorem mem_normalizer_centerMod {U A : Subgroup G} {g : G} (hg : g ∈ normalizer (U : Set G))
    (hgA : g ∈ normalizer (A : Set G)) (hUA : U ≤ A) :
    g ∈ normalizer ((centerMod U A : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_eq
  rw [← centerMod_conj hg hUA, conj_eq_of_mem_normalizer hgA]


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isFactor_sl2Pair {X N Λ : Subgroup G} {t : G} (hΛ : IsFactor X N Λ t K)
    (ht : t * t = 1) (h4 : 4 ≤ Nat.card K) : Sl2Pair K N X Λ (Λᵍ[t]) := by
  have hXt : Xᵍ[t] = X := by
    have h1 : (Λ ⊓ Λᵍ[t])ᵍ[t] = Λᵍ[t] ⊓ Λ := by
      rw [conj_inf, conj_conj_of_mul_self ht]
    rw [hΛ.inf] at h1
    rw [h1, inf_comm, hΛ.inf]
  refine ⟨inferInstance, h4, hΛ.sup, hΛ.inf, hΛ.comm, hΛ.quot, ?_⟩
  have := CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.IsQuotientIso.conj
    hΛ.quot t
  rwa [hXt] at this


section SL2

variable [Finite G]

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux in
theorem sl2Pair_sup_inf {N D K₁ K₂ : Subgroup G} (hS : Sl2Pair K N D K₁ K₂) {A A' : Subgroup G}
    (hDA : D ≤ A) (hDA' : D ≤ A') (hAK : A ≤ K₁) (hA'K : A' ≤ K₁)
    (hcard : Nat.card A = Nat.card D * Nat.card K)
    (hcard' : Nat.card A' = Nat.card D * Nat.card K) (hne : A ≠ A') :
    A ⊔ A' = K₁ ∧ A ⊓ A' = D := by
  haveI := hS.charTwo
  obtain ⟨φ, hφ, hker⟩ := hS.isoK
  obtain ⟨m, hm⟩ := SL2Aux.card_eq_two_pow (F := K)
  have hm1 : 1 ≤ m := by
    have h4 := hS.four_le
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; omega
    · exact h0
  have hDK : D ≤ K₁ := SL2Aux.D_le_left hS
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hcardMap : ∀ {B : Subgroup G}, D ≤ B → B ≤ K₁ →
      Nat.card ((B.subgroupOf K₁).map φ) * Nat.card D = Nat.card B := by
    intro B hDB hBK
    have h1 := CFSG.LocalAnalysis.EvenBN.Common.card_map_mul_card_inf_ker φ (B.subgroupOf K₁)
    have hle : D.subgroupOf K₁ ≤ B.subgroupOf K₁ := fun x hx =>
      mem_subgroupOf.2 (hDB (mem_subgroupOf.1 hx))
    rw [hker, inf_eq_right.mpr hle, Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv] at h1
    exact h1
  have hcomap : ∀ {B : Subgroup G}, D ≤ B →
      ((B.subgroupOf K₁).map φ).comap φ = B.subgroupOf K₁ := by
    intro B hDB
    apply Subgroup.comap_map_eq_self
    rw [hker]
    exact fun x hx => mem_subgroupOf.2 (hDB (mem_subgroupOf.1 hx))
  have hcardĀ : Nat.card ((A.subgroupOf K₁).map φ) = Nat.card K := by
    have := hcardMap hDA hAK
    rw [hcard] at this
    exact Nat.eq_of_mul_eq_mul_right hDpos (by rw [this]; ring)
  have hcardĀ' : Nat.card ((A'.subgroupOf K₁).map φ) = Nat.card K := by
    have := hcardMap hDA' hA'K
    rw [hcard'] at this
    exact Nat.eq_of_mul_eq_mul_right hDpos (by rw [this]; ring)
  have hne' : (A.subgroupOf K₁).map φ ≠ (A'.subgroupOf K₁).map φ := by
    intro h
    apply hne
    have h1 := hcomap hDA
    have h2 := hcomap hDA'
    rw [h] at h1
    have h3 : A.subgroupOf K₁ = A'.subgroupOf K₁ := h1.symm.trans h2
    ext x
    constructor
    · intro hx
      have := (Subgroup.ext_iff.1 h3 ⟨x, hAK hx⟩).1 (mem_subgroupOf.2 hx)
      exact mem_subgroupOf.1 this
    · intro hx
      have := (Subgroup.ext_iff.1 h3 ⟨x, hA'K hx⟩).2 (mem_subgroupOf.2 hx)
      exact mem_subgroupOf.1 this
  have hKpow : Nat.card K = 2 ^ m := hm
  have hSylĀ := CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1Aux.isSylowOf_top_sl2
    hKpow hm1 hcardĀ
  have hSylĀ' := CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1Aux.isSylowOf_top_sl2
    hKpow hm1 hcardĀ'
  have hsup := CFSG.LocalAnalysis.EvenBN.U5.Prelim.sup_eq_of_isSylowOf_ne hKpow hm1
    (Subgroup.topEquiv : (⊤ : Subgroup SL(2, K)) ≃* SL(2, K)) hSylĀ hSylĀ' hne'
  constructor
  · refine le_antisymm (sup_le hAK hA'K) (fun x hx => ?_)
    have hφx : φ ⟨x, hx⟩ ∈ (⊤ : Subgroup SL(2, K)) := Subgroup.mem_top _
    rw [← hsup, ← Subgroup.map_sup] at hφx
    obtain ⟨y, hy, hyx⟩ := hφx
    have hy' : y ∈ (A ⊔ A').subgroupOf K₁ := by
      have : A.subgroupOf K₁ ⊔ A'.subgroupOf K₁ ≤ (A ⊔ A').subgroupOf K₁ :=
        sup_le (fun z hz => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hz)))
          (fun z hz => mem_subgroupOf.2 (mem_sup_right (mem_subgroupOf.1 hz)))
      exact this hy
    have hker' : y⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at hker'
    have hDM : D ≤ A ⊔ A' := hDA.trans le_sup_left
    have : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_subgroupOf.1 hy') (hDM hker')
  · refine le_antisymm (fun x hx => ?_) (le_inf hDA hDA')
    obtain ⟨hxA, hxA'⟩ := mem_inf.1 hx
    by_contra hxD
    have hxK : x ∈ K₁ := hAK hxA
    have hφ1 : φ ⟨x, hxK⟩ ≠ 1 := by
      intro h1
      apply hxD
      have : (⟨x, hxK⟩ : ↥K₁) ∈ φ.ker := h1
      rw [hker, mem_subgroupOf] at this
      exact this
    exact hne' (CFSG.LocalAnalysis.EvenBN.Common.eq_of_mem_of_card
      (Subgroup.topEquiv : (⊤ : Subgroup SL(2, K)) ≃* SL(2, K))
      le_top le_top hcardĀ hcardĀ' (s := φ ⟨x, hxK⟩)
      ⟨⟨x, hxK⟩, mem_subgroupOf.2 hxA, rfl⟩ ⟨⟨x, hxK⟩, mem_subgroupOf.2 hxA', rfl⟩ hφ1)

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux in
theorem sl2Pair_eq_or_eq {N D K₁ K₂ : Subgroup G} (hS : Sl2Pair K N D K₁ K₂) {t : G}
    (ht : t * t = 1) (hKt : K₁ᵍ[t] = K₂) {X : Subgroup G} (hDX : D ≤ X) (hXN : X ≤ N)
    (hNX : N ≤ normalizer (X : Set G)) (hXt : Xᵍ[t] = X) : X = D ∨ X = N := by
  have hK₂t : K₂ᵍ[t] = K₁ := by rw [← hKt, conj_conj_of_mul_self ht]
  have hK₁N : K₁ ≤ N := SL2Aux.left_le hS
  have hK₂N : K₂ ≤ N := SL2Aux.right_le hS
  have h1 : X ⊓ K₁ = D ∨ X ⊓ K₁ = K₁ :=
    SL2Aux.eq_or_eq_left hS (le_inf hDX (SL2Aux.D_le_left hS)) inf_le_right
      fun k hk => SL2Aux.le_normalizer_inf X K₁ ⟨hNX (hK₁N hk), le_normalizer hk⟩
  have h2 : X ⊓ K₂ = D ∨ X ⊓ K₂ = K₂ :=
    SL2Aux.eq_or_eq_left hS.symm (le_inf hDX (SL2Aux.D_le_right hS)) inf_le_right
      fun k hk => SL2Aux.le_normalizer_inf X K₂ ⟨hNX (hK₂N hk), le_normalizer hk⟩
  have hNle : K₁ ≤ X → X = N := by
    intro hK
    have hK' : K₂ ≤ X := by
      have := conj_mono hK t
      rwa [hKt, hXt] at this
    exact le_antisymm hXN (hS.sup_eq ▸ sup_le hK hK')
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · left
      refine le_antisymm (fun x hx => ?_) hDX
      have hxN : x ∈ N := hXN hx
      have hxK₂ : x ∈ K₂ := by
        refine SL2Aux.mem_right_of_comm hS hxN fun y hy => ?_
        have hxX : x * y * x⁻¹ * y⁻¹ ∈ X := by
          have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [e]
          exact mul_mem hx ((mem_normalizer_iff.1 (hNX (hK₁N hy)) _).1 (inv_mem hx))
        have hxK : x * y * x⁻¹ * y⁻¹ ∈ K₁ :=
          mul_mem ((mem_normalizer_iff.1 (hS.le_normalizer hxN) y).1 hy) (inv_mem hy)
        rw [← h1]
        exact ⟨hxX, hxK⟩
      rw [← h2]
      exact ⟨hx, hxK₂⟩
    · right
      have hK₂X : K₂ ≤ X := inf_eq_right.1 h2
      have hK₁X : K₁ ≤ X := by
        have := conj_mono hK₂X t
        rwa [hK₂t, hXt] at this
      exact hNle hK₁X
  · right
    exact hNle (inf_eq_right.1 h1)

end SL2



theorem mem_normalizer_conj_of_comm {A : Subgroup G} {t r : G} (htr : t * r = r * t)
    (hr : r ∈ normalizer (A : Set G)) : r ∈ normalizer ((Aᵍ[t] : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_conj_iff, mem_conj_iff]
  have e : t * (r * x * r⁻¹) * t⁻¹ = r * (t * x * t⁻¹) * r⁻¹ := by
    calc t * (r * x * r⁻¹) * t⁻¹ = (t * r) * x * (t * r)⁻¹ := by group
      _ = (r * t) * x * (r * t)⁻¹ := by rw [htr]
      _ = r * (t * x * t⁻¹) * r⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 hr _

theorem mem_normalizer_centralizer_singleton {t g : G} (hg : g * t = t * g) :
    g ∈ normalizer (centralizer ({t} : Set G) : Set G) := by
  have fwd : ∀ {g : G}, g * t = t * g → ∀ y : G, y * t = t * y →
      (g * y * g⁻¹) * t = t * (g * y * g⁻¹) := by
    intro g hg y hy
    have hgi : g⁻¹ * t = t * g⁻¹ := by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
        _ = t * g⁻¹ := by group
    calc (g * y * g⁻¹) * t = g * y * (g⁻¹ * t) := by group
      _ = g * (y * t) * g⁻¹ := by rw [hgi]; group
      _ = g * (t * y) * g⁻¹ := by rw [hy]
      _ = (g * t) * y * g⁻¹ := by group
      _ = (t * g) * y * g⁻¹ := by rw [hg]
      _ = t * (g * y * g⁻¹) := by group
  have hgi : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
      _ = t * g⁻¹ := by group
  rw [mem_normalizer_iff]
  intro y
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  refine ⟨fwd hg y, fun hy => ?_⟩
  have := fwd hgi _ hy
  simpa [mul_assoc] using this

theorem pow_card_eq_one_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) : x ^ Nat.card H = 1 := by
  have := pow_card_eq_one' (G := H) (x := ⟨x, hx⟩)
  exact congrArg Subtype.val this

theorem mem_normalizer_of_forall_conj {H : Subgroup G} {g : G} (h₁ : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h₂ : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h₁ y, fun hy => ?_⟩
  have := h₂ _ hy
  simpa [mul_assoc] using this

theorem mem_centerMod_sup {U A B : Subgroup G} (hUA : U ≤ A) (hUB : U ≤ B)
    (hA : A ≤ normalizer (U : Set G)) (hB : B ≤ normalizer (U : Set G)) {z : G}
    (hzA : z ∈ centerMod U A) (hzB : z ∈ centerMod U B) : z ∈ centerMod U (A ⊔ B) := by
  rw [mem_centerMod_iff_of_le hUA hA] at hzA
  rw [mem_centerMod_iff_of_le hUB hB] at hzB
  rw [mem_centerMod_iff_of_le (hUA.trans le_sup_left) (sup_le hA hB)]
  refine ⟨mem_sup_left hzA.1, ?_⟩
  have h1 : A ≤ commSub U z := fun a ha => ⟨hA ha, hzA.2 a ha⟩
  have h2 : B ≤ commSub U z := fun a ha => ⟨hB ha, hzB.2 a ha⟩
  intro a ha
  exact (sup_le h1 h2 ha).2

theorem centralizerMod_conj {U B : Subgroup G} {g : G} (hg : g ∈ normalizer (U : Set G)) :
    centralizerMod U (Bᵍ[g]) = (centralizerMod U B)ᵍ[g] := by
  ext x
  have hx1 := mem_centralizerMod_iff
    (N := U) (B := Bᵍ[g]) (g := x)
  have hx2 : x ∈ (centralizerMod U B)ᵍ[g] ↔ g * x * g⁻¹ ∈ centralizerMod U B := mem_conj_iff
  have hx3 := mem_centralizerMod_iff
    (N := U) (B := B) (g := g * x * g⁻¹)
  rw [hx1, hx2, hx3]
  have hN : ∀ y, y ∈ normalizer (U : Set G) ↔ g * y * g⁻¹ ∈ normalizer (U : Set G) := by
    intro y
    constructor
    · intro hy
      exact mul_mem (mul_mem hg hy) (inv_mem hg)
    · intro hy
      have := mul_mem (mul_mem (inv_mem hg) hy) hg
      simpa [mul_assoc] using this
  refine and_congr (hN x) ?_
  constructor
  · intro H b hb hbn
    have := H (g⁻¹ * b * g) (by rw [mem_conj_iff]; simpa [mul_assoc] using hb)
      ((hN _).2 (by simpa [mul_assoc] using hbn))
    have e : g * (x * (g⁻¹ * b * g) * x⁻¹ * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * b * (g * x * g⁻¹)⁻¹ * b⁻¹ := by group
    have h2 := (mem_normalizer_iff.1 hg _).1 this
    rwa [e] at h2
  · intro H b hb hbn
    rw [mem_conj_iff] at hb
    have := H (g * b * g⁻¹) hb ((hN b).1 hbn)
    have e : g * (x * b * x⁻¹ * b⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * (g * b * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
    apply (mem_normalizer_iff.1 hg _).2
    rwa [e]

theorem mem_normalizer_centralizerMod {U B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (U : Set G)) (hgB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((centralizerMod U B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_eq
  rw [← centralizerMod_conj hg, conj_eq_of_mem_normalizer hgB]

theorem isFactor_conj {X N Λ : Subgroup G} {t : G} (hΛ : IsFactor X N Λ t K) (ht : t * t = 1)
    (h4 : 4 ≤ Nat.card K) : IsFactor X N (Λᵍ[t]) t K := by
  have hS := isFactor_sl2Pair hΛ ht h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hΛ.inf]
    exact inf_le_right
  · rw [← hΛ.sup]
    exact le_sup_right
  · rw [conj_conj_of_mul_self ht, sup_comm]
    exact hΛ.sup
  · rw [conj_conj_of_mul_self ht, inf_comm]
    exact hΛ.inf
  · rw [conj_conj_of_mul_self ht, Subgroup.commutator_comm]
    exact hΛ.comm
  · exact hS.isoK'

section SL2b

variable [Finite G]

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux in
theorem sl2Pair_sylow_conj {N D K₁ K₂ : Subgroup G} (hS : Sl2Pair K N D K₁ K₂) {t r : G}
    (ht : t * t = 1) (hKt : K₁ᵍ[t] = K₂) {P : Subgroup G} (hP : IsSylowOf 2 P N) (hDP : D ≤ P)
    (hPt : Pᵍ[t] = P) (hrN : r ∈ N) (hr2 : r * r = 1) (htr : t * r = r * t)
    (hrP : r ∉ normalizer (P : Set G)) :
    P ⊓ Pᵍ[r] = D ∧ K₁ = (P ⊓ K₁) ⊔ (P ⊓ K₁)ᵍ[r] ∧ K₂ = (P ⊓ K₂) ⊔ (P ⊓ K₂)ᵍ[r] := by
  have hK₂t : K₂ᵍ[t] = K₁ := by rw [← hKt, conj_conj_of_mul_self ht]
  obtain ⟨-, -, hPeq, hAA', -⟩ := sylow_prod hP hS.sup_eq hS.inf_eq hS.comm_le hDP
  have hrK₁ : r ∈ normalizer (K₁ : Set G) := hS.le_normalizer hrN
  have hrK₂ : r ∈ normalizer (K₂ : Set G) := hS.symm.le_normalizer hrN
  have hrD : r ∈ normalizer (D : Set G) := SL2Aux.le_normalizer_D hS hrN
  have hK₁r : K₁ᵍ[r] = K₁ := conj_eq_of_mem_normalizer hrK₁
  have hK₂r : K₂ᵍ[r] = K₂ := conj_eq_of_mem_normalizer hrK₂
  have hDr : Dᵍ[r] = D := conj_eq_of_mem_normalizer hrD
  have hDK₁ : D ≤ K₁ := SL2Aux.D_le_left hS
  have hDK₂ : D ≤ K₂ := SL2Aux.D_le_right hS
  set A := P ⊓ K₁ with hA
  set A' := P ⊓ K₂ with hA'
  have hA't : Aᵍ[t] = A' := by rw [hA, conj_inf, hPt, hKt]
  have hAr : Aᵍ[r] = Pᵍ[r] ⊓ K₁ := by rw [hA, conj_inf, hK₁r]
  have hA'r : A'ᵍ[r] = Pᵍ[r] ⊓ K₂ := by rw [hA', conj_inf, hK₂r]
  have hDAr : D ≤ Aᵍ[r] := by
    rw [← hDr]
    exact conj_mono (le_inf hDP hDK₁) r
  have hDA'r : D ≤ A'ᵍ[r] := by
    rw [← hDr]
    exact conj_mono (le_inf hDP hDK₂) r
  have hcardA : Nat.card A = Nat.card D * Nat.card K := by
    have h1 := hS.relIndex_sylow hP hDP
    have h2 := Subgroup.relIndex_mul_card D A
    rw [inf_eq_left.2 (le_inf hDP hDK₁), h1] at h2
    rw [← h2, mul_comm]
  have hcardA' : Nat.card A' = Nat.card D * Nat.card K := by
    have h1 := hS.symm.relIndex_sylow hP hDP
    have h2 := Subgroup.relIndex_mul_card D A'
    rw [inf_eq_left.2 (le_inf hDP hDK₂), h1] at h2
    rw [← h2, mul_comm]
  have hne : A ≠ Aᵍ[r] := by
    intro heq
    have hrA : r ∈ normalizer (A : Set G) := mem_normalizer_of_conj_eq heq.symm
    have hrA' : r ∈ normalizer (A' : Set G) := by
      rw [← hA't]
      exact mem_normalizer_conj_of_comm htr hrA
    apply hrP
    rw [hPeq]
    exact SL2Aux.mem_normalizer_sup hrA hrA'
  have hne' : A' ≠ A'ᵍ[r] := by
    intro heq
    have hrA' : r ∈ normalizer (A' : Set G) := mem_normalizer_of_conj_eq heq.symm
    have hAt : A'ᵍ[t] = A := by rw [← hA't, conj_conj_of_mul_self ht]
    have hrA : r ∈ normalizer (A : Set G) := by
      have := mem_normalizer_conj_of_comm htr hrA'
      rwa [hAt] at this
    apply hrP
    rw [hPeq]
    exact SL2Aux.mem_normalizer_sup hrA hrA'
  have hcardAr : Nat.card (Aᵍ[r]) = Nat.card D * Nat.card K := by rw [card_conj, hcardA]
  have hcardA'r : Nat.card (A'ᵍ[r]) = Nat.card D * Nat.card K := by rw [card_conj, hcardA']
  have hAr_le : Aᵍ[r] ≤ K₁ := by rw [hAr]; exact inf_le_right
  have hA'r_le : A'ᵍ[r] ≤ K₂ := by rw [hA'r]; exact inf_le_right
  obtain ⟨hsup1, hinf1⟩ := sl2Pair_sup_inf hS (le_inf hDP hDK₁) hDAr inf_le_right hAr_le hcardA
    hcardAr hne
  obtain ⟨hsup2, hinf2⟩ := sl2Pair_sup_inf hS.symm (le_inf hDP hDK₂) hDA'r inf_le_right hA'r_le
    hcardA' hcardA'r hne'
  refine ⟨?_, hsup1.symm, hsup2.symm⟩
  refine le_antisymm (fun x hx => ?_) (le_inf hDP (by rw [← hDr]; exact conj_mono hDP r))
  obtain ⟨hxP, hxPr⟩ := mem_inf.1 hx
  have hA'A : A' ≤ normalizer (A : Set G) := fun y hy =>
    SL2Aux.le_normalizer_inf P K₁
      ⟨le_normalizer (mem_inf.1 hy).1, SL2Aux.right_le_normalizer hS (mem_inf.1 hy).2⟩
  have hA'rAr : A'ᵍ[r] ≤ normalizer ((Aᵍ[r] : Subgroup G) : Set G) := by
    intro y hy
    rw [hAr]
    refine SL2Aux.le_normalizer_inf (Pᵍ[r]) K₁
      ⟨le_normalizer ?_, SL2Aux.right_le_normalizer hS (hA'r_le hy)⟩
    rw [hA'r] at hy
    exact (mem_inf.1 hy).1
  have hxsup : x ∈ A ⊔ A' := hPeq ▸ hxP
  have hxsup' : x ∈ Aᵍ[r] ⊔ A'ᵍ[r] := by
    have hPr : Pᵍ[r] = Aᵍ[r] ⊔ A'ᵍ[r] := by
      conv_lhs => rw [hPeq]
      exact conj_sup A A' r
    exact hPr ▸ hxPr
  obtain ⟨a, ha, a', ha', rfl⟩ := SL2Aux.exists_mul_of_mem_sup hA'A hxsup
  obtain ⟨b, hb, b', hb', hab⟩ := SL2Aux.exists_mul_of_mem_sup hA'rAr hxsup'
  have hba : b⁻¹ * a = b' * a'⁻¹ := by
    have : b⁻¹ * (a * a') = b' := by rw [hab]; group
    calc b⁻¹ * a = b⁻¹ * (a * a') * a'⁻¹ := by group
      _ = b' * a'⁻¹ := by rw [this]
  have hbaD : b⁻¹ * a ∈ D := by
    rw [← hS.inf_eq]
    refine mem_inf.2 ⟨mul_mem (inv_mem (hAr_le hb)) (mem_inf.1 ha).2, ?_⟩
    rw [hba]
    exact mul_mem (hA'r_le hb') (inv_mem (mem_inf.1 ha').2)
  have haD : a ∈ D := by
    have haAr : a ∈ Aᵍ[r] := by
      have := mul_mem hb (hDAr hbaD)
      simpa using this
    rw [← hinf1]
    exact mem_inf.2 ⟨ha, haAr⟩
  have ha'D : a' ∈ D := by
    have hba' : b' * a'⁻¹ ∈ D := hba ▸ hbaD
    have ha'Ar : a' ∈ A'ᵍ[r] := by
      have := mul_mem (inv_mem (hDA'r hba')) hb'
      simpa using this
    rw [← hinf2]
    exact mem_inf.2 ⟨ha', ha'Ar⟩
  exact mul_mem haD ha'D

end SL2b

end Generic

end ProductN1Aux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] in
private theorem wa_mem_leviA (d : G2Data L K) : d.wa ∈ d.leviA :=
  d.emb_mem_image (weylElt_mem_g2RankOne g2ir 1)

omit [Finite G] in
private theorem wa_not_mem_normalizer_S (d : G2Data L K) : d.wa ∉ normalizer (d.S : Set G) := by
  intro hmem
  have hSm : Model.S K ≤ adjointGroup .G2 K := Model.S_le_adjointGroup K
  have h1 : d.wa ∈ L ⊓ normalizer (d.image (Model.S K) : Set G) :=
    ⟨(d.wa_mem_inf_normalizer_U).1, hmem⟩
  rw [← d.image_inf_normalizer hSm] at h1
  obtain ⟨g, hg, hge⟩ := d.mem_image.1 h1
  have hgw : g = ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩ := d.emb_injective hge
  have hg' : (g : ModGL .G2 K) ∈ adjointGroup .G2 K ⊓ normalizer (Model.S K : Set (ModGL .G2 K)) :=
    ⟨g.2, (mem_inf.1 hg).2⟩
  rw [(Model.adjointGroup_inf_normalizer_S (K := K)).1] at hg'
  rw [hgw] at hg'
  exact weylElt_not_mem_borelGroup g2ir hg'

private theorem yamadaP_inf_centralizer_S (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ⊓ centralizer ({t} : Set G) = d.S := by
  have hSP : d.S ≤ yamadaP d t := by
    obtain ⟨-, -, -, -, hS₆P, -, -⟩ := h.yamadaP_facts hW d hK hQ
    exact (S_le_yamadaS₆ d t).trans hS₆P
  obtain ⟨-, hPR₈, -, -, -, -, -⟩ := h.yamadaP_facts hW d hK hQ
  obtain ⟨⟨-, -, htP⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  have htS : t ∈ normalizer (d.S : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))
  refine le_antisymm (fun x hx => ?_) (le_inf hSP (h.S_le_centralizer d))
  obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxR : x ∈ yamadaR d t := by
    rw [← (h.yamada_5_49_1 hW d hK hQ).2.2]
    exact Subgroup.mem_inf.2 ⟨hPR₈ hxP, hxC⟩
  rw [yamadaR, h.centralizer_L_inf] at hxR
  rcases (CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical.mem_sup_zpowers_iff_of_involution
    h.t_mul_t htS).1 hxR with hs | ⟨s, hs, e⟩
  · exact hs
  · exfalso
    apply htP
    have := mul_mem (inv_mem (hSP hs)) hxP
    rwa [e, inv_mul_cancel_left] at this

private theorem wa_not_mem_normalizer_P (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wa ∉ normalizer (yamadaP d t : Set G) := by
  intro hmem
  apply wa_not_mem_normalizer_S d
  have hwaC : d.wa ∈ normalizer (centralizer ({t} : Set G) : Set G) :=
    ProductN1Aux.mem_normalizer_centralizer_singleton
      (mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.wa_mem_inf_normalizer_U).1))
  have := Common.mem_normalizer_inf hmem hwaC
  rwa [yamadaP_inf_centralizer_S hW h d hK hQ] at this

omit [Finite G] [Finite K] in
private theorem yamadaK₁_le_inf_aux (d : G2Data L K) :
    yamadaK₁ d ≤ L ⊓ normalizer (d.U : Set G) :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem yamadaK₁_le_normalizer_D₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
  (yamadaK₁_le_inf_aux d).trans (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).1

private theorem normalizer_D₇_le_normalizer_N₁ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaD₇ d t : Set G) ≤ normalizer (yamadaN₁ d t : Set G) := by
  have hK₁ := yamadaK₁_le_normalizer_D₇ hW h d hK hQ
  have hN : ((yamadaN₁ d t).subgroupOf (normalizer (yamadaD₇ d t : Set G))).Normal :=
    CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer
      hK₁
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (yamadaN₁_le_normalizer d t hK₁)).1 hN

theorem yamada_7_6 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ : Subgroup G}
    (hΛ : IsFactor (yamadaD₇ d t) (yamadaN₁ d t) Λ₁ t K) :
    (yamadaP d t ⊓ (yamadaP d t)ᵍ[d.wa] = yamadaD₇ d t ∧
      Λ₁ = (yamadaP d t ⊓ Λ₁) ⊔ (yamadaP d t ⊓ Λ₁)ᵍ[d.wa] ∧
      d.J ≤ normalizer ((yamadaP d t ⊓ Λ₁ : Subgroup G) : Set G)) ∧
    (zc (yamadaN₁ d t) = yamadaU₁ d t ∧
      centerMod (yamadaU₁ d t) (yamadaN₁ d t) = yamadaU₁ d t ∧
      yamadaN₁ d t ⊓ centralizerMod (yamadaU₁ d t) (yamadaD₇ d t) = yamadaD₇ d t) ∧
    (centerMod (yamadaU₁ d t) (yamadaP d t) = yamadaY₂ d t ∧
      centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓
        centerMod (yamadaU₁ d t) ((yamadaP d t ⊓ Λ₁)ᵍ[t]) = yamadaY₂ d t ∧
      centerMod (yamadaU₁ d t) Λ₁ =
        centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓
          centerMod (yamadaU₁ d t) ((yamadaP d t ⊓ Λ₁)ᵍ[d.wa])) ∧
    (centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓ (d.D ⊔ yamadaU₁ d t) = d.Y ⊔ yamadaU₁ d t ∧
      centerMod (yamadaU₁ d t) Λ₁ ⊓ centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) = yamadaU₁ d t) := by
  classical
  have ht2 : t * t = 1 := h.t_mul_t
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hD := hQ.doubling
  have hDP : yamadaD₇ d t ≤ yamadaP d t := yamadaD₇_le_yamadaP d t
  have hDN : yamadaD₇ d t ≤ yamadaN₁ d t := yamadaD₇_le_yamadaN₁ d t
  obtain ⟨⟨-, htNP, htP⟩, -, ⟨-, htND, -⟩⟩ := h.yamada_5_51 hW d hK hQ
  have hS := ProductN1Aux.isFactor_sl2Pair hΛ ht2 hK4
  have hsyl := hp.sylow₁
  have hPt : (yamadaP d t)ᵍ[t] = yamadaP d t := conj_eq_of_mem_normalizer htNP
  have hwaU : d.wa ∈ L ⊓ normalizer (d.U : Set G) := d.wa_mem_inf_normalizer_U
  have hr2 : d.wa * d.wa = 1 := (d.yamada_3_7_G (hK ▸ h.four_le)).2.2.1
  have htr : t * d.wa = d.wa * t :=
    (mem_centralizer_singleton_iff.1 (h.L_le_centralizer hwaU.1)).symm
  have hwaK₁ : d.wa ∈ yamadaK₁ d := by
    rw [yamadaK₁_eq d hK4]
    exact mem_sup_right (wa_mem_leviA d)
  have hwaN : d.wa ∈ yamadaN₁ d t := yamadaK₁_le_yamadaN₁ d t hwaK₁
  have hwaD : d.wa ∈ normalizer (yamadaD₇ d t : Set G) :=
    h.wa_mem_normalizer_yamadaD₇ hW d hK hQ
  have hwaP := wa_not_mem_normalizer_P hW h d hK hQ
  obtain ⟨hPPr, hΛeq, hΛteq⟩ :=
    ProductN1Aux.sl2Pair_sylow_conj hS ht2 rfl hsyl hDP hPt hwaN hr2 htr hwaP
  have hJD : d.J ≤ normalizer (yamadaD₇ d t : Set G) := h.J_le_normalizer_yamadaD₇ hW d hK hQ
  have hJP : d.J ≤ normalizer (yamadaP d t : Set G) := h.J_le_normalizer_yamadaP hW d hK hQ
  have hJN : d.J ≤ normalizer (yamadaN₁ d t : Set G) := fun j hj =>
    normalizer_D₇_le_normalizer_N₁ hW h d hK hQ (hJD hj)
  have hJΛ : d.J ≤ normalizer (Λ₁ : Set G) := by
    intro j hj
    exact mem_normalizer_of_pow_mem hS.ne (hS.conj_factor (hJN hj) (hJD hj))
      (Or.comm.1 (hS.symm.conj_factor (hJN hj) (hJD hj))) (odd_card_J d)
      (by rw [ProductN1Aux.pow_card_eq_one_of_mem hj]; exact one_mem _)
  have hJA : d.J ≤ normalizer ((yamadaP d t ⊓ Λ₁ : Subgroup G) : Set G) := fun j hj =>
    Common.mem_normalizer_inf (hJP hj) (hJΛ hj)
  obtain ⟨hZ, hZ2⟩ := h.yamada_5_52 hW d hK hQ
  have hZ0 : (Subgroup.upperCentralSeries (yamadaP d t) 0).map (yamadaP d t).subtype = ⊥ := by
    rw [Subgroup.upperCentralSeries_zero]
    exact Subgroup.map_bot _
  have hmemU₁ := fun x => mem_of_map_upperCentralSeries_succ hZ0 hZ (x := x)
  have hmemY₂ := fun x => mem_of_map_upperCentralSeries_succ hZ hZ2 (x := x)
  have hU₁P : yamadaU₁ d t ≤ yamadaP d t := fun u hu => ((hmemU₁ u).1 hu).1
  have hU₁c : ∀ u ∈ yamadaU₁ d t, ∀ g ∈ yamadaP d t, g * u = u * g := fun u hu g hg => by
    have := ((hmemU₁ u).1 hu).2 g hg
    have h1 : u * g * u⁻¹ * g⁻¹ = 1 := by simpa using this
    calc g * u = (u * g * u⁻¹ * g⁻¹)⁻¹ * (u * g) := by group
      _ = u * g := by rw [h1]; group
  have hPU₁ : yamadaP d t ≤ normalizer (yamadaU₁ d t : Set G) := fun g hg =>
    ProductN1Aux.mem_normalizer_of_forall_conj (fun u hu => by
      rw [show g * u * g⁻¹ = u by rw [hU₁c u hu g hg]; group]
      exact hu) (fun u hu => by
      rw [show g⁻¹ * u * g = u by rw [hU₁c u hu g⁻¹ (inv_mem hg), inv_mul_cancel_right]]
      exact hu)
  have hY₂P : yamadaY₂ d t ≤ yamadaP d t := fun y hy => ((hmemY₂ y).1 hy).1
  have hcmP : centerMod (yamadaU₁ d t) (yamadaP d t) = yamadaY₂ d t := by
    ext z
    rw [ProductN1Aux.mem_centerMod_iff_of_le hU₁P hPU₁]
    exact (hmemY₂ z).symm
  obtain ⟨hAsyl, hA'syl, hPeq, hAA', -⟩ := sylow_prod hsyl hS.sup_eq hS.inf_eq hS.comm_le hDP
  have hPN : yamadaP d t ≤ yamadaN₁ d t := hsyl.le
  have hPrN : (yamadaP d t)ᵍ[d.wa] ≤ yamadaN₁ d t := by
    intro x hx
    rw [mem_conj_iff] at hx
    have := mul_mem (mul_mem (inv_mem hwaN) (hPN hx)) hwaN
    simpa [mul_assoc] using this
  have hNeq : yamadaN₁ d t = yamadaP d t ⊔ (yamadaP d t)ᵍ[d.wa] := by
    refine le_antisymm ?_ (sup_le hPN hPrN)
    rw [← hS.sup_eq]
    refine sup_le (hΛeq.le.trans (sup_le ?_ ?_)) (hΛteq.le.trans (sup_le ?_ ?_))
    · exact (inf_le_left : yamadaP d t ⊓ Λ₁ ≤ yamadaP d t).trans le_sup_left
    · exact (conj_mono (inf_le_left : yamadaP d t ⊓ Λ₁ ≤ yamadaP d t) d.wa).trans le_sup_right
    · exact (inf_le_left : yamadaP d t ⊓ Λ₁ᵍ[t] ≤ yamadaP d t).trans le_sup_left
    · exact (conj_mono (inf_le_left : yamadaP d t ⊓ Λ₁ᵍ[t] ≤ yamadaP d t) d.wa).trans
        le_sup_right
  have hwaU₁ : d.wa ∈ normalizer (yamadaU₁ d t : Set G) :=
    hD.inf_normalizer_U_le_normalizer hK hwaU
  have hU₁N : ∀ u ∈ yamadaU₁ d t, ∀ n ∈ yamadaN₁ d t, u * n = n * u := by
    have hle : yamadaN₁ d t ≤ Subgroup.centralizer (yamadaU₁ d t : Set G) := by
      rw [hNeq]
      refine sup_le (fun g hg => mem_centralizer_iff.2 fun u hu => (hU₁c u hu g hg).symm) ?_
      intro x hx
      rw [mem_conj_iff] at hx
      refine mem_centralizer_iff.2 fun u hu => ?_
      have hu' : d.wa * u * d.wa⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 hwaU₁ u).1 hu
      have := hU₁c _ hu' _ hx
      have e1 : (d.wa * x * d.wa⁻¹) * (d.wa * u * d.wa⁻¹) = d.wa * (x * u) * d.wa⁻¹ := by group
      have e2 : (d.wa * u * d.wa⁻¹) * (d.wa * x * d.wa⁻¹) = d.wa * (u * x) * d.wa⁻¹ := by group
      rw [e1, e2] at this
      exact (mul_left_cancel (mul_right_cancel this)).symm
    intro u hu n hn
    exact (mem_centralizer_iff.1 (hle hn) u hu)
  have hU₁Nle : yamadaU₁ d t ≤ yamadaN₁ d t := hU₁P.trans hPN
  have hNU₁ : yamadaN₁ d t ≤ normalizer (yamadaU₁ d t : Set G) := fun n hn =>
    ProductN1Aux.mem_normalizer_of_forall_conj (fun u hu => by
      rw [show n * u * n⁻¹ = u by rw [← hU₁N u hu n hn]; group]
      exact hu) (fun u hu => by
      rw [show n⁻¹ * u * n = u by rw [← hU₁N u hu n⁻¹ (inv_mem hn), inv_mul_cancel_right]]
      exact hu)
  have hD₇U₁ : ∀ x ∈ yamadaD₇ d t, ∀ y ∈ yamadaD₇ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaU₁ d t :=
    h.commutator_mem_yamadaU₁_of_mem_yamadaD₇ hW d hK hQ
  have htU₁ : t ∈ normalizer (yamadaU₁ d t : Set G) := (h.t_mem_normalizer_yamadaU₁ d hK hD).1
  have htN : t ∈ normalizer (yamadaN₁ d t : Set G) :=
    normalizer_D₇_le_normalizer_N₁ hW h d hK hQ htND
  have hU₁D₇ : yamadaU₁ d t ≤ yamadaD₇ d t := h.yamadaU₁_le_yamadaD₇ hW d hK hQ
  have hND : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) := le_normalizer_D hS
  have hY₂W₃ : yamadaY₂ d t ≤ yamadaW₃ d t :=
    (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans (h.yamadaW₃_facts hW d hK hD).2.2.2.1
  have h2c : yamadaN₁ d t ⊓ centralizerMod (yamadaU₁ d t) (yamadaD₇ d t) = yamadaD₇ d t := by
    set X := yamadaN₁ d t ⊓ centralizerMod (yamadaU₁ d t) (yamadaD₇ d t) with hX
    have hDC : yamadaD₇ d t ≤ centralizerMod (yamadaU₁ d t) (yamadaD₇ d t) := by
      intro g hg
      rw [mem_centralizerMod_iff]
      exact ⟨hNU₁ (hDN hg), fun b hb _ => hD₇U₁ g hg b hb⟩
    have hDX : yamadaD₇ d t ≤ X := le_inf hDN hDC
    have hNX : yamadaN₁ d t ≤ normalizer (X : Set G) := fun n hn =>
      Common.mem_normalizer_inf (le_normalizer hn)
        (ProductN1Aux.mem_normalizer_centralizerMod (hNU₁ hn) (hND hn))
    have hXt : Xᵍ[t] = X := by
      rw [hX, conj_inf, conj_eq_of_mem_normalizer htN,
        ← ProductN1Aux.centralizerMod_conj htU₁, conj_eq_of_mem_normalizer htND]
    rcases ProductN1Aux.sl2Pair_eq_or_eq hS ht2 rfl hDX inf_le_left hNX hXt with h1 | h1
    · exact h1
    · exfalso
      have hNC : yamadaN₁ d t ≤ centralizerMod (yamadaU₁ d t) (yamadaD₇ d t) := fun n hn =>
        (mem_inf.1 (h1.symm ▸ hn : n ∈ X)).2
      have hDY : yamadaD₇ d t ≤ yamadaY₂ d t := by
        intro z hz
        rw [← hcmP]
        refine (ProductN1Aux.mem_centerMod_iff_of_le hU₁P hPU₁).2 ⟨hDP hz, fun a ha => ?_⟩
        have h2 := ((mem_centralizerMod_iff.1
          (hNC (hPN ha))).2 z hz (hNU₁ (hDN hz)))
        have h3 := inv_mem h2
        rwa [show (a * z * a⁻¹ * z⁻¹)⁻¹ = z * a * z⁻¹ * a⁻¹ by group] at h3
      have hcard := Subgroup.card_le_of_le hDY
      rw [h.card_yamadaD₇ hW d hK hQ, h.card_yamadaY₂ d hK hD] at hcard
      exact absurd hcard (not_le.2 (Nat.pow_lt_pow_right (by omega) (by norm_num)))
  have hZmem : ∀ z ∈ centerMod (yamadaU₁ d t) (yamadaN₁ d t), z ∈ yamadaY₂ d t := by
    intro z hz
    obtain ⟨hzN, hzc⟩ := (ProductN1Aux.mem_centerMod_iff_of_le hU₁Nle hNU₁).1 hz
    have hzD : z ∈ yamadaD₇ d t := by
      rw [← h2c]
      refine mem_inf.2 ⟨hzN, ?_⟩
      rw [mem_centralizerMod_iff]
      exact ⟨hNU₁ hzN, fun b hb _ => hzc b (hDN hb)⟩
    rw [← hcmP]
    exact (ProductN1Aux.mem_centerMod_iff_of_le hU₁P hPU₁).2
      ⟨hDP hzD, fun a ha => hzc a (hPN ha)⟩
  have h2b : centerMod (yamadaU₁ d t) (yamadaN₁ d t) = yamadaU₁ d t := by
    refine le_antisymm (fun z hz => ?_) (fun u hu => ?_)
    · have hz₁ := hZmem z hz
      have hz' : d.wa * z * d.wa⁻¹ ∈ centerMod (yamadaU₁ d t) (yamadaN₁ d t) := by
        have := ProductN1Aux.mem_normalizer_centerMod hwaU₁ (le_normalizer hwaN) hU₁Nle
        exact (mem_normalizer_iff.1 this z).1 hz
      have hz₂ := hZmem _ hz'
      rw [← Q52.yamadaW₃_inf_map_wa hW h d hK hQ]
      refine mem_inf.2 ⟨hY₂W₃ hz₁, ?_⟩
      rw [mem_map_conj_iff]
      have e : d.wa⁻¹ * z * d.wa = d.wa * z * d.wa⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right hr2]
      rw [e]
      exact hY₂W₃ hz₂
    · refine (ProductN1Aux.mem_centerMod_iff_of_le hU₁Nle hNU₁).2 ⟨hU₁Nle hu, fun a ha => ?_⟩
      have : u * a * u⁻¹ * a⁻¹ = 1 := by rw [hU₁N u hu a ha]; group
      rw [this]
      exact one_mem _
  have h2a : zc (yamadaN₁ d t) = yamadaU₁ d t := by
    refine le_antisymm (fun z hz => ?_) (fun u hu => ?_)
    · rw [← h2b]
      refine (ProductN1Aux.mem_centerMod_iff_of_le hU₁Nle hNU₁).2 ⟨hz.1, fun a ha => ?_⟩
      have : z * a * z⁻¹ * a⁻¹ = 1 := by
        rw [← mem_centralizer_iff.1 hz.2 a ha]; group
      rw [this]
      exact one_mem _
    · refine ⟨hU₁Nle hu, mem_centralizer_iff.2 fun n hn => ?_⟩
      exact (hU₁N u hu n hn).symm
  have hDΛ : yamadaD₇ d t ≤ Λ₁ := hΛ.X_le
  have hDΛt : yamadaD₇ d t ≤ Λ₁ᵍ[t] := D_le_right hS
  have hΛN : Λ₁ ≤ yamadaN₁ d t := left_le hS
  have hΛtN : Λ₁ᵍ[t] ≤ yamadaN₁ d t := right_le hS
  have hA't : (yamadaP d t ⊓ Λ₁)ᵍ[t] = yamadaP d t ⊓ Λ₁ᵍ[t] := by rw [conj_inf, hPt]
  have hDA : yamadaD₇ d t ≤ yamadaP d t ⊓ Λ₁ := le_inf hDP hDΛ
  have hDA' : yamadaD₇ d t ≤ yamadaP d t ⊓ Λ₁ᵍ[t] := le_inf hDP hDΛt
  have hUA : yamadaU₁ d t ≤ yamadaP d t ⊓ Λ₁ := hU₁D₇.trans hDA
  have hUA' : yamadaU₁ d t ≤ yamadaP d t ⊓ Λ₁ᵍ[t] := hU₁D₇.trans hDA'
  have hAN : (yamadaP d t ⊓ Λ₁ : Subgroup G) ≤ normalizer (yamadaU₁ d t : Set G) :=
    inf_le_left.trans hPU₁
  have hA'N : (yamadaP d t ⊓ Λ₁ᵍ[t] : Subgroup G) ≤ normalizer (yamadaU₁ d t : Set G) :=
    inf_le_left.trans hPU₁
  have hΛU : Λ₁ ≤ normalizer (yamadaU₁ d t : Set G) := hΛN.trans hNU₁
  have hΛtU : Λ₁ᵍ[t] ≤ normalizer (yamadaU₁ d t : Set G) := hΛtN.trans hNU₁
  have hY₂D₇ : yamadaY₂ d t ≤ yamadaD₇ d t := h.yamadaY₂_le_yamadaD₇ hW d hK hQ
  have hY₂cA : yamadaY₂ d t ≤ centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) := by
    intro y hy
    have hy' := hy
    rw [← hcmP] at hy'
    obtain ⟨-, hyc⟩ := (ProductN1Aux.mem_centerMod_iff_of_le hU₁P hPU₁).1 hy'
    exact (ProductN1Aux.mem_centerMod_iff_of_le hUA hAN).2
      ⟨hDA (hY₂D₇ hy), fun a ha => hyc a (mem_inf.1 ha).1⟩
  have hY₂cA' : yamadaY₂ d t ≤ centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁ᵍ[t]) := by
    intro y hy
    have hy' := hy
    rw [← hcmP] at hy'
    obtain ⟨-, hyc⟩ := (ProductN1Aux.mem_centerMod_iff_of_le hU₁P hPU₁).1 hy'
    exact (ProductN1Aux.mem_centerMod_iff_of_le hUA' hA'N).2
      ⟨hDA' (hY₂D₇ hy), fun a ha => hyc a (mem_inf.1 ha).1⟩
  have h3b : centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓
      centerMod (yamadaU₁ d t) ((yamadaP d t ⊓ Λ₁)ᵍ[t]) = yamadaY₂ d t := by
    rw [hA't]
    refine le_antisymm (fun z hz => ?_) (le_inf hY₂cA hY₂cA')
    have := ProductN1Aux.mem_centerMod_sup hUA hUA' hAN hA'N (mem_inf.1 hz).1 (mem_inf.1 hz).2
    rw [← hPeq, hcmP] at this
    exact this
  have hArU : yamadaU₁ d t ≤ (yamadaP d t ⊓ Λ₁)ᵍ[d.wa] := fun u hu => by
    rw [mem_conj_iff]
    exact hDA ((mem_normalizer_iff.1 hwaD u).1 (hU₁D₇ hu))
  have hArΛ : (yamadaP d t ⊓ Λ₁)ᵍ[d.wa] ≤ Λ₁ := (le_sup_right.trans hΛeq.ge)
  have hArN : (yamadaP d t ⊓ Λ₁)ᵍ[d.wa] ≤ normalizer (yamadaU₁ d t : Set G) :=
    hArΛ.trans hΛU
  have h3c : centerMod (yamadaU₁ d t) Λ₁ = centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓
      centerMod (yamadaU₁ d t) ((yamadaP d t ⊓ Λ₁)ᵍ[d.wa]) := by
    refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · have hz' := (ProductN1Aux.mem_centerMod_iff_of_le (hU₁D₇.trans hDΛ) hΛU).1 hz
      have hzD : z ∈ yamadaD₇ d t := mem_D_of_comm hS hz'.1 (fun x hx => hU₁D₇ (hz'.2 x hx))
      refine mem_inf.2 ⟨?_, ?_⟩
      · exact (ProductN1Aux.mem_centerMod_iff_of_le hUA hAN).2
          ⟨hDA hzD, fun a ha => hz'.2 a (mem_inf.1 ha).2⟩
      · refine (ProductN1Aux.mem_centerMod_iff_of_le hArU hArN).2
          ⟨?_, fun a ha => hz'.2 a (hArΛ ha)⟩
        rw [mem_conj_iff]
        exact hDA ((mem_normalizer_iff.1 hwaD z).1 hzD)
    · have := ProductN1Aux.mem_centerMod_sup hUA hArU hAN hArN (mem_inf.1 hz).1 (mem_inf.1 hz).2
      rwa [← hΛeq] at this
  have hcomm1 : ∀ u ∈ yamadaU₁ d t, ∀ a ∈ yamadaN₁ d t, u * a * u⁻¹ * a⁻¹ ∈ yamadaU₁ d t := by
    intro u hu a ha
    have : u * a * u⁻¹ * a⁻¹ = 1 := by rw [hU₁N u hu a ha]; group
    rw [this]
    exact one_mem _
  have h4b : centerMod (yamadaU₁ d t) Λ₁ ⊓ centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) =
      yamadaU₁ d t := by
    refine le_antisymm (fun z hz => ?_) (fun u hu => mem_inf.2 ⟨?_, ?_⟩)
    · have := ProductN1Aux.mem_centerMod_sup (hU₁D₇.trans hDΛ) (hU₁D₇.trans hDΛt) hΛU hΛtU
        (mem_inf.1 hz).1 (mem_inf.1 hz).2
      rw [hS.sup_eq, h2b] at this
      exact this
    · exact (ProductN1Aux.mem_centerMod_iff_of_le (hU₁D₇.trans hDΛ) hΛU).2
        ⟨hDΛ (hU₁D₇ hu), fun a ha => hcomm1 u hu a (hΛN ha)⟩
    · exact (ProductN1Aux.mem_centerMod_iff_of_le (hU₁D₇.trans hDΛt) hΛtU).2
        ⟨hDΛt (hU₁D₇ hu), fun a ha => hcomm1 u hu a (hΛtN ha)⟩
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -, hSL⟩ := d.inclusions
  have hDC : d.D ≤ centralizer ({t} : Set G) := (hDS.trans hSL).trans h.L_le_centralizer
  have hYD : d.Y ≤ d.D := hYX.trans (hXF.trans hFD)
  have hU₁Dn : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
    h.yamadaU₁_le_normalizer_of_le_D d hK hD le_rfl
  have hU₁cA : yamadaU₁ d t ≤ centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) := fun u hu =>
    (ProductN1Aux.mem_centerMod_iff_of_le hUA hAN).2
      ⟨hUA hu, fun a ha => hcomm1 u hu a (hPN (mem_inf.1 ha).1)⟩
  have h4a : centerMod (yamadaU₁ d t) (yamadaP d t ⊓ Λ₁) ⊓ (d.D ⊔ yamadaU₁ d t) =
      d.Y ⊔ yamadaU₁ d t := by
    refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨hzA, hzDU⟩ := mem_inf.1 hz
      obtain ⟨δ, hδ, u, hu, hzeq⟩ := exists_mul_of_mem_sup hU₁Dn hzDU
      have hδC : δ * t = t * δ := mem_centralizer_singleton_iff.1 (hDC hδ)
      have hδt : t * δ * t⁻¹ = δ := by rw [← hδC]; group
      have hu' : t * u * t⁻¹ ∈ yamadaU₁ d t := (mem_normalizer_iff.1 htU₁ u).1 hu
      have e : t * z * t⁻¹ = z * (u⁻¹ * (t * u * t⁻¹)) := by
        rw [hzeq]
        calc t * (δ * u) * t⁻¹ = (t * δ * t⁻¹) * (t * u * t⁻¹) := by group
          _ = δ * (t * u * t⁻¹) := by rw [hδt]
          _ = δ * u * (u⁻¹ * (t * u * t⁻¹)) := by group
      have hzt : z ∈ centerMod (yamadaU₁ d t) ((yamadaP d t ⊓ Λ₁)ᵍ[t]) := by
        rw [ProductN1Aux.centerMod_conj htU₁ hUA, mem_conj_iff, e]
        exact mul_mem hzA (hU₁cA (mul_mem (inv_mem hu) hu'))
      have hzY : z ∈ yamadaY₂ d t := by
        rw [← h3b]
        exact mem_inf.2 ⟨hzA, hzt⟩
      have hδY : δ ∈ d.Y := by
        rw [← h.yamadaY₂_inf_centralizer d hK hD]
        refine mem_inf.2 ⟨?_, hDC hδ⟩
        have : δ = z * u⁻¹ := by rw [hzeq]; group
        rw [this]
        exact mul_mem hzY (inv_mem (yamadaU₁_le_yamadaY₂ d t hu))
      rw [hzeq]
      exact mul_mem (mem_sup_left hδY) (mem_sup_right hu)
    · have hYU : d.Y ⊔ yamadaU₁ d t ≤ yamadaY₂ d t :=
        sup_le (h.Y_le_yamadaY₂ d hK hD) (yamadaU₁_le_yamadaY₂ d t)
      exact mem_inf.2 ⟨hY₂cA (hYU hz), sup_le_sup_right hYD _ hz⟩
  exact ⟨⟨hPPr, hΛeq, hJA⟩, ⟨h2a, h2b, h2c⟩, ⟨hcmP, h3b, h3c⟩, ⟨h4a, h4b⟩⟩

omit [Finite G] [Finite K] in
private theorem yamadaK₂_le_inf_aux (d : G2Data L K) :
    yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G) :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem normalizer_M₆_le_normalizer_N₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaN₂ d t : Set G) := by
  have hK₂ : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (yamadaK₂_le_inf_aux d).trans (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  have hN : ((yamadaN₂ d t).subgroupOf (normalizer (yamadaM₆ d t : Set G))).Normal :=
    CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer
      hK₂
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (yamadaN₂_le_normalizer d t hK₂)).1 hN

theorem exists_labelled (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    ∃ Λ₁ Λ₂ : Subgroup G, Labelled d t Λ₁ Λ₂ := by
  classical
  have ht2 : t * t = 1 := h.t_mul_t
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hD := hQ.doubling
  obtain ⟨Λ₂, hΛ₂⟩ := exists_isFactor₂ hW h d hK hQ hp
  obtain ⟨Λ₀, hΛ₀⟩ := exists_isFactor₁ hW h d hK hQ hp
  have hS₁ := ProductN1Aux.isFactor_sl2Pair hΛ₀ ht2 hK4
  have hS₂ := ProductN1Aux.isFactor_sl2Pair hΛ₂ ht2 hK4
  have hsyl₁ := hp.sylow₁
  have hsyl₂ := hp.sylow₂
  have hDP : yamadaD₇ d t ≤ yamadaP d t := yamadaD₇_le_yamadaP d t
  have hM₆P : yamadaM₆ d t ≤ yamadaP d t := h.yamadaM₆_le_yamadaP hW d hK hQ
  obtain ⟨⟨-, htNP, htP⟩, -, ⟨-, htND, -⟩⟩ := h.yamada_5_51 hW d hK hQ
  have hPt : (yamadaP d t)ᵍ[t] = yamadaP d t := conj_eq_of_mem_normalizer htNP
  obtain ⟨hZ1, hZ2, hZ3⟩ := h.yamada_5_57_1 hW d hK hQ
  obtain ⟨hPD₇, hPM₆⟩ := h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ
  obtain ⟨⟨-, hMsup, -⟩, -, -, hP₂⟩ := h.yamada_7_3 hW d hK hQ hp hΛ₂
  obtain ⟨⟨-, hcY⟩, -⟩ := h.yamada_7_4 hW d hK hQ hp hΛ₂
  have hchar := (h.yamada_7_3_char hW d hK hQ hp).1
  obtain ⟨α, hex₂, -⟩ := hp.exact₂
  obtain ⟨hN₂W₃, -, -, hcF, -, -⟩ := h.yamadaN₂_centers hW d hK hQ hsyl₂ hex₂
  have hM₆Λ : yamadaM₆ d t ≤ Λ₂ := hΛ₂.X_le
  have hM₆Λt : yamadaM₆ d t ≤ Λ₂ᵍ[t] := D_le_right hS₂
  have hY₂M₆ := h.yamadaY₂_le_yamadaM₆ hW d hK hQ
  have hW₃M₆ := h.yamadaW₃_le_yamadaM₆ hW d hK hQ
  have hF₅M₆ := h.yamadaF₅_le_yamadaM₆ hW d hK hQ
  have hF₅D₇ := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
  have hM₆D₇ : yamadaM₆ d t ⊓ yamadaD₇ d t = yamadaF₅ d t := h.yamadaM₆_inf_yamadaD₇ hW d hK hQ
  have hM₆F₅ : ¬ yamadaM₆ d t ≤ yamadaF₅ d t := by
    intro hle
    have := Subgroup.card_le_of_le hle
    obtain ⟨-, -, -, hF₅, -, -, hM₆, -, -⟩ := h.card_yamada_five_six hW d hK hQ
    rw [hM₆, hF₅] at this
    exact absurd this (not_le.2 (Nat.pow_lt_pow_right (by omega) (by norm_num)))
  have hP₂N : yamadaP d t ≤ yamadaN₂ d t := hsyl₂.le
  have hPΛ₂ : yamadaP d t ≤ normalizer (Λ₂ : Set G) := fun p hp => hS₂.le_normalizer (hP₂N hp)
  have hPY : ∀ g ∈ normalizer (yamadaP d t : Set G), g ∈ normalizer (yamadaY₂ d t : Set G) :=
    fun g hg => hZ2 ▸ mem_normalizer_map_upperCentralSeries hg 2
  have hY₂P : yamadaY₂ d t ≤ yamadaP d t := hY₂M₆.trans hM₆P
  have hY₂A : yamadaY₂ d t ≤ yamadaP d t ⊓ Λ₂ := le_inf hY₂P (hY₂M₆.trans hM₆Λ)
  have hAY : (yamadaP d t ⊓ Λ₂ : Subgroup G) ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg =>
    hPY g (le_normalizer (mem_inf.1 hg).1)
  have hcA : centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) ≤ yamadaP d t ⊓ Λ₂ := fun z hz =>
    ((ProductN1Aux.mem_centerMod_iff_of_le hY₂A hAY).1 hz).1
  have hWdef : centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) = yamadaF₅ d t ⊔
      centerMod (yamadaW₃ d t) Λ₂ := by rw [hcY, hP₂]
  set Z := centerMod (yamadaW₃ d t) Λ₂ with hZdef
  set W := centerMod (yamadaY₂ d t) (yamadaP d t ⊓ Λ₂) ⊔ yamadaD₇ d t with hWdef'
  have hDW : yamadaD₇ d t ≤ W := le_sup_right
  have hWP : W ≤ yamadaP d t := sup_le (hcA.trans inf_le_left) hDP
  have hinv : yamadaN₁ d t ⊓ normalizer (yamadaP d t : Set G) ≤ normalizer (W : Set G) := by
    intro g hg
    obtain ⟨hgN₁, hgP⟩ := mem_inf.1 hg
    have hg' : g ∈ normalizer (yamadaM₆ d t : Set G) ⊓ normalizer (yamadaD₇ d t : Set G) :=
      hchar ▸ hgP
    have hgN₂ : g ∈ normalizer (yamadaN₂ d t : Set G) :=
      normalizer_M₆_le_normalizer_N₂ hW h d hK hQ hg'.1
    have hfac1 := hS₂.conj_factor hgN₂ hg'.1
    have hfac2 := hS₂.symm.conj_factor hgN₂ hg'.1
    have hPM : yamadaP d t ≤ yamadaN₁ d t ⊓ normalizer (yamadaP d t : Set G) :=
      le_inf hsyl₁.le le_normalizer
    have hodd : Odd ((yamadaP d t).relIndex
        (yamadaN₁ d t ⊓ normalizer (yamadaP d t : Set G))) := by
      have h1 := Subgroup.relIndex_mul_relIndex (yamadaP d t)
        (yamadaN₁ d t ⊓ normalizer (yamadaP d t : Set G)) (yamadaN₁ d t) hPM inf_le_left
      have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hsyl₁).2.2
      rw [Nat.odd_iff]
      by_contra hc
      exact h2 (by rw [← h1]; exact Dvd.dvd.mul_right (by omega) _)
    have hgΛ₂ : g ∈ normalizer (Λ₂ : Set G) :=
      mem_normalizer_of_pow_mem hS₂.ne hfac1 (Or.comm.1 hfac2) hodd
        (hPΛ₂ (CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.pow_relIndex_mem
          hPM inf_le_right hg))
    have hgA : g ∈ normalizer ((yamadaP d t ⊓ Λ₂ : Subgroup G) : Set G) :=
      Common.mem_normalizer_inf hgP hgΛ₂
    exact mem_normalizer_sup (ProductN1Aux.mem_normalizer_centerMod (hPY g hgP) hgA hY₂A) hg'.2
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) := Q44.t_mem_normalizer_W₃ hW h d hK hD
  have hW₃Λ : yamadaW₃ d t ≤ Λ₂ := hW₃M₆.trans hM₆Λ
  have hZ'eq : centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) = Zᵍ[t] :=
    ProductN1Aux.centerMod_conj htW₃ hW₃Λ
  have hZM : Z ≤ yamadaM₆ d t := hMsup ▸ le_sup_left
  have hF₅t : (yamadaF₅ d t)ᵍ[t] = yamadaF₅ d t :=
    conj_eq_of_mem_normalizer (hZ3 ▸ mem_normalizer_map_upperCentralSeries htNP 3)
  have hM₆t : (yamadaM₆ d t)ᵍ[t] = yamadaM₆ d t :=
    conj_eq_of_mem_normalizer (Q44.t_mem_normalizer_M₆ hW h d hK hQ)
  have hWD : W ≠ yamadaD₇ d t := by
    intro hWeq
    have hZD : Z ≤ yamadaD₇ d t := by
      refine le_trans ?_ hWeq.le
      rw [hWdef', hWdef]
      exact le_sup_right.trans le_sup_left
    have hZF : Z ≤ yamadaF₅ d t := hM₆D₇ ▸ le_inf hZM hZD
    have hZ'F : centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) ≤ yamadaF₅ d t := by
      rw [hZ'eq]
      have := conj_mono hZF t
      rwa [hF₅t] at this
    exact hM₆F₅ (hMsup ▸ sup_le hZF hZ'F)
  have hWP' : W ≠ yamadaP d t := by
    intro hWeq
    have hEM : yamadaF₅ d t ⊔ Z ≤ yamadaM₆ d t := sup_le hF₅M₆ hZM
    have hM₆E : yamadaM₆ d t ≤ yamadaF₅ d t ⊔ Z := by
      intro m hm
      have hmW : m ∈ W := hWeq ▸ hM₆P hm
      have hW' : W = (yamadaF₅ d t ⊔ Z) ⊔ yamadaD₇ d t := by rw [hWdef', hWdef]
      rw [hW', sup_comm] at hmW
      have hEN : (yamadaF₅ d t ⊔ Z) ≤ normalizer (yamadaD₇ d t : Set G) :=
        (sup_le (hF₅M₆.trans hM₆P) (hZM.trans hM₆P)).trans hPD₇
      obtain ⟨d', hd', e, he, hme⟩ := exists_mul_of_mem_sup hEN hmW
      have hd'M : d' ∈ yamadaM₆ d t := by
        have : d' = m * e⁻¹ := by rw [hme]; group
        rw [this]
        exact mul_mem hm (inv_mem (hEM he))
      have hd'F : d' ∈ yamadaF₅ d t := hM₆D₇ ▸ mem_inf.2 ⟨hd'M, hd'⟩
      rw [hme]
      exact mul_mem (mem_sup_left hd'F) he
    have hEeq : yamadaF₅ d t ⊔ Z = yamadaM₆ d t := le_antisymm hEM hM₆E
    have hW₃A : yamadaW₃ d t ≤ yamadaP d t ⊓ Λ₂ := le_inf (hW₃M₆.trans hM₆P) hW₃Λ
    have hW₃A' : yamadaW₃ d t ≤ yamadaP d t ⊓ Λ₂ᵍ[t] :=
      le_inf (hW₃M₆.trans hM₆P) (hW₃M₆.trans hM₆Λt)
    have hPW₃ : yamadaP d t ≤ normalizer (yamadaW₃ d t : Set G) := fun g hg => hN₂W₃ (hP₂N hg)
    have hA₂W : (yamadaP d t ⊓ Λ₂ : Subgroup G) ≤ normalizer (yamadaW₃ d t : Set G) :=
      inf_le_left.trans hPW₃
    have hA₂'W : (yamadaP d t ⊓ Λ₂ᵍ[t] : Subgroup G) ≤ normalizer (yamadaW₃ d t : Set G) :=
      inf_le_left.trans hPW₃
    obtain ⟨-, -, hPeq₂, -, -⟩ := sylow_prod hsyl₂ hS₂.sup_eq hS₂.inf_eq hS₂.comm_le hM₆P
    have h1 : yamadaM₆ d t ≤ centerMod (yamadaW₃ d t) (yamadaP d t ⊓ Λ₂) := by
      rw [hP₂, hEeq]
    have h2 : yamadaM₆ d t ≤ centerMod (yamadaW₃ d t) (yamadaP d t ⊓ Λ₂ᵍ[t]) := by
      have e1 : (yamadaP d t ⊓ Λ₂)ᵍ[t] = yamadaP d t ⊓ Λ₂ᵍ[t] := by rw [conj_inf, hPt]
      have : centerMod (yamadaW₃ d t) (yamadaP d t ⊓ Λ₂ᵍ[t]) =
          (centerMod (yamadaW₃ d t) (yamadaP d t ⊓ Λ₂))ᵍ[t] := by
        rw [← e1]
        exact ProductN1Aux.centerMod_conj htW₃ hW₃A
      rw [this, hP₂, hEeq, hM₆t]
    have h3 : yamadaM₆ d t ≤ centerMod (yamadaW₃ d t) (yamadaP d t) := by
      intro z hz
      have := ProductN1Aux.mem_centerMod_sup hW₃A hW₃A' hA₂W hA₂'W (h1 hz) (h2 hz)
      rwa [← hPeq₂] at this
    exact hM₆F₅ (hcF ▸ h3)
  rcases hS₁.invariant hsyl₁ hDP hDW hWP hinv with h1 | h1 | h1 | h1
  · exact absurd h1 hWD
  · refine ⟨Λ₀ᵍ[t], Λ₂, ⟨ProductN1Aux.isFactor_conj hΛ₀ ht2 hK4, hΛ₂, ?_⟩⟩
    rw [conj_inf, hPt, conj_conj_of_mul_self ht2]
    exact h1.symm
  · refine ⟨Λ₀, Λ₂, ⟨hΛ₀, hΛ₂, ?_⟩⟩
    rw [conj_inf, hPt]
    exact h1.symm
  · exact absurd h1 hWP'

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
