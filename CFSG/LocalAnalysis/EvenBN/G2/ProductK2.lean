module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductLifts
public import CFSG.LocalAnalysis.EvenBN.G2.ProductN3
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
  (centerMod centralizerMod IsQuotientIso zc mem_centerMod_iff)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1Aux
  (commutator_commutator_eq_bot_of_central)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductK2Aux

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_comm_self {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) :=
  CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator
    hg

theorem commutator_le_inf_of_normalizes {N A B : Subgroup G} (hAN : A ≤ N) (hBN : B ≤ N)
    (hA : N ≤ normalizer (A : Set G)) (hB : N ≤ normalizer (B : Set G)) : ⁅A, B⁆ ≤ A ⊓ B := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  refine mem_inf.2 ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hA (hBN hb)) a⁻¹).1 (inv_mem ha)
    have := mul_mem ha h1
    simpa [mul_assoc] using this
  · have h1 : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (hB (hAN ha)) b).1 hb
    exact mul_mem h1 (inv_mem hb)

theorem conj_eq_map_conj {s : G} (hs : s * s = 1) (A : Subgroup G) :
    Aᵍ[s] = A.map (MulAut.conj s).toMonoidHom := by
  have : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  show A.map (MulEquiv.toMonoidHom (MulAut.conj s⁻¹)) = _
  rw [this]

theorem le_normalizer_sup_of_conj_mem {K A Y : Subgroup G} (hY : K ≤ normalizer (Y : Set G))
    (hA : ∀ g ∈ K, ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ Y) :
    K ≤ normalizer ((A ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ g ∈ K, ∀ x ∈ A ⊔ Y, g * x * g⁻¹ ∈ A ⊔ Y := by
    intro g hg x hx
    have hle : A ⊔ Y ≤ (A ⊔ Y).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun y hy => ?_)
      · exact hA g hg a ha
      · exact mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hY hg) y).1 hy)
    exact hle hx
  intro g hg
  exact SL2Aux.mem_normalizer_of_conj_mem (key g hg) (fun x hx => by
    have := key g⁻¹ (inv_mem hg) x hx
    simpa using this)

theorem inf_le_of_complement {X₁ P A₁ B₁ D C Y : Subgroup G}
    (hX₁ : (P ⊓ A₁) ⊔ B₁ = X₁) (hn : A₁ ≤ normalizer (B₁ : Set G)) (hB₁D : B₁ ≤ D)
    (hYD : Y ≤ D) (hAC : A₁ ≤ C) (hCD : C ⊓ D = ⊥) : X₁ ⊓ Y ≤ B₁ := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hx' : x ∈ B₁ ⊔ (P ⊓ A₁) := by
    rw [sup_comm, hX₁]
    exact hx1
  obtain ⟨b, hb, τ, hτ, rfl⟩ := SL2Aux.exists_mul_of_mem_sup
    (fun g hg => hn (mem_inf.1 hg).2) hx'
  have hτD : τ ∈ D := by
    have := mul_mem (inv_mem (hB₁D hb)) (hYD hx2)
    simpa using this
  have hτ1 : τ = 1 := by
    have : τ ∈ C ⊓ D := mem_inf.2 ⟨hAC (mem_inf.1 hτ).2, hτD⟩
    rwa [hCD, Subgroup.mem_bot] at this
  rw [hτ1, mul_one]
  exact hb

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem le_centralizer_comm {N U : Subgroup G} (hU : U ≤ centralizer (N : Set G)) :
    N ≤ centralizer (U : Set G) := by
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.2 hU

theorem commutator_conj_eq_bot {t : G} (ht : t * t = 1)
    {K U N : Subgroup G} (hsup : K ⊔ Kᵍ[t] = N) (hU : U ≤ centralizer (N : Set G))
    (hUt : Uᵍ[t] = U) (hcomm : ⁅K, Kᵍ[t]⁆ ≤ U) (hperf : ⁅K, K⁆ ⊔ U = K) :
    ⁅K, Kᵍ[t]⁆ = ⊥ := by
  have hKN : K ≤ N := hsup ▸ le_sup_left
  have hKtN : Kᵍ[t] ≤ N := hsup ▸ le_sup_right
  have h1 := commutator_commutator_eq_bot_of_central hKN hKtN hcomm hU
  have hKt : Kᵍ[t] = ⁅Kᵍ[t], Kᵍ[t]⁆ ⊔ U := by
    conv_lhs => rw [← hperf]
    rw [conj_sup, conj_commutator, hUt]
  rw [commutator_eq_bot_iff_le_centralizer]
  conv_lhs => rw [← hperf]
  refine sup_le ?_ ?_
  · rw [hKt, Common.centralizer_sup_eq]
    exact le_inf (commutator_eq_bot_iff_le_centralizer.1 h1)
      ((commutator_self_le K).trans (hKN.trans (le_centralizer_comm hU)))
  · exact hU.trans (centralizer_le hKtN)

theorem zc_conj {t : G} (ht : t * t = 1) (S : Subgroup G) : zc (Sᵍ[t]) = (zc S)ᵍ[t] := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext x
  simp only [zc, mem_inf, mem_conj_iff_of_mul_self ht, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have e1 : t⁻¹ * (t * y * t⁻¹) * t = y := by group
    have h2 := hc (t * y * t⁻¹) (by rw [e1]; exact hy)
    calc y * (t⁻¹ * x * t) = t⁻¹ * ((t * y * t⁻¹) * x) * t := by group
      _ = t⁻¹ * (x * (t * y * t⁻¹)) * t := by rw [h2]
      _ = (t⁻¹ * x * t) * y := by group
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h2 := hc (t⁻¹ * y * t) hy
    calc y * x = t * ((t⁻¹ * y * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * x * t) * (t⁻¹ * y * t)) * t⁻¹ := by rw [h2]
      _ = x * y := by group

theorem centerMod_conj {t : G} (ht : t * t = 1) {U A : Subgroup G} (hUt : Uᵍ[t] = U)
    (hUA : U ≤ A) : centerMod U (Aᵍ[t]) = (centerMod U A)ᵍ[t] := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htN : t ∈ normalizer (U : Set G) := mem_normalizer_of_conj_eq hUt
  have htiN : t⁻¹ ∈ normalizer (U : Set G) := inv_mem htN
  have hUAt : U ≤ Aᵍ[t] := hUt ▸ conj_mono hUA t
  have hUmem : ∀ w : G, t⁻¹ * w * t ∈ U ↔ w ∈ U := fun w =>
    (mem_normalizer_iff''.1 htN w).symm
  have hUmem' : ∀ w : G, t * w * t⁻¹ ∈ U ↔ w ∈ U := fun w => by
    rw [← hUmem (t * w * t⁻¹)]
    have e : t⁻¹ * (t * w * t⁻¹) * t = w := by group
    rw [e]
  have hNx : ∀ x : G, x ∈ normalizer (U : Set G) ↔ t⁻¹ * x * t ∈ normalizer (U : Set G) :=
    fun x => ⟨fun hx => mul_mem (mul_mem htiN hx) htN, fun hx => by
      have := mul_mem (mul_mem htN hx) htiN
      have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [e] at this⟩
  have hmemA : ∀ y : G, y ∈ Aᵍ[t] ↔ t⁻¹ * y * t ∈ A := fun y => mem_conj_iff_of_mul_self ht
  ext x
  rw [mem_centerMod_iff hUAt, mem_conj_iff_of_mul_self ht (A := centerMod U A),
    mem_centerMod_iff hUA]
  constructor
  · rintro ⟨hxA, hxN, hc⟩
    refine ⟨(hmemA x).1 hxA, (hNx x).1 hxN, fun a ha haN => ?_⟩
    have ha' : t * a * t⁻¹ ∈ Aᵍ[t] := by
      rw [hmemA]
      have e : t⁻¹ * (t * a * t⁻¹) * t = a := by group
      rwa [e]
    have haN' : t * a * t⁻¹ ∈ normalizer (U : Set G) := mul_mem (mul_mem htN haN) htiN
    have h2 := hc _ ha' haN'
    rw [← hUmem] at h2
    have e : t⁻¹ * (x * (t * a * t⁻¹) * x⁻¹ * (t * a * t⁻¹)⁻¹) * t =
        (t⁻¹ * x * t) * a * (t⁻¹ * x * t)⁻¹ * a⁻¹ := by group
    rwa [e] at h2
  · rintro ⟨hxA, hxN, hc⟩
    refine ⟨(hmemA x).2 hxA, (hNx x).2 hxN, fun a ha haN => ?_⟩
    rw [hmemA] at ha
    have haN' : t⁻¹ * a * t ∈ normalizer (U : Set G) := (hNx a).1 haN
    have h2 := hc _ ha haN'
    rw [← hUmem'] at h2
    have e : t * ((t⁻¹ * x * t) * (t⁻¹ * a * t) * (t⁻¹ * x * t)⁻¹ * (t⁻¹ * a * t)⁻¹) * t⁻¹ =
        x * a * x⁻¹ * a⁻¹ := by group
    rwa [e] at h2

theorem comm_mul_left (x y p : G) :
    (x * y) * p * (x * y)⁻¹ * p⁻¹ =
      (x * (y * p * y⁻¹ * p⁻¹) * x⁻¹) * (x * p * x⁻¹ * p⁻¹) := by group

theorem comm_mul_right (x p q : G) :
    x * (p * q) * x⁻¹ * (p * q)⁻¹ =
      (x * p * x⁻¹ * p⁻¹) * (p * (x * q * x⁻¹ * q⁻¹) * p⁻¹) := by group

theorem conj_eq_of_mem_centralizer {N U : Subgroup G} (hU : U ≤ centralizer (N : Set G)) {x u : G}
    (hx : x ∈ N) (hu : u ∈ U) : x * u * x⁻¹ = u := by
  have := mem_centralizer_iff.1 (hU hu) x hx
  rw [this]
  group

theorem comm_mem_of_mul_mem {N U : Subgroup G} (hU : U ≤ centralizer (N : Set G)) {x y p : G}
    (hx : x ∈ N) (h1 : (x * y) * p * (x * y)⁻¹ * p⁻¹ ∈ U) (h2 : y * p * y⁻¹ * p⁻¹ ∈ U) :
    x * p * x⁻¹ * p⁻¹ ∈ U := by
  rw [comm_mul_left, conj_eq_of_mem_centralizer hU hx h2] at h1
  have h3 := mul_mem (inv_mem h2) h1
  rwa [inv_mul_cancel_left] at h3

theorem comm_mem_of_mul_mem' {N U : Subgroup G} (hU : U ≤ centralizer (N : Set G)) {x y p : G}
    (hx : x ∈ N) (h1 : (x * y) * p * (x * y)⁻¹ * p⁻¹ ∈ U) (h2 : x * p * x⁻¹ * p⁻¹ ∈ U) :
    y * p * y⁻¹ * p⁻¹ ∈ U := by
  rw [comm_mul_left] at h1
  have h3 := mul_mem h1 (inv_mem h2)
  have e : x * (y * p * y⁻¹ * p⁻¹) * x⁻¹ * (x * p * x⁻¹ * p⁻¹) * (x * p * x⁻¹ * p⁻¹)⁻¹ =
      x * (y * p * y⁻¹ * p⁻¹) * x⁻¹ := by group
  rw [e] at h3
  have hxi : x⁻¹ ∈ N := inv_mem hx
  have h5 := conj_eq_of_mem_centralizer hU hxi h3
  have e2 : x⁻¹ * (x * (y * p * y⁻¹ * p⁻¹) * x⁻¹) * x⁻¹⁻¹ = y * p * y⁻¹ * p⁻¹ := by group
  rw [e2] at h5
  rw [h5]
  exact h3

theorem comm_mem_mul_right {N U : Subgroup G} (hU : U ≤ centralizer (N : Set G)) {a p₁ p₂ : G}
    (hp₁ : p₁ ∈ N) (h1 : a * p₁ * a⁻¹ * p₁⁻¹ ∈ U) (h2 : a * p₂ * a⁻¹ * p₂⁻¹ ∈ U) :
    a * (p₁ * p₂) * a⁻¹ * (p₁ * p₂)⁻¹ ∈ U := by
  rw [comm_mul_right, conj_eq_of_mem_centralizer hU hp₁ h2]
  exact mul_mem h1 h2

theorem le_normalizer_of_commutator_le {A B C : Subgroup G} (hC : C ≤ A) (h : ⁅A, B⁆ ≤ C) :
    B ≤ normalizer (A : Set G) := by
  refine le_normalizer_of_commutator_mem fun b hb a ha => ?_
  have h1 : ⁅a, b⁆ ∈ C := h (commutator_mem_commutator ha hb)
  have h2 : b * a * b⁻¹ * a⁻¹ = (⁅a, b⁆)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact hC (inv_mem h1)

structure N1Data (t : G) (U Y D P N Λ : Subgroup G) : Prop where
  ht : t * t = 1
  hUt : Uᵍ[t] = U
  hYt : Yᵍ[t] = Y
  hUN : U ≤ centralizer (N : Set G)
  hUD : U ≤ D
  hΛN : Λ ≤ N
  hΛtN : Λᵍ[t] ≤ N
  hPN : P ≤ N
  hDP : D ≤ P
  hDΛ : D ≤ Λ
  hDΛt : D ≤ Λᵍ[t]
  hDD : ⁅D, D⁆ ≤ U
  hND : N ≤ normalizer (D : Set G)
  hDV : D = centerMod U Λ ⊔ centerMod U (Λᵍ[t])
  hVVt : centerMod U Λ ⊓ centerMod U (Λᵍ[t]) = U
  hPeq : P = (P ⊓ Λ) ⊔ (P ⊓ Λᵍ[t])
  hPcomm : ⁅P ⊓ Λ, P ⊓ Λᵍ[t]⁆ ≤ D
  hYD : Y ≤ D
  hYcen : centerMod U P = Y

namespace N1Data

variable {t : G} {U Y D P N Λ : Subgroup G} (S : N1Data t U Y D P N Λ)
include S

theorem hUΛ : U ≤ Λ := S.hUD.trans S.hDΛ

theorem hUΛt : U ≤ Λᵍ[t] := S.hUD.trans S.hDΛt

theorem hUP : U ≤ P := S.hUD.trans S.hDP

theorem hVt_eq : centerMod U (Λᵍ[t]) = (centerMod U Λ)ᵍ[t] :=
  centerMod_conj S.ht S.hUt S.hUΛ

theorem hV_eq : centerMod U Λ = (centerMod U (Λᵍ[t]))ᵍ[t] := by
  rw [S.hVt_eq, conj_conj_of_mul_self S.ht]

theorem hNU : N ≤ normalizer (U : Set G) :=
  fun _ hx => Subgroup.centralizer_le_normalizer _ (le_centralizer_comm S.hUN hx)

theorem hVt_le : centerMod U (Λᵍ[t]) ≤ D := by
  rw [S.hDV]
  exact le_sup_right

theorem hV_le : centerMod U Λ ≤ D := by
  rw [S.hDV]
  exact le_sup_left

theorem le_of_inf_eq (hX : centerMod U (Λᵍ[t]) ⊓ Y = U) : Y ≤ U := by
  intro y hy
  have hU : U ≤ centralizer (N : Set G) := S.hUN
  have hUP : U ≤ P := S.hUP
  have hyD : y ∈ D := S.hYD hy
  have hyD' : y ∈ centerMod U (Λᵍ[t]) ⊔ centerMod U Λ := by
    rw [sup_comm, ← S.hDV]
    exact hyD
  have hVn : centerMod U Λ ≤ normalizer ((centerMod U (Λᵍ[t]) : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun v hv a ha => ?_
    have h1 : v * a * v⁻¹ * a⁻¹ ∈ U := S.hDD (commutator_mem_commutator (S.hV_le hv) (S.hVt_le ha))
    exact le_upperCenterMod S.hUΛt 1 h1
  obtain ⟨a, ha, b, hb, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hVn hyD'
  have haD : a ∈ D := S.hVt_le ha
  have hbD : b ∈ D := S.hV_le hb
  have haN : a ∈ N := S.hΛN (S.hDΛ haD)
  have hbN : b ∈ N := S.hΛN (S.hDΛ hbD)
  have hyCM : a * b ∈ centerMod U P := S.hYcen ▸ hy
  have hyc := ((mem_centerMod_iff hUP).1 hyCM).2.2
  have hac := ((mem_centerMod_iff S.hUΛt).1 ha).2.2
  have hbc := ((mem_centerMod_iff S.hUΛ).1 hb).2.2
  have hPn : P ⊓ Λᵍ[t] ≤ normalizer ((P ⊓ Λ : Subgroup G) : Set G) :=
    le_normalizer_of_commutator_le (le_inf S.hDP S.hDΛ) S.hPcomm
  have hdecomp : ∀ p ∈ P, ∃ p₁ ∈ P ⊓ Λ, ∃ p₂ ∈ P ⊓ Λᵍ[t], p = p₁ * p₂ := fun p hp => by
    have hp' : p ∈ (P ⊓ Λ) ⊔ (P ⊓ Λᵍ[t]) := S.hPeq ▸ hp
    exact SL2Aux.exists_mul_of_mem_sup hPn hp'
  have hPN' : ∀ p ∈ P, p ∈ N := fun p hp => S.hPN hp
  have hnU : ∀ p ∈ N, p ∈ normalizer (U : Set G) := fun p hp => S.hNU hp
  have haP : a ∈ centerMod U P := by
    rw [mem_centerMod_iff hUP]
    refine ⟨S.hDP haD, hnU a haN, fun p hp _ => ?_⟩
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hdecomp p hp
    refine comm_mem_mul_right hU (hPN' _ hp₁.1) ?_ ?_
    · refine comm_mem_of_mul_mem hU haN (hyc p₁ hp₁.1 (hnU _ (hPN' _ hp₁.1))) ?_
      exact hbc p₁ hp₁.2 (hnU _ (hPN' _ hp₁.1))
    · exact hac p₂ hp₂.2 (hnU _ (hPN' _ hp₂.1))
  have hbP : b ∈ centerMod U P := by
    rw [mem_centerMod_iff hUP]
    refine ⟨S.hDP hbD, hnU b hbN, fun p hp _ => ?_⟩
    obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hdecomp p hp
    refine comm_mem_mul_right hU (hPN' _ hp₁.1) ?_ ?_
    · exact hbc p₁ hp₁.2 (hnU _ (hPN' _ hp₁.1))
    · refine comm_mem_of_mul_mem' hU haN (hyc p₂ hp₂.1 (hnU _ (hPN' _ hp₂.1))) ?_
      exact hac p₂ hp₂.2 (hnU _ (hPN' _ hp₂.1))
  have haU : a ∈ U := by
    rw [← hX]
    exact ⟨ha, S.hYcen ▸ haP⟩
  have hbU : b ∈ U := by
    have h1 : b ∈ (centerMod U (Λᵍ[t]) ⊓ Y)ᵍ[t] := by
      rw [conj_inf, S.hYt, ← S.hV_eq]
      exact ⟨hb, S.hYcen ▸ hbP⟩
    rwa [hX, S.hUt] at h1
  exact mul_mem haU hbU

theorem le_of_le_Vt (hY : Y ≤ centerMod U (Λᵍ[t])) : Y ≤ U := by
  have h1 : Yᵍ[t] ≤ (centerMod U (Λᵍ[t]))ᵍ[t] := conj_mono hY t
  rw [S.hYt, ← S.hV_eq] at h1
  rw [← S.hVVt]
  exact le_inf h1 hY

theorem inf_le_sup_of_le_sup {A : Subgroup G} (hAD : A ≤ normalizer (D : Set G))
    (hΛ : Λ ≤ A ⊔ D) {x : G} (hxP : x ∈ P) (hxΛ : x ∈ Λ) :
    ∃ d ∈ D, ∃ a ∈ P ⊓ A, x = d * a := by
  have hx : x ∈ D ⊔ A := by
    rw [sup_comm]
    exact hΛ hxΛ
  obtain ⟨d, hd, a, ha, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hAD hx
  refine ⟨d, hd, a, ⟨?_, ha⟩, rfl⟩
  have := mul_mem (inv_mem (S.hDP hd)) hxP
  simpa using this

theorem mem_U_of_centralizes {A K1 : Subgroup G} (hAK : A ≤ K1) (hAΛ : A ≤ Λ) (hΛ : Λ ≤ A ⊔ D)
    (hVtK : centerMod U (Λᵍ[t]) ≤ K1) (hK : ⁅K1, K1ᵍ[t]⁆ = ⊥)
    (hZP : ∀ z ∈ P, (∀ p ∈ P, z * p = p * z) → z ∈ U)
    {z : G} (hzP : z ∈ P) (hzK : z ∈ K1)
    (hz : ∀ x ∈ (P ⊓ A) ⊔ centerMod U (Λᵍ[t]), z * x = x * z) : z ∈ U := by
  apply hZP z hzP
  have hKc : ∀ x ∈ K1ᵍ[t], z * x = x * z := fun x hx =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hK hzK) x hx).symm
  have hDt : Dᵍ[t] = D := by
    rw [S.hDV, conj_sup, ← S.hVt_eq, ← S.hV_eq, sup_comm]
  have hVK : centerMod U Λ ≤ K1ᵍ[t] := by
    rw [S.hV_eq]
    exact conj_mono hVtK t
  have hDz : ∀ d ∈ D, z * d = d * z := by
    intro d hd
    rw [S.hDV] at hd
    have hle : centerMod U Λ ⊔ centerMod U (Λᵍ[t]) ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact mem_centralizer_singleton_iff.2 (hKc x (hVK hx)).symm
      · exact mem_centralizer_singleton_iff.2 (hz x (mem_sup_right hx)).symm
    exact (mem_centralizer_singleton_iff.1 (hle hd)).symm
  have hP₁ : ∀ x ∈ P ⊓ Λ, z * x = x * z := by
    intro x hx
    obtain ⟨d, hd, a, ha, rfl⟩ := S.inf_le_sup_of_le_sup (A := A)
      ((hAΛ.trans S.hΛN).trans S.hND) hΛ hx.1 hx.2
    have h1 : z * a = a * z := hz a (mem_sup_left ha)
    calc z * (d * a) = (z * d) * a := by rw [mul_assoc]
      _ = (d * z) * a := by rw [hDz d hd]
      _ = d * (z * a) := by rw [mul_assoc]
      _ = d * (a * z) := by rw [h1]
      _ = d * a * z := by rw [mul_assoc]
  have hP₂ : ∀ x ∈ P ⊓ Λᵍ[t], z * x = x * z := by
    intro x hx
    have hΛt : Λᵍ[t] ≤ Aᵍ[t] ⊔ D := by
      have := conj_mono hΛ t
      rwa [conj_sup, hDt] at this
    have hAtN : Aᵍ[t] ≤ normalizer (D : Set G) :=
      (conj_mono hAΛ t).trans (S.hΛtN.trans S.hND)
    have hx' : x ∈ D ⊔ Aᵍ[t] := by
      rw [sup_comm]
      exact hΛt hx.2
    obtain ⟨d, hd, a, ha, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hAtN hx'
    have h1 : z * a = a * z := hKc a (conj_mono hAK t ha)
    calc z * (d * a) = (z * d) * a := by rw [mul_assoc]
      _ = (d * z) * a := by rw [hDz d hd]
      _ = d * (z * a) := by rw [mul_assoc]
      _ = d * (a * z) := by rw [h1]
      _ = d * a * z := by rw [mul_assoc]
  intro p hp
  have hp' : p ∈ (P ⊓ Λ) ⊔ (P ⊓ Λᵍ[t]) := S.hPeq ▸ hp
  have hle : (P ⊓ Λ) ⊔ (P ⊓ Λᵍ[t]) ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact mem_centralizer_singleton_iff.2 (hP₁ x hx).symm
    · exact mem_centralizer_singleton_iff.2 (hP₂ x hx).symm
  exact (mem_centralizer_singleton_iff.1 (hle hp')).symm

end N1Data

end Generic

section PartII

variable {G : Type*} [Group G]

theorem Z_le_and_inf_le {s : G} {Y Z Z' U B₁ B₁t X₁ : Subgroup G}
    (hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hZY : Z ≤ Y) (hZ'Y : Z' ≤ Y) (hZZ' : Z ⊓ Z' = ⊥)
    (hYZ : ∀ y ∈ Y, ∃ z ∈ Z, ∃ z' ∈ Z', y = z * z') (hUY : U ≤ Y)
    (hX : B₁ ⊓ Y = Z ⊔ U) (hXt : B₁t ⊓ Y = Z' ⊔ U) (hBB : B₁ ⊓ B₁t ≤ U)
    (hX₁ : X₁ ⊓ Y ≤ B₁) (hB₁X₁ : B₁ ≤ X₁)
    (hYs : Yᵍ[s] = Y) (hZs : Zᵍ[s] = Z) (hZ's : Z'ᵍ[s] = Z') (hUUs : U ⊓ Uᵍ[s] = ⊥) :
    Z ≤ X₁ ⊓ X₁ᵍ[s] ∧ X₁ ⊓ X₁ᵍ[s] ⊓ Y ≤ Z := by
  have hZX : Z ≤ B₁ ⊓ Y := hX ▸ le_sup_left
  have hZ'Xt : Z' ≤ B₁t ⊓ Y := hXt ▸ le_sup_left
  have hUX : U ≤ B₁ ⊓ Y := hX ▸ le_sup_right
  have hUXt : U ≤ B₁t ⊓ Y := hXt ▸ le_sup_right
  refine ⟨le_inf (hZX.trans (inf_le_left.trans hB₁X₁)) ?_, ?_⟩
  · have := conj_mono (hZX.trans (inf_le_left.trans hB₁X₁)) s
    rwa [hZs] at this
  have hsplit : ∀ u ∈ U, ∃ a ∈ Z ⊓ U, ∃ a' ∈ Z' ⊓ U, u = a * a' := by
    intro u hu
    obtain ⟨z, hz, z', hz', rfl⟩ := hYZ u (hUY hu)
    have hz'1 : z' ∈ B₁ ⊓ Y := by
      have := mul_mem (inv_mem (hZX hz)) (hUX hu)
      simpa using this
    have hz1 : z ∈ B₁t ⊓ Y := by
      have := mul_mem (hUXt hu) (inv_mem (hZ'Xt hz'))
      simpa using this
    exact ⟨z, ⟨hz, hBB ⟨(hZX hz).1, hz1.1⟩⟩, z', ⟨hz', hBB ⟨hz'1.1, (hZ'Xt hz').1⟩⟩, rfl⟩
  intro y hy
  obtain ⟨⟨hy1, hy2⟩, hyY⟩ := hy
  have hyB : y ∈ B₁ ⊓ Y := ⟨hX₁ ⟨hy1, hyY⟩, hyY⟩
  have hysY : s * y * s⁻¹ ∈ Y := by
    have : y ∈ Yᵍ[s] := by rw [hYs]; exact hyY
    exact mem_conj_iff.1 this
  have hysB : s * y * s⁻¹ ∈ B₁ ⊓ Y := ⟨hX₁ ⟨mem_conj_iff.1 hy2, hysY⟩, hysY⟩
  rw [hX] at hyB hysB
  have hcomm1 : ∀ a ∈ Z, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hYab a (hZY ha) b (hUY hb)
  obtain ⟨z₁, hz₁, u₁, hu₁, rfl⟩ := (UCSAux.mem_sup_iff_of_commute hcomm1).1 hyB
  obtain ⟨z₂, hz₂, u₂, hu₂, he₂⟩ := (UCSAux.mem_sup_iff_of_commute hcomm1).1 hysB
  obtain ⟨a, ha, a', ha', rfl⟩ := hsplit u₁ hu₁
  obtain ⟨b, hb, b', hb', rfl⟩ := hsplit u₂ hu₂
  set c : G := s⁻¹ * z₂ * s with hc
  set e : G := s⁻¹ * b * s with he
  set e' : G := s⁻¹ * b' * s with he'
  have hcZ : c ∈ Z := by
    have : c ∈ Zᵍ[s] := by
      rw [mem_conj_iff]
      have : s * c * s⁻¹ = z₂ := by rw [hc]; group
      rw [this]; exact hz₂
    rwa [hZs] at this
  have heZ : e ∈ Z := by
    have : e ∈ Zᵍ[s] := by
      rw [mem_conj_iff]
      have : s * e * s⁻¹ = b := by rw [he]; group
      rw [this]; exact (mem_inf.1 hb).1
    rwa [hZs] at this
  have he'Z' : e' ∈ Z' := by
    have : e' ∈ Z'ᵍ[s] := by
      rw [mem_conj_iff]
      have : s * e' * s⁻¹ = b' := by rw [he']; group
      rw [this]; exact (mem_inf.1 hb').1
    rwa [hZ's] at this
  have he'U : e' ∈ Uᵍ[s] := by
    rw [mem_conj_iff]
    have : s * e' * s⁻¹ = b' := by rw [he']; group
    rw [this]; exact (mem_inf.1 hb').2
  have hy_eq : z₁ * (a * a') = (c * e) * e' := by
    have h1 : z₁ * (a * a') = s⁻¹ * (z₂ * (b * b')) * s := by
      rw [← he₂]
      group
    rw [h1, hc, he, he']
    group
  have hpZ : z₁ * a ∈ Z := mul_mem hz₁ (mem_inf.1 ha).1
  have hqZ : c * e ∈ Z := mul_mem hcZ heZ
  have hcomm2 : ∀ x ∈ Z, ∀ w ∈ Z', x * w = w * x := fun x hx w hw => hYab x (hZY hx) w (hZ'Y hw)
  have hkey : a' = e' := by
    have h1 : (c * e)⁻¹ * (z₁ * a) = e' * a'⁻¹ := by
      have h2 : (z₁ * a) * a' = (c * e) * e' := by rw [← hy_eq]; group
      calc (c * e)⁻¹ * (z₁ * a) = (c * e)⁻¹ * ((z₁ * a) * a') * a'⁻¹ := by group
        _ = (c * e)⁻¹ * ((c * e) * e') * a'⁻¹ := by rw [h2]
        _ = e' * a'⁻¹ := by group
    have h3 : (c * e)⁻¹ * (z₁ * a) ∈ Z ⊓ Z' := by
      refine mem_inf.2 ⟨mul_mem (inv_mem hqZ) hpZ, ?_⟩
      rw [h1]
      exact mul_mem he'Z' (inv_mem (mem_inf.1 ha').1)
    rw [hZZ', Subgroup.mem_bot] at h3
    have h4 : e' * a'⁻¹ = 1 := by rw [← h1]; exact h3
    have h5 : e' = a' := by
      have := mul_inv_eq_one.1 h4
      exact this
    exact h5.symm
  have ha'1 : a' = 1 := by
    have h1 : a' ∈ U ⊓ Uᵍ[s] := mem_inf.2 ⟨(mem_inf.1 ha').2, hkey ▸ he'U⟩
    rwa [hUUs, Subgroup.mem_bot] at h1
  rw [ha'1, mul_one]
  exact mul_mem hz₁ (mem_inf.1 ha).1

theorem conj_conj_comm {s t : G} (hst : s * t = t * s) (A : Subgroup G) :
    (Aᵍ[s])ᵍ[t] = (Aᵍ[t])ᵍ[s] := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : s⁻¹ * t⁻¹ = t⁻¹ * s⁻¹ := by
    have : (t * s)⁻¹ = (s * t)⁻¹ := by rw [hst]
    simpa using this
  calc t⁻¹ * (s⁻¹ * x * s⁻¹⁻¹) * t⁻¹⁻¹ = (t⁻¹ * s⁻¹) * x * (t⁻¹ * s⁻¹)⁻¹ := by group
    _ = (s⁻¹ * t⁻¹) * x * (s⁻¹ * t⁻¹)⁻¹ := by rw [h1]
    _ = s⁻¹ * (t⁻¹ * x * t⁻¹⁻¹) * s⁻¹⁻¹ := by group

theorem inf_conj_le_B {s : G} {X₁ X₂ P M B A : Subgroup G} (hX₁X₂ : X₁ ≤ X₂)
    (hX₂ : X₂ = (P ⊓ A) ⊔ B) (hBM : B ≤ M) (hMP : M ≤ P) (hPPs : P ⊓ Pᵍ[s] = M)
    (hAM : A ⊓ M = ⊥) (hAB : A ≤ normalizer (B : Set G)) : X₁ ⊓ X₁ᵍ[s] ≤ B := by
  have hX₂P : X₂ ≤ P := by
    rw [hX₂]
    exact sup_le inf_le_left (hBM.trans hMP)
  intro h hh
  obtain ⟨hh1, hh2⟩ := mem_inf.1 hh
  have hhP : h ∈ P := hX₂P (hX₁X₂ hh1)
  have hhPs : h ∈ Pᵍ[s] := conj_mono hX₂P s (conj_mono hX₁X₂ s hh2)
  have hhM : h ∈ M := by
    rw [← hPPs]
    exact mem_inf.2 ⟨hhP, hhPs⟩
  have hh' : h ∈ B ⊔ (P ⊓ A) := by
    rw [sup_comm, ← hX₂]
    exact hX₁X₂ hh1
  obtain ⟨β, hβ, τ, hτ, rfl⟩ := SL2Aux.exists_mul_of_mem_sup
    (fun x hx => hAB (mem_inf.1 hx).2) hh'
  have hτM : τ ∈ M := by
    have := mul_mem (inv_mem (hBM hβ)) hhM
    simpa using this
  have hτ1 : τ = 1 := by
    have : τ ∈ A ⊓ M := mem_inf.2 ⟨(mem_inf.1 hτ).2, hτM⟩
    rwa [hAM, Subgroup.mem_bot] at this
  rw [hτ1, mul_one]
  exact hβ

theorem inf_conj_le_centralizer {s t : G} (hst : s * t = t * s)
    {X₁ K1 K3 : Subgroup G} (hK3 : K3 ≤ X₁ ⊔ X₁ᵍ[s]) (hX₁ : X₁ ≤ K1)
    (hK : ⁅K1, K1ᵍ[t]⁆ = ⊥) : X₁ ⊓ X₁ᵍ[s] ≤ centralizer ((K3ᵍ[t] : Subgroup G) : Set G) := by
  have hHK : X₁ ⊓ X₁ᵍ[s] ≤ K1 := inf_le_left.trans hX₁
  have hHKs : X₁ ⊓ X₁ᵍ[s] ≤ K1ᵍ[s] := inf_le_right.trans (conj_mono hX₁ s)
  have hKt : K1ᵍ[t] ≤ centralizer (K1 : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hK
  have hKs : (K1ᵍ[t])ᵍ[s] ≤ centralizer ((K1ᵍ[s] : Subgroup G) : Set G) := by
    have h1 : ⁅(K1ᵍ[t])ᵍ[s], K1ᵍ[s]⁆ = ⊥ := by
      rw [← conj_commutator, commutator_comm, hK]
      exact Subgroup.map_bot _
    exact commutator_eq_bot_iff_le_centralizer.1 h1
  have hle : K3ᵍ[t] ≤ centralizer ((X₁ ⊓ X₁ᵍ[s] : Subgroup G) : Set G) := by
    have h1 : K3ᵍ[t] ≤ X₁ᵍ[t] ⊔ (X₁ᵍ[s])ᵍ[t] := by
      have := conj_mono hK3 t
      rwa [conj_sup] at this
    refine h1.trans (sup_le ?_ ?_)
    · exact (conj_mono hX₁ t).trans (hKt.trans (centralizer_le hHK))
    · rw [conj_conj_comm hst]
      exact (conj_mono (conj_mono hX₁ t) s).trans (hKs.trans (centralizer_le hHKs))
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm,
    commutator_eq_bot_iff_le_centralizer]
  exact hle

theorem conj_le_normalizer_conj {g : G} {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) :
    Xᵍ[g] ≤ normalizer ((Yᵍ[g] : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_conj_iff] at hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conj_iff, mem_conj_iff]
  have h1 := Subgroup.mem_normalizer_iff.1 (h hx) (g * y * g⁻¹)
  have e : g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem K3_le_sup {s : G} (hs : s * s = 1) {X₁ P K3 P3 A Y B U : Subgroup G}
    (hK3 : K3 = P3 ⊔ P3ᵍ[s]) (hP3 : P3 = P ⊓ K3) (hK3A : K3 ≤ A ⊔ Y)
    (hAY : A ≤ normalizer (Y : Set G)) (hYP : Y ≤ P)
    (hX₂ : X₁ ⊔ Y = (P ⊓ A) ⊔ B) (hYU : Y = U ⊔ Uᵍ[s]) (hUX₁ : U ≤ X₁) :
    K3 ≤ X₁ ⊔ X₁ᵍ[s] := by
  have hYV : Y ≤ X₁ ⊔ X₁ᵍ[s] := by
    rw [hYU]
    exact sup_le (hUX₁.trans le_sup_left) ((conj_mono hUX₁ s).trans le_sup_right)
  have hX₂V : X₁ ⊔ Y ≤ X₁ ⊔ X₁ᵍ[s] := sup_le le_sup_left hYV
  have hP3V : P3 ≤ X₁ ⊔ X₁ᵍ[s] := by
    intro x hx
    rw [hP3] at hx
    obtain ⟨hxP, hxK⟩ := mem_inf.1 hx
    have hx' : x ∈ Y ⊔ A := by
      rw [sup_comm]
      exact hK3A hxK
    obtain ⟨y, hy, a, ha, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hAY hx'
    have haP : a ∈ P := by
      have := mul_mem (inv_mem (hYP hy)) hxP
      simpa using this
    have haV : a ∈ X₁ ⊔ X₁ᵍ[s] := by
      apply hX₂V
      rw [hX₂]
      exact mem_sup_left (mem_inf.2 ⟨haP, ha⟩)
    exact mul_mem (hYV hy) haV
  have hP3sV : P3ᵍ[s] ≤ X₁ ⊔ X₁ᵍ[s] := by
    have := conj_mono hP3V s
    rw [conj_sup, conj_conj_of_mul_self hs, sup_comm] at this
    exact this
  rw [hK3]
  exact sup_le hP3V hP3sV

theorem B_le_mul {s : G} (hs : s * s = 1) {X₁ P M B Y U B₁ A : Subgroup G}
    (hX₂ : X₁ ⊔ Y = (P ⊓ A) ⊔ B) (hBM : B ≤ M) (hMP : M ≤ P) (hYB : Y ≤ B)
    (hYM : ∀ y ∈ Y, ∀ m ∈ M, y * m = m * y) (hPY : P ≤ normalizer (Y : Set G))
    (hBs : Bᵍ[s] = B) (hYs : Yᵍ[s] = Y) (hYU : Y = U ⊔ Uᵍ[s]) (hUB₁ : U ≤ B₁)
    (hB₁X₁ : B₁ ≤ X₁) (hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) (hHB : X₁ ⊓ X₁ᵍ[s] ≤ B)
    (hUY : U ≤ Y) :
    ∀ b ∈ B, ∃ h ∈ X₁ ⊓ X₁ᵍ[s], ∃ y ∈ Y, b = h * y := by
  have hX₂P : (P ⊓ A) ⊔ B ≤ P := sup_le inf_le_left (hBM.trans hMP)
  have hX₁P : X₁ ≤ P := le_sup_left.trans (hX₂ ▸ hX₂P)
  have hX₁N : X₁ ≤ normalizer (Y : Set G) := hX₁P.trans hPY
  have hX₁sN : X₁ᵍ[s] ≤ normalizer (Y : Set G) := by
    have := conj_le_normalizer_conj (g := s) hX₁N
    rwa [hYs] at this
  set X : Subgroup G := B₁ ⊓ Y with hXdef
  have hXY : X ≤ Y := inf_le_right
  have hXC : X ≤ X₁ ⊓ B := le_inf (inf_le_left.trans hB₁X₁) (inf_le_right.trans hYB)
  have hXsC : Xᵍ[s] ≤ X₁ᵍ[s] ⊓ B := by
    refine le_inf (conj_mono (inf_le_left.trans hB₁X₁) s) ?_
    have := conj_mono (hXY.trans hYB) s
    rwa [hBs] at this
  have hXsY : Xᵍ[s] ≤ Y := by
    have := conj_mono hXY s
    rwa [hYs] at this
  have hUX : U ≤ X := le_inf hUB₁ hUY
  have hYX : ∀ y ∈ Y, ∃ x₁ ∈ X, ∃ x₂ ∈ Xᵍ[s], y = x₁ * x₂ := by
    intro y hy
    have hy' : y ∈ X ⊔ Xᵍ[s] := by
      rw [hYU] at hy
      exact (sup_le_sup hUX (conj_mono hUX s)) hy
    exact (UCSAux.mem_sup_iff_of_commute fun a ha b hb => hYab a (hXY ha) b (hXsY hb)).1 hy'
  have hBX : B ≤ X₁ ⊔ Y := by
    rw [hX₂]
    exact le_sup_right
  have hBXs : B ≤ X₁ᵍ[s] ⊔ Y := by
    have := conj_mono hBX s
    rwa [conj_sup, hBs, hYs] at this
  have hC : ∀ c ∈ X₁ ⊓ B, ∃ h ∈ X₁ ⊓ X₁ᵍ[s], ∃ x₁ ∈ X, c = h * x₁ := by
    intro c hc
    obtain ⟨hcX, hcB⟩ := mem_inf.1 hc
    have hc' : c ∈ Y ⊔ X₁ᵍ[s] := by
      rw [sup_comm]
      exact hBXs hcB
    obtain ⟨y₁, hy₁, c₁, hc₁, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hX₁sN hc'
    have hc₁B : c₁ ∈ B := by
      have := mul_mem (inv_mem (hYB hy₁)) hcB
      simpa using this
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hYX y₁ hy₁
    have hx₂C := hXsC hx₂
    have hhC : x₂ * c₁ ∈ X₁ᵍ[s] ⊓ B :=
      mem_inf.2 ⟨mul_mem (mem_inf.1 hx₂C).1 hc₁, mul_mem (mem_inf.1 hx₂C).2 hc₁B⟩
    have hx₁Y : x₁ ∈ Y := hXY hx₁
    have hcomm : x₁ * (x₂ * c₁) = (x₂ * c₁) * x₁ :=
      hYM x₁ hx₁Y _ (hBM (mem_inf.1 hhC).2)
    have hx₁X₁ : x₁ ∈ X₁ := (hXC hx₁).1
    refine ⟨x₂ * c₁, mem_inf.2 ⟨?_, (mem_inf.1 hhC).1⟩, x₁, hx₁, ?_⟩
    · have h1 : (x₂ * c₁) = (x₁ * x₂ * c₁) * x₁⁻¹ := by
        calc x₂ * c₁ = (x₂ * c₁) * x₁ * x₁⁻¹ := by group
          _ = (x₁ * (x₂ * c₁)) * x₁⁻¹ := by rw [hcomm]
          _ = (x₁ * x₂ * c₁) * x₁⁻¹ := by group
      rw [h1]
      exact mul_mem hcX (inv_mem hx₁X₁)
    · calc x₁ * x₂ * c₁ = x₁ * (x₂ * c₁) := by group
        _ = (x₂ * c₁) * x₁ := hcomm
  intro b hb
  have hb' : b ∈ Y ⊔ X₁ := by
    rw [sup_comm]
    exact hBX hb
  obtain ⟨y₀, hy₀, x₀, hx₀, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hX₁N hb'
  have hx₀B : x₀ ∈ B := by
    have := mul_mem (inv_mem (hYB hy₀)) hb
    simpa using this
  obtain ⟨h, hh, x₁, hx₁, rfl⟩ := hC x₀ (mem_inf.2 ⟨hx₀, hx₀B⟩)
  have hcomm : y₀ * h = h * y₀ := hYM y₀ hy₀ h (hBM (hHB hh))
  refine ⟨h, hh, y₀ * x₁, mul_mem hy₀ (hXY hx₁), ?_⟩
  calc y₀ * (h * x₁) = (y₀ * h) * x₁ := by group
    _ = (h * y₀) * x₁ := by rw [hcomm]
    _ = h * (y₀ * x₁) := by group

end PartII

section PartIII

variable {G : Type} [Group G] [Finite G]

structure N2Data (t : G) (Λ K1 K2 B N M Y A Z Z' K3t H : Subgroup G) : Prop where
  hK1 : K1 = ⁅Λ, Λ⁆
  hK2 : K2 = ⁅K1, K1⁆
  hB : B = pCoreOf 2 K1
  ht : t * t = 1
  hNt : Nᵍ[t] = N
  hYt : Yᵍ[t] = Y
  hZt : Z = Z'ᵍ[t]
  hΛN : Λ ≤ N
  hNΛ : N ≤ normalizer (Λ : Set G)
  hNM : N ≤ normalizer (M : Set G)
  hMΛ : M ≤ Λ
  hM2 : IsPGroup 2 M
  hNsup : K1 ⊔ K1ᵍ[t] = N
  hKinf : K1 ⊓ K1ᵍ[t] = Y
  hKcomm : ⁅K1, K1ᵍ[t]⁆ ≤ Y
  hKAB : K1 = A ⊔ B
  hBsup : B ⊔ Bᵍ[t] = M
  hBinf : B ⊓ Bᵍ[t] = Y
  hperf : K2 ⊔ Y = K1
  hZsup : Z' ⊔ Z = Y
  hZinf : Z' ⊓ Z = ⊥
  hAZ : ⁅A ⊔ Z, A ⊔ Z⁆ = A ⊔ Z
  hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x
  hYM : ∀ y ∈ Y, ∀ m ∈ M, y * m = m * y
  hAΛ : A ≤ Λ
  hAM : A ⊓ M = ⊥
  hΛAM : ∀ x ∈ Λ, ∃ a ∈ A, ∃ m ∈ M, x = a * m
  hZ'A : Z' ≤ centralizer (A : Set G)
  hYK : Y ≤ K3t
  hKK3 : K1 ≤ normalizer (K3t : Set G)
  hZK : ∀ z ∈ K3t, (∀ k ∈ K3t, k * z = z * k) → z ∈ Z
  hHB : H ≤ B
  hHC : H ≤ centralizer (K3t : Set G)
  hBH : ∀ b ∈ B, ∃ h ∈ H, ∃ y ∈ Y, b = h * y
  hZH : Z ≤ H
  hHY : H ⊓ Y ≤ Z

namespace N2Data

variable {t : G} {Λ K1 K2 B N M Y A Z Z' K3t H : Subgroup G}
  (S : N2Data t Λ K1 K2 B N M Y A Z Z' K3t H)
include S

theorem hYB : Y ≤ B := S.hBinf ▸ inf_le_left

theorem hBM : B ≤ M := S.hBsup ▸ le_sup_left

theorem hBK1 : B ≤ K1 := S.hKAB ▸ le_sup_right

theorem hYK1 : Y ≤ K1 := S.hYB.trans S.hBK1

theorem hZY : Z ≤ Y := S.hZsup ▸ le_sup_right

theorem hZ'Y : Z' ≤ Y := S.hZsup ▸ le_sup_left

theorem hAK1 : A ≤ K1 := S.hKAB ▸ le_sup_left

theorem hK2K1 : K2 ≤ K1 := S.hK2 ▸ commutator_self_le K1

theorem hAZK2 : A ⊔ Z ≤ K2 := by
  have h1 : A ⊔ Z ≤ K1 := sup_le S.hAK1 (S.hZY.trans S.hYK1)
  have := commutator_mono h1 h1
  rw [S.hAZ] at this
  rwa [← S.hK2] at this

theorem hZ'c : K1 ≤ centralizer (Z' : Set G) := by
  have hle : K1 ≤ A ⊔ B := S.hKAB.le
  refine hle.trans (sup_le (le_centralizer_comm S.hZ'A) fun b hb => ?_)
  exact mem_centralizer_iff.2 fun z hz => S.hYM z (S.hZ'Y hz) b (S.hBM hb)

theorem hK1eq : K1 = K2 ⊔ Z' := by
  have hY_le : Y ≤ K2 ⊔ Z' := by
    rw [← S.hZsup]
    exact sup_le le_sup_right ((S.hAZK2.trans' le_sup_right).trans le_sup_left)
  refine le_antisymm ?_ (sup_le S.hK2K1 (S.hZ'Y.trans S.hYK1))
  calc K1 = K2 ⊔ Y := S.hperf.symm
    _ ≤ K2 ⊔ Z' := sup_le le_sup_left hY_le

theorem perfect : ⁅K2, K2⁆ = K2 := by
  refine le_antisymm (commutator_self_le K2) ?_
  have hc : Z' ≤ centralizer ((K2 ⊔ Z' : Subgroup G) : Set G) := by
    rw [← S.hK1eq]
    exact le_centralizer_comm S.hZ'c
  have key := Common.commutator_sup_le_of_le_centralizer hc
  rw [← S.hK1eq] at key
  rwa [← S.hK2] at key

theorem hZK2 : Z ≤ K2 := S.hAZK2.trans' le_sup_right

theorem hAK2 : A ≤ K2 := S.hAZK2.trans' le_sup_left

theorem hBHZ' : ∀ b ∈ B, ∃ h ∈ H, ∃ z' ∈ Z', b = h * z' := by
  intro b hb
  obtain ⟨h, hh, y, hy, rfl⟩ := S.hBH b hb
  have hy' : y ∈ Z' ⊔ Z := S.hZsup ▸ hy
  have hcomm : ∀ x ∈ Z', ∀ w ∈ Z, x * w = w * x := fun x hx w hw =>
    S.hYab x (S.hZ'Y hx) w (S.hZY hw)
  obtain ⟨z', hz', z, hz, rfl⟩ := (UCSAux.mem_sup_iff_of_commute hcomm).1 hy'
  refine ⟨h * z, mul_mem hh (S.hZH hz), z', hz', ?_⟩
  have := hcomm z' hz' z hz
  calc h * (z' * z) = h * (z * z') := by rw [this]
    _ = h * z * z' := by group

theorem hH_eq : H = B ⊓ centralizer (K3t : Set G) := by
  refine le_antisymm (le_inf S.hHB S.hHC) fun b hb => ?_
  obtain ⟨hbB, hbC⟩ := mem_inf.1 hb
  obtain ⟨h, hh, z', hz', rfl⟩ := S.hBHZ' b hbB
  have hz'C : z' ∈ centralizer (K3t : Set G) := by
    have := mul_mem (inv_mem (S.hHC hh)) hbC
    simpa using this
  have hz'Z : z' ∈ Z := by
    refine S.hZK z' (S.hYK (S.hZ'Y hz')) fun k hk => ?_
    exact mem_centralizer_iff.1 hz'C k hk
  have : z' ∈ Z' ⊓ Z := mem_inf.2 ⟨hz', hz'Z⟩
  rw [S.hZinf, Subgroup.mem_bot] at this
  rw [this, mul_one]
  exact hh

theorem hHn : K1 ≤ normalizer (H : Set G) := by
  intro g hg
  rw [S.hH_eq]
  exact Common.mem_normalizer_inf_centralizer
    (S.hB ▸ le_normalizer_pCoreOf K1 hg) (S.hKK3 hg)

theorem hAn : A ≤ normalizer (H : Set G) := S.hAK1.trans S.hHn

theorem hAH_inf_M : (A ⊔ H) ⊓ M = H := by
  refine le_antisymm ?_ (le_inf le_sup_right (S.hHB.trans S.hBM))
  intro x hx
  obtain ⟨hx1, hxM⟩ := mem_inf.1 hx
  have hx' : x ∈ H ⊔ A := by
    rw [sup_comm]
    exact hx1
  obtain ⟨h, hh, a, ha, rfl⟩ := SL2Aux.exists_mul_of_mem_sup S.hAn hx'
  have haM : a ∈ M := by
    have := mul_mem (inv_mem (S.hBM (S.hHB hh))) hxM
    simpa using this
  have ha1 : a = 1 := by
    have : a ∈ A ⊓ M := mem_inf.2 ⟨ha, haM⟩
    rwa [S.hAM, Subgroup.mem_bot] at this
  rw [ha1, mul_one]
  exact hh

theorem hAH_inf_Z' : (A ⊔ H) ⊓ Z' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hxM : x ∈ M := S.hBM (S.hYB (S.hZ'Y hx2))
  have hxH : x ∈ H := S.hAH_inf_M ▸ mem_inf.2 ⟨hx1, hxM⟩
  have hxZ : x ∈ Z := S.hHY (mem_inf.2 ⟨hxH, S.hZ'Y hx2⟩)
  have : x ∈ Z' ⊓ Z := mem_inf.2 ⟨hx2, hxZ⟩
  rwa [S.hZinf] at this

theorem hK1_eq' : K1 = (A ⊔ H) ⊔ Z' := by
  have hBle : B ≤ H ⊔ Z' := fun b hb => by
    obtain ⟨h, hh, z', hz', rfl⟩ := S.hBHZ' b hb
    exact mul_mem (mem_sup_left hh) (mem_sup_right hz')
  refine le_antisymm ?_ (sup_le (sup_le S.hAK1 (S.hHB.trans S.hBK1)) (S.hZ'Y.trans S.hYK1))
  calc K1 = A ⊔ B := S.hKAB
    _ ≤ (A ⊔ H) ⊔ Z' := sup_le (le_sup_left.trans le_sup_left)
        (hBle.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right))

theorem hK2_le : K2 ≤ A ⊔ H := by
  have hc : Z' ≤ centralizer (((A ⊔ H) ⊔ Z' : Subgroup G) : Set G) := by
    rw [← S.hK1_eq']
    exact le_centralizer_comm S.hZ'c
  have key := Common.commutator_sup_le_of_le_centralizer hc
  rw [← S.hK1_eq'] at key
  rw [S.hK2]
  exact key.trans (commutator_self_le _)

theorem hK2_eq : K2 = A ⊔ H := by
  refine le_antisymm S.hK2_le (sup_le S.hAK2 fun h hh => ?_)
  have hh1 : h ∈ K2 ⊔ Z' := S.hK1eq ▸ S.hBK1 (S.hHB hh)
  have hcomm : ∀ k ∈ K2, ∀ z ∈ Z', k * z = z * k := fun k hk z hz =>
    (mem_centralizer_iff.1 (S.hZ'c (S.hK2K1 hk)) z hz).symm
  obtain ⟨k, hk, z', hz', rfl⟩ := (UCSAux.mem_sup_iff_of_commute hcomm).1 hh1
  have hz'AH : z' ∈ A ⊔ H := by
    have := mul_mem (inv_mem (S.hK2_le hk)) (mem_sup_right hh)
    simpa using this
  have hz'1 : z' = 1 := by
    have : z' ∈ (A ⊔ H) ⊓ Z' := mem_inf.2 ⟨hz'AH, hz'⟩
    rwa [S.hAH_inf_Z', Subgroup.mem_bot] at this
  rw [hz'1, mul_one]
  exact hk

theorem hK2_inf_M : K2 ⊓ M = H := by
  rw [S.hK2_eq]
  exact S.hAH_inf_M

theorem pCore_eq : pCoreOf 2 K2 = H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · have hK1K2 : K1 ≤ normalizer (K2 : Set G) := fun g hg =>
      S.hK2 ▸ mem_normalizer_comm_self (Subgroup.le_normalizer hg)
    have hR : pCoreOf 2 K2 ≤ pCoreOf 2 K1 := by
      refine le_pCoreOf_of_normal ((pCoreOf_le K2).trans S.hK2K1) (fun g hg => ?_)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K2)
      exact mem_normalizer_pCoreOf (hK1K2 hg)
    rw [← S.hB] at hR
    rw [← S.hK2_inf_M]
    exact le_inf (pCoreOf_le K2) (hR.trans S.hBM)
  · refine le_pCoreOf_of_normal (S.hK2_eq ▸ le_sup_right) ?_ (S.hM2.to_le (S.hHB.trans S.hBM))
    exact (S.hK2K1).trans S.hHn

theorem hZ'_eq : Zᵍ[t] = Z' := by
  rw [S.hZt, conj_conj_of_mul_self S.ht]

theorem hMt : Mᵍ[t] = M := by
  rw [← S.hBsup, conj_sup, conj_conj_of_mul_self S.ht, sup_comm]

theorem N_eq : N = K2 ⊔ K2ᵍ[t] := by
  have hZ'K2t : Z' ≤ K2ᵍ[t] := by
    rw [← S.hZ'_eq]
    exact conj_mono S.hZK2 t
  have hZK2 : Z ≤ K2 := S.hZK2
  refine le_antisymm ?_ (sup_le (S.hK2K1.trans (S.hNsup ▸ le_sup_left))
    ((conj_mono S.hK2K1 t).trans (S.hNsup ▸ le_sup_right)))
  rw [← S.hNsup]
  refine sup_le ?_ ?_
  · rw [S.hK1eq]
    exact sup_le le_sup_left (hZ'K2t.trans le_sup_right)
  · have h1 : K1ᵍ[t] = K2ᵍ[t] ⊔ Z := by
      rw [S.hK1eq, conj_sup, ← S.hZt]
    rw [h1]
    exact sup_le le_sup_right (hZK2.trans le_sup_left)

theorem hNK2 : N ≤ normalizer (K2 : Set G) := by
  intro g hg
  have h1 := S.hNΛ hg
  have h2 : g ∈ normalizer ((K1 : Subgroup G) : Set G) := by
    rw [S.hK1]
    exact mem_normalizer_comm_self h1
  rw [S.hK2]
  exact mem_normalizer_comm_self h2

theorem hNK2t : N ≤ normalizer ((K2ᵍ[t] : Subgroup G) : Set G) := by
  have := conj_le_normalizer_conj (g := t) S.hNK2
  rwa [S.hNt] at this

theorem hK2N : K2 ≤ N := S.hK2K1.trans (S.hNsup ▸ le_sup_left)

theorem hK2tN : K2ᵍ[t] ≤ N := (conj_mono S.hK2K1 t).trans (S.hNsup ▸ le_sup_right)

theorem K2_inf : K2 ⊓ K2ᵍ[t] = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hxY : x ∈ Y := by
    rw [← S.hKinf]
    exact mem_inf.2 ⟨S.hK2K1 hx1, conj_mono S.hK2K1 t hx2⟩
  have hxZ : x ∈ Z := by
    refine S.hHY (mem_inf.2 ⟨?_, hxY⟩)
    rw [← S.hK2_inf_M]
    exact mem_inf.2 ⟨hx1, S.hBM (S.hYB hxY)⟩
  have hxt : t⁻¹ * x * t ∈ Z := by
    have hY' : t⁻¹ * x * t ∈ Y := by
      have : x ∈ Yᵍ[t] := by rw [S.hYt]; exact hxY
      exact (mem_conj_iff_of_mul_self S.ht).1 this
    refine S.hHY (mem_inf.2 ⟨?_, hY'⟩)
    rw [← S.hK2_inf_M]
    exact mem_inf.2 ⟨(mem_conj_iff_of_mul_self S.ht).1 hx2, S.hBM (S.hYB hY')⟩
  have hxZ' : x ∈ Z' := by
    rw [← S.hZ'_eq]
    exact (mem_conj_iff_of_mul_self S.ht).2 hxt
  have : x ∈ Z' ⊓ Z := mem_inf.2 ⟨hxZ', hxZ⟩
  rwa [S.hZinf] at this

theorem K2_comm : ⁅K2, K2ᵍ[t]⁆ = ⊥ := by
  have := commutator_le_inf_of_normalizes S.hK2N S.hK2tN S.hNK2 S.hNK2t
  rw [S.K2_inf] at this
  exact eq_bot_iff.2 this

theorem H_sup : H ⊔ Hᵍ[t] = M := by
  have hBle : B ≤ H ⊔ Z' := fun b hb => by
    obtain ⟨h, hh, z', hz', rfl⟩ := S.hBHZ' b hb
    exact mul_mem (mem_sup_left hh) (mem_sup_right hz')
  have hZ'Ht : Z' ≤ Hᵍ[t] := by
    rw [← S.hZ'_eq]
    exact conj_mono S.hZH t
  refine le_antisymm (sup_le (S.hHB.trans S.hBM) ?_) ?_
  · have := conj_mono (S.hHB.trans S.hBM) t
    rwa [S.hMt] at this
  · rw [← S.hBsup]
    refine sup_le (hBle.trans (sup_le le_sup_left (hZ'Ht.trans le_sup_right))) ?_
    have h1 := conj_mono hBle t
    rw [conj_sup, ← S.hZt] at h1
    exact h1.trans (sup_le le_sup_right (S.hZH.trans le_sup_left))

theorem H_inf : H ⊓ Hᵍ[t] = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hxY : x ∈ Y := by
    rw [← S.hBinf]
    exact mem_inf.2 ⟨S.hHB hx1, conj_mono S.hHB t hx2⟩
  have hxZ : x ∈ Z := S.hHY (mem_inf.2 ⟨hx1, hxY⟩)
  have hxt : t⁻¹ * x * t ∈ Z := by
    have hY' : t⁻¹ * x * t ∈ Y := by
      have : x ∈ Yᵍ[t] := by rw [S.hYt]; exact hxY
      exact (mem_conj_iff_of_mul_self S.ht).1 this
    exact S.hHY (mem_inf.2 ⟨(mem_conj_iff_of_mul_self S.ht).1 hx2, hY'⟩)
  have hxZ' : x ∈ Z' := by
    rw [← S.hZ'_eq]
    exact (mem_conj_iff_of_mul_self S.ht).2 hxt
  have : x ∈ Z' ⊓ Z := mem_inf.2 ⟨hxZ', hxZ⟩
  rwa [S.hZinf] at this

end N2Data

end PartIII

section Odd

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_factor_of_odd {K : Type} [Field K] [Finite K] {N D Λ P N₂ : Subgroup G}
    {t : G} (hS : Sl2Pair K N D Λ (Λᵍ[t])) (hP : IsSylowOf 2 P N₂) (hPN : P ≤ N) {g : G}
    (hg₂ : g ∈ N₂) (hgP : g ∈ normalizer (P : Set G)) (hgN : g ∈ normalizer (N : Set G))
    (hgD : g ∈ normalizer (D : Set G)) : g ∈ normalizer (Λ : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPM : P ≤ N₂ ⊓ normalizer (P : Set G) := le_inf hP.le Subgroup.le_normalizer
  have hMP : N₂ ⊓ normalizer (P : Set G) ≤ normalizer (P : Set G) := inf_le_right
  have hgM : g ∈ N₂ ⊓ normalizer (P : Set G) := ⟨hg₂, hgP⟩
  have hpow := pow_relIndex_mem hPM hMP hgM
  have hodd : Odd (P.relIndex (N₂ ⊓ normalizer (P : Set G))) := by
    have h1 := (isSylowOf_iff.1 hP).2.2
    have h2 := Subgroup.relIndex_mul_relIndex P (N₂ ⊓ normalizer (P : Set G)) N₂ hPM inf_le_left
    have h3 : P.relIndex (N₂ ⊓ normalizer (P : Set G)) ∣ P.relIndex N₂ :=
      ⟨_, h2.symm⟩
    rw [← Nat.not_even_iff_odd]
    intro he
    exact h1 ((even_iff_two_dvd.1 he).trans h3)
  exact mem_normalizer_of_pow_mem hS.ne (hS.conj_factor hgN hgD)
    ((hS.symm.conj_factor hgN hgD).symm) hodd (hS.le_normalizer (hPN hpow))

end Odd

section N1Side

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem n1Data (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    N1Data t (yamadaU₁ d t) (yamadaY₂ d t) (yamadaD₇ d t) (yamadaP d t) (yamadaN₁ d t) Λ₁ := by
  have hF₁ := hL.fac₁
  have hD := hQ.doubling
  have ht2 := h.t_mul_t
  have h76 := h.yamada_7_6 hW d hK hQ hp hF₁
  have h79 := h.yamada_7_9 hW d hK hQ hp hL
  have h557 := h.yamada_5_55_1 hW d hK hQ
  have h5572 := h.yamada_5_57_2 hW d hK hQ
  have h551 := h.yamada_5_51 hW d hK hQ
  have htU := (h.t_mem_normalizer_yamadaU₁ d hK hD).1
  have htD : t ∈ normalizer (yamadaD₇ d t : Set G) := h551.2.2.2.1
  have htM : t ∈ normalizer (yamadaM₆ d t : Set G) := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
  have hYtN : t ∈ normalizer (yamadaY₂ d t : Set G) := by
    rw [← h557.2.2]
    exact mem_normalizer_comm_self htM
  have hY₂F₅ : yamadaY₂ d t ≤ yamadaF₅ d t := by
    obtain ⟨hY₂W, -, hWX, -⟩ := h.yamada_5_46_1 hW d hK hQ
    exact hY₂W.trans (hWX ▸ le_sup_left)
  have hYD : yamadaY₂ d t ≤ yamadaD₇ d t := hY₂F₅.trans h5572.2.1
  have hK₁N : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
    (commutator_self_le _).trans (h.normalizer_L_inf_U_le_yamadaD₇ hW d hK hQ)
  have hND : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    yamadaN₁_le_normalizer d t hK₁N
  have hDt : (yamadaD₇ d t)ᵍ[t] = yamadaD₇ d t := conj_eq_of_mem_normalizer htD
  obtain ⟨-, -, hPeq, -, hPcomm⟩ := sylow_prod hp.sylow₁ hF₁.sup hF₁.inf hF₁.comm h5572.2.2.2.1
  obtain ⟨-, -, -, -, -, -, hDV, hVVt⟩ := h79.1
  refine ⟨ht2, conj_eq_of_mem_normalizer htU, conj_eq_of_mem_normalizer hYtN, ?_, ?_, hF₁.le, ?_,
    hp.sylow₁.le, h5572.2.2.2.1, hF₁.X_le, ?_, h557.1.2.le, hND, hDV.symm, hVVt, hPeq, hPcomm, hYD,
    h76.2.2.1.1⟩
  · intro u hu
    have hu' : u ∈ zc (yamadaN₁ d t) := h76.2.1.1 ▸ hu
    exact hu'.2
  · exact (le_sup_left : yamadaU₁ d t ≤ yamadaY₂ d t).trans hYD
  · exact hF₁.sup ▸ (le_sup_right : Λ₁ᵍ[t] ≤ Λ₁ ⊔ Λ₁ᵍ[t])
  · have := conj_mono hF₁.X_le t
    rwa [hDt] at this

theorem inv714 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    ∀ g ∈ yamadaN₂ d t ⊓ normalizer (yamadaP d t : Set G),
      g ∈ normalizer ((pCoreOf 2 (derived₁ Λ₁) ⊓ yamadaY₂ d t : Subgroup G) : Set G) := by
  intro g hg
  have hF₁ := hL.fac₁
  have h73c := h.yamada_7_3_char hW d hK hQ hp
  have h557 := h.yamada_5_55_1 hW d hK hQ
  have htD : t ∈ normalizer (yamadaD₇ d t : Set G) := (h.yamada_5_51 hW d hK hQ).2.2.2.1
  have hDt : (yamadaD₇ d t)ᵍ[t] = yamadaD₇ d t := conj_eq_of_mem_normalizer htD
  have hK₁N : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
    (commutator_self_le _).trans (h.normalizer_L_inf_U_le_yamadaD₇ hW d hK hQ)
  have hK₂N : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_self_le _).trans (h.normalizer_L_inf_Y_le_yamadaM₆ hW d hK hQ)
  have hN₁D : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    yamadaN₁_le_normalizer d t hK₁N
  have hN₂M : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hK₂N
  have hgPMD : g ∈ normalizer (yamadaM₆ d t : Set G) ⊓ normalizer (yamadaD₇ d t : Set G) := by
    rw [← h73c.1]
    exact hg.2
  have hgN₁ : g ∈ normalizer (yamadaN₁ d t : Set G) := by
    have hn := Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hK₁N
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hN₁D).1 hn) hgPMD.2
  have hS : Sl2Pair K (yamadaN₁ d t) (yamadaD₇ d t) Λ₁ (Λ₁ᵍ[t]) := by
    refine ⟨inferInstance, hQ.four_le, hF₁.sup, hF₁.inf, hF₁.comm, hF₁.quot, ?_⟩
    have := IsQuotientIso.conj hF₁.quot t
    rwa [hDt] at this
  have hgΛ : g ∈ normalizer (Λ₁ : Set G) :=
    mem_normalizer_factor_of_odd hS hp.sylow₂ hp.sylow₁.le hg.1 hg.2 hgN₁ hgPMD.2
  have hgK1 : g ∈ normalizer ((derived₁ Λ₁ : Subgroup G) : Set G) := mem_normalizer_comm_self hgΛ
  have hgB : g ∈ normalizer ((pCoreOf 2 (derived₁ Λ₁) : Subgroup G) : Set G) :=
    mem_normalizer_pCoreOf hgK1
  have hgY : g ∈ normalizer (yamadaY₂ d t : Set G) := by
    rw [← h557.2.2]
    exact mem_normalizer_comm_self (hN₂M hg.1)
  exact SL2Aux.le_normalizer_inf _ _ ⟨hgB, hgY⟩

theorem n1Derived (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    (yamadaU₁ d t ≤ derived₁ Λ₁ ∧ derived₁ Λ₁ ⊓ (derived₁ Λ₁)ᵍ[t] = yamadaU₁ d t) ∧
      pCoreOf 2 (derived₁ Λ₁) = centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) ∧
      ⁅derived₁ Λ₁, (derived₁ Λ₁)ᵍ[t]⁆ = ⊥ ∧ leviFactor₁ d Λ₁ ≤ derived₁ Λ₁ ∧
      yamadaU₁ d t ≤ pCoreOf 2 (derived₁ Λ₁) ∧ pCoreOf 2 (derived₁ Λ₁) ≤ yamadaD₇ d t ∧
      Λ₁ ≤ leviFactor₁ d Λ₁ ⊔ yamadaD₇ d t := by
  have hF₁ := hL.fac₁
  have S := n1Data hW h d hK hQ hp hL
  have h79 := h.yamada_7_9 hW d hK hQ hp hL
  have ht2 := h.t_mul_t
  obtain ⟨⟨-, -, hcommdM, hperfdM, hdMA, hdMB, -, -⟩, hN1sup, -, -, hKinf⟩ := h79
  have hUK1 : yamadaU₁ d t ≤ derived₁ Λ₁ := hKinf ▸ inf_le_left
  have hdM : derivedMod (yamadaU₁ d t) Λ₁ = derived₁ Λ₁ := sup_eq_left.2 hUK1
  rw [hdM] at hcommdM hperfdM hdMA hdMB
  have hperf : ⁅derived₁ Λ₁, derived₁ Λ₁⁆ ⊔ yamadaU₁ d t = derived₁ Λ₁ := hperfdM
  have hB : pCoreOf 2 (derived₁ Λ₁) = centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) := hdMB.symm
  refine ⟨⟨hUK1, hKinf⟩, hB, commutator_conj_eq_bot ht2 hN1sup.symm S.hUN S.hUt hcommdM hperf,
    hdMA ▸ le_sup_left, ?_, ?_, ?_⟩
  · rw [hB]
    exact le_upperCenterMod S.hUΛt 1
  · rw [hB]
    exact S.hVt_le
  · intro x hx
    have hxN : x ∈ yamadaN₁ d t := hF₁.le hx
    rw [hp.compl₁.1] at hxN
    have hCn : yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G) ≤ normalizer (yamadaD₇ d t : Set G) :=
      inf_le_left.trans S.hND
    have hx' : x ∈ yamadaD₇ d t ⊔ (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) := by
      rw [sup_comm]
      exact hxN
    obtain ⟨dd, hdd, c, hc, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hCn hx'
    have hcΛ : c ∈ Λ₁ := by
      have := mul_mem (inv_mem (S.hDΛ hdd)) hx
      simpa using this
    have hcA : c ∈ leviFactor₁ d Λ₁ := ⟨hcΛ, hc.2⟩
    exact mul_mem (mem_sup_right hdd) (mem_sup_left hcA)

theorem zcP₃_le_U (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂)
    (hX : pCoreOf 2 (derived₁ Λ₁) ⊓ yamadaY₂ d t = zc (yamadaP₃ d t Λ₂)) :
    zc (yamadaP₃ d t Λ₂) ≤ yamadaU₁ d t := by
  have hF₂ := hL.fac₂
  have S := n1Data hW h d hK hQ hp hL
  have h711 := h.yamada_7_11 hW d hK hQ hp hL
  have h57 := h.yamada_5_57_1 hW d hK hQ
  obtain ⟨-, hB, hK1comm, hA₁K1, -, -, hΛAD⟩ := n1Derived hW h d hK hQ hp hL
  have hVtK1 : centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) ≤ derived₁ Λ₁ := hB ▸ pCoreOf_le _
  have hZP : ∀ z ∈ yamadaP d t, (∀ p ∈ yamadaP d t, z * p = p * z) → z ∈ yamadaU₁ d t := by
    intro z hzP hcomm
    have hz' : z ∈ (Subgroup.upperCentralSeries (yamadaP d t) 1).map (yamadaP d t).subtype := by
      refine ⟨⟨z, hzP⟩, ?_, rfl⟩
      rw [Subgroup.upperCentralSeries_one]
      exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcomm g g.2).symm
    rwa [h57.1] at hz'
  have hAK₃ : leviFactor₂ hp.Astar Λ₂ ≤ yamadaK₃ d t Λ₂ :=
    inf_le_inf_left Λ₂ (hp.Astar_spec.le_cen.trans
      (le_sup_left : yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) ≤ _))
  have hB₂M : pCoreOf 2 (derived₁ Λ₂) ≤ yamadaM₆ d t := by
    rw [← h711.1.2.2.2.2.1]
    exact le_sup_left
  intro z hz
  have hzX : z ∈ pCoreOf 2 (derived₁ Λ₁) ⊓ yamadaY₂ d t := hX.symm ▸ hz
  have hzVt : z ∈ centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) := hB ▸ hzX.1
  have hzY : z ∈ yamadaY₂ d t := hzX.2
  have hzP : z ∈ yamadaP d t := S.hDP (S.hYD hzY)
  have hX₂ : (yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂) ⊔ pCoreOf 2 (derived₁ Λ₂) ≤
      centralizer ({z} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hxP₃ : x ∈ yamadaP₃ d t Λ₂ := ⟨hx.1, hAK₃ hx.2⟩
      have := mem_centralizer_iff.1 hz.2 x hxP₃
      exact mem_centralizer_singleton_iff.2 this
    · have hxM : x ∈ yamadaM₆ d t := hB₂M hx
      have hc : z * x = x * z := by
        have hz2 := (h.yamada_5_45_2 hW d hK hQ) hzY
        obtain ⟨w, hw, hwz⟩ := hz2
        rw [Subgroup.upperCentralSeries_one] at hw
        have := Subgroup.mem_center_iff.1 hw ⟨x, hxM⟩
        have h2 := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h2
        have hwz' : (w : G) = z := hwz
        rw [hwz'] at h2
        exact h2.symm
      exact mem_centralizer_singleton_iff.2 hc.symm
  refine S.mem_U_of_centralizes hA₁K1 inf_le_left hΛAD hVtK1 hK1comm hZP hzP (hVtK1 hzVt) ?_
  intro x hx
  have hx2 : x ∈ ((yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁)) ⊔ yamadaY₂ d t :=
    mem_sup_left (hB ▸ hx)
  rw [h711.2] at hx2
  exact (mem_centralizer_singleton_iff.1 (hX₂ hx2)).symm

end N1Side

end ProductK2Aux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


theorem yamada_7_14 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    pCoreOf 2 (derived₁ Λ₁) ⊓ yamadaY₂ d t = zc ((yamadaP₃ d t Λ₂)ᵍ[t]) := by
  have hF₂ := hL.fac₂
  have S := ProductK2Aux.n1Data hW h d hK hQ hp hL
  have h713 := h.yamada_7_13 hW d hK hQ hp hF₂
  have hcard := h.yamada_series_card hW d hK hQ
  have ht2 := h.t_mul_t
  obtain ⟨⟨hUK1, -⟩, hB, -, -, hUB, -, -⟩ := ProductK2Aux.n1Derived hW h d hK hQ hp hL
  have hnotYU : ¬ yamadaY₂ d t ≤ yamadaU₁ d t := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard.2.1, hcard.1] at h1
    have h2 : 1 < Nat.card K := hQ.one_lt
    have h3 := Nat.pow_lt_pow_right h2 (show 2 < 4 by norm_num)
    omega
  have hopts := h713.2.2 (pCoreOf 2 (derived₁ Λ₁) ⊓ yamadaY₂ d t)
    (le_inf hUB (le_sup_left : yamadaU₁ d t ≤ yamadaY₂ d t)) inf_le_right
    (ProductK2Aux.inv714 hW h d hK hQ hp hL)
  rcases hopts with hX | hX | hX | hX
  · exfalso
    apply hnotYU
    apply S.le_of_inf_eq
    rwa [← hB]
  · exfalso
    have hzcU := ProductK2Aux.zcP₃_le_U hW h d hK hQ hp hL hX
    have hKz : zc (yamadaK₃ d t Λ₂) ≤ yamadaU₁ d t := by
      refine le_trans ?_ hzcU
      rw [h713.2.1.2.2.1]
      exact le_sup_left
    have hKzt : zc ((yamadaK₃ d t Λ₂)ᵍ[t]) ≤ yamadaU₁ d t := by
      rw [ProductK2Aux.zc_conj ht2]
      have := conj_mono hKz t
      rwa [S.hUt] at this
    apply hnotYU
    rw [← h713.2.1.1]
    exact sup_le hKz hKzt
  · exact hX
  · exfalso
    apply hnotYU
    apply S.le_of_le_Vt
    rw [← hB]
    exact hX ▸ inf_le_left

end Local

end Setup

namespace ProductK2Aux

section N2Side

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem t_mem_normalizer_N₂_aux (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaN₂ d t : Set G) := by
  have htM : t ∈ normalizer (yamadaM₆ d t : Set G) := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
  have hK₂N : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_self_le _).trans (h.normalizer_L_inf_Y_le_yamadaM₆ hW d hK hQ)
  have hN₂M : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hK₂N
  have hn := Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hK₂N
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hN₂M).1 hn) htM

theorem sl2Pair₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {Λ₂ : Subgroup G}
    (hF₂ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    Sl2Pair K (yamadaN₂ d t) (yamadaM₆ d t) Λ₂ (Λ₂ᵍ[t]) := by
  have htM : t ∈ normalizer (yamadaM₆ d t : Set G) := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
  have hMt : (yamadaM₆ d t)ᵍ[t] = yamadaM₆ d t := conj_eq_of_mem_normalizer htM
  refine ⟨inferInstance, hQ.four_le, hF₂.sup, hF₂.inf, hF₂.comm, hF₂.quot, ?_⟩
  have := IsQuotientIso.conj hF₂.quot t
  rwa [hMt] at this

theorem n2_A_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₂ : Subgroup G}
    (hF₂ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    (leviFactor₂ hp.Astar Λ₂ ⊓ yamadaM₆ d t = ⊥) ∧
      (∀ x ∈ Λ₂, ∃ a ∈ leviFactor₂ hp.Astar Λ₂, ∃ m ∈ yamadaM₆ d t, x = a * m) ∧
      yamadaK₃ d t Λ₂ = leviFactor₂ hp.Astar Λ₂ ⊔ yamadaY₂ d t ∧
      leviFactor₂ hp.Astar Λ₂ ≤ normalizer (yamadaY₂ d t : Set G) := by
  have h557 := h.yamada_5_55_1 hW d hK hQ
  have hK₂N : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_self_le _).trans (h.normalizer_L_inf_Y_le_yamadaM₆ hW d hK hQ)
  have hN₂M : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hK₂N
  have hMY : normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg => by
    rw [← h557.2.2]
    exact mem_normalizer_comm_self hg
  have hMY₂ : yamadaY₂ d t ≤ yamadaM₆ d t := by
    rw [← h557.2.2]
    exact commutator_self_le _
  have hspec := hp.Astar_spec
  have hAstarN : hp.Astar ≤ normalizer (yamadaM₆ d t : Set G) :=
    (hspec.le_cen.trans inf_le_left).trans hN₂M
  have hN₃ : yamadaN₃ d t = hp.Astar ⊔ yamadaY₂ d t := hspec.yamadaN₃_eq hN₂M hp.inf₂
  have hAΛ : leviFactor₂ hp.Astar Λ₂ ≤ Λ₂ := inf_le_left
  have hAA : leviFactor₂ hp.Astar Λ₂ ≤ hp.Astar := inf_le_right
  have hAM : leviFactor₂ hp.Astar Λ₂ ⊓ yamadaM₆ d t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ hp.Astar ⊓ yamadaM₆ d t := mem_inf.2 ⟨hAA (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩
    rwa [hspec.inf_eq, Subgroup.mem_bot] at this
  refine ⟨hAM, ?_, ?_, (hAA.trans hAstarN).trans hMY⟩
  · intro x hx
    have hxN : x ∈ yamadaN₂ d t := hF₂.le hx
    rw [hspec.sup_eq] at hxN
    have hx' : x ∈ yamadaM₆ d t ⊔ hp.Astar := by
      rw [sup_comm]
      exact hxN
    obtain ⟨m, hm, a₀, ha₀, rfl⟩ := SL2Aux.exists_mul_of_mem_sup hAstarN hx'
    have ha₀Λ : a₀ ∈ Λ₂ := by
      have := mul_mem (inv_mem (hF₂.X_le hm)) hx
      simpa using this
    have ha₀A : a₀ ∈ leviFactor₂ hp.Astar Λ₂ := mem_inf.2 ⟨ha₀Λ, ha₀⟩
    have hm' : a₀⁻¹ * m * a₀ ∈ yamadaM₆ d t :=
      (Subgroup.mem_normalizer_iff''.1 (hAstarN ha₀) m).1 hm
    exact ⟨a₀, ha₀A, a₀⁻¹ * m * a₀, hm', by group⟩
  · refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : x ∈ yamadaN₃ d t := (mem_inf.1 hx).2
      have hx'' : x ∈ yamadaY₂ d t ⊔ hp.Astar := by
        rw [hN₃, sup_comm] at hx'
        exact hx'
      obtain ⟨y, hy, a₀, ha₀, rfl⟩ := SL2Aux.exists_mul_of_mem_sup (hAstarN.trans hMY) hx''
      have ha₀Λ : a₀ ∈ Λ₂ := by
        have := mul_mem (inv_mem (hF₂.X_le (hMY₂ hy))) (mem_inf.1 hx).1
        simpa using this
      exact mul_mem (mem_sup_right hy) (mem_sup_left (mem_inf.2 ⟨ha₀Λ, ha₀⟩))
    · refine sup_le (le_inf hAΛ ?_) (le_inf (hMY₂.trans hF₂.X_le) ?_)
      · rw [hN₃]
        exact hAA.trans le_sup_left
      · rw [hN₃]
        exact le_sup_right

theorem n2Basic (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    yamadaY₂ d t ≤ yamadaM₆ d t ∧ yamadaM₆ d t ≤ yamadaP d t ∧
      yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) ∧
      normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) ∧
      (∀ y ∈ yamadaY₂ d t, ∀ m ∈ yamadaM₆ d t, y * m = m * y) ∧
      yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) ∧
      yamadaP d t ⊓ (yamadaP d t)ᵍ[d.wb] = yamadaM₆ d t ∧
      d.wb ∈ yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) ∧ d.wb * d.wb = 1 ∧
      d.wb * t = t * d.wb ∧ t ∈ normalizer (yamadaN₂ d t : Set G) ∧
      t ∈ normalizer (yamadaY₂ d t : Set G) := by
  have h557 := h.yamada_5_55_1 hW d hK hQ
  have hs2 := Setup.Q44.wb_mul_self h d hK
  have hK₂N : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_self_le _).trans (h.normalizer_L_inf_Y_le_yamadaM₆ hW d hK hQ)
  have hN₂M : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    yamadaN₂_le_normalizer d t hK₂N
  have hMY : normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg => by
    rw [← h557.2.2]
    exact mem_normalizer_comm_self hg
  have htM : t ∈ normalizer (yamadaM₆ d t : Set G) := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
  obtain ⟨α, hex, -⟩ := hp.exact₂
  refine ⟨?_, (h.yamada_5_57_2 hW d hK hQ).2.2.1, hN₂M, hMY, ?_,
    fun g hg => hMY ((h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ).2 hg), ?_,
    hp.Astar_spec.le_cen (hp.Astar_spec.levi_le d.wb_mem_leviB), hs2, Setup.Q44.wb_mul_t h d,
    t_mem_normalizer_N₂_aux hW h d hK hQ,
    hMY htM⟩
  · rw [← h557.2.2]
    exact commutator_self_le _
  · intro y hy m hm
    obtain ⟨w, hw, hwz⟩ := (h.yamada_5_45_2 hW d hK hQ) hy
    rw [Subgroup.upperCentralSeries_one] at hw
    have := Subgroup.mem_center_iff.1 hw ⟨m, hm⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    have hwz' : (w : G) = y := hwz
    rw [hwz'] at h2
    exact h2.symm
  · have hPs' := (h.yamadaP_inf_map_conj_wb hW d hK hQ hp.sylow₂ hex).1
    rw [conj_eq_map_conj hs2]
    exact hPs'

theorem n2PartII (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) {X₁ : Subgroup G}
    (hX₁ : (yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁) = X₁) :
    X₁ ⊓ X₁ᵍ[d.wb] ≤ pCoreOf 2 (derived₁ Λ₂) ∧
      X₁ ⊓ X₁ᵍ[d.wb] ≤ centralizer (((yamadaK₃ d t Λ₂)ᵍ[t] : Subgroup G) : Set G) ∧
      (∀ b ∈ pCoreOf 2 (derived₁ Λ₂), ∃ k ∈ X₁ ⊓ X₁ᵍ[d.wb], ∃ y ∈ yamadaY₂ d t, b = k * y) ∧
      zc ((yamadaK₃ d t Λ₂)ᵍ[t]) ≤ X₁ ⊓ X₁ᵍ[d.wb] ∧
      X₁ ⊓ X₁ᵍ[d.wb] ⊓ yamadaY₂ d t ≤ zc ((yamadaK₃ d t Λ₂)ᵍ[t]) := by
  have hF₁ := hL.fac₁
  have hF₂ := hL.fac₂
  have ht2 := h.t_mul_t
  have S := n1Data hW h d hK hQ hp hL
  have hS₂ := sl2Pair₂ hW h d hK hQ hF₂
  have h711 := h.yamada_7_11 hW d hK hQ hp hL
  have h713 := h.yamada_7_13 hW d hK hQ hp hF₂
  have h714 := h.yamada_7_14 hW d hK hQ hp hL
  have h557 := h.yamada_5_55_1 hW d hK hQ
  obtain ⟨hYM₆, hMP, hN₂M, hMY, hYM, hPY, hPs, hwbA, hs2, hst, htN₂, htY⟩ :=
    n2Basic hW h d hK hQ hp
  obtain ⟨hAM, -, hK3eq, hAY⟩ := n2_A_facts hW h d hK hQ hp hF₂
  obtain ⟨⟨hUK1, hK1inf⟩, hB₁eq, hK1comm, hA₁K1, hUB₁, hB₁D, -⟩ := n1Derived hW h d hK hQ hp hL
  have hYB : yamadaY₂ d t ≤ pCoreOf 2 (derived₁ Λ₂) := h711.1.2.2.2.2.2 ▸ inf_le_left
  have hdY : derivedMod (yamadaY₂ d t) Λ₂ = derived₁ Λ₂ := sup_eq_left.2 (hYB.trans (pCoreOf_le _))
  have hBM : pCoreOf 2 (derived₁ Λ₂) ≤ yamadaM₆ d t := h711.1.2.2.2.2.1 ▸ le_sup_left
  have hKAB : derived₁ Λ₂ = leviFactor₂ hp.Astar Λ₂ ⊔ pCoreOf 2 (derived₁ Λ₂) := by
    have := h711.1.2.2.2.1
    rwa [hdY] at this
  have hAK1 : leviFactor₂ hp.Astar Λ₂ ≤ derived₁ Λ₂ := hKAB ▸ le_sup_left
  have hABn : leviFactor₂ hp.Astar Λ₂ ≤
      normalizer ((pCoreOf 2 (derived₁ Λ₂) : Subgroup G) : Set G) :=
    hAK1.trans (le_normalizer_pCoreOf _)
  have hX₂ : X₁ ⊔ yamadaY₂ d t =
      (yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂) ⊔ pCoreOf 2 (derived₁ Λ₂) := by
    rw [← hX₁]
    exact h711.2
  have hX₁X₂ : X₁ ≤ (yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂) ⊔ pCoreOf 2 (derived₁ Λ₂) :=
    le_sup_left.trans hX₂.le
  have hX₁K1 : X₁ ≤ derived₁ Λ₁ := hX₁ ▸ sup_le (inf_le_right.trans hA₁K1) (pCoreOf_le _)
  have hB₁X₁ : pCoreOf 2 (derived₁ Λ₁) ≤ X₁ := hX₁ ▸ le_sup_right
  have hUY : yamadaU₁ d t ≤ yamadaY₂ d t := le_sup_left
  have hYU : yamadaY₂ d t = yamadaU₁ d t ⊔ (yamadaU₁ d t)ᵍ[d.wb] := by
    rw [conj_eq_map_conj hs2]
    rfl
  have hHB := inf_conj_le_B (s := d.wb) hX₁X₂ rfl hBM hMP hPs hAM hABn
  have hYP : yamadaY₂ d t ≤ yamadaP d t := hYM₆.trans hMP
  have hK3 := K3_le_sup (s := d.wb) hs2 h713.1.2 rfl hK3eq.le hAY hYP hX₂ hYU (hUB₁.trans hB₁X₁)
  have hHC := inf_conj_le_centralizer hst hK3 hX₁K1 hK1comm
  have hwbN₂ : d.wb ∈ yamadaN₂ d t := hwbA.1
  have hwbΛ : d.wb ∈ normalizer (Λ₂ : Set G) := hS₂.le_normalizer hwbN₂
  have hBs : (pCoreOf 2 (derived₁ Λ₂))ᵍ[d.wb] = pCoreOf 2 (derived₁ Λ₂) :=
    conj_eq_of_mem_normalizer (mem_normalizer_pCoreOf (mem_normalizer_comm_self hwbΛ))
  have hYs : (yamadaY₂ d t)ᵍ[d.wb] = yamadaY₂ d t := conj_eq_of_mem_normalizer (hMY (hN₂M hwbN₂))
  have hUt : (yamadaU₁ d t)ᵍ[t] = yamadaU₁ d t := S.hUt
  have hHBH := B_le_mul (s := d.wb) hs2 hX₂ hBM hMP hYB hYM hPY hBs hYs hYU hUB₁ hB₁X₁
    (fun x hx y hy => hYM x hx y (hYM₆ hy)) hHB hUY
  have hK3wb : (yamadaK₃ d t Λ₂)ᵍ[d.wb] = yamadaK₃ d t Λ₂ := by
    refine conj_eq_of_mem_normalizer ?_
    have h1 : d.wb ∈ yamadaN₃ d t :=
      mem_sup_left hwbA
    exact SL2Aux.le_normalizer_inf _ _ ⟨hwbΛ, Subgroup.le_normalizer h1⟩
  have hZ's : (zc (yamadaK₃ d t Λ₂))ᵍ[d.wb] = zc (yamadaK₃ d t Λ₂) := by
    rw [← zc_conj hs2, hK3wb]
  have hZs : (zc ((yamadaK₃ d t Λ₂)ᵍ[t]))ᵍ[d.wb] = zc ((yamadaK₃ d t Λ₂)ᵍ[t]) := by
    rw [← zc_conj hs2, conj_conj_comm hst.symm, hK3wb]
  have hZY : zc ((yamadaK₃ d t Λ₂)ᵍ[t]) ≤ yamadaY₂ d t := h713.2.1.1 ▸ le_sup_right
  have hZ'Y : zc (yamadaK₃ d t Λ₂) ≤ yamadaY₂ d t := h713.2.1.1 ▸ le_sup_left
  have hZZ' : zc ((yamadaK₃ d t Λ₂)ᵍ[t]) ⊓ zc (yamadaK₃ d t Λ₂) = ⊥ := by
    rw [inf_comm]
    exact h713.2.1.2.1
  have hYab : ∀ x ∈ yamadaY₂ d t, ∀ y ∈ yamadaY₂ d t, x * y = y * x :=
    fun x hx y hy => hYM x hx y (hYM₆ hy)
  have hYZ : ∀ y ∈ yamadaY₂ d t, ∃ z ∈ zc ((yamadaK₃ d t Λ₂)ᵍ[t]),
      ∃ z' ∈ zc (yamadaK₃ d t Λ₂), y = z * z' := by
    intro y hy
    have hy' : y ∈ zc (yamadaK₃ d t Λ₂) ⊔ zc ((yamadaK₃ d t Λ₂)ᵍ[t]) := h713.2.1.1 ▸ hy
    obtain ⟨z', hz', z, hz, rfl⟩ := (UCSAux.mem_sup_iff_of_commute fun x hx w hw =>
      hYab x (hZ'Y hx) w (hZY hw)).1 hy'
    exact ⟨z, hz, z', hz', hYab z' (hZ'Y hz') z (hZY hz)⟩
  have hX : pCoreOf 2 (derived₁ Λ₁) ⊓ yamadaY₂ d t =
      zc ((yamadaK₃ d t Λ₂)ᵍ[t]) ⊔ yamadaU₁ d t := by
    rw [h714, zc_conj ht2, h713.2.1.2.2.1, conj_sup, hUt, ← zc_conj ht2]
  have hXt : (pCoreOf 2 (derived₁ Λ₁))ᵍ[t] ⊓ yamadaY₂ d t =
      zc (yamadaK₃ d t Λ₂) ⊔ yamadaU₁ d t := by
    have h1 := congrArg (fun X : Subgroup G => Xᵍ[t]) hX
    simp only [conj_inf, conj_sup, S.hYt, hUt] at h1
    rw [h1, ← zc_conj ht2, conj_conj_of_mul_self ht2]
  have hBB : pCoreOf 2 (derived₁ Λ₁) ⊓ (pCoreOf 2 (derived₁ Λ₁))ᵍ[t] ≤ yamadaU₁ d t := by
    rw [← hK1inf]
    exact inf_le_inf (pCoreOf_le _) (conj_mono (pCoreOf_le _) t)
  have hX₁Y : X₁ ⊓ yamadaY₂ d t ≤ pCoreOf 2 (derived₁ Λ₁) :=
    inf_le_of_complement hX₁ (hA₁K1.trans (le_normalizer_pCoreOf _)) hB₁D S.hYD
      (inf_le_inf_right _ hF₁.le) hp.compl₁.2.1
  have hUUs : yamadaU₁ d t ⊓ (yamadaU₁ d t)ᵍ[d.wb] = ⊥ := by
    rw [conj_eq_map_conj hs2]
    exact (h.yamada_5_13_1 d hK (hQ.doubling)).1.1
  have hZ := Z_le_and_inf_le (s := d.wb) hYab hZY hZ'Y hZZ' hYZ hUY hX hXt hBB hX₁Y hB₁X₁ hYs hZs
    hZ's hUUs
  exact ⟨hHB, hHC, hHBH, hZ.1, hZ.2⟩

theorem n2Data (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    N2Data t Λ₂ (derived₁ Λ₂) (derived₂ Λ₂) (pCoreOf 2 (derived₁ Λ₂)) (yamadaN₂ d t)
      (yamadaM₆ d t) (yamadaY₂ d t) (leviFactor₂ hp.Astar Λ₂) (zc ((yamadaK₃ d t Λ₂)ᵍ[t]))
      (zc (yamadaK₃ d t Λ₂)) ((yamadaK₃ d t Λ₂)ᵍ[t])
      (((yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁)) ⊓
        ((yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁))ᵍ[d.wb]) := by
  have hF₂ := hL.fac₂
  have ht2 := h.t_mul_t
  have hS₂ := sl2Pair₂ hW h d hK hQ hF₂
  have h711 := h.yamada_7_11 hW d hK hQ hp hL
  have h713 := h.yamada_7_13 hW d hK hQ hp hF₂
  have h74 := h.yamada_7_4 hW d hK hQ hp hF₂
  obtain ⟨hYM₆, hMP, hN₂M, hMY, hYM, hPY, hPs, hwbA, hs2, hst, htN₂, htY⟩ :=
    n2Basic hW h d hK hQ hp
  obtain ⟨hAM, hΛAM, hK3eq, hAY⟩ := n2_A_facts hW h d hK hQ hp hF₂
  obtain ⟨hHB, hHC, hBH, hZH, hHY⟩ := n2PartII hW h d hK hQ hp hL rfl
  have hYB : yamadaY₂ d t ≤ pCoreOf 2 (derived₁ Λ₂) := h711.1.2.2.2.2.2 ▸ inf_le_left
  have hdY : derivedMod (yamadaY₂ d t) Λ₂ = derived₁ Λ₂ := sup_eq_left.2 (hYB.trans (pCoreOf_le _))
  have hKAB : derived₁ Λ₂ = leviFactor₂ hp.Astar Λ₂ ⊔ pCoreOf 2 (derived₁ Λ₂) := by
    have := h711.1.2.2.2.1
    rwa [hdY] at this
  have hAK1 : leviFactor₂ hp.Astar Λ₂ ≤ derived₁ Λ₂ := hKAB ▸ le_sup_left
  have hAK₃ : leviFactor₂ hp.Astar Λ₂ ≤ yamadaK₃ d t Λ₂ := hK3eq ▸ le_sup_left
  have hYK₃ : yamadaY₂ d t ≤ yamadaK₃ d t Λ₂ := hK3eq ▸ le_sup_right
  have hK₁N : derived₁ Λ₂ ≤ normalizer (yamadaY₂ d t : Set G) :=
    (commutator_self_le Λ₂).trans (hF₂.le.trans (hN₂M.trans hMY))
  refine
    { hK1 := rfl, hK2 := rfl, hB := rfl, ht := ht2,
      hNt := conj_eq_of_mem_normalizer htN₂, hYt := conj_eq_of_mem_normalizer htY,
      hZt := zc_conj ht2 (yamadaK₃ d t Λ₂), hΛN := hF₂.le, hNΛ := hS₂.le_normalizer,
      hNM := hN₂M, hMΛ := hF₂.X_le, hM2 := hp.sylow₂.isPGroup.to_le hMP,
      hNsup := ?_, hKinf := ?_, hKcomm := ?_, hKAB := hKAB, hBsup := h711.1.2.2.2.2.1,
      hBinf := h711.1.2.2.2.2.2, hperf := ?_, hZsup := h713.2.1.1, hZinf := h713.2.1.2.1,
      hAZ := h713.2.1.2.2.2, hYab := fun x hx y hy => hYM x hx y (hYM₆ hy), hYM := hYM,
      hAΛ := inf_le_left, hAM := hAM, hΛAM := hΛAM, hZ'A := ?_, hYK := ?_, hKK3 := ?_,
      hZK := ?_, hHB := hHB, hHC := hHC, hBH := hBH, hZH := hZH, hHY := hHY }
  · have := h711.1.1
    rw [hdY] at this
    exact this.symm
  · have := h711.1.2.1
    rwa [hdY] at this
  · have := h711.1.2.2.1
    rwa [hdY] at this
  · have := h74.2.1
    rw [hdY] at this
    exact this
  · exact fun z hz => centralizer_le hAK₃ (mem_inf.1 hz).2
  · have := conj_mono hYK₃ t
    rwa [conj_eq_of_mem_normalizer htY] at this
  · have hK3t : (yamadaK₃ d t Λ₂)ᵍ[t] = (leviFactor₂ hp.Astar Λ₂)ᵍ[t] ⊔ yamadaY₂ d t := by
      rw [hK3eq, conj_sup, conj_eq_of_mem_normalizer htY]
    rw [hK3t]
    refine le_normalizer_sup_of_conj_mem hK₁N fun g hg a ha => ?_
    have h1 : g * a * g⁻¹ * a⁻¹ ∈ yamadaY₂ d t := by
      have hc := commutator_mem_commutator hg (conj_mono hAK1 t ha)
      have := h711.1.2.2.1
      rw [hdY] at this
      have h2 := this hc
      rwa [commutatorElement_def] at h2
    have e : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact mul_mem (mem_sup_right h1) (mem_sup_left ha)
  · intro z hz hc
    exact ⟨hz, mem_centralizer_iff.2 hc⟩

end N2Side

end ProductK2Aux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


theorem yamada_7_15 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    (yamadaN₂ d t = derived₂ Λ₂ ⊔ (derived₂ Λ₂)ᵍ[t] ∧
      derived₂ Λ₂ ⊓ (derived₂ Λ₂)ᵍ[t] = ⊥ ∧
      ⁅derived₂ Λ₂, (derived₂ Λ₂)ᵍ[t]⁆ = ⊥ ∧
      derived₂ Λ₂ = leviFactor₂ hp.Astar Λ₂ ⊔ pCoreOf 2 (derived₂ Λ₂) ∧
      ⁅derived₂ Λ₂, derived₂ Λ₂⁆ = derived₂ Λ₂ ∧
      pCoreOf 2 (derived₂ Λ₂) ⊔ (pCoreOf 2 (derived₂ Λ₂))ᵍ[t] = yamadaM₆ d t ∧
      pCoreOf 2 (derived₂ Λ₂) ⊓ (pCoreOf 2 (derived₂ Λ₂))ᵍ[t] = ⊥) ∧
    pCoreOf 2 (derived₂ Λ₂) =
      ((yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁)) ⊓
        ((yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₁ Λ₁))ᵍ[d.wb] := by
  have S := ProductK2Aux.n2Data hW h d hK hQ hp hL
  have hpc := S.pCore_eq
  refine ⟨⟨S.N_eq, S.K2_inf, S.K2_comm, ?_, S.perfect, ?_, ?_⟩, hpc⟩
  · rw [hpc]
    exact S.hK2_eq
  · rw [hpc]
    exact S.H_sup
  · rw [hpc]
    exact S.H_inf

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
