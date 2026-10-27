module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductK2
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductDecomp
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Sylow
public import CFSG.LocalAnalysis.EvenBN.G2.LocalN60
public import CFSG.GH74.Generic.S45.LEvSporGen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (sylow_prod mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer'
    le_normalizer_of_commutator_mem le_normalizer_pCoreOf le_pCoreOf_of_normal Sl2Pair
    mem_normalizer_of_pow_mem pow_relIndex_mem conj_eq_of_mem_normalizer
    mem_normalizer_of_conj_eq)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductDecompAux

section Generic

variable {G : Type} [Group G] [Finite G]

theorem inf_sup_eq_of_le_of_le_normalizer {A B P : Subgroup G} (hBP : B ≤ P)
    (hAB : A ≤ normalizer (B : Set G)) : P ⊓ (A ⊔ B) = (P ⊓ A) ⊔ B := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left P le_sup_left) (le_inf hBP le_sup_right))
  intro x hx
  obtain ⟨hxP, hxAB⟩ := mem_inf.1 hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hAB).1 hxAB
  have haP : a ∈ P := by
    have := mul_mem hxP (inv_mem (hBP hb))
    simpa using this
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨haP, ha⟩)) (mem_sup_right hb)

theorem inf_sup_eq_of_le_of_le_normalizer' {A B P : Subgroup G} (hAP : A ≤ P)
    (hAB : A ≤ normalizer (B : Set G)) : P ⊓ (A ⊔ B) = A ⊔ (P ⊓ B) := by
  refine le_antisymm ?_ (sup_le (le_inf hAP le_sup_left) (inf_le_inf_left P le_sup_right))
  intro x hx
  obtain ⟨hxP, hxAB⟩ := mem_inf.1 hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hAB).1 hxAB
  have hbP : b ∈ P := by
    have := mul_mem (inv_mem (hAP ha)) hxP
    simpa using this
  exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_inf.2 ⟨hbP, hb⟩))

theorem le_of_isSylowOf_of_le_normalizer {P K O : Subgroup G} (hP : IsSylowOf 2 P K)
    (hOK : O ≤ K) (hKO : K ≤ normalizer (O : Set G)) (hO : IsPGroup 2 O) : O ≤ P := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  haveI : (O.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hOK).2 hKO
  have h1 : O.subgroupOf K ≤ (Q : Subgroup K) :=
    IsPGroup.le_sylow_of_normal (N := O.subgroupOf K) hO.comap_subtype Q
  rw [hQ] at h1
  intro x hx
  have hx' : (⟨x, hOK hx⟩ : K) ∈ O.subgroupOf K := hx
  exact h1 hx'

theorem zc_conj (A : Subgroup G) (g : G) : zc (Aᵍ[g]) = (zc A)ᵍ[g] := by
  have key : ∀ (B : Subgroup G) (x : G), x ∈ Bᵍ[g] ↔ g * x * g⁻¹ ∈ B := fun B x =>
    TrialityD4.ProductCase.ProductN1SylowAux.mem_conj_iff
  ext x
  simp only [zc, mem_inf, key, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h1 := hc (g⁻¹ * y * g) (by simpa [mul_assoc] using hy)
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun z hz => ?_⟩
    have h1 := hc (g * z * g⁻¹) hz
    calc z * x = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by rw [h1]
      _ = x * z := by group

theorem card_sup_of_commute {A B : Subgroup G} (hc : ⁅A, B⁆ = ⊥) (hi : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hB : B ≤ normalizer (A : Set G) := by
    rw [commutator_comm] at hc
    exact (commutator_eq_bot_iff_le_centralizer.1 hc).trans (Subgroup.centralizer_le_normalizer _)
  have := Common.card_sup_mul_card_inf_eq hB
  rw [hi] at this
  simpa using this

theorem commutator_sup_central {A Z : Subgroup G}
    (hZ : Z ≤ centralizer ((A ⊔ Z : Subgroup G) : Set G)) : ⁅A ⊔ Z, A ⊔ Z⁆ = ⁅A, A⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_sup_left)
  have hcomm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a := fun a ha z hz =>
    mem_centralizer_iff.1 (hZ hz) a (mem_sup_left ha)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, z, hz, rfl⟩ :=
    (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute hcomm).1 hx
  obtain ⟨a', ha', z', hz', rfl⟩ :=
    (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute hcomm).1 hy
  have hzz' : z * z' = z' * z := mem_centralizer_iff.1 (hZ hz') z (mem_sup_right hz)
  have := TrialityD4.commutatorElement_mul_mul_of_commute' (a := a) (b := a') (c := z) (d := z')
    (hcomm a' ha' z hz).symm hzz' (hcomm a ha z' hz').symm
  rw [this]
  exact Subgroup.commutator_mem_commutator ha ha'

theorem mem_pCoreOf_of_mul_mem {A B : Subgroup G} (hc : ⁅A, B⁆ = ⊥) (hi : A ⊓ B = ⊥) {a b : G}
    (ha : a ∈ A) (hb : b ∈ B) (hab : a * b ∈ pCoreOf 2 (A ⊔ B)) : a ∈ pCoreOf 2 A := by
  set O := pCoreOf 2 (A ⊔ B) with hO
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.1 hc
  have hAB : A ≤ normalizer (B : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.1 hc).trans (Subgroup.centralizer_le_normalizer _)
  have hBA : B ≤ normalizer (A : Set G) := by
    rw [commutator_comm] at hc
    exact (commutator_eq_bot_iff_le_centralizer.1 hc).trans (Subgroup.centralizer_le_normalizer _)
  have hON : A ⊔ B ≤ normalizer (O : Set G) := le_normalizer_pCoreOf _
  have hBO : B ≤ normalizer (O : Set G) := le_sup_right.trans hON
  set Wa : Subgroup G := A ⊓ (O ⊔ B) with hWa
  have haW : a ∈ Wa := by
    refine ⟨ha, ?_⟩
    have : a = (a * b) * b⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_left hab) (mem_sup_right (inv_mem hb))
  have hWA : Wa ≤ A := inf_le_left
  have hAW : A ≤ normalizer (Wa : Set G) :=
    fun x hx => Common.mem_normalizer_inf (Subgroup.le_normalizer hx)
      (Common.mem_normalizer_sup (hON (mem_sup_left hx)) (hAB hx))
  have hWp : IsPGroup 2 Wa := by
    intro w
    obtain ⟨hwA, hwOB⟩ := w.2
    obtain ⟨o, ho, b', hb', hw⟩ := (mem_sup_iff_of_le_normalizer' hBO).1 hwOB
    obtain ⟨n, hn⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ B)) ⟨o, ho⟩
    have hon : o ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hwb : (w : G) * b' = b' * w := hcomm _ hwA _ hb'
    have ho' : o = (w : G) * b'⁻¹ := by rw [hw]; group
    have hcom : Commute (w : G) b'⁻¹ := (Commute.inv_right (hwb : Commute (w : G) b'))
    have h1 : (w : G) ^ (2 ^ n) * (b'⁻¹) ^ (2 ^ n) = 1 := by
      rw [← hcom.mul_pow, ← ho']
      exact hon
    have h2 : (w : G) ^ (2 ^ n) ∈ A ⊓ B := by
      refine ⟨pow_mem hwA _, ?_⟩
      have : (w : G) ^ (2 ^ n) = ((b'⁻¹) ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact B.inv_mem (B.pow_mem (B.inv_mem hb') _)
    rw [hi, Subgroup.mem_bot] at h2
    exact ⟨n, Subtype.ext (by simpa using h2)⟩
  exact le_pCoreOf_of_normal hWA hAW hWp haW

theorem pCoreOf_sup_le_of_commute {A B : Subgroup G} (hc : ⁅A, B⁆ = ⊥) (hi : A ⊓ B = ⊥) :
    pCoreOf 2 (A ⊔ B) ≤ pCoreOf 2 A ⊔ pCoreOf 2 B := by
  intro x hx
  have hxAB : x ∈ A ⊔ B := LieType.BorelTits.pCoreOf_le 2 _ hx
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.1 hc
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute hcomm).1 hxAB
  have hc' : ⁅B, A⁆ = ⊥ := by rw [commutator_comm]; exact hc
  have hi' : B ⊓ A = ⊥ := by rw [inf_comm]; exact hi
  refine mul_mem (mem_sup_left (mem_pCoreOf_of_mul_mem hc hi ha hb hx))
    (mem_sup_right (mem_pCoreOf_of_mul_mem hc' hi' hb ha ?_))
  rw [sup_comm, ← hcomm a ha b hb]
  exact hx

theorem mem_normalizer_commutator_of_mem {T R : Subgroup G} {g : G}
    (hT : g ∈ normalizer (T : Set G)) (hR : g ∈ normalizer (R : Set G)) :
    g ∈ normalizer ((⁅T, R⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_eq
  rw [TrialityD4.ProductCase.ProductN1SylowAux.conj_commutator, conj_eq_of_mem_normalizer hT,
    conj_eq_of_mem_normalizer hR]

theorem sylow_decomp {P N A : Subgroup G} {t : G} {n : ℕ} (hP : IsSylowOf 2 P N)
    (hN : A ⊔ Aᵍ[t] = N) (hi : A ⊓ Aᵍ[t] = ⊥) (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (hPt : Pᵍ[t] = P)
    (hcard : Nat.card P = n ^ 2) :
    IsSylowOf 2 (P ⊓ A) A ∧ P = (P ⊓ A) ⊔ (P ⊓ A)ᵍ[t] ∧
      (P ⊓ A) ⊓ (P ⊓ A)ᵍ[t] = ⊥ ∧ ⁅P ⊓ A, (P ⊓ A)ᵍ[t]⁆ = ⊥ ∧ Nat.card (P ⊓ A : Subgroup G) = n := by
  obtain ⟨hS, -, hPeq, hPinf, hPcomm⟩ := sylow_prod hP hN hi hc.le bot_le
  have hconj : P ⊓ Aᵍ[t] = (P ⊓ A)ᵍ[t] := by
    rw [TrialityD4.ProductCase.ProductDecompAux.conjT_inf, hPt]
  rw [hconj] at hPeq hPinf hPcomm
  have hcomm : ⁅P ⊓ A, (P ⊓ A)ᵍ[t]⁆ = ⊥ := le_bot_iff.1 hPcomm
  refine ⟨hS, hPeq, hPinf, hcomm, ?_⟩
  have h1 := card_sup_of_commute hcomm hPinf
  rw [← hPeq, TrialityD4.ProductCase.ProductDecompAux.card_conjT, hcard] at h1
  have h2 : Nat.card (P ⊓ A : Subgroup G) ^ 2 = n ^ 2 := by
    rw [pow_two, ← h1, pow_two]
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2




theorem eq_of_mul_eq_mul_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a₁ a₂ b₁ b₂ : G}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (h : a₁ * b₁ = a₂ * b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
      _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
      _ = b₂ * b₁⁻¹ := by group
  have h2 : a₂⁻¹ * a₁ ∈ A ⊓ B :=
    mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, by rw [h1]; exact mul_mem hb₂ (inv_mem hb₁)⟩
  rw [hAB, Subgroup.mem_bot] at h2
  have e1 : a₁ = a₂ := by
    have := mul_eq_one_iff_eq_inv.1 h2
    simpa using this.symm
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem decomp_center {P A O Z : Subgroup G} {t : G} (ht : t * t = 1)
    (hAB : A ⊓ Aᵍ[t] = ⊥) (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (hPA : P ≤ A ⊔ Aᵍ[t])
    (hOA : O ≤ A) (hAO : A ≤ normalizer (O : Set G)) (hOP : O ≤ P) (hOtP : Oᵍ[t] ≤ P)
    (hZO : Z ≤ O ⊔ Oᵍ[t]) (hZP : ∀ z ∈ Z, ∀ y ∈ P, y * z = z * y)
    (hZcen : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Z) :
    Z ≤ (O ⊓ Z) ⊔ (Oᵍ[t] ⊓ Z) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.1 hc
  have hOtA : Oᵍ[t] ≤ Aᵍ[t] := Subgroup.map_mono hOA
  have hAtO : Aᵍ[t] ≤ normalizer ((Oᵍ[t] : Subgroup G) : Set G) := fun y hy => by
    refine TrialityD4.ProductCase.ProductDecompAux.mem_normalizer_map_conj_of ?_
    exact hAO ((TrialityD4.ProductCase.ProductN1SylowAux.mem_conj_iff).1 hy)
  have hOOt : O ⊓ Oᵍ[t] = ⊥ := le_bot_iff.1 (hAB ▸ inf_le_inf hOA hOtA)
  intro u hu
  obtain ⟨o, ho, o', ho', rfl⟩ := (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute
    (fun a ha b hb => hcomm a (hOA ha) b (hOtA hb))).1 (hZO hu)
  have hoc : ∀ x ∈ P, x * o = o * x := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute hcomm).1 (hPA hx)
    have hu' := hZP (o * o') hu (a * b) hx
    have h1 : (a * o * a⁻¹) * (b * o' * b⁻¹) = o * o' := by
      have e1 : (a * b) * (o * o') = (o * o') * (a * b) := hu'
      have hbo : b * o = o * b := (hcomm o (hOA ho) b hb).symm
      have hao' : a * (b * o' * b⁻¹) = (b * o' * b⁻¹) * a :=
        hcomm a ha _ (mul_mem (mul_mem hb (hOtA ho')) (inv_mem hb))
      calc (a * o * a⁻¹) * (b * o' * b⁻¹)
          = a * o * (a⁻¹ * (b * o' * b⁻¹) * a) * a⁻¹ := by group
        _ = a * o * (b * o' * b⁻¹) * a⁻¹ := by
            have : a⁻¹ * (b * o' * b⁻¹) * a = b * o' * b⁻¹ := by
              rw [mul_assoc, ← hao']
              group
            rw [this]
        _ = (a * b) * (o * o') * (a * b)⁻¹ := by
            have e2 : a * o * (b * o' * b⁻¹) * a⁻¹ = a * (o * b) * o' * b⁻¹ * a⁻¹ := by group
            rw [e2, ← hbo]
            group
        _ = o * o' := by rw [e1]; group
    have hao : a * o * a⁻¹ ∈ O := (mem_normalizer_iff.1 (hAO ha) o).1 ho
    have hbo' : b * o' * b⁻¹ ∈ Oᵍ[t] := (mem_normalizer_iff.1 (hAtO hb) o').1 ho'
    obtain ⟨e1, -⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hOOt hao ho hbo' ho' h1
    calc (a * b) * o = a * (o * b) * 1 := by
          have hbo : b * o = o * b := (hcomm o (hOA ho) b hb).symm
          rw [mul_one, ← hbo]; group
      _ = o * (a * b) := by
          have : a * o = o * a := by
            have := e1
            calc a * o = (a * o * a⁻¹) * a := by group
              _ = o * a := by rw [e1]
          have hbo : b * o = o * b := (hcomm o (hOA ho) b hb).symm
          calc a * (o * b) * 1 = (a * o) * b := by group
            _ = o * (a * b) := by rw [this]; group
  have hoZ : o ∈ Z := hZcen o (hOP ho) (fun y hy => hoc y hy)
  have ho'Z : o' ∈ Z := by
    have := mul_mem (inv_mem hoZ) hu
    simpa using this
  exact mul_mem (mem_sup_left ⟨ho, hoZ⟩) (mem_sup_right ⟨ho', ho'Z⟩)

theorem le_commutator_of_complement {X Λ A : Subgroup G} {T : Type*} [Group T]
    (h : IsQuotientIso Λ X T) (hT : Group.IsPerfect T) (hXΛ : X ≤ Λ) (hAΛ : A ≤ Λ)
    (hAX : A ⊓ X = ⊥) (hΛA : Λ ≤ A ⊔ X) (hAN : A ≤ normalizer (X : Set G)) : A ≤ ⁅A, A⁆ := by
  obtain ⟨φ, hφ, hker⟩ := h
  have hmk : ∀ δ : Λ, (δ : G) ∈ X → φ δ = 1 := fun δ hδ => by
    have : δ ∈ φ.ker := by rw [hker]; exact hδ
    exact this
  let ψ : A →* T := φ.comp (Subgroup.inclusion hAΛ)
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨x, rfl⟩ := hφ s
    obtain ⟨a, ha, δ, hδ, hx⟩ := (mem_sup_iff_of_le_normalizer hAN).1 (hΛA x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have hxe : x = ⟨a, hAΛ ha⟩ * ⟨δ, hXΛ hδ⟩ := Subtype.ext hx
    change φ ⟨a, hAΛ ha⟩ = φ x
    rw [hxe, map_mul, hmk ⟨δ, hXΛ hδ⟩ hδ, mul_one]
  have hψk : ψ.ker = (⊥ : Subgroup G).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxX : (x : G) ∈ X := by
        have : (⟨x, hAΛ x.2⟩ : Λ) ∈ φ.ker := hx
        rw [hker] at this
        exact this
      have : (x : G) ∈ A ⊓ X := ⟨x.2, hxX⟩
      rw [hAX] at this
      exact this
    · intro hx
      have hx1 : x = 1 := Subtype.ext hx
      rw [hx1, map_one]
  have := TrialityD4.ProductCase.ProductDecompAux.le_commutator_sup_of_isQuotientIso
    ⟨ψ, hψ, hψk⟩ hT
  simpa using this

theorem normalizer_le_normalizer_normalClosure {X Y : Subgroup G}
    (hY : Y ≤ normalizer (X : Set G)) :
    normalizer (X : Set G) ≤ normalizer
      ((Common.RankOneLayerRadical.normalClosureInNormalizer X Y : Subgroup G) : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    (Common.RankOneLayerRadical.normalClosureInNormalizer_le_normalizer hY)).1
    (Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hY)

end Generic

section Sl2

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {N D K K' : Subgroup G}

theorem mem_normalizer_of_odd_pow (hS : Sl2Pair F N D K K') {g : G}
    (hgN : g ∈ normalizer (N : Set G)) (hgD : g ∈ normalizer (D : Set G)) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m ∈ normalizer (K : Set G)) : g ∈ normalizer (K : Set G) :=
  mem_normalizer_of_pow_mem hS.ne (TrialityD4.ProductCase.ProductN1SylowAux.Sl2Pair.conj_factor
    hS hgN hgD) (TrialityD4.ProductCase.ProductN1SylowAux.Sl2Pair.conj_factor hS.symm hgN hgD).symm
    hm hgm

theorem le_normalizer_of_odd_card (hS : Sl2Pair F N D K K') {J : Subgroup G}
    (hJN : J ≤ normalizer (N : Set G)) (hJD : J ≤ normalizer (D : Set G))
    (hodd : Odd (Nat.card J)) : J ≤ normalizer (K : Set G) := fun g hg => by
  refine mem_normalizer_of_odd_pow hS (hJN hg) (hJD hg) hodd ?_
  have h1 : (⟨g, hg⟩ : J) ^ Nat.card J = 1 := pow_card_eq_one'
  have h2 : g ^ Nat.card J = 1 := by
    have := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [h2]
  exact one_mem _

theorem mem_normalizer_of_mem_normalizer_sylow (hS : Sl2Pair F N D K K') {N₂ P : Subgroup G}
    (hP₁ : P ≤ N) (hP₂ : IsSylowOf 2 P N₂) {g : G} (hg₂ : g ∈ N₂)
    (hgP : g ∈ normalizer (P : Set G)) (hgN : g ∈ normalizer (N : Set G))
    (hgD : g ∈ normalizer (D : Set G)) : g ∈ normalizer (K : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : P ≤ N₂ ⊓ normalizer (P : Set G) := le_inf hP₂.le Subgroup.le_normalizer
  have h2 : ¬ 2 ∣ P.relIndex N₂ := ((CFSG.ABGLocalTools.isSylowOf_iff).1 hP₂).2.2
  have hdvd : P.relIndex (N₂ ⊓ normalizer (P : Set G)) ∣ P.relIndex N₂ :=
    ⟨_, (Subgroup.relIndex_mul_relIndex P (N₂ ⊓ normalizer (P : Set G)) N₂ hM inf_le_left).symm⟩
  have hodd : Odd (P.relIndex (N₂ ⊓ normalizer (P : Set G))) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => h2 (h.trans hdvd))
  have hpow : g ^ P.relIndex (N₂ ⊓ normalizer (P : Set G)) ∈ P :=
    pow_relIndex_mem hM inf_le_right ⟨hg₂, hgP⟩
  exact mem_normalizer_of_odd_pow hS hgN hgD hodd (hS.le_normalizer (hP₁ hpow))

theorem le_commutator_borel (hS : Sl2Pair F N D K K') {P A : Subgroup G}
    (hP : IsSylowOf 2 P N) (hDP : D ≤ P) (hAK : A ≤ K) (hAD : A ⊓ D = ⊥) (hKA : K ≤ A ⊔ D) :
    P ⊓ A ≤ ⁅P ⊓ A, A ⊓ normalizer ((P ⊓ A : Subgroup G) : Set G)⁆ := by
  haveI := hS.charTwo
  obtain ⟨ψ, hψ⟩ := TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.exists_qupData_sylow hS hP hDP
  set T : Subgroup G := P ⊓ A with hT
  set R : Subgroup G := A ⊓ normalizer (T : Set G) with hR
  have hDK : D ≤ K := TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.D_le_left hS
  have hKN : K ≤ normalizer (D : Set G) := fun x hx =>
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS
      (TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.left_le hS hx)
  have hAD' : A ≤ normalizer (D : Set G) := hAK.trans hKN
  have hTA : T ≤ A := inf_le_right
  have hKeq : K = A ⊔ D := le_antisymm hKA (sup_le hAK hDK)
  have hPK : P ⊓ K = T ⊔ D := by
    rw [hKeq]
    exact ProductDecompAux.inf_sup_eq_of_le_of_le_normalizer hDP hAD'
  have hex : ∃ a ∈ T, a ∉ D := by
    by_contra hcon
    push Not at hcon
    have hle : P ⊓ K ≤ D := by
      rw [hPK]
      exact sup_le (fun x hx => hcon x hx) le_rfl
    have h1 := Subgroup.relIndex_eq_one.2 hle
    rw [TrialityD4.ProductCase.ProductN1SylowAux.Sl2Pair.relIndex_sylow hS hP hDP] at h1
    have := hS.four_le
    omega
  obtain ⟨a, haT, haD⟩ := hex
  have haPK : a ∈ P ⊓ K := ⟨haT.1, hAK haT.2⟩
  set W : Subgroup G := ⁅T, R⁆ ⊔ D with hW
  have hdec : ∀ k : G, k ∈ K → k ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) →
      ∃ α ∈ R, ∃ δ ∈ D, k = α * δ := by
    intro k hk hkN
    obtain ⟨α, hα, δ, hδ, hkαδ⟩ := (mem_sup_iff_of_le_normalizer hAD').1 (hKA hk)
    have hδN : δ ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) :=
      Subgroup.le_normalizer ⟨hDP hδ, hDK hδ⟩
    have hαN : α ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) := by
      have := mul_mem hkN (inv_mem hδN)
      rwa [hkαδ, mul_inv_cancel_right] at this
    have hαT : α ∈ normalizer (T : Set G) := by
      have := Common.mem_normalizer_inf hαN (Subgroup.le_normalizer hα)
      have e : (P ⊓ K) ⊓ A = T := by
        rw [hT, inf_assoc, inf_eq_right.2 hAK]
      rwa [e] at this
    exact ⟨α, ⟨hα, hαT⟩, δ, hδ, hkαδ⟩
  have hWnorm : ∀ k : K, ψ k ∈ GH74.GLS.IVK.Proofs2.Bor F → (k : G) ∈ normalizer (W : Set G) := by
    intro k hk
    have hkN := (hψ.mem_normalizer_iff_mem_Bor k).2 hk
    obtain ⟨α, hαR, δ, hδ, hkαδ⟩ := hdec k k.2 hkN
    have hαW : α ∈ normalizer (W : Set G) :=
      Common.mem_normalizer_sup
        (mem_normalizer_commutator_of_mem hαR.2 (Subgroup.le_normalizer hαR))
        (hAD' hαR.1)
    rw [hkαδ]
    exact mul_mem hαW (Subgroup.le_normalizer (Subgroup.mem_sup_right hδ))
  have hWcomm : ∀ k : K, ψ k ∈ GH74.GLS.IVK.Proofs2.Bor F →
      (k : G) * a * (k : G)⁻¹ * a⁻¹ ∈ W := by
    intro k hk
    have hkN := (hψ.mem_normalizer_iff_mem_Bor k).2 hk
    obtain ⟨α, hαR, δ, hδ, hkαδ⟩ := hdec k k.2 hkN
    have hαa : α * a * α⁻¹ * a⁻¹ ∈ ⁅T, R⁆ := by
      have h1 : a * α * a⁻¹ * α⁻¹ ∈ ⁅T, R⁆ := Subgroup.commutator_mem_commutator haT hαR
      have h2 := inv_mem h1
      have e : (a * α * a⁻¹ * α⁻¹)⁻¹ = α * a * α⁻¹ * a⁻¹ := by group
      rwa [e] at h2
    have hd₁ : δ * a * δ⁻¹ * a⁻¹ ∈ D := by
      have := mul_mem hδ ((mem_normalizer_iff.1 (hKN (hAK haT.2)) δ⁻¹).1 (inv_mem hδ))
      simpa [mul_assoc] using this
    have hd₂ : α * (δ * a * δ⁻¹ * a⁻¹) * α⁻¹ ∈ D :=
      (mem_normalizer_iff.1 (hAD' hαR.1) _).1 hd₁
    have e : (k : G) * a * (k : G)⁻¹ * a⁻¹ =
        (α * (δ * a * δ⁻¹ * a⁻¹) * α⁻¹) * (α * a * α⁻¹ * a⁻¹) := by
      rw [hkαδ]; group
    rw [e]
    exact mul_mem (mem_sup_right hd₂) (mem_sup_left hαa)
  have hle := hψ.le_of_comm hS.four_le haPK haD (le_sup_right : D ≤ W) hWnorm hWcomm
  intro x hx
  have hxW : x ∈ W := hle ⟨hx.1, hAK hx.2⟩
  have hcT : ⁅T, R⁆ ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.1 inf_le_right
  have hcN : ⁅T, R⁆ ≤ normalizer (D : Set G) := hcT.trans (hTA.trans hAD')
  obtain ⟨c, hc, δ, hδ, rfl⟩ := (mem_sup_iff_of_le_normalizer hcN).1 hxW
  have hδT : δ ∈ T := by
    have := mul_mem (inv_mem (hcT hc)) hx
    simpa using this
  have hδ1 : δ ∈ A ⊓ D := ⟨hTA hδT, hδ⟩
  rw [hAD, Subgroup.mem_bot] at hδ1
  rw [hδ1, mul_one]
  exact hc

theorem inf_normalizer_le_normalizer_sylow (hS : Sl2Pair F N D K K') {P A : Subgroup G}
    (hP : IsSylowOf 2 P N) (hDP : D ≤ P) (hAK : A ≤ K) (hKA : K ≤ A ⊔ D) :
    A ⊓ normalizer ((P ⊓ A : Subgroup G) : Set G) ≤ normalizer (P : Set G) := by
  obtain ⟨-, -, hPeq, -, -⟩ := sylow_prod hP hS.sup_eq hS.inf_eq hS.comm_le hDP
  intro α hα
  have hDK : D ≤ K := TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.D_le_left hS
  have hKN : K ≤ normalizer (D : Set G) := fun x hx =>
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS
      (TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.left_le hS hx)
  have hαK : α ∈ K := hAK hα.1
  have h1 : α ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) := by
    have hKeq : K = A ⊔ D := le_antisymm hKA (sup_le hAK hDK)
    have hPK : P ⊓ K = (P ⊓ A) ⊔ D := by
      rw [hKeq]
      exact ProductDecompAux.inf_sup_eq_of_le_of_le_normalizer hDP (hAK.trans hKN)
    rw [hPK]
    exact Common.mem_normalizer_sup hα.2 (hKN hαK)
  have h2 : α ∈ normalizer ((P ⊓ K' : Subgroup G) : Set G) :=
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.right_mem_normalizer_inf hS.symm hDP hαK
  rw [hPeq]
  exact Common.mem_normalizer_sup h1 h2

theorem sl2Pair_of_isFactor {X N Λ : Subgroup G} {t : G} [CharP F 2]
    (hΛ : IsFactor X N Λ t F) (htX : t ∈ normalizer (X : Set G)) (hF : 4 ≤ Nat.card F) :
    Sl2Pair F N X Λ (Λᵍ[t]) where
  charTwo := inferInstance
  four_le := hF
  sup_eq := hΛ.sup
  inf_eq := hΛ.inf
  comm_le := hΛ.comm
  isoK := hΛ.quot
  isoK' := by
    have := TrialityD4.ProductCase.ProductN1SylowAux.IsQuotientIso.conj hΛ.quot t
    rwa [TrialityD4.ProductCase.ProductDecompAux.conjT_eq_of_mem_normalizer htX] at this

theorem card_inf_complement (hS : Sl2Pair F N D K K') {P A : Subgroup G} {q : ℕ}
    (hP : IsSylowOf 2 P N) (hDP : D ≤ P) (hqF : Nat.card F = q) (hAK : A ≤ K)
    (hAD : A ⊓ D = ⊥) (hKA : K ≤ A ⊔ D) : Nat.card (P ⊓ A : Subgroup G) = q := by
  have hDK : D ≤ K := TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.D_le_left hS
  have hKN : K ≤ normalizer (D : Set G) := fun x hx =>
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS
      (TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.left_le hS hx)
  have hKeq : K = A ⊔ D := le_antisymm hKA (sup_le hAK hDK)
  have hP₂eq : P ⊓ K = D ⊔ (P ⊓ A) := by
    rw [hKeq, inf_sup_eq_of_le_of_le_normalizer hDP (hAK.trans hKN), sup_comm]
  have hrel := TrialityD4.ProductCase.ProductN1SylowAux.Sl2Pair.relIndex_sylow hS hP hDP
  have h1 := Subgroup.relIndex_mul_card D (P ⊓ K)
  rw [inf_eq_left.2 (le_inf hDP hDK), hrel, hqF, hP₂eq] at h1
  have hTN : P ⊓ A ≤ normalizer (D : Set G) := (inf_le_right.trans hAK).trans hKN
  have h2 := Common.card_sup_mul_card_inf_eq hTN
  have hinf : D ⊓ (P ⊓ A) = ⊥ :=
    le_bot_iff.1 (le_trans (le_inf (inf_le_right.trans inf_le_right) inf_le_left) hAD.le)
  rw [hinf] at h2
  simp only [Subgroup.card_bot, mul_one] at h2
  rw [h2] at h1
  have hpos : 0 < Nat.card D := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (mul_comm _ _))

end Sl2

section Stages

variable {G : Type} [Group G] [Finite G]

theorem nat_aux {q a x : ℕ} (hq : 0 < q) (ha : a ≤ q) (hx : 0 < x) (h : q ^ 2 * x = a * a) :
    x = 1 ∧ a = q := by
  have hq2 : 0 < q ^ 2 := by positivity
  have h1 : a * a ≤ q ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul ha ha
  have hx1 : x = 1 := by
    have : q ^ 2 * x ≤ q ^ 2 * 1 := by rw [h, mul_one]; exact h1
    have := Nat.le_of_mul_le_mul_left this hq2
    omega
  refine ⟨hx1, ?_⟩
  subst hx1
  have h2 : a * a = q * q := by rw [← h, pow_two]; ring
  exact Nat.mul_self_inj.1 h2

theorem stage_U {P A O U : Subgroup G} {t : G} {q : ℕ} (ht : t * t = 1)
    (hAB : A ⊓ Aᵍ[t] = ⊥) (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (hPA : P ≤ A ⊔ Aᵍ[t])
    (hOA : O ≤ A) (hAO : A ≤ normalizer (O : Set G)) (hOi : O ⊓ Oᵍ[t] = ⊥)
    (hOP : O ≤ P) (hOtP : Oᵍ[t] ≤ P) (hUO : U ≤ O ⊔ Oᵍ[t]) (hUt : Uᵍ[t] = U)
    (hZPc : ∀ z ∈ U, ∀ y ∈ P, y * z = z * y)
    (hZcen : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ U) (hUcard : Nat.card U = q ^ 2) :
    U = (O ⊓ U) ⊔ (O ⊓ U)ᵍ[t] ∧ (O ⊓ U) ⊓ (O ⊓ U)ᵍ[t] = ⊥ ∧
      ⁅O ⊓ U, (O ⊓ U)ᵍ[t]⁆ = ⊥ ∧ Nat.card (O ⊓ U : Subgroup G) = q := by
  have hOtA : Oᵍ[t] ≤ Aᵍ[t] := Subgroup.map_mono hOA
  have hsplit : U ≤ (O ⊓ U) ⊔ (Oᵍ[t] ⊓ U) :=
    decomp_center ht hAB hc hPA hOA hAO hOP hOtP hUO hZPc hZcen
  have hHt : (O ⊓ U)ᵍ[t] = Oᵍ[t] ⊓ U := by
    rw [TrialityD4.ProductCase.ProductDecompAux.conjT_inf, hUt]
  rw [← hHt] at hsplit
  have hUH : U = (O ⊓ U) ⊔ (O ⊓ U)ᵍ[t] :=
    le_antisymm hsplit (sup_le inf_le_right (hHt ▸ inf_le_right))
  have hHHt : (O ⊓ U) ⊓ (O ⊓ U)ᵍ[t] = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hOi]
    exact inf_le_inf inf_le_left (hHt ▸ inf_le_left)
  have hHc : ⁅O ⊓ U, (O ⊓ U)ᵍ[t]⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hc]
    exact Subgroup.commutator_mono (inf_le_left.trans hOA)
      (Subgroup.map_mono (inf_le_left.trans hOA))
  refine ⟨hUH, hHHt, hHc, ?_⟩
  have h1 := card_sup_of_commute hHc hHHt
  rw [← hUH, hUcard, TrialityD4.ProductCase.ProductDecompAux.card_conjT] at h1
  have h2 : Nat.card (O ⊓ U : Subgroup G) ^ 2 = q ^ 2 := by rw [pow_two, ← h1, pow_two]
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2

theorem stage_T₂Q {F : Type} [Field F] [Finite F] {N D K K' P A Q Z : Subgroup G}
    (hS : Sl2Pair F N D K K') (hP : IsSylowOf 2 P N) (hDP : D ≤ P) (hAK : A ≤ K)
    (hAD : A ⊓ D = ⊥) (hKA : K ≤ A ⊔ D)
    (hRQ : ∀ g ∈ A ⊓ normalizer ((P ⊓ A : Subgroup G) : Set G), g ∈ normalizer (Q : Set G))
    (hZN : Z ≤ normalizer (Q : Set G)) (hZc : Z ≤ centralizer (A : Set G))
    (hTQZ : P ⊓ A ≤ Q ⊔ Z) : P ⊓ A ≤ Q := by
  refine (le_commutator_borel hS hP hDP hAK hAD hKA).trans ?_
  rw [Subgroup.commutator_le]
  intro x hx g hg
  obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer' hZN).1 (hTQZ hx)
  have hzg : g * z = z * g := mem_centralizer_iff.1 (hZc hz) g hg.1
  rw [commutatorElement_def]
  have e : (y * z) * g * (y * z)⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by
    calc (y * z) * g * (y * z)⁻¹ * g⁻¹ = y * (z * g) * z⁻¹ * y⁻¹ * g⁻¹ := by group
      _ = y * (g * z) * z⁻¹ * y⁻¹ * g⁻¹ := by rw [← hzg]
      _ = y * (g * y⁻¹ * g⁻¹) := by group
  rw [e]
  exact mul_mem hy ((mem_normalizer_iff.1 (hRQ g hg) y⁻¹).1 (inv_mem hy))

theorem stage_Q {F : Type} [Field F] [Finite F] {N₂ M6 Λ₂ P A₂ K2 O Q U Ht : Subgroup G}
    {t : G} {q : ℕ} (hS₂ : Sl2Pair F N₂ M6 Λ₂ (Λ₂ᵍ[t])) (hP₂ : IsSylowOf 2 P N₂)
    (hM6P : M6 ≤ P) (hqF : Nat.card F = q) (hA₂Λ : A₂ ≤ Λ₂) (hA₂M : A₂ ⊓ M6 = ⊥)
    (hΛA₂ : Λ₂ ≤ A₂ ⊔ M6) (hI₂ : K2 ⊓ K2ᵍ[t] = ⊥) (hc₂ : ⁅K2, K2ᵍ[t]⁆ = ⊥)
    (hA₂K : A₂ ≤ K2) (hOK : O ≤ K2) (hKO : K2 ≤ normalizer (O : Set G))
    (hM6O : O ⊔ Oᵍ[t] = M6) (hOi : O ⊓ Oᵍ[t] = ⊥) (hM6card : Nat.card M6 = q ^ 10)
    (hT₂Q : P ⊓ A₂ ≤ Q) (hOQ : O ≤ Q) (hHtU : Ht ≤ U) (hUQ : U ≤ Q) (hHtO : Ht ≤ Oᵍ[t])
    (hHtcard : Nat.card Ht = q) (hQcard : Nat.card Q = q ^ 7) :
    Q = ((P ⊓ A₂) ⊔ O) ⊔ Ht ∧ ((P ⊓ A₂) ⊔ O) ⊓ Ht = ⊥ ∧ ⁅(P ⊓ A₂) ⊔ O, Ht⁆ = ⊥ ∧
      Nat.card (P ⊓ A₂ : Subgroup G) = q ∧ Nat.card O = q ^ 5 ∧
      Nat.card ((P ⊓ A₂) ⊔ O : Subgroup G) = q ^ 6 := by
  have hΛ₂N : Λ₂ ≤ N₂ := TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.left_le hS₂
  have hM6Λ : M6 ≤ Λ₂ := TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.D_le_left hS₂
  have hN₂M : N₂ ≤ normalizer (M6 : Set G) :=
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS₂
  have hT₂A₂ : P ⊓ A₂ ≤ A₂ := inf_le_right
  have hOM6 : O ≤ M6 := hM6O ▸ le_sup_left
  have hOc : ⁅O, Oᵍ[t]⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hc₂]
    exact Subgroup.commutator_mono hOK (Subgroup.map_mono hOK)
  have hOcard : Nat.card O = q ^ 5 := by
    have h1 := card_sup_of_commute hOc hOi
    rw [hM6O, hM6card, TrialityD4.ProductCase.ProductDecompAux.card_conjT] at h1
    have h2 : Nat.card O ^ 2 = (q ^ 5) ^ 2 := by
      calc Nat.card O ^ 2 = Nat.card O * Nat.card O := pow_two _
        _ = q ^ 10 := h1.symm
        _ = (q ^ 5) ^ 2 := by ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  have hT₂card : Nat.card (P ⊓ A₂ : Subgroup G) = q :=
    card_inf_complement hS₂ hP₂ hM6P hqF hA₂Λ hA₂M hΛA₂
  have hT₂N : P ⊓ A₂ ≤ normalizer (O : Set G) := (inf_le_right.trans hA₂K).trans hKO
  have hI₂K : (P ⊓ A₂) ⊔ O ≤ K2 := sup_le (inf_le_right.trans hA₂K) hOK
  have hI₂card : Nat.card ((P ⊓ A₂) ⊔ O : Subgroup G) = q ^ 6 := by
    have h2 := Common.card_sup_mul_card_inf_eq hT₂N
    have hinf : O ⊓ (P ⊓ A₂) = ⊥ :=
      le_bot_iff.1 (le_trans (le_inf (inf_le_right.trans hT₂A₂) (inf_le_left.trans hOM6))
        hA₂M.le)
    rw [hinf, ← sup_comm] at h2
    simp only [Subgroup.card_bot, mul_one] at h2
    rw [h2, hOcard, hT₂card]
    ring
  have hHtK : Ht ≤ K2ᵍ[t] := hHtO.trans (Subgroup.map_mono hOK)
  have hI₂Ht : ((P ⊓ A₂) ⊔ O) ⊓ Ht = ⊥ := le_bot_iff.1 (hI₂ ▸ inf_le_inf hI₂K hHtK)
  have hI₂Htc : ⁅(P ⊓ A₂) ⊔ O, Ht⁆ = ⊥ :=
    le_bot_iff.1 (hc₂ ▸ Subgroup.commutator_mono hI₂K hHtK)
  have hIHt : Nat.card (((P ⊓ A₂) ⊔ O) ⊔ Ht : Subgroup G) = q ^ 7 := by
    rw [card_sup_of_commute hI₂Htc hI₂Ht, hI₂card, hHtcard]
    ring
  have hle : ((P ⊓ A₂) ⊔ O) ⊔ Ht ≤ Q := sup_le (sup_le hT₂Q hOQ) (hHtU.trans hUQ)
  have hQeq : ((P ⊓ A₂) ⊔ O) ⊔ Ht = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hIHt])
  exact ⟨hQeq.symm, hI₂Ht, hI₂Htc, hT₂card, hOcard, hI₂card⟩

theorem stage_inter {N₁ K1p U H Ht P : Subgroup G} {t : G} {q : ℕ} (ht : t * t = 1)
    (hN₁ : N₁ = ⁅K1p, K1p⁆ ⊔ (⁅K1p, K1p⁆)ᵍ[t]) (hN₁' : N₁ = K1p ⊔ K1pᵍ[t])
    (hK1p : K1p ⊓ K1pᵍ[t] = U) (hK1c : ⁅K1p, K1pᵍ[t]⁆ ≤ U)
    (hUN₁ : ∀ x ∈ U, ∀ y ∈ N₁, y * x = x * y) (hperf : ⁅K1p, K1p⁆ ⊔ U = K1p)
    (hUH : U = H ⊔ Ht) (hUcard : Nat.card U = q ^ 2) (hHtcard : Nat.card Ht = q)
    (hHtU : Ht ≤ U) (hK1ppHt : ⁅K1p, K1p⁆ ⊓ Ht = ⊥) (hUt : Uᵍ[t] = U) (hUP : U ≤ P)
    (hZPc : ∀ z ∈ U, ∀ y ∈ P, y * z = z * y) (hUp : Uᵍ[t] ≤ P) :
    ⁅⁅K1p, K1p⁆, (⁅K1p, K1p⁆)ᵍ[t]⁆ = ⊥ ∧ ⁅K1p, K1p⁆ ⊓ (⁅K1p, K1p⁆)ᵍ[t] = ⊥ ∧
      K1p = ⁅K1p, K1p⁆ ⊔ Ht := by
  have hK1N₁ : K1p ≤ N₁ := hN₁' ▸ le_sup_left
  have hK1tN₁ : K1pᵍ[t] ≤ N₁ := hN₁' ▸ le_sup_right
  have hUc : U ≤ centralizer (K1p : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hUN₁ x hx y (hK1N₁ hy)
  have hK1pp_le : ⁅K1p, K1p⁆ ≤ K1p := TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _
  have h1 : ⁅⁅K1p, K1pᵍ[t]⁆, K1p⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    have : ⁅⁅K1p, K1pᵍ[t]⁆, K1p⁆ ≤ ⁅U, K1p⁆ := Subgroup.commutator_mono hK1c le_rfl
    rwa [commutator_eq_bot_iff_le_centralizer.2 hUc] at this
  have h2 : ⁅⁅K1pᵍ[t], K1p⁆, K1p⁆ = ⊥ := by rw [Subgroup.commutator_comm K1pᵍ[t] K1p]; exact h1
  have h3 : ⁅⁅K1p, K1p⁆, K1pᵍ[t]⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hcomm : ⁅⁅K1p, K1p⁆, (⁅K1p, K1p⁆)ᵍ[t]⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← h3]
    exact Subgroup.commutator_mono le_rfl (Subgroup.map_mono hK1pp_le)
  refine ⟨hcomm, ?_⟩
  set A : Subgroup G := ⁅K1p, K1p⁆ ⊓ U with hA
  have hAU : A ≤ U := inf_le_right
  have hAtU : Aᵍ[t] ≤ U := by rw [← hUt]; exact Subgroup.map_mono hAU
  have hUnorm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => (hZPc a ha b (hUP hb)).symm
  have hUK1 : U ≤ K1p := by rw [← hK1p]; exact inf_le_left
  have hUK1t : U ≤ K1pᵍ[t] := by rw [← hK1p]; exact inf_le_right
  have hAt : Aᵍ[t] = (⁅K1p, K1p⁆)ᵍ[t] ⊓ U := by
    rw [hA, TrialityD4.ProductCase.ProductDecompAux.conjT_inf, hUt]
  have hUsup : U ≤ A ⊔ Aᵍ[t] := by
    intro u hu
    have hcm : ∀ a ∈ ⁅K1p, K1p⁆, ∀ b ∈ (⁅K1p, K1p⁆)ᵍ[t], a * b = b * a :=
      TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.1 hcomm
    have huN : u ∈ ⁅K1p, K1p⁆ ⊔ (⁅K1p, K1p⁆)ᵍ[t] := by
      rw [← hN₁]
      exact hK1N₁ (hUK1 hu)
    obtain ⟨k, hk, k', hk', hkk⟩ :=
      (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute hcm).1 huN
    have hkK1t : k ∈ K1pᵍ[t] := by
      have : k = u * k'⁻¹ := by rw [← hkk]; group
      rw [this]
      exact mul_mem (hUK1t hu) (inv_mem (Subgroup.map_mono hK1pp_le hk'))
    have hkU : k ∈ U := by
      rw [← hK1p]
      exact ⟨hK1pp_le hk, hkK1t⟩
    have hk'U : k' ∈ U := by
      have : k' = k⁻¹ * u := by rw [← hkk]; group
      rw [this]
      exact mul_mem (inv_mem hkU) hu
    rw [← hkk]
    exact mul_mem (mem_sup_left ⟨hk, hkU⟩) (mem_sup_right (hAt ▸ ⟨hk', hk'U⟩))
  have hq : 0 < q := hHtcard ▸ Nat.card_pos
  have hHtcom : ⁅A, Ht⁆ = ⊥ :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.2 fun a ha b hb =>
      (hZPc a (hAU ha) b (hUP (hHtU hb))).symm
  have hAHt : A ⊓ Ht = ⊥ := le_bot_iff.1 (hK1ppHt ▸ inf_le_inf inf_le_left le_rfl)
  have hAcard : Nat.card A ≤ q := by
    have h1 := card_sup_of_commute hHtcom hAHt
    have h2 : Nat.card (A ⊔ Ht : Subgroup G) ≤ Nat.card U :=
      Subgroup.card_le_of_le (sup_le hAU hHtU)
    rw [h1, hHtcard, hUcard, pow_two] at h2
    exact Nat.le_of_mul_le_mul_right h2 hq
  have hAtcard : Nat.card Aᵍ[t] = Nat.card A :=
    TrialityD4.ProductCase.ProductDecompAux.card_conjT t A
  have hAAt : ⁅A, Aᵍ[t]⁆ = ⊥ :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.2 fun a ha b hb =>
      (hZPc a (hAU ha) b (hUP (hAtU hb))).symm
  have hsupU : A ⊔ Aᵍ[t] = U := le_antisymm (sup_le hAU hAtU) hUsup
  have hAtN : Aᵍ[t] ≤ normalizer (A : Set G) := by
    have := hAAt
    rw [Subgroup.commutator_comm] at this
    exact (commutator_eq_bot_iff_le_centralizer.1 this).trans
      (Subgroup.centralizer_le_normalizer _)
  have hprod := Common.card_sup_mul_card_inf_eq hAtN
  rw [hsupU, hUcard, hAtcard] at hprod
  obtain ⟨hAA, hAcard'⟩ := nat_aux hq hAcard Nat.card_pos hprod
  have hinfA : A ⊓ Aᵍ[t] = ⊥ := Subgroup.eq_bot_of_card_eq _ hAA
  have hle : ⁅K1p, K1p⁆ ⊓ (⁅K1p, K1p⁆)ᵍ[t] ≤ U :=
    (inf_le_inf hK1pp_le (Subgroup.map_mono hK1pp_le)).trans hK1p.le
  have hK1ppK1ppt : ⁅K1p, K1p⁆ ⊓ (⁅K1p, K1p⁆)ᵍ[t] = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hinfA]
    exact le_inf (le_inf inf_le_left hle) (hAt ▸ le_inf inf_le_right hle)
  have hUAHt : A ⊔ Ht = U := by
    have h1 := card_sup_of_commute hHtcom hAHt
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAU hHtU) ?_
    rw [h1, hAcard', hHtcard, hUcard, pow_two]
  have hUle : U ≤ ⁅K1p, K1p⁆ ⊔ Ht :=
    hUAHt.symm.le.trans (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
  refine ⟨hK1ppK1ppt, le_antisymm ?_ (sup_le hK1pp_le (hHtU.trans hUK1))⟩
  calc K1p = ⁅K1p, K1p⁆ ⊔ U := hperf.symm
    _ ≤ ⁅K1p, K1p⁆ ⊔ Ht := sup_le le_sup_left hUle

theorem stage_count {I₁ I₂ T₁ T₂ E D M : Subgroup G} {q : ℕ}
    (hI₁ : Nat.card I₁ = q ^ 6) (hI₂ : Nat.card I₂ = q ^ 6) (hE : Nat.card E = q ^ 4)
    (hT₂ : Nat.card T₂ = q) (hT₁ : Nat.card T₁ = q)
    (hE₁ : E = ⁅I₁, I₁⁆) (hE₂ : E = ⁅I₂, I₂⁆)
    (hT₁I₁ : T₁ ≤ I₁) (hT₂I₁ : T₂ ≤ I₁) (hT₁I₂ : T₁ ≤ I₂) (hT₂I₂ : T₂ ≤ I₂)
    (hED : E ≤ D) (hEM : E ≤ M) (hT₂D : T₂ ≤ D) (hT₁D : T₁ ⊓ D = ⊥) (hT₂M : T₂ ⊓ M = ⊥) :
    I₁ = I₂ := by
  have hEN : I₁ ≤ normalizer (E : Set G) := fun g hg => by
    rw [hE₁]
    exact TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator
      (Subgroup.le_normalizer hg)
  have hEI₁ : E ≤ I₁ := hE₁ ▸ TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _
  have hEI₂ : E ≤ I₂ := hE₂ ▸ TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _
  set C : Subgroup G := T₂ ⊔ E with hC
  have hCN : T₂ ≤ normalizer (E : Set G) := hT₂I₁.trans hEN
  have hCcard : Nat.card C = q ^ 5 := by
    have h2 := Common.card_sup_mul_card_inf_eq hCN
    have hinf : E ⊓ T₂ = ⊥ :=
      le_bot_iff.1 (le_trans (le_inf inf_le_right (inf_le_left.trans hEM)) hT₂M.le)
    rw [hinf, ← sup_comm] at h2
    simp only [Subgroup.card_bot, mul_one] at h2
    rw [hC, h2, hE, hT₂]
    ring
  have hCI₁ : C ≤ I₁ := sup_le hT₂I₁ hEI₁
  have hCI₂ : C ≤ I₂ := sup_le hT₂I₂ hEI₂
  have hCD : C ≤ D := sup_le hT₂D hED
  have hT₁N : T₁ ≤ normalizer (C : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx c hc => ?_
    have h1 : x * c * x⁻¹ * c⁻¹ ∈ ⁅I₁, I₁⁆ :=
      Subgroup.commutator_mem_commutator (hT₁I₁ hx) (hCI₁ hc)
    rw [← hE₁] at h1
    exact (le_sup_right : E ≤ C) h1
  have hsupcard : Nat.card (C ⊔ T₁ : Subgroup G) = q ^ 6 := by
    have h2 := Common.card_sup_mul_card_inf_eq hT₁N
    have hinf : C ⊓ T₁ = ⊥ :=
      le_bot_iff.1 (le_trans (inf_le_inf hCD le_rfl) (by rw [inf_comm]; exact hT₁D.le))
    rw [hinf] at h2
    simp only [Subgroup.card_bot, mul_one] at h2
    rw [h2, hCcard, hT₁]
    ring
  have hle₁ : C ⊔ T₁ ≤ I₁ := sup_le hCI₁ hT₁I₁
  have hle₂ : C ⊔ T₁ ≤ I₂ := sup_le hCI₂ hT₁I₂
  have e₁ : C ⊔ T₁ = I₁ := Subgroup.eq_of_le_of_card_ge hle₁ (by rw [hsupcard, hI₁])
  have e₂ : C ⊔ T₁ = I₂ := Subgroup.eq_of_le_of_card_ge hle₂ (by rw [hsupcard, hI₂])
  rw [← e₁, ← e₂]

theorem stage_one {K1p A₁ D7 N₁ : Subgroup G} {t : G}
    (hK1A : K1p = A₁ ⊔ pCoreOf 2 K1p) (hA₁K : A₁ ≤ ⁅A₁, A₁⁆)
    (hN₁ : N₁ = ⁅K1p, K1p⁆ ⊔ (⁅K1p, K1p⁆)ᵍ[t])
    (hinf : ⁅K1p, K1p⁆ ⊓ (⁅K1p, K1p⁆)ᵍ[t] = ⊥)
    (hcomm : ⁅⁅K1p, K1p⁆, (⁅K1p, K1p⁆)ᵍ[t]⁆ = ⊥)
    (hD7N₁ : D7 ≤ N₁) (hN₁D7 : N₁ ≤ normalizer (D7 : Set G)) (hD7p : IsPGroup 2 D7)
    (hD7t : D7ᵍ[t] = D7) (hB₁D7 : pCoreOf 2 K1p ≤ D7) :
    ⁅K1p, K1p⁆ = A₁ ⊔ pCoreOf 2 ⁅K1p, K1p⁆ ∧
      pCoreOf 2 ⁅K1p, K1p⁆ ⊔ (pCoreOf 2 ⁅K1p, K1p⁆)ᵍ[t] = D7 ∧
      pCoreOf 2 ⁅K1p, K1p⁆ ⊓ (pCoreOf 2 ⁅K1p, K1p⁆)ᵍ[t] = ⊥ := by
  have hpp : ⁅K1p, K1p⁆ ≤ K1p := TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _
  have hA₁K1 : A₁ ≤ K1p := hK1A ▸ le_sup_left
  have hA₁pp : A₁ ≤ ⁅K1p, K1p⁆ := hA₁K.trans (Subgroup.commutator_mono hA₁K1 hA₁K1)
  have hK1N : K1p ≤ normalizer ((⁅K1p, K1p⁆ : Subgroup G) : Set G) := fun g hg =>
    TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator (Subgroup.le_normalizer hg)
  have hpc : pCoreOf 2 ⁅K1p, K1p⁆ = ⁅K1p, K1p⁆ ⊓ pCoreOf 2 K1p :=
    TrialityD4.ProductCase.ProductDecompAux.pCoreOf_eq_inf_of_normal hpp hK1N
  have hOpp : pCoreOf 2 ⁅K1p, K1p⁆ ≤ ⁅K1p, K1p⁆ := LieType.BorelTits.pCoreOf_le 2 _
  have hOD : pCoreOf 2 ⁅K1p, K1p⁆ ≤ D7 := hpc ▸ (inf_le_right.trans hB₁D7)
  refine ⟨?_, ?_, ?_⟩
  · calc ⁅K1p, K1p⁆ = ⁅K1p, K1p⁆ ⊓ K1p := (inf_eq_left.2 hpp).symm
      _ = ⁅K1p, K1p⁆ ⊓ (A₁ ⊔ pCoreOf 2 K1p) := by rw [← hK1A]
      _ = A₁ ⊔ (⁅K1p, K1p⁆ ⊓ pCoreOf 2 K1p) :=
          ProductDecompAux.inf_sup_eq_of_le_of_le_normalizer' hA₁pp
            (hA₁K1.trans (le_normalizer_pCoreOf K1p))
      _ = A₁ ⊔ pCoreOf 2 ⁅K1p, K1p⁆ := by rw [hpc]
  · refine le_antisymm (sup_le hOD (by rw [← hD7t]; exact Subgroup.map_mono hOD)) ?_
    have h1 : D7 ≤ pCoreOf 2 N₁ := le_pCoreOf_of_normal hD7N₁ hN₁D7 hD7p
    rw [hN₁] at h1
    refine h1.trans ((ProductDecompAux.pCoreOf_sup_le_of_commute hcomm hinf).trans ?_)
    rw [TrialityD4.ProductCase.ProductN1SylowAux.pCoreOf_conj]
  · refine le_bot_iff.1 ?_
    rw [← hinf]
    exact inf_le_inf hOpp (Subgroup.map_mono hOpp)

theorem stage_T₁I₂ {Q I₂ Ht T₁ K2 J₃ : Subgroup G} {t : G}
    (hQ : Q = I₂ ⊔ Ht) (hT₁Q : T₁ ≤ Q) (hI₂K : I₂ ≤ K2) (hHtK : Ht ≤ K2ᵍ[t])
    (hinf : K2 ⊓ K2ᵍ[t] = ⊥) (hI₂Htc : ⁅I₂, Ht⁆ = ⊥)
    (hJK : ∀ c ∈ J₃, c ∈ normalizer (K2 : Set G))
    (hJKt : ∀ c ∈ J₃, c ∈ normalizer ((K2ᵍ[t] : Subgroup G) : Set G))
    (hT₁c : ∀ c ∈ J₃, ∀ x ∈ T₁, c * x = x * c)
    (hU₃ : ∀ x ∈ Ht, (∀ c ∈ J₃, c * x = x * c) → x = 1) : T₁ ≤ I₂ := by
  intro x hx
  have hHtN : Ht ≤ normalizer (I₂ : Set G) := by
    rw [commutator_comm] at hI₂Htc
    exact (commutator_eq_bot_iff_le_centralizer.1 hI₂Htc).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨y, hy, h', hh', rfl⟩ := (mem_sup_iff_of_le_normalizer' hHtN).1 (hQ ▸ hT₁Q hx)
  have hfix : ∀ c ∈ J₃, c * h' = h' * c := by
    intro c hc
    have h1 : c * (y * h') * c⁻¹ = y * h' := by
      rw [hT₁c c hc _ hx]; group
    have h2 : (c * y * c⁻¹) * (c * h' * c⁻¹) = y * h' := by
      rw [← h1]; group
    obtain ⟨-, h3⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hinf
      ((mem_normalizer_iff.1 (hJK c hc) y).1 (hI₂K hy)) (hI₂K hy)
      ((mem_normalizer_iff.1 (hJKt c hc) h').1 (hHtK hh')) (hHtK hh') (h2.trans rfl)
    calc c * h' = (c * h' * c⁻¹) * c := by group
      _ = h' * c := by rw [h3]
  have hh1 : h' = 1 := hU₃ h' hh' hfix
  rw [hh1, mul_one]
  exact hy

theorem stage_E_eq {Q I₁ I₂ Ht : Subgroup G}
    (hQ₁ : Q = I₁ ⊔ Ht) (hQ₂ : Q = I₂ ⊔ Ht)
    (hc₁ : ∀ h ∈ Ht, ∀ y ∈ I₁, h * y = y * h) (hc₂ : ∀ h ∈ Ht, ∀ y ∈ I₂, h * y = y * h)
    (hHt : ∀ h ∈ Ht, ∀ h' ∈ Ht, h * h' = h' * h) : ⁅I₁, I₁⁆ = ⁅I₂, I₂⁆ := by
  have key : ∀ I : Subgroup G, (∀ h ∈ Ht, ∀ y ∈ I, h * y = y * h) → ⁅I ⊔ Ht, I ⊔ Ht⁆ = ⁅I, I⁆ := by
    intro I hc
    refine commutator_sup_central ?_
    intro h hh
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (TrialityD4.ProductCase.ProductDecompAux.mem_sup_of_forall_commute
        (fun a ha b hb => (hc b hb a ha).symm)).1 hz
    calc a * b * h = a * (b * h) := by group
      _ = a * (h * b) := by rw [hHt b hb h hh]
      _ = (a * h) * b := by group
      _ = (h * a) * b := by rw [(hc h hh a ha).symm]
      _ = h * (a * b) := by group
  rw [← key I₁ hc₁, ← key I₂ hc₂, ← hQ₁, ← hQ₂]

theorem stage_E_card {A I₁ P S F : Subgroup G} {t : G} {q : ℕ} (ht : t * t = 1)
    (hc : ⁅A, Aᵍ[t]⁆ = ⊥) (hi : A ⊓ Aᵍ[t] = ⊥) (hI₁A : I₁ ≤ A) (hP : P = I₁ ⊔ I₁ᵍ[t])
    (hS : P ⊓ centralizer ({t} : Set G) = S) (hSF : ⁅S, S⁆ = F) (hF : Nat.card F = q ^ 4) :
    Nat.card (⁅I₁, I₁⁆ : Subgroup G) = q ^ 4 := by
  have h1 : TrialityD4.ProductCase.ProductDecompAux.dg A t hc I₁ = S := by
    rw [TrialityD4.ProductCase.ProductDecompAux.dg_eq_inf_centralizer ht hc hi hI₁A, ← hP, hS]
  have h2 := TrialityD4.ProductCase.ProductDecompAux.dg_commutator (hc := hc) hI₁A hI₁A
  rw [h1, hSF] at h2
  have h3 := TrialityD4.ProductCase.ProductDecompAux.card_dg (hc := hc) hi
    ((Subgroup.commutator_mono hI₁A hI₁A).trans
      (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le A))
  rw [h2, hF] at h3
  exact h3.symm

end Stages

section Levi

variable {G : Type} [Group G] [Finite G]

theorem levi_facts {N X Λ Cen : Subgroup G} (hΛN : Λ ≤ N) (hXΛ : X ≤ Λ)
    (hNX : N ≤ normalizer (X : Set G)) (hcompl : N = Cen ⊔ X) (hCenX : Cen ⊓ X = ⊥)
    (hCenN : Cen ≤ N) : Λ ⊓ Cen ≤ Λ ∧ (Λ ⊓ Cen) ⊓ X = ⊥ ∧ Λ ≤ (Λ ⊓ Cen) ⊔ X := by
  refine ⟨inf_le_left, le_bot_iff.1 ?_, ?_⟩
  · rw [← hCenX]
    exact inf_le_inf inf_le_right le_rfl
  · have h1 := inf_sup_eq_of_le_of_le_normalizer hXΛ (hCenN.trans hNX)
    rw [← hcompl, inf_eq_left.2 hΛN] at h1
    exact h1.le

end Levi

section Master

variable {G : Type} [Group G] [Finite G]

theorem master {F : Type} [Field F] [Finite F] {t : G}
    {P U D7 M6 N₁ N₂ Λ₁ Λ₂ A₁ A₂ K1p K2pp B₁ O₂ Z₃ Z₃' J₃ S Fq Y : Subgroup G} {q : ℕ}
    (ht2 : t * t = 1) (hqF : Nat.card F = q)
    (hPt : Pᵍ[t] = P) (hUt : Uᵍ[t] = U) (hD7t : D7ᵍ[t] = D7)
    (hS₁ : Sl2Pair F N₁ D7 Λ₁ (Λ₁ᵍ[t])) (hS₂ : Sl2Pair F N₂ M6 Λ₂ (Λ₂ᵍ[t]))
    (hP₁ : IsSylowOf 2 P N₁) (hP₂ : IsSylowOf 2 P N₂)
    (hPcard : Nat.card P = q ^ 12) (hUcard : Nat.card U = q ^ 2)
    (hM6card : Nat.card M6 = q ^ 10)
    (hUP : U ≤ P) (hD7P : D7 ≤ P) (hM6P : M6 ≤ P) (hUM6 : U ≤ M6) (hYP : Y ≤ P)
    (hZPc : ∀ z ∈ U, ∀ y ∈ P, y * z = z * y)
    (hZcen : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ U)
    (hUN₁ : ∀ x ∈ U, ∀ y ∈ N₁, y * x = x * y)
    (hK1p : K1p = ⁅Λ₁, Λ₁⁆) (hB₁ : B₁ = pCoreOf 2 K1p)
    (h9a : N₁ = K1p ⊔ K1pᵍ[t]) (h9b : K1p ⊓ K1pᵍ[t] = U) (h9c : ⁅K1p, K1pᵍ[t]⁆ ≤ U)
    (h9d : ⁅K1p, K1p⁆ ⊔ U = K1p) (h9e : K1p = A₁ ⊔ B₁) (h9g : B₁ ≤ D7)
    (h9j : N₁ = ⁅K1p, K1p⁆ ⊔ (⁅K1p, K1p⁆)ᵍ[t]) (h9k : ⁅⁅K1p, K1p⁆, ⁅K1p, K1p⁆⁆ = ⁅K1p, K1p⁆)
    (hO₂ : O₂ = pCoreOf 2 K2pp)
    (hN₂ : N₂ = K2pp ⊔ K2ppᵍ[t]) (hI₂ : K2pp ⊓ K2ppᵍ[t] = ⊥) (hc₂ : ⁅K2pp, K2ppᵍ[t]⁆ = ⊥)
    (hA₂K : K2pp = A₂ ⊔ O₂) (hM6eq : O₂ ⊔ O₂ᵍ[t] = M6) (hM6i : O₂ ⊓ O₂ᵍ[t] = ⊥)
    (hO₂Q : O₂ ≤ (P ⊓ A₁) ⊔ B₁)
    (hA₁perf : A₁ ≤ ⁅A₁, A₁⁆) (hA₂Λ : A₂ ≤ Λ₂) (hA₂M : A₂ ⊓ M6 = ⊥) (hΛA₂ : Λ₂ ≤ A₂ ⊔ M6)
    (hA₁D : A₁ ⊓ D7 = ⊥) (hA₁Λ : A₁ ≤ Λ₁) (hΛA₁ : Λ₁ ≤ A₁ ⊔ D7)
    (hRΛ₁ : ∀ g ∈ A₂ ⊓ normalizer ((P ⊓ A₂ : Subgroup G) : Set G), g ∈ normalizer (Λ₁ : Set G))
    (hY : Y = Z₃ ⊔ Z₃') (hZ₃'B : Z₃' ≤ B₁) (hZ₃c : Z₃ ≤ centralizer (A₂ : Set G))
    (hT₂Y : P ⊓ A₂ ≤ ((P ⊓ A₁) ⊔ B₁) ⊔ Y)
    (hJK : ∀ c ∈ J₃, c ∈ normalizer (K2pp : Set G))
    (hJKt : ∀ c ∈ J₃, c ∈ normalizer ((K2ppᵍ[t] : Subgroup G) : Set G))
    (hA₁c : ∀ c ∈ J₃, ∀ x ∈ A₁, c * x = x * c)
    (hU₃ : ∀ x ∈ U, (∀ c ∈ J₃, c * x = x * c) → x = 1)
    (hT₂D : P ⊓ A₂ ≤ D7) (hPP : ⁅P, P⁆ ≤ D7 ⊓ M6) (hSP : P ⊓ centralizer ({t} : Set G) = S)
    (hSF : ⁅S, S⁆ = Fq) (hFcard : Nat.card Fq = q ^ 4) :
    (N₁ = ⁅K1p, K1p⁆ ⊔ (⁅K1p, K1p⁆)ᵍ[t] ∧ ⁅K1p, K1p⁆ ⊓ (⁅K1p, K1p⁆)ᵍ[t] = ⊥ ∧
      ⁅⁅K1p, K1p⁆, (⁅K1p, K1p⁆)ᵍ[t]⁆ = ⊥ ∧ ⁅K1p, K1p⁆ = A₁ ⊔ pCoreOf 2 ⁅K1p, K1p⁆ ∧
      ⁅⁅K1p, K1p⁆, ⁅K1p, K1p⁆⁆ = ⁅K1p, K1p⁆ ∧
      pCoreOf 2 ⁅K1p, K1p⁆ ⊔ (pCoreOf 2 ⁅K1p, K1p⁆)ᵍ[t] = D7 ∧
      pCoreOf 2 ⁅K1p, K1p⁆ ⊓ (pCoreOf 2 ⁅K1p, K1p⁆)ᵍ[t] = ⊥) ∧
    (P ⊓ A₁) ⊔ pCoreOf 2 ⁅K1p, K1p⁆ = (P ⊓ A₂) ⊔ O₂ := by
  have hK1pp_le : ⁅K1p, K1p⁆ ≤ K1p := TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _
  have hUK1 : U ≤ K1p := by rw [← h9b]; exact inf_le_left
  have hUK1t : U ≤ K1pᵍ[t] := by rw [← h9b]; exact inf_le_right
  have hA₁K1 : A₁ ≤ K1p := h9e ▸ le_sup_left
  have hB₁P : B₁ ≤ P := h9g.trans hD7P
  have hB₁N : K1p ≤ normalizer (B₁ : Set G) := by rw [hB₁]; exact le_normalizer_pCoreOf K1p
  have hQeq : (P ⊓ A₁) ⊔ B₁ = P ⊓ K1p := by
    conv_rhs => rw [h9e]
    exact (inf_sup_eq_of_le_of_le_normalizer hB₁P (hA₁K1.trans hB₁N)).symm
  have hUQ : U ≤ (P ⊓ A₁) ⊔ B₁ := by rw [hQeq]; exact le_inf hUP hUK1
  obtain ⟨hSylK1, -, hPK1eq, hPK1inf, hPK1comm⟩ := sylow_prod hP₁ h9a.symm h9b h9c hUP
  have hconjK1 : P ⊓ K1pᵍ[t] = (P ⊓ K1p)ᵍ[t] := by
    rw [TrialityD4.ProductCase.ProductDecompAux.conjT_inf, hPt]
  rw [hconjK1] at hPK1eq hPK1inf hPK1comm
  have hQcard : Nat.card ((P ⊓ K1p : Subgroup G)) = q ^ 7 := by
    have hQN : (P ⊓ K1p)ᵍ[t] ≤ normalizer ((P ⊓ K1p : Subgroup G) : Set G) := by
      refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅(P ⊓ K1p)ᵍ[t], P ⊓ K1p⁆ :=
        Subgroup.commutator_mem_commutator hx hy
      rw [Subgroup.commutator_comm] at h1
      exact le_inf hUP hUK1 (hPK1comm h1)
    have h1 := Common.card_sup_mul_card_inf_eq hQN
    rw [← hPK1eq, hPK1inf, TrialityD4.ProductCase.ProductDecompAux.card_conjT, hPcard,
      hUcard] at h1
    have h2 : Nat.card (P ⊓ K1p : Subgroup G) ^ 2 = (q ^ 7) ^ 2 := by
      calc Nat.card (P ⊓ K1p : Subgroup G) ^ 2 = Nat.card (P ⊓ K1p : Subgroup G) *
            Nat.card (P ⊓ K1p : Subgroup G) := pow_two _
        _ = q ^ 12 * q ^ 2 := h1.symm
        _ = (q ^ 7) ^ 2 := by ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  rw [← hQeq] at hQcard hSylK1
  have hO₂K : O₂ ≤ K2pp := by rw [hO₂]; exact LieType.BorelTits.pCoreOf_le 2 _
  have hKO₂ : K2pp ≤ normalizer (O₂ : Set G) := by rw [hO₂]; exact le_normalizer_pCoreOf _
  have hO₂P : O₂ ≤ P := (le_sup_left.trans hM6eq.le).trans hM6P
  have hO₂tP : O₂ᵍ[t] ≤ P := (le_sup_right.trans hM6eq.le).trans hM6P
  have hPK2 : P ≤ K2pp ⊔ K2ppᵍ[t] := hN₂ ▸ hP₂.le
  obtain ⟨hUH, hHHt, hHc, hHcard⟩ := stage_U ht2 hI₂ hc₂ hPK2 hO₂K hKO₂ hM6i hO₂P hO₂tP
    (hUM6.trans hM6eq.ge) hUt hZPc hZcen hUcard
  have hHtU : (O₂ ⊓ U)ᵍ[t] ≤ U := by
    rw [TrialityD4.ProductCase.ProductDecompAux.conjT_inf, hUt]; exact inf_le_right
  have hHtO : (O₂ ⊓ U)ᵍ[t] ≤ O₂ᵍ[t] := by
    rw [TrialityD4.ProductCase.ProductDecompAux.conjT_inf, hUt]; exact inf_le_left
  have hHtcard : Nat.card ((O₂ ⊓ U)ᵍ[t] : Subgroup G) = q := by
    rw [TrialityD4.ProductCase.ProductDecompAux.card_conjT, hHcard]
  have hA₂K' : A₂ ≤ K2pp := le_sup_left.trans hA₂K.ge
  have hK1tN : K1pᵍ[t] ≤ normalizer (K1p : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅K1pᵍ[t], K1p⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [Subgroup.commutator_comm] at h1
    exact hUK1 (h9c h1)
  have hPK1N : P ≤ normalizer (K1p : Set G) :=
    hP₁.le.trans (h9a ▸ sup_le Subgroup.le_normalizer hK1tN)
  have hRP : A₂ ⊓ normalizer ((P ⊓ A₂ : Subgroup G) : Set G) ≤ normalizer (P : Set G) :=
    inf_normalizer_le_normalizer_sylow hS₂ hP₂ hM6P hA₂Λ hΛA₂
  have hRK1 : ∀ g ∈ A₂ ⊓ normalizer ((P ⊓ A₂ : Subgroup G) : Set G),
      g ∈ normalizer (K1p : Set G) := fun g hg => by
    rw [hK1p]
    exact TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator (hRΛ₁ g hg)
  have hRQ : ∀ g ∈ A₂ ⊓ normalizer ((P ⊓ A₂ : Subgroup G) : Set G),
      g ∈ normalizer (((P ⊓ A₁) ⊔ B₁ : Subgroup G) : Set G) := fun g hg => by
    rw [hQeq]
    exact Common.mem_normalizer_inf (hRP hg) (hRK1 g hg)
  have hPQ : P ≤ normalizer (((P ⊓ A₁) ⊔ B₁ : Subgroup G) : Set G) := fun x hx => by
    rw [hQeq]
    exact Common.mem_normalizer_inf (Subgroup.le_normalizer hx) (hPK1N hx)
  have hZ₃Y : Z₃ ≤ Y := le_sup_left.trans hY.ge
  have hZ₃N : Z₃ ≤ normalizer (((P ⊓ A₁) ⊔ B₁ : Subgroup G) : Set G) :=
    (hZ₃Y.trans hYP).trans hPQ
  have hT₂QZ : P ⊓ A₂ ≤ ((P ⊓ A₁) ⊔ B₁) ⊔ Z₃ :=
    hT₂Y.trans (sup_le le_sup_left (hY.le.trans (sup_le le_sup_right
      ((hZ₃'B.trans le_sup_right).trans le_sup_left))))
  have hT₂Q : P ⊓ A₂ ≤ (P ⊓ A₁) ⊔ B₁ :=
    stage_T₂Q hS₂ hP₂ hM6P hA₂Λ hA₂M hΛA₂ hRQ hZ₃N hZ₃c hT₂QZ
  obtain ⟨hQ₂eq, hI₂Ht, hI₂Htc, hT₂card, hO₂card, hI₂card⟩ := stage_Q (U := U) hS₂ hP₂ hM6P hqF
    hA₂Λ hA₂M hΛA₂ hI₂ hc₂ hA₂K' hO₂K hKO₂ hM6eq hM6i hM6card hT₂Q hO₂Q hHtU hUQ hHtO hHtcard hQcard
  have hK1N₁ : K1p ≤ N₁ := h9a ▸ le_sup_left
  have hHtK1 : (O₂ ⊓ U)ᵍ[t] ≤ K1p := hHtU.trans hUK1
  have hHtc : (O₂ ⊓ U)ᵍ[t] ≤ centralizer (K1p : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hUN₁ x (hHtU hx) y (hK1N₁ hy)
  have hHt2 : IsPGroup 2 ((O₂ ⊓ U)ᵍ[t] : Subgroup G) :=
    hP₁.isPGroup.to_le (hHtU.trans hUP)
  have hK1ppHt : ⁅K1p, K1p⁆ ⊓ (O₂ ⊓ U)ᵍ[t] = ⊥ :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_inf_eq_bot_of_sylow_complement hHtK1 hHtc
      hHt2 hSylK1 ((sup_comm _ _).trans hQ₂eq.symm) ((inf_comm _ _).trans hI₂Ht)
  obtain ⟨hcomm, hinf, hK1pHt⟩ := stage_inter ht2 h9j h9a h9b h9c hUN₁ h9d hUH hUcard hHtcard
    hHtU hK1ppHt hUt hUP hZPc (by rw [hUt]; exact hUP)
  have hD7N₁ : D7 ≤ N₁ :=
    (TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.D_le_left hS₁).trans
      (TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.left_le hS₁)
  have hN₁D7 : N₁ ≤ normalizer (D7 : Set G) :=
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS₁
  obtain ⟨hone, hD7eq, hOi⟩ := stage_one (by rw [← hB₁]; exact h9e) hA₁perf h9j hinf hcomm hD7N₁
    hN₁D7 (hP₁.isPGroup.to_le hD7P) hD7t (hB₁ ▸ h9g)
  have hK1pp_le : ⁅K1p, K1p⁆ ≤ K1p := TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _
  have hOo₁D7 : pCoreOf 2 ⁅K1p, K1p⁆ ≤ D7 := le_sup_left.trans hD7eq.le
  have hOo₁P : pCoreOf 2 ⁅K1p, K1p⁆ ≤ P := hOo₁D7.trans hD7P
  have hA₁K1pp : A₁ ≤ ⁅K1p, K1p⁆ := by
    have : A₁ ≤ A₁ ⊔ pCoreOf 2 ⁅K1p, K1p⁆ := le_sup_left
    rwa [← hone] at this
  have hI₁eq : P ⊓ ⁅K1p, K1p⁆ = (P ⊓ A₁) ⊔ pCoreOf 2 ⁅K1p, K1p⁆ := by
    conv_lhs => rw [hone]
    exact inf_sup_eq_of_le_of_le_normalizer hOo₁P
      (hA₁K1pp.trans (le_normalizer_pCoreOf _))
  have hPcard' : Nat.card P = (q ^ 6) ^ 2 := by rw [hPcard, ← pow_mul]
  obtain ⟨-, hPeq, -, -, hI₁card⟩ := sylow_decomp hP₁ h9j.symm hinf hcomm hPt hPcard'
  have hHtcom : ∀ y ∈ (O₂ ⊓ U)ᵍ[t], ∀ x ∈ K1p, y * x = x * y := fun y hy x hx =>
    (hUN₁ y (hHtU hy) x (hK1N₁ hx)).symm
  have hHtN : ⁅K1p, K1p⁆ ≤ normalizer (((O₂ ⊓ U)ᵍ[t] : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [(hHtcom y hy x (hK1pp_le hx)).symm]; group
    rw [this]
    exact one_mem _
  have hQ₁eq : (P ⊓ A₁) ⊔ B₁ = (P ⊓ ⁅K1p, K1p⁆) ⊔ (O₂ ⊓ U)ᵍ[t] := by
    calc (P ⊓ A₁) ⊔ B₁ = P ⊓ K1p := hQeq
      _ = P ⊓ (⁅K1p, K1p⁆ ⊔ (O₂ ⊓ U)ᵍ[t]) := congrArg (fun X => P ⊓ X) hK1pHt
      _ = (P ⊓ ⁅K1p, K1p⁆) ⊔ (O₂ ⊓ U)ᵍ[t] :=
          inf_sup_eq_of_le_of_le_normalizer (hHtU.trans hUP) hHtN
  have hRK1pp : ∀ g ∈ A₂ ⊓ normalizer ((P ⊓ A₂ : Subgroup G) : Set G),
      g ∈ normalizer ((⁅K1p, K1p⁆ : Subgroup G) : Set G) := fun g hg =>
    TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator (hRK1 g hg)
  have hHtK2 : (O₂ ⊓ U)ᵍ[t] ≤ K2ppᵍ[t] := hHtO.trans (Subgroup.map_mono hO₂K)
  have hcc₂ : ∀ a ∈ K2pp, ∀ b ∈ K2ppᵍ[t], a * b = b * a :=
    TrialityD4.ProductCase.ProductDecompAux.commutator_eq_bot_iff.1 hc₂
  have hT₂I₁ : P ⊓ A₂ ≤ P ⊓ ⁅K1p, K1p⁆ := by
    refine stage_T₂Q hS₂ hP₂ hM6P hA₂Λ hA₂M hΛA₂ (fun g hg => ?_) (fun h hh => ?_)
      (fun h hh => ?_) (hT₂Q.trans hQ₁eq.le)
    · exact Common.mem_normalizer_inf (hRP hg) (hRK1pp g hg)
    · refine Common.mem_normalizer_inf (Subgroup.le_normalizer (hHtU.trans hUP hh))
        (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_))
      exact (hHtcom h hh x (hK1pp_le hx)).symm
    · exact mem_centralizer_iff.2 fun a ha => hcc₂ a (hA₂K' ha) h (hHtK2 hh)
  have hT₁I₂ : P ⊓ A₁ ≤ (P ⊓ A₂) ⊔ O₂ :=
    stage_T₁I₂ hQ₂eq le_sup_left (sup_le (inf_le_right.trans hA₂K') hO₂K) hHtK2 hI₂ hI₂Htc hJK hJKt
      (fun c hc x hx => hA₁c c hc x hx.2) (fun x hx hfix => hU₃ x (hHtU hx) hfix)
  have hEeq : ⁅P ⊓ ⁅K1p, K1p⁆, P ⊓ ⁅K1p, K1p⁆⁆ = ⁅(P ⊓ A₂) ⊔ O₂, (P ⊓ A₂) ⊔ O₂⁆ :=
    stage_E_eq (Q := (P ⊓ A₁) ⊔ B₁) hQ₁eq hQ₂eq
      (fun h hh y hy => hHtcom h hh y (hK1pp_le hy.2))
      (fun h hh y hy => (hcc₂ y (sup_le (inf_le_right.trans hA₂K') hO₂K hy) h (hHtK2 hh)).symm)
      (fun h hh h' hh' => (hZPc h (hHtU hh) h' (hUP (hHtU hh'))).symm)
  have hEcard : Nat.card (⁅P ⊓ ⁅K1p, K1p⁆, P ⊓ ⁅K1p, K1p⁆⁆ : Subgroup G) = q ^ 4 :=
    stage_E_card ht2 hcomm hinf inf_le_right hPeq hSP hSF hFcard
  have hT₁card : Nat.card (P ⊓ A₁ : Subgroup G) = q :=
    card_inf_complement hS₁ hP₁ hD7P hqF hA₁Λ hA₁D hΛA₁
  have hT₁I₁ : P ⊓ A₁ ≤ P ⊓ ⁅K1p, K1p⁆ := inf_le_inf_left P hA₁K1pp
  have hcount : P ⊓ ⁅K1p, K1p⁆ = (P ⊓ A₂) ⊔ O₂ :=
    stage_count hI₁card hI₂card hEcard hT₂card hT₁card rfl hEeq hT₁I₁ hT₂I₁ hT₁I₂ le_sup_left
      ((commutator_mono inf_le_left inf_le_left).trans hPP |>.trans inf_le_left)
      ((commutator_mono inf_le_left inf_le_left).trans hPP |>.trans inf_le_right) hT₂D
      (le_bot_iff.1 (hA₁D ▸ inf_le_inf inf_le_right le_rfl))
      (le_bot_iff.1 (hA₂M ▸ inf_le_inf inf_le_right le_rfl))
  exact ⟨⟨h9j, hinf, hcomm, hone, h9k, hD7eq, hOi⟩, hI₁eq.symm.trans hcount⟩

end Master
end ProductDecompAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


private theorem inf_centralizer_J₄_le_yamadaD₇ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaP d t ⊓ centralizer (d.J₄ : Set G) ≤ yamadaD₇ d t := by
  rintro x ⟨hxP, hxC⟩
  have hmul : x ∈ ((yamadaM₆ d t : Set G) * (yamadaD₇ d t : Set G)) := by
    rw [← h.yamadaP_eq_mul hW d hK hQ]
    exact hxP
  obtain ⟨m, hm, δ, hδ, rfl⟩ := Set.mem_mul.1 hmul
  have hF₅D := h.yamadaF₅_le_yamadaD₇ hW d hK hQ
  have hel := (h.yamada_5_57_2 hW d hK hQ).2.2.2.2.2.2
  have hM₆P := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hF₅P : yamadaF₅ d t ≤ yamadaP d t := (h.yamadaF₅_le_yamadaM₆ hW d hK hQ).trans hM₆P
  have hmF : ∀ j ∈ d.J₄, ⁅j, m⁆ ∈ yamadaF₅ d t := by
    intro j hj
    have hfix : j * (m * δ) = (m * δ) * j := mem_centralizer_iff.1 hxC j hj
    have hjδ : ⁅j, δ⁆ ∈ yamadaF₅ d t :=
      h.commutator_J₄_yamadaD₇_le_yamadaF₅ hW d hK hQ j hj δ hδ
    have hconj : m * ⁅j, δ⁆ * m⁻¹ ∈ yamadaF₅ d t := by
      have h1 : ⁅m, ⁅j, δ⁆⁆ ∈ yamadaF₅ d t := (hel m (hM₆P hm) _ (hF₅P hjδ)).2
      have e : m * ⁅j, δ⁆ * m⁻¹ = ⁅m, ⁅j, δ⁆⁆ * ⁅j, δ⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem h1 hjδ
    have key : ⁅j, m * δ⁆ = ⁅j, m⁆ * (m * ⁅j, δ⁆ * m⁻¹) := by
      simp only [commutatorElement_def]; group
    have h1 : ⁅j, m * δ⁆ = 1 := by
      rw [commutatorElement_def, hfix]; group
    rw [eq_inv_of_mul_eq_one_left (key.symm.trans h1)]
    exact inv_mem hconj
  exact mul_mem (hF₅D (h.mem_yamadaF₅_of_fixed_J₄_yamadaM₆ hW d hK hQ m hm hmF)) hδ

private theorem glue_setting (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaP d t)ᵍ[t] = yamadaP d t ∧ (yamadaU₁ d t)ᵍ[t] = yamadaU₁ d t ∧
      (yamadaD₇ d t)ᵍ[t] = yamadaD₇ d t ∧
      Nat.card (yamadaP d t) = Nat.card K ^ 12 ∧ Nat.card (yamadaU₁ d t) = Nat.card K ^ 2 ∧
      Nat.card (yamadaM₆ d t) = Nat.card K ^ 10 ∧
      yamadaU₁ d t ≤ yamadaP d t ∧ yamadaD₇ d t ≤ yamadaP d t ∧ yamadaM₆ d t ≤ yamadaP d t ∧
      yamadaU₁ d t ≤ yamadaM₆ d t ∧ yamadaY₂ d t ≤ yamadaP d t ∧
      (∀ z ∈ yamadaU₁ d t, ∀ y ∈ yamadaP d t, y * z = z * y) ∧
      (∀ x ∈ yamadaP d t, (∀ y ∈ yamadaP d t, y * x = x * y) → x ∈ yamadaU₁ d t) ∧
      ⁅yamadaP d t, yamadaP d t⁆ ≤ yamadaD₇ d t ⊓ yamadaM₆ d t ∧
      yamadaP d t ⊓ centralizer ({t} : Set G) = d.S ∧ ⁅d.S, d.S⁆ = d.F ∧
      Nat.card d.F = Nat.card K ^ 4 := by
  classical
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hD := hQ.doubling
  have hcard := h.yamada_series_card hW d hK hQ
  have hZ1 := (h.yamada_5_57_1 hW d hK hQ).1
  have h572 := h.yamada_5_57_2 hW d hK hQ
  have hDP : yamadaD₇ d t ≤ yamadaP d t := yamadaD₇_le_yamadaP d t
  have hFSS := d.yamada_3_12_commutators hK4
  refine ⟨TrialityD4.ProductCase.ProductDecompAux.conjT_eq_of_mem_normalizer
      (h.yamada_5_51 hW d hK hQ).1.2.1,
    TrialityD4.ProductCase.ProductDecompAux.conjT_eq_of_mem_normalizer
      (h.t_mem_normalizer_yamadaU₁ d hK hD).1,
    TrialityD4.ProductCase.ProductDecompAux.conjT_eq_of_mem_normalizer
      (h.yamada_5_51 hW d hK hQ).2.2.2.1,
    hcard.2.2.2.2.2, hcard.1, hcard.2.2.2.2.1,
    (h.yamadaU₁_le_yamadaD₇ hW d hK hQ).trans hDP, hDP, h.yamadaM₆_le_yamadaP hW d hK hQ,
    (yamadaU₁_le_yamadaY₂ d t).trans (h.yamadaY₂_le_yamadaM₆ hW d hK hQ),
    (h.yamadaY₂_le_yamadaD₇ hW d hK hQ).trans hDP, ?_, ?_, ?_,
    (h.yamada_series_inf_centralizer hW d hK hQ).2.2.2.2.2, hFSS.2.2.1, d.cards.2.2.2.2.1⟩
  · intro z hz y hy
    rw [← hZ1] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    rw [Subgroup.upperCentralSeries_one] at hz'
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨y, hy⟩)
  · intro x hx hc
    rw [← hZ1]
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one]
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2)
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    exact (le_inf h572.2.1 h572.1) (h572.2.2.2.2.2.2 x hx y hy).2

private theorem glue_J (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {Λ₂ : Subgroup G}
    (hS₂ : Sl2Pair K (yamadaN₂ d t) (yamadaM₆ d t) Λ₂ (Λ₂ᵍ[t])) :
    (∀ c ∈ d.J₃, c ∈ normalizer (derived₂ Λ₂ : Set G)) ∧
      ∀ c ∈ d.J₃, c ∈ normalizer (((derived₂ Λ₂)ᵍ[t] : Subgroup G) : Set G) := by
  have hJ₃J := Setup.J₃_le_J d
  have hJM : d.J₃ ≤ normalizer (yamadaM₆ d t : Set G) := fun j hj =>
    h.J_le_normalizer_yamadaM₆ hW d hK hQ (hJ₃J hj)
  have hK₂M : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2
  have hJN : d.J₃ ≤ normalizer (yamadaN₂ d t : Set G) := fun j hj =>
    ProductDecompAux.normalizer_le_normalizer_normalClosure hK₂M (hJM hj)
  have hJΛ : d.J₃ ≤ normalizer (Λ₂ : Set G) :=
    ProductDecompAux.le_normalizer_of_odd_card hS₂ hJN hJM
      ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₃J))
  have hJK : ∀ c ∈ d.J₃, c ∈ normalizer (derived₂ Λ₂ : Set G) := fun c hc =>
    TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator
      (TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator (hJΛ hc))
  refine ⟨hJK, fun c hc => ?_⟩
  have hct : c * t = t * c := N60.J_comm_t h d (hJ₃J hc)
  refine TrialityD4.ProductCase.ProductDecompAux.mem_normalizer_map_conj_of ?_
  have e : t * c * t⁻¹ = c := by rw [← hct]; group
  rw [e]
  exact hJK c hc

private theorem glue_levi₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    leviFactor₁ d Λ₁ ≤ ⁅leviFactor₁ d Λ₁, leviFactor₁ d Λ₁⁆ ∧
      leviFactor₁ d Λ₁ ⊓ yamadaD₇ d t = ⊥ ∧ Λ₁ ≤ leviFactor₁ d Λ₁ ⊔ yamadaD₇ d t := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hD7t : t ∈ normalizer (yamadaD₇ d t : Set G) := (h.yamada_5_51 hW d hK hQ).2.2.2.1
  have hS₁ : Sl2Pair K (yamadaN₁ d t) (yamadaD₇ d t) Λ₁ (Λ₁ᵍ[t]) :=
    ProductDecompAux.sl2Pair_of_isFactor hL.fac₁ hD7t hK4
  have hN₁D : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS₁
  have hΛN : Λ₁ ≤ yamadaN₁ d t := hL.fac₁.le
  have hA₁Λ : leviFactor₁ d Λ₁ ≤ Λ₁ := inf_le_left
  have hA₁eq : leviFactor₁ d Λ₁ = Λ₁ ⊓ (yamadaN₁ d t ⊓ centralizer (d.J₃ : Set G)) := by
    unfold leviFactor₁
    rw [← inf_assoc, inf_eq_left.2 hΛN]
  obtain ⟨-, hinf, hsup⟩ := ProductDecompAux.levi_facts hΛN hL.fac₁.X_le hN₁D hp.compl₁.1
    hp.compl₁.2.1 inf_le_left
  rw [← hA₁eq] at hinf hsup
  exact ⟨ProductDecompAux.le_commutator_of_complement hL.fac₁.quot
    (CFSG.ClassicalInvolution.sl2_isPerfect hK4) hL.fac₁.X_le hA₁Λ hinf hsup
    (hA₁Λ.trans (hΛN.trans hN₁D)), hinf, hsup⟩

private theorem glue_levi₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    leviFactor₂ hp.Astar Λ₂ ⊓ yamadaM₆ d t = ⊥ ∧ Λ₂ ≤ leviFactor₂ hp.Astar Λ₂ ⊔ yamadaM₆ d t := by
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  have hM6t : t ∈ normalizer (yamadaM₆ d t : Set G) := ((h.yamada_5_44_1 hW d hK hQ).1).2.1
  have hS₂ : Sl2Pair K (yamadaN₂ d t) (yamadaM₆ d t) Λ₂ (Λ₂ᵍ[t]) :=
    ProductDecompAux.sl2Pair_of_isFactor hL.fac₂ hM6t hK4
  have hN₂M : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
    TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux.le_normalizer_D hS₂
  obtain ⟨-, hinf, hsup⟩ := ProductDecompAux.levi_facts hL.fac₂.le hL.fac₂.X_le hN₂M
    hp.Astar_spec.sup_eq hp.Astar_spec.inf_eq (hp.Astar_spec.le_cen.trans inf_le_left)
  exact ⟨hinf, hsup⟩

private theorem glue_79 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    yamadaN₁ d t = derived₁ Λ₁ ⊔ (derived₁ Λ₁)ᵍ[t] ∧
      derived₁ Λ₁ ⊓ (derived₁ Λ₁)ᵍ[t] = yamadaU₁ d t ∧
      ⁅derived₁ Λ₁, (derived₁ Λ₁)ᵍ[t]⁆ ≤ yamadaU₁ d t ∧
      ⁅derived₁ Λ₁, derived₁ Λ₁⁆ ⊔ yamadaU₁ d t = derived₁ Λ₁ ∧
      derived₁ Λ₁ = leviFactor₁ d Λ₁ ⊔ pCoreOf 2 (derived₁ Λ₁) ∧
      pCoreOf 2 (derived₁ Λ₁) ≤ yamadaD₇ d t ∧
      yamadaN₁ d t = derived₂ Λ₁ ⊔ (derived₂ Λ₁)ᵍ[t] ∧
      ⁅derived₂ Λ₁, derived₂ Λ₁⁆ = derived₂ Λ₁ := by
  obtain ⟨⟨h9a, h9b, h9c, h9d, h9e, h9f, h9g, -⟩, ⟨-, h9j, h9k, h9l⟩⟩ :=
    h.yamada_7_9 hW d hK hQ hp hL
  have hUK1 : yamadaU₁ d t ≤ derived₁ Λ₁ := h9l ▸ inf_le_left
  have hdm : derivedMod (yamadaU₁ d t) Λ₁ = derived₁ Λ₁ := sup_eq_left.2 hUK1
  rw [hdm] at h9a h9b h9c h9d h9e h9f
  refine ⟨h9a, h9b, h9c, h9d, ?_, ?_, h9j, h9k⟩
  · rw [← h9f]
    exact h9e
  · rw [← h9f]
    exact (le_sup_right : centerMod (yamadaU₁ d t) (Λ₁ᵍ[t]) ≤ _).trans h9g.le

private theorem glue_Z (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂) :
    zc ((yamadaK₃ d t Λ₂)ᵍ[t]) ≤ pCoreOf 2 (derived₁ Λ₁) := by
  have h713b := (h.yamada_7_13 hW d hK hQ hp hL.fac₂).2.1
  have h714 := h.yamada_7_14 hW d hK hQ hp hL
  rw [ProductDecompAux.zc_conj]
  have h1 : zc (yamadaK₃ d t Λ₂) ≤ zc (yamadaP₃ d t Λ₂) := by
    rw [h713b.2.2.1]
    exact le_sup_left
  have h2 := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) h1
  rw [← ProductDecompAux.zc_conj (yamadaP₃ d t Λ₂) t, ← h714] at h2
  exact h2.trans inf_le_left

private theorem glue_hRΛ₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f)
    {Λ₁ Λ₂ : Subgroup G} (hL : Labelled d t Λ₁ Λ₂)
    (hS₁ : Sl2Pair K (yamadaN₁ d t) (yamadaD₇ d t) Λ₁ (Λ₁ᵍ[t]))
    (hS₂ : Sl2Pair K (yamadaN₂ d t) (yamadaM₆ d t) Λ₂ (Λ₂ᵍ[t]))
    (hΛA₂ : Λ₂ ≤ leviFactor₂ hp.Astar Λ₂ ⊔ yamadaM₆ d t) :
    ∀ g ∈ leviFactor₂ hp.Astar Λ₂ ⊓
        normalizer ((yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂ : Subgroup G) : Set G),
      g ∈ normalizer (Λ₁ : Set G) := by
  have hK₁D : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
    (TrialityD4.ProductCase.ProductDecompAux.commutator_self_le _).trans
      (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).1
  have hchar := (h.yamada_7_3_char hW d hK hQ hp).1
  have hA₂Λ : leviFactor₂ hp.Astar Λ₂ ≤ Λ₂ := inf_le_left
  intro g hg
  have hgP : g ∈ normalizer (yamadaP d t : Set G) :=
    ProductDecompAux.inf_normalizer_le_normalizer_sylow hS₂ hp.sylow₂
      (h.yamadaM₆_le_yamadaP hW d hK hQ) hA₂Λ hΛA₂ hg
  have hgD : g ∈ normalizer (yamadaD₇ d t : Set G) := (hchar.le hgP).2
  have hgN : g ∈ normalizer (yamadaN₁ d t : Set G) :=
    ProductDecompAux.normalizer_le_normalizer_normalClosure hK₁D hgD
  exact ProductDecompAux.mem_normalizer_of_mem_normalizer_sylow hS₁ hp.sylow₁.le hp.sylow₂
    (hL.fac₂.le (hA₂Λ hg.1)) hgP hgN hgD

theorem yamada_7_16 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    (yamadaN₁ d t = derived₂ Λ₁ ⊔ (derived₂ Λ₁)ᵍ[t] ∧
      derived₂ Λ₁ ⊓ (derived₂ Λ₁)ᵍ[t] = ⊥ ∧
      ⁅derived₂ Λ₁, (derived₂ Λ₁)ᵍ[t]⁆ = ⊥ ∧
      derived₂ Λ₁ = leviFactor₁ d Λ₁ ⊔ pCoreOf 2 (derived₂ Λ₁) ∧
      ⁅derived₂ Λ₁, derived₂ Λ₁⁆ = derived₂ Λ₁ ∧
      pCoreOf 2 (derived₂ Λ₁) ⊔ (pCoreOf 2 (derived₂ Λ₁))ᵍ[t] = yamadaD₇ d t ∧
      pCoreOf 2 (derived₂ Λ₁) ⊓ (pCoreOf 2 (derived₂ Λ₁))ᵍ[t] = ⊥) ∧
    (yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₂ Λ₁) =
      (yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂) ⊔ pCoreOf 2 (derived₂ Λ₂) := by
  classical
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hPt, hUt, hD7t, hPcard, hUcard, hM6card, hUP, hD7P, hM6P, hUM6, hYP, hZPc, hZcen, hPP,
    hSP, hSF, hFcard⟩ := glue_setting hW h d hK hQ
  have hS₁ : Sl2Pair K (yamadaN₁ d t) (yamadaD₇ d t) Λ₁ (Λ₁ᵍ[t]) :=
    ProductDecompAux.sl2Pair_of_isFactor hL.fac₁ (h.yamada_5_51 hW d hK hQ).2.2.2.1 hK4
  have hS₂ : Sl2Pair K (yamadaN₂ d t) (yamadaM₆ d t) Λ₂ (Λ₂ᵍ[t]) :=
    ProductDecompAux.sl2Pair_of_isFactor hL.fac₂ ((h.yamada_5_44_1 hW d hK hQ).1).2.1 hK4
  obtain ⟨hA₁perf, hA₁D, hΛA₁⟩ := glue_levi₁ hW h d hK hQ hp hL
  obtain ⟨hA₂M, hΛA₂⟩ := glue_levi₂ hW h d hK hQ hp hL
  obtain ⟨h9a, h9b, h9c, h9d, h9e, h9g, h9j, h9k⟩ := glue_79 hW h d hK hQ hp hL
  obtain ⟨⟨hN₂, hI₂, hc₂, hA₂, -, hM6, hM6i⟩, hO₂⟩ := h.yamada_7_15 hW d hK hQ hp hL
  obtain ⟨hJK, hJKt⟩ := glue_J hW h d hK hQ hS₂
  have h713b := (h.yamada_7_13 hW d hK hQ hp hL.fac₂).2.1
  have h711 := (h.yamada_7_11 hW d hK hQ hp hL).2
  have hzcN₁ := (h.yamada_7_6 hW d hK hQ hp hL.fac₁).2.1.1
  have hAK₃ : leviFactor₂ hp.Astar Λ₂ ≤ yamadaK₃ d t Λ₂ :=
    inf_le_inf_left Λ₂ (hp.Astar_spec.le_cen.trans
      (le_sup_left : yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G) ≤ _))
  exact ProductDecompAux.master (F := K) (t := t) (q := Nat.card K)
    (P := yamadaP d t) (U := yamadaU₁ d t) (D7 := yamadaD₇ d t) (M6 := yamadaM₆ d t)
    (N₁ := yamadaN₁ d t) (N₂ := yamadaN₂ d t) (Λ₁ := Λ₁) (Λ₂ := Λ₂)
    (A₁ := leviFactor₁ d Λ₁) (A₂ := leviFactor₂ hp.Astar Λ₂) (K1p := derived₁ Λ₁)
    (K2pp := derived₂ Λ₂) (B₁ := pCoreOf 2 (derived₁ Λ₁)) (O₂ := pCoreOf 2 (derived₂ Λ₂))
    (Z₃ := zc (yamadaK₃ d t Λ₂)) (Z₃' := zc ((yamadaK₃ d t Λ₂)ᵍ[t])) (J₃ := d.J₃)
    (S := d.S) (Fq := d.F) (Y := yamadaY₂ d t)
    h.t_mul_t rfl hPt hUt hD7t hS₁ hS₂ hp.sylow₁ hp.sylow₂ hPcard hUcard hM6card
    hUP hD7P hM6P hUM6 hYP hZPc hZcen
    (fun x hx y hy => mem_centralizer_iff.1
      (Subgroup.mem_inf.1 (hzcN₁ ▸ hx : x ∈ zc (yamadaN₁ d t))).2 y hy)
    rfl rfl h9a h9b h9c h9d h9e h9g h9j h9k
    rfl hN₂ hI₂ hc₂ hA₂ hM6 hM6i (hO₂.le.trans inf_le_left)
    hA₁perf inf_le_left hA₂M hΛA₂ hA₁D inf_le_left hΛA₁
    (glue_hRΛ₁ hW h d hK hQ hp hL hS₁ hS₂ hΛA₂)
    h713b.1.symm (glue_Z hW h d hK hQ hp hL)
    ((inf_le_right : zc (yamadaK₃ d t Λ₂) ≤ _).trans (Subgroup.centralizer_le hAK₃))
    ((le_sup_left : yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂ ≤ _).trans h711.ge)
    hJK hJKt
    (fun c hc x hx => mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 c hc)
    (fun x hx hfix => N60.eq_one_of_mem_yamadaU₁_of_forall_J₃ hW h d hK hQ hx hfix)
    ((inf_le_inf_left _ (inf_le_right.trans (hp.Astar_spec.le_cen.trans inf_le_right))).trans
      (inf_centralizer_J₄_le_yamadaD₇ hW h d hK hQ))
    hPP hSP hSF hFcard

theorem yamada_7_18 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₁ Λ₂ : Subgroup G}
    (hL : Labelled d t Λ₁ Λ₂) :
    yamadaP d t ⊓ derived₂ Λ₁ = yamadaP d t ⊓ derived₂ Λ₂ ∧
      yamadaP d t = (yamadaP d t ⊓ derived₂ Λ₁) ⊔ (yamadaP d t ⊓ derived₂ Λ₁)ᵍ[t] ∧
      (yamadaP d t ⊓ derived₂ Λ₁) ⊓ (yamadaP d t ⊓ derived₂ Λ₁)ᵍ[t] = ⊥ ∧
      Nat.card (yamadaP d t ⊓ derived₂ Λ₁ : Subgroup G) = Nat.card K ^ 6 := by
  have hPt : t ∈ normalizer (yamadaP d t : Set G) := (h.yamada_5_51 hW d hK hQ).1.2.1
  have hPt' : (yamadaP d t)ᵍ[t] = yamadaP d t :=
    TrialityD4.ProductCase.ProductDecompAux.conjT_eq_of_mem_normalizer hPt
  obtain ⟨⟨hN₁, hI₁, hc₁, hA₁, -, -, -⟩, h716⟩ := h.yamada_7_16 hW d hK hQ hp hL
  obtain ⟨⟨hN₂, hI₂, hc₂, hA₂, -, -, -⟩, -⟩ := h.yamada_7_15 hW d hK hQ hp hL
  have hcard : Nat.card (yamadaP d t) = (Nat.card K ^ 6) ^ 2 := by
    rw [(h.yamada_series_card hW d hK hQ).2.2.2.2.2, ← pow_mul]
  obtain ⟨hS₁, hPeq, hPinf, -, hcard₁⟩ :=
    ProductDecompAux.sylow_decomp hp.sylow₁ hN₁.symm hI₁ hc₁ hPt' hcard
  obtain ⟨hS₂, -⟩ := ProductDecompAux.sylow_decomp hp.sylow₂ hN₂.symm hI₂ hc₂ hPt' hcard
  refine ⟨?_, hPeq, hPinf, hcard₁⟩
  have hO₁ : pCoreOf 2 (derived₂ Λ₁) ≤ yamadaP d t ⊓ derived₂ Λ₁ :=
    ProductDecompAux.le_of_isSylowOf_of_le_normalizer hS₁ (LieType.BorelTits.pCoreOf_le 2 _)
      (le_normalizer_pCoreOf _) (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hO₂ : pCoreOf 2 (derived₂ Λ₂) ≤ yamadaP d t ⊓ derived₂ Λ₂ :=
    ProductDecompAux.le_of_isSylowOf_of_le_normalizer hS₂ (LieType.BorelTits.pCoreOf_le 2 _)
      (le_normalizer_pCoreOf _) (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have e₁ : yamadaP d t ⊓ derived₂ Λ₁ =
      (yamadaP d t ⊓ leviFactor₁ d Λ₁) ⊔ pCoreOf 2 (derived₂ Λ₁) := by
    conv_lhs => rw [hA₁]
    exact ProductDecompAux.inf_sup_eq_of_le_of_le_normalizer (hO₁.trans inf_le_left)
      ((hA₁ ▸ le_sup_left : leviFactor₁ d Λ₁ ≤ derived₂ Λ₁).trans (le_normalizer_pCoreOf _))
  have e₂ : yamadaP d t ⊓ derived₂ Λ₂ =
      (yamadaP d t ⊓ leviFactor₂ hp.Astar Λ₂) ⊔ pCoreOf 2 (derived₂ Λ₂) := by
    conv_lhs => rw [hA₂]
    exact ProductDecompAux.inf_sup_eq_of_le_of_le_normalizer (hO₂.trans inf_le_left)
      ((hA₂ ▸ le_sup_left : leviFactor₂ hp.Astar Λ₂ ≤ derived₂ Λ₂).trans (le_normalizer_pCoreOf _))
  rw [e₁, e₂]
  exact h716

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
