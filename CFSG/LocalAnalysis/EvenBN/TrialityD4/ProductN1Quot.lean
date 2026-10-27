module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Sylow
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModuleBridge
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB
public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplit

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def xQ (d : TrialityD4Data L q) (t : G) (K₁ : Subgroup G) : Subgroup G :=
  qOne d t K₁ ⊓ (qOne d t K₁)ᵍ[vG d]

@[expose] noncomputable def pZero (d : TrialityD4Data L q) (t : G) (K K₁ : Subgroup G) :
    Subgroup G :=
  qThree d t K ⊔ xQ d t K₁

end Defs

namespace ProductN1QuotAux

section Y8_D

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem bar_sup {A X Y : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hY : Y ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A (X ⊔ Y) = NormalizerQuotient.bar A X ⊔ NormalizerQuotient.bar A Y := by
  unfold NormalizerQuotient.bar
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem bar_inf {A X Y : Subgroup G} (hAX : A ≤ X) (hAY : A ≤ Y) :
    NormalizerQuotient.bar A (X ⊓ Y) = NormalizerQuotient.bar A X ⊓ NormalizerQuotient.bar A Y := by
  ext y
  obtain ⟨x, rfl⟩ := NormalizerQuotient.proj_surjective y
  rw [Subgroup.mem_inf, NormalizerQuotient.mem_bar_iff hAX, NormalizerQuotient.mem_bar_iff hAY,
    NormalizerQuotient.mem_bar_iff (le_inf hAX hAY), Subgroup.mem_inf]

theorem bar_commutator {A X Y : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hY : Y ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A ⁅X, Y⁆ = ⁅NormalizerQuotient.bar A X, NormalizerQuotient.bar A Y⁆ := by
  unfold NormalizerQuotient.bar
  have hXY : ⁅X, Y⁆ ≤ normalizer (A : Set G) := Subgroup.commutator_le_of_le hX hY
  have h1 : ⁅X, Y⁆.subgroupOf (normalizer (A : Set G)) =
      ⁅X.subgroupOf (normalizer (A : Set G)), Y.subgroupOf (normalizer (A : Set G))⁆ := by
    apply Subgroup.map_injective (normalizer (A : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hX, inf_of_le_left hY,
      inf_of_le_left hXY]
  rw [h1, Subgroup.map_commutator]

theorem bar_le_bar_iff {A X Y : Subgroup G} (hAY : A ≤ Y) (hX : X ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A X ≤ NormalizerQuotient.bar A Y ↔ X ≤ Y := by
  constructor
  · intro h x hx
    have := h (NormalizerQuotient.proj_mem_bar (x := ⟨x, hX hx⟩) hx)
    exact (NormalizerQuotient.mem_bar_iff hAY ⟨x, hX hx⟩).1 this
  · intro h
    exact NormalizerQuotient.bar_mono h

theorem bar_map_conj {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) (X : Subgroup G) :
    NormalizerQuotient.bar A (X.map (MulEquiv.toMonoidHom (MulAut.conj g⁻¹))) =
      (NormalizerQuotient.bar A X).map
        (MulEquiv.toMonoidHom (MulAut.conj (NormalizerQuotient.proj A ⟨g, hg⟩)⁻¹)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x₀, hx₀, hxz⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hz)
    have hxz' : g⁻¹ * x₀ * g = (z : G) := by simpa using hxz
    have hx₀N : x₀ ∈ normalizer (A : Set G) := by
      have : x₀ = g * (z : G) * g⁻¹ := by rw [← hxz']; group
      rw [this]
      exact mul_mem (mul_mem hg z.2) (inv_mem hg)
    refine ⟨NormalizerQuotient.proj A ⟨x₀, hx₀N⟩,
      ⟨⟨x₀, hx₀N⟩, Subgroup.mem_subgroupOf.2 hx₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [hxz']
  · rintro ⟨p, ⟨w, hw, rfl⟩, rfl⟩
    have hwX : (w : G) ∈ X := Subgroup.mem_subgroupOf.1 hw
    have hN : g⁻¹ * (w : G) * g ∈ normalizer (A : Set G) :=
      mul_mem (mul_mem (inv_mem hg) w.2) hg
    refine ⟨⟨g⁻¹ * (w : G) * g, hN⟩, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_map.2 ⟨w, hwX, by simp⟩), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem bar_pCoreOf {A X : Subgroup G} (hA : IsPGroup 2 A) (hAX : A ≤ X)
    (hXN : X ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A (pCoreOf 2 X) = pCoreOf 2 (NormalizerQuotient.bar A X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := NormalizerQuotient.bar A X with hB
  apply le_antisymm
  · have hAO : A ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAX hXN hA
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (NormalizerQuotient.bar_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
      (NormalizerQuotient.bar_le_normalizer_bar hAO
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)) ?_
    exact NormalizerQuotient.isPGroup_bar (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  · set O := pCoreOf 2 B with hO
    have hOB : O ≤ B := CFSG.LieType.BorelTits.pCoreOf_le 2 B
    set L := NormalizerQuotient.lift O with hL
    have hLX : L ≤ X := by
      have := NormalizerQuotient.lift_mono hOB
      rwa [NormalizerQuotient.lift_bar hAX hXN] at this
    have hL2 : IsPGroup 2 L :=
      NormalizerQuotient.isPGroup_lift hA (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B)
    have key : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
      intro x hx l hl
      have hxN : x ∈ normalizer (A : Set G) := hXN hx
      obtain ⟨hlN, hlO⟩ := NormalizerQuotient.mem_lift_iff.1 hl
      refine NormalizerQuotient.mem_lift_iff.2 ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hxN hlN) (inv_mem hxN)
      · have hxB : NormalizerQuotient.proj A ⟨x, hxN⟩ ∈ B :=
          NormalizerQuotient.proj_mem_bar hx
        have hnorm : B ≤ normalizer (O : Set (NormalizerQuotient.Bar A)) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
        have := (mem_normalizer_iff.1 (hnorm hxB) _).1 hlO
        have e : (NormalizerQuotient.proj A ⟨x, hxN⟩ * NormalizerQuotient.proj A ⟨l, hlN⟩ *
            (NormalizerQuotient.proj A ⟨x, hxN⟩)⁻¹) =
            NormalizerQuotient.proj A ⟨x * l * x⁻¹,
              mul_mem (mul_mem hxN hlN) (inv_mem hxN)⟩ := by
          rw [← map_inv, ← map_mul, ← map_mul]; rfl
        rwa [e] at this
    have hLnorm : X ≤ normalizer (L : Set G) := by
      intro x hx
      rw [mem_normalizer_iff]
      intro l
      constructor
      · exact key x hx l
      · intro h
        have := key x⁻¹ (inv_mem hx) _ h
        simpa [mul_assoc] using this
    have : L ≤ pCoreOf 2 X :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hLX hLnorm hL2
    calc O = NormalizerQuotient.bar A L := (NormalizerQuotient.bar_lift O).symm
      _ ≤ NormalizerQuotient.bar A (pCoreOf 2 X) := NormalizerQuotient.bar_mono this

theorem bar_isSylowOf {A R K : Subgroup G} (hAR : A ≤ R) (hK : K ≤ normalizer (A : Set G))
    (hRK : IsSylowOf 2 R K) :
    IsSylowOf 2 (NormalizerQuotient.bar A R) (NormalizerQuotient.bar A K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hRK
  refine CFSG.ABGLocalTools.isSylowOf_iff.2
    ⟨NormalizerQuotient.bar_mono hle, NormalizerQuotient.isPGroup_bar hp, ?_⟩
  have hRN : R ≤ normalizer (A : Set G) := hle.trans hK
  have h1 := NormalizerQuotient.card_bar_mul hAR hRN
  have h2 := NormalizerQuotient.card_bar_mul (hAR.trans hle) hK
  have h3 := Subgroup.relIndex_mul_card (H := NormalizerQuotient.bar A R)
    (K := NormalizerQuotient.bar A K)
  have h4 := Subgroup.relIndex_mul_card (H := R) (K := K)
  rw [inf_of_le_left (NormalizerQuotient.bar_mono hle)] at h3
  rw [inf_of_le_left hle] at h4
  have e : (NormalizerQuotient.bar A R).relIndex (NormalizerQuotient.bar A K) = R.relIndex K := by
    have hApos : 0 < Nat.card A := Nat.card_pos
    have hRpos : 0 < Nat.card (NormalizerQuotient.bar A R) := Nat.card_pos
    have : (NormalizerQuotient.bar A R).relIndex (NormalizerQuotient.bar A K) *
        Nat.card (NormalizerQuotient.bar A R) * Nat.card A =
        R.relIndex K * Nat.card (NormalizerQuotient.bar A R) * Nat.card A := by
      calc _ = Nat.card (NormalizerQuotient.bar A K) * Nat.card A := by rw [h3]
        _ = Nat.card K := h2
        _ = R.relIndex K * Nat.card R := h4.symm
        _ = _ := by rw [mul_assoc, h1]
    exact Nat.eq_of_mul_eq_mul_right hRpos (Nat.eq_of_mul_eq_mul_right hApos this)
  rw [e]
  exact hdvd

theorem bar_self (A : Subgroup G) : NormalizerQuotient.bar A A = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨x, hx, rfl⟩
  have hx' : (x : G) ∈ A := hx
  exact Subgroup.mem_bot.2 (NormalizerQuotient.proj_eq_one_iff.2 hx')

theorem bar_sup_self {A X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A (X ⊔ A) = NormalizerQuotient.bar A X := by
  rw [bar_sup hX Subgroup.le_normalizer, bar_self, sup_bot_eq]

theorem lift_bar_sup {A X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) :
    NormalizerQuotient.lift (NormalizerQuotient.bar A X) = X ⊔ A := by
  rw [← bar_sup_self hX]
  exact NormalizerQuotient.lift_bar le_sup_right (sup_le hX Subgroup.le_normalizer)

theorem lift_inf {A : Subgroup G} (Y Y' : Subgroup (NormalizerQuotient.Bar A)) :
    NormalizerQuotient.lift (Y ⊓ Y') = NormalizerQuotient.lift Y ⊓ NormalizerQuotient.lift Y' := by
  ext g
  rw [Subgroup.mem_inf, NormalizerQuotient.mem_lift_iff, NormalizerQuotient.mem_lift_iff,
    NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨⟨hg, h1⟩, ⟨hg, h2⟩⟩
  · rintro ⟨⟨hg, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hg, h1, h2⟩

theorem proj_mem_normalizer_bar {A X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgX : g ∈ normalizer (X : Set G)) :
    NormalizerQuotient.proj A ⟨g, hgA⟩ ∈
      normalizer ((NormalizerQuotient.bar A X : Subgroup (NormalizerQuotient.Bar A)) :
        Set (NormalizerQuotient.Bar A)) := by
  rw [mem_normalizer_iff]
  intro y
  obtain ⟨x, rfl⟩ := NormalizerQuotient.proj_surjective y
  have e : NormalizerQuotient.proj A ⟨g, hgA⟩ * NormalizerQuotient.proj A x *
      (NormalizerQuotient.proj A ⟨g, hgA⟩)⁻¹ =
      NormalizerQuotient.proj A (⟨g, hgA⟩ * x * ⟨g, hgA⟩⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [e, ← bar_sup_self hX]
  have hXA : A ≤ X ⊔ A := le_sup_right
  rw [NormalizerQuotient.mem_bar_iff hXA, NormalizerQuotient.mem_bar_iff hXA]
  have := mem_normalizer_iff.1 (mem_normalizer_sup hgX hgA) (x : G)
  simpa using this

theorem bar_inj {A X X' : Subgroup G} (hAX : A ≤ X) (hAX' : A ≤ X')
    (hX : X ≤ normalizer (A : Set G)) (hX' : X' ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A X = NormalizerQuotient.bar A X' ↔ X = X' := by
  constructor
  · intro h
    rw [← NormalizerQuotient.lift_bar hAX hX, ← NormalizerQuotient.lift_bar hAX' hX', h]
  · rintro rfl
    rfl

end Y8_D

section Y8_SL

open Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

structure NatSL2 (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ) (K E Q : Subgroup G) :
    Prop where
  two_le : 2 ≤ n
  card_k : Nat.card k = 2 ^ n
  E_le : E ≤ K
  E_le_Q : E ≤ Q
  Q_le : Q ≤ K
  iso : IsQuotientIso K E SL(2, k)
  E_comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  E_sq : ∀ x ∈ E, x * x = 1
  card_E : Nat.card E = (2 ^ n) ^ 2
  card_Q : Nat.card Q = 2 ^ n * Nat.card E
  card_fix : Nat.card (E ⊓ centralizer (Q : Set G) : Subgroup G) = 2 ^ n

variable {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ} {K E Q : Subgroup G}

theorem NatSL2.exists_phi (H : NatSL2 k n K E Q) :
    ∃ φ : ↥K →* SL(2, k), Function.Surjective φ ∧ φ.ker = E.subgroupOf K ∧
      (Q.subgroupOf K).map φ = CFSG.Timmesfeld.upperUnipotent k := by
  obtain ⟨φ₀, hs, hk⟩ := H.iso
  have hU : Nat.card ((Q.subgroupOf K).map φ₀) = Nat.card k := by
    rw [← Subgroup.relIndex_ker, hk, Subgroup.relIndex_subgroupOf H.Q_le]
    have h1 := Subgroup.relIndex_mul_card E Q
    rw [inf_of_le_left H.E_le_Q] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    rw [H.card_k]
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, H.card_Q])
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_conj_eq_upperUnipotent H.card_k hU
  refine ⟨(MulAut.conj g).toMonoidHom.comp φ₀, ?_, ?_, ?_⟩
  · exact (MulAut.conj g).surjective.comp hs
  · rw [MonoidHom.ker_comp_of_injective φ₀ _ (MulAut.conj g).injective]
    exact hk
  · rw [← Subgroup.map_map]
    exact hg

section SL2Facts

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open CFSG.LocalAnalysis.EvenBN.Common

@[expose] noncomputable def diagHomSL (k : Type) [Field k] : kˣ →* SL(2, k) where
  toFun := diagElt
  map_one' := diagElt_one
  map_mul' c d := (diagElt_mul_diagElt c d).symm

theorem diagHomSL_apply {k : Type} [Field k] (c : kˣ) : diagHomSL k c = diagElt c := rfl

theorem diagHomSL_injective {k : Type} [Field k] : Function.Injective (diagHomSL k) := by
  intro c d h
  have := congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [diagHomSL_apply, coe_diagElt] at this
  exact Units.ext (by simpa using this)

theorem card_diagHomSL_range {k : Type} [Field k] [Finite k] :
    Nat.card (diagHomSL k).range = Nat.card k - 1 :=
  (Nat.card_congr (MonoidHom.ofInjective diagHomSL_injective).toEquiv).symm.trans
    (Nat.card_units k)

theorem coe_conj_upperElt {k : Type} [Field k] (g : SL(2, k)) (t : k) :
    ((g * upperElt k t * g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      !![1 - (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 * t,
        (g : Matrix (Fin 2) (Fin 2) k) 0 0 ^ 2 * t;
        -((g : Matrix (Fin 2) (Fin 2) k) 1 0 ^ 2 * t),
        1 + (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 * t] := by
  obtain ⟨a, b, c, d, h, rfl⟩ := exists_eq_mkSL g
  rw [mkSL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mkSL, coe_upperElt, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem conj_upper_mem_of_apply_zero {k : Type} [Field k] {g : SL(2, k)}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) {x : SL(2, k)}
    (hx : x ∈ CFSG.Timmesfeld.upperUnipotent k) :
    g * x * g⁻¹ ∈ CFSG.Timmesfeld.upperUnipotent k := by
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).1 hx
  rw [mem_upperUnipotent_iff]
  refine ⟨(g : Matrix (Fin 2) (Fin 2) k) 0 0 ^ 2 * t, ?_⟩
  ext i j
  rw [coe_conj_upperElt]
  fin_cases i <;> fin_cases j <;> simp [coe_upperElt, hg]

theorem mem_normalizer_upper_of_apply_zero {k : Type} [Field k] {g : SL(2, k)}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    g ∈ normalizer (CFSG.Timmesfeld.upperUnipotent k : Set SL(2, k)) := by
  have hg' : ((g⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hg]
  refine mem_normalizer_of_conj_mem (fun h hh => conj_upper_mem_of_apply_zero hg hh) fun h hh => ?_
  simpa using conj_upper_mem_of_apply_zero hg' hh

theorem upper_inf_conj_eq_bot {k : Type} [Field k] {g : SL(2, k)}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    CFSG.Timmesfeld.upperUnipotent k ⊓
      (CFSG.Timmesfeld.upperUnipotent k).map (MulEquiv.toMonoidHom (MulAut.conj g)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, y, hy, rfl⟩
  obtain ⟨s, hs⟩ := (mem_upperUnipotent_iff k).1 hx
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).1 hy
  have h1 := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 1 0) hs
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  rw [coe_conj_upperElt] at h1
  simp [coe_upperElt] at h1
  have ht : t = 0 := by
    rcases h1 with h1 | h1
    · exact absurd h1 hg
    · exact h1
  subst ht
  rw [upperElt_zero] at hs ⊢
  simp [MulEquiv.coe_toMonoidHom]

theorem sl2_commutator_top {k : Type} [Field k] [Finite k] (h4 : 4 ≤ Nat.card k) :
    ⁅(⊤ : Subgroup SL(2, k)), (⊤ : Subgroup SL(2, k))⁆ = ⊤ := by
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h4)
  have h := Group.IsPerfect.commutator_eq_top (G := SL(2, k))
  rwa [commutator_def] at h

theorem sl2_hom_trivial {k : Type} [Field k] [Finite k] (h4 : 4 ≤ Nat.card k) {A : Type}
    [CommGroup A] (f : SL(2, k) →* A) (g : SL(2, k)) : f g = 1 := by
  have hle : ⁅(⊤ : Subgroup SL(2, k)), (⊤ : Subgroup SL(2, k))⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [sl2_commutator_top h4] at hle
  exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top g))

end SL2Facts

section Action

open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule (actionFixed mem_actionFixed
  even_linear_two_half_fixed_module_transitivity)

theorem exists_conjAction {K E : Subgroup G} (hEK : E ≤ K) {k : Type} [Field k]
    (φ : ↥K →* SL(2, k)) (hs : Function.Surjective φ) (hker : φ.ker = E.subgroupOf K)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ ρ : SL(2, k) →* MulAut ↥E, ∀ (x : ↥K) (e : ↥E), ((ρ (φ x) e : ↥E) : G) = x * e * x⁻¹ := by
  have hnorm : K ≤ normalizer (E : Set G) := by
    have : (E.subgroupOf K).Normal := hker ▸ φ.normal_ker
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).1 this
  let c : ↥K →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hc : ∀ x e, ((c x e : ↥E) : G) = x * e * x⁻¹ := fun x e => rfl
  have hk : φ.ker ≤ c.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    ext e
    rw [hc]
    show (x : G) * e * (x : G)⁻¹ = e
    have := hcomm _ hx _ e.2
    rw [this, mul_inv_cancel_right]
  let ρ₀ := QuotientGroup.lift φ.ker c hk
  let ι := (QuotientGroup.quotientKerEquivOfSurjective φ hs).symm
  refine ⟨ρ₀.comp ι.toMonoidHom, fun x e => ?_⟩
  have hι : ι (φ x) = (x : ↥K ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hι, ρ₀, QuotientGroup.lift_mk]
  exact hc x e

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem actionFixed_top_eq_bot {A : Type} [CommGroup A] [Finite A] {n : ℕ} (hn : 2 ≤ n)
    (hk : Nat.card k = 2 ^ n) (hA : Nat.card A = (2 ^ n) ^ 2) (ρ : SL(2, k) →* MulAut A)
    (hρ : ρ ≠ 1) : actionFixed ρ ⊤ = ⊥ := by
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  by_contra hC
  set C := actionFixed ρ ⊤ with hCdef
  have hmap : ∀ j, C.map (ρ j : A →* A) = C := by
    intro j
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have h1 : ρ j c = c := hc j (Subgroup.mem_top j)
      show ρ j c ∈ C
      rw [h1]
      exact hc
    · intro hx
      exact ⟨x, hx, hx j (Subgroup.mem_top j)⟩
  haveI : C.Normal := Subgroup.normal_of_comm C
  set ρb := CFSG.SL2MinimalFaithful.quotientAction ρ C hmap with hρbdef
  by_cases hρb : ρb = 1
  · apply hρ
    refine MonoidHom.ext fun g => MulEquiv.ext fun a => ?_
    have hfix : ∀ h : SL(2, k), a⁻¹ * ρ h a ∈ C := by
      intro h
      have h1 : ρb h (a : A ⧸ C) = (a : A ⧸ C) := by
        rw [hρb]
        rfl
      rw [hρbdef, CFSG.SL2MinimalFaithful.quotientAction_mk] at h1
      exact QuotientGroup.eq.1 h1.symm
    let f : SL(2, k) →* A := MonoidHom.mk' (fun h => a⁻¹ * ρ h a) (fun h₁ h₂ => by
      have hc₂ := hfix h₂
      have e : ρ h₂ a = a * (a⁻¹ * ρ h₂ a) := by group
      show a⁻¹ * ρ (h₁ * h₂) a = (a⁻¹ * ρ h₁ a) * (a⁻¹ * ρ h₂ a)
      rw [map_mul, MulAut.mul_apply, e, map_mul, hfix h₂ h₁ (Subgroup.mem_top h₁)]
      group)
    have := sl2_hom_trivial h4 f g
    simp only [f, MonoidHom.mk'_apply] at this
    rw [MonoidHom.one_apply, MulAut.one_apply]
    exact (inv_mul_eq_one.1 this).symm
  · have hV : IsPGroup 2 (A ⧸ C) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 2 * n) (by rw [hA, ← pow_mul, mul_comm])
      exact hA2.to_quotient C
    have h1 := sl2_card_sq_le_of_ne_one (MulEquiv.refl SL(2, k)) hk hn ρb hV hρb
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
    have hCpos : 0 < Nat.card C := Nat.card_pos
    rw [hk] at h1
    rw [hA] at h2
    have h3 : Nat.card C ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have : (2 ^ n) ^ 2 * 2 ≤ (2 ^ n) ^ 2 := by
        calc (2 ^ n) ^ 2 * 2 ≤ Nat.card (A ⧸ C) * Nat.card C := Nat.mul_le_mul h1 hlt
          _ = (2 ^ n) ^ 2 := h2.symm
      have hp : 0 < (2 ^ n) ^ 2 := by positivity
      omega
    exact hC (Subgroup.card_eq_one.1 (by omega))

variable {n : ℕ} {K E Q : Subgroup G}

theorem NatSL2.fixed_isPGroup (H : NatSL2 k n K E Q) {φ : ↥K →* SL(2, k)}
    (hs : Function.Surjective φ) (hker : φ.ker = E.subgroupOf K)
    (hQ : (Q.subgroupOf K).map φ = CFSG.Timmesfeld.upperUnipotent k)
    (x : ↥K) (e : G) (he : e ∈ E) (he1 : e ≠ 1) (hx : (x : G) * e * (x : G)⁻¹ = e) :
    ∃ m : ℕ, φ x ^ (2 ^ m) = 1 := by
  letI : CommGroup ↥E :=
    { (inferInstance : Group ↥E) with
      mul_comm := fun a b => Subtype.ext (H.E_comm a a.2 b b.2) }
  obtain ⟨ρ, hρ⟩ := exists_conjAction H.E_le φ hs hker H.E_comm
  have hA : Nat.card ↥E = (2 ^ n) ^ 2 := H.card_E
  have hρ1 : ρ ≠ 1 := by
    intro h1
    have hne : E ⊓ centralizer (Q : Set G) ≠ E := by
      intro heq
      have := H.card_fix
      rw [heq, H.card_E] at this
      have h2 : 2 ^ n < (2 ^ n) ^ 2 := by
        rw [sq]
        exact lt_mul_of_one_lt_right (by positivity)
          (Nat.one_lt_two_pow (by have := H.two_le; omega))
      exact h2.ne' this
    obtain ⟨e', he', hnc⟩ : ∃ e' ∈ E, e' ∉ centralizer (Q : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm inf_le_left fun y hy => Subgroup.mem_inf.2 ⟨hy, hcon y hy⟩)
    rw [Subgroup.mem_centralizer_iff] at hnc
    push Not at hnc
    obtain ⟨q, hq, hqe⟩ := hnc
    have h3 := hρ ⟨q, H.Q_le hq⟩ ⟨e', he'⟩
    rw [h1, MonoidHom.one_apply, MulAut.one_apply] at h3
    exact hqe (by
      have h4 : e' = q * e' * q⁻¹ := h3
      calc q * e' = q * e' * q⁻¹ * q := by group
        _ = e' * q := by rw [← h4])
  have hD := actionFixed_top_eq_bot H.two_le H.card_k hA ρ hρ1
  have hB : Nat.card (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)) = 2 ^ n := by
    rw [← H.card_fix]
    have hmap : (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)).map E.subtype =
        E ⊓ centralizer (Q : Set G) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine Subgroup.mem_inf.2 ⟨a.2, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
        have hqa := ha (φ ⟨q, H.Q_le hq⟩) (by
          rw [← hQ]
          exact ⟨⟨q, H.Q_le hq⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩)
        have h5 : (a : G) = q * a * q⁻¹ := by
          have := hρ ⟨q, H.Q_le hq⟩ a
          rw [hqa] at this
          exact this
        show q * (a : G) = (a : G) * q
        calc q * (a : G) = q * a * q⁻¹ * q := by group
          _ = a * q := by rw [← h5]
      · intro hy
        obtain ⟨hyE, hyc⟩ := Subgroup.mem_inf.1 hy
        refine ⟨⟨y, hyE⟩, fun u hu => ?_, rfl⟩
        rw [← hQ] at hu
        obtain ⟨x', hx', rfl⟩ := hu
        have hx'Q : (x' : G) ∈ Q := Subgroup.mem_subgroupOf.1 hx'
        apply Subtype.ext
        rw [hρ]
        have := Subgroup.mem_centralizer_iff.1 hyc _ hx'Q
        show (x' : G) * y * (x' : G)⁻¹ = y
        rw [this]
        group
    rw [← hmap, Subgroup.card_map_of_injective E.subtype_injective]
  obtain ⟨-, -, -, -, -, -, hsyl⟩ :=
    even_linear_two_half_fixed_module_transitivity H.card_k hA ρ hD hB
  obtain ⟨P, hP⟩ := hsyl ⟨e, he⟩ (fun h => he1 (congrArg Subtype.val h))
  have hmem : φ x ∈ P := (hP (φ x)).1 (by
    apply Subtype.ext
    rw [hρ]
    exact hx)
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨φ x, hmem⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

end Action

theorem NatSL2.exists_torus (H : NatSL2 k n K E Q) :
    ∃ T : Subgroup G, T ≤ K ∧ T ≤ normalizer (Q : Set G) ∧ Nat.card T = 2 ^ n - 1 ∧
      ∀ τ ∈ T, ∀ e ∈ E, τ * e * τ⁻¹ = e → τ = 1 ∨ e = 1 := by
  obtain ⟨φ, hs, hker, hQ⟩ := H.exists_phi
  set Tb : Subgroup SL(2, k) := (diagHomSL k).range with hTb
  have hTb_card : Nat.card Tb = 2 ^ n - 1 := by
    rw [hTb, card_diagHomSL_range, H.card_k]
  have hTb_norm : ∀ t ∈ Tb, t ∈ normalizer (CFSG.Timmesfeld.upperUnipotent k : Set SL(2, k)) := by
    rintro _ ⟨c, rfl⟩
    exact CFSG.Timmesfeld.ARS.NaturalModule.diagElt_mem_normalizer_upperUnipotent c
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := H.two_le; omega⟩
    subst hm
    rw [pow_succ]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    generalize 2 ^ m = a at h1 ⊢
    exact ⟨a - 1, by omega⟩
  have hmemQ : ∀ x : ↥K, φ x ∈ CFSG.Timmesfeld.upperUnipotent k → (x : G) ∈ Q := by
    intro x hx
    rw [← hQ] at hx
    obtain ⟨q', hq', hφq'⟩ := hx
    have hmem : (q'⁻¹ * x : ↥K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφq', inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    have hqQ : (q' : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq'
    have : (x : G) = (q' : G) * ((q'⁻¹ * x : ↥K) : G) := by simp
    rw [this]
    exact mul_mem hqQ (H.E_le_Q hmem)
  set KT : Subgroup ↥K := Tb.comap φ with hKT
  set N₀ : Subgroup ↥KT := φ.ker.subgroupOf KT with hN₀
  haveI hN₀n : N₀.Normal := (φ.normal_ker).subgroupOf KT
  let ψ : ↥KT →* ↥Tb := (φ.comp KT.subtype).codRestrict Tb (fun x => x.2)
  have hψs : Function.Surjective ψ := by
    intro t
    obtain ⟨x, hx⟩ := hs t.1
    exact ⟨⟨x, by rw [hKT, Subgroup.mem_comap, hx]; exact t.2⟩, Subtype.ext hx⟩
  have hψk : ψ.ker = N₀ := by
    ext y
    simp only [MonoidHom.mem_ker, hN₀, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcard1 : Nat.card N₀ * Nat.card Tb = Nat.card KT := by
    rw [← hψk]
    exact Subgroup.card_ker_mul_card_of_surjective hψs
  have hindex : N₀.index = 2 ^ n - 1 := by
    have h2 := Subgroup.card_mul_index N₀
    have hpos : 0 < Nat.card N₀ := Nat.card_pos
    rw [← hcard1, hTb_card] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hcop : Nat.Coprime (Nat.card N₀) N₀.index := by
    rw [hindex]
    have hN₀card : Nat.card N₀ = (2 ^ n) ^ 2 := by
      have hle : φ.ker ≤ KT := by
        intro x hx
        rw [hKT, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
        exact one_mem _
      rw [hN₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hker,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.E_le).toEquiv, H.card_E]
    rw [hN₀card]
    exact Nat.Coprime.pow_left 2 (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd))
  obtain ⟨T₀, hT₀⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hT₀card : Nat.card T₀ = 2 ^ n - 1 := by
    have h2 := hT₀.card_mul
    have hpos : 0 < Nat.card N₀ := Nat.card_pos
    rw [← hcard1] at h2
    rw [← hTb_card]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hTmem : ∀ τ ∈ (T₀.map KT.subtype).map K.subtype,
      ∃ y : ↥KT, y ∈ T₀ ∧ ((y : ↥K) : G) = τ := by
    intro τ hτ
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hτ
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨y, hy, rfl⟩
  refine ⟨(T₀.map KT.subtype).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  ·
    intro τ hτ
    obtain ⟨y, hy, rfl⟩ := hTmem τ hτ
    have hφy : φ (y : ↥K) ∈ Tb := y.2
    have key : ∀ (z : ↥K), φ z ∈ Tb → ∀ q ∈ Q, (z : G) * q * (z : G)⁻¹ ∈ Q := by
      intro z hz q hq
      have hqK : q ∈ K := H.Q_le hq
      have : φ (z * ⟨q, hqK⟩ * z⁻¹) ∈ CFSG.Timmesfeld.upperUnipotent k := by
        have h1 : φ ⟨q, hqK⟩ ∈ CFSG.Timmesfeld.upperUnipotent k := by
          rw [← hQ]
          exact ⟨⟨q, hqK⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩
        have h2 := (Subgroup.mem_normalizer_iff.1 (hTb_norm _ hz) (φ ⟨q, hqK⟩)).1 h1
        simpa [map_mul, map_inv] using h2
      exact hmemQ _ this
    refine CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_of_conj_mem (key (y : ↥K) hφy)
      fun q hq => ?_
    have hφy' : φ ((y : ↥K)⁻¹) ∈ Tb := by rw [map_inv]; exact inv_mem hφy
    simpa using key ((y : ↥K)⁻¹) hφy' q hq
  · rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective KT.subtype_injective, hT₀card]
  · intro τ hτ e he hτe
    obtain ⟨y, hy, rfl⟩ := hTmem τ hτ
    by_cases he1 : e = 1
    · exact Or.inr he1
    left
    obtain ⟨m, hm⟩ := H.fixed_isPGroup hs hker hQ (y : ↥K) e he he1 hτe
    have hφy : φ (y : ↥K) ∈ Tb := y.2
    have hdvd1 : orderOf (φ (y : ↥K)) ∣ 2 ^ n - 1 := by
      have := orderOf_dvd_natCard (⟨φ (y : ↥K), hφy⟩ : Tb)
      rwa [hTb_card, Subgroup.orderOf_mk] at this
    have hdvd2 : orderOf (φ (y : ↥K)) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    have hcop2 : Nat.Coprime (2 ^ n - 1) (2 ^ m) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
    have h1 : orderOf (φ (y : ↥K)) = 1 :=
      Nat.Coprime.eq_one_of_dvd (hcop2.coprime_dvd_left hdvd1) hdvd2
    have hφ1 : φ (y : ↥K) = 1 := orderOf_eq_one_iff.1 h1
    have hyN : y ∈ N₀ := by
      rw [hN₀, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact hφ1
    have : y = 1 := by
      have := Subgroup.disjoint_def.1 hT₀.disjoint hyN hy
      exact this
    rw [this]
    rfl

theorem NatSL2.K_le_normalizer (H : NatSL2 k n K E Q) : K ≤ normalizer (E : Set G) := by
  obtain ⟨φ, -, hker, -⟩ := H.exists_phi
  have : (E.subgroupOf K).Normal := hker ▸ φ.normal_ker
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer H.E_le).1 this

theorem NatSL2.mem_of_phi_mem (H : NatSL2 k n K E Q) {φ : ↥K →* SL(2, k)}
    (hker : φ.ker = E.subgroupOf K)
    (hQ : (Q.subgroupOf K).map φ = CFSG.Timmesfeld.upperUnipotent k) (x : ↥K)
    (hx : φ x ∈ CFSG.Timmesfeld.upperUnipotent k) : (x : G) ∈ Q := by
  rw [← hQ] at hx
  obtain ⟨q', hq', hφq'⟩ := hx
  have hmem : (q'⁻¹ * x : ↥K) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφq', inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hmem
  have hqQ : (q' : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq'
  have : (x : G) = (q' : G) * ((q'⁻¹ * x : ↥K) : G) := by simp
  rw [this]
  exact mul_mem hqQ (H.E_le_Q hmem)

theorem NatSL2.E_le_commutator (H : NatSL2 k n K E Q) : E ≤ ⁅K, K⁆ := by
  obtain ⟨T, hTK, hTN, hTcard, hfpf⟩ := H.exists_torus
  have hKN := H.K_le_normalizer
  haveI : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (H.E_comm a a.2 b b.2)⟩⟩
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := H.two_le; omega⟩
    subst hm
    rw [pow_succ]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    generalize 2 ^ m = a at h1 ⊢
    exact ⟨a - 1, by omega⟩
  have hNE : ⁅E, T⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro e he τ hτ
    have h1 : τ * e⁻¹ * τ⁻¹ ∈ E :=
      ((Subgroup.mem_normalizer_iff.1 (hKN (hTK hτ)) e⁻¹).1 (inv_mem he))
    have : ⁅e, τ⁆ = e * (τ * e⁻¹ * τ⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem he h1
  have hE_norm_N : E ≤ normalizer ((⁅E, T⁆ : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact H.E_comm m (hNE hm) x hx
  have hcop : (Nat.card T).Coprime (Nat.card E) := by
    rw [hTcard, H.card_E]
    exact Nat.Coprime.pow_right 2 (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd))
  have hTne : ∃ τ ∈ T, τ ≠ 1 := by
    have h1 : 1 < Nat.card T := by
      rw [hTcard]
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) H.two_le
      omega
    haveI := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨⟨τ, hτ⟩, h2⟩ := exists_ne (1 : T)
    exact ⟨τ, hτ, fun h => h2 (Subtype.ext h)⟩
  intro e he
  have hfix : ∀ s ∈ T, e⁻¹ * (s * e * s⁻¹) ∈ ⁅E, T⁆ := by
    intro s hs
    have := Subgroup.commutator_mem_commutator (inv_mem he) hs
    rw [commutatorElement_def] at this
    simpa [mul_assoc] using this
  obtain ⟨c, hc, m, hm, hec⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mem_inf_centralizer_mul_of_coprime (M := E)
      (N := ⁅E, T⁆) (S := T) hNE hE_norm_N (hTK.trans hKN)
      (Subgroup.normalizer_commutator_ge_right E T) inferInstance hcop he hfix
  obtain ⟨hcE, hcT⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨τ, hτ, hτ1⟩ := hTne
  have hc1 : c = 1 := by
    have h1 : τ * c * τ⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.1 hcT τ hτ
      rw [this, mul_inv_cancel_right]
    rcases hfpf τ hτ c hcE h1 with h | h
    · exact absurd h hτ1
    · exact h
  rw [hec, hc1, one_mul]
  exact Subgroup.commutator_mono H.E_le hTK (hm)

theorem NatSL2.K_le_commutator (H : NatSL2 k n K E Q) : K ≤ ⁅K, K⁆ := by
  obtain ⟨φ, hs, hker, hQ⟩ := H.exists_phi
  have h4 : 4 ≤ Nat.card k := by
    rw [H.card_k]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) H.two_le
  intro x hx
  have hc : (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆).map φ = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective φ hs,
      sl2_commutator_top h4]
  have hmem : φ ⟨x, hx⟩ ∈ (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆).map φ := by
    rw [hc]
    exact Subgroup.mem_top _
  obtain ⟨c, hcmem, hφc⟩ := hmem
  have hcK : (c : G) ∈ ⁅K, K⁆ := by
    have h1 := Subgroup.map_subtype_commutator K
    rw [commutator_def] at h1
    rw [← h1]
    exact ⟨c, hcmem, rfl⟩
  have hker' : (c⁻¹ * ⟨x, hx⟩ : ↥K) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφc, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf] at hker'
  have hxeq : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥K) : G) := by simp
  rw [hxeq]
  exact mul_mem hcK (H.E_le_commutator hker')

theorem NatSL2.conj_mem_of_phi_mem_normalizer (H : NatSL2 k n K E Q) {φ : ↥K →* SL(2, k)}
    (hker : φ.ker = E.subgroupOf K)
    (hQ : (Q.subgroupOf K).map φ = CFSG.Timmesfeld.upperUnipotent k) (z : ↥K)
    (hz : φ z ∈ normalizer (CFSG.Timmesfeld.upperUnipotent k : Set SL(2, k))) (q : G)
    (hq : q ∈ Q) : (z : G) * q * (z : G)⁻¹ ∈ Q := by
  have hqK : q ∈ K := H.Q_le hq
  have h1 : φ ⟨q, hqK⟩ ∈ CFSG.Timmesfeld.upperUnipotent k := by
    rw [← hQ]
    exact ⟨⟨q, hqK⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.1 hz (φ ⟨q, hqK⟩)).1 h1
  have : φ (z * ⟨q, hqK⟩ * z⁻¹) ∈ CFSG.Timmesfeld.upperUnipotent k := by
    simpa [map_mul, map_inv] using h2
  exact H.mem_of_phi_mem hker hQ _ this

theorem NatSL2.inf_conj (H : NatSL2 k n K E Q) {g : G} (hg : g ∈ K)
    (hgQ : g ∉ normalizer (Q : Set G)) :
    Q ⊓ Q.map (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) = E := by
  obtain ⟨φ, hs, hker, hQ⟩ := H.exists_phi
  have hĝ : ((φ ⟨g, hg⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
    intro h0
    apply hgQ
    have hn := mem_normalizer_upper_of_apply_zero h0
    refine CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_of_conj_mem
      (fun q hq => H.conj_mem_of_phi_mem_normalizer hker hQ ⟨g, hg⟩ hn q hq) (fun q hq => ?_)
    have := H.conj_mem_of_phi_mem_normalizer hker hQ (⟨g, hg⟩⁻¹) (by
      rw [map_inv]; exact inv_mem hn) q hq
    simpa using this
  have hĝ' : (((φ ⟨g, hg⟩)⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simpa using hĝ
  apply le_antisymm
  · intro x hx
    obtain ⟨hxQ, q, hq, rfl⟩ := Subgroup.mem_inf.1 hx
    have hxK : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) q ∈ K := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hg) (H.Q_le hq)) hg
    have h1 : φ ⟨_, hxK⟩ ∈ CFSG.Timmesfeld.upperUnipotent k ⊓
        (CFSG.Timmesfeld.upperUnipotent k).map
          (MulEquiv.toMonoidHom (MulAut.conj (φ ⟨g, hg⟩)⁻¹)) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [← hQ]
        exact ⟨⟨_, hxK⟩, Subgroup.mem_subgroupOf.2 hxQ, rfl⟩
      · have hqK : q ∈ K := H.Q_le hq
        refine ⟨φ ⟨q, hqK⟩, ?_, ?_⟩
        · rw [← hQ]
          exact ⟨⟨q, hqK⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩
        · have : (⟨_, hxK⟩ : ↥K) = ⟨g, hg⟩⁻¹ * ⟨q, hqK⟩ * ⟨g, hg⟩ := by
            apply Subtype.ext
            simp [MulAut.conj_apply]
          rw [this, map_mul, map_mul, map_inv]
          simp [MulAut.conj_apply]
    rw [upper_inf_conj_eq_bot hĝ', Subgroup.mem_bot] at h1
    have : (⟨_, hxK⟩ : ↥K) ∈ φ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact this
  · intro e he
    refine Subgroup.mem_inf.2 ⟨H.E_le_Q he, ?_⟩
    have hKN := H.K_le_normalizer
    have h1 : g * e * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hKN hg) e).1 he
    refine ⟨g * e * g⁻¹, H.E_le_Q h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem NatSL2.sup_conj (H : NatSL2 k n K E Q) {g : G} (hg : g ∈ K)
    (hgQ : g ∉ normalizer (Q : Set G)) :
    Q ⊔ Q.map (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) = K := by
  obtain ⟨φ, hs, hker, hQ⟩ := H.exists_phi
  have hĝ : ((φ ⟨g, hg⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
    intro h0
    apply hgQ
    have hn := mem_normalizer_upper_of_apply_zero h0
    refine CFSG.LocalAnalysis.EvenBN.Common.mem_normalizer_of_conj_mem
      (fun q hq => H.conj_mem_of_phi_mem_normalizer hker hQ ⟨g, hg⟩ hn q hq) (fun q hq => ?_)
    have := H.conj_mem_of_phi_mem_normalizer hker hQ (⟨g, hg⟩⁻¹) (by
      rw [map_inv]; exact inv_mem hn) q hq
    simpa using this
  have hĝ' : (((φ ⟨g, hg⟩)⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simpa using hĝ
  have hgen :=
    CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule.upperUnipotent_sup_map_conj_eq_top hĝ'
  apply le_antisymm
  · refine sup_le H.Q_le ?_
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact mul_mem (mul_mem (inv_mem hg) (H.Q_le hq)) hg
  · intro x hx
    have hmem : φ ⟨x, hx⟩ ∈ CFSG.Timmesfeld.upperUnipotent k ⊔
        (CFSG.Timmesfeld.upperUnipotent k).map
          (MulEquiv.toMonoidHom (MulAut.conj (φ ⟨g, hg⟩)⁻¹)) := by
      rw [hgen]
      exact Subgroup.mem_top _
    set S : Subgroup ↥K := (Q ⊔ Q.map (MulEquiv.toMonoidHom (MulAut.conj g⁻¹))).subgroupOf K
    have hUS : CFSG.Timmesfeld.upperUnipotent k ≤ S.map φ := by
      rw [← hQ]
      refine Subgroup.map_mono fun y hy => ?_
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hy))
    have hUS' : (CFSG.Timmesfeld.upperUnipotent k).map
        (MulEquiv.toMonoidHom (MulAut.conj (φ ⟨g, hg⟩)⁻¹)) ≤ S.map φ := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← hQ] at hu
      obtain ⟨q', hq', rfl⟩ := hu
      have hqQ : (q' : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq'
      have hmK : g⁻¹ * (q' : G) * g ∈ K := mul_mem (mul_mem (inv_mem hg) q'.2) hg
      refine ⟨⟨g⁻¹ * (q' : G) * g, hmK⟩, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right ⟨q', hqQ, ?_⟩)
        simp [MulAut.conj_apply]
      · have : (⟨g⁻¹ * (q' : G) * g, hmK⟩ : ↥K) = ⟨g, hg⟩⁻¹ * q' * ⟨g, hg⟩ := by
          apply Subtype.ext
          simp
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [this, map_mul, map_mul, map_inv]
    obtain ⟨s, hsS, hφs⟩ := (sup_le hUS hUS') hmem
    have hker' : (s⁻¹ * ⟨x, hx⟩ : ↥K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφs, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hker'
    have hsS' : (s : G) ∈ Q ⊔ Q.map (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) :=
      Subgroup.mem_subgroupOf.1 hsS
    have hxeq : x = (s : G) * ((s⁻¹ * ⟨x, hx⟩ : ↥K) : G) := by simp
    rw [hxeq]
    exact mul_mem hsS' (Subgroup.mem_sup_left (H.E_le_Q hker'))

theorem NatSL2.inf_centralizer_eq_bot (H : NatSL2 k n K E Q) :
    E ⊓ centralizer (K : Set G) = ⊥ := by
  obtain ⟨T, hTK, -, hTcard, hTfpf⟩ := H.exists_torus
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) H.two_le
  have hne : ∃ τ ∈ T, τ ≠ 1 := by
    have h1 : 1 < Nat.card T := by rw [hTcard]; omega
    haveI := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨⟨τ, hτ⟩, h2⟩ := exists_ne (1 : T)
    exact ⟨τ, hτ, fun h => h2 (Subtype.ext h)⟩
  obtain ⟨τ, hτ, hτ1⟩ := hne
  rw [eq_bot_iff]
  rintro e ⟨heE, heC⟩
  have hc : τ * e * τ⁻¹ = e := by
    have := mem_centralizer_iff.1 heC τ (hTK hτ)
    rw [this]
    group
  rcases hTfpf τ hτ e heE hc with h1 | h1
  · exact absurd h1 hτ1
  · exact mem_bot.2 h1

end Y8_SL

section Y8_IS

open Subgroup
open CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  rw [pow_succ]
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  generalize 2 ^ m = a at h1 ⊢
  exact ⟨a - 1, by omega⟩

theorem fpf_mod {E Z T : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcardE : Nat.card E = (2 ^ n) ^ 2)
    (hZE : Z ≤ E) (hTE : T ≤ normalizer (E : Set G)) (hTZ : T ≤ normalizer (Z : Set G))
    (hT_card : Nat.card T = 2 ^ n - 1)
    (hT_fpf : ∀ τ ∈ T, ∀ e ∈ E, τ * e * τ⁻¹ = e → τ = 1 ∨ e = 1)
    {τ : G} (hτ : τ ∈ T) (hτ1 : τ ≠ 1) {e : G} (he : e ∈ E)
    (hfix : e⁻¹ * (τ * e * τ⁻¹) ∈ Z) : e ∈ Z := by
  haveI : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEab a a.2 b b.2)⟩⟩
  let Fix : Subgroup G :=
    { carrier := {s | s ∈ T ∧ e⁻¹ * (s * e * s⁻¹) ∈ Z}
      mul_mem' := by
        rintro s s' ⟨hs, hsZ⟩ ⟨hs', hs'Z⟩
        refine ⟨mul_mem hs hs', ?_⟩
        have h1 : s * s' * e * (s * s')⁻¹ = s * (s' * e * s'⁻¹) * s⁻¹ := by group
        have h2 : s' * e * s'⁻¹ = e * (e⁻¹ * (s' * e * s'⁻¹)) := by group
        have h3 : s * e * s⁻¹ = e * (e⁻¹ * (s * e * s⁻¹)) := by group
        have h4 : e⁻¹ * (s * s' * e * (s * s')⁻¹) =
            (e⁻¹ * (s * e * s⁻¹)) * (s * (e⁻¹ * (s' * e * s'⁻¹)) * s⁻¹) := by
          rw [h1]
          conv_lhs => rw [h2]
          group
        rw [h4]
        refine mul_mem hsZ ?_
        exact (Subgroup.mem_normalizer_iff.1 (hTZ hs) _).1 hs'Z
      one_mem' := ⟨one_mem T, by simp⟩
      inv_mem' := by
        rintro s ⟨hs, hsZ⟩
        refine ⟨inv_mem hs, ?_⟩
        have h1 : e⁻¹ * (s⁻¹ * e * s⁻¹⁻¹) =
            (s⁻¹ * (e⁻¹ * (s * e * s⁻¹)) * s⁻¹⁻¹)⁻¹ := by group
        rw [h1]
        refine inv_mem ?_
        exact (Subgroup.mem_normalizer_iff.1 (hTZ (inv_mem hs)) _).1 hsZ }
  have hFixT : Fix ≤ T := fun s hs => hs.1
  have hτFix : τ ∈ Fix := ⟨hτ, hfix⟩
  have hodd : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
  have hcop : (Nat.card Fix).Coprime (Nat.card E) := by
    have h1 : Nat.card Fix ∣ 2 ^ n - 1 := hT_card ▸ Subgroup.card_dvd_of_le hFixT
    rw [hcardE]
    exact (Nat.Coprime.pow_right 2 (Nat.Coprime.pow_right n
      (Nat.coprime_two_right.2 hodd))).coprime_dvd_left h1
  have hEN : E ≤ normalizer (Z : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hEab z (hZE hz) x hx
  obtain ⟨c, hc, z, hz, hcz⟩ :=
    exists_mem_inf_centralizer_mul_of_coprime (M := E) (N := Z) (S := Fix) hZE hEN
      (hFixT.trans hTE) (hFixT.trans hTZ) inferInstance hcop he (fun s hs => hs.2)
  obtain ⟨hcE, hcF⟩ := Subgroup.mem_inf.1 hc
  have hc1 : c = 1 := by
    have h1 : τ * c * τ⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.1 hcF τ hτFix, mul_inv_cancel_right]
    rcases hT_fpf τ hτ c hcE h1 with h | h
    · exact absurd h hτ1
    · exact h
  rw [hcz, hc1, one_mul]
  exact hz

theorem regular_of_fpf {E Z T B : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcardE : Nat.card E = (2 ^ n) ^ 2)
    (hcardZ : Nat.card Z = 2 ^ n) (hZE : Z ≤ E) (hTE : T ≤ normalizer (E : Set G))
    (hTZ : T ≤ normalizer (Z : Set G)) (hT_card : Nat.card T = 2 ^ n - 1)
    (hT_fpf : ∀ τ ∈ T, ∀ e ∈ E, τ * e * τ⁻¹ = e → τ = 1 ∨ e = 1)
    (hZB : Z ≤ B) (hBE : B ≤ E) (hTB : ∀ τ ∈ T, ∀ b ∈ B, τ * b * τ⁻¹ ∈ B) :
    B = Z ∨ B = E := by
  by_cases hBZ : B ≤ Z
  · exact Or.inl (le_antisymm hBZ hZB)
  right
  obtain ⟨b, hbB, hbZ⟩ := Set.not_subset.1 hBZ
  haveI : IsMulCommutative B :=
    ⟨⟨fun x y => Subtype.ext (hEab x (hBE x.2) y (hBE y.2))⟩⟩
  haveI : (Z.subgroupOf B).Normal := Subgroup.normal_of_comm _
  let F : Option ↥T → ↥B ⧸ Z.subgroupOf B := fun o =>
    match o with
    | none => 1
    | some τ => ((⟨(τ : G) * b * (τ : G)⁻¹, hTB τ τ.2 b hbB⟩ : ↥B) : ↥B ⧸ Z.subgroupOf B)
  have hτnot : ∀ τ : T, (τ : G) * b * (τ : G)⁻¹ ∉ Z := by
    intro τ hτ
    apply hbZ
    have := (Subgroup.mem_normalizer_iff.1 (hTZ (inv_mem τ.2)) _).1 hτ
    simpa [mul_assoc] using this
  have hinj : Function.Injective F := by
    rintro (_ | τ) (_ | τ') h
    · rfl
    · exfalso
      have : (⟨(τ' : G) * b * (τ' : G)⁻¹, hTB τ' τ'.2 b hbB⟩ : ↥B) ∈ Z.subgroupOf B := by
        have h' : ((1 : ↥B) : ↥B ⧸ Z.subgroupOf B) = ((⟨(τ' : G) * b * (τ' : G)⁻¹,
            hTB τ' τ'.2 b hbB⟩ : ↥B) : ↥B ⧸ Z.subgroupOf B) := h
        rw [QuotientGroup.eq] at h'
        simpa using h'
      exact hτnot τ' (Subgroup.mem_subgroupOf.1 this)
    · exfalso
      have : (⟨(τ : G) * b * (τ : G)⁻¹, hTB τ τ.2 b hbB⟩ : ↥B) ∈ Z.subgroupOf B := by
        have h' : ((⟨(τ : G) * b * (τ : G)⁻¹, hTB τ τ.2 b hbB⟩ : ↥B) : ↥B ⧸ Z.subgroupOf B) =
            ((1 : ↥B) : ↥B ⧸ Z.subgroupOf B) := h
        rw [QuotientGroup.eq] at h'
        simpa using h'
      exact hτnot τ (Subgroup.mem_subgroupOf.1 this)
    · have h' : ((⟨(τ : G) * b * (τ : G)⁻¹, hTB τ τ.2 b hbB⟩ : ↥B) : ↥B ⧸ Z.subgroupOf B) =
          ((⟨(τ' : G) * b * (τ' : G)⁻¹, hTB τ' τ'.2 b hbB⟩ : ↥B) : ↥B ⧸ Z.subgroupOf B) := h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
      have h'' : ((τ : G) * b * (τ : G)⁻¹)⁻¹ * ((τ' : G) * b * (τ' : G)⁻¹) ∈ Z := by
        simpa using h'
      by_contra hne
      have hσ : (τ : G)⁻¹ * τ' ≠ 1 := by
        intro h1
        apply hne
        have : (τ : G) = τ' := by
          have h2 : (τ : G)⁻¹ * τ' = 1 := h1
          rw [inv_mul_eq_one] at h2
          exact h2
        rw [Subtype.ext this]
      have hσT : (τ : G)⁻¹ * τ' ∈ T := mul_mem (inv_mem τ.2) τ'.2
      have hbE : b ∈ E := hBE hbB
      have hfix : b⁻¹ * (((τ : G)⁻¹ * τ') * b * ((τ : G)⁻¹ * τ')⁻¹) ∈ Z := by
        have h3 := (Subgroup.mem_normalizer_iff.1 (hTZ (inv_mem τ.2)) _).1 h''
        have e : b⁻¹ * (((τ : G)⁻¹ * τ') * b * ((τ : G)⁻¹ * τ')⁻¹) =
            (τ : G)⁻¹ * (((τ : G) * b * (τ : G)⁻¹)⁻¹ * ((τ' : G) * b * (τ' : G)⁻¹)) *
              (τ : G)⁻¹⁻¹ := by group
        rw [e]
        exact h3
      exact hbZ (fpf_mod hn hEab hcardE hZE hTE hTZ hT_card hT_fpf hσT hσ hbE hfix)
  have hcard1 := Nat.card_le_card_of_injective F hinj
  rw [Finite.card_option] at hcard1
  have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf B)
  have hcard3 : Nat.card (Z.subgroupOf B) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, hcardZ]
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h4 : 2 ^ n ≤ Nat.card (↥B ⧸ Z.subgroupOf B) := by
    rw [hT_card, Nat.sub_add_cancel hone] at hcard1
    exact hcard1
  have h5 : Nat.card E ≤ Nat.card B := by
    rw [hcardE, hcard2, hcard3, sq]
    exact Nat.mul_le_mul_right _ h4
  exact Subgroup.eq_of_le_of_card_ge hBE h5

theorem independent_scalars {E E' Z Z' ZQ T T' : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hEE' : E ⊓ E' = ⊥) (hcomm : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE'ab : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x)
    (hZE : Z ≤ E) (hZE' : Z' ≤ E')
    (hcardE : Nat.card E = (2 ^ n) ^ 2) (hcardE' : Nat.card E' = (2 ^ n) ^ 2)
    (hcardZ : Nat.card Z = 2 ^ n) (hcardZ' : Nat.card Z' = 2 ^ n)
    (hZQ_le : ZQ ≤ E ⊔ E') (hV : Z ⊔ Z' ≤ ZQ) (hcardZQ : Nat.card ZQ = (2 ^ n) ^ 3)
    (hT_norm : T ≤ normalizer (E : Set G) ⊓ normalizer (Z : Set G) ⊓ normalizer (ZQ : Set G))
    (hT_cent : ∀ τ ∈ T, ∀ e ∈ E', τ * e = e * τ)
    (hT_card : Nat.card T = 2 ^ n - 1)
    (hT_fpf : ∀ τ ∈ T, ∀ e ∈ E, τ * e * τ⁻¹ = e → τ = 1 ∨ e = 1)
    (hT'_norm : T' ≤ normalizer (E' : Set G) ⊓ normalizer (Z' : Set G) ⊓ normalizer (ZQ : Set G))
    (hT'_cent : ∀ τ ∈ T', ∀ e ∈ E, τ * e = e * τ)
    (hT'_card : Nat.card T' = 2 ^ n - 1)
    (hT'_fpf : ∀ τ ∈ T', ∀ e ∈ E', τ * e * τ⁻¹ = e → τ = 1 ∨ e = 1) :
    ZQ = E ⊔ Z' ∨ ZQ = E' ⊔ Z := by
  have hn1 : 1 ≤ n := by omega
  have hone : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  obtain ⟨⟨hTE, hTZ⟩, hTZQ⟩ := (⟨⟨fun x hx => (hT_norm hx).1.1, fun x hx => (hT_norm hx).1.2⟩,
    fun x hx => (hT_norm hx).2⟩ :
      (T ≤ normalizer (E : Set G) ∧ T ≤ normalizer (Z : Set G)) ∧ T ≤ normalizer (ZQ : Set G))
  obtain ⟨⟨hT'E', hT'Z'⟩, hT'ZQ⟩ :=
    (⟨⟨fun x hx => (hT'_norm hx).1.1, fun x hx => (hT'_norm hx).1.2⟩,
      fun x hx => (hT'_norm hx).2⟩ :
      (T' ≤ normalizer (E' : Set G) ∧ T' ≤ normalizer (Z' : Set G)) ∧ T' ≤ normalizer (ZQ : Set G))
  have hdis : Disjoint E E' := disjoint_iff.2 hEE'
  have hE'N : E' ≤ normalizer (E : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  have hEN' : E ≤ normalizer (E' : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have hZZQ : Z ≤ ZQ := le_sup_left.trans hV
  have hZ'ZQ : Z' ≤ ZQ := le_sup_right.trans hV
  have hB1 : ZQ ⊓ E = Z ∨ ZQ ⊓ E = E :=
    regular_of_fpf hn1 hEab hcardE hcardZ hZE hTE hTZ hT_card hT_fpf (B := ZQ ⊓ E)
      (le_inf hZZQ hZE) inf_le_right (fun τ hτ b hb =>
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hTZQ hτ) b).1 (Subgroup.mem_inf.1 hb).1,
          (Subgroup.mem_normalizer_iff.1 (hTE hτ) b).1 (Subgroup.mem_inf.1 hb).2⟩)
  have hB2 : ZQ ⊓ E' = Z' ∨ ZQ ⊓ E' = E' :=
    regular_of_fpf hn1 hE'ab hcardE' hcardZ' hZE' hT'E' hT'Z' hT'_card hT'_fpf (B := ZQ ⊓ E')
      (le_inf hZ'ZQ hZE') inf_le_right (fun τ hτ b hb =>
        Subgroup.mem_inf.2
          ⟨(Subgroup.mem_normalizer_iff.1 (hT'ZQ hτ) b).1 (Subgroup.mem_inf.1 hb).1,
            (Subgroup.mem_normalizer_iff.1 (hT'E' hτ) b).1 (Subgroup.mem_inf.1 hb).2⟩)
  have hTne : ∃ τ ∈ T, τ ≠ 1 := by
    have h1 : 1 < Nat.card T := by
      rw [hT_card]
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    haveI := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨⟨τ, hτ⟩, h2⟩ := exists_ne (1 : T)
    exact ⟨τ, hτ, fun h => h2 (Subtype.ext h)⟩
  have hTne' : ∃ τ ∈ T', τ ≠ 1 := by
    have h1 : 1 < Nat.card T' := by
      rw [hT'_card]
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    haveI := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨⟨τ, hτ⟩, h2⟩ := exists_ne (1 : T')
    exact ⟨τ, hτ, fun h => h2 (Subtype.ext h)⟩
  rcases hB1 with h1 | h1
  · rcases hB2 with h2 | h2
    ·
      exfalso
      have hZZ'dis : Disjoint Z Z' := hdis.mono hZE hZE'
      have hZ'N : Z' ≤ normalizer (Z : Set G) := by
        refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact hcomm z (hZE hz) y (hZE' hy)
      have hcardZZ' := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z Z' hZ'N
        hZZ'dis
      have hle : ZQ ≤ Z ⊔ Z' := by
        intro a ha
        have ha' : a ∈ (E : Set G) * (E' : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left E E' hE'N]
          exact hZQ_le ha
        obtain ⟨e, he, e', he', rfl⟩ := ha'
        obtain ⟨τ, hτ, hτ1⟩ := hTne
        obtain ⟨τ', hτ', hτ'1⟩ := hTne'
        have heZ : e ∈ Z := by
          have h3 : τ * (e * e') * τ⁻¹ ∈ ZQ := (Subgroup.mem_normalizer_iff.1 (hTZQ hτ) _).1 ha
          have h4 : τ * (e * e') * τ⁻¹ = (τ * e * τ⁻¹) * e' := by
            have := hT_cent τ hτ e' he'
            calc τ * (e * e') * τ⁻¹ = (τ * e) * (e' * τ⁻¹) := by group
              _ = (τ * e) * (τ⁻¹ * (τ * e' * τ⁻¹)) := by group
              _ = (τ * e) * (τ⁻¹ * (e' * τ * τ⁻¹)) := by rw [this]
              _ = (τ * e * τ⁻¹) * e' := by group
          have hy : e⁻¹ * (τ * e * τ⁻¹) ∈ E :=
            mul_mem (inv_mem he) ((Subgroup.mem_normalizer_iff.1 (hTE hτ) e).1 he)
          have h5 : (e * e')⁻¹ * (τ * (e * e') * τ⁻¹) = e⁻¹ * (τ * e * τ⁻¹) := by
            rw [h4]
            have hc := hcomm _ hy e'⁻¹ (inv_mem he')
            calc (e * e')⁻¹ * ((τ * e * τ⁻¹) * e') = e'⁻¹ * (e⁻¹ * (τ * e * τ⁻¹)) * e' := by group
              _ = (e⁻¹ * (τ * e * τ⁻¹)) * e'⁻¹ * e' := by rw [← hc]
              _ = e⁻¹ * (τ * e * τ⁻¹) := by group
          have h6 : e⁻¹ * (τ * e * τ⁻¹) ∈ ZQ ⊓ E :=
            Subgroup.mem_inf.2 ⟨h5 ▸ mul_mem (inv_mem ha) h3, hy⟩
          rw [h1] at h6
          exact fpf_mod hn1 hEab hcardE hZE hTE hTZ hT_card hT_fpf hτ hτ1 he h6
        have he'Z' : e' ∈ Z' := by
          have h3 : τ' * (e * e') * τ'⁻¹ ∈ ZQ := (Subgroup.mem_normalizer_iff.1 (hT'ZQ hτ') _).1 ha
          have h4 : τ' * (e * e') * τ'⁻¹ = e * (τ' * e' * τ'⁻¹) := by
            have := hT'_cent τ' hτ' e he
            calc τ' * (e * e') * τ'⁻¹ = (τ' * e) * (e' * τ'⁻¹) := by group
              _ = (e * τ') * (e' * τ'⁻¹) := by rw [this]
              _ = e * (τ' * e' * τ'⁻¹) := by group
          have hy : e'⁻¹ * (τ' * e' * τ'⁻¹) ∈ E' :=
            mul_mem (inv_mem he') ((Subgroup.mem_normalizer_iff.1 (hT'E' hτ') e').1 he')
          have h5 : (e * e')⁻¹ * (τ' * (e * e') * τ'⁻¹) = e'⁻¹ * (τ' * e' * τ'⁻¹) := by
            rw [h4]
            group
          have h6 : e'⁻¹ * (τ' * e' * τ'⁻¹) ∈ ZQ ⊓ E' :=
            Subgroup.mem_inf.2 ⟨h5 ▸ mul_mem (inv_mem ha) h3, hy⟩
          rw [h2] at h6
          exact fpf_mod hn1 hE'ab hcardE' hZE' hT'E' hT'Z' hT'_card hT'_fpf hτ' hτ'1 he' h6
        exact mul_mem (Subgroup.mem_sup_left heZ) (Subgroup.mem_sup_right he'Z')
      have := Subgroup.card_le_of_le hle
      rw [hcardZZ', hcardZ, hcardZ', hcardZQ, ← sq] at this
      have h7 : (2 ^ n) ^ 2 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right hone (by norm_num)
      omega
    ·
      right
      have hE'ZQ : E' ≤ ZQ := by
        have := h2 ▸ (inf_le_left : ZQ ⊓ E' ≤ ZQ)
        exact inf_eq_right.1 h2 |> fun h => h
      have hZN : Z ≤ normalizer (E' : Set G) := hZE.trans hEN'
      have hdis' : Disjoint E' Z := hdis.symm.mono_right hZE
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E' Z hZN
        hdis'
      refine (Subgroup.eq_of_le_of_card_ge (sup_le hE'ZQ hZZQ) ?_).symm
      rw [hcard, hcardE', hcardZ, hcardZQ]
      exact (by ring : (2 ^ n) ^ 3 = (2 ^ n) ^ 2 * 2 ^ n).le
  ·
    left
    have hEZQ : E ≤ ZQ := inf_eq_right.1 h1
    have hZ'N : Z' ≤ normalizer (E : Set G) := hZE'.trans hE'N
    have hdis' : Disjoint E Z' := hdis.mono_right hZE'
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E Z' hZ'N hdis'
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hEZQ hZ'ZQ) ?_).symm
    rw [hcard, hcardE, hcardZ', hcardZQ]
    exact (by ring : (2 ^ n) ^ 3 = (2 ^ n) ^ 2 * 2 ^ n).le

end Y8_IS

section Y8_J

open Subgroup
open scoped commutatorElement

section Abstract

variable {X : Type} [Group X] {q : ℕ} (d : TrialityD4Data X q)

include d in
theorem fpf_M_mod_W (j : X) (μ ν : d.Γ) (hμ : μ ≠ 1) (hν : ν ≠ 1)
    (h1 : ∀ a, j * d.x₁ a * j⁻¹ = d.x₁ (μ * a)) (h3 : ∀ a, j * d.x₃ a * j⁻¹ = d.x₃ (ν * a))
    (hjW : j ∈ normalizer (d.W : Set X)) :
    ∀ m ∈ d.M, m * j * m⁻¹ * j⁻¹ ∈ d.W → m ∈ d.W := by
  have := d.finite
  intro m hm hcomm
  obtain ⟨z, n, hn, rfl⟩ := d.exists_mv_of_mem_M hm
  set z' : Fin 2 → d.Γ := ![μ * z 0, ν * z 1] with hz'
  have hmv : ∀ y : Fin 2 → d.Γ, d.mv y = d.x₁ (y 0) * d.x₃ (y 1) := fun y => rfl
  have hj : j * d.mv z * j⁻¹ = d.mv z' := by
    rw [hmv, hmv]
    have : j * (d.x₁ (z 0) * d.x₃ (z 1)) * j⁻¹ =
        (j * d.x₁ (z 0) * j⁻¹) * (j * d.x₃ (z 1) * j⁻¹) := by group
    rw [this, h1, h3]
    simp [hz']
  have hn'' : j * n * j⁻¹ ∈ d.W := (mem_normalizer_iff.1 hjW n).1 hn
  have hmvS : ∀ y : Fin 2 → d.Γ, d.mv y ∈ d.S := fun y =>
    mul_mem (d.U₁_le_S (d.x₁_mem_U₁ _)) (d.U₃_le_S (d.x₃_mem_U₃ _))
  set m := d.mv z * n with hm
  have hjm : j * m * j⁻¹ = d.mv z' * (j * n * j⁻¹) := by
    rw [hm]
    have : j * (d.mv z * n) * j⁻¹ = (j * d.mv z * j⁻¹) * (j * n * j⁻¹) := by group
    rw [this, hj]
  set w₁ := m * (j * m * j⁻¹)⁻¹ with hw₁
  have hw₁W : w₁ ∈ d.W := by
    have : m * (j * m * j⁻¹)⁻¹ = m * j * m⁻¹ * j⁻¹ := by group
    rw [hw₁, this]
    exact hcomm
  have hc : (d.mv z')⁻¹ * w₁ * d.mv z' ∈ d.W := by
    have hN : d.mv z' ∈ normalizer (d.W : Set X) := d.S_le_normalizer_W (hmvS z')
    have := (mem_normalizer_iff.1 (inv_mem hN) w₁).1 hw₁W
    simpa using this
  have hz : z = z' := by
    refine d.eq_of_mv_mul_eq (n := n) (n' := ((d.mv z')⁻¹ * w₁ * d.mv z') * (j * n * j⁻¹)) hn
      (mul_mem hc hn'') ?_
    have e : m = w₁ * (j * m * j⁻¹) := by rw [hw₁]; group
    rw [hjm] at e
    have e2 : d.mv z * n = d.mv z' * (((d.mv z')⁻¹ * w₁ * d.mv z') * (j * n * j⁻¹)) := by
      calc d.mv z * n = m := rfl
        _ = w₁ * (d.mv z' * (j * n * j⁻¹)) := e
        _ = _ := by group
    exact e2
  have hz0 : z 0 = 0 := by
    have h0 : z 0 = μ * z 0 := by
      have := congrFun hz 0
      simpa [hz'] using this
    have : (μ - 1) * z 0 = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hμ
    · exact h
  have hz1 : z 1 = 0 := by
    have h0 : z 1 = ν * z 1 := by
      have := congrFun hz 1
      simpa [hz'] using this
    have : (ν - 1) * z 1 = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hν
    · exact h
  have hmv0 : d.mv z = 1 := by
    rw [hmv, hz0, hz1, d.x₁_zero, d.x₃_zero, mul_one]
  rw [hm, hmv0, one_mul]
  exact hn

include d in
theorem triv_W_mod_Y (j : X) (h4 : ∀ a, j * d.x₄ a * j⁻¹ = d.x₄ a)
    (hjY : j ∈ normalizer (d.Y : Set X)) :
    ∀ w ∈ d.W, w * j * w⁻¹ * j⁻¹ ∈ d.Y := by
  have := d.finite
  intro w hw
  obtain ⟨a, n, hn, rfl⟩ := d.mem_W_iff.1 hw
  have hn' : j * n * j⁻¹ ∈ d.Y := (mem_normalizer_iff.1 hjY n).1 hn
  set u := d.x₄ a with hu
  have hc : j⁻¹ * u⁻¹ = u⁻¹ * j⁻¹ := by
    have h1 : j * u = u * j := by
      have := h4 a
      rw [← hu] at this
      calc j * u = j * u * j⁻¹ * j := by group
        _ = u * j := by rw [this]
    calc j⁻¹ * u⁻¹ = (u * j)⁻¹ := by group
      _ = (j * u)⁻¹ := by rw [h1]
      _ = u⁻¹ * j⁻¹ := by group
  have e : (u * n) * j * (u * n)⁻¹ * j⁻¹ = u * (n * (j * n * j⁻¹)⁻¹) * u⁻¹ := by
    calc (u * n) * j * (u * n)⁻¹ * j⁻¹ = u * n * j * n⁻¹ * (u⁻¹ * j⁻¹) := by group
      _ = u * n * j * n⁻¹ * (j⁻¹ * u⁻¹) := by rw [hc]
      _ = u * (n * (j * n * j⁻¹)⁻¹) * u⁻¹ := by group
  rw [e]
  have hy : n * (j * n * j⁻¹)⁻¹ ∈ d.Y := mul_mem hn (inv_mem hn')
  have huN : u ∈ normalizer (d.Y : Set X) :=
    d.S_le_normalizer_Y (d.U₄_le_S (d.x₄_mem_U₄ a))
  exact (mem_normalizer_iff.1 huN _).1 hy

end Abstract

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem exists_J4_element (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    ∃ j : G, j ∈ d.leviLong.map L.subtype ∧ Odd (orderOf j) ∧ j ∈ centralizer ({t} : Set G) ∧
      j ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ∧
      (∀ m ∈ d.M.map L.subtype, m * j * m⁻¹ * j⁻¹ ∈ d.W.map L.subtype →
        m ∈ d.W.map L.subtype) ∧
      (∀ w ∈ d.W.map L.subtype, w * j * w⁻¹ * j⁻¹ ∈ d.Y.map L.subtype) := by
  have hfin := d.finite
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨β, hβ⟩ : ∃ β : (d.Γ₀)ˣ, β ≠ 1 := by
    have h1 : 1 < Nat.card (d.Γ₀)ˣ := by rw [d.card_units_Γ₀]; omega
    haveI := Finite.one_lt_card_iff_nontrivial.1 h1
    obtain ⟨β, hβ⟩ := exists_ne (1 : (d.Γ₀)ˣ)
    exact ⟨β, hβ⟩
  set j₀ : L := d.hA β with hj₀
  set β' : d.Γ := ((β : d.Γ₀) : d.Γ) with hβ'
  have hβ'0 : β' ≠ 0 := by
    have : (β : d.Γ₀) ≠ 0 := β.ne_zero
    exact fun h0 => this (Subtype.ext h0)
  have hβ'1 : β' ≠ 1 := by
    intro h1
    have h2 : ((β : d.Γ₀) : d.Γ) = ((1 : d.Γ₀) : d.Γ) := by simpa [hβ'] using h1
    exact hβ (Units.ext (Subtype.ext h2))
  have hsq : (((β ^ 2 : (d.Γ₀)ˣ) : d.Γ₀) : d.Γ) = β' ^ 2 := by
    simp [hβ', Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
  have hσβ : d.σ β' = β' := apply_coe_fixedSubfield _
  have hμ : (((d.unitsIncl β⁻¹ : d.Γˣ)) : d.Γ) = β'⁻¹ := by
    rw [d.coe_unitsIncl]
    simp [hβ']
  have h1 : ∀ a, j₀ * d.x₁ a * j₀⁻¹ = d.x₁ (β'⁻¹ * a) := by
    intro a
    rw [hj₀, d.hA_apply, d.torus_x₁, hμ]
  have h3 : ∀ a, j₀ * d.x₃ a * j₀⁻¹ = d.x₃ (β' * a) := by
    intro a
    rw [hj₀, d.hA_apply, d.torus_x₃]
    congr 1
    rw [hsq, hμ]
    field_simp
  have h4 : ∀ a, j₀ * d.x₄ a * j₀⁻¹ = d.x₄ a := by
    intro a
    rw [hj₀, d.hA_apply, d.torus_x₄]
    congr 1
    have e : d.σ (((d.unitsIncl β⁻¹ : d.Γˣ)) : d.Γ) = β'⁻¹ := by
      rw [hμ, map_inv₀, hσβ]
    rw [hsq, e, map_inv₀, hσβ]
    field_simp
  have hj₀J₄ : j₀ ∈ d.J₄ := by
    rw [d.J₄_eq_range_hA]
    exact ⟨β, rfl⟩
  have hj₀J : j₀ ∈ d.J := hj₀J₄.1
  have hsub : ∀ x : L, (x : G) ∈ d.W.map L.subtype ↔ x ∈ d.W := fun x =>
    Subgroup.mem_map_iff_mem L.subtype_injective
  refine ⟨(j₀ : G), ⟨j₀, d.J₄_le_leviLong hj₀J₄, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hdvd : orderOf j₀ ∣ 2 ^ f - 1 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hj₀, ← map_pow, ← d.card_units_Γ₀, pow_card_eq_one', map_one]
    have hodd : Odd (2 ^ f - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
      subst hm
      rw [pow_succ]
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      generalize 2 ^ m = a at h1 ⊢
      exact ⟨a - 1, by omega⟩
    rw [Subgroup.orderOf_coe]
    exact hodd.of_dvd_nat hdvd
  ·
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 h.htL j₀ j₀.2)
  ·
    have hN : j₀ ∈ normalizer (d.S : Set L) := d.J_le_normalizer_S hj₀J
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨j₀ * s * j₀⁻¹, (Subgroup.mem_normalizer_iff.1 hN s).1 hs, by simp⟩
    · rintro ⟨s, hs, hsx⟩
      refine ⟨j₀⁻¹ * s * j₀, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hN) s).1 hs
        simpa using this
      · have : (j₀ : G) * x * (j₀ : G)⁻¹ = s := hsx.symm
        calc ((j₀⁻¹ * s * j₀ : L) : G) = (j₀ : G)⁻¹ * s * j₀ := by simp
          _ = (j₀ : G)⁻¹ * ((j₀ : G) * x * (j₀ : G)⁻¹) * j₀ := by rw [this]
          _ = x := by group
  ·
    rintro _ ⟨m₀, hm₀, rfl⟩ hcomm
    have hjW : j₀ ∈ normalizer (d.W : Set L) := d.J_le_normalizer_W hj₀J
    have hμ1 : β'⁻¹ ≠ 1 := fun h' => hβ'1 (by rw [inv_eq_one] at h'; exact h')
    have : m₀ ∈ d.W := by
      refine fpf_M_mod_W d j₀ β'⁻¹ β' hμ1 hβ'1 h1 h3 hjW m₀ hm₀ ?_
      rw [← hsub]
      simpa using hcomm
    exact ⟨m₀, this, rfl⟩
  ·
    rintro _ ⟨w₀, hw₀, rfl⟩
    have hjY : j₀ ∈ normalizer (d.Y : Set L) := d.J_le_normalizer_Y hj₀J
    have := triv_W_mod_Y d j₀ h4 hjY w₀ hw₀
    exact ⟨_, this, by simp⟩

end Main

end Y8_J

section Y8_Gen

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement Pointwise

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_conj_iff {A : Subgroup G} {g x : G} : x ∈ Aᵍ[g] ↔ g * x * g⁻¹ ∈ A :=
  mem_map_conj_inv_iff

theorem conj_eq_of_mem_normalizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    Aᵍ[g] = A := by
  ext x
  rw [mem_conj_iff]
  exact (mem_normalizer_iff.1 hg x).symm

theorem conj_conj_of_mul_self {g : G} (hg : g * g = 1) (A : Subgroup G) : (Aᵍ[g])ᵍ[g] = A :=
  map_conj_inv_map_conj_inv hg A

theorem conj_mono {A B : Subgroup G} (g : G) (h : A ≤ B) : Aᵍ[g] ≤ Bᵍ[g] :=
  Subgroup.map_mono h

theorem card_conj (A : Subgroup G) (g : G) : Nat.card (Aᵍ[g] : Subgroup G) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conj_sup (A B : Subgroup G) (g : G) : (A ⊔ B)ᵍ[g] = Aᵍ[g] ⊔ Bᵍ[g] :=
  Subgroup.map_sup _ _ _

theorem conj_inf (A B : Subgroup G) (g : G) : (A ⊓ B)ᵍ[g] = Aᵍ[g] ⊓ Bᵍ[g] :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conj_commutator (A B : Subgroup G) (g : G) : ⁅A, B⁆ᵍ[g] = ⁅Aᵍ[g], Bᵍ[g]⁆ :=
  Subgroup.map_commutator _ _ _

theorem normalizer_le_normalizer_centralizer (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer ((centralizer (Q : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  have key : ∀ g' ∈ normalizer (Q : Set G), ∀ x ∈ centralizer (Q : Set G),
      g' * x * g'⁻¹ ∈ centralizer (Q : Set G) := by
    intro g' hg' x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : g'⁻¹ * q * g' ∈ Q := by
      have := (mem_normalizer_iff.1 (inv_mem hg') q).1 hq
      simpa using this
    have := Subgroup.mem_centralizer_iff.1 hx _ hq'
    calc q * (g' * x * g'⁻¹) = g' * ((g'⁻¹ * q * g') * x) * g'⁻¹ := by group
      _ = g' * (x * (g'⁻¹ * q * g')) * g'⁻¹ := by rw [this]
      _ = g' * x * g'⁻¹ * q := by group
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_zc (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer ((zc Q : Subgroup G) : Set G) := fun _ hg =>
  mem_normalizer_inf hg (normalizer_le_normalizer_centralizer Q hg)

theorem mem_normalizer_centerMod {V Q : Subgroup G} (hVQ : V ≤ Q) {g : G}
    (hV : g ∈ normalizer (V : Set G)) (hQ : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((centerMod V Q : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ normalizer (V : Set G), g' ∈ normalizer (Q : Set G) →
      ∀ x ∈ centerMod V Q, g' * x * g'⁻¹ ∈ centerMod V Q := by
    intro g' hV' hQ' x hx
    obtain ⟨hxQ, hxN, hxc⟩ := (mem_centerMod_iff hVQ).1 hx
    refine (mem_centerMod_iff hVQ).2 ⟨(mem_normalizer_iff.1 hQ' x).1 hxQ,
      mul_mem (mul_mem hV' hxN) (inv_mem hV'), fun a haQ haN => ?_⟩
    have ha'Q : g'⁻¹ * a * g' ∈ Q := by
      simpa using (mem_normalizer_iff.1 (inv_mem hQ') a).1 haQ
    have ha'N : g'⁻¹ * a * g' ∈ normalizer (V : Set G) :=
      mul_mem (mul_mem (inv_mem hV') haN) hV'
    have h1 := hxc _ ha'Q ha'N
    have h2 : g' * x * g'⁻¹ * a * (g' * x * g'⁻¹)⁻¹ * a⁻¹ =
        g' * (x * (g'⁻¹ * a * g') * x⁻¹ * (g'⁻¹ * a * g')⁻¹) * g'⁻¹ := by group
    rw [h2]
    exact (mem_normalizer_iff.1 hV' _).1 h1
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hV hQ x
  · intro hx
    have := key g⁻¹ (inv_mem hV) (inv_mem hQ) _ hx
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_series (P : Subgroup G) (i : ℕ) :
    normalizer (P : Set G) ≤
      normalizer (((Subgroup.upperCentralSeries ↥P i).map P.subtype : Subgroup G) : Set G) := by
  intro g hg
  have key : ∀ g' ∈ normalizer (P : Set G), ∀ x ∈ (Subgroup.upperCentralSeries ↥P i).map P.subtype,
      g' * x * g'⁻¹ ∈ (Subgroup.upperCentralSeries ↥P i).map P.subtype := by
    intro g' hg' x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : MulAut ↥P := (P.normalizerMonoidHom ⟨g', hg'⟩)
    have hφ : ((φ y : ↥P) : G) = g' * (y : G) * g'⁻¹ := rfl
    have hc := (inferInstance : (Subgroup.upperCentralSeries ↥P i).Characteristic).fixed φ
    have : φ y ∈ Subgroup.upperCentralSeries ↥P i := by
      have h2 : y ∈ (Subgroup.upperCentralSeries ↥P i).comap φ.toMonoidHom := by
        rw [hc]
        exact hy
      exact h2
    exact ⟨φ y, this, hφ⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem mem_sup_of_commute' {A C : Subgroup G} (hc : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) {x : G}
    (hx : x ∈ A ⊔ C) : ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  have hCN : C ≤ normalizer (A : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro c hc'
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hc c hc' a ha).symm
  have : x ∈ (A : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A C hCN]
    exact hx
  obtain ⟨a, ha, c, hc', rfl⟩ := this
  exact ⟨a, ha, c, hc', rfl⟩

theorem commute_sup_of_central {A₀ B₀ C : Subgroup G}
    (hCa : ∀ c ∈ C, ∀ x ∈ A₀, c * x = x * c) (hCb : ∀ c ∈ C, ∀ x ∈ B₀, c * x = x * c)
    (hCc : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c)
    (hAB : ∀ a ∈ A₀, ∀ b ∈ B₀, a * b = b * a) :
    ∀ x ∈ A₀ ⊔ C, ∀ y ∈ B₀ ⊔ C, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_commute' hCa hx
  obtain ⟨b, hb, c', hc', rfl⟩ := mem_sup_of_commute' hCb hy
  calc a * c * (b * c') = a * (c * b) * c' := by group
    _ = a * (b * c) * c' := by rw [hCb c hc b hb]
    _ = a * b * (c * c') := by group
    _ = b * a * (c' * c) := by rw [hAB a ha b hb, hCc c hc c' hc']
    _ = b * (a * c') * c := by group
    _ = b * (c' * a) * c := by rw [← hCa c' hc' a ha]
    _ = b * c' * (a * c) := by group

theorem centerMod_conj {V Q : Subgroup G} (hVQ : V ≤ Q) {g : G}
    (hg : g ∈ normalizer (V : Set G)) :
    (centerMod V Q)ᵍ[g] = centerMod V Qᵍ[g] := by
  have hVg : Vᵍ[g] = V := conj_eq_of_mem_normalizer hg
  have hVQg : V ≤ Qᵍ[g] := hVg ▸ conj_mono g hVQ
  ext x
  rw [mem_conj_iff, mem_centerMod_iff hVQ, mem_centerMod_iff hVQg]
  have hgi : g⁻¹ ∈ normalizer (V : Set G) := inv_mem hg
  constructor
  · rintro ⟨hxQ, hxN, hxc⟩
    refine ⟨mem_conj_iff.2 hxQ, ?_, fun a haQ haN => ?_⟩
    · have := mul_mem (mul_mem hgi hxN) hg
      simpa [mul_assoc] using this
    · have haQ' : g * a * g⁻¹ ∈ Q := mem_conj_iff.1 haQ
      have haN' : g * a * g⁻¹ ∈ normalizer (V : Set G) := mul_mem (mul_mem hg haN) hgi
      have := hxc _ haQ' haN'
      have e : x * a * x⁻¹ * a⁻¹ =
          g⁻¹ * ((g * x * g⁻¹) * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹) * g := by
        group
      rw [e]
      exact (mem_normalizer_iff.1 hgi _).1 (by simpa using this) |> fun h => by simpa using h
  · rintro ⟨hxQ, hxN, hxc⟩
    refine ⟨mem_conj_iff.1 hxQ, mul_mem (mul_mem hg hxN) hgi, fun a haQ haN => ?_⟩
    have haQ' : g⁻¹ * a * g ∈ Qᵍ[g] := by
      rw [mem_conj_iff]
      simpa [mul_assoc] using haQ
    have haN' : g⁻¹ * a * g ∈ normalizer (V : Set G) := mul_mem (mul_mem hgi haN) hg
    have := hxc _ haQ' haN'
    have e : g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ * a⁻¹ =
        g * (x * (g⁻¹ * a * g) * x⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hg _).1 this

theorem le_normalizer_of_commute' {A B : Subgroup G} (hc : ∀ x ∈ B, ∀ y ∈ A, x * y = y * x) :
    B ≤ normalizer (A : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hc x hx y hy).symm

theorem card_sup_mul_card_inf_of_commute' (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

theorem conj_mem_normalizer_conj {A : Subgroup G} {g : G} (t : G)
    (hg : g ∈ normalizer (A : Set G)) :
    t⁻¹ * g * t ∈ normalizer ((Aᵍ[t] : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_conj_iff, mem_conj_iff]
  have e : t * (t⁻¹ * g * t * x * (t⁻¹ * g * t)⁻¹) * t⁻¹ = g * (t * x * t⁻¹) * g⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 hg _

theorem mem_conj_iff' {A : Subgroup G} {t x : G} (hx : x ∈ Aᵍ[t]) :
    t * x * t⁻¹ ∈ A ∧ x = t⁻¹ * (t * x * t⁻¹) * t := ⟨mem_conj_iff.1 hx, by group⟩

end Generic


section Specific

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem cLV_le_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    cLV d ≤ nOne d t := by
  intro x hu
  have huN : x ∈ normalizer (yamadaD₅ d t : Set G) :=
    ProductN1HatAux.cLV_le_normalizer_D5 h d hp.layer hu
  have hmem : NormalizerQuotient.proj (yamadaD₅ d t) ⟨x, huN⟩ ∈ kBar d t :=
    NormalizerQuotient.proj_mem_bar hu
  have hkx : kBar d t ≤ xBar d t := fun x hx => Subgroup.subset_normalClosure hx
  have hperf : Group.IsPerfect (↥(kBar d t)) := by
    obtain ⟨e⟩ := (D1_centralizer_tbar h d hp).2.2.1.1
    have h4 : 4 ≤ Nat.card d.Γ := by
      rw [d.card_Γ]
      have := hp.two_le
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ f) ^ 3 := by
          calc 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
            _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
    have hSL := CFSG.LinearGroups.special_linear_dimension_two_perfect
      (CFSG.LocalAnalysis.EvenBN.Common.exists_finset_card_four (k := d.Γ) h4)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hperf' : Group.IsPerfect (↥((kBar d t).subgroupOf (xBar d t))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hkx).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hkx).symm.surjective
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual _ hperf'
  have hkn : kBar d t ≤ nOneBar d t := by
    intro x hx
    exact ⟨⟨x, hkx hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  exact NormalizerQuotient.mem_lift_iff.2 ⟨huN, hkn hmem⟩

theorem u_mem_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    uG d ∈ nOne d t :=
  cLV_le_nOne h d hp ⟨d.u, d.u_mem_centralizer_V, rfl⟩

theorem nOne_le_normalizer {K₁ : Subgroup G} {d : TrialityD4Data L (2 ^ f)}
    (hK₁ : IsN1Factor d t K₁) : nOne d t ≤ normalizer (K₁ : Set G) := by
  rw [hK₁.sup_eq]
  refine sup_le Subgroup.le_normalizer ?_
  rw [Subgroup.le_normalizer_iff_commutator_le_right, commutator_comm]
  exact hK₁.comm_le.trans hK₁.D₅_le

end Specific

end Y8_Gen

section Y8_G0

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement Pointwise

section G0

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem eOne_comm (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    ∀ x ∈ eOne d t K, ∀ y ∈ eOne d t K, x * y = y * x := by
  obtain ⟨-, -, ⟨-, -, hEel, -, -, -, -⟩⟩ := A2_sylow h d hp hK
  exact fun x hx y hy => congrArg Subtype.val (hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem qThree_le_kThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K : Subgroup G} (hK : IsLayerComponent d t K) :
    qThree d t K ≤ kThree d t K := by
  obtain ⟨-, ⟨-, -, -, hQSyl, -⟩, ⟨-, -, -, -, hEQ, hEQn, -⟩⟩ := A2_sylow h d hp hK
  have hQN : qThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEQ).1 hEQn
  have hQ2 := hQSyl.isPGroup
  intro x hx
  refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨(inf_le_right : qThree d t K ≤ K) hx,
    hQN hx⟩, ?_⟩
  obtain ⟨k, hk⟩ := hQ2 ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem natSL2_layer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    NatSL2 d.Γ₀ f (kThree d t K) (eOne d t K) (qThree d t K) := by
  obtain ⟨⟨hXY, hXSyl, hXcard⟩, ⟨hXQ, hQQt, hQQc, hQSyl, hQcard⟩,
    ⟨hYE, hEEt, hEel, hEcard, hEQ, hEQn, hEcoat⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩,
    ⟨hNX, hlev, hNM, v₁, hv₁K, hv₁eq, hv₁Q⟩, ⟨hN3M, hN2M, hPM, hPSyl, hMJ⟩⟩ :=
    A3_structure h d hp hK
  obtain ⟨⟨hZE, hZcard, hVZ, hZZt⟩, hKu, hQu⟩ := A4_u_component h d hp hK
  have hEcomm := eOne_comm h d hp hK
  have hEsq : ∀ x ∈ eOne d t K, x * x = 1 := fun x hx => by
    simpa [sq] using hEel.2 x hx
  have hQK₃ := qThree_le_kThree h d hp hK
  have hzcE : eOne d t K ⊓ centralizer ((qThree d t K : Subgroup G) : Set G) =
      zc (qThree d t K) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans hEQ) inf_le_right
    · refine le_inf ?_ (inf_le_right : zc (qThree d t K) ≤ _)
      rw [hZE]
      exact inf_le_left
  refine ⟨hp.two_le, d.card_Γ₀, hEK₃, hEQ, hQK₃, hK₃iso, hEcomm, hEsq, hEcard, ?_, ?_⟩
  · rw [hQcard, hEcard]
    ring
  · rw [hzcE, hZcard]

theorem qOne_comm (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    ∀ x ∈ qOne d t K₁, ∀ y ∈ (qOne d t K₁)ᵍ[t], x * y = y * x := by
  obtain ⟨hZ1, -, -, -⟩ := S5_upperCentralSeries_P h d hp.layer
  obtain ⟨⟨hV₁K₁', hV₁Z⟩, hE3b⟩ := E3_commutators h d hp hK₁
  set V₁ := yamadaV₁ d t with hV₁def
  set P := yamadaP d t with hPdef
  set Q₁ := qOne d t K₁ with hQ₁def
  have htP : t ∈ normalizer (P : Set G) := h.t_mem_normalizer_yamadaP d hp.layer
  have hNPV₁ : normalizer (P : Set G) ≤ normalizer (V₁ : Set G) := by
    have := normalizer_le_normalizer_series P 1
    rwa [hZ1] at this
  have htV₁ : t ∈ normalizer (V₁ : Set G) := hNPV₁ htP
  have hV₁t : V₁ᵍ[t] = V₁ := conj_eq_of_mem_normalizer htV₁
  obtain ⟨hnOne, -, hK₁', hK₁''⟩ := hE3b
  set K₁' := ⁅K₁, K₁⁆ with hK₁'def
  set K₁'' := ⁅K₁', K₁'⁆ with hK₁''def
  have hK₁'nOne : K₁' ≤ nOne d t := hnOne ▸ le_sup_left
  have hK₁'tnOne : K₁'ᵍ[t] ≤ nOne d t := hnOne ▸ le_sup_right
  have hcen : ∀ c ∈ V₁, ∀ x ∈ nOne d t, c * x = x * c := fun c hc x hx =>
    (Subgroup.mem_centralizer_iff.1 (hV₁Z hc).2 x hx).symm
  have hmain := commute_sup_of_central (A₀ := K₁'') (B₀ := K₁''ᵍ[t]) (C := V₁)
    (fun c hc x hx => hcen c hc x (hK₁'nOne (Subgroup.commutator_le_self _ hx)))
    (fun c hc x hx => hcen c hc x (hK₁'tnOne (conj_mono t (Subgroup.commutator_le_self _) hx)))
    (fun c hc c' hc' => hcen c hc c' (hK₁'nOne (hV₁K₁' hc')))
    (fun a ha b hb => (Subgroup.mem_centralizer_iff.1
      ((commutator_eq_bot_iff_le_centralizer.1 hK₁'') ha) b hb).symm)
  intro x hx y hy
  have hx' : x ∈ K₁'' ⊔ V₁ := by rw [← hK₁']; exact (inf_le_right : Q₁ ≤ K₁') hx
  have hy' : y ∈ K₁''ᵍ[t] ⊔ V₁ := by
    have : y ∈ K₁'ᵍ[t] := conj_mono t (inf_le_right : Q₁ ≤ K₁') hy
    rw [hK₁', conj_sup, hV₁t] at this
    exact this
  exact hmain x hx' y hy'

theorem card_Y₂_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 := by
  obtain ⟨-, -, ⟨hYE, hEEt, hEel, hEcard, hEQ, hEQn, hEcoat⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩, -, -⟩ :=
    A3_structure h d hp hK
  obtain ⟨⟨hZE, hZcard, hVZ, hZZt⟩, hKu, hQu⟩ := A4_u_component h d hp hK
  have hKK₃t' : ∀ x ∈ kThree d t K, ∀ y ∈ (kThree d t K)ᵍ[t], x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hKK₃c hx) y hy).symm
  have hEEt' : ∀ x ∈ eOne d t K, ∀ y ∈ (eOne d t K)ᵍ[t], x * y = y * x := fun x hx y hy =>
    hKK₃t' x (hEK₃ hx) y (conj_mono t hEK₃ hy)
  have hZE₁ : zc (qThree d t K) ≤ eOne d t K := by rw [hZE]; exact inf_le_left
  constructor
  · have h1 := card_sup_mul_card_inf_of_commute' (eOne d t K) (eOne d t K)ᵍ[t] hEEt'
    rw [hEEt, Subgroup.card_bot, mul_one, ← hYE, hEcard, card_conj, hEcard] at h1
    rw [h1]
    ring
  · have hcm : ∀ x ∈ zc (qThree d t K), ∀ y ∈ (zc (qThree d t K))ᵍ[t], x * y = y * x :=
      fun x hx y hy => hKK₃t' x (hEK₃ (hZE₁ hx)) y (conj_mono t hEK₃ (conj_mono t hZE₁ hy))
    have h1 := card_sup_mul_card_inf_of_commute' (zc (qThree d t K)) (zc (qThree d t K))ᵍ[t] hcm
    rw [hZZt, Subgroup.card_bot, mul_one, ← hVZ, hZcard, card_conj, hZcard] at h1
    rw [h1]
    ring

theorem G0_aux (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    centerMod (yamadaV₁ d t) (qOne d t K₁) = eOne d t K ⊔ yamadaV₁ d t ∧
      eOne d t K ≤ qOne d t K₁ ∧ qThree d t K ≤ qOne d t K₁ := by
  have hK : IsLayerComponent d t K := hL.comp
  have hK₁ : IsN1Factor d t K₁ := hL.factor
  obtain ⟨⟨hXY, hXSyl, hXcard⟩, ⟨hXQ, hQQt, hQQc, hQSyl, hQcard⟩,
    ⟨hYE, hEEt, hEel, hEcard, hEQ, hEQn, hEcoat⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩,
    ⟨hNX, hlev, hNM, v₁, hv₁K, hv₁eq, hv₁Q⟩, ⟨hN3M, hN2M, hPM, hPSyl, hMJ⟩⟩ :=
    A3_structure h d hp hK
  obtain ⟨⟨hZE, hZcard, hVZ, hZZt⟩, hKu, hQu⟩ := A4_u_component h d hp hK
  obtain ⟨⟨hN2K2, hK2K2t, hK2K2c, hK2iso, hK2sec⟩, hB1b⟩ := B1_decomposition h d hp hK
  obtain ⟨⟨hPQ, hQQV, hQQc', hD1, hD2, hD3⟩, hZser, hRdec, hF4⟩ := F0_sylow h d hp hK hK₁
  obtain ⟨⟨hN1norm, hN2norm⟩, hR, hlabel⟩ := F1_normalizers h d hp hK hK₁
  obtain ⟨⟨hF4a, hF4b, hF4c, hF4d⟩, hF2b⟩ := F2_auxiliary h d hp hL
  obtain ⟨⟨hV₁K₁', hV₁Z⟩, hE3b⟩ := E3_commutators h d hp hK₁
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hp.layer
  have hEcomm := eOne_comm h d hp hK
  have hQK₃ := qThree_le_kThree h d hp hK
  have H3 := natSL2_layer h d hp hK
  obtain ⟨T, hTK, hTN, hTcard, hTfpf⟩ := H3.exists_torus
  set V₁ := yamadaV₁ d t with hV₁def
  set Y₂ := yamadaY₂ d t with hY₂def
  set P := yamadaP d t with hPdef
  set E₁ := eOne d t K with hE₁def
  set Q₃ := qThree d t K with hQ₃def
  set K₃ := kThree d t K with hK₃def
  set Q₁ := qOne d t K₁ with hQ₁def
  set M₆ := yamadaM₆ d t with hM₆def
  set X := prodX d t with hXdef
  set Z := zc Q₃ with hZdef
  have htt : t * t = 1 := h.t_mul_t
  have htP : t ∈ normalizer (P : Set G) := h.t_mem_normalizer_yamadaP d hp.layer
  have hNPV₁ : normalizer (P : Set G) ≤ normalizer (V₁ : Set G) := by
    have := normalizer_le_normalizer_series P 1
    rwa [hZ1] at this
  have htV₁ : t ∈ normalizer (V₁ : Set G) := hNPV₁ htP
  have hV₁t : V₁ᵍ[t] = V₁ := conj_eq_of_mem_normalizer htV₁
  have htM₆ : t ∈ normalizer (M₆ : Set G) := hB1b.2.2 htP
  have hM₆t : M₆ᵍ[t] = M₆ := conj_eq_of_mem_normalizer htM₆
  have hKK₃t' : ∀ x ∈ K₃, ∀ y ∈ K₃ᵍ[t], x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hKK₃c hx) y hy).symm
  have hEEt' : ∀ x ∈ E₁, ∀ y ∈ E₁ᵍ[t], x * y = y * x := fun x hx y hy =>
    hKK₃t' x (hEK₃ hx) y (conj_mono t hEK₃ hy)
  have hEtab : ∀ x ∈ E₁ᵍ[t], ∀ y ∈ E₁ᵍ[t], x * y = y * x := by
    intro x hx y hy
    have hx' : t * x * t⁻¹ ∈ E₁ := mem_conj_iff.1 hx
    have hy' : t * y * t⁻¹ ∈ E₁ := mem_conj_iff.1 hy
    have := hEcomm _ hx' _ hy'
    calc x * y = t⁻¹ * ((t * x * t⁻¹) * (t * y * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * y * t⁻¹) * (t * x * t⁻¹)) * t := by rw [this]
      _ = y * x := by group
  have hEtcard : Nat.card (E₁ᵍ[t] : Subgroup G) = (2 ^ f) ^ 2 := by
    rw [card_conj, hEcard]
  have hZtcard : Nat.card (Zᵍ[t] : Subgroup G) = 2 ^ f := by
    rw [card_conj, hZcard]
  have hZE₁ : Z ≤ E₁ := by rw [hZE]; exact inf_le_left
  have hZtE : Zᵍ[t] ≤ E₁ᵍ[t] := conj_mono t hZE₁
  have hV₁P : V₁ ≤ P := by rw [← hZ1]; exact Subgroup.map_subtype_le _
  have hV₁Q₁ : V₁ ≤ Q₁ := le_inf hV₁P hV₁K₁'
  have hQ₁comm := qOne_comm h d hp hK₁
  set ZQ := centerMod V₁ Q₁ with hZQdef
  have hZQQ₁ : ZQ ≤ Q₁ := fun x hx => ((mem_centerMod_iff hV₁Q₁).1 hx).1
  have hV₁ZQ : V₁ ≤ ZQ := by
    unfold ZQ centerMod upperCenterMod
    exact NormalizerQuotient.le_lift _
  have hZQt : ZQᵍ[t] = centerMod V₁ Q₁ᵍ[t] := centerMod_conj hV₁Q₁ htV₁
  have hY₂ZQ : Y₂ = ZQ ⊔ ZQᵍ[t] := by
    rw [hZQt]
    exact hZser.1
  have hZQY : ZQ ≤ Y₂ := hY₂ZQ ▸ le_sup_left
  have hZQinf : ZQ ⊓ ZQᵍ[t] = V₁ := by
    apply le_antisymm
    · intro x hx
      have : x ∈ Q₁ ⊓ Q₁ᵍ[t] := Subgroup.mem_inf.2 ⟨hZQQ₁ hx.1, conj_mono t hZQQ₁ hx.2⟩
      rwa [hQQV] at this
    · exact le_inf hV₁ZQ (hV₁t ▸ conj_mono t hV₁ZQ)
  have hcardY₂ : Nat.card Y₂ = (2 ^ f) ^ 4 := by
    have h1 := card_sup_mul_card_inf_of_commute' E₁ E₁ᵍ[t] hEEt'
    rw [hEEt, Subgroup.card_bot, mul_one, ← hYE, hEcard, hEtcard] at h1
    rw [h1]
    ring
  have hcardV₁ : Nat.card V₁ = (2 ^ f) ^ 2 := by
    have hcm : ∀ x ∈ Z, ∀ y ∈ Zᵍ[t], x * y = y * x := fun x hx y hy =>
      hKK₃t' x (hEK₃ (hZE₁ hx)) y (conj_mono t hEK₃ (hZtE hy))
    have h1 := card_sup_mul_card_inf_of_commute' Z Zᵍ[t] hcm
    rw [hZZt, Subgroup.card_bot, mul_one, ← hVZ, hZcard, hZtcard] at h1
    rw [h1]
    ring
  have hcardZQ : Nat.card ZQ = (2 ^ f) ^ 3 := by
    have h1 := card_sup_mul_card_inf_of_commute' ZQ ZQᵍ[t]
      (fun x hx y hy => hQ₁comm x (hZQQ₁ hx) y (conj_mono t hZQQ₁ hy))
    rw [← hY₂ZQ, hZQinf, hcardY₂, hcardV₁, card_conj] at h1
    have h2 : Nat.card ZQ * Nat.card ZQ = (2 ^ f) ^ 3 * (2 ^ f) ^ 3 := by
      rw [← h1]
      ring
    exact Nat.mul_self_inj.1 h2
  have hQ₃K : Q₃ ≤ K := inf_le_right
  have hK₃nThree : K₃ ≤ nThree d t := hNK ▸ le_sup_left
  have hK₃tnThree : K₃ᵍ[t] ≤ nThree d t := hNK ▸ le_sup_right
  have hnThreeTwo : nThree d t ≤ nTwo d t := le_sup_left
  have hK₃NQt : K₃ ≤ normalizer ((Q₃ᵍ[t] : Subgroup G) : Set G) :=
    le_normalizer_of_commute' fun x hx y hy => hKK₃t' x hx y (conj_mono t hQK₃ hy)
  have hQ₁N : ∀ g ∈ nTwo d t, g ∈ normalizer (P : Set G) → g ∈ normalizer (Q₁ : Set G) := by
    intro g hg1 hg2
    have := hN2norm (Subgroup.mem_inf.2 ⟨hg1, hg2⟩)
    exact mem_normalizer_inf hg2 (Subgroup.mem_inf.1 this).2
  have hZQN : ∀ g ∈ nTwo d t, g ∈ normalizer (P : Set G) → g ∈ normalizer (ZQ : Set G) :=
    fun g hg1 hg2 => mem_normalizer_centerMod hV₁Q₁ (hNPV₁ hg2) (hQ₁N g hg1 hg2)
  have hTP : ∀ τ ∈ T, τ ∈ normalizer (P : Set G) := by
    intro τ hτ
    have hτK₃ : τ ∈ K₃ := hTK hτ
    have hτX : τ ∈ normalizer ((X : Subgroup G) : Set G) := by
      rw [hXQ]
      exact mem_normalizer_sup (hTN hτ) (hK₃NQt hτK₃)
    have hτM : τ ∈ normalizer (M₆ : Set G) := hNM (hK₃nThree hτK₃)
    rw [hPM]
    exact mem_normalizer_sup hτM hτX
  have hTnTwo : ∀ τ ∈ T, τ ∈ nTwo d t := fun τ hτ => hnThreeTwo (hK₃nThree (hTK hτ))
  have hT'P : ∀ τ ∈ Tᵍ[t], τ ∈ normalizer (P : Set G) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := mem_conj_iff' hτ
    rw [h2]
    exact mul_mem (mul_mem (inv_mem htP) (hTP _ h1)) htP
  have hT'nTwo : ∀ τ ∈ Tᵍ[t], τ ∈ nTwo d t := fun τ hτ =>
    hnThreeTwo (hK₃tnThree (conj_mono t hTK hτ))
  have hT'N_E : ∀ τ ∈ Tᵍ[t], τ ∈ normalizer ((E₁ᵍ[t] : Subgroup G) : Set G) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := mem_conj_iff' hτ
    rw [h2]
    exact conj_mem_normalizer_conj t (H3.K_le_normalizer (hTK h1))
  have hT'N_Z : ∀ τ ∈ Tᵍ[t], τ ∈ normalizer ((Zᵍ[t] : Subgroup G) : Set G) := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := mem_conj_iff' hτ
    rw [h2]
    exact conj_mem_normalizer_conj t (normalizer_le_normalizer_zc Q₃ (hTN h1))
  have hT'fpf : ∀ τ ∈ Tᵍ[t], ∀ e ∈ E₁ᵍ[t], τ * e * τ⁻¹ = e → τ = 1 ∨ e = 1 := by
    intro τ hτ e he hfix
    obtain ⟨hτT, hτeq⟩ := mem_conj_iff' hτ
    obtain ⟨heE, heeq⟩ := mem_conj_iff' he
    have key := hTfpf (t * τ * t⁻¹) hτT (t * e * t⁻¹) heE (by
      have e1 : t * τ * t⁻¹ * (t * e * t⁻¹) * (t * τ * t⁻¹)⁻¹ = t * (τ * e * τ⁻¹) * t⁻¹ := by
        group
      rw [e1, hfix])
    rcases key with h1 | h1
    · left
      calc τ = t⁻¹ * (t * τ * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    · right
      calc e = t⁻¹ * (t * e * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
  have hZQ_IS := independent_scalars (E := E₁) (E' := E₁ᵍ[t]) (Z := Z) (Z' := Zᵍ[t])
    (ZQ := ZQ) (T := T) (T' := Tᵍ[t]) (n := f) hp.two_le hEEt hEEt' hEcomm hEtab hZE₁ hZtE
    hEcard hEtcard hZcard hZtcard (by rw [← hYE]; exact hZQY) (by rw [← hVZ]; exact hV₁ZQ) hcardZQ
    (fun τ hτ => Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨H3.K_le_normalizer (hTK hτ),
      normalizer_le_normalizer_zc Q₃ (hTN hτ)⟩, hZQN τ (hTnTwo τ hτ) (hTP τ hτ)⟩)
    (fun τ hτ e he => hKK₃t' τ (hTK hτ) e (conj_mono t hEK₃ he)) hTcard hTfpf
    (fun τ hτ => Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hT'N_E τ hτ, hT'N_Z τ hτ⟩,
      hZQN τ (hT'nTwo τ hτ) (hT'P τ hτ)⟩)
    (fun τ hτ e he => (hKK₃t' e (hEK₃ he) τ (conj_mono t hTK hτ)).symm)
    (by rw [card_conj, hTcard]) hT'fpf
  have hY₂X : Y₂ ≤ X := by
    rw [hYE, hXQ]
    exact sup_le (hEQ.trans le_sup_left) (conj_mono t hEQ |>.trans le_sup_right)
  have hXP : X ≤ P := by rw [hPM]; exact le_sup_right
  have hQ₃P : Q₃ ≤ P := by rw [hXQ] at hXP; exact le_sup_left.trans hXP
  have hZQeq : ZQ = E₁ ⊔ V₁ := by
    rcases hZQ_IS with h1 | h1
    · rw [h1]
      apply le_antisymm
      · exact sup_le le_sup_left (le_sup_of_le_right (hVZ ▸ le_sup_right))
      · refine sup_le le_sup_left ?_
        rw [hVZ]
        exact sup_le (hZE₁.trans le_sup_left) le_sup_right
    · exfalso
      have hEtQ₁ : E₁ᵍ[t] ≤ Q₁ := by
        have : E₁ᵍ[t] ≤ ZQ := by rw [h1]; exact le_sup_left
        exact this.trans hZQQ₁
      have hEtY : E₁ᵍ[t] ≤ Y₂ := by rw [hYE]; exact le_sup_right
      have hEtP : E₁ᵍ[t] ≤ P := hEtY.trans (hY₂X.trans hXP)
      have hQ₃B : Q₃ ≤ Q₁ ⊔ M₆ := by
        rw [hF2b.1]
        exact le_inf hQ₃P (hQK₃.trans le_sup_left)
      have hM₆C : M₆ ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyY : y ∈ Y₂ := by rw [hYE]; exact Subgroup.mem_sup_right hy
        have hx' : x ∈ P ⊓ centralizer (Y₂ : Set G) := hB1b.1.symm ▸ hx
        exact Subgroup.mem_centralizer_iff.1 hx'.2 y hyY
      have hQ₃C : Q₃ ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hKK₃t' x (hQK₃ hx) y (conj_mono t hEK₃ hy)).symm
      have hQtC : Q₁ᵍ[t] ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hQ₁comm y (hEtQ₁ hy) x hx
      have hQ₃tC : Q₃ᵍ[t] ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := by
        have h2 : Q₃ᵍ[t] ≤ Q₁ᵍ[t] ⊔ M₆ := by
          have := conj_mono t hQ₃B
          rwa [conj_sup, hM₆t] at this
        exact h2.trans (sup_le hQtC hM₆C)
      have hPC : P ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := by
        rw [hPM, hXQ]
        exact sup_le hM₆C (sup_le hQ₃C hQ₃tC)
      have hEtV₁ : E₁ᵍ[t] ≤ V₁ := by
        intro x hx
        rw [← hZ1]
        refine ⟨⟨x, hEtP hx⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.1 (hPC g.2) x hx).symm
      have hEtV : E₁ᵍ[t] = V₁ :=
        Subgroup.eq_of_le_of_card_ge hEtV₁ (by rw [hcardV₁, hEtcard])
      have hZbot : Z ≤ ⊥ := by
        rw [← hEEt]
        refine le_inf hZE₁ ?_
        rw [hEtV, hVZ]
        exact le_sup_left
      have : Nat.card Z = 1 := Subgroup.card_eq_one.2 (le_bot_iff.1 hZbot)
      rw [hZcard] at this
      have h2 : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by have := hp.two_le; omega)
      omega
  have hE₁Q₁ : E₁ ≤ Q₁ := (le_sup_left.trans hZQeq.symm.le).trans hZQQ₁
  refine ⟨hZQeq, hE₁Q₁, ?_⟩
  have huN₁ : uG d ∈ normalizer (K₁ : Set G) := nOne_le_normalizer hK₁ (u_mem_nOne h d hp)
  have hK₁u : K₁ᵍ[uG d] = K₁ := conj_eq_of_mem_normalizer huN₁
  have hK₁'u : ⁅K₁, K₁⁆ᵍ[uG d] = ⁅K₁, K₁⁆ := by rw [conj_commutator, hK₁u]
  have hEu : E₁ᵍ[uG d] ≤ ⁅K₁, K₁⁆ :=
    (conj_mono (uG d) (hE₁Q₁.trans (inf_le_right : Q₁ ≤ ⁅K₁, K₁⁆))).trans hK₁'u.le
  have hEuP : E₁ᵍ[uG d] ≤ P := by
    have : E₁ᵍ[uG d] ≤ Q₃ := by rw [hQu]; exact le_sup_right
    exact this.trans hQ₃P
  rw [hQu]
  exact sup_le hE₁Q₁ (le_inf hEuP hEu)

end G0

end Y8_G0

section Y8_GA

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement Pointwise

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem conj_inf_conj_self {τ : Γ} (hτ : τ * τ = 1) (A : Subgroup Γ) :
    (A ⊓ Aᵍ[τ])ᵍ[τ] = A ⊓ Aᵍ[τ] := by
  rw [conj_inf, conj_conj_of_mul_self hτ, inf_comm]

theorem commute_of_mem_conj {τ : Γ} (hτ : τ * τ = 1) {A W : Subgroup Γ}
    (hA1 : A ⊓ Aᵍ[τ] = W) (hWc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) :
    ∀ b ∈ Aᵍ[τ], ∀ w ∈ W, b * w = w * b := by
  intro b hb w hw
  have hWt : Wᵍ[τ] = W := by rw [← hA1]; exact conj_inf_conj_self hτ A
  have hw' : τ * w * τ⁻¹ ∈ W := by
    have : w ∈ Wᵍ[τ] := by rw [hWt]; exact hw
    exact mem_conj_iff.1 this
  have hb' : τ * b * τ⁻¹ ∈ A := mem_conj_iff.1 hb
  have h := hWc _ hb' _ hw'
  calc b * w = τ⁻¹ * ((τ * b * τ⁻¹) * (τ * w * τ⁻¹)) * τ := by group
    _ = τ⁻¹ * ((τ * w * τ⁻¹) * (τ * b * τ⁻¹)) * τ := by rw [h]
    _ = w * b := by group

theorem commute_conj_of_central {τ : Γ} (hτ : τ * τ = 1) {A W : Subgroup Γ}
    (hA1 : A ⊓ Aᵍ[τ] = W) (hA2 : ⁅A, Aᵍ[τ]⁆ ≤ W) (hWc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hA4 : A ≤ ⁅A, A⁆ ⊔ W) : ∀ a ∈ A, ∀ b ∈ Aᵍ[τ], a * b = b * a := by
  have hWcent : W ≤ centralizer (A : Set Γ) := fun w hw =>
    mem_centralizer_iff.2 fun a ha => hWc a ha w hw
  have h1 : ⁅⁅A, Aᵍ[τ]⁆, A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.2 (hA2.trans hWcent)
  have h2 : ⁅⁅Aᵍ[τ], A⁆, A⁆ = ⊥ := by
    rw [commutator_comm Aᵍ[τ] A]
    exact h1
  have h3 : ⁅⁅A, A⁆, Aᵍ[τ]⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have h3' : ⁅A, A⁆ ≤ centralizer ((Aᵍ[τ] : Subgroup Γ) : Set Γ) :=
    commutator_eq_bot_iff_le_centralizer.1 h3
  have hWb := commute_of_mem_conj hτ hA1 hWc
  intro a ha b hb
  have hc : ∀ c ∈ W, ∀ x ∈ ⁅A, A⁆, c * x = x * c := fun c hc x hx =>
    (hWc x (Subgroup.commutator_le_self A hx) c hc).symm
  obtain ⟨a₁, ha₁, w, hw, rfl⟩ := mem_sup_of_commute' hc (hA4 ha)
  have e1 : b * a₁ = a₁ * b := mem_centralizer_iff.1 (h3' ha₁) b hb
  calc a₁ * w * b = a₁ * (w * b) := by group
    _ = a₁ * (b * w) := by rw [hWb b hb w hw]
    _ = (a₁ * b) * w := by group
    _ = (b * a₁) * w := by rw [e1]
    _ = b * (a₁ * w) := by group


theorem commutator_mul_central {a b w₁ w₂ : Γ} (h2 : Commute w₁ b) (h3 : Commute w₂ a)
    (h5 : Commute w₁ w₂) : ⁅a * w₁, b * w₂⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  rw [h2.left_comm, h5.left_comm, mul_inv_cancel_left, h3.inv_right.left_comm, mul_inv_cancel_left]

theorem commutator_mul_mul_of_commute {d₁ d₂ e₁ e₂ : Γ} (h11 : Commute e₁ d₁)
    (h12 : Commute e₂ d₁) (h21 : Commute e₁ d₂) (h22 : Commute e₂ d₂) :
    ⁅d₁ * e₁, d₂ * e₂⁆ = ⁅d₁, d₂⁆ * ⁅e₁, e₂⁆ := by
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  rw [h21.left_comm, h11.inv_left.inv_right.left_comm, h12.inv_right.left_comm,
    h11.inv_right.left_comm, h22.inv_inv.eq, h21.inv_inv.left_comm, h22.inv_right.left_comm,
    h21.inv_right.left_comm]


theorem commutator_sup_sup_central {D E W : Subgroup Γ}
    (hDE : ∀ e ∈ E, ∀ d ∈ D, e * d = d * e)
    (hWc : ∀ w ∈ W, ∀ x ∈ D ⊔ E ⊔ W, w * x = x * w) :
    ⁅D ⊔ E ⊔ W, D ⊔ E ⊔ W⁆ ≤ ⁅D, D⁆ ⊔ ⁅E, E⁆ := by
  rw [commutator_le]
  intro x hx y hy
  have hWc' : ∀ c ∈ W, ∀ a ∈ D ⊔ E, c * a = a * c := fun c hc a ha =>
    hWc c hc a (Subgroup.mem_sup_left ha)
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_sup_of_commute' hWc' hx
  obtain ⟨v, hv, w', hw', rfl⟩ := mem_sup_of_commute' hWc' hy
  obtain ⟨d, hd, e, he, rfl⟩ := mem_sup_of_commute' hDE hu
  obtain ⟨d', hd', e', he', rfl⟩ := mem_sup_of_commute' hDE hv
  have hwx : ∀ z ∈ D ⊔ E ⊔ W, Commute w z := fun z hz => (hWc w hw z hz)
  have hw'x : ∀ z ∈ D ⊔ E ⊔ W, Commute w' z := fun z hz => (hWc w' hw' z hz)
  have hdeM : d * e ∈ D ⊔ E ⊔ W :=
    Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right he))
  have hdeM' : d' * e' ∈ D ⊔ E ⊔ W :=
    Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left hd') (Subgroup.mem_sup_right he'))
  rw [commutator_mul_central (hwx _ hdeM') (hw'x _ hdeM) (hwx w' (Subgroup.mem_sup_right hw')),
    commutator_mul_mul_of_commute (hDE e he d hd) (hDE e' he' d hd) (hDE e he d' hd')
      (hDE e' he' d' hd')]
  exact mul_mem (mem_sup_left (commutator_mem_commutator hd hd'))
    (mem_sup_right (commutator_mem_commutator he he'))


theorem split_central {τ : Γ} (hτ : τ * τ = 1) {A W O M Q D F : Subgroup Γ}
    (hA1 : A ⊓ Aᵍ[τ] = W) (hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[τ], a * b = b * a)
    (hWc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) (hA4 : A ≤ ⁅A, A⁆ ⊔ W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hW2 : IsPGroup 2 W)
    (hOA : O ≤ A) (hM : M = O ⊔ Oᵍ[τ]) (hM' : ⁅M, M⁆ = W)
    (hQ1 : Q ⊓ Qᵍ[τ] = ⊥) (hDQ : D ≤ Q) (hDM : D ≤ M) (hOD : O = D ⊔ W) (hF : F = ⁅D, D⁆)
    (hSyl : ∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = Q ⊔ W) :
    F ≤ Q ∧ F ≤ ⁅A, A⁆ ∧ Fᵍ[τ] ≤ W ∧ W = F ⊔ Fᵍ[τ] ∧ F ⊓ Fᵍ[τ] = ⊥ ∧
      ⁅A, A⁆ ⊓ Fᵍ[τ] = ⊥ ∧ A = ⁅A, A⁆ ⊔ Fᵍ[τ] := by
  have hWt : Wᵍ[τ] = W := by rw [← hA1]; exact conj_inf_conj_self hτ A
  have hWb := commute_of_mem_conj hτ hA1 hWc
  have hWA : W ≤ A := hA1 ▸ inf_le_left
  have hDO : D ≤ O := by rw [hOD]; exact le_sup_left
  have hWO : W ≤ O := by rw [hOD]; exact le_sup_right
  have hOM : O ≤ M := by rw [hM]; exact le_sup_left
  have hOtM : Oᵍ[τ] ≤ M := by rw [hM]; exact le_sup_right
  have hFD : F ≤ D := by rw [hF]; exact Subgroup.commutator_le_self _
  have hFQ : F ≤ Q := hFD.trans hDQ
  have hFB : F ≤ ⁅A, A⁆ := by
    rw [hF]; exact commutator_mono (hDO.trans hOA) (hDO.trans hOA)
  have hFW : F ≤ W := by rw [← hM', hF]; exact commutator_mono hDM hDM
  have hFtW : Fᵍ[τ] ≤ W := by
    have := conj_mono τ hFW
    rwa [hWt] at this
  have hFFt : F ⊓ Fᵍ[τ] = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf hFQ (conj_mono τ hFQ)) hQ1.le)
  have hOt : Oᵍ[τ] = Dᵍ[τ] ⊔ W := by rw [hOD, conj_sup, hWt]
  have hDtM : Dᵍ[τ] ≤ M := (conj_mono τ hDO).trans hOtM
  have hMeq : M = D ⊔ Dᵍ[τ] ⊔ W := by
    apply le_antisymm
    · calc M = O ⊔ Oᵍ[τ] := hM
        _ ≤ D ⊔ Dᵍ[τ] ⊔ W := by
          refine sup_le ?_ ?_
          · rw [hOD]; exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right
          · rw [hOt]; exact sup_le (le_trans le_sup_right le_sup_left) le_sup_right
    · exact sup_le (sup_le hDM hDtM) (hWO.trans hOM)
  have hMcent : M ≤ centralizer (W : Set Γ) := by
    rw [hM]
    refine sup_le (fun o ho => mem_centralizer_iff.2 fun w hw => ?_)
      (fun o ho => mem_centralizer_iff.2 fun w hw => ?_)
    · exact (hWc o (hOA ho) w hw).symm
    · exact (hWb o (conj_mono τ hOA ho) w hw).symm
  have hWcM : ∀ w ∈ W, ∀ x ∈ D ⊔ Dᵍ[τ] ⊔ W, w * x = x * w := by
    intro w hw x hx
    rw [← hMeq] at hx
    exact mem_centralizer_iff.1 (hMcent hx) w hw
  have hED : ∀ e ∈ Dᵍ[τ], ∀ d ∈ D, e * d = d * e := fun e he d hd =>
    (hcomm d (hDO.trans hOA hd) e (conj_mono τ (hDO.trans hOA) he)).symm
  have hWle : W ≤ F ⊔ Fᵍ[τ] := by
    calc W = ⁅M, M⁆ := hM'.symm
      _ = ⁅D ⊔ Dᵍ[τ] ⊔ W, D ⊔ Dᵍ[τ] ⊔ W⁆ := by rw [← hMeq]
      _ ≤ ⁅D, D⁆ ⊔ ⁅Dᵍ[τ], Dᵍ[τ]⁆ := commutator_sup_sup_central hED hWcM
      _ = F ⊔ Fᵍ[τ] := by rw [hF, conj_commutator]
  have hWeq : W = F ⊔ Fᵍ[τ] := le_antisymm hWle (sup_le hFW hFtW)
  have hFtA : Fᵍ[τ] ≤ A := hFtW.trans hWA
  have hFtn : A ≤ normalizer ((Fᵍ[τ] : Subgroup Γ) : Set Γ) :=
    le_normalizer_of_commute' fun x hx y hy => hWc x hx y (hFtW hy)
  have hFtab : ∀ x ∈ Fᵍ[τ], ∀ y ∈ Fᵍ[τ], x * y = y * x := fun x hx y hy =>
    hWab x (hFtW hx) y (hFtW hy)
  have hFt2 : IsPGroup 2 (Fᵍ[τ] : Subgroup Γ) := hW2.to_le hFtW
  have hCsup : Q ⊔ Fᵍ[τ] = Q ⊔ W := by
    apply le_antisymm
    · exact sup_le le_sup_left (hFtW.trans le_sup_right)
    · exact sup_le le_sup_left (hWeq ▸ sup_le (hFQ.trans le_sup_left) le_sup_right)
  have hCX : Q ⊓ Fᵍ[τ] = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_left Q (conj_mono τ hFQ)) hQ1.le)
  obtain ⟨Y, hYA, hYX, hYsup⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_complement_of_sylow
    hFtA hFtn hFtab hFt2 hSyl (le_sup_left : Q ≤ Q ⊔ W) hCX hCsup
  have hBY : ⁅A, A⁆ ≤ Y := by
    rw [commutator_le]
    intro a ha b hb
    have hc : ∀ c ∈ Fᵍ[τ], ∀ y ∈ Y, c * y = y * c := fun c hc y hy =>
      (hWc y (hYA hy) c (hFtW hc)).symm
    rw [← hYsup] at ha hb
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_commute' hc ha
    obtain ⟨y', hy', z', hz', rfl⟩ := mem_sup_of_commute' hc hb
    rw [commutator_mul_central (hc z hz y' hy') (hc z' hz' y hy)
      (hFtab z hz z' hz')]
    exact Subgroup.commutator_le_self Y (commutator_mem_commutator hy hy')
  have hBFt : ⁅A, A⁆ ⊓ Fᵍ[τ] = ⊥ := eq_bot_iff.2 (le_trans (inf_le_inf hBY le_rfl) hYX.le)
  have hAeq : A = ⁅A, A⁆ ⊔ Fᵍ[τ] := by
    apply le_antisymm
    · calc A ≤ ⁅A, A⁆ ⊔ W := hA4
        _ = ⁅A, A⁆ ⊔ (F ⊔ Fᵍ[τ]) := by rw [← hWeq]
        _ ≤ ⁅A, A⁆ ⊔ Fᵍ[τ] := sup_le le_sup_left (sup_le (hFB.trans le_sup_left) le_sup_right)
    · exact sup_le (Subgroup.commutator_le_self A) hFtA
  exact ⟨hFQ, hFB, hFtW, hWeq, hFFt, hBFt, hAeq⟩

theorem mem_normalizer_of_conj_eq {X : Subgroup Γ} {g : Γ} (h : Xᵍ[g] = X) :
    g ∈ normalizer (X : Set Γ) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conj_iff, h]

theorem mem_normalizer_commutator_self {A : Subgroup Γ} {g : Γ} (hg : g ∈ normalizer (A : Set Γ)) :
    g ∈ normalizer ((⁅A, A⁆ : Subgroup Γ) : Set Γ) :=
  mem_normalizer_of_conj_eq (by rw [conj_commutator, conj_eq_of_mem_normalizer hg])

theorem derived_conj_disjoint {τ : Γ} (hτ : τ * τ = 1) {A W F : Subgroup Γ}
    (hA1 : A ⊓ Aᵍ[τ] = W) (hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[τ], a * b = b * a)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hFB : F ≤ ⁅A, A⁆) (hFtW : Fᵍ[τ] ≤ W)
    (hFW : F ≤ W) (hWeq : W = F ⊔ Fᵍ[τ]) (hFFt : F ⊓ Fᵍ[τ] = ⊥) (hBFt : ⁅A, A⁆ ⊓ Fᵍ[τ] = ⊥)
    (hAeq : A = ⁅A, A⁆ ⊔ Fᵍ[τ]) :
    ⁅A, A⁆ ⊓ W = F ∧ ⁅A, A⁆ ⊓ ⁅A, A⁆ᵍ[τ] = ⊥ ∧
      (∀ x ∈ ⁅A, A⁆, ∀ y ∈ ⁅A, A⁆ᵍ[τ], x * y = y * x) ∧ A ⊔ Aᵍ[τ] = ⁅A, A⁆ ⊔ ⁅A, A⁆ᵍ[τ] := by
  have hWt : Wᵍ[τ] = W := by rw [← hA1]; exact conj_inf_conj_self hτ A
  have hBA : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self A
  have h1 : ⁅A, A⁆ ⊓ W = F := by
    apply le_antisymm
    · intro w hw
      have hw' : w ∈ F ⊔ Fᵍ[τ] := hWeq ▸ hw.2
      obtain ⟨f, hf, z, hz, rfl⟩ := mem_sup_of_commute'
        (fun c hc a ha => hWab c (hFtW hc) a (hFW ha)) hw'
      have hz' : z ∈ ⁅A, A⁆ ⊓ Fᵍ[τ] := by
        refine ⟨?_, hz⟩
        have := mul_mem (inv_mem (hFB hf)) hw.1
        simpa using this
      rw [hBFt, mem_bot] at hz'
      rw [hz', mul_one]
      exact hf
    · exact le_inf hFB hFW
  have h1' : ⁅A, A⁆ᵍ[τ] ⊓ W = Fᵍ[τ] := by
    have := congrArg (fun X => Xᵍ[τ]) h1
    simp only [conj_inf, hWt] at this
    exact this
  have h2 : ⁅A, A⁆ ⊓ ⁅A, A⁆ᵍ[τ] = ⊥ := by
    have hle : ⁅A, A⁆ ⊓ ⁅A, A⁆ᵍ[τ] ≤ W := by
      rw [← hA1]; exact inf_le_inf hBA (conj_mono τ hBA)
    rw [eq_bot_iff, ← hFFt]
    refine le_inf ?_ ?_
    · rw [← h1]; exact le_inf inf_le_left hle
    · rw [← h1']; exact le_inf inf_le_right hle
  refine ⟨h1, h2, fun x hx y hy => hcomm x (hBA hx) y (conj_mono τ hBA hy), ?_⟩
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact hAeq.le.trans (sup_le le_sup_left (le_trans (conj_mono τ hFB) le_sup_right))
    · have : Aᵍ[τ] ≤ ⁅A, A⁆ᵍ[τ] ⊔ F := by
        have := conj_mono τ hAeq.le
        rwa [conj_sup, conj_conj_of_mul_self hτ] at this
      exact this.trans (sup_le le_sup_right (hFB.trans le_sup_left))
  · exact sup_le_sup hBA (conj_mono τ hBA)

theorem le_of_coprime_complement {A B Z W D : Subgroup Γ} {j : Γ}
    (hAeq : A = B ⊔ Z) (hBA : B ≤ A) (hBnorm : A ≤ normalizer (B : Set Γ))
    (hZW : Z ≤ W) (hWc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hDA : D ≤ A) (hD2 : IsPGroup 2 D) (hjodd : Odd (orderOf j))
    (hjB : j ∈ normalizer (B : Set Γ)) (hjD : j ∈ normalizer (D : Set Γ))
    (hjW : ∀ w ∈ W, j * w = w * j)
    (hfix : ∀ x ∈ D, x * j * x⁻¹ * j⁻¹ = 1 → x ∈ B) : D ≤ B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := zpowers j with hS
  have hSB : S ≤ normalizer (B : Set Γ) := (zpowers_le).2 hjB
  have hSD : S ≤ normalizer (D : Set Γ) := (zpowers_le).2 hjD
  have hDBn : D ≤ normalizer ((D ⊓ B : Subgroup Γ) : Set Γ) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (hBnorm (hDA hx))
  have hSDB : S ≤ normalizer ((D ⊓ B : Subgroup Γ) : Set Γ) := fun s hs =>
    mem_normalizer_inf (hSD hs) (hSB hs)
  have hsolv : Group.IsSolvable D := by
    haveI := hD2.isNilpotent
    infer_instance
  have hcop : (Nat.card S).Coprime (Nat.card D) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hD2
    rw [hk, hS, Nat.card_zpowers]
    exact (Nat.coprime_two_right.2 hjodd).pow_right k
  have hSW : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s := by
    intro s hs w hw
    have : S ≤ centralizer ({w} : Set Γ) :=
      (zpowers_le).2 (mem_centralizer_singleton_iff.2 (hjW w hw))
    exact mem_centralizer_singleton_iff.1 (this hs)
  intro d hd
  have hdA : d ∈ B ⊔ Z := hAeq ▸ hDA hd
  have hc : ∀ c ∈ Z, ∀ a ∈ B, c * a = a * c := fun c hc a ha =>
    (hWc a (hBA ha) c (hZW hc)).symm
  obtain ⟨b, hb, z, hz, rfl⟩ := mem_sup_of_commute' hc hdA
  have hfix' : ∀ s ∈ S, (b * z)⁻¹ * (s * (b * z) * s⁻¹) ∈ D ⊓ B := by
    intro s hs
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.inv_mem hd) ((mem_normalizer_iff.1 (hSD hs) _).1 hd)
    · have hsb : s * b * s⁻¹ ∈ B := (mem_normalizer_iff.1 (hSB hs) b).1 hb
      have hX : b⁻¹ * (s * b * s⁻¹) ∈ B := B.mul_mem (B.inv_mem hb) hsb
      have hzs : s * z = z * s := hSW s hs z (hZW hz)
      have hzX : z * (b⁻¹ * (s * b * s⁻¹)) = (b⁻¹ * (s * b * s⁻¹)) * z :=
        hWc _ (hBA hX) z (hZW hz) |>.symm
      have e : (b * z)⁻¹ * (s * (b * z) * s⁻¹) = z⁻¹ * (b⁻¹ * (s * b * s⁻¹)) * z := by
        have : s * (b * z) * s⁻¹ = (s * b * s⁻¹) * (s * z * s⁻¹) := by group
        rw [this, hzs]
        group
      rw [e]
      have : z⁻¹ * (b⁻¹ * (s * b * s⁻¹)) * z = b⁻¹ * (s * b * s⁻¹) := by
        calc z⁻¹ * (b⁻¹ * (s * b * s⁻¹)) * z
            = z⁻¹ * (z * (b⁻¹ * (s * b * s⁻¹))) := by rw [hzX, mul_assoc]
          _ = b⁻¹ * (s * b * s⁻¹) := by group
      rw [this]
      exact hX
  obtain ⟨c, hcmem, n, hn, hdcn⟩ := exists_mem_inf_centralizer_mul_of_coprime (M := D)
    (N := D ⊓ B) (S := S) inf_le_left hDBn hSD hSDB hsolv hcop hd hfix'
  have hcD : c ∈ D := hcmem.1
  have hjc : j * c = c * j := mem_centralizer_iff.1 hcmem.2 j (mem_zpowers j)
  have hc1 : c * j * c⁻¹ * j⁻¹ = 1 := by
    rw [← hjc]; group
  rw [hdcn]
  exact mul_mem (hfix c hcD hc1) hn.2

theorem structure_main {τ : Γ} (hτ : τ * τ = 1) {A W O M Q D K3 : Subgroup Γ} {j : Γ}
    (hA1 : A ⊓ Aᵍ[τ] = W) (hA2 : ⁅A, Aᵍ[τ]⁆ ≤ W)
    (hWc : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a) (hA4 : A ≤ ⁅A, A⁆ ⊔ W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hW2 : IsPGroup 2 W)
    (hO : O = pCoreOf 2 A) (hM : M = O ⊔ Oᵍ[τ]) (hM' : ⁅M, M⁆ = W)
    (hQ1 : Q ⊓ Qᵍ[τ] = ⊥) (hDQ : D ≤ Q) (hDM : D ≤ M) (hOD : O = D ⊔ W)
    (hSyl : ∃ P : Sylow 2 A, (P : Subgroup A).map A.subtype = Q ⊔ W)
    (hjodd : Odd (orderOf j)) (hjA : j ∈ normalizer (A : Set Γ))
    (hjD : j ∈ normalizer (D : Set Γ)) (hjW : ∀ w ∈ W, j * w = w * j)
    (hDfix : ∀ x ∈ D, x * j * x⁻¹ * j⁻¹ = 1 → x ∈ W)
    (hK3 : K3 ≤ ⁅A, A⁆) (hAK3 : A = K3 ⊔ O) :
    (∀ a ∈ A, ∀ b ∈ Aᵍ[τ], a * b = b * a) ∧ ⁅A, A⁆ ⊓ ⁅A, A⁆ᵍ[τ] = ⊥ ∧
      (∀ x ∈ ⁅A, A⁆, ∀ y ∈ ⁅A, A⁆ᵍ[τ], x * y = y * x) ∧ A ⊔ Aᵍ[τ] = ⁅A, A⁆ ⊔ ⁅A, A⁆ᵍ[τ] ∧
      pCoreOf 2 ⁅A, A⁆ = D ∧ ⁅A, A⁆ = K3 ⊔ pCoreOf 2 ⁅A, A⁆ ∧
      M = pCoreOf 2 ⁅A, A⁆ ⊔ (pCoreOf 2 ⁅A, A⁆)ᵍ[τ] := by
  have hcomm := commute_conj_of_central hτ hA1 hA2 hWc hA4
  have hO2 : IsPGroup 2 O := by rw [hO]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A
  have hOA : O ≤ A := by rw [hO]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 A
  obtain ⟨hFQ, hFB, hFtW, hWeq, hFFt, hBFt, hAeq⟩ :=
    split_central hτ hA1 hcomm hWc hA4 hWab hW2 hOA hM hM' hQ1 hDQ hDM hOD (F := ⁅D, D⁆) rfl hSyl
  set F := ⁅D, D⁆ with hF
  have hWA : W ≤ A := by rw [← hA1]; exact inf_le_left
  have hDO : D ≤ O := by rw [hOD]; exact le_sup_left
  have hFD : F ≤ D := Subgroup.commutator_le_self D
  have hFW : F ≤ W := by rw [← hM']; exact commutator_mono hDM hDM
  have hDA : D ≤ A := hDO.trans hOA
  obtain ⟨hBW, hBBt, hBBc, hAAt⟩ :=
    derived_conj_disjoint hτ hA1 hcomm hWab hFB hFtW hFW hWeq hFFt hBFt hAeq
  have hBA : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self A
  have hBnorm : A ≤ normalizer ((⁅A, A⁆ : Subgroup Γ) : Set Γ) := fun a ha =>
    mem_normalizer_commutator_self (Subgroup.le_normalizer ha)
  have hQW : Q ⊓ W ≤ F := by
    intro x hx
    have hxW : x ∈ F ⊔ Fᵍ[τ] := by rw [← hWeq]; exact hx.2
    obtain ⟨f, hf, z, hz, rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => hWab c (hFtW hc) a (hFW ha)) hxW
    have hzQ : z ∈ Q ⊓ Fᵍ[τ] := by
      refine ⟨?_, hz⟩
      have := Q.mul_mem (Q.inv_mem (hFQ hf)) hx.1
      simpa using this
    have hQt : Q ⊓ Fᵍ[τ] = ⊥ :=
      eq_bot_iff.2 (le_trans (inf_le_inf_left Q (conj_mono τ hFQ)) hQ1.le)
    rw [hQt, mem_bot] at hzQ
    rw [hzQ, mul_one]
    exact hf
  have hfix : ∀ x ∈ D, x * j * x⁻¹ * j⁻¹ = 1 → x ∈ ⁅A, A⁆ := fun x hx h1 =>
    hFB (hQW ⟨hDQ hx, hDfix x hx h1⟩)
  have hDB : D ≤ ⁅A, A⁆ :=
    le_of_coprime_complement hAeq hBA hBnorm hFtW hWc hDA (hO2.to_le hDO) hjodd
      (mem_normalizer_commutator_self hjA) hjD hjW hfix
  have hOeq : O = D ⊔ Fᵍ[τ] := by
    apply le_antisymm
    · rw [hOD]
      refine sup_le le_sup_left ?_
      rw [hWeq]
      exact sup_le (hFD.trans le_sup_left) le_sup_right
    · rw [hOD]
      exact sup_le_sup_left hFtW D
  have hDD₂ : D ≤ pCoreOf 2 ⁅A, A⁆ := by
    have hX : O ⊓ ⁅A, A⁆ ≤ pCoreOf 2 ⁅A, A⁆ := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        (hO2.to_le inf_le_left)
      intro b hb
      have hbA : b ∈ A := hBA hb
      have hbO : b ∈ normalizer (O : Set Γ) := by
        rw [hO]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A hbA
      exact mem_normalizer_inf hbO (Subgroup.le_normalizer hb)
    exact fun x hx => hX ⟨hDO hx, hDB hx⟩
  have hD₂O : pCoreOf 2 ⁅A, A⁆ ≤ O := by
    rw [hO]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hBA) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    refine hAeq.le.trans (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) ?_)
    refine le_normalizer_of_commute' fun x hx y hy => ?_
    exact hWc y (hBA (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy)) x (hFtW hx) |>.symm
  have hD₂D : pCoreOf 2 ⁅A, A⁆ ≤ D := by
    intro x hx
    have hxO : x ∈ D ⊔ Fᵍ[τ] := by rw [← hOeq]; exact hD₂O hx
    obtain ⟨d, hd, z, hz, rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => (hWc a (hDA ha) c (hFtW hc)).symm) hxO
    have hxB : d * z ∈ ⁅A, A⁆ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have hzB : z ∈ ⁅A, A⁆ := by
      have := (⁅A, A⁆ : Subgroup Γ).mul_mem ((⁅A, A⁆ : Subgroup Γ).inv_mem (hDB hd)) hxB
      simpa using this
    have hz' : z ∈ ⁅A, A⁆ ⊓ Fᵍ[τ] := ⟨hzB, hz⟩
    rw [hBFt, mem_bot] at hz'
    rw [hz', mul_one]
    exact hd
  have hD₂eq : pCoreOf 2 ⁅A, A⁆ = D := le_antisymm hD₂D hDD₂
  have hKeq : ⁅A, A⁆ = K3 ⊔ pCoreOf 2 ⁅A, A⁆ := by
    rw [hD₂eq]
    have hB' : K3 ⊔ D ≤ ⁅A, A⁆ := sup_le hK3 hDB
    have hAB' : A = (K3 ⊔ D) ⊔ Fᵍ[τ] := by
      calc A = K3 ⊔ O := hAK3
        _ = K3 ⊔ (D ⊔ Fᵍ[τ]) := by rw [hOeq]
        _ = (K3 ⊔ D) ⊔ Fᵍ[τ] := (sup_assoc _ _ _).symm
    apply le_antisymm _ hB'
    intro b hb
    obtain ⟨b', hb', z, hz, rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => (hWc a (hBA (hB' ha)) c (hFtW hc)).symm) (hAB'.le (hBA hb))
    have hzB : z ∈ ⁅A, A⁆ := by
      have := (⁅A, A⁆ : Subgroup Γ).mul_mem ((⁅A, A⁆ : Subgroup Γ).inv_mem (hB' hb')) hb
      simpa using this
    have hz' : z ∈ ⁅A, A⁆ ⊓ Fᵍ[τ] := ⟨hzB, hz⟩
    rw [hBFt, mem_bot] at hz'
    rw [hz', mul_one]
    exact hb'
  have hMeq : M = pCoreOf 2 ⁅A, A⁆ ⊔ (pCoreOf 2 ⁅A, A⁆)ᵍ[τ] := by
    rw [hD₂eq]
    have hOt : Oᵍ[τ] = Dᵍ[τ] ⊔ F := by
      rw [hOeq, conj_sup, conj_conj_of_mul_self hτ]
    apply le_antisymm
    · calc M = O ⊔ Oᵍ[τ] := hM
        _ ≤ D ⊔ Dᵍ[τ] := by
          refine sup_le ?_ ?_
          · rw [hOeq]; exact sup_le le_sup_left ((conj_mono τ hFD).trans le_sup_right)
          · rw [hOt]; exact sup_le le_sup_right (hFD.trans le_sup_left)
    · refine sup_le hDM ?_
      exact (conj_mono τ hDO).trans (by rw [hM]; exact le_sup_right)
  exact ⟨hcomm, hBBt, hBBc, hAAt, hD₂eq, hKeq, hMeq⟩

end Abstract

end Y8_GA

section Y8_GB

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement Pointwise

section Dict2

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_le_normalizer {B A : Subgroup G} (hB : B ≤ normalizer (A : Set G)) {x : G}
    (hx : x ∈ B ⊔ A) : ∃ b ∈ B, ∃ a ∈ A, x = b * a := by
  have : x ∈ (B : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B A hB]
    exact hx
  obtain ⟨b, hb, a, ha, rfl⟩ := this
  exact ⟨b, hb, a, ha, rfl⟩

theorem dedekind_sup_inf {A B C : Subgroup G} (hAC : A ≤ C) (hB : B ≤ normalizer (A : Set G)) :
    (B ⊔ A) ⊓ C = (B ⊓ C) ⊔ A := by
  apply le_antisymm
  · rintro x ⟨hxBA, hxC⟩
    obtain ⟨b, hb, a, ha, rfl⟩ := mem_sup_of_le_normalizer hB hxBA
    have hbC : b ∈ C := by
      have := C.mul_mem hxC (C.inv_mem (hAC ha))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hb, hbC⟩ ha
  · exact sup_le (inf_le_inf le_sup_left le_rfl) (le_inf le_sup_right hAC)

theorem pCoreOf_conj {t : G} (htt : t * t = 1) (X : Subgroup G) :
    pCoreOf 2 (Xᵍ[t]) = (pCoreOf 2 X)ᵍ[t] := by
  have key : ∀ X : Subgroup G, (pCoreOf 2 X)ᵍ[t] ≤ pCoreOf 2 (Xᵍ[t]) := by
    intro X
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (conj_mono t (CFSG.LieType.BorelTits.pCoreOf_le 2 X)) ?_ ?_
    · intro x hx
      have hx' : t * x * t⁻¹ ∈ X := mem_conj_iff.1 hx
      have h1 := conj_mem_normalizer_conj t
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx')
      have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rwa [e] at h1
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).of_equiv
        (Subgroup.equivMapOfInjective _ (MulEquiv.toMonoidHom (MulAut.conj t⁻¹))
          (MulAut.conj t⁻¹).injective)
  apply le_antisymm _ (key X)
  have := conj_mono t (key (Xᵍ[t]))
  rwa [conj_conj_of_mul_self htt, conj_conj_of_mul_self htt] at this

theorem normal_subgroupOf_of_le_normalizer' {A X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) :
    (A.subgroupOf X).Normal := by
  have : A.subgroupOf X =
      ((NormalizerQuotient.proj A).comp (Subgroup.inclusion hX)).ker := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact (NormalizerQuotient.proj_eq_one_iff (A := A) (x := Subgroup.inclusion hX x)).symm
  rw [this]
  exact MonoidHom.normal_ker _

theorem exists_barEquiv {A X : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    [(A.subgroupOf X).Normal] :
    Nonempty ((X ⧸ A.subgroupOf X) ≃* NormalizerQuotient.bar A X) := by
  let φ : X →* NormalizerQuotient.Bar A :=
    (NormalizerQuotient.proj A).comp (Subgroup.inclusion hX)
  have hker : φ.ker = A.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact NormalizerQuotient.proj_eq_one_iff (A := A) (x := Subgroup.inclusion hX x)
  have hrange : φ.range = NormalizerQuotient.bar A X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact NormalizerQuotient.proj_mem_bar (x := Subgroup.inclusion hX x) x.2
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem commutator_mem_of_bar_comm {A X X' : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hX' : X' ≤ normalizer (A : Set G))
    (h : ∀ a ∈ NormalizerQuotient.bar A X, ∀ b ∈ NormalizerQuotient.bar A X', a * b = b * a) :
    ∀ x ∈ X, ∀ y ∈ X', x * y * x⁻¹ * y⁻¹ ∈ A := by
  intro x hx y hy
  have h1 := h _ (NormalizerQuotient.proj_mem_bar (x := ⟨x, hX hx⟩) hx) _
    (NormalizerQuotient.proj_mem_bar (x := ⟨y, hX' hy⟩) hy)
  exact (commutator_mem_iff_proj (hX hx) (hX' hy)).1 h1.symm

theorem bar_comm_of_commutator_mem {A X X' : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hX' : X' ≤ normalizer (A : Set G))
    (h : ∀ x ∈ X, ∀ y ∈ X', x * y * x⁻¹ * y⁻¹ ∈ A) :
    ∀ a ∈ NormalizerQuotient.bar A X, ∀ b ∈ NormalizerQuotient.bar A X', a * b = b * a := by
  rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
  have hx' : (x : G) ∈ X := hx
  have hy' : (y : G) ∈ X' := hy
  exact ((commutator_mem_iff_proj x.2 y.2).2 (h x hx' y hy')).symm

end Dict2

end Y8_GB

section Y8_G1

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (bar proj Bar)
open scoped MatrixGroups commutatorElement Pointwise

section G1Core

variable {G : Type} [Group G] [Finite G]

theorem G1_core {t : G} (htt : t * t = 1) {Y W M Q₁ R K₃ K₄ N O K₅ : Subgroup G} {j : G}
    (hYN : N ≤ normalizer (Y : Set G)) (htY : t ∈ normalizer (Y : Set G))
    (hY2 : IsPGroup 2 Y) (hYW : Y ≤ W) (hN : N = K₄ ⊔ K₄ᵍ[t])
    (hK₄K₄t : K₄ ⊓ K₄ᵍ[t] = W) (hK₄K₄tc : ⁅K₄, K₄ᵍ[t]⁆ ≤ W)
    (hK₄W : ∀ x ∈ K₄, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ Y)
    (hK₄p : K₄ ≤ ⁅K₄, K₄⁆ ⊔ W) (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hW2 : IsPGroup 2 W)
    (hO : O = pCoreOf 2 K₄) (hM : M = O ⊔ Oᵍ[t]) (hM' : ⁅M, M⁆ = W)
    (hQN : Q₁ ≤ normalizer (Y : Set G)) (hQQt : (Q₁ ⊔ Y) ⊓ (Q₁ᵍ[t] ⊔ Y) = Y)
    (hR : R = Q₁ ⊔ W) (hRK : IsSylowOf 2 R K₄) (hOQ : O = (Q₁ ⊓ M) ⊔ W)
    (hjN : j ∈ N) (hjK : j ∈ normalizer (K₄ : Set G)) (hjQ : j ∈ normalizer (Q₁ : Set G))
    (hjM : j ∈ normalizer (M : Set G)) (hjodd : Odd (orderOf j))
    (hjW : ∀ w ∈ W, w * j * w⁻¹ * j⁻¹ ∈ Y)
    (hjfix : ∀ m ∈ M, m * j * m⁻¹ * j⁻¹ ∈ W → m ∈ W)
    (hK₃ : K₃ ≤ ⁅K₄, K₄⁆) (hK₄K₃ : K₄ = K₃ ⊔ O) (hK₅ : K₅ = ⁅K₄, K₄⁆ ⊔ Y) :
    (∀ x ∈ K₄, ∀ y ∈ K₄ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y) ∧ K₅ ⊓ K₅ᵍ[t] = Y ∧
      (∀ x ∈ K₅, ∀ y ∈ K₅ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y) ∧ K₅ ⊔ K₅ᵍ[t] = N ∧
      pCoreOf 2 K₅ = (Q₁ ⊓ M) ⊔ Y ∧ K₅ = K₃ ⊔ pCoreOf 2 K₅ ∧
      M = pCoreOf 2 K₅ ⊔ pCoreOf 2 (K₅ᵍ[t]) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₄N' : K₄ ≤ N := by rw [hN]; exact le_sup_left
  have hK₄tN' : K₄ᵍ[t] ≤ N := by rw [hN]; exact le_sup_right
  have hK₄Y : K₄ ≤ normalizer (Y : Set G) := hK₄N'.trans hYN
  have hK₄tY : K₄ᵍ[t] ≤ normalizer (Y : Set G) := hK₄tN'.trans hYN
  have hWK₄ : W ≤ K₄ := by rw [← hK₄K₄t]; exact inf_le_left
  have hWK₄t : W ≤ K₄ᵍ[t] := by rw [← hK₄K₄t]; exact inf_le_right
  have hYK₄ : Y ≤ K₄ := hYW.trans hWK₄
  have hYK₄t : Y ≤ K₄ᵍ[t] := hYW.trans hWK₄t
  have hWY : W ≤ normalizer (Y : Set G) := hWK₄.trans hK₄Y
  have hOK₄ : O ≤ K₄ := by rw [hO]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 K₄
  have hOtK₄t : Oᵍ[t] ≤ K₄ᵍ[t] := conj_mono t hOK₄
  have hMN : M ≤ N := by rw [hM]; exact sup_le (hOK₄.trans hK₄N') (hOtK₄t.trans hK₄tN')
  have hMY : M ≤ normalizer (Y : Set G) := hMN.trans hYN
  have hWO : W ≤ O := by rw [hOQ]; exact le_sup_right
  have hOM : O ≤ M := by rw [hM]; exact le_sup_left
  have hOY : O ≤ normalizer (Y : Set G) := hOK₄.trans hK₄Y
  have hOtY : Oᵍ[t] ≤ normalizer (Y : Set G) := hOtK₄t.trans hK₄tY
  have hYM : Y ≤ M := hYW.trans (hWO.trans hOM)
  have hB4 : ⁅K₄, K₄⁆ ≤ K₄ := Subgroup.commutator_le_self K₄
  have hB4Y : ⁅K₄, K₄⁆ ≤ normalizer (Y : Set G) := hB4.trans hK₄Y
  have hK₅K₄ : K₅ ≤ K₄ := by rw [hK₅]; exact sup_le hB4 hYK₄
  have hK₅Y : K₅ ≤ normalizer (Y : Set G) := hK₅K₄.trans hK₄Y
  have hK₅tY : K₅ᵍ[t] ≤ normalizer (Y : Set G) := (conj_mono t hK₅K₄).trans hK₄tY
  have hYt : Yᵍ[t] = Y := conj_eq_of_mem_normalizer htY
  have hYK₅ : Y ≤ K₅ := by rw [hK₅]; exact le_sup_right
  have hYK₅t : Y ≤ K₅ᵍ[t] := by
    have := conj_mono t hYK₅
    rwa [hYt] at this
  have hQtN : Q₁ᵍ[t] ≤ normalizer (Y : Set G) := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ Q₁ := mem_conj_iff.1 hx
    have h1 := conj_mem_normalizer_conj t (g := t * x * t⁻¹) (A := Y) (hQN hx')
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    rw [e, hYt] at h1
    exact h1
  have hjY : j ∈ normalizer (Y : Set G) := hYN hjN
  have hK₃N : K₃ ≤ normalizer (Y : Set G) := (hK₃.trans hB4).trans hK₄Y
  have hτ : proj Y ⟨t, htY⟩ * proj Y ⟨t, htY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htY⟩ : normalizer (Y : Set G)) * ⟨t, htY⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have hconj : ∀ X : Subgroup G,
      bar Y (Xᵍ[t]) = (bar Y X)ᵍ[proj Y ⟨t, htY⟩] := fun X => bar_map_conj htY X
  have hA1 : bar Y K₄ ⊓ (bar Y K₄)ᵍ[proj Y ⟨t, htY⟩] = bar Y W := by
    rw [← hconj K₄, ← bar_inf hYK₄ hYK₄t, hK₄K₄t]
  have hA2 : ⁅bar Y K₄, (bar Y K₄)ᵍ[proj Y ⟨t, htY⟩]⁆ ≤ bar Y W := by
    rw [← hconj K₄, ← bar_commutator hK₄Y hK₄tY]
    exact NormalizerQuotient.bar_mono hK₄K₄tc
  have hWc : ∀ a ∈ bar Y K₄, ∀ w ∈ bar Y W, a * w = w * a :=
    bar_comm_of_commutator_mem hK₄Y hWY hK₄W
  have hA4 : bar Y K₄ ≤ ⁅bar Y K₄, bar Y K₄⁆ ⊔ bar Y W := by
    rw [← bar_commutator hK₄Y hK₄Y, ← bar_sup hB4Y hWY]
    exact NormalizerQuotient.bar_mono hK₄p
  have hWab' : ∀ x ∈ bar Y W, ∀ y ∈ bar Y W, x * y = y * x := by
    refine bar_comm_of_commutator_mem hWY hWY fun x hx y hy => ?_
    rw [hWab x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem Y
  have hW2' : IsPGroup 2 (bar Y W) := NormalizerQuotient.isPGroup_bar hW2
  have hOγ : bar Y O = pCoreOf 2 (bar Y K₄) := by
    rw [hO]; exact bar_pCoreOf hY2 hYK₄ hK₄Y
  have hM_eq : bar Y M = pCoreOf 2 (bar Y K₄) ⊔ (pCoreOf 2 (bar Y K₄))ᵍ[proj Y ⟨t, htY⟩] := by
    rw [← hOγ, ← hconj O, ← bar_sup hOY hOtY, ← hM]
  have hM'γ : ⁅bar Y M, bar Y M⁆ = bar Y W := by
    rw [← bar_commutator hMY hMY, hM']
  have hQ1 : bar Y Q₁ ⊓ (bar Y Q₁)ᵍ[proj Y ⟨t, htY⟩] = ⊥ := by
    have : bar Y Q₁ ⊓ (bar Y Q₁)ᵍ[proj Y ⟨t, htY⟩] = bar Y ((Q₁ ⊔ Y) ⊓ (Q₁ᵍ[t] ⊔ Y)) := by
      rw [bar_inf le_sup_right le_sup_right, bar_sup_self hQN, bar_sup_self hQtN, hconj Q₁]
    rw [this, hQQt, bar_self]
  have hD_eq : bar Y Q₁ ⊓ bar Y M = bar Y ((Q₁ ⊓ M) ⊔ Y) := by
    rw [← bar_sup_self hQN, ← bar_inf (A := Y) (X := Q₁ ⊔ Y) (Y := M) le_sup_right hYM,
      dedekind_sup_inf hYM hQN]
  have hOD : pCoreOf 2 (bar Y K₄) = (bar Y Q₁ ⊓ bar Y M) ⊔ bar Y W := by
    have e : ((Q₁ ⊓ M) ⊔ Y) ⊔ W = O := by rw [sup_assoc, sup_eq_right.2 hYW, ← hOQ]
    have hX : (Q₁ ⊓ M) ⊔ Y ≤ normalizer (Y : Set G) :=
      sup_le (inf_le_left.trans hQN) Subgroup.le_normalizer
    rw [← hOγ, hD_eq, ← bar_sup hX hWY, e]
  have hYR : Y ≤ R := by rw [hR]; exact hYW.trans le_sup_right
  have hSyl : IsSylowOf 2 (bar Y Q₁ ⊔ bar Y W) (bar Y K₄) := by
    rw [← bar_sup hQN hWY, ← hR]
    exact bar_isSylowOf hYR hK₄Y hRK
  have hjodd' : Odd (orderOf (proj Y ⟨j, hjY⟩)) := by
    have h1 : orderOf (proj Y ⟨j, hjY⟩) ∣ orderOf (⟨j, hjY⟩ : normalizer (Y : Set G)) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact hjodd.of_dvd_nat h1
  have hjA' : proj Y ⟨j, hjY⟩ ∈ normalizer ((bar Y K₄ : Subgroup (Bar Y)) : Set (Bar Y)) :=
    proj_mem_normalizer_bar hK₄Y hjY hjK
  have hjD' : proj Y ⟨j, hjY⟩ ∈
      normalizer (((bar Y Q₁ ⊓ bar Y M : Subgroup (Bar Y))) : Set (Bar Y)) :=
    mem_normalizer_inf (proj_mem_normalizer_bar hQN hjY hjQ) (proj_mem_normalizer_bar hMY hjY hjM)
  have hjW' : ∀ w ∈ bar Y W, proj Y ⟨j, hjY⟩ * w = w * proj Y ⟨j, hjY⟩ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : G) ∈ W := hw
    exact (commutator_mem_iff_proj w.2 hjY).2 (hjW w hw')
  have hDfix' : ∀ x ∈ bar Y Q₁ ⊓ bar Y M,
      x * proj Y ⟨j, hjY⟩ * x⁻¹ * (proj Y ⟨j, hjY⟩)⁻¹ = 1 → x ∈ bar Y W := by
    intro x hx h1
    have hx' : x ∈ bar Y ((Q₁ ⊓ M) ⊔ Y) := by rw [← hD_eq]; exact hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx'
    have hx₀' : (x₀ : G) ∈ (Q₁ ⊓ M) ⊔ Y := hx₀
    have hx₀M : (x₀ : G) ∈ M := (sup_le inf_le_right hYM) hx₀'
    have h2 : proj Y x₀ * proj Y ⟨j, hjY⟩ = proj Y ⟨j, hjY⟩ * proj Y x₀ := by
      have h3 := mul_inv_eq_one.1 h1
      calc proj Y x₀ * proj Y ⟨j, hjY⟩
          = (proj Y x₀ * proj Y ⟨j, hjY⟩ * (proj Y x₀)⁻¹) * proj Y x₀ := by group
        _ = proj Y ⟨j, hjY⟩ * proj Y x₀ := by rw [h3]
    have hc : (x₀ : G) * j * (x₀ : G)⁻¹ * j⁻¹ ∈ Y :=
      (commutator_mem_iff_proj x₀.2 hjY).1 h2.symm
    exact NormalizerQuotient.proj_mem_bar (hjfix _ hx₀M (hYW hc))
  have hK3' : bar Y K₃ ≤ ⁅bar Y K₄, bar Y K₄⁆ := by
    rw [← bar_commutator hK₄Y hK₄Y]; exact NormalizerQuotient.bar_mono hK₃
  have hAK3' : bar Y K₄ = bar Y K₃ ⊔ pCoreOf 2 (bar Y K₄) := by
    rw [← hOγ, ← bar_sup hK₃N hOY, ← hK₄K₃]
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := structure_main
    (τ := proj Y ⟨t, htY⟩) hτ (A := bar Y K₄) (W := bar Y W) (O := pCoreOf 2 (bar Y K₄))
    (M := bar Y M) (Q := bar Y Q₁) (D := bar Y Q₁ ⊓ bar Y M) (K3 := bar Y K₃)
    (j := proj Y ⟨j, hjY⟩) hA1 hA2 hWc hA4 hWab' hW2' rfl hM_eq hM'γ hQ1 inf_le_left inf_le_right
    hOD hSyl hjodd' hjA' hjD' hjW' hDfix' hK3' hAK3'
  have hbarB : bar Y K₅ = ⁅bar Y K₄, bar Y K₄⁆ := by
    rw [hK₅, bar_sup_self hB4Y, bar_commutator hK₄Y hK₄Y]
  have hbarBt : bar Y (K₅ᵍ[t]) = (⁅bar Y K₄, bar Y K₄⁆)ᵍ[proj Y ⟨t, htY⟩] := by
    rw [hconj, hbarB]
  have hpK₅ : pCoreOf 2 K₅ ≤ normalizer (Y : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 K₅).trans hK₅Y
  have hY_le : Y ≤ pCoreOf 2 K₅ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYK₅ hK₅Y hY2
  have hpK₅t : pCoreOf 2 (K₅ᵍ[t]) ≤ normalizer (Y : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hK₅tY
  have hY_let : Y ≤ pCoreOf 2 (K₅ᵍ[t]) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYK₅t hK₅tY hY2
  have hX : (Q₁ ⊓ M) ⊔ Y ≤ normalizer (Y : Set G) :=
    sup_le (inf_le_left.trans hQN) Subgroup.le_normalizer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine commutator_mem_of_bar_comm hK₄Y hK₄tY fun a ha b hb => hc1 a ha b ?_
    rw [← hconj K₄]; exact hb
  · have h1 : bar Y (K₅ ⊓ K₅ᵍ[t]) = bar Y Y := by
      rw [bar_inf hYK₅ hYK₅t, hbarB, hbarBt, hc2, bar_self]
    exact (bar_inj (le_inf hYK₅ hYK₅t) le_rfl (inf_le_left.trans hK₅Y)
      Subgroup.le_normalizer).1 h1
  · refine commutator_mem_of_bar_comm hK₅Y hK₅tY fun a ha b hb => hc3 a ?_ b ?_
    · rw [← hbarB]; exact ha
    · rw [← hbarBt]; exact hb
  · have h1 : bar Y (K₅ ⊔ K₅ᵍ[t]) = bar Y N := by
      rw [bar_sup hK₅Y hK₅tY, hbarB, hbarBt, ← hc4, hN, bar_sup hK₄Y hK₄tY, hconj K₄]
    have hYN' : Y ≤ N := hYK₄.trans hK₄N'
    exact (bar_inj (hYK₅.trans le_sup_left) hYN' (sup_le hK₅Y hK₅tY) hYN).1 h1
  · have h1 : bar Y (pCoreOf 2 K₅) = bar Y ((Q₁ ⊓ M) ⊔ Y) := by
      rw [bar_pCoreOf hY2 hYK₅ hK₅Y, hbarB, hc5, hD_eq]
    exact (bar_inj hY_le le_sup_right hpK₅ hX).1 h1
  · have h1 : bar Y K₅ = bar Y (K₃ ⊔ pCoreOf 2 K₅) := by
      rw [bar_sup hK₃N hpK₅, bar_pCoreOf hY2 hYK₅ hK₅Y, hbarB]
      exact hc6
    exact (bar_inj hYK₅ (hY_le.trans le_sup_right) hK₅Y (sup_le hK₃N hpK₅)).1 h1
  · have h1 : bar Y M = bar Y (pCoreOf 2 K₅ ⊔ pCoreOf 2 (K₅ᵍ[t])) := by
      rw [bar_sup hpK₅ hpK₅t, bar_pCoreOf hY2 hYK₅ hK₅Y, bar_pCoreOf hY2 hYK₅t hK₅tY, hbarB,
        hbarBt, pCoreOf_conj hτ]
      exact hc7
    exact (bar_inj hYM (hY_le.trans le_sup_left) hMY (sup_le hpK₅ hpK₅t)).1 h1

end G1Core

end Y8_G1

section Y8_G1b

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (bar proj Bar)
open scoped MatrixGroups commutatorElement Pointwise

section G1Aux

variable {G : Type} [Group G] [Finite G]

theorem Q_inter_Y {Q Qt Z Z' Y : Subgroup G} (hZQ : Z ≤ Q) (hZ'Qt : Z' ≤ Qt) (hY : Y = Z ⊔ Z')
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Qt, x * y = y * x) (hQQt : Q ⊓ Qt ≤ Z) :
    (Q ⊔ Y) ⊓ (Qt ⊔ Y) = Y := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have e1 : Q ⊔ Y = Q ⊔ Z' := by
      apply le_antisymm
      · rw [hY]; exact sup_le le_sup_left (sup_le (hZQ.trans le_sup_left) le_sup_right)
      · exact sup_le_sup_left (hY ▸ le_sup_right) Q
    have e2 : Qt ⊔ Y = Qt ⊔ Z := by
      apply le_antisymm
      · rw [hY]; exact sup_le le_sup_left (sup_le le_sup_right (hZ'Qt.trans le_sup_left))
      · exact sup_le_sup_left (hY ▸ le_sup_left) Qt
    rw [e1] at hx1
    rw [e2] at hx2
    obtain ⟨q, hq, z', hz', rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => (hcomm a ha c (hZ'Qt hc)).symm) hx1
    obtain ⟨q', hq', z, hz, hxe⟩ := mem_sup_of_commute'
      (fun c hc a ha => hcomm c (hZQ hc) a ha) hx2
    have hzz' : z * z' = z' * z := hcomm z (hZQ hz) z' (hZ'Qt hz')
    have h1 : q * z⁻¹ = q' * z'⁻¹ := by
      have e : q = q' * z * z'⁻¹ := by
        calc q = q * z' * z'⁻¹ := by group
          _ = q' * z * z'⁻¹ := by rw [hxe]
      rw [e]
      calc q' * z * z'⁻¹ * z⁻¹ = q' * (z * z'⁻¹ * z⁻¹) := by group
        _ = q' * z'⁻¹ := by
          congr 1
          have : z * z'⁻¹ = z'⁻¹ * z := by
            calc z * z'⁻¹ = z'⁻¹ * (z' * z) * z'⁻¹ := by group
              _ = z'⁻¹ * (z * z') * z'⁻¹ := by rw [hzz']
              _ = z'⁻¹ * z := by group
          rw [this]; group
    have hmem : q * z⁻¹ ∈ Q ⊓ Qt := by
      refine ⟨Q.mul_mem hq (Q.inv_mem (hZQ hz)), ?_⟩
      rw [h1]
      exact Qt.mul_mem hq' (Qt.inv_mem (hZ'Qt hz'))
    have hqz : q ∈ Z := by
      have := Z.mul_mem (hQQt hmem) hz
      simpa using this
    rw [hY]
    exact mul_mem (Subgroup.mem_sup_left hqz) (Subgroup.mem_sup_right hz')
  · exact le_inf le_sup_right le_sup_right

theorem step1_commute {Y W P K₃ K₄ O Q₃ : Subgroup G} {v : G}
    (hK₄ : K₄ = K₃ ⊔ O) (hOP : O ≤ P) (hPY : P ≤ normalizer (Y : Set G))
    (hPW : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ Y) (hWY : W ≤ normalizer (Y : Set G))
    (hK₃ : K₃ = Q₃ ⊔ Q₃ᵍ[v]) (hQ₃P : Q₃ ≤ P) (hvY : v ∈ normalizer (Y : Set G))
    (hvW : v ∈ normalizer (W : Set G)) :
    ∀ x ∈ K₄, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ Y := by
  have hP : P ≤ centralizerMod Y W := fun x hx =>
    mem_centralizerMod_iff.2 ⟨hPY hx, fun b hb _ => hPW x hx b hb⟩
  have hQv : Q₃ᵍ[v] ≤ centralizerMod Y W := by
    intro y hy
    have hy' : v * y * v⁻¹ ∈ Q₃ := mem_conj_iff.1 hy
    have hyN : y ∈ normalizer (Y : Set G) := by
      have h1 := mul_mem (mul_mem (inv_mem hvY) (hPY (hQ₃P hy'))) hvY
      simpa [mul_assoc] using h1
    refine mem_centralizerMod_iff.2 ⟨hyN, fun w hw hwN => ?_⟩
    have hw' : v * w * v⁻¹ ∈ W := (mem_normalizer_iff.1 hvW w).1 hw
    have h1 := hPW _ (hQ₃P hy') _ hw'
    have h2 := (mem_normalizer_iff.1 (inv_mem hvY) _).1 h1
    have e : v⁻¹ * (v * y * v⁻¹ * (v * w * v⁻¹) * (v * y * v⁻¹)⁻¹ * (v * w * v⁻¹)⁻¹) * v⁻¹⁻¹ =
        y * w * y⁻¹ * w⁻¹ := by group
    rw [e] at h2
    exact h2
  have hK₃C : K₃ ≤ centralizerMod Y W := by
    rw [hK₃]; exact sup_le (hQ₃P.trans hP) hQv
  intro x hx w hw
  have hxC : x ∈ centralizerMod Y W := by
    rw [hK₄] at hx
    exact (sup_le hK₃C (hOP.trans hP)) hx
  exact (mem_centralizerMod_iff.1 hxC).2 w hw (hWY hw)

theorem mem_zpowers_sq_of_odd {Γ : Type} [Group Γ] {j : Γ} (hodd : Odd (orderOf j)) :
    j ∈ zpowers (j ^ 2) := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨(k + 1 : ℕ), ?_⟩
  simp only [zpow_natCast]
  have h1 : (j ^ 2) ^ (k + 1) = j ^ (2 * k + 2) := by rw [← pow_mul]; congr 1
  have h2 : j ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one j
  rw [h1, show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ, h2, one_mul]

theorem fpf_abstract {Γ : Type} [Group Γ] {τ j : Γ} {Mγ Lγ : Subgroup Γ} (hτ : τ * τ = 1)
    (hjτ : j * τ = τ * j) (hab : ∀ x ∈ Mγ, ∀ y ∈ Mγ, x * y = y * x)
    (hsq : ∀ x ∈ Mγ, x * x = 1) (hτM : τ ∈ normalizer (Mγ : Set Γ))
    (hfix : ∀ x ∈ Mγ, τ * x * τ⁻¹ = x → x ∈ Lγ) (hL : ∀ x ∈ Lγ, j * x * j⁻¹ = x → x = 1) :
    ∀ m ∈ Mγ, j * m * j⁻¹ = m → m = 1 := by
  intro m hm hjm
  have ha : τ * m * τ⁻¹ ∈ Mγ := (mem_normalizer_iff.1 hτM m).1 hm
  have hτa : τ * (τ * m * τ⁻¹) * τ⁻¹ = m := by
    calc τ * (τ * m * τ⁻¹) * τ⁻¹ = (τ * τ) * m * (τ * τ)⁻¹ := by group
      _ = m := by rw [hτ]; group
  have hu : m * (τ * m * τ⁻¹) ∈ Mγ := Mγ.mul_mem hm ha
  have hufix : τ * (m * (τ * m * τ⁻¹)) * τ⁻¹ = m * (τ * m * τ⁻¹) := by
    calc τ * (m * (τ * m * τ⁻¹)) * τ⁻¹ = (τ * m * τ⁻¹) * (τ * (τ * m * τ⁻¹) * τ⁻¹) := by group
      _ = (τ * m * τ⁻¹) * m := by rw [hτa]
      _ = m * (τ * m * τ⁻¹) := hab _ ha m hm
  have huL := hfix _ hu hufix
  have hjτ' : j * τ * j⁻¹ = τ := by rw [hjτ]; group
  have hja : j * (τ * m * τ⁻¹) * j⁻¹ = τ * m * τ⁻¹ := by
    calc j * (τ * m * τ⁻¹) * j⁻¹
        = (j * τ * j⁻¹) * (j * m * j⁻¹) * (j * τ * j⁻¹)⁻¹ := by group
      _ = τ * m * τ⁻¹ := by rw [hjτ', hjm]
  have hju : j * (m * (τ * m * τ⁻¹)) * j⁻¹ = m * (τ * m * τ⁻¹) := by
    calc j * (m * (τ * m * τ⁻¹)) * j⁻¹ = (j * m * j⁻¹) * (j * (τ * m * τ⁻¹) * j⁻¹) := by group
      _ = m * (τ * m * τ⁻¹) := by rw [hjm, hja]
  have h1 : m * (τ * m * τ⁻¹) = 1 := hL _ huL hju
  have h2 : τ * m * τ⁻¹ = m :=
    (eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right (hsq m hm))
  have hmL := hfix m hm h2
  exact hL m hmL hjm

theorem trivial_abstract {Γ : Type} [Group Γ] {τ j : Γ} {Wγ Lγ : Subgroup Γ} (hτ : τ * τ = 1)
    (hjτ : j * τ = τ * j) (hodd : Odd (orderOf j)) (hab : ∀ x ∈ Wγ, ∀ y ∈ Wγ, x * y = y * x)
    (hsq : ∀ x ∈ Wγ, x * x = 1) (hτW : τ ∈ normalizer (Wγ : Set Γ))
    (hjW : j ∈ normalizer (Wγ : Set Γ))
    (hfix : ∀ x ∈ Wγ, τ * x * τ⁻¹ = x → x ∈ Lγ) (hL : ∀ x ∈ Lγ, j * x * j⁻¹ = x) :
    ∀ w ∈ Wγ, j * w * j⁻¹ = w := by
  have key : ∀ w ∈ Wγ, (j * j) * w * (j * j)⁻¹ = w := by
    intro w hw
    obtain ⟨c, hc⟩ : ∃ c, c = j * w * j⁻¹ := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = τ * w * τ⁻¹ := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, e = j * d * j⁻¹ := ⟨_, rfl⟩
    have hcW : c ∈ Wγ := by rw [hc]; exact (mem_normalizer_iff.1 hjW w).1 hw
    have hdW : d ∈ Wγ := by rw [hd]; exact (mem_normalizer_iff.1 hτW w).1 hw
    have heW : e ∈ Wγ := by rw [he]; exact (mem_normalizer_iff.1 hjW d).1 hdW
    have hτd : τ * d * τ⁻¹ = w := by
      rw [hd]
      calc τ * (τ * w * τ⁻¹) * τ⁻¹ = (τ * τ) * w * (τ * τ)⁻¹ := by group
        _ = w := by rw [hτ]; group
    have hτc : τ * c * τ⁻¹ = e := by
      rw [hc, he, hd]
      calc τ * (j * w * j⁻¹) * τ⁻¹ = (τ * j) * w * (τ * j)⁻¹ := by group
        _ = (j * τ) * w * (j * τ)⁻¹ := by rw [← hjτ]
        _ = j * (τ * w * τ⁻¹) * j⁻¹ := by group
    have ha : w * d ∈ Wγ := Wγ.mul_mem hw hdW
    have hafix : τ * (w * d) * τ⁻¹ = w * d := by
      calc τ * (w * d) * τ⁻¹ = (τ * w * τ⁻¹) * (τ * d * τ⁻¹) := by group
        _ = d * w := by rw [← hd, hτd]
        _ = w * d := hab d hdW w hw
    have haL := hL _ (hfix _ ha hafix)
    have eq1 : c * e = w * d := by
      calc c * e = j * (w * d) * j⁻¹ := by rw [hc, he, hd]; group
        _ = w * d := haL
    have hu : c * w ∈ Wγ := Wγ.mul_mem hcW hw
    have hτu : τ * (c * w) * τ⁻¹ = e * d := by
      calc τ * (c * w) * τ⁻¹ = (τ * c * τ⁻¹) * (τ * w * τ⁻¹) := by group
        _ = e * d := by rw [hτc, ← hd]
    have huu : (c * w) * (τ * (c * w) * τ⁻¹) = 1 := by
      calc (c * w) * (τ * (c * w) * τ⁻¹) = (c * w) * (e * d) := by rw [hτu]
        _ = c * (w * e) * d := by group
        _ = c * (e * w) * d := by rw [hab w hw e heW]
        _ = (c * e) * (w * d) := by group
        _ = (w * d) * (w * d) := by rw [eq1]
        _ = 1 := hsq _ ha
    have hufix : τ * (c * w) * τ⁻¹ = c * w := by
      rw [eq_inv_of_mul_eq_one_right huu]
      exact inv_eq_of_mul_eq_one_right (hsq _ hu)
    have huL := hL _ (hfix _ hu hufix)
    have hjc : j * c * j⁻¹ = w := by
      have h3 : (j * c * j⁻¹) * c = c * w := by
        calc (j * c * j⁻¹) * c = (j * c * j⁻¹) * (j * w * j⁻¹) := by rw [← hc]
          _ = j * (c * w) * j⁻¹ := by group
          _ = c * w := huL
      calc j * c * j⁻¹ = (j * c * j⁻¹ * c) * c⁻¹ := by group
        _ = (c * w) * c⁻¹ := by rw [h3]
        _ = w := by rw [hab c hcW w hw]; group
    calc (j * j) * w * (j * j)⁻¹ = j * (j * w * j⁻¹) * j⁻¹ := by group
      _ = j * c * j⁻¹ := by rw [← hc]
      _ = w := hjc
  intro w hw
  have hmem : j ^ 2 ∈ centralizer (Wγ : Set Γ) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := key x hx
    rw [pow_two]
    calc x * (j * j) = ((j * j) * x * (j * j)⁻¹) * (j * j) := by rw [h1]
      _ = (j * j) * x := by group
  have hj : j ∈ centralizer (Wγ : Set Γ) := (zpowers_le).2 hmem (mem_zpowers_sq_of_odd hodd)
  have h2 := mem_centralizer_iff.1 hj w hw
  calc j * w * j⁻¹ = (w * j) * j⁻¹ := by rw [h2]
    _ = w := by group

theorem proj_fixed_iff {A : Subgroup G} {t x₀ : G} (ht : t ∈ normalizer (A : Set G))
    (hx : x₀ ∈ normalizer (A : Set G)) :
    proj A ⟨t, ht⟩ * proj A ⟨x₀, hx⟩ * (proj A ⟨t, ht⟩)⁻¹ = proj A ⟨x₀, hx⟩ ↔
      x₀⁻¹ * (t * x₀ * t⁻¹) ∈ A := by
  have e : proj A (⟨x₀, hx⟩⁻¹ * (⟨t, ht⟩ * ⟨x₀, hx⟩ * ⟨t, ht⟩⁻¹)) =
      (proj A ⟨x₀, hx⟩)⁻¹ * (proj A ⟨t, ht⟩ * proj A ⟨x₀, hx⟩ * (proj A ⟨t, ht⟩)⁻¹) := by
    simp only [map_mul, map_inv]
  have e2 : proj A (⟨x₀, hx⟩⁻¹ * (⟨t, ht⟩ * ⟨x₀, hx⟩ * ⟨t, ht⟩⁻¹)) = 1 ↔
      x₀⁻¹ * (t * x₀ * t⁻¹) ∈ A := NormalizerQuotient.proj_eq_one_iff
  rw [← e2, e, inv_mul_eq_one]
  exact eq_comm

theorem fpf_transfer {t j : G} {W M ML : Subgroup G} (htt : t * t = 1) (hjt : j * t = t * j)
    (hMW : M ≤ normalizer (W : Set G)) (hML : ML ≤ M)
    (hsq : ∀ x ∈ M, x * x ∈ W) (hcom : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ W)
    (htW : t ∈ normalizer (W : Set G)) (htM : t ∈ normalizer (M : Set G))
    (hjW : j ∈ normalizer (W : Set G))
    (hT2 : ∀ a ∈ M, a⁻¹ * (t * a * t⁻¹) ∈ W → a ∈ ML ⊔ W)
    (hfpf : ∀ m ∈ ML, m * j * m⁻¹ * j⁻¹ ∈ W → m ∈ W) :
    ∀ m ∈ M, m * j * m⁻¹ * j⁻¹ ∈ W → m ∈ W := by
  intro m hm hmj
  have hmN : m ∈ normalizer (W : Set G) := hMW hm
  have hjτ : proj W ⟨j, hjW⟩ * proj W ⟨t, htW⟩ = proj W ⟨t, htW⟩ * proj W ⟨j, hjW⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hjt
  have hτ : proj W ⟨t, htW⟩ * proj W ⟨t, htW⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htW⟩ : normalizer (W : Set G)) * ⟨t, htW⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have hab : ∀ x ∈ bar W M, ∀ y ∈ bar W M, x * y = y * x :=
    bar_comm_of_commutator_mem hMW hMW hcom
  have hsq' : ∀ x ∈ bar W M, x * x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    exact NormalizerQuotient.proj_eq_one_iff.2 (hsq x₀ hx₀)
  have hτM := proj_mem_normalizer_bar hMW htW htM
  have hfix : ∀ x ∈ bar W M, proj W ⟨t, htW⟩ * x * (proj W ⟨t, htW⟩)⁻¹ = x → x ∈ bar W ML := by
    rintro _ ⟨x₀, hx₀, rfl⟩ hx
    have hx₀M : (x₀ : G) ∈ M := hx₀
    have h1 := (proj_fixed_iff htW x₀.2).1 hx
    have h2 := hT2 _ hx₀M h1
    rw [← bar_sup_self (hML.trans hMW)]
    exact NormalizerQuotient.proj_mem_bar h2
  have hL : ∀ x ∈ bar W ML, proj W ⟨j, hjW⟩ * x * (proj W ⟨j, hjW⟩)⁻¹ = x → x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩ hx
    have hx₀ML : (x₀ : G) ∈ ML := hx₀
    have h3 := (commutator_mem_iff_proj x₀.2 hjW).1 (mul_inv_eq_iff_eq_mul.1 hx)
    exact NormalizerQuotient.proj_eq_one_iff.2 (hfpf _ hx₀ML h3)
  have h5 := fpf_abstract hτ hjτ hab hsq' hτM hfix hL (proj W ⟨m, hmN⟩)
    (NormalizerQuotient.proj_mem_bar hm)
    (mul_inv_eq_iff_eq_mul.2 ((commutator_mem_iff_proj hmN hjW).2 hmj))
  exact NormalizerQuotient.proj_eq_one_iff.1 h5

theorem trivial_transfer {t j : G} {Y W WL : Subgroup G} (htt : t * t = 1) (hjt : j * t = t * j)
    (hodd : Odd (orderOf j)) (hYW : Y ≤ W) (hWY : W ≤ normalizer (Y : Set G))
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hWsq : ∀ x ∈ W, x * x = 1)
    (htY : t ∈ normalizer (Y : Set G)) (htW : t ∈ normalizer (W : Set G))
    (hjY : j ∈ normalizer (Y : Set G)) (hjW : j ∈ normalizer (W : Set G))
    (hWL : WL ≤ W)
    (hT2 : ∀ a ∈ W, a⁻¹ * (t * a * t⁻¹) ∈ Y → a ∈ WL ⊔ Y)
    (hjWL : ∀ w ∈ WL, w * j * w⁻¹ * j⁻¹ ∈ Y) :
    ∀ w ∈ W, w * j * w⁻¹ * j⁻¹ ∈ Y := by
  intro w hw
  have hwN : w ∈ normalizer (Y : Set G) := hWY hw
  have hjτ : proj Y ⟨j, hjY⟩ * proj Y ⟨t, htY⟩ = proj Y ⟨t, htY⟩ * proj Y ⟨j, hjY⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hjt
  have hτ : proj Y ⟨t, htY⟩ * proj Y ⟨t, htY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htY⟩ : normalizer (Y : Set G)) * ⟨t, htY⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have hjodd : Odd (orderOf (proj Y ⟨j, hjY⟩)) := by
    have h1 : orderOf (proj Y ⟨j, hjY⟩) ∣ orderOf (⟨j, hjY⟩ : normalizer (Y : Set G)) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  have hab : ∀ x ∈ bar Y W, ∀ y ∈ bar Y W, x * y = y * x := by
    refine bar_comm_of_commutator_mem hWY hWY fun x hx y hy => ?_
    rw [hWab x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem Y
  have hsq' : ∀ x ∈ bar Y W, x * x = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have : ((x₀ * x₀ : normalizer (Y : Set G)) : G) = 1 := by
      rw [Subgroup.coe_mul]; exact hWsq _ hx₀
    exact NormalizerQuotient.proj_eq_one_iff.2 (by rw [this]; exact one_mem Y)
  have hτW := proj_mem_normalizer_bar hWY htY htW
  have hjW' := proj_mem_normalizer_bar hWY hjY hjW
  have hfix : ∀ x ∈ bar Y W, proj Y ⟨t, htY⟩ * x * (proj Y ⟨t, htY⟩)⁻¹ = x → x ∈ bar Y WL := by
    rintro _ ⟨x₀, hx₀, rfl⟩ hx
    have hx₀W : (x₀ : G) ∈ W := hx₀
    have h1 := (proj_fixed_iff htY x₀.2).1 hx
    have h2 := hT2 _ hx₀W h1
    rw [← bar_sup_self (hWL.trans hWY)]
    exact NormalizerQuotient.proj_mem_bar h2
  have hL : ∀ x ∈ bar Y WL, proj Y ⟨j, hjY⟩ * x * (proj Y ⟨j, hjY⟩)⁻¹ = x := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    have hx₀ML : (x₀ : G) ∈ WL := hx₀
    have h3 := (commutator_mem_iff_proj x₀.2 hjY).2 (hjWL _ hx₀ML)
    exact mul_inv_eq_iff_eq_mul.2 h3
  have h5 := trivial_abstract hτ hjτ hjodd hab hsq' hτW hjW' hfix hL (proj Y ⟨w, hwN⟩)
    (NormalizerQuotient.proj_mem_bar hw)
  have h6 : proj Y ⟨j, hjY⟩ * proj Y ⟨w, hwN⟩ = proj Y ⟨w, hwN⟩ * proj Y ⟨j, hjY⟩ :=
    mul_inv_eq_iff_eq_mul.1 h5
  exact (commutator_mem_iff_proj hwN hjY).1 h6

theorem mem_centralizerMod_zpowers_of_fixed {A : Subgroup G} {t x : G} (htt : t * t = 1)
    (ht : t ∈ normalizer (A : Set G)) (hx : x ∈ normalizer (A : Set G))
    (h : x⁻¹ * (t * x * t⁻¹) ∈ A) : x ∈ centralizerMod A (zpowers t) := by
  rw [mem_centralizerMod_iff]
  refine ⟨hx, fun b hb hbN => ?_⟩
  rcases ProductToolboxAux.Core.eq_one_or_eq_of_mem_zpowers htt hb with rfl | rfl
  · simpa using one_mem A
  · have h2 := (mem_normalizer_iff.1 (inv_mem hx) _).1 h
    have hx' := mem_normalizer_iff.1 hx
    have e : x * b * x⁻¹ * b⁻¹ = (x * (x⁻¹ * (b * x * b⁻¹)) * x⁻¹)⁻¹ := by group
    rw [e]
    refine inv_mem ?_
    have := (mem_normalizer_iff.1 hx _).1 h
    simpa using this

theorem diag_equiv {Γ : Type} [Group Γ] [Finite Γ] {τ : Γ} (hτ : τ * τ = 1) {B : Subgroup Γ}
    (hBBt : B ⊓ Bᵍ[τ] = ⊥) (hcomm : ∀ x ∈ B, ∀ y ∈ Bᵍ[τ], x * y = y * x) :
    Nonempty (B ≃* ↥((B ⊔ Bᵍ[τ]) ⊓ centralizer ({τ} : Set Γ))) := by
  have hτconj : ∀ x ∈ B, τ * x * τ⁻¹ ∈ Bᵍ[τ] := by
    intro x hx
    rw [mem_conj_iff]
    have : τ * (τ * x * τ⁻¹) * τ⁻¹ = x := by
      calc _ = (τ * τ) * x * (τ * τ)⁻¹ := by group
        _ = x := by rw [hτ]; group
    rw [this]; exact hx
  have hτconj' : ∀ y ∈ Bᵍ[τ], τ * y * τ⁻¹ ∈ B := fun y hy => mem_conj_iff.1 hy
  let δ : B →* Γ := MonoidHom.mk' (fun b => (b : Γ) * (τ * (b : Γ) * τ⁻¹)) (by
    intro a b
    have h1 : (b : Γ) * (τ * (a : Γ) * τ⁻¹) = (τ * (a : Γ) * τ⁻¹) * (b : Γ) :=
      hcomm (b : Γ) b.2 _ (hτconj a a.2)
    simp only [Subgroup.coe_mul]
    calc (a : Γ) * (b : Γ) * (τ * ((a : Γ) * (b : Γ)) * τ⁻¹)
        = (a : Γ) * ((b : Γ) * (τ * (a : Γ) * τ⁻¹)) * (τ * (b : Γ) * τ⁻¹) := by group
      _ = (a : Γ) * ((τ * (a : Γ) * τ⁻¹) * (b : Γ)) * (τ * (b : Γ) * τ⁻¹) := by rw [h1]
      _ = ((a : Γ) * (τ * (a : Γ) * τ⁻¹)) * ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) := by group)
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb' : (b : Γ) * (τ * (b : Γ) * τ⁻¹) = 1 := hb
    have hbt : (b : Γ) = (τ * (b : Γ) * τ⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hb'
    have : (b : Γ) ∈ B ⊓ Bᵍ[τ] := by
      refine ⟨b.2, ?_⟩
      rw [hbt]; exact Bᵍ[τ].inv_mem (hτconj _ b.2)
    rw [hBBt, mem_bot] at this
    exact Subtype.ext this
  have hrange : δ.range = (B ⊔ Bᵍ[τ]) ⊓ centralizer ({τ} : Set Γ) := by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      refine ⟨Subgroup.mul_mem_sup b.2 (hτconj _ b.2), ?_⟩
      show δ b ∈ centralizer ({τ} : Set Γ)
      rw [mem_centralizer_singleton_iff]
      have hbb : (b : Γ) * (τ * (b : Γ) * τ⁻¹) = (τ * (b : Γ) * τ⁻¹) * (b : Γ) :=
        hcomm _ b.2 _ (hτconj _ b.2)
      have hτx : τ * ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) * τ⁻¹ = (τ * (b : Γ) * τ⁻¹) * (b : Γ) := by
        calc τ * ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) * τ⁻¹
            = (τ * (b : Γ) * τ⁻¹) * ((τ * τ) * (b : Γ) * (τ * τ)⁻¹) := by group
          _ = (τ * (b : Γ) * τ⁻¹) * (b : Γ) := by rw [hτ]; group
      have hcent : τ * ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) = ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) * τ := by
        calc τ * ((b : Γ) * (τ * (b : Γ) * τ⁻¹))
            = (τ * ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) * τ⁻¹) * τ := by group
          _ = ((τ * (b : Γ) * τ⁻¹) * (b : Γ)) * τ := by rw [hτx]
          _ = ((b : Γ) * (τ * (b : Γ) * τ⁻¹)) * τ := by rw [← hbb]
      exact hcent.symm
    · rintro x ⟨hxN, hxc⟩
      obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup_of_commute'
        (fun c hc a ha => (hcomm a ha c hc).symm) hxN
      have hfix : τ * (b * c) * τ⁻¹ = b * c := by
        have := mem_centralizer_singleton_iff.1 hxc
        calc τ * (b * c) * τ⁻¹ = (b * c) * τ * τ⁻¹ := by rw [this]
          _ = b * c := by group
      have hc' : τ * c * τ⁻¹ ∈ B := hτconj' c hc
      have hb' : τ * b * τ⁻¹ ∈ Bᵍ[τ] := hτconj b hb
      have e1 : (τ * c * τ⁻¹) * (τ * b * τ⁻¹) = b * c := by
        calc (τ * c * τ⁻¹) * (τ * b * τ⁻¹) = τ * (c * b) * τ⁻¹ := by group
          _ = τ * (b * c) * τ⁻¹ := by rw [hcomm b hb c hc]
          _ = b * c := hfix
      have e2 : b⁻¹ * (τ * c * τ⁻¹) = c * (τ * b * τ⁻¹)⁻¹ := by
        have h3 : b⁻¹ * ((τ * c * τ⁻¹) * (τ * b * τ⁻¹)) = c := by rw [e1]; group
        calc b⁻¹ * (τ * c * τ⁻¹)
            = b⁻¹ * ((τ * c * τ⁻¹) * (τ * b * τ⁻¹)) * (τ * b * τ⁻¹)⁻¹ := by group
          _ = c * (τ * b * τ⁻¹)⁻¹ := by rw [h3]
      have hmem : c * (τ * b * τ⁻¹)⁻¹ ∈ B ⊓ Bᵍ[τ] := by
        refine ⟨?_, Bᵍ[τ].mul_mem hc (Bᵍ[τ].inv_mem hb')⟩
        rw [← e2]; exact B.mul_mem (B.inv_mem hb) hc'
      rw [hBBt, mem_bot] at hmem
      have hcq : c = τ * b * τ⁻¹ := mul_inv_eq_one.1 hmem
      exact ⟨⟨b, hb⟩, by show b * (τ * b * τ⁻¹) = b * c; rw [← hcq]⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem sectionIso_of_decomp {t : G} (htt : t * t = 1) {Y K₅ N L YL : Subgroup G}
    (hYN : N ≤ normalizer (Y : Set G)) (htY : t ∈ normalizer (Y : Set G))
    (hK₅N : K₅ ≤ N) (hYK₅ : Y ≤ K₅) (hK₅tN : K₅ᵍ[t] ≤ N)
    (hinf : K₅ ⊓ K₅ᵍ[t] = Y) (hcomm : ∀ x ∈ K₅, ∀ y ∈ K₅ᵍ[t], x * y * x⁻¹ * y⁻¹ ∈ Y)
    (hsup : K₅ ⊔ K₅ᵍ[t] = N)
    (hfix : N ⊓ centralizerMod Y (zpowers t) = L ⊔ Y) (hLN : L ≤ N)
    (hLt : ∀ l ∈ L, l * t = t * l) (hLY : L ⊓ Y = YL) :
    SectionIso K₅ Y L YL := by
  have hK₅Y : K₅ ≤ normalizer (Y : Set G) := hK₅N.trans hYN
  have hK₅tY : K₅ᵍ[t] ≤ normalizer (Y : Set G) := hK₅tN.trans hYN
  have hLY' : L ≤ normalizer (Y : Set G) := hLN.trans hYN
  have hYt : Yᵍ[t] = Y := conj_eq_of_mem_normalizer htY
  have hYK₅t : Y ≤ K₅ᵍ[t] := by
    have := conj_mono t hYK₅
    rwa [hYt] at this
  have hτ : proj Y ⟨t, htY⟩ * proj Y ⟨t, htY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htY⟩ : normalizer (Y : Set G)) * ⟨t, htY⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have hconj : ∀ X : Subgroup G,
      bar Y (Xᵍ[t]) = (bar Y X)ᵍ[proj Y ⟨t, htY⟩] := fun X => bar_map_conj htY X
  have hBBt : bar Y K₅ ⊓ (bar Y K₅)ᵍ[proj Y ⟨t, htY⟩] = ⊥ := by
    rw [← hconj, ← bar_inf hYK₅ hYK₅t, hinf, bar_self]
  have hcommΓ : ∀ x ∈ bar Y K₅, ∀ y ∈ (bar Y K₅)ᵍ[proj Y ⟨t, htY⟩], x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ bar Y (K₅ᵍ[t]) := by rw [hconj]; exact hy
    exact bar_comm_of_commutator_mem hK₅Y hK₅tY hcomm x hx y hy'
  have hBsup : bar Y K₅ ⊔ (bar Y K₅)ᵍ[proj Y ⟨t, htY⟩] = bar Y N := by
    rw [← hconj, ← bar_sup hK₅Y hK₅tY, hsup]
  have hτconj : ∀ x ∈ bar Y K₅, proj Y ⟨t, htY⟩ * x * (proj Y ⟨t, htY⟩)⁻¹ ∈
      (bar Y K₅)ᵍ[proj Y ⟨t, htY⟩] := by
    intro x hx
    rw [mem_conj_iff]
    have : proj Y ⟨t, htY⟩ * (proj Y ⟨t, htY⟩ * x * (proj Y ⟨t, htY⟩)⁻¹) *
        (proj Y ⟨t, htY⟩)⁻¹ = x := by
      calc _ = (proj Y ⟨t, htY⟩ * proj Y ⟨t, htY⟩) * x *
            (proj Y ⟨t, htY⟩ * proj Y ⟨t, htY⟩)⁻¹ := by group
        _ = x := by rw [hτ]; group
    rw [this]; exact hx
  have hLY'' : L ≤ N := hLN
  have hrangeL : bar Y N ⊓ centralizer ({proj Y ⟨t, htY⟩} : Set (Bar Y)) = bar Y L := by
    apply le_antisymm
    · rintro x ⟨hxN, hxc⟩
      obtain ⟨x₀, hx₀, rfl⟩ := hxN
      have hx₀N : (x₀ : G) ∈ N := hx₀
      have hxc' : proj Y x₀ * proj Y ⟨t, htY⟩ = proj Y ⟨t, htY⟩ * proj Y x₀ :=
        mem_centralizer_singleton_iff.1 hxc
      have h1 : (x₀ : G)⁻¹ * (t * (x₀ : G) * t⁻¹) ∈ Y := by
        refine (proj_fixed_iff htY x₀.2).1 ?_
        rw [← hxc']
        group
      have hxC : (x₀ : G) ∈ centralizerMod Y (zpowers t) :=
        mem_centralizerMod_zpowers_of_fixed htt htY x₀.2 h1
      have hxLY : (x₀ : G) ∈ L ⊔ Y := by
        rw [← hfix]; exact ⟨hx₀N, hxC⟩
      rw [← bar_sup_self hLY']
      exact NormalizerQuotient.proj_mem_bar hxLY
    · rintro x ⟨x₀, hx₀, rfl⟩
      have hx₀L : (x₀ : G) ∈ L := hx₀
      refine ⟨NormalizerQuotient.proj_mem_bar (hLN hx₀L), ?_⟩
      show proj Y x₀ ∈ centralizer ({proj Y ⟨t, htY⟩} : Set (Bar Y))
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hLt _ hx₀L)
  haveI hnK₅ : (Y.subgroupOf K₅).Normal := normal_subgroupOf_of_le_normalizer' hK₅Y
  haveI hnLY : (Y.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer' hLY'
  have hYLeq : YL.subgroupOf L = Y.subgroupOf L := by
    rw [← hLY, Subgroup.inf_subgroupOf_left]
  haveI hnL : (YL.subgroupOf L).Normal := by rw [hYLeq]; exact hnLY
  refine ⟨hnK₅, hnL, ?_⟩
  have e1 := (exists_barEquiv hK₅Y).some
  have e2 := (diag_equiv hτ hBBt hcommΓ).some
  have e3 : ↥((bar Y K₅ ⊔ (bar Y K₅)ᵍ[proj Y ⟨t, htY⟩]) ⊓
      centralizer ({proj Y ⟨t, htY⟩} : Set (Bar Y))) ≃* ↥(bar Y L) :=
    MulEquiv.subgroupCongr (by rw [hBsup, hrangeL])
  have e4 := (exists_barEquiv hLY').some
  exact ⟨e1.trans (e2.trans (e3.trans (e4.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hYLeq.symm))))⟩

theorem dedekind_sup_inf_left {A B C : Subgroup G} (hAC : A ≤ C) (hA : A ≤ normalizer (B : Set G)) :
    (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  apply le_antisymm
  · rintro x ⟨hxAB, hxC⟩
    have : x ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hA]
      exact hxAB
    obtain ⟨a, ha, b, hb, rfl⟩ := this
    have hbC : b ∈ C := by
      have := C.mul_mem (C.inv_mem (hAC ha)) hxC
      simpa using this
    exact Subgroup.mul_mem_sup ha ⟨hb, hbC⟩
  · exact sup_le (le_inf le_sup_left hAC) (inf_le_inf le_sup_right le_rfl)

theorem P_inf_K₅ {P K₃ O₅ K₅ Q₃ : Subgroup G} (hK₅ : K₅ = K₃ ⊔ O₅) (hO₅P : O₅ ≤ P)
    (hK₃O : K₃ ≤ normalizer (O₅ : Set G)) (hPK₃ : P ⊓ K₃ = Q₃) : P ⊓ K₅ = Q₃ ⊔ O₅ := by
  rw [hK₅, inf_comm, dedekind_sup_inf hO₅P hK₃O, inf_comm, hPK₃]

theorem P_inf_K₃ {P M X₀ N₃ K₃ K Q₃ : Subgroup G} (hP : P = M ⊔ X₀) (hX₀N : X₀ ≤ N₃)
    (hX₀M : X₀ ≤ normalizer (M : Set G)) (hN₃M : N₃ ⊓ M ≤ X₀) (hK₃N : K₃ ≤ N₃) (hK₃K : K₃ ≤ K)
    (hQ₃ : Q₃ = X₀ ⊓ K) (hQ₃K₃ : Q₃ ≤ K₃) : P ⊓ K₃ = Q₃ := by
  apply le_antisymm
  · rintro x ⟨hxP, hxK₃⟩
    have hxP' : x ∈ (X₀ ⊔ M) ⊓ N₃ := ⟨by rw [sup_comm, ← hP]; exact hxP, hK₃N hxK₃⟩
    rw [dedekind_sup_inf_left hX₀N hX₀M] at hxP'
    have hxX₀ : x ∈ X₀ := by
      have h1 : x ∈ X₀ ⊔ (M ⊓ N₃) := hxP'
      have h2 : X₀ ⊔ (M ⊓ N₃) ≤ X₀ := sup_le le_rfl (by rw [inf_comm]; exact hN₃M)
      exact h2 h1
    rw [hQ₃]
    exact ⟨hxX₀, hK₃K hxK₃⟩
  · refine le_inf ?_ hQ₃K₃
    rw [hQ₃, hP]
    exact inf_le_left.trans le_sup_right

theorem part3_l {t : G} {Y M P Q₁ Q₃ O₅ X₀ J : Subgroup G}
    (hO₅ : O₅ = (Q₁ ⊓ M) ⊔ Y) (hQ₃Q₁ : Q₃ ≤ Q₁) (hQ₁P : Q₁ ≤ P) (hYP : Y ≤ P)
    (hYX₀ : Y ≤ X₀) (hYM : Y ≤ M) (hQ₁Y : Q₁ ≤ normalizer (Y : Set G))
    (hX₀ : X₀ = Q₃ ⊔ Q₃ᵍ[t]) (hcomm : ∀ x ∈ Q₁, ∀ y ∈ Q₁ᵍ[t], x * y = y * x)
    (hQQt : Q₁ ⊓ Q₁ᵍ[t] ≤ Y) (hP2 : IsPGroup 2 P)
    (hJodd : Odd (Nat.card J)) (hJQ : J ≤ normalizer (Q₁ : Set G))
    (hJY : J ≤ normalizer (Y : Set G)) (hJO₅ : J ≤ normalizer (O₅ : Set G))
    (hPO₅ : P ≤ normalizer (O₅ : Set G))
    (hPJ : ∀ x ∈ P, ∀ s ∈ J, x * s * x⁻¹ * s⁻¹ ∈ M)
    (hPC : P ⊓ centralizer (J : Set G) ≤ X₀) : Q₃ ⊔ O₅ = Q₁ ⊔ Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYO₅ : Y ≤ O₅ := by rw [hO₅]; exact le_sup_right
  have hO₅M' : O₅ ≤ Q₁ ⊔ Y := by rw [hO₅]; exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  apply le_antisymm
  · exact sup_le (hQ₃Q₁.trans le_sup_left) hO₅M'
  · refine sup_le ?_ (hYO₅.trans le_sup_right)
    set M' := Q₁ ⊔ Y with hM'
    have hM'P : M' ≤ P := sup_le hQ₁P hYP
    have hJM' : J ≤ normalizer (M' : Set G) := fun s hs => mem_normalizer_sup (hJQ hs) (hJY hs)
    have hM'n : M' ≤ normalizer (O₅ : Set G) := hM'P.trans hPO₅
    have hM'2 : IsPGroup 2 M' := hP2.to_le hM'P
    have hsolv : Group.IsSolvable M' := by
      haveI := hM'2.isNilpotent
      infer_instance
    have hcop : (Nat.card J).Coprime (Nat.card M') := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hM'2
      rw [hk]
      exact (Nat.coprime_two_right.2 hJodd).pow_right k
    have hMeq : M' ⊓ M = O₅ := by
      rw [hM', hO₅]
      exact dedekind_sup_inf hYM hQ₁Y
    intro x hx
    have hxM' : x ∈ M' := Subgroup.mem_sup_left hx
    have hfix : ∀ s ∈ J, x⁻¹ * (s * x * s⁻¹) ∈ O₅ := by
      intro s hs
      have h1 : x⁻¹ * (s * x * s⁻¹) ∈ M' := by
        have := M'.mul_mem (M'.inv_mem hxM') ((mem_normalizer_iff.1 (hJM' hs) x).1 hxM')
        exact this
      have h2 : x⁻¹ * (s * x * s⁻¹) ∈ M := by
        have := hPJ x⁻¹ (P.inv_mem (hM'P hxM')) s hs
        simpa [mul_assoc] using this
      rw [← hMeq]
      exact ⟨h1, h2⟩
    obtain ⟨c, hc, n, hn, hxcn⟩ := exists_mem_inf_centralizer_mul_of_coprime (M := M') (N := O₅)
      (S := J) hO₅M' hM'n hJM' hJO₅ hsolv hcop hxM' hfix
    have hcX₀ : c ∈ X₀ := hPC ⟨hM'P hc.1, hc.2⟩
    have hcM' : c ∈ (Q₁ ⊓ X₀) ⊔ Y := by
      have : c ∈ (Q₁ ⊔ Y) ⊓ X₀ := ⟨hc.1, hcX₀⟩
      rwa [dedekind_sup_inf hYX₀ hQ₁Y] at this
    have hQ₁X₀ : Q₁ ⊓ X₀ ≤ Q₃ ⊔ Y := by
      rintro y ⟨hyQ₁, hyX₀⟩
      rw [hX₀] at hyX₀
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute'
        (fun c hc a ha => (hcomm a (hQ₃Q₁ ha) c (conj_mono t hQ₃Q₁ hc)).symm) hyX₀
      have hbQ₁ : b ∈ Q₁ := by
        have := Q₁.mul_mem (Q₁.inv_mem (hQ₃Q₁ ha)) hyQ₁
        simpa using this
      have hbY : b ∈ Y := hQQt ⟨hbQ₁, conj_mono t hQ₃Q₁ hb⟩
      exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbY)
    have hcQ₃ : c ∈ Q₃ ⊔ O₅ := by
      have h1 : (Q₁ ⊓ X₀) ⊔ Y ≤ Q₃ ⊔ O₅ := sup_le (hQ₁X₀.trans (sup_le le_sup_left
        (hYO₅.trans le_sup_right))) (hYO₅.trans le_sup_right)
      exact h1 hcM'
    rw [hxcn]
    exact mul_mem hcQ₃ (Subgroup.mem_sup_right hn)

end G1Aux

end Y8_G1b

section Y8_G1c

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (bar proj Bar)
open scoped MatrixGroups commutatorElement Pointwise

section G1Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem h1Zero_up {A B : Subgroup G} (hAB : IsElemSection A B) {τ : G} (hτ : τ * τ = 1)
    (hτA : τ ∈ normalizer (A : Set G)) (hτB : τ ∈ normalizer (B : Set G))
    (hfree : IsFreeSection τ A B) (hH1 : H1Zero τ B) : H1Zero τ A :=
  T2_h1_zero hτ hAB.le (ProductToolboxAux.Core.le_normalizer hAB) hτA hτB hH1
    (T1_h1_zero hAB hτ hτA hτB hfree)

theorem h1Zero_bot' (τ : G) : H1Zero τ ⊥ := by
  intro n hn _
  rw [Subgroup.mem_bot.1 hn]
  exact ⟨1, one_mem _, by simp⟩

theorem normalizer_of_commutator_le {K K' N : Subgroup G} (hN : N = K ⊔ K')
    (hc : ⁅K, K'⁆ ≤ K) : N ≤ normalizer (K : Set G) := by
  have key : ∀ y ∈ K', ∀ x ∈ K, y * x * y⁻¹ ∈ K := by
    intro y hy x hx
    have h1 : ⁅x, y⁆ ∈ K := hc (commutator_mem_commutator hx hy)
    have e : y * x * y⁻¹ = ⁅x, y⁆⁻¹ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem (K.inv_mem h1) hx
  rw [hN]
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key y hy x
  · intro hx
    have := key y⁻¹ (K'.inv_mem hy) _ hx
    simpa [mul_assoc] using this

theorem t_mem_normalizer_swap {t : G} (htt : t * t = 1) (K : Subgroup G) :
    t ∈ normalizer ((K ⊔ Kᵍ[t] : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_eq (by rw [conj_sup, conj_conj_of_mul_self htt, sup_comm])

theorem inf_centralizerMod_eq {t : G} (htt : t * t = 1) {N Y : Subgroup G} (hYN : Y ≤ N)
    (hNY : N ≤ normalizer (Y : Set G)) (htN : t ∈ normalizer (N : Set G))
    (htY : t ∈ normalizer (Y : Set G)) (hH1 : H1Zero t Y) :
    N ⊓ centralizerMod Y (zpowers t) = (N ⊓ centralizer ({t} : Set G)) ⊔ Y := by
  apply le_antisymm
  · rintro x ⟨hxN, hxC⟩
    have hx1 := (mem_centralizerMod_iff.1 hxC).2 t (mem_zpowers t) htY
    have hxi : x⁻¹ ∈ centralizerMod Y (zpowers t) := (centralizerMod Y (zpowers t)).inv_mem hxC
    have hx2 := (mem_centralizerMod_iff.1 hxi).2 t (mem_zpowers t) htY
    have hfix : x⁻¹ * (t * x * t⁻¹) ∈ Y := by simpa [mul_assoc] using hx2
    exact T2_lift htt hYN hNY htN htY hH1 x hxN hfix
  · refine sup_le ?_ ?_
    · rintro x ⟨hxN, hxc⟩
      refine ⟨hxN, mem_centralizerMod_iff.2 ⟨hNY hxN, fun b hb hbN => ?_⟩⟩
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxc
      rcases ProductToolboxAux.Core.eq_one_or_eq_of_mem_zpowers htt hb with rfl | rfl
      · simpa using one_mem Y
      · rw [hxt]; simpa using one_mem Y
    · intro y hy
      refine ⟨hYN hy, mem_centralizerMod_iff.2 ⟨hNY (hYN hy), fun b _ hb => ?_⟩⟩
      have h1 : b * y⁻¹ * b⁻¹ ∈ Y := (mem_normalizer_iff.1 hb y⁻¹).1 (Y.inv_mem hy)
      have e : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
      rw [e]
      exact Y.mul_mem hy h1

theorem G1_aux (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (nTwo d t = kFive d t K ⊔ (kFive d t K)ᵍ[t] ∧
      kFive d t K ⊓ (kFive d t K)ᵍ[t] = yamadaY₂ d t ∧
      ⁅kFive d t K, (kFive d t K)ᵍ[t]⁆ ≤ yamadaY₂ d t ∧
      SectionIso (kFive d t K) (yamadaY₂ d t) (lvM d) (d.Y.map L.subtype) ∧
      nTwo d t ⊓ centralizerMod (yamadaY₂ d t) (zpowers t) = lvM d ⊔ yamadaY₂ d t ∧
      kFive d t K = ⁅kFour d t K, kFour d t K⁆ ⊔ yamadaY₂ d t ∧
      nTwo d t ≤ normalizer ((kFive d t K : Subgroup G) : Set G)) ∧
    (kFive d t K = kThree d t K ⊔ pCoreOf 2 (kFive d t K) ∧
      yamadaM₆ d t = pCoreOf 2 (kFive d t K) ⊔ pCoreOf 2 ((kFive d t K)ᵍ[t]) ∧
      pCoreOf 2 (kFive d t K) = (qOne d t K₁ ⊓ yamadaM₆ d t) ⊔ yamadaY₂ d t) ∧
    (yamadaP d t ⊓ kFive d t K = qThree d t K ⊔ pCoreOf 2 (kFive d t K) ∧
      qThree d t K ⊔ pCoreOf 2 (kFive d t K) = qOne d t K₁ ⊔ yamadaY₂ d t) := by
  have hlay := hp.layer
  have hK : IsLayerComponent d t K := hL.comp
  have hK₁ : IsN1Factor d t K₁ := hL.factor
  have htt : t * t = 1 := h.t_mul_t
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hXY, hXSyl, hXcard⟩, ⟨hXQ, hQQt, hQQc, hQSyl, hQcard⟩,
    ⟨hYE, hEEt, hEel, hEcard, hEQ, hEQn, hEcoat⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩,
    ⟨hNX, hlev, hNM, v₁, hv₁K, hv₁eq, hv₁Q⟩, ⟨hN3M, hN2M, hPM, hPSyl, hMJ⟩⟩ :=
    A3_structure h d hp hK
  obtain ⟨⟨hZE, hZcard, hVZ, hZZt⟩, hKu, hQu⟩ := A4_u_component h d hp hK
  obtain ⟨⟨hN2K2, hK2K2t, hK2K2c, hK2iso, hK2sec⟩, hB1b⟩ := B1_decomposition h d hp hK
  obtain ⟨-, ⟨hN2K4, hK4K4t, hK4K4c, hK4eq, hK4iso, hK4C, hK4C', hK4perf⟩,
    ⟨hWK4, hK4O, hMO, hOz⟩⟩ := C2_decomposition h d hp hK
  obtain ⟨⟨hPQ, hQQV, hQQc', hD1, hD2, hD3⟩, hZser, hRdec, hF4⟩ := F0_sylow h d hp hK hK₁
  obtain ⟨⟨hN1norm, hN2norm⟩, hRQO, hlabel⟩ := F1_normalizers h d hp hK hK₁
  have hF3 := F3_R_eq h d hp hL
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  have hM6c := S5_commutator_M₆ h d hlay
  have hT4 := T4_series_free h d hp
  have hT5 := T5_J₀ h d hp
  have hG0 := G0_aux h d hp hL
  have hQ₃Q₁ : qThree d t K ≤ qOne d t K₁ := hG0.2.2
  have H3 := natSL2_layer h d hp hK
  set Y := yamadaY₂ d t with hYdef
  set W := yamadaW₃ d t with hWdef
  set M := yamadaM₆ d t with hMdef
  set P := yamadaP d t with hPdef
  set N := nTwo d t with hNdef
  set N₃ := nThree d t with hN₃def
  set K₃ := kThree d t K with hK₃def
  set K₄ := kFour d t K with hK₄def
  set K₅ := kFive d t K with hK₅def
  set Q₁ := qOne d t K₁ with hQ₁def
  set Q₃ := qThree d t K with hQ₃def
  set O := pCoreOf 2 K₄ with hOdef
  set R := rSub d t K with hRdef
  set X₀ := prodX d t with hX₀def
  have hP2 : IsPGroup 2 P := hPSyl.isPGroup
  have hPN : P ≤ N := hPSyl.le
  have hPY : P ≤ normalizer (Y : Set G) := by
    have := normalizer_le_normalizer_series P 2
    rw [hZ2] at this
    exact Subgroup.le_normalizer.trans this
  have hMP : M ≤ P := yamadaM₆_le_yamadaP d t
  have hMY : M ≤ normalizer (Y : Set G) := hMP.trans hPY
  have hYN₃ : Y ≤ N₃ := by rw [← hN3M]; exact inf_le_left
  have hN₃Y : N₃ ≤ normalizer (Y : Set G) := by
    obtain ⟨φ, -, hker⟩ := hN3iso
    have : (Y.subgroupOf N₃).Normal := hker ▸ MonoidHom.normal_ker φ
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYN₃).1 this
  have hN₃N : N₃ ≤ N := le_sup_left
  have hNY : N ≤ normalizer (Y : Set G) := sup_le hN₃Y hMY
  have htY : t ∈ normalizer (Y : Set G) := h.t_mem_normalizer_yamadaY₂ d
  have htP : t ∈ normalizer (P : Set G) := h.t_mem_normalizer_yamadaP d hlay
  have hYP : Y ≤ P := by rw [← hZ2]; exact Subgroup.map_subtype_le _
  have hY2 : IsPGroup 2 Y := hP2.to_le hYP
  have hYW : Y ≤ W := by
    rw [← hZ2, ← hZ3]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hWP : W ≤ P := by rw [← hZ3]; exact Subgroup.map_subtype_le _
  have hW2 : IsPGroup 2 W := hP2.to_le hWP
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
    mul_comm_of_isMulCommutative_D4 (h.yamada_5_21 d hlay).2.1.1
  have hWsq : ∀ x ∈ W, x * x = 1 := fun x hx => by
    have := (h.yamada_5_21 d hlay).2.1.2 x hx
    rwa [pow_two] at this
  have hPW : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ Y := by
    intro x hx w hw
    rw [← hZ3] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have h1 := Subgroup.mem_upperCentralSeries_succ_iff.1 hw' ⟨x, hx⟩
    have h3 : ((w' * ⟨x, hx⟩ * w'⁻¹ * ⟨x, hx⟩⁻¹ : P) : G) ∈ Y := by
      rw [← hZ2]; exact ⟨_, h1, rfl⟩
    have e : x * (w' : G) * x⁻¹ * (w' : G)⁻¹ =
        ((w' * ⟨x, hx⟩ * w'⁻¹ * ⟨x, hx⟩⁻¹ : P) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      group
    rw [Subgroup.coe_subtype, e]
    exact Y.inv_mem h3
  have hK₄N : K₄ ≤ N := by rw [hN2K4]; exact le_sup_left
  have hK₄tN : K₄ᵍ[t] ≤ N := by rw [hN2K4]; exact le_sup_right
  have hOM : M = O ⊔ Oᵍ[t] := by rw [hMO, pCoreOf_conj htt]
  have hOMle : O ≤ M := by rw [hOM]; exact le_sup_left
  have hOP : O ≤ P := hOMle.trans hMP
  have hWK₄ : W ≤ K₄ := hWK4
  have hK₄W' : K₄ ≤ normalizer (W : Set G) := by
    obtain ⟨hnW, -, -⟩ := hK4iso
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hWK₄).1 hnW
  have hWt : Wᵍ[t] = W := by rw [← hK4K4t]; exact conj_inf_conj_self htt K₄
  have hK₄tW' : K₄ᵍ[t] ≤ normalizer (W : Set G) := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ K₄ := mem_conj_iff.1 hx
    have h1 := conj_mem_normalizer_conj t (hK₄W' hx')
    rw [hWt] at h1
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    rwa [e] at h1
  have hNW : N ≤ normalizer (W : Set G) := by rw [hN2K4]; exact sup_le hK₄W' hK₄tW'
  have htW : t ∈ normalizer (W : Set G) := mem_normalizer_of_conj_eq hWt
  have htN : t ∈ normalizer (N : Set G) := by rw [hN2K4]; exact t_mem_normalizer_swap htt K₄
  have hWY : W ≤ normalizer (Y : Set G) := hWK₄.trans (hK₄N.trans hNY)
  have hvN₃ : vG d ∈ N₃ := hlev ⟨d.v, d.v_mem_leviLong, rfl⟩
  have hvY : vG d ∈ normalizer (Y : Set G) := hN₃Y hvN₃
  have hvW : vG d ∈ normalizer (W : Set G) := hNW (hN₃N hvN₃)
  have hQ₃K₃ := qThree_le_kThree h d hp hK
  have hKK₃t' : ∀ x ∈ K₃, ∀ y ∈ K₃ᵍ[t], x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hKK₃c hx) y hy).symm
  have hK₃sup : K₃ = Q₃ ⊔ Q₃ᵍ[vG d] := by
    have h1 := H3.sup_conj hv₁K hv₁Q
    have hw₁ : t⁻¹ * v₁ * t ∈ K₃ᵍ[t] := by
      rw [mem_conj_iff]
      have e : t * (t⁻¹ * v₁ * t) * t⁻¹ = v₁ := by group
      rw [e]; exact hv₁K
    have hpt : ∀ q ∈ Q₃, (vG d)⁻¹ * q * vG d = v₁⁻¹ * q * v₁ := by
      intro q hq
      have hc := hKK₃t' (v₁⁻¹ * q * v₁)
        (K₃.mul_mem (K₃.mul_mem (K₃.inv_mem hv₁K) (hQ₃K₃ hq)) hv₁K) _ hw₁
      rw [hv₁eq]
      calc (v₁ * (t⁻¹ * v₁ * t))⁻¹ * q * (v₁ * (t⁻¹ * v₁ * t))
          = (t⁻¹ * v₁ * t)⁻¹ * (v₁⁻¹ * q * v₁) * (t⁻¹ * v₁ * t) := by group
        _ = (t⁻¹ * v₁ * t)⁻¹ * ((t⁻¹ * v₁ * t) * (v₁⁻¹ * q * v₁)) := by rw [← hc]; group
        _ = v₁⁻¹ * q * v₁ := by group
    have h2 : Q₃ᵍ[vG d] = Q₃.map (MulEquiv.toMonoidHom (MulAut.conj v₁⁻¹)) := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, (hpt q hq).symm⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, hpt q hq⟩
    rw [h2]; exact h1.symm
  have hQ₃P : Q₃ ≤ P := by
    have : X₀ ≤ P := by rw [hPM]; exact le_sup_right
    exact (inf_le_left : Q₃ ≤ X₀).trans this
  have hK₄W : ∀ x ∈ K₄, ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ Y :=
    step1_commute hK4O hOP hPY hPW hWY hK₃sup hQ₃P hvY hvW
  have hK₄K₄tc' : ⁅K₄, K₄ᵍ[t]⁆ ≤ K₄ := hK4K4c.trans hWK₄
  have hNK₄ : N ≤ normalizer (K₄ : Set G) := normalizer_of_commutator_le hN2K4 hK₄K₄tc'
  have hRK : IsSylowOf 2 R K₄ := hPSyl.inf_of_le_normalizer hK₄N hNK₄
  have hWO : W ≤ O :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWK₄ hK₄W' hW2
  have hWM : W ≤ M := hWO.trans hOMle
  have hQ₁P : Q₁ ≤ P := inf_le_left
  have hQ₁W : Q₁ ≤ normalizer (W : Set G) := hQ₁P.trans (hPN.trans hNW)
  have hRQ₃O : R = Q₃ ⊔ O := hRQO.1
  have hRM : R ⊓ M = O := by
    apply le_antisymm
    · rintro x ⟨hxR, hxM⟩
      have hK₃K₄ : K₃ ≤ K₄ := (le_sup_left : K₃ ≤ K₃ ⊔ O).trans hK4O.ge
      have hQ₃O : Q₃ ≤ normalizer (O : Set G) := fun q hq =>
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₄ (hK₃K₄ (hQ₃K₃ hq))
      rw [hRQ₃O] at hxR
      obtain ⟨q, hq, o, ho, rfl⟩ := mem_sup_of_le_normalizer hQ₃O hxR
      have hqM : q ∈ M := by
        have := M.mul_mem hxM (M.inv_mem (hOMle ho))
        simpa using this
      have hqY : q ∈ Y := by
        have hX₀N₃ : X₀ ≤ N₃ := by rw [hNX]; exact le_sup_left
        have : q ∈ N₃ ⊓ M := ⟨hX₀N₃ ((inf_le_left : Q₃ ≤ X₀) hq), hqM⟩
        rwa [hN3M] at this
      exact O.mul_mem (hWO (hYW hqY)) ho
    · exact le_inf (hRQ₃O ▸ le_sup_right) hOMle
  have hOQ : O = (Q₁ ⊓ M) ⊔ W := by
    calc O = R ⊓ M := hRM.symm
      _ = (Q₁ ⊔ W) ⊓ M := by rw [hF3]
      _ = (Q₁ ⊓ M) ⊔ W := dedekind_sup_inf hWM hQ₁W
  obtain ⟨⟨hV₁K₁', hV₁Z⟩, hE3b⟩ := E3_commutators h d hp hK₁
  have hNPV₁ : normalizer (P : Set G) ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := by
    have := normalizer_le_normalizer_series P 1
    rwa [hZ1] at this
  have htV₁ : t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := hNPV₁ htP
  have hV₁t : (yamadaV₁ d t)ᵍ[t] = yamadaV₁ d t := conj_eq_of_mem_normalizer htV₁
  have hV₁P : yamadaV₁ d t ≤ P := by rw [← hZ1]; exact Subgroup.map_subtype_le _
  have hV₁Q₁ : yamadaV₁ d t ≤ Q₁ := le_inf hV₁P hV₁K₁'
  have hV₁Q₁t : yamadaV₁ d t ≤ Q₁ᵍ[t] := by
    have := conj_mono t hV₁Q₁
    rwa [hV₁t] at this
  have hcommQ := qOne_comm h d hp hK₁
  have hQQt : (Q₁ ⊔ Y) ⊓ (Q₁ᵍ[t] ⊔ Y) = Y := by
    refine Q_inter_Y (Q := Q₁) (Qt := Q₁ᵍ[t]) (Z := centerMod (yamadaV₁ d t) Q₁)
      (Z' := centerMod (yamadaV₁ d t) (Q₁ᵍ[t])) (Y := Y) ?_ ?_ hZser.1 hcommQ ?_
    · exact fun x hx => ((mem_centerMod_iff hV₁Q₁).1 hx).1
    · exact fun x hx => ((mem_centerMod_iff hV₁Q₁t).1 hx).1
    · rw [hQQV]
      unfold centerMod upperCenterMod
      exact NormalizerQuotient.le_lift _
  obtain ⟨hVC, hYC, hWC, hFC, hDC, hMC, hSC, -, -, -, hfl1, hfl2, hfl3, hfl4, hfl5, hfl6, hfl7,
    hfl8⟩ := hT4
  obtain ⟨j, hjlev, hjodd, hjt, hjS, hjfpf₀, hjtriv₀⟩ := exists_J4_element h d hp.two_le
  have hjL : j ∈ L := by
    obtain ⟨j₀, -, hj₀⟩ := hjlev
    exact hj₀ ▸ j₀.2
  have hjN₃ : j ∈ N₃ := hlev hjlev
  have hjN : j ∈ N := hN₃N hjN₃
  have hjP : j ∈ normalizer (P : Set G) :=
    ncs_le_normalizer_yamadaP h d hlay (mem_inf.2 ⟨hjt, hjS⟩)
  have hjQ : j ∈ normalizer (Q₁ : Set G) :=
    mem_normalizer_inf hjP (hN2norm (mem_inf.2 ⟨hjN, hjP⟩)).2
  have hNM : N ≤ normalizer (M : Set G) := by
    intro x hx
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hx
    rwa [hN2M] at this
  have hjM : j ∈ normalizer (M : Set G) := hNM hjN
  have hjK : j ∈ normalizer (K₄ : Set G) := hNK₄ hjN
  have hjt' : j * t = t * j := mem_centralizer_singleton_iff.1 hjt
  have htV₁' : t ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top t
  have h1V : H1Zero t (yamadaV₁ d t) :=
    h1Zero_up hfl1.1 htt htV₁ htV₁' hfl1.2.1 (h1Zero_bot' t)
  have h1Y : H1Zero t Y := h1Zero_up hfl2.1 htt htY htV₁ hfl2.2.1 h1V
  have h1W : H1Zero t W := h1Zero_up hfl3.1 htt htW htY hfl3.2.1 h1Y
  have hWL : (d.W.map L.subtype : Subgroup G) ≤ W := by rw [← hWC]; exact inf_le_left
  have hYL : (d.Y.map L.subtype : Subgroup G) ≤ Y := by rw [← hYC]; exact inf_le_left
  have hML : (d.M.map L.subtype : Subgroup G) ≤ M := by rw [← hMC]; exact inf_le_left
  have hjW : ∀ w ∈ W, w * j * w⁻¹ * j⁻¹ ∈ Y := by
    refine trivial_transfer htt hjt' hjodd hYW hWY hWab hWsq htY htW (hNY hjN) (hNW hjN)
      hWL ?_ ?_
    · intro a ha h'
      have := T2_lift htt hYW hWY htW htY h1Y a ha h'
      rwa [hWC] at this
    · intro w hw
      exact hYL (hjtriv₀ w hw)
  have hMN' : M ≤ N := hMP.trans hPN
  have hjfix : ∀ m ∈ M, m * j * m⁻¹ * j⁻¹ ∈ W → m ∈ W := by
    refine fpf_transfer htt hjt' (hMN'.trans hNW) hML
      (fun x hx => h.mul_self_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx)
      (fun x hx y hy => h.commutator_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx hy)
      htW (hB1b.2.2 htP) (hNW hjN) ?_ ?_
    · intro a ha h'
      have := T2_lift htt hWM (hMN'.trans hNW) (hB1b.2.2 htP) htW h1W a ha h'
      rwa [hMC] at this
    · intro m hm hmj
      have hmL : m ∈ L := by
        obtain ⟨m₀, -, hm₀⟩ := hm
        exact hm₀ ▸ m₀.2
      have hcL : m * j * m⁻¹ * j⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem hmL hjL) (L.inv_mem hmL)) (L.inv_mem hjL)
      have hct : m * j * m⁻¹ * j⁻¹ ∈ centralizer ({t} : Set G) := h.L_le_centralizer hcL
      have hmem : m * j * m⁻¹ * j⁻¹ ∈ d.W.map L.subtype := by
        rw [← hWC]; exact ⟨hmj, hct⟩
      exact hWL (hjfpf₀ m hm hmem)
  have hK₃K₄ : K₃ ≤ K₄ := (le_sup_left : K₃ ≤ K₃ ⊔ O).trans hK4O.ge
  have hK₃B : K₃ ≤ ⁅K₄, K₄⁆ :=
    H3.K_le_commutator.trans (Subgroup.commutator_mono hK₃K₄ hK₃K₄)
  have hK₅eq : K₅ = ⁅K₄, K₄⁆ ⊔ Y := by
    show ⁅K₄, K₄⁆ ⊔ K₃ ⊔ Y = ⁅K₄, K₄⁆ ⊔ Y
    rw [sup_eq_left.2 hK₃B]
  have hQN : Q₁ ≤ normalizer (Y : Set G) := hQ₁P.trans hPY
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := G1_core htt hNY htY hY2 hYW hN2K4 hK4K4t hK4K4c hK₄W
    hK4perf hWab hW2 rfl hOM hM6c hQN hQQt hF3 hRK hOQ hjN hjK hjQ hjM hjodd hjW hjfix hK₃B hK4O
    hK₅eq
  have hB4 : ⁅K₄, K₄⁆ ≤ K₄ := Subgroup.commutator_le_self K₄
  have hYK₄ : Y ≤ K₄ := hYW.trans hWK₄
  have hK₅K₄ : K₅ ≤ K₄ := by rw [hK₅eq]; exact sup_le hB4 hYK₄
  have hK₅N : K₅ ≤ N := hK₅K₄.trans hK₄N
  have hYK₅ : Y ≤ K₅ := by rw [hK₅eq]; exact le_sup_right
  have hK₅tN : K₅ᵍ[t] ≤ N := (conj_mono t hK₅K₄).trans hK₄tN
  have hYN' : Y ≤ N := hYN₃.trans hN₃N
  have hfixN : N ⊓ centralizerMod Y (zpowers t) = lvM d ⊔ Y := by
    rw [inf_centralizerMod_eq htt hYN' hNY htN htY h1Y, hK4C]
  have hLN : lvM d ≤ N := by rw [← hK4C]; exact inf_le_left
  have hLC : lvM d ≤ centralizer ({t} : Set G) := by rw [← hK4C]; exact inf_le_right
  have hLt : ∀ l ∈ lvM d, l * t = t * l := fun l hl => mem_centralizer_singleton_iff.1 (hLC hl)
  have hLY : lvM d ⊓ Y = d.Y.map L.subtype := by
    apply le_antisymm
    · intro x hx
      rw [← hYC]
      exact ⟨hx.2, hLC hx.1⟩
    · intro x hx
      have hx' : x ∈ Y ⊓ centralizer ({t} : Set G) := by rw [hYC]; exact hx
      refine ⟨?_, hx'.1⟩
      rw [← hK4C]
      exact ⟨hYN' hx'.1, hx'.2⟩
  have hSec : SectionIso K₅ Y (lvM d) (d.Y.map L.subtype) :=
    sectionIso_of_decomp htt hNY htY hK₅N hYK₅ hK₅tN c2 c3 c4 hfixN hLN hLt hLY
  have hNK₅ : N ≤ normalizer (K₅ : Set G) := fun g hg => by
    rw [hK₅eq]
    exact mem_normalizer_sup (mem_normalizer_commutator_self (hNK₄ hg)) (hNY hg)
  have hJodd : Odd (Nat.card (jZeroG d : Subgroup G)) := by
    show Odd (Nat.card (d.J₀.map L.subtype : Subgroup G))
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact d.odd_card_J₀
  have hJP : jZeroG d ≤ normalizer (P : Set G) := fun x hx =>
    ncs_le_normalizer_yamadaP h d hlay
      ⟨Setup.J₀_map_le_centralizer h d hx, Setup.J₀_map_le_normalizer_S d hx⟩
  have hJcLV : jZeroG d ≤ cLV d := by
    unfold jZeroG cLV
    exact Subgroup.map_mono (d.J₀_le_J₆.trans inf_le_right)
  have hJnOne : jZeroG d ≤ nOne d t := hJcLV.trans (cLV_le_nOne h d hp)
  have hJK₁ : jZeroG d ≤ normalizer (K₁ : Set G) := fun x hx =>
    nOne_le_normalizer hK₁ (hJnOne hx)
  have hJQ' : jZeroG d ≤ normalizer (Q₁ : Set G) := fun x hx =>
    mem_normalizer_inf (hJP hx) (mem_normalizer_commutator_self (hJK₁ hx))
  obtain ⟨hT5Y, -, -, -, -, -, hT5P, -, -, -, hT5X, -⟩ := hT5
  have hJY : jZeroG d ≤ normalizer (Y : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 (hT5Y hy) x hx).symm)
  have hJK₄ : jZeroG d ≤ normalizer (K₄ : Set G) := fun x hx =>
    (hN1norm (mem_inf.2 ⟨hJnOne hx, hJP hx⟩)).2
  have hJK₅ : jZeroG d ≤ normalizer (K₅ : Set G) := fun x hx => by
    rw [hK₅eq]
    exact mem_normalizer_sup (mem_normalizer_commutator_self (hJK₄ hx)) (hJY hx)
  have hJO₅ : jZeroG d ≤ normalizer (pCoreOf 2 K₅ : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₅ (hJK₅ hx)
  have hPO₅ : P ≤ normalizer (pCoreOf 2 K₅ : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₅ (hNK₅ (hPN hx))
  have hJM : ∀ s ∈ jZeroG d, s ∈ normalizer (M : Set G) := fun s hs => hB1b.2.2 (hJP hs)
  have hPJ : ∀ x ∈ P, ∀ s ∈ jZeroG d, x * s * x⁻¹ * s⁻¹ ∈ M := fun x hx s hs =>
    (mem_centralizerMod_iff.1 (hT5P hx)).2 s hs (hJM s hs)
  have hPC : P ⊓ centralizer ((jZeroG d : Subgroup G) : Set G) ≤ X₀ := hT5X.le
  have hX₀N₃ : X₀ ≤ N₃ := by rw [hNX]; exact le_sup_left
  have hX₀P : X₀ ≤ P := by rw [hPM]; exact le_sup_right
  have hX₀M : X₀ ≤ normalizer (M : Set G) := hX₀P.trans (hPN.trans hNM)
  have hYX₀ : Y ≤ X₀ := by rw [hXY]; exact le_sup_left
  have hN₃MX : N₃ ⊓ M ≤ X₀ := by rw [hN3M]; exact hYX₀
  have hK₃N₃ : K₃ ≤ N₃ := by rw [hNK]; exact le_sup_left
  have hK₃K : K₃ ≤ K := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact hx.1.1
  have hPK₃ : P ⊓ K₃ = Q₃ := P_inf_K₃ hPM hX₀N₃ hX₀M hN₃MX hK₃N₃ hK₃K rfl hQ₃K₃
  have hO₅P : pCoreOf 2 K₅ ≤ P := by
    rw [c5]; exact sup_le (inf_le_left.trans hQ₁P) hYP
  have hK₃K₅ : K₃ ≤ K₅ := by rw [c6]; exact le_sup_left
  have hK₃O : K₃ ≤ normalizer (pCoreOf 2 K₅ : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₅ (hK₃K₅ hx)
  have hk := P_inf_K₅ c6 hO₅P hK₃O hPK₃
  have hl := part3_l (t := t) c5 hQ₃Q₁ hQ₁P hYP hYX₀ (hYW.trans hWM) hQN hXQ hcommQ
    (by rw [hQQV]; exact Setup.yamadaV₁_le_yamadaY₂ d) hP2 hJodd hJQ' hJY hJO₅ hPO₅ hPJ hPC
  refine ⟨⟨c4.symm, c2, ?_, hSec, hfixN, hK₅eq, hNK₅⟩, ⟨c6, c7, c5⟩, ⟨hk, hl⟩⟩
  exact Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]; exact c3 x hx y hy

end G1Assembly

end Y8_G1c

section Y8_G2a

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (bar proj Bar)
open scoped MatrixGroups commutatorElement Pointwise

section G2a

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem PK₃_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    yamadaP d t ⊓ kThree d t K = qThree d t K := by
  obtain ⟨⟨hXY, hXSyl, hXcard⟩, ⟨hXQ, hQQt, hQQc, hQSyl, hQcard⟩, -⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩,
    ⟨hNX, hlev, hNM, v₁, hv₁K, hv₁eq, hv₁Q⟩, ⟨hN3M, hN2M, hPM, hPSyl, hMJ⟩⟩ :=
    A3_structure h d hp hK
  obtain ⟨-, hB1b⟩ := B1_decomposition h d hp hK
  have hX₀N₃ : prodX d t ≤ nThree d t := by rw [hNX]; exact le_sup_left
  have hX₀P : prodX d t ≤ yamadaP d t := by rw [hPM]; exact le_sup_right
  have hX₀M : prodX d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) :=
    hX₀P.trans (Subgroup.le_normalizer.trans hB1b.2.2)
  have hYX₀ : yamadaY₂ d t ≤ prodX d t := by rw [hXY]; exact le_sup_left
  have hN₃MX : nThree d t ⊓ yamadaM₆ d t ≤ prodX d t := by rw [hN3M]; exact hYX₀
  have hK₃N₃ : kThree d t K ≤ nThree d t := by rw [hNK]; exact le_sup_left
  have hK₃K : kThree d t K ≤ K := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact hx.1.1
  exact P_inf_K₃ hPM hX₀N₃ hX₀M hN₃MX hK₃N₃ hK₃K rfl (qThree_le_kThree h d hp hK)

theorem v_action (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kThree d t K = qThree d t K ⊔ (qThree d t K)ᵍ[vG d] ∧
      qThree d t K ⊓ (qThree d t K)ᵍ[vG d] = eOne d t K ∧
      (kThree d t K)ᵍ[vG d] = kThree d t K ∧ (eOne d t K)ᵍ[vG d] = eOne d t K ∧
      zc (qThree d t K) ⊓ (zc (qThree d t K))ᵍ[vG d] = ⊥ := by
  have htt : t * t = 1 := h.t_mul_t
  obtain ⟨-, ⟨hXQ, hQQt, hQQc, hQSyl, hQcard⟩, ⟨hYE, hEEt, hEel, hEcard, hEQ, hEQn, hEcoat⟩⟩ :=
    A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩,
    ⟨hNX, hlev, hNM, v₁, hv₁K, hv₁eq, hv₁Q⟩, -⟩ := A3_structure h d hp hK
  have H3 := natSL2_layer h d hp hK
  have hQ₃K₃ := qThree_le_kThree h d hp hK
  have hKK₃t' : ∀ x ∈ kThree d t K, ∀ y ∈ (kThree d t K)ᵍ[t], x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hKK₃c hx) y hy).symm
  have hw₁ : t⁻¹ * v₁ * t ∈ (kThree d t K)ᵍ[t] := by
    rw [mem_conj_iff]
    have e : t * (t⁻¹ * v₁ * t) * t⁻¹ = v₁ := by group
    rw [e]; exact hv₁K
  have hpt : ∀ q ∈ kThree d t K, (vG d)⁻¹ * q * vG d = v₁⁻¹ * q * v₁ := by
    intro q hq
    have hc := hKK₃t' (v₁⁻¹ * q * v₁)
      ((kThree d t K).mul_mem ((kThree d t K).mul_mem ((kThree d t K).inv_mem hv₁K) hq) hv₁K) _ hw₁
    rw [hv₁eq]
    calc (v₁ * (t⁻¹ * v₁ * t))⁻¹ * q * (v₁ * (t⁻¹ * v₁ * t))
        = (t⁻¹ * v₁ * t)⁻¹ * (v₁⁻¹ * q * v₁) * (t⁻¹ * v₁ * t) := by group
      _ = (t⁻¹ * v₁ * t)⁻¹ * ((t⁻¹ * v₁ * t) * (v₁⁻¹ * q * v₁)) := by rw [← hc]; group
      _ = v₁⁻¹ * q * v₁ := by group
  have hconj : ∀ A : Subgroup G, A ≤ kThree d t K →
      Aᵍ[vG d] = A.map (MulEquiv.toMonoidHom (MulAut.conj v₁⁻¹)) := by
    intro A hA
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, (hpt q (hA hq)).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, hpt q (hA hq)⟩
  have hK₃N : kThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) := by
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kThree d t K)
    rwa [hOK₃] at this
  have hK₃sup : kThree d t K = qThree d t K ⊔ (qThree d t K)ᵍ[vG d] := by
    rw [hconj _ hQ₃K₃]; exact (H3.sup_conj hv₁K hv₁Q).symm
  have hinf : qThree d t K ⊓ (qThree d t K)ᵍ[vG d] = eOne d t K := by
    rw [hconj _ hQ₃K₃]; exact H3.inf_conj hv₁K hv₁Q
  have hKv : (kThree d t K)ᵍ[vG d] = kThree d t K := by
    rw [hconj _ le_rfl]
    exact conj_eq_of_mem_normalizer (Subgroup.le_normalizer hv₁K)
  have hEv : (eOne d t K)ᵍ[vG d] = eOne d t K := by
    rw [hconj _ hEK₃]
    exact conj_eq_of_mem_normalizer (hK₃N hv₁K)
  refine ⟨hK₃sup, hinf, hKv, hEv, ?_⟩
  obtain ⟨⟨hZE, hZcard, hVZ, hZZt⟩, -, -⟩ := A4_u_component h d hp hK
  have hZE₁ : zc (qThree d t K) ≤ eOne d t K := by rw [hZE]; exact inf_le_left
  have hZK₃ : zc (qThree d t K) ≤ kThree d t K := hZE₁.trans hEK₃
  rw [eq_bot_iff]
  intro z ⟨hz1, hz2⟩
  have hz2' : v₁ * z * v₁⁻¹ ∈ zc (qThree d t K) := by
    rw [hconj _ hZK₃] at hz2
    obtain ⟨y, hy, hyz⟩ := hz2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyz
    rw [← hyz]
    simpa [mul_assoc] using hy
  have hzK : z ∈ centralizer ((kThree d t K : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    rw [hK₃sup] at hk
    have hQ : ∀ q ∈ qThree d t K, q * z = z * q := fun q hq =>
      mem_centralizer_iff.1 hz1.2 q hq
    have hQv : ∀ q ∈ (qThree d t K)ᵍ[vG d], q * z = z * q := by
      intro q hq
      rw [hconj _ hQ₃K₃] at hq
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have hc : q₀ * (v₁ * z * v₁⁻¹) = (v₁ * z * v₁⁻¹) * q₀ :=
        mem_centralizer_iff.1 hz2'.2 q₀ hq₀
      calc v₁⁻¹ * q₀ * v₁ * z = v₁⁻¹ * (q₀ * (v₁ * z * v₁⁻¹)) * v₁ := by group
        _ = v₁⁻¹ * ((v₁ * z * v₁⁻¹) * q₀) * v₁ := by rw [hc]
        _ = z * (v₁⁻¹ * q₀ * v₁) := by group
    have hcent : (qThree d t K ⊔ (qThree d t K)ᵍ[vG d]) ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun q hq => ?_) (fun q hq => ?_)
      · rw [mem_centralizer_singleton_iff]; exact hQ q hq
      · rw [mem_centralizer_singleton_iff]; exact hQv q hq
    have := mem_centralizer_singleton_iff.1 (hcent hk)
    exact this
  have hzE : z ∈ eOne d t K := hZE₁ hz1
  have := H3.inf_centralizer_eq_bot
  have hz0 : z ∈ eOne d t K ⊓ centralizer ((kThree d t K : Subgroup G) : Set G) := ⟨hzE, hzK⟩
  rw [this] at hz0
  exact hz0

end G2a

end Y8_G2a

section Y8_G2

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (bar proj Bar)
open scoped MatrixGroups commutatorElement Pointwise

section G2Aux

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have h1 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := A.subgroupOf N ⊔ B.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := A.subgroupOf N) (K := B.subgroupOf N)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hc _ (sup_le hAN hB), hc A hAN] at h1
  rw [hinf, hc _ (inf_le_left.trans hAN), hc B hB] at h2
  rw [← h1, ← h2]
  ring

theorem commutator_normalized (H₁ H₂ : Subgroup G) :
    H₁ ⊔ H₂ ≤ normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  have hle : ⁅H₁, H₂⁆ ≤ H₁ ⊔ H₂ := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))
      (inv_mem (Subgroup.mem_sup_left ha))) (inv_mem (Subgroup.mem_sup_right hb))
  have : (⁅H₁, H₂⁆.subgroupOf (H₁ ⊔ H₂)).Normal := inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 this

theorem commute_conj_elems {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (g : G) :
    ∀ a ∈ Aᵍ[g], ∀ b ∈ Bᵍ[g], a * b = b * a := by
  intro a ha b hb
  have ha' : g * a * g⁻¹ ∈ A := mem_conj_iff.1 ha
  have hb' : g * b * g⁻¹ ∈ B := mem_conj_iff.1 hb
  have := h _ ha' _ hb'
  calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [this]
    _ = b * a := by group

theorem conj_conj_comm {a b : G} (hab : a * b = b * a) (A : Subgroup G) :
    (Aᵍ[a])ᵍ[b] = (Aᵍ[b])ᵍ[a] := by
  ext y
  rw [mem_conj_iff, mem_conj_iff, mem_conj_iff, mem_conj_iff]
  have e : a * (b * y * b⁻¹) * a⁻¹ = b * (a * y * a⁻¹) * b⁻¹ := by
    calc a * (b * y * b⁻¹) * a⁻¹ = (a * b) * y * (a * b)⁻¹ := by group
      _ = (b * a) * y * (b * a)⁻¹ := by rw [hab]
      _ = b * (a * y * a⁻¹) * b⁻¹ := by group
  rw [e]

theorem TI_mod {Q₃ Q₃v M K₃ E₁ : Subgroup G} (hQ₃N : Q₃ ≤ normalizer (M : Set G))
    (hQ₃vN : Q₃v ≤ normalizer (M : Set G)) (hQ₃K : Q₃ ≤ K₃) (hQ₃vK : Q₃v ≤ K₃)
    (hK₃M : K₃ ⊓ M ≤ E₁) (hE₁Q : E₁ ≤ Q₃) (hE₁M : E₁ ≤ M) (hTI : Q₃ ⊓ Q₃v ≤ E₁) :
    (Q₃ ⊔ M) ⊓ (Q₃v ⊔ M) ≤ M := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨q, hq, m, hm, rfl⟩ := mem_sup_of_le_normalizer hQ₃N hx1
  obtain ⟨q', hq', m', hm', hxe⟩ := mem_sup_of_le_normalizer hQ₃vN hx2
  have he : q'⁻¹ * q ∈ K₃ ⊓ M := by
    refine ⟨K₃.mul_mem (K₃.inv_mem (hQ₃vK hq')) (hQ₃K hq), ?_⟩
    have h1 : q'⁻¹ * q = m' * m⁻¹ := by
      calc q'⁻¹ * q = q'⁻¹ * (q * m) * m⁻¹ := by group
        _ = q'⁻¹ * (q' * m') * m⁻¹ := by rw [hxe]
        _ = m' * m⁻¹ := by group
    rw [h1]
    exact M.mul_mem hm' (M.inv_mem hm)
  have he' := hK₃M he
  have hq'Q : q' ∈ Q₃ := by
    have : q' = q * (q'⁻¹ * q)⁻¹ := by group
    rw [this]
    exact Q₃.mul_mem hq (Q₃.inv_mem (hE₁Q he'))
  have hq'E := hTI ⟨hq'Q, hq'⟩
  have hqE : q ∈ E₁ := by
    have : q = q' * (q'⁻¹ * q) := by group
    rw [this]
    exact E₁.mul_mem hq'E he'
  exact M.mul_mem (hE₁M hqE) hm

theorem inter_E_V {E E' Z Z' Zv Z'v : Subgroup G} (hZE : Z ≤ E) (hZvE : Zv ≤ E)
    (hZ'E' : Z' ≤ E') (hZ'vE' : Z'v ≤ E') (hEE' : E ⊓ E' = ⊥)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) (hZ'inf : Z' ⊓ Z'v = ⊥) :
    (E ⊔ (Z ⊔ Z')) ⊓ (E ⊔ (Zv ⊔ Z'v)) ≤ E := by
  have e1 : E ⊔ (Z ⊔ Z') = E ⊔ Z' := by
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le (hZE.trans le_sup_left) le_sup_right)
    · exact sup_le_sup_left le_sup_right E
  have e2 : E ⊔ (Zv ⊔ Z'v) = E ⊔ Z'v := by
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le (hZvE.trans le_sup_left) le_sup_right)
    · exact sup_le_sup_left le_sup_right E
  rintro x ⟨hx1, hx2⟩
  rw [e1] at hx1
  rw [e2] at hx2
  obtain ⟨e, he, a, ha, rfl⟩ := mem_sup_of_commute'
    (fun c hc y hy => (hcomm y hy c (hZ'E' hc)).symm) hx1
  obtain ⟨e', he', b, hb, hxe⟩ := mem_sup_of_commute'
    (fun c hc y hy => (hcomm y hy c (hZ'vE' hc)).symm) hx2
  have h1 : e'⁻¹ * e = b * a⁻¹ := by
    calc e'⁻¹ * e = e'⁻¹ * (e * a) * a⁻¹ := by group
      _ = e'⁻¹ * (e' * b) * a⁻¹ := by rw [hxe]
      _ = b * a⁻¹ := by group
  have hmem : e'⁻¹ * e ∈ E ⊓ E' := by
    refine ⟨E.mul_mem (E.inv_mem he') he, ?_⟩
    rw [h1]
    exact E'.mul_mem (hZ'vE' hb) (E'.inv_mem (hZ'E' ha))
  rw [hEE', mem_bot] at hmem
  have hba : b = a := by
    have h2 : b * a⁻¹ = 1 := by rw [← h1]; exact hmem
    exact mul_inv_eq_one.1 h2
  have ha1 : a ∈ Z' ⊓ Z'v := ⟨ha, hba ▸ hb⟩
  rw [hZ'inf, mem_bot] at ha1
  rw [ha1, mul_one]
  exact he

theorem inf_Y_eq {Q Qt Z Z' Y : Subgroup G} (hZQ : Z ≤ Q) (hZ'Qt : Z' ≤ Qt) (hY : Y = Z ⊔ Z')
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Qt, x * y = y * x) (hQQt : Q ⊓ Qt ≤ Z) : Q ⊓ Y = Z := by
  apply le_antisymm
  · rintro y ⟨hyQ, hyY⟩
    rw [hY] at hyY
    obtain ⟨z, hz, z', hz', rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => (hcomm a (hZQ ha) c (hZ'Qt hc)).symm) hyY
    have hz'Q : z' ∈ Q ⊓ Qt := by
      refine ⟨?_, hZ'Qt hz'⟩
      have := Q.mul_mem (Q.inv_mem (hZQ hz)) hyQ
      simpa using this
    have := Z.mul_mem hz (hQQt hz'Q)
    exact this
  · exact le_inf hZQ (hY ▸ le_sup_left)

theorem eq_sup_of_index {O U U' X E' Y : Subgroup G} {q : ℕ} (hq : 0 < q)
    (hUO : U ≤ O) (hU'O : U' ≤ O) (hXU : X = U ⊓ U') (hOU : O = U ⊔ Y) (hOU' : O = U' ⊔ Y)
    (hUY : U ≤ normalizer (Y : Set G)) (hU'Y : U' ≤ normalizer (Y : Set G))
    (hYcard : Nat.card Y = q ^ 4) (hUYcard : Nat.card (U ⊓ Y : Subgroup G) = q ^ 3)
    (hU'Ycard : Nat.card (U' ⊓ Y : Subgroup G) = q ^ 3) (hE'O : E' ≤ O)
    (hXE' : ∀ x ∈ X, ∀ e ∈ E', x * e = e * x) (hXE'inf : X ⊓ E' = ⊥)
    (hE'card : Nat.card E' = q ^ 2) : O = X ⊔ E' := by
  have hindex : ∀ V : Subgroup G, V ≤ O → O = V ⊔ Y → V ≤ normalizer (Y : Set G) →
      Nat.card (V ⊓ Y : Subgroup G) = q ^ 3 → V.relIndex O = q := by
    intro V hVO hOV hVY hVYcard
    have h1 := card_sup_mul_card_inf_of_le_normalizer' hVY
    have h1' : Nat.card O * Nat.card (V ⊓ Y : Subgroup G) = Nat.card V * Nat.card Y := by
      have := card_sup_mul_card_inf_of_le_normalizer' (A := Y) (B := V) hVY
      rw [sup_comm, ← hOV, inf_comm] at this
      rw [this]
      ring
    rw [hVYcard, hYcard] at h1'
    have h2 := Subgroup.relIndex_mul_card (H := V) (K := O)
    rw [inf_eq_left.2 hVO] at h2
    have hVpos : 0 < Nat.card V := Nat.card_pos
    have h3 : 0 < q ^ 3 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hVpos
    apply Nat.eq_of_mul_eq_mul_right h3
    calc V.relIndex O * Nat.card V * q ^ 3 = Nat.card O * q ^ 3 := by rw [h2]
      _ = Nat.card V * q ^ 4 := h1'
      _ = q * Nat.card V * q ^ 3 := by ring
  have hU := hindex U hUO hOU hUY hUYcard
  have hU' := hindex U' hU'O hOU' hU'Y hU'Ycard
  have hXO : X ≤ O := by rw [hXU]; exact inf_le_left.trans hUO
  have hX : X.relIndex O ≤ q * q := by
    have := Subgroup.relIndex_inf_le (H := U) (K := U') (L := O)
    rw [← hXU, hU, hU'] at this
    exact this
  have hXcard := Subgroup.relIndex_mul_card (H := X) (K := O)
  rw [inf_eq_left.2 hXO] at hXcard
  have hcardsup : Nat.card (X ⊔ E' : Subgroup G) * Nat.card (X ⊓ E' : Subgroup G) =
      Nat.card X * Nat.card E' := card_sup_mul_card_inf_of_commute' X E' hXE'
  rw [hXE'inf, Subgroup.card_bot, mul_one, hE'card] at hcardsup
  have hsupO : X ⊔ E' ≤ O := sup_le hXO hE'O
  refine (Subgroup.eq_of_le_of_card_ge hsupO ?_).symm
  rw [hcardsup, ← hXcard]
  calc X.relIndex O * Nat.card X ≤ (q * q) * Nat.card X := Nat.mul_le_mul_right _ hX
    _ = Nat.card X * q ^ 2 := by ring

theorem X_eq_sup_commutator {O X E E' Y J : Subgroup G}
    (hO : O = X ⊔ E') (hXE' : ∀ x ∈ X, ∀ e ∈ E', x * e = e * x) (hE'Y : E' ≤ Y)
    (hYJ : ∀ y ∈ Y, ∀ j ∈ J, j * y = y * j) (hJX : J ≤ normalizer (X : Set G))
    (hJO : J ≤ normalizer (O : Set G)) (hO2 : IsPGroup 2 O) (hJodd : Odd (Nat.card J))
    (hC : O ⊓ centralizer (J : Set G) ≤ Y) (hEX : E ≤ X) (hXY : X ⊓ Y ≤ E) :
    X = E ⊔ ⁅O, J⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := ⁅O, J⁆ with hA
  have hAO : A ≤ O := Subgroup.le_normalizer_iff_commutator_le_left.1 hJO
  have hXO : X ≤ O := by rw [hO]; exact le_sup_left
  have hAX : A ≤ X := by
    refine Subgroup.commutator_le.2 fun o ho j hj => ?_
    rw [hO] at ho
    obtain ⟨x, hx, z, hz, rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => (hXE' a ha c hc).symm) ho
    have hzj : j * z = z * j := hYJ z (hE'Y hz) j hj
    have e : ⁅x * z, j⁆ = x * (j * x⁻¹ * j⁻¹) := by
      rw [commutatorElement_def]
      calc x * z * j * (x * z)⁻¹ * j⁻¹ = x * (z * j * z⁻¹) * x⁻¹ * j⁻¹ := by group
        _ = x * (j * z * z⁻¹) * x⁻¹ * j⁻¹ := by rw [hzj]
        _ = x * (j * x⁻¹ * j⁻¹) := by group
    rw [e]
    exact X.mul_mem hx ((mem_normalizer_iff.1 (hJX hj) x⁻¹).1 (X.inv_mem hx))
  have hAn : O ⊔ J ≤ normalizer (A : Set G) := commutator_normalized O J
  have hsolv : Group.IsSolvable O := by
    haveI := hO2.isNilpotent
    infer_instance
  have hcop : (Nat.card J).Coprime (Nat.card O) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hO2
    rw [hk]
    exact (Nat.coprime_two_right.2 hJodd).pow_right k
  apply le_antisymm
  · intro x hx
    have hfix : ∀ s ∈ J, x⁻¹ * (s * x * s⁻¹) ∈ A := by
      intro s hs
      have := Subgroup.commutator_mem_commutator (O.inv_mem (hXO hx)) hs
      rw [commutatorElement_def] at this
      simpa [mul_assoc] using this
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hAO
      (le_sup_left.trans hAn) hJO (le_sup_right.trans hAn) hsolv hcop (hXO hx) hfix
    have hcX : c ∈ X := by
      have := X.mul_mem hx (X.inv_mem (hAX hn))
      simpa using this
    exact mul_mem (hXY ⟨hcX, hC hc⟩ |> Subgroup.mem_sup_left) (Subgroup.mem_sup_right hn)
  · exact sup_le hEX hAX

theorem mem_normalizer_commutator_of_centralizes {O J : Subgroup G} {k : G}
    (hkO : k ∈ normalizer (O : Set G)) (hkJ : ∀ j ∈ J, k * j = j * k) :
    k ∈ normalizer ((⁅O, J⁆ : Subgroup G) : Set G) := by
  have hkJ' : k ∈ normalizer (J : Set G) :=
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj => (hkJ j hj).symm)
  exact mem_normalizer_of_conj_eq (by
    rw [conj_commutator, conj_eq_of_mem_normalizer hkO, conj_eq_of_mem_normalizer hkJ'])

theorem commutator_eq_bot_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ⁅A, B⁆ = ⊥ :=
  commutator_eq_bot_iff_le_centralizer.2 fun a ha => mem_centralizer_iff.2 fun b hb =>
    (h a ha b hb).symm

theorem Q_eq_sup {Q P₀ E E' Z Z' Y : Subgroup G} (hQ : Q ⊔ Y = P₀ ⊔ E') (hP₀Q : P₀ ≤ Q)
    (hcomm : ∀ p ∈ P₀, ∀ e ∈ E', p * e = e * p) (hQY : Q ⊓ Y = E ⊔ (Z ⊔ Z'))
    (hZE : Z ≤ E) (hZ'E' : Z' ≤ E') (hEE' : E ⊓ E' = ⊥)
    (hEE'c : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) (hE'Y : E' ≤ Y) (hZ'Q : Z' ≤ Q) :
    Q = P₀ ⊔ Z' := by
  apply le_antisymm
  · intro q hq
    have hq' : q ∈ P₀ ⊔ E' := hQ ▸ (le_sup_left : Q ≤ Q ⊔ Y) hq
    obtain ⟨p, hp, e, he, rfl⟩ := mem_sup_of_commute'
      (fun c hc a ha => (hcomm a ha c hc).symm) hq'
    have heQ : e ∈ Q ⊓ Y := by
      refine ⟨?_, hE'Y he⟩
      have := Q.mul_mem (Q.inv_mem (hP₀Q hp)) hq
      simpa using this
    rw [hQY] at heQ
    have e1 : E ⊔ (Z ⊔ Z') = E ⊔ Z' := by
      apply le_antisymm
      · exact sup_le le_sup_left (sup_le (hZE.trans le_sup_left) le_sup_right)
      · exact sup_le_sup_left le_sup_right E
    rw [e1] at heQ
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute'
      (fun c hc y hy => (hEE'c y hy c (hZ'E' hc)).symm) heQ
    have haE' : a ∈ E ⊓ E' := by
      refine ⟨ha, ?_⟩
      have : a = e * b⁻¹ := by rw [hab]; group
      rw [this]
      exact E'.mul_mem he (E'.inv_mem (hZ'E' hb))
    rw [hEE', mem_bot] at haE'
    have heb : e = b := by rw [hab, haE', one_mul]
    exact mul_mem (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right (heb ▸ hb))
  · exact sup_le hP₀Q hZ'Q

end G2Aux

section G2Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem G2_aux (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (xQ d t K₁ ≤ yamadaM₆ d t ∧ xQ d t K₁ ⊓ yamadaY₂ d t = eOne d t K ∧
      pCoreOf 2 (kFive d t K) = xQ d t K₁ ⊔ (eOne d t K)ᵍ[t] ∧
      xQ d t K₁ ⊓ (eOne d t K)ᵍ[t] = ⊥ ∧ ⁅xQ d t K₁, (eOne d t K)ᵍ[t]⁆ = ⊥ ∧
      ⁅xQ d t K₁, (kThree d t K)ᵍ[t]⁆ = ⊥) ∧
    (qOne d t K₁ ⊔ yamadaY₂ d t = pZero d t K K₁ ⊔ (eOne d t K)ᵍ[t] ∧
      pZero d t K K₁ ⊓ (eOne d t K)ᵍ[t] = ⊥ ∧ ⁅pZero d t K K₁, (eOne d t K)ᵍ[t]⁆ = ⊥ ∧
      qOne d t K₁ = pZero d t K K₁ ⊔ (zc (qThree d t K))ᵍ[t] ∧
      pZero d t K K₁ ⊓ (zc (qThree d t K))ᵍ[t] = ⊥ ∧
      ⁅pZero d t K K₁, (zc (qThree d t K))ᵍ[t]⁆ = ⊥) := by
  have hlay := hp.layer
  have hK : IsLayerComponent d t K := hL.comp
  have hK₁ : IsN1Factor d t K₁ := hL.factor
  have htt : t * t = 1 := h.t_mul_t
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hXY, hXSyl, hXcard⟩, ⟨hXQ, hQQt, hQQc, hQSyl, hQcard⟩,
    ⟨hYE, hEEt, hEel, hEcard, hEQ, hEQn, hEcoat⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hEK₃, hOK₃, hK₃iso, hK₃Z, hNK, hKK₃t, hKK₃c, hN3iso⟩,
    ⟨hNX, hlev, hNM, v₁, hv₁K, hv₁eq, hv₁Q⟩, ⟨hN3M, hN2M, hPM, hPSyl, hMJ⟩⟩ :=
    A3_structure h d hp hK
  obtain ⟨⟨hZE, hZcard, hVZ, hZZt⟩, hKu, hQu⟩ := A4_u_component h d hp hK
  obtain ⟨-, hB1b⟩ := B1_decomposition h d hp hK
  obtain ⟨⟨hPQ, hQQV, hQQc', hD1, hD2, hD3⟩, hZser, hRdec, hF4⟩ := F0_sylow h d hp hK hK₁
  obtain ⟨⟨hN1norm, hN2norm⟩, hRQO, hlabel⟩ := F1_normalizers h d hp hK hK₁
  obtain ⟨⟨hF4a, hF4b, hF4c, hF4d⟩, hF2b⟩ := F2_auxiliary h d hp hL
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  have hT5 := T5_J₀ h d hp
  have hG0 := G0_aux h d hp hL
  obtain ⟨⟨hG1a, hG1b, hG1c, hG1d, hG1e, hG1f, hG1g⟩, ⟨hG1h, hG1i, hG1j⟩, ⟨hG1k, hG1l⟩⟩ :=
    G1_aux h d hp hL
  obtain ⟨hK₃sup, hTI, hKv, hEv, hZinf⟩ := v_action h d hp hK
  have H3 := natSL2_layer h d hp hK
  have hcardYV := card_Y₂_V₁ h d hp hK
  have hcommQ := qOne_comm h d hp hK₁
  obtain ⟨⟨hV₁K₁', hV₁Z⟩, hE3b⟩ := E3_commutators h d hp hK₁
  have hQ₃K₃ := qThree_le_kThree h d hp hK
  have hEcomm := eOne_comm h d hp hK
  have hPK₃ := PK₃_eq h d hp hK
  set Y := yamadaY₂ d t with hYdef
  set W := yamadaW₃ d t with hWdef
  set M := yamadaM₆ d t with hMdef
  set P := yamadaP d t with hPdef
  set N := nTwo d t with hNdef
  set N₃ := nThree d t with hN₃def
  set K₃ := kThree d t K with hK₃def
  set K₅ := kFive d t K with hK₅def
  set Q₁ := qOne d t K₁ with hQ₁def
  set Q₃ := qThree d t K with hQ₃def
  set E₁ := eOne d t K with hE₁def
  set V₁ := yamadaV₁ d t with hV₁def
  set X := xQ d t K₁ with hXdef
  set Z := zc Q₃ with hZdef
  set O₅ := pCoreOf 2 K₅ with hO₅def
  have hQ₃Q₁ : Q₃ ≤ Q₁ := hG0.2.2
  have hE₁Q₁ : E₁ ≤ Q₁ := hG0.2.1
  have hP2 : IsPGroup 2 P := hPSyl.isPGroup
  have hPN : P ≤ N := hPSyl.le
  have hPY : P ≤ normalizer (Y : Set G) := by
    have := normalizer_le_normalizer_series P 2
    rw [hZ2] at this
    exact Subgroup.le_normalizer.trans this
  have hMP : M ≤ P := yamadaM₆_le_yamadaP d t
  have hMY : M ≤ normalizer (Y : Set G) := hMP.trans hPY
  have hYN₃ : Y ≤ N₃ := by rw [← hN3M]; exact inf_le_left
  have hN₃Y : N₃ ≤ normalizer (Y : Set G) := by
    obtain ⟨φ, -, hker⟩ := hN3iso
    have : (Y.subgroupOf N₃).Normal := hker ▸ MonoidHom.normal_ker φ
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYN₃).1 this
  have hN₃N : N₃ ≤ N := le_sup_left
  have hNY : N ≤ normalizer (Y : Set G) := sup_le hN₃Y hMY
  have hYP : Y ≤ P := by rw [← hZ2]; exact Subgroup.map_subtype_le _
  have hYW : Y ≤ W := by
    rw [← hZ2, ← hZ3]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hWP : W ≤ P := by rw [← hZ3]; exact Subgroup.map_subtype_le _
  have hQ₁P : Q₁ ≤ P := inf_le_left
  have hvN₃ : vG d ∈ N₃ := hlev ⟨d.v, d.v_mem_leviLong, rfl⟩
  have hvt : t * vG d = vG d * t := by
    have : ((d.v : L) : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.v : L).2
    exact (mem_centralizer_singleton_iff.1 this).symm
  set v := vG d with hvdef
  have hvY : v ∈ normalizer (Y : Set G) := hN₃Y hvN₃
  have hvM : v ∈ normalizer (M : Set G) := hNM hvN₃
  have hYv : Yᵍ[v] = Y := conj_eq_of_mem_normalizer hvY
  have hMv : Mᵍ[v] = M := conj_eq_of_mem_normalizer hvM
  have hK₅N : N ≤ normalizer (K₅ : Set G) := hG1g
  have hvO₅ : v ∈ normalizer (O₅ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₅ (hK₅N (hN₃N hvN₃))
  have hO₅v : O₅ᵍ[v] = O₅ := conj_eq_of_mem_normalizer hvO₅
  have hYM : Y ≤ M := by rw [← hN3M]; exact inf_le_right
  have hK₃N₃ : K₃ ≤ N₃ := by rw [hNK]; exact le_sup_left
  have hK₃K : K₃ ≤ K := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact hx.1.1
  have hK₃M : K₃ ≤ normalizer (M : Set G) := hK₃N₃.trans hNM
  have hKK₃t' : ∀ x ∈ K₃, ∀ y ∈ K₃ᵍ[t], x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hKK₃c hx) y hy).symm
  have hEEt' : ∀ x ∈ E₁, ∀ y ∈ E₁ᵍ[t], x * y = y * x := fun x hx y hy =>
    hKK₃t' x (hEK₃ hx) y (conj_mono t hEK₃ hy)
  have hZE₁ : Z ≤ E₁ := by rw [hZE]; exact inf_le_left
  have hE₁Y : E₁ ≤ Y := inf_le_left
  have hbS : bSub d t K = Q₃ ⊔ M := by
    show P ⊓ (K₃ ⊔ M) = Q₃ ⊔ M
    rw [inf_comm, dedekind_sup_inf hMP hK₃M, inf_comm, hPK₃]
  have hQ₁B : Q₁ ≤ Q₃ ⊔ M := by
    rw [← hbS, ← hF2b.1]; exact le_sup_left
  have hQ₃vK : Q₃ᵍ[v] ≤ K₃ := by
    have := conj_mono v hQ₃K₃
    rwa [hKv] at this
  have hQ₁vB : Q₁ᵍ[v] ≤ Q₃ᵍ[v] ⊔ M := by
    have := conj_mono v hQ₁B
    rwa [conj_sup, hMv] at this
  have hXQ₁ : X ≤ Q₁ := inf_le_left
  have hXQ₁v : X ≤ Q₁ᵍ[v] := inf_le_right
  have hXM : X ≤ M := by
    have h1 : X ≤ (Q₃ ⊔ M) ⊓ (Q₃ᵍ[v] ⊔ M) := le_inf (hXQ₁.trans hQ₁B) (hXQ₁v.trans hQ₁vB)
    refine h1.trans (TI_mod (hQ₃K₃.trans hK₃M) (hQ₃vK.trans hK₃M) hQ₃K₃ hQ₃vK ?_ hEQ
      (hE₁Y.trans hYM) hTI.le)
    rintro x ⟨hx3, hxM⟩
    have hxY : x ∈ Y := by rw [← hN3M]; exact ⟨hK₃N₃ hx3, hxM⟩
    exact ⟨hxY, hK₃K hx3⟩
  have hNPV₁ : normalizer (P : Set G) ≤ normalizer (V₁ : Set G) := by
    have := normalizer_le_normalizer_series P 1
    rwa [hZ1] at this
  have htP : t ∈ normalizer (P : Set G) := h.t_mem_normalizer_yamadaP d hlay
  have htV₁ : t ∈ normalizer (V₁ : Set G) := hNPV₁ htP
  have hV₁t : V₁ᵍ[t] = V₁ := conj_eq_of_mem_normalizer htV₁
  have hV₁P : V₁ ≤ P := by rw [← hZ1]; exact Subgroup.map_subtype_le _
  have hV₁Q₁ : V₁ ≤ Q₁ := le_inf hV₁P hV₁K₁'
  have hV₁Q₁t : V₁ ≤ Q₁ᵍ[t] := by
    have := conj_mono t hV₁Q₁
    rwa [hV₁t] at this
  have hQ₁Y : Q₁ ⊓ Y = E₁ ⊔ V₁ := by
    have := inf_Y_eq (Q := Q₁) (Qt := Q₁ᵍ[t]) (Z := centerMod V₁ Q₁)
      (Z' := centerMod V₁ (Q₁ᵍ[t])) (Y := Y)
      (fun x hx => ((mem_centerMod_iff hV₁Q₁).1 hx).1)
      (fun x hx => ((mem_centerMod_iff hV₁Q₁t).1 hx).1) hZser.1 hcommQ (by
        rw [hQQV]
        unfold centerMod upperCenterMod
        exact NormalizerQuotient.le_lift _)
    rw [this, hG0.1]
  have hvt' : t * v = v * t := hvt
  have hE₁tv : (E₁ᵍ[t])ᵍ[v] = E₁ᵍ[t] := by rw [conj_conj_comm hvt', hEv]
  have hZtinf : Zᵍ[t] ⊓ (Zᵍ[t])ᵍ[v] = ⊥ := by
    rw [conj_conj_comm hvt', ← conj_inf, hZinf, Subgroup.map_bot]
  have hXY : X ⊓ Y = E₁ := by
    apply le_antisymm
    · rintro x ⟨hxX, hxY⟩
      have h1 : x ∈ Q₁ ⊓ Y := ⟨hXQ₁ hxX, hxY⟩
      have h2 : x ∈ Q₁ᵍ[v] ⊓ Y := ⟨hXQ₁v hxX, hxY⟩
      have e1 : Q₁ ⊓ Y = E₁ ⊔ (Z ⊔ Zᵍ[t]) := by rw [hQ₁Y, hVZ]
      have e2 : Q₁ᵍ[v] ⊓ Y = E₁ ⊔ (Zᵍ[v] ⊔ (Zᵍ[t])ᵍ[v]) := by
        calc Q₁ᵍ[v] ⊓ Y = Q₁ᵍ[v] ⊓ Yᵍ[v] := by rw [hYv]
          _ = (Q₁ ⊓ Y)ᵍ[v] := (conj_inf _ _ _).symm
          _ = (E₁ ⊔ V₁)ᵍ[v] := by rw [hQ₁Y]
          _ = E₁ ⊔ (Zᵍ[v] ⊔ (Zᵍ[t])ᵍ[v]) := by rw [conj_sup, hEv, hVZ, conj_sup]
      have hZvE : Zᵍ[v] ≤ E₁ := by
        have := conj_mono v hZE₁
        rwa [hEv] at this
      have hZ'E' : Zᵍ[t] ≤ E₁ᵍ[t] := conj_mono t hZE₁
      have hZ'vE' : (Zᵍ[t])ᵍ[v] ≤ E₁ᵍ[t] := by
        have := conj_mono v hZ'E'
        rwa [hE₁tv] at this
      exact inter_E_V (E := E₁) (E' := E₁ᵍ[t]) hZE₁ hZvE hZ'E' hZ'vE' hEEt hEEt' hZtinf
        ⟨by rw [← e1]; exact h1, by rw [← e2]; exact h2⟩
    · intro x hx
      have hE₁Q₁v : E₁ ≤ Q₁ᵍ[v] := by
        have := conj_mono v hE₁Q₁
        rwa [hEv] at this
      exact ⟨⟨hE₁Q₁ hx, hE₁Q₁v hx⟩, hE₁Y hx⟩
  have hq : 0 < 2 ^ f := by positivity
  have hYO₅ : Y ≤ O₅ := by rw [hG1j]; exact le_sup_right
  have hUO : Q₁ ⊓ M ≤ O₅ := by rw [hG1j]; exact le_sup_left
  have hU'eq : (Q₁ ⊓ M)ᵍ[v] = Q₁ᵍ[v] ⊓ M := by rw [conj_inf, hMv]
  have hXU : X = (Q₁ ⊓ M) ⊓ (Q₁ ⊓ M)ᵍ[v] := by
    rw [hU'eq]
    apply le_antisymm
    · exact le_inf (le_inf hXQ₁ hXM) (le_inf hXQ₁v hXM)
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hU'O : (Q₁ ⊓ M)ᵍ[v] ≤ O₅ := by
    have := conj_mono v hUO
    rwa [hO₅v] at this
  have hOU : O₅ = (Q₁ ⊓ M) ⊔ Y := hG1j
  have hOU' : O₅ = (Q₁ ⊓ M)ᵍ[v] ⊔ Y := by
    calc O₅ = O₅ᵍ[v] := hO₅v.symm
      _ = ((Q₁ ⊓ M) ⊔ Y)ᵍ[v] := by rw [hOU]
      _ = (Q₁ ⊓ M)ᵍ[v] ⊔ Y := by rw [conj_sup, hYv]
  have hUY : Q₁ ⊓ M ≤ normalizer (Y : Set G) := inf_le_left.trans (hQ₁P.trans hPY)
  have hU'Y : (Q₁ ⊓ M)ᵍ[v] ≤ normalizer (Y : Set G) := by
    intro x hx
    have hx' : v * x * v⁻¹ ∈ Q₁ ⊓ M := mem_conj_iff.1 hx
    have h1 := conj_mem_normalizer_conj v (hUY hx')
    have e : v⁻¹ * (v * x * v⁻¹) * v = x := by group
    rw [e, hYv] at h1
    exact h1
  have hYab : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x :=
    mul_comm_of_isMulCommutative_D4 (h.yamada_5_9_2 d hlay).2.2.1
  have hq3 : Nat.card ((Q₁ ⊓ M) ⊓ Y : Subgroup G) = (2 ^ f) ^ 3 := by
    have e : (Q₁ ⊓ M) ⊓ Y = E₁ ⊔ V₁ := by rw [inf_assoc, inf_eq_right.2 hYM, hQ₁Y]
    rw [e]
    have hV₁Y : V₁ ≤ Y := Setup.yamadaV₁_le_yamadaY₂ d
    have hc : ∀ x ∈ E₁, ∀ y ∈ V₁, x * y = y * x := fun x hx y hy =>
      hYab x (hE₁Y hx) y (hV₁Y hy)
    have h1 := card_sup_mul_card_inf_of_commute' E₁ V₁ hc
    rw [← hZE, hZcard, hEcard, hcardYV.2] at h1
    have hpos : 0 < 2 ^ f := hq
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  have hq3' : Nat.card ((Q₁ ⊓ M)ᵍ[v] ⊓ Y : Subgroup G) = (2 ^ f) ^ 3 := by
    have e : (Q₁ ⊓ M)ᵍ[v] ⊓ Y = ((Q₁ ⊓ M) ⊓ Y)ᵍ[v] := by rw [conj_inf (Q₁ ⊓ M) Y v, hYv]
    rw [e, card_conj, hq3]
  have hE₁tY : E₁ᵍ[t] ≤ Y := by rw [hYE]; exact le_sup_right
  have hXE' : ∀ x ∈ X, ∀ e ∈ E₁ᵍ[t], x * e = e * x := fun x hx e he =>
    hcommQ x (hXQ₁ hx) e (conj_mono t hE₁Q₁ he)
  have hXE'inf : X ⊓ E₁ᵍ[t] = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxE⟩
    have : x ∈ E₁ ⊓ E₁ᵍ[t] := ⟨hXY.le ⟨hxX, hE₁tY hxE⟩, hxE⟩
    rwa [hEEt, mem_bot] at this
  have hO₅eq : O₅ = X ⊔ E₁ᵍ[t] :=
    eq_sup_of_index (q := 2 ^ f) hq hUO hU'O hXU hOU hOU' hUY hU'Y hcardYV.1 hq3 hq3'
      (hE₁tY.trans hYO₅) hXE' hXE'inf (by rw [card_conj, hEcard])
  have hvJ : v ∈ normalizer ((jZeroG d : Subgroup G) : Set G) :=
    Setup.coe_mem_normalizer_map d.v_mem_normalizer_J₀
  have hJodd : Odd (Nat.card (jZeroG d : Subgroup G)) := by
    show Odd (Nat.card (d.J₀.map L.subtype : Subgroup G))
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact d.odd_card_J₀
  have hJP : jZeroG d ≤ normalizer (P : Set G) := fun x hx =>
    ncs_le_normalizer_yamadaP h d hlay
      ⟨Setup.J₀_map_le_centralizer h d hx, Setup.J₀_map_le_normalizer_S d hx⟩
  have hJcLV : jZeroG d ≤ cLV d := by
    unfold jZeroG cLV
    exact Subgroup.map_mono (d.J₀_le_J₆.trans inf_le_right)
  have hJnOne : jZeroG d ≤ nOne d t := hJcLV.trans (cLV_le_nOne h d hp)
  have hJK₁ : jZeroG d ≤ normalizer (K₁ : Set G) := fun x hx =>
    nOne_le_normalizer hK₁ (hJnOne hx)
  have hJQ' : jZeroG d ≤ normalizer (Q₁ : Set G) := fun x hx =>
    mem_normalizer_inf (hJP hx) (mem_normalizer_commutator_self (hJK₁ hx))
  obtain ⟨hT5Y, -, -, -, -, -, -, -, -, hT5M, -, -⟩ := hT5
  have hJY : jZeroG d ≤ normalizer (Y : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 (hT5Y hy) x hx).symm)
  have hJK₄ : jZeroG d ≤ normalizer ((kFour d t K : Subgroup G) : Set G) := fun x hx =>
    (hN1norm (mem_inf.2 ⟨hJnOne hx, hJP hx⟩)).2
  have hJK₅ : jZeroG d ≤ normalizer (K₅ : Set G) := fun x hx => by
    rw [hG1f]
    exact mem_normalizer_sup (mem_normalizer_commutator_self (hJK₄ hx)) (hJY hx)
  have hJO₅ : jZeroG d ≤ normalizer (O₅ : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₅ (hJK₅ hx)
  have hJX : jZeroG d ≤ normalizer (X : Set G) := by
    intro j hj
    have h1 : j ∈ normalizer (Q₁ : Set G) := hJQ' hj
    have hvj : v * j * v⁻¹ ∈ jZeroG d := (mem_normalizer_iff.1 hvJ j).1 hj
    have h2 : v⁻¹ * (v * j * v⁻¹) * v ∈ normalizer ((Q₁ᵍ[v] : Subgroup G) : Set G) :=
      conj_mem_normalizer_conj v (hJQ' hvj)
    have e : v⁻¹ * (v * j * v⁻¹) * v = j := by group
    rw [e] at h2
    exact mem_normalizer_inf h1 h2
  have hO₅P : O₅ ≤ P := by rw [hG1j]; exact sup_le (inf_le_left.trans hQ₁P) hYP
  have hO₅M : O₅ ≤ M := by rw [hG1j]; exact sup_le inf_le_right hYM
  have hE₁X : E₁ ≤ X := hXY.ge.trans inf_le_left
  have hXeq : X = E₁ ⊔ ⁅O₅, jZeroG d⁆ :=
    X_eq_sup_commutator (E := E₁) (E' := E₁ᵍ[t]) (Y := Y) hO₅eq hXE' hE₁tY
      (fun y hy j hj => mem_centralizer_iff.1 (hT5Y hy) j hj) hJX hJO₅ (hP2.to_le hO₅P) hJodd
      (fun x hx => hT5M.le ⟨hO₅M hx.1, hx.2⟩) hE₁X hXY.le
  have hK₃K₅ : K₃ ≤ K₅ := (le_sup_left : K₃ ≤ K₃ ⊔ O₅).trans hG1h.ge
  have hK₃E : K₃ ≤ normalizer (E₁ : Set G) := by
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₃
    rwa [hOK₃] at this
  have hK₃X : K₃ ≤ normalizer (X : Set G) := by
    intro k hk
    have hkO₅ : k ∈ normalizer (O₅ : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₅ (hK₃K₅ hk)
    have hkJ : ∀ j ∈ jZeroG d, k * j = j * k := fun j hj =>
      (mem_centralizer_iff.1 (hK.le (hK₃K hk)) j hj).symm
    rw [hXeq]
    exact mem_normalizer_sup (hK₃E hk) (mem_normalizer_commutator_of_centralizes hkO₅ hkJ)
  have hP₀def : pZero d t K K₁ = Q₃ ⊔ X := rfl
  have hP₀Q₁ : pZero d t K K₁ ≤ Q₁ := by rw [hP₀def]; exact sup_le hQ₃Q₁ hXQ₁
  have hP₀Y : pZero d t K K₁ ⊓ Y ≤ E₁ := by
    rintro p ⟨hp1, hpY⟩
    rw [hP₀def] at hp1
    obtain ⟨q, hq, x, hx, rfl⟩ := mem_sup_of_le_normalizer (hQ₃K₃.trans hK₃X) hp1
    have hqM : q ∈ M := by
      have : q = (q * x) * x⁻¹ := by group
      rw [this]
      exact M.mul_mem (hYM hpY) (M.inv_mem (hXM hx))
    have hqY : q ∈ Y := by rw [← hN3M]; exact ⟨hK₃N₃ (hQ₃K₃ hq), hqM⟩
    have hqE : q ∈ E₁ := ⟨hqY, hK₃K (hQ₃K₃ hq)⟩
    exact hXY.le ⟨X.mul_mem (hE₁X hqE) hx, hpY⟩
  have hE₁tE : E₁ᵍ[t] ≤ E₁ᵍ[t] := le_rfl
  have hP₀E : pZero d t K K₁ ⊓ E₁ᵍ[t] = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : x ∈ E₁ ⊓ E₁ᵍ[t] := ⟨hP₀Y ⟨hx1, hE₁tY hx2⟩, hx2⟩
    rwa [hEEt, mem_bot] at this
  have hP₀comm : ∀ p ∈ pZero d t K K₁, ∀ e ∈ E₁ᵍ[t], p * e = e * p := by
    intro p hp e he
    have hP₀C : pZero d t K K₁ ≤ centralizer ((E₁ᵍ[t] : Subgroup G) : Set G) := by
      rw [hP₀def]
      refine sup_le (fun q hq => ?_) (fun x hx => ?_)
      · rw [mem_centralizer_iff]
        intro e he
        exact (hKK₃t' q (hQ₃K₃ hq) e (conj_mono t hEK₃ he)).symm
      · rw [mem_centralizer_iff]
        intro e he
        exact (hXE' x hx e he).symm
    exact (mem_centralizer_iff.1 (hP₀C hp) e he).symm
  have hK₃tsup : K₃ᵍ[t] = Q₃ᵍ[t] ⊔ (Q₃ᵍ[t])ᵍ[v] := by
    calc K₃ᵍ[t] = (Q₃ ⊔ Q₃ᵍ[v])ᵍ[t] := by rw [← hK₃sup]
      _ = Q₃ᵍ[t] ⊔ (Q₃ᵍ[v])ᵍ[t] := conj_sup _ _ _
      _ = Q₃ᵍ[t] ⊔ (Q₃ᵍ[t])ᵍ[v] := by rw [conj_conj_comm hvt'.symm]
  have hXK₃t : ⁅X, K₃ᵍ[t]⁆ = ⊥ := by
    have hc1 : ∀ x ∈ X, ∀ y ∈ Q₃ᵍ[t], x * y = y * x := fun x hx y hy =>
      hcommQ x (hXQ₁ hx) y (conj_mono t hQ₃Q₁ hy)
    have hc2 : ∀ x ∈ X, ∀ y ∈ (Q₃ᵍ[t])ᵍ[v], x * y = y * x := fun x hx y hy =>
      commute_conj_elems hcommQ v x (hXQ₁v hx) y (conj_mono v (conj_mono t hQ₃Q₁) hy)
    have hcent : K₃ᵍ[t] ≤ centralizer (X : Set G) := by
      rw [hK₃tsup]
      exact sup_le (fun y hy => mem_centralizer_iff.2 fun x hx => hc1 x hx y hy)
        (fun y hy => mem_centralizer_iff.2 fun x hx => hc2 x hx y hy)
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 hcent
  have hQsup : Q₁ ⊔ Y = pZero d t K K₁ ⊔ E₁ᵍ[t] := by
    calc Q₁ ⊔ Y = Q₃ ⊔ O₅ := hG1l.symm
      _ = Q₃ ⊔ (X ⊔ E₁ᵍ[t]) := by rw [hO₅eq]
      _ = (Q₃ ⊔ X) ⊔ E₁ᵍ[t] := (sup_assoc _ _ _).symm
  have hZtE : Zᵍ[t] ≤ E₁ᵍ[t] := conj_mono t hZE₁
  have hZtQ₁ : Zᵍ[t] ≤ Q₁ := (le_sup_right : Zᵍ[t] ≤ Z ⊔ Zᵍ[t]).trans (hVZ.ge.trans hV₁Q₁)
  have hQeq : Q₁ = pZero d t K K₁ ⊔ Zᵍ[t] :=
    Q_eq_sup (Z := Z) (E := E₁) (E' := E₁ᵍ[t]) hQsup hP₀Q₁ hP₀comm (by rw [hQ₁Y, hVZ]) hZE₁
      hZtE hEEt hEEt' hE₁tY hZtQ₁
  have hP₀Z : pZero d t K K₁ ⊓ Zᵍ[t] = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left _ hZtE).trans hP₀E.le)
  exact ⟨⟨hXM, hXY, hO₅eq, hXE'inf, commutator_eq_bot_of_commute hXE', hXK₃t⟩,
    hQsup, hP₀E, commutator_eq_bot_of_commute hP₀comm, hQeq, hP₀Z,
    commutator_eq_bot_of_commute fun p hp e he => hP₀comm p hp e (hZtE he)⟩

end G2Main

end Y8_G2

end ProductN1QuotAux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem G0_Q3_le_Q1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    centerMod (yamadaV₁ d t) (qOne d t K₁) = eOne d t K ⊔ yamadaV₁ d t ∧
      eOne d t K ≤ qOne d t K₁ ∧ qThree d t K ≤ qOne d t K₁ :=
  ProductN1QuotAux.G0_aux h d hp hL

theorem G1_decomposition_mod_Y2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (nTwo d t = kFive d t K ⊔ (kFive d t K)ᵍ[t] ∧
      kFive d t K ⊓ (kFive d t K)ᵍ[t] = yamadaY₂ d t ∧
      ⁅kFive d t K, (kFive d t K)ᵍ[t]⁆ ≤ yamadaY₂ d t ∧
      SectionIso (kFive d t K) (yamadaY₂ d t) (lvM d) (d.Y.map L.subtype) ∧
      nTwo d t ⊓ centralizerMod (yamadaY₂ d t) (zpowers t) = lvM d ⊔ yamadaY₂ d t ∧
      kFive d t K = ⁅kFour d t K, kFour d t K⁆ ⊔ yamadaY₂ d t ∧
      nTwo d t ≤ normalizer ((kFive d t K : Subgroup G) : Set G)) ∧
    (kFive d t K = kThree d t K ⊔ pCoreOf 2 (kFive d t K) ∧
      yamadaM₆ d t = pCoreOf 2 (kFive d t K) ⊔ pCoreOf 2 ((kFive d t K)ᵍ[t]) ∧
      pCoreOf 2 (kFive d t K) = (qOne d t K₁ ⊓ yamadaM₆ d t) ⊔ yamadaY₂ d t) ∧
    (yamadaP d t ⊓ kFive d t K = qThree d t K ⊔ pCoreOf 2 (kFive d t K) ∧
      qThree d t K ⊔ pCoreOf 2 (kFive d t K) = qOne d t K₁ ⊔ yamadaY₂ d t) :=
  ProductN1QuotAux.G1_aux h d hp hL

theorem G2_structure_Q1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (xQ d t K₁ ≤ yamadaM₆ d t ∧ xQ d t K₁ ⊓ yamadaY₂ d t = eOne d t K ∧
      pCoreOf 2 (kFive d t K) = xQ d t K₁ ⊔ (eOne d t K)ᵍ[t] ∧
      xQ d t K₁ ⊓ (eOne d t K)ᵍ[t] = ⊥ ∧ ⁅xQ d t K₁, (eOne d t K)ᵍ[t]⁆ = ⊥ ∧
      ⁅xQ d t K₁, (kThree d t K)ᵍ[t]⁆ = ⊥) ∧
    (qOne d t K₁ ⊔ yamadaY₂ d t = pZero d t K K₁ ⊔ (eOne d t K)ᵍ[t] ∧
      pZero d t K K₁ ⊓ (eOne d t K)ᵍ[t] = ⊥ ∧ ⁅pZero d t K K₁, (eOne d t K)ᵍ[t]⁆ = ⊥ ∧
      qOne d t K₁ = pZero d t K K₁ ⊔ (zc (qThree d t K))ᵍ[t] ∧
      pZero d t K K₁ ⊓ (zc (qThree d t K))ᵍ[t] = ⊥ ∧
      ⁅pZero d t K K₁, (zc (qThree d t K))ᵍ[t]⁆ = ⊥) :=
  ProductN1QuotAux.G2_aux h d hp hL

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
