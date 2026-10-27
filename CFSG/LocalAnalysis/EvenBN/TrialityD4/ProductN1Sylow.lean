module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1
public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def qOne (d : TrialityD4Data L q) (t : G) (K₁ : Subgroup G) :
    Subgroup G :=
  yamadaP d t ⊓ ⁅K₁, K₁⁆

@[expose] noncomputable def rSub (d : TrialityD4Data L q) (t : G) (K : Subgroup G) :
    Subgroup G :=
  yamadaP d t ⊓ kFour d t K

@[expose] noncomputable def aSub (d : TrialityD4Data L q) (t : G) (K₁ : Subgroup G) :
    Subgroup G :=
  yamadaP d t ⊓ K₁

@[expose] noncomputable def bSub (d : TrialityD4Data L q) (t : G) (K : Subgroup G) :
    Subgroup G :=
  yamadaP d t ⊓ kTwo d t K

structure Labelled (d : TrialityD4Data L q) (t : G) (K K₁ : Subgroup G) : Prop where
  comp : IsLayerComponent d t K
  factor : IsN1Factor d t K₁
  label : rSub d t K ⊔ yamadaD₅ d t = aSub d t K₁

end Defs

namespace ProductN1SylowAux

section Conj

variable {G : Type*} [Group G]

theorem mem_conj_iff {A : Subgroup G} {g x : G} : x ∈ Aᵍ[g] ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp [mul_assoc]

theorem le_normalizer_of_commutator_mem {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ Y) : X ≤ normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact mul_mem (h x hx y hy) hy
  · intro hy
    have h2 := h x⁻¹ (inv_mem hx) _ hy
    have e : y = (x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ * (x * y * x⁻¹)⁻¹) * (x * y * x⁻¹) := by group
    rw [e]
    exact mul_mem h2 hy

theorem mem_sup_iff_of_le_normalizer {H N : Subgroup G} (h : H ≤ normalizer (N : Set G))
    {x : G} : x ∈ H ⊔ N ↔ ∃ a ∈ H, ∃ b ∈ N, x = a * b := by
  have := Subgroup.coe_mul_of_left_le_normalizer_right H N h
  rw [← SetLike.mem_coe, this]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem mem_sup_iff_of_le_normalizer' {H N : Subgroup G} (h : H ≤ normalizer (N : Set G))
    {x : G} : x ∈ N ⊔ H ↔ ∃ b ∈ N, ∃ a ∈ H, x = b * a := by
  have := Subgroup.coe_mul_of_right_le_normalizer_left N H h
  rw [← SetLike.mem_coe, this]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

theorem mem_normalizer_of_conj_eq {A : Subgroup G} {g : G} (h : Aᵍ[g] = A) :
    g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conj_iff, h]

theorem mem_normalizer_commutator {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_eq
  rw [Subgroup.map_commutator]
  have h1 : Kᵍ[g] = K := by
    ext x
    rw [mem_conj_iff]
    exact ((mem_normalizer_iff.1 hg x).symm)
  show ⁅Kᵍ[g], Kᵍ[g]⁆ = ⁅K, K⁆
  rw [h1]

theorem mem_normalizer_oTwoPrimeRes {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((oTwoPrimeRes X : Subgroup G) : Set G) := by
  have hs : g ∈ normalizer ({x : G | x ∈ X ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx, k, hk⟩
      refine ⟨(mem_normalizer_iff.1 hg x).1 hx, k, ?_⟩
      rw [show g * x * g⁻¹ = MulAut.conj g x from rfl, ← map_pow, hk, map_one]
    · rintro ⟨hx, k, hk⟩
      refine ⟨(mem_normalizer_iff.1 hg x).2 hx, k, ?_⟩
      have h2 : (MulAut.conj g x) ^ (2 ^ k) = 1 := hk
      rw [← map_pow] at h2
      exact (MulAut.conj g).injective (h2.trans (map_one _).symm)
  exact Subgroup.normalizer_le_normalizer_closure _ hs

theorem conj_mono {A B : Subgroup G} (h : A ≤ B) (g : G) : Aᵍ[g] ≤ Bᵍ[g] :=
  Subgroup.map_mono h

theorem conj_inf (A B : Subgroup G) (g : G) : (A ⊓ B)ᵍ[g] = Aᵍ[g] ⊓ Bᵍ[g] :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conj_sup (A B : Subgroup G) (g : G) : (A ⊔ B)ᵍ[g] = Aᵍ[g] ⊔ Bᵍ[g] :=
  Subgroup.map_sup _ _ _

theorem conj_commutator (A B : Subgroup G) (g : G) : ⁅A, B⁆ᵍ[g] = ⁅Aᵍ[g], Bᵍ[g]⁆ :=
  Subgroup.map_commutator _ _ _

theorem card_conj (A : Subgroup G) (g : G) : Nat.card ↥(Aᵍ[g]) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conj_eq_of_mem_normalizer {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    Aᵍ[g] = A := by
  ext x
  rw [mem_conj_iff]
  exact ((mem_normalizer_iff.1 hg x).symm)

theorem conj_conj_of_mul_self {t : G} (ht : t * t = 1) (A : Subgroup G) : (Aᵍ[t])ᵍ[t] = A :=
  map_conj_inv_map_conj_inv ht A

theorem mem_conj_iff_of_mul_self {t : G} (ht : t * t = 1) {A : Subgroup G} {x : G} :
    x ∈ Aᵍ[t] ↔ t⁻¹ * x * t ∈ A := by
  have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [mem_conj_iff, h]

theorem pCoreOf_map_mulEquiv (e : G ≃* G) (A : Subgroup G) :
    pCoreOf 2 (A.map (e : G →* G)) = (pCoreOf 2 A).map (e : G →* G) := by
  have h := CFSG.pCore_map_iso 2 (MulEquiv.subgroupMap e A)
  have hcomp : (A.map (e : G →* G)).subtype.comp (MulEquiv.subgroupMap e A).toMonoidHom =
      (e : G →* G).comp A.subtype := by
    ext x
    rfl
  unfold pCoreOf
  conv_lhs => rw [← h, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem pCoreOf_conj (A : Subgroup G) (g : G) :
    pCoreOf 2 (Aᵍ[g]) = (pCoreOf 2 A)ᵍ[g] :=
  pCoreOf_map_mulEquiv (MulAut.conj g⁻¹) A

theorem mem_normalizer_pCoreOf {A : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer ((pCoreOf 2 A : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_eq
  have h1 : Aᵍ[g] = A := by
    ext x
    rw [mem_conj_iff]
    exact ((mem_normalizer_iff.1 hg x).symm)
  have := pCoreOf_conj A g
  rw [h1] at this
  exact this.symm

theorem le_normalizer_pCoreOf (A : Subgroup G) :
    A ≤ normalizer ((pCoreOf 2 A : Subgroup G) : Set G) := by
  haveI : ((pCoreOf 2 A).subgroupOf A).Normal := by
    have : (pCoreOf 2 A).subgroupOf A = CFSG.pCore 2 ↥A :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
    rw [this]
    exact CFSG.pCore_normal
  exact Subgroup.le_normalizer_of_normal_subgroupOf (by rintro _ ⟨x, -, rfl⟩; exact x.2)

theorem le_pCoreOf_of_normal {A W : Subgroup G} (hWA : W ≤ A) (hN : A ≤ normalizer (W : Set G))
    (hW : IsPGroup 2 W) : W ≤ pCoreOf 2 A := by
  have hnorm : (W.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWA).2 hN
  have hp : IsPGroup 2 (W.subgroupOf A) := hW.comap_subtype
  have h1 : W.subgroupOf A ≤ CFSG.pCore 2 ↥A := le_sSup ⟨hnorm, hp⟩
  intro x hx
  have hxA : x ∈ A := hWA hx
  exact ⟨⟨x, hxA⟩, h1 hx, rfl⟩

theorem oTwoPrimeRes_le (X : Subgroup G) : oTwoPrimeRes X ≤ X :=
  (Subgroup.closure_le X).2 fun _ hx => hx.1

theorem le_oTwoPrimeRes_of_isPGroup {X Q : Subgroup G} (hQX : Q ≤ X) (hQ : IsPGroup 2 Q) :
    Q ≤ oTwoPrimeRes X := by
  intro x hx
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  exact Subgroup.subset_closure ⟨hQX hx, k, by simpa using congrArg Subtype.val hk⟩

theorem pCoreOf_le (A : Subgroup G) : pCoreOf 2 A ≤ A := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

end Conj

section QuotientIso

variable {G : Type*} [Group G]

theorem IsQuotientIso.conj {X N : Subgroup G} {T : Type*} [Group T] (h : IsQuotientIso X N T)
    (g : G) : IsQuotientIso (Xᵍ[g]) (Nᵍ[g]) T := by
  obtain ⟨φ, hφ, hker⟩ := h
  let e : ↥(Xᵍ[g]) ≃* ↥X := (MulEquiv.subgroupMap (MulAut.conj g⁻¹) X).symm
  have he : ∀ x : ↥(Xᵍ[g]), ((e x : ↥X) : G) = g * (x : G) * g⁻¹ := by
    intro x
    have h1 : (MulEquiv.subgroupMap (MulAut.conj g⁻¹) X) (e x) = x :=
      (MulEquiv.subgroupMap (MulAut.conj g⁻¹) X).apply_symm_apply x
    have h2 := congrArg Subtype.val h1
    have h3 : (MulAut.conj g⁻¹) ((e x : ↥X) : G) = (x : G) := h2
    have h4 : g⁻¹ * ((e x : ↥X) : G) * g = (x : G) := by simpa using h3
    rw [← h4]
    group
  refine ⟨φ.comp e.toMonoidHom, hφ.comp e.surjective, ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have h5 : φ (e x) = 1 ↔ (((e x : ↥X) : G)) ∈ N := by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [h5, he x, Subgroup.mem_subgroupOf, mem_conj_iff]

theorem IsQuotientIso.card_eq [Finite G] {X N : Subgroup G} {T : Type*} [Group T]
    (h : IsQuotientIso X N T) (hNX : N ≤ X) : Nat.card X = Nat.card N * Nat.card T := by
  obtain ⟨φ, hφ, hker⟩ := h
  have := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [hker] at this
  rw [← this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]

end QuotientIso

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem sylow_prod {P N A B W : Subgroup G} (hP : IsSylowOf 2 P N) (hN : A ⊔ B = N)
    (hAB : A ⊓ B = W) (hC : ⁅A, B⁆ ≤ W) (hWP : W ≤ P) :
    IsSylowOf 2 (P ⊓ A) A ∧ IsSylowOf 2 (P ⊓ B) B ∧ P = (P ⊓ A) ⊔ (P ⊓ B) ∧
      (P ⊓ A) ⊓ (P ⊓ B) = W ∧ ⁅P ⊓ A, P ⊓ B⁆ ≤ W := by
  have hWA : W ≤ A := hAB ▸ inf_le_left
  have hWB : W ≤ B := hAB ▸ inf_le_right
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ W := fun a ha b hb =>
    hC (Subgroup.commutator_mem_commutator ha hb)
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ W := by
    intro b hb a ha
    have := inv_mem (hcomm a ha b hb)
    have e : (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ := by group
    rwa [e] at this
  have hBA : B ≤ normalizer (A : Set G) :=
    le_normalizer_of_commutator_mem fun b hb a ha => hWA (hcomm' b hb a ha)
  have hAB' : A ≤ normalizer (B : Set G) :=
    le_normalizer_of_commutator_mem fun a ha b hb => hWB (hcomm a ha b hb)
  have hNA : N ≤ normalizer (A : Set G) := hN ▸ sup_le le_normalizer hBA
  have hNB : N ≤ normalizer (B : Set G) := hN ▸ sup_le hAB' le_normalizer
  have hAN : A ≤ N := hN ▸ le_sup_left
  have hBN : B ≤ N := hN ▸ le_sup_right
  have hPA : IsSylowOf 2 (P ⊓ A) A := hP.inf_of_le_normalizer hAN hNA
  have hPB : IsSylowOf 2 (P ⊓ B) B := hP.inf_of_le_normalizer hBN hNB
  have hint : (P ⊓ A) ⊓ (P ⊓ B) = W := by
    apply le_antisymm
    · intro x hx
      rw [← hAB]
      exact ⟨hx.1.2, hx.2.2⟩
    · intro x hx
      exact ⟨⟨hWP hx, hWA hx⟩, ⟨hWP hx, hWB hx⟩⟩
  have hcomm2 : ⁅P ⊓ A, P ⊓ B⁆ ≤ W :=
    (Subgroup.commutator_mono inf_le_right inf_le_right).trans hC
  refine ⟨hPA, hPB, ?_, hint, hcomm2⟩
  set QA := P ⊓ A with hQA
  set QB := P ⊓ B with hQB
  have hQBA : QB ≤ normalizer (QA : Set G) := by
    refine le_normalizer_of_commutator_mem fun b hb a ha => ?_
    have h1 : b * a * b⁻¹ * a⁻¹ ∈ W := hcomm' b hb.2 a ha.2
    exact ⟨hWP h1, hWA h1⟩
  have hT := card_sup_mul_card_inf_eq_D4 hQBA
  have hN2 := card_sup_mul_card_inf_eq_D4 hBA
  rw [hint] at hT
  rw [hN, hAB] at hN2
  have hTP : QA ⊔ QB ≤ P := sup_le inf_le_left inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hTP ?_).symm
  have hcardP := hP.card_eq
  have hcA := hPA.card_eq
  have hcB := hPB.card_eq
  obtain ⟨w, hw⟩ := (IsPGroup.iff_card (p := 2) (G := W)).1 ((hP.isPGroup).to_le hWP)
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card N).factorization 2 + w = (Nat.card A).factorization 2 +
      (Nat.card B).factorization 2 := by
    have h := congrArg (fun n => n.factorization 2) hN2
    rw [hw, Nat.factorization_mul hN0 (by positivity), Nat.factorization_mul hA0 hB0] at h
    simpa [Nat.Prime.factorization_pow Nat.prime_two] using h
  have hTcard : Nat.card (QA ⊔ QB : Subgroup G) = 2 ^ ((Nat.card N).factorization 2) := by
    have h1 : Nat.card (QA ⊔ QB : Subgroup G) * 2 ^ w = 2 ^ ((Nat.card A).factorization 2) *
        2 ^ ((Nat.card B).factorization 2) := by
      rw [← hw, hT, hcA, hcB]
    rw [← pow_add, ← hfac, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  rw [hcardP, hTcard]

theorem pow_relIndex_mem {M P : Subgroup G} (hPM : P ≤ M) (hMP : M ≤ normalizer (P : Set G))
    {g : G} (hg : g ∈ M) : g ^ P.relIndex M ∈ P := by
  haveI : (P.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hMP
  have h := Subgroup.pow_index_mem (P.subgroupOf M) (⟨g, hg⟩ : M)
  rw [Subgroup.mem_subgroupOf] at h
  exact h

theorem mem_normalizer_of_pow_mem {K K' : Subgroup G} (hne : K ≠ K') {g : G}
    (hK : K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = K')
    (hK' : K'.map (MulAut.conj g).toMonoidHom = K ∨ K'.map (MulAut.conj g).toMonoidHom = K')
    {m : ℕ} (hm : Odd m) (hgm : g ^ m ∈ normalizer (K : Set G)) :
    g ∈ normalizer (K : Set G) := by
  have hinj : Function.Injective (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj g).injective
  have hmul : ∀ (a b : G) (X : Subgroup G),
      X.map (MulAut.conj (a * b)).toMonoidHom =
        (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b X
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hnorm : K.map (MulAut.conj g).toMonoidHom = K → g ∈ normalizer (K : Set G) := by
    intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h2
      rwa [← this]
  by_contra hg
  have hK1 : K.map (MulAut.conj g).toMonoidHom = K' := by
    rcases hK with h | h
    · exact absurd (hnorm h) hg
    · exact h
  have hK2 : K'.map (MulAut.conj g).toMonoidHom = K := by
    rcases hK' with h | h
    · exact h
    · exfalso
      apply hne
      apply hinj
      show K.map (MulAut.conj g).toMonoidHom = K'.map (MulAut.conj g).toMonoidHom
      rw [hK1, h]
  have hsq : K.map (MulAut.conj (g * g)).toMonoidHom = K := by
    rw [hmul, hK1, hK2]
  have hpow : ∀ n : ℕ, K.map (MulAut.conj (g ^ (2 * n))).toMonoidHom = K := by
    intro n
    induction n with
    | zero =>
      ext x
      simp only [Subgroup.mem_map, mul_zero, pow_zero, map_one, MulEquiv.coe_toMonoidHom,
        MulAut.one_apply, exists_eq_right]
    | succ n ih =>
      have : g ^ (2 * (n + 1)) = (g * g) * g ^ (2 * n) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, pow_two]
      rw [this, hmul, ih, hsq]
  obtain ⟨k, rfl⟩ := hm
  have hgm' : K.map (MulAut.conj (g ^ (2 * k + 1))).toMonoidHom = K' := by
    have : g ^ (2 * k + 1) = g * g ^ (2 * k) := by rw [pow_succ']
    rw [this, hmul, hpow k, hK1]
  have hKK : K.map (MulAut.conj (g ^ (2 * k + 1))).toMonoidHom = K := by
    have h := hgm
    rw [Subgroup.mem_normalizer_iff] at h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).1 hy
    · intro hx
      refine ⟨(g ^ (2 * k + 1))⁻¹ * x * (g ^ (2 * k + 1)), ?_, ?_⟩
      swap
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have h2 := (h ((g ^ (2 * k + 1))⁻¹ * x * (g ^ (2 * k + 1)))).2
      apply h2
      have e : g ^ (2 * k + 1) * ((g ^ (2 * k + 1))⁻¹ * x * g ^ (2 * k + 1)) *
          (g ^ (2 * k + 1))⁻¹ = x := by group
      rw [e]
      exact hx
  exact hne (hKK.symm.trans hgm')

theorem exists_centralizer_mul {M P J : Subgroup G} (hPM : P ≤ M) (hP2 : IsPGroup 2 P)
    (hMP : M ≤ normalizer (P : Set G)) (hJM : J ≤ M) (hJ : Odd (Nat.card J))
    (hcomm : ∀ m ∈ M, ∀ j ∈ J, m * j * m⁻¹ * j⁻¹ ∈ P) {m : G} (hm : m ∈ M) :
    ∃ z ∈ M ⊓ centralizer (J : Set G), ∃ p ∈ P, m = z * p := by
  have hJP : J ≤ normalizer (P : Set G) := hJM.trans hMP
  letI : MulDistribMulAction J P := Subgroup.conjMulDistribMulActionOfLeNormalizer J P hJP
  have hsolv : Group.IsSolvable P := by
    haveI : Group.IsNilpotent P := hP2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card J) (Nat.card P) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := P)).1 hP2
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hJ)
  have hmem : ∀ j : J, m⁻¹ * (j : G) * m * (j : G)⁻¹ ∈ P := by
    intro j
    have := hcomm m⁻¹ (inv_mem hm) j j.2
    simpa using this
  let c : J → P := fun j => ⟨m⁻¹ * (j : G) * m * (j : G)⁻¹, hmem j⟩
  have hc : ∀ a b : J, c (a * b) = c a * (a • c b) := by
    intro a b
    apply Subtype.ext
    change m⁻¹ * ((a : G) * (b : G)) * m * ((a : G) * (b : G))⁻¹ =
      (m⁻¹ * (a : G) * m * (a : G)⁻¹) * ((a : G) * (m⁻¹ * (b : G) * m * (b : G)⁻¹) * (a : G)⁻¹)
    group
  obtain ⟨x, hx⟩ := CFSG.exists_principal_cocycle_of_solvable_coprime hsolv hcop c hc
  refine ⟨m * (x : G), mem_inf.2 ⟨mul_mem hm (hPM x.2), mem_centralizer_iff.2 fun a ha => ?_⟩,
    (x : G)⁻¹, inv_mem x.2, by group⟩
  have h1 := congrArg Subtype.val (hx ⟨a, ha⟩)
  change m⁻¹ * a * m * a⁻¹ = (x : G) * (a * (x : G) * a⁻¹)⁻¹ at h1
  have h2 : m⁻¹ * a * m = (x : G) * a * (x : G)⁻¹ := by
    have h3 : m⁻¹ * a * m = (m⁻¹ * a * m * a⁻¹) * a := by group
    rw [h3, h1]
    group
  calc a * (m * (x : G)) = m * ((m⁻¹ * a * m) * (x : G)) := by group
    _ = m * ((x : G) * a * (x : G)⁻¹ * (x : G)) := by rw [h2]
    _ = m * (x : G) * a := by group

theorem card_sup_half_sq {P N H F : Subgroup G} {t : G}
    (hsup : H ⊔ Hᵍ[t] = P) (hinf : H ⊓ Hᵍ[t] = N) (hcomm : ⁅H, Hᵍ[t]⁆ ≤ N) (hNH : N ≤ H)
    (hFt : Fᵍ[t] = F) (hNF : N ≤ F) (hPF : P ≤ normalizer (F : Set G))
    (hdec : F ≤ (H ⊓ F) ⊔ (Hᵍ[t] ⊓ F)) :
    Nat.card (H ⊔ F : Subgroup G) ^ 2 = Nat.card P * Nat.card F := by
  have hHtN : Hᵍ[t] ≤ normalizer (H : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅Hᵍ[t], H⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [Subgroup.commutator_comm] at h1
    exact hNH (hcomm h1)
  have h1 := card_sup_mul_card_inf_eq_D4 hHtN
  rw [hsup, hinf, card_conj] at h1
  have hF₂ : (H ⊓ F)ᵍ[t] = Hᵍ[t] ⊓ F := by rw [conj_inf, hFt]
  have hNHt : N ≤ Hᵍ[t] := hinf ▸ inf_le_right
  have hinfF : (H ⊓ F) ⊓ (Hᵍ[t] ⊓ F) = N := by
    apply le_antisymm
    · intro x hx
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨hx.1.1, hx.2.1⟩
    · exact le_inf (le_inf hNH hNF) (le_inf hNHt hNF)
  have hsupF : (H ⊓ F) ⊔ (Hᵍ[t] ⊓ F) = F := le_antisymm (sup_le inf_le_right inf_le_right) hdec
  have hF₂N : (Hᵍ[t] ⊓ F) ≤ normalizer ((H ⊓ F : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅Hᵍ[t], H⁆ :=
      Subgroup.commutator_mem_commutator hx.1 hy.1
    rw [Subgroup.commutator_comm] at h1
    exact Subgroup.mem_inf.2 ⟨hNH (hcomm h1), hNF (hcomm h1)⟩
  have h2 := card_sup_mul_card_inf_eq_D4 hF₂N
  rw [hsupF, hinfF, ← hF₂, card_conj] at h2
  have hHF : H ≤ normalizer (F : Set G) := by
    have : H ≤ P := hsup ▸ le_sup_left
    exact this.trans hPF
  have h3 := card_sup_mul_card_inf_eq_D4 (A := F) (B := H) hHF
  rw [sup_comm, inf_comm] at h3
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have hF0 : 0 < Nat.card F := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hF0 hN0)
  have h4 : (Nat.card (H ⊔ F : Subgroup G) * Nat.card (H ⊓ F : Subgroup G)) ^ 2 =
      (Nat.card H * Nat.card F) ^ 2 := by rw [h3, mul_comm]
  calc Nat.card (H ⊔ F : Subgroup G) ^ 2 * (Nat.card F * Nat.card N)
      = Nat.card (H ⊔ F : Subgroup G) ^ 2 * Nat.card (H ⊓ F : Subgroup G) ^ 2 := by rw [h2]; ring
    _ = (Nat.card (H ⊔ F : Subgroup G) * Nat.card (H ⊓ F : Subgroup G)) ^ 2 := by ring
    _ = (Nat.card H * Nat.card F) ^ 2 := h4
    _ = (Nat.card H * Nat.card H) * Nat.card F ^ 2 := by ring
    _ = Nat.card P * Nat.card N * Nat.card F ^ 2 := by rw [h1]
    _ = Nat.card P * Nat.card F * (Nat.card F * Nat.card N) := by ring

end Sylow

namespace UCSAux

section Abstract

variable {Q : Type*} [Group Q]

abbrev zs (S : Subgroup Q) (i : ℕ) : Subgroup Q :=
  (Subgroup.upperCentralSeries ↥S i).map S.subtype

theorem zs_zero (S : Subgroup Q) : zs S 0 = ⊥ := by
  simp [zs]

theorem zs_le (S : Subgroup Q) (i : ℕ) : zs S i ≤ S :=
  Subgroup.map_subtype_le _

theorem mem_zs_succ {S : Subgroup Q} {i : ℕ} {y : Q} :
    y ∈ zs S (i + 1) ↔ y ∈ S ∧ ∀ w ∈ S, y * w * y⁻¹ * w⁻¹ ∈ zs S i := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun w hw => ?_⟩
    exact ⟨z * ⟨w, hw⟩ * z⁻¹ * ⟨w, hw⟩⁻¹,
      Subgroup.mem_upperCentralSeries_succ_iff.1 hz ⟨w, hw⟩, rfl⟩
  · rintro ⟨hy, h⟩
    refine ⟨⟨y, hy⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun w => ?_, rfl⟩
    obtain ⟨c, hc, hcw⟩ := h w w.2
    have hcc : c = (⟨y, hy⟩ : S) * w * (⟨y, hy⟩ : S)⁻¹ * w⁻¹ := S.subtype_injective hcw
    show ((⟨y, hy⟩ : S) * w * (⟨y, hy⟩ : S)⁻¹ * w⁻¹) ∈ Subgroup.upperCentralSeries ↥S i
    rw [← hcc]
    exact hc

theorem le_normalizer_zs (S : Subgroup Q) (j : ℕ) : S ≤ normalizer (zs S j : Set Q) := by
  have h : (zs S j).subgroupOf S = Subgroup.upperCentralSeries ↥S j :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  haveI : ((zs S j).subgroupOf S).Normal := by
    rw [h]
    infer_instance
  exact Subgroup.le_normalizer_of_normal_subgroupOf (zs_le S j)

theorem mem_sup_iff_of_commute {X Y : Subgroup Q} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    {z : Q} : z ∈ X ⊔ Y ↔ ∃ x ∈ X, ∃ y ∈ Y, z = x * y := by
  constructor
  · intro hz
    rw [Subgroup.sup_eq_closure] at hz
    induction hz using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with hu | hu
      · exact ⟨u, hu, 1, one_mem _, (mul_one u).symm⟩
      · exact ⟨1, one_mem _, u, hu, (one_mul u).symm⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    | mul u v _ _ ihu ihv =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihu
      obtain ⟨a', ha', b', hb', rfl⟩ := ihv
      refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
      have h1 : b * a' = a' * b := (h a' ha' b hb).symm
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [h1]
        _ = a * a' * (b * b') := by group
    | inv u _ ihu =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihu
      refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
      calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h a ha b hb]
        _ = a⁻¹ * b⁻¹ := mul_inv_rev b a
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_sup hx hy

variable {A B : Subgroup Q}

theorem commutator_mem {a a' : Q} (ha : a ∈ A) (ha' : a' ∈ A) : a * a' * a⁻¹ * a'⁻¹ ∈ A :=
  mul_mem (mul_mem (mul_mem ha ha') (inv_mem ha)) (inv_mem ha')

theorem commutator_prod (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a a' b b' : Q} (ha : a ∈ A)
    (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) :
    a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹ =
      (a * a' * a⁻¹ * a'⁻¹) * (b * b' * b⁻¹ * b'⁻¹) := by
  have h1 : b * a' = a' * b := (hc a' ha' b hb).symm
  have h2 : (b * b' * b⁻¹) * a⁻¹ = a⁻¹ * (b * b' * b⁻¹) :=
    (hc a⁻¹ (inv_mem ha) _ (mul_mem (mul_mem hb hb') (inv_mem hb))).symm
  have h3 : (b * b' * b⁻¹ * b'⁻¹) * a'⁻¹ = a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹) :=
    (hc a'⁻¹ (inv_mem ha') _ (commutator_mem hb hb')).symm
  calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
      = a * (b * a') * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by group
    _ = a * (a' * b) * b' * b⁻¹ * a⁻¹ * b'⁻¹ * a'⁻¹ := by rw [h1]
    _ = a * a' * ((b * b' * b⁻¹) * a⁻¹) * b'⁻¹ * a'⁻¹ := by group
    _ = a * a' * (a⁻¹ * (b * b' * b⁻¹)) * b'⁻¹ * a'⁻¹ := by rw [h2]
    _ = a * a' * a⁻¹ * ((b * b' * b⁻¹ * b'⁻¹) * a'⁻¹) := by group
    _ = a * a' * a⁻¹ * (a'⁻¹ * (b * b' * b⁻¹ * b'⁻¹)) := by rw [h3]
    _ = (a * a' * a⁻¹ * a'⁻¹) * (b * b' * b⁻¹ * b'⁻¹) := by group

theorem zs_mul_mem_iff (hI : A ⊓ B = ⊥) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (i : ℕ) :
    ∀ a ∈ A, ∀ b ∈ B, a * b ∈ zs (A ⊔ B) i ↔ a ∈ zs A i ∧ b ∈ zs B i := by
  induction i with
  | zero =>
    intro a ha b hb
    simp only [zs_zero, Subgroup.mem_bot]
    constructor
    · intro h
      have hab : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
      have hB : a ∈ B := by
        rw [hab]
        exact inv_mem hb
      have hmem : a ∈ A ⊓ B := Subgroup.mem_inf.2 ⟨ha, hB⟩
      rw [hI, Subgroup.mem_bot] at hmem
      subst hmem
      exact ⟨rfl, by simpa using h⟩
    · rintro ⟨rfl, rfl⟩
      simp
  | succ i ih =>
    intro a ha b hb
    rw [mem_zs_succ, mem_zs_succ, mem_zs_succ]
    have hmem : a * b ∈ A ⊔ B := mul_mem_sup ha hb
    constructor
    · rintro ⟨-, h⟩
      have h' : ∀ a' ∈ A, ∀ b' ∈ B,
          a * a' * a⁻¹ * a'⁻¹ ∈ zs A i ∧ b * b' * b⁻¹ * b'⁻¹ ∈ zs B i := by
        intro a' ha' b' hb'
        have h1 := h (a' * b') (mul_mem_sup ha' hb')
        rw [commutator_prod hc ha ha' hb hb'] at h1
        exact (ih _ (commutator_mem ha ha') _ (commutator_mem hb hb')).1 h1
      refine ⟨⟨ha, fun w hw => ?_⟩, ⟨hb, fun w hw => ?_⟩⟩
      · exact (h' w hw 1 (one_mem _)).1
      · exact (h' 1 (one_mem _) w hw).2
    · rintro ⟨⟨-, hA⟩, ⟨-, hB⟩⟩
      refine ⟨hmem, fun w hw => ?_⟩
      obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_commute hc).1 hw
      rw [commutator_prod hc ha ha' hb hb']
      exact (ih _ (commutator_mem ha ha') _ (commutator_mem hb hb')).2
        ⟨hA a' ha', hB b' hb'⟩

theorem zs_sup (hI : A ⊓ B = ⊥) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (i : ℕ) :
    zs (A ⊔ B) i = zs A i ⊔ zs B i := by
  have hc' : ∀ a ∈ zs A i, ∀ b ∈ zs B i, a * b = b * a := fun a ha b hb =>
    hc a (zs_le A i ha) b (zs_le B i hb)
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hc).1 (zs_le (A ⊔ B) i hy)
    obtain ⟨h1, h2⟩ := (zs_mul_mem_iff hI hc i a ha b hb).1 hy
    exact mul_mem_sup h1 h2
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hc').1 hy
    exact (zs_mul_mem_iff hI hc i a (zs_le A i ha) b (zs_le B i hb)).2 ⟨ha, hb⟩

end Abstract

section Quotient

variable {G : Type*} [Group G]

theorem upperCenterMod_eq_lift_zs (N A : Subgroup G) (i : ℕ) :
    upperCenterMod N A i = NormalizerQuotient.lift (zs (NormalizerQuotient.bar N A) i) :=
  rfl

theorem lift_sup {N : Subgroup G} (Y Y' : Subgroup (NormalizerQuotient.Bar N)) :
    NormalizerQuotient.lift (Y ⊔ Y') =
      NormalizerQuotient.lift Y ⊔ NormalizerQuotient.lift Y' := by
  unfold NormalizerQuotient.lift
  rw [← Subgroup.comap_sup_eq (NormalizerQuotient.proj N) Y Y'
    NormalizerQuotient.proj_surjective, Subgroup.map_sup]

end Quotient

end UCSAux

section UCS

variable {G : Type*} [Group G]

theorem upperCenterMod_zero (N A : Subgroup G) : upperCenterMod N A 0 = N := by
  rw [UCSAux.upperCenterMod_eq_lift_zs, UCSAux.zs_zero]
  ext g
  rw [NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨_, h⟩
    exact NormalizerQuotient.proj_eq_one_iff.1 (Subgroup.mem_bot.1 h)
  · intro hg
    exact ⟨Subgroup.le_normalizer hg,
      Subgroup.mem_bot.2 (NormalizerQuotient.proj_eq_one_iff.2 hg)⟩

theorem mem_upperCenterMod_succ {N A : Subgroup G} (hNA : N ≤ A) {i : ℕ} {x : G} :
    x ∈ upperCenterMod N A (i + 1) ↔ x ∈ A ∧ x ∈ normalizer (N : Set G) ∧
      ∀ a ∈ A, ∀ _ : a ∈ normalizer (N : Set G),
        x * a * x⁻¹ * a⁻¹ ∈ upperCenterMod N A i := by
  rw [UCSAux.upperCenterMod_eq_lift_zs, NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hx, hmem⟩
    rw [UCSAux.mem_zs_succ] at hmem
    obtain ⟨hxbar, hcomm⟩ := hmem
    refine ⟨(NormalizerQuotient.mem_bar_iff hNA ⟨x, hx⟩).1 hxbar, hx, fun a ha han => ?_⟩
    have h1 := hcomm (NormalizerQuotient.proj N ⟨a, han⟩) (NormalizerQuotient.proj_mem_bar ha)
    have hmul : x * a * x⁻¹ * a⁻¹ ∈ normalizer (N : Set G) :=
      mul_mem (mul_mem (mul_mem hx han) (inv_mem hx)) (inv_mem han)
    rw [UCSAux.upperCenterMod_eq_lift_zs]
    refine NormalizerQuotient.mem_lift_iff.2 ⟨hmul, ?_⟩
    have e : (⟨x * a * x⁻¹ * a⁻¹, hmul⟩ : normalizer (N : Set G)) =
        ⟨x, hx⟩ * ⟨a, han⟩ * ⟨x, hx⟩⁻¹ * ⟨a, han⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h1
  · rintro ⟨hxA, hx, h⟩
    refine ⟨hx, ?_⟩
    rw [UCSAux.mem_zs_succ]
    refine ⟨(NormalizerQuotient.mem_bar_iff hNA ⟨x, hx⟩).2 hxA, fun w hw => ?_⟩
    obtain ⟨⟨a, han⟩, rfl⟩ := NormalizerQuotient.proj_surjective w
    have haA : a ∈ A := (NormalizerQuotient.mem_bar_iff hNA ⟨a, han⟩).1 hw
    have h1 := h a haA han
    rw [UCSAux.upperCenterMod_eq_lift_zs] at h1
    obtain ⟨hmul, hzs⟩ := NormalizerQuotient.mem_lift_iff.1 h1
    have e : (⟨x * a * x⁻¹ * a⁻¹, hmul⟩ : normalizer (N : Set G)) =
        ⟨x, hx⟩ * ⟨a, han⟩ * ⟨x, hx⟩⁻¹ * ⟨a, han⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at hzs
    exact hzs

theorem le_upperCenterMod {N A : Subgroup G} (hNA : N ≤ A) (i : ℕ) :
    N ≤ upperCenterMod N A i :=
  NormalizerQuotient.le_lift _

theorem upperCenterMod_le {N A : Subgroup G} (hNA : N ≤ A) (i : ℕ) :
    upperCenterMod N A i ≤ A := by
  cases i with
  | zero =>
    rw [upperCenterMod_zero]
    exact hNA
  | succ i =>
    intro x hx
    exact ((mem_upperCenterMod_succ hNA).1 hx).1

theorem upperCenterMod_upperCentralSeries (P : Subgroup G) (j i : ℕ) :
    upperCenterMod ((Subgroup.upperCentralSeries ↥P j).map P.subtype) P i =
      (Subgroup.upperCentralSeries ↥P (j + i)).map P.subtype := by
  induction i with
  | zero =>
    rw [upperCenterMod_zero]
    rfl
  | succ i ih =>
    ext x
    rw [mem_upperCenterMod_succ (UCSAux.zs_le P j), ih]
    show _ ↔ x ∈ UCSAux.zs P (j + i + 1)
    rw [UCSAux.mem_zs_succ]
    constructor
    · rintro ⟨hxP, -, h⟩
      exact ⟨hxP, fun w hw => h w hw (UCSAux.le_normalizer_zs P j hw)⟩
    · rintro ⟨hxP, h⟩
      exact ⟨hxP, UCSAux.le_normalizer_zs P j hxP, fun a ha _ => h a ha⟩

theorem upperCenterMod_sup {N A B C : Subgroup G} (hNA : N ≤ A) (hNB : N ≤ B)
    (hAN : A ≤ normalizer (N : Set G)) (hBN : B ≤ normalizer (N : Set G)) (hC : A ⊔ B = C)
    (hI : A ⊓ B = N) (hcomm : ⁅A, B⁆ ≤ N) (i : ℕ) :
    upperCenterMod N C i = upperCenterMod N A i ⊔ upperCenterMod N B i := by
  subst hC
  have hI' : NormalizerQuotient.bar N A ⊓ NormalizerQuotient.bar N B = ⊥ := by
    refine le_bot_iff.1 fun y hy => ?_
    obtain ⟨x, rfl⟩ := NormalizerQuotient.proj_surjective y
    have hxA := (NormalizerQuotient.mem_bar_iff hNA x).1 hy.1
    have hxB := (NormalizerQuotient.mem_bar_iff hNB x).1 hy.2
    have hxN : (x : G) ∈ N := hI.le (Subgroup.mem_inf.2 ⟨hxA, hxB⟩)
    exact Subgroup.mem_bot.2 (NormalizerQuotient.proj_eq_one_iff.2 hxN)
  have hc' : ∀ u ∈ NormalizerQuotient.bar N A, ∀ v ∈ NormalizerQuotient.bar N B,
      u * v = v * u := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := NormalizerQuotient.proj_surjective u
    obtain ⟨b, rfl⟩ := NormalizerQuotient.proj_surjective v
    have ha := (NormalizerQuotient.mem_bar_iff hNA a).1 hu
    have hb := (NormalizerQuotient.mem_bar_iff hNB b).1 hv
    have hab : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ N :=
      hcomm (Subgroup.commutator_mem_commutator ha hb)
    exact ((commutator_mem_iff_proj a.2 b.2).2 hab).symm
  have hbar : NormalizerQuotient.bar N (A ⊔ B) =
      NormalizerQuotient.bar N A ⊔ NormalizerQuotient.bar N B := by
    have hl : NormalizerQuotient.lift (NormalizerQuotient.bar N A ⊔ NormalizerQuotient.bar N B) =
        A ⊔ B := by
      rw [UCSAux.lift_sup, NormalizerQuotient.lift_bar hNA hAN,
        NormalizerQuotient.lift_bar hNB hBN]
    rw [← hl, NormalizerQuotient.bar_lift]
  rw [UCSAux.upperCenterMod_eq_lift_zs, UCSAux.upperCenterMod_eq_lift_zs,
    UCSAux.upperCenterMod_eq_lift_zs, hbar, UCSAux.zs_sup hI' hc' i, UCSAux.lift_sup]

end UCS

namespace SL2Aux

section Abstract

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup {H₁ H₂ : Subgroup G} (h : H₂ ≤ normalizer (H₁ : Set G)) {x : G}
    (hx : x ∈ H₁ ⊔ H₂) : ∃ a ∈ H₁, ∃ b ∈ H₂, x = a * b := by
  have hx' : x ∈ (↑(H₁ ⊔ H₂) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left H₁ H₂ h] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem le_normalizer_inf (A B : Subgroup G) :
    normalizer (A : Set G) ⊓ normalizer (B : Set G) ≤
      normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf, mem_normalizer_iff.1 hx.1 y, mem_normalizer_iff.1 hx.2 y]

theorem conj_mem_sup {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) {y : G} (hy : y ∈ A ⊔ B) : x * y * x⁻¹ ∈ A ⊔ B := by
  have h1 : A.map (MulAut.conj x).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.1 hA a).1 ha
  have h2 : B.map (MulAut.conj x).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.1 hB b).1 hb
  have h3 : (A ⊔ B).map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le_sup h1 h2
  exact h3 ⟨y, hy, rfl⟩

theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_sup hA hB, fun hy => ?_⟩
  have := conj_mem_sup (inv_mem hA) (inv_mem hB) hy
  simpa [mul_assoc] using this

theorem eq_ker_or_eq_top {X S : Type*} [Group X] [Group S] [IsSimpleGroup S] (φ : X →* S)
    (hφ : Function.Surjective φ) (M : Subgroup X) [hM : M.Normal] (hker : φ.ker ≤ M) :
    M = φ.ker ∨ M = ⊤ := by
  haveI : (M.map φ).Normal := hM.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map φ) with h | h
  · left
    refine le_antisymm (fun x hx => ?_) hker
    have hx' : φ x ∈ M.map φ := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact hx'
  · right
    have h2 : M ⊔ φ.ker = ⊤ := by rw [← Subgroup.comap_map_eq, h, Subgroup.comap_top]
    rwa [sup_eq_left.2 hker] at h2

theorem comm_mem_of_mul_mem {W D : Subgroup G} {k a a' : G} (hDW : D ≤ W)
    (hk : k ∈ normalizer (W : Set G)) (hw : a * a' ∈ W)
    (h2 : a * (k * a' * k⁻¹ * a'⁻¹) * a⁻¹ ∈ D) : k * a * k⁻¹ * a⁻¹ ∈ W := by
  have h3 : k * (a * a') * k⁻¹ ∈ W := (mem_normalizer_iff.1 hk _).1 hw
  have h4 : k * (a * a') * k⁻¹ * (a * a')⁻¹ ∈ W := mul_mem h3 (inv_mem hw)
  have h5 : (a * (k * a' * k⁻¹ * a'⁻¹) * a⁻¹)⁻¹ ∈ W := inv_mem (hDW h2)
  have e : k * a * k⁻¹ * a⁻¹ = (k * (a * a') * k⁻¹ * (a * a')⁻¹) *
      (a * (k * a' * k⁻¹ * a'⁻¹) * a⁻¹)⁻¹ := by group
  rw [e]
  exact mul_mem h4 h5

theorem map_eq_one_iff {X D' : Subgroup G} {T : Type*} [Group T] {φ : X →* T}
    (h : φ.ker = D'.subgroupOf X) (x : X) : φ x = 1 ↔ (x : G) ∈ D' := by
  rw [← MonoidHom.mem_ker, h, mem_subgroupOf]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {x : G} (h₁ : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (h₂ : ∀ h ∈ H, x⁻¹ * h * x ∈ H) : x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h₁ y, fun hy => ?_⟩
  have := h₂ _ hy
  simpa [mul_assoc] using this

theorem comm_prod_mem {D A A' P : Subgroup G} {k₁ k₂ k₁' k₂' : G} (hDA : D ≤ A) (hDA' : D ≤ A')
    (hA : A ≤ P) (hA' : A' ≤ P) (h12 : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ A)
    (h12' : k₁' * k₂' * k₁'⁻¹ * k₂'⁻¹ ∈ A') (h1_2' : k₁ * k₂' * k₁⁻¹ * k₂'⁻¹ ∈ D)
    (h1'_2 : k₁' * k₂ * k₁'⁻¹ * k₂⁻¹ ∈ D) (hD2 : ∀ d ∈ D, k₂ * d * k₂⁻¹ ∈ D)
    (hk1 : ∀ a ∈ A', k₁ * a * k₁⁻¹ ∈ A') (hk2 : ∀ a ∈ A', k₂ * a * k₂⁻¹ ∈ A') :
    (k₁ * k₁') * (k₂ * k₂') * (k₁ * k₁')⁻¹ * (k₂ * k₂')⁻¹ ∈ P := by
  have hT2 : k₁ * (k₂ * k₂') * k₁⁻¹ * (k₂ * k₂')⁻¹ ∈ P := by
    have e : k₁ * (k₂ * k₂') * k₁⁻¹ * (k₂ * k₂')⁻¹ =
        (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * (k₂ * (k₁ * k₂' * k₁⁻¹ * k₂'⁻¹) * k₂⁻¹) := by group
    rw [e]
    exact mul_mem (hA h12) (hA (hDA (hD2 _ h1_2')))
  have hT1 : k₁ * (k₁' * (k₂ * k₂') * k₁'⁻¹ * (k₂ * k₂')⁻¹) * k₁⁻¹ ∈ P := by
    have e : k₁' * (k₂ * k₂') * k₁'⁻¹ * (k₂ * k₂')⁻¹ =
        (k₁' * k₂ * k₁'⁻¹ * k₂⁻¹) * (k₂ * (k₁' * k₂' * k₁'⁻¹ * k₂'⁻¹) * k₂⁻¹) := by group
    have h3 : k₁' * (k₂ * k₂') * k₁'⁻¹ * (k₂ * k₂')⁻¹ ∈ A' := by
      rw [e]
      exact mul_mem (hDA' h1'_2) (hk2 _ h12')
    exact hA' (hk1 _ h3)
  have e : (k₁ * k₁') * (k₂ * k₂') * (k₁ * k₁')⁻¹ * (k₂ * k₂')⁻¹ =
      (k₁ * (k₁' * (k₂ * k₂') * k₁'⁻¹ * (k₂ * k₂')⁻¹) * k₁⁻¹) *
        (k₁ * (k₂ * k₂') * k₁⁻¹ * (k₂ * k₂')⁻¹) := by group
  rw [e]
  exact mul_mem hT1 hT2

end Abstract

section SLPart

open CFSG.GH74.GLS.IVK.Proofs2 (Qup Bor SL2 mem_Qup mem_Bor normalizer_Qup)
open CFSG.GH74.GLS.IVK.Proofs2 renaming upperSL → uSL, diagSL → dSL, coe_upperSL → coe_uSL,
  coe_diagSL → coe_dSL, upperSL_add → uSL_add, upperSL_zero → uSL_zero,
  conj_upperSL_of_mem_Bor → conj_uSL_of_mem_Bor, exists_conj_of_card_eq → exists_conj_card

variable {F : Type} [Field F]

theorem diagSL_mem_Bor (μ : Fˣ) : dSL μ ∈ Bor F := by
  rw [mem_Bor, coe_dSL]
  simp

theorem diagSL_conj_upperSL (μ : Fˣ) (c : F) :
    dSL μ * uSL c * (dSL μ)⁻¹ = uSL ((μ : F) ^ 2 * c) := by
  have := conj_uSL_of_mem_Bor (diagSL_mem_Bor μ) c
  simpa [coe_dSL] using this

theorem upperSL_inv (c : F) : (uSL c)⁻¹ = uSL (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [uSL_add, add_neg_cancel, uSL_zero])

@[expose] def borEntry (F : Type) [Field F] : Bor F →* F where
  toFun b := ((b : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0
  map_one' := by simp
  map_mul' a b := by
    have hb := mem_Bor.1 b.2
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb]

theorem commutator_mem_Qup {b₁ b₂ : SL2 F} (h₁ : b₁ ∈ Bor F) (h₂ : b₂ ∈ Bor F) :
    b₁ * b₂ * b₁⁻¹ * b₂⁻¹ ∈ Qup F := by
  set c : Bor F := ⟨b₁, h₁⟩ * ⟨b₂, h₂⟩ * ⟨b₁, h₁⟩⁻¹ * ⟨b₂, h₂⟩⁻¹ with hc
  have hcB : ((c : Bor F) : SL2 F) = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := rfl
  have hinv : ∀ b : Bor F, borEntry F b * borEntry F b⁻¹ = 1 := fun b => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have h00 : ((c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have : borEntry F c = 1 := by
      rw [hc, map_mul, map_mul, map_mul]
      calc borEntry F ⟨b₁, h₁⟩ * borEntry F ⟨b₂, h₂⟩ * borEntry F ⟨b₁, h₁⟩⁻¹ *
            borEntry F ⟨b₂, h₂⟩⁻¹
          = (borEntry F ⟨b₁, h₁⟩ * borEntry F ⟨b₁, h₁⟩⁻¹) *
            (borEntry F ⟨b₂, h₂⟩ * borEntry F ⟨b₂, h₂⟩⁻¹) := by ring
        _ = 1 := by rw [hinv, hinv, one_mul]
    exact this
  have h10 : ((c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := mem_Bor.1 c.2
  have hdet := (c : SL2 F).2
  rw [Matrix.det_fin_two, h00, h10] at hdet
  have h11 : ((c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by linear_combination hdet
  rw [← hcB, mem_Qup]
  refine ⟨((c : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, h00, h10, h11]

theorem exists_sq_eq [Finite F] [CharP F 2] (ν : Fˣ) : ∃ μ : Fˣ, μ ^ 2 = ν := by
  have hinj : Function.Injective (fun μ : Fˣ => μ ^ 2) := by
    intro μ ν h
    exact Units.ext (CharTwo.sq_injective (by simpa using congrArg Units.val h))
  exact (Finite.injective_iff_surjective.1 hinj) ν

theorem exists_unit_sq_ne_one [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    ∃ μ : Fˣ, (μ : F) ^ 2 ≠ 1 := by
  have h : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  haveI : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.1 h
  obtain ⟨ν, hν⟩ := exists_ne (1 : Fˣ)
  obtain ⟨μ, rfl⟩ := exists_sq_eq ν
  refine ⟨μ, fun h1 => hν ?_⟩
  exact Units.ext (by simpa using h1)

theorem card_eq_two_pow [Finite F] [CharP F 2] : ∃ n : ℕ, Nat.card F = 2 ^ n := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

structure QupData {G : Type} [Group G] (F : Type) [Field F] (D K A : Subgroup G)
    (ψ : K →* SL2 F) : Prop where
  le : A ≤ K
  surj : Function.Surjective ψ
  ker_eq : ψ.ker = D.subgroupOf K
  mem_iff : ∀ a : K, (a : G) ∈ A ↔ ψ a ∈ Qup F

section QupData

variable {G : Type} [Group G] {F : Type} [Field F] {D K A : Subgroup G} {ψ : K →* SL2 F}

theorem QupData.map_eq_one_iff (h : QupData F D K A ψ) (x : K) : ψ x = 1 ↔ (x : G) ∈ D :=
  SL2Aux.map_eq_one_iff h.ker_eq x

theorem QupData.conj_mem (h : QupData F D K A ψ) {k : K} (hk : ψ k ∈ Bor F) {x : K}
    (hx : (x : G) ∈ A) : (k : G) * x * (k : G)⁻¹ ∈ A := by
  have h1 : ψ x ∈ Qup F := (h.mem_iff x).1 hx
  have h2 : ψ k * ψ x * (ψ k)⁻¹ ∈ Qup F := by
    have := (mem_normalizer_iff.1 (normalizer_Qup (F := F) ▸ hk) (ψ x)).1 h1
    exact this
  rw [← map_inv, ← map_mul, ← map_mul] at h2
  exact (h.mem_iff (k * x * k⁻¹)).2 h2

theorem QupData.mem_normalizer_iff_mem_Bor (h : QupData F D K A ψ) (k : K) :
    (k : G) ∈ normalizer (A : Set G) ↔ ψ k ∈ Bor F := by
  constructor
  · intro hk
    rw [← normalizer_Qup, Subgroup.mem_normalizer_iff]
    intro t
    obtain ⟨z, rfl⟩ := h.surj t
    rw [← h.mem_iff z, ← map_inv, ← map_mul, ← map_mul, ← h.mem_iff (k * z * k⁻¹)]
    exact Subgroup.mem_normalizer_iff.1 hk z
  · intro hk
    refine SL2Aux.mem_normalizer_of_conj_mem (fun x hx => h.conj_mem hk (x := ⟨x, h.le hx⟩) hx)
      (fun x hx => ?_)
    have := h.conj_mem (k := k⁻¹) (by rw [map_inv]; exact inv_mem hk) (x := ⟨x, h.le hx⟩) hx
    simpa using this

theorem QupData.comm_mem (h : QupData F D K A ψ) {x y : K} (hx : ψ x ∈ Bor F)
    (hy : ψ y ∈ Bor F) : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ A := by
  have h1 : ψ (x * y * x⁻¹ * y⁻¹) ∈ Qup F := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_mem_Qup hx hy
  exact (h.mem_iff _).2 h1

theorem QupData.exists_torus (h : QupData F D K A ψ) (μ : Fˣ) :
    ∃ k : K, ψ k = dSL μ ∧ (k : G) ∈ normalizer (A : Set G) := by
  obtain ⟨k, hk⟩ := h.surj (dSL μ)
  refine ⟨k, hk, (h.mem_normalizer_iff_mem_Bor k).2 ?_⟩
  rw [hk]
  exact diagSL_mem_Bor μ

theorem QupData.le_of_comm [Finite F] [CharP F 2] (h : QupData F D K A ψ) (h4 : 4 ≤ Nat.card F)
    {W : Subgroup G} {a : G} (ha : a ∈ A) (haD : a ∉ D) (hDW : D ≤ W)
    (hW : ∀ k : K, ψ k ∈ Bor F → (k : G) ∈ normalizer (W : Set G))
    (hcomm : ∀ k : K, ψ k ∈ Bor F → (k : G) * a * (k : G)⁻¹ * a⁻¹ ∈ W) : A ≤ W := by
  have haK : a ∈ K := h.le ha
  obtain ⟨c, hc⟩ := mem_Qup.1 ((h.mem_iff ⟨a, haK⟩).1 ha)
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine haD ((h.map_eq_one_iff ⟨a, haK⟩).1 ?_)
    rw [hc, uSL_zero]
  obtain ⟨μ, hμ⟩ := exists_unit_sq_ne_one h4
  obtain ⟨k₀, hk₀, -⟩ := h.exists_torus μ
  have hk₀B : ψ k₀ ∈ Bor F := by rw [hk₀]; exact diagSL_mem_Bor μ
  have hzW : (k₀ : G) * a * (k₀ : G)⁻¹ * a⁻¹ ∈ W := hcomm k₀ hk₀B
  have hψz : ψ (k₀ * ⟨a, haK⟩ * k₀⁻¹ * ⟨a, haK⟩⁻¹) = uSL (((μ : F) ^ 2 - 1) * c) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk₀, hc, diagSL_conj_upperSL,
      upperSL_inv, uSL_add]
    congr 1
    ring
  have he : ((μ : F) ^ 2 - 1) * c ≠ 0 := mul_ne_zero (sub_ne_zero.2 hμ) hc0
  have hall : ∀ c' : F, ∃ y : K, (y : G) ∈ W ∧ ψ y = uSL c' := by
    intro c'
    by_cases hc' : c' = 0
    · exact ⟨1, one_mem _, by rw [hc', uSL_zero, map_one]⟩
    · obtain ⟨ν, hν⟩ := exists_sq_eq
        (Units.mk0 (c' / (((μ : F) ^ 2 - 1) * c)) (div_ne_zero hc' he))
      obtain ⟨k, hk, -⟩ := h.exists_torus ν
      have hkB : ψ k ∈ Bor F := by rw [hk]; exact diagSL_mem_Bor ν
      refine ⟨k * (k₀ * ⟨a, haK⟩ * k₀⁻¹ * ⟨a, haK⟩⁻¹) * k⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hW k hkB) _).1 hzW
      · rw [map_mul, map_mul, map_inv, hk, hψz, diagSL_conj_upperSL]
        congr 1
        have h1 : (ν : F) ^ 2 = c' / (((μ : F) ^ 2 - 1) * c) := by
          simpa using congrArg Units.val hν
        rw [h1]
        field_simp
  intro a₁ ha₁
  have ha₁K : a₁ ∈ K := h.le ha₁
  obtain ⟨c', hc'⟩ := mem_Qup.1 ((h.mem_iff ⟨a₁, ha₁K⟩).1 ha₁)
  obtain ⟨y, hyW, hy⟩ := hall c'
  have h1 : ψ (⟨a₁, ha₁K⟩ * y⁻¹) = 1 := by rw [map_mul, map_inv, hc', hy, mul_inv_cancel]
  have h2 : a₁ * (y : G)⁻¹ ∈ D := (h.map_eq_one_iff _).1 h1
  have e : a₁ = (a₁ * (y : G)⁻¹) * (y : G) := by group
  rw [e]
  exact mul_mem (hDW h2) hyW

theorem exists_qupData [Finite F] [CharP F 2] (hiso : IsQuotientIso K D SL(2, F))
    (hDA : D ≤ A) (hAK : A ≤ K) (hcard : D.relIndex A = Nat.card F) :
    ∃ ψ : K →* SL2 F, QupData F D K A ψ := by
  obtain ⟨φ, hφ, hker⟩ := hiso
  have hker' : φ.ker ≤ A.subgroupOf K := by
    rw [hker]
    intro x hx
    exact hDA hx
  have hAcard : Nat.card ((A.subgroupOf K).map φ) = Nat.card F := by
    have h1 := Subgroup.relIndex_map_map φ ⊥ (A.subgroupOf K)
    rw [Subgroup.map_bot, Subgroup.relIndex_bot_left, bot_sup_eq, sup_eq_left.2 hker', hker,
      Subgroup.relIndex_subgroupOf hAK] at h1
    rw [h1, hcard]
  obtain ⟨n, hn⟩ := card_eq_two_pow (F := F)
  obtain ⟨g, hg⟩ := exists_conj_card Nat.prime_two hn hAcard
  have hc : ((A.subgroupOf K).map φ).comap φ = A.subgroupOf K := by
    rw [Subgroup.comap_map_eq, sup_eq_left.2 hker']
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp φ, hAK, ?_, ?_, ?_⟩
  · exact (MulAut.conj g⁻¹).surjective.comp hφ
  · have : ((MulAut.conj g⁻¹).toMonoidHom.comp φ).ker = φ.ker := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this, hker]
  · intro a
    have h1 : (a : G) ∈ A ↔ φ a ∈ (A.subgroupOf K).map φ := by
      rw [← Subgroup.mem_comap, hc]
      exact Iff.rfl
    rw [h1, hg]
    simp [MulAut.conj_apply]

end QupData

end SLPart

end SL2Aux

section SL2

open CFSG.GH74.GLS.IVK.Proofs2 (Qup Bor SL2)

variable {G : Type} [Group G] [Finite G]

structure Sl2Pair (F : Type) [Field F] [Finite F] (N D K K' : Subgroup G) : Prop where
  charTwo : CharP F 2
  four_le : 4 ≤ Nat.card F
  sup_eq : K ⊔ K' = N
  inf_eq : K ⊓ K' = D
  comm_le : ⁅K, K'⁆ ≤ D
  isoK : IsQuotientIso K D SL(2, F)
  isoK' : IsQuotientIso K' D SL(2, F)

variable {F : Type} [Field F] [Finite F] {N D K K' : Subgroup G}

theorem Sl2Pair.symm (hS : Sl2Pair F N D K K') : Sl2Pair F N D K' K where
  charTwo := hS.charTwo
  four_le := hS.four_le
  sup_eq := by rw [sup_comm]; exact hS.sup_eq
  inf_eq := by rw [inf_comm]; exact hS.inf_eq
  comm_le := by rw [commutator_comm]; exact hS.comm_le
  isoK := hS.isoK'
  isoK' := hS.isoK

namespace SL2Aux

omit [Finite G] in
theorem D_le_left (hS : Sl2Pair F N D K K') : D ≤ K := by
  rw [← hS.inf_eq]; exact inf_le_left

omit [Finite G] in
theorem D_le_right (hS : Sl2Pair F N D K K') : D ≤ K' := by
  rw [← hS.inf_eq]; exact inf_le_right

omit [Finite G] in
theorem left_le (hS : Sl2Pair F N D K K') : K ≤ N := by
  rw [← hS.sup_eq]; exact le_sup_left

omit [Finite G] in
theorem right_le (hS : Sl2Pair F N D K K') : K' ≤ N := by
  rw [← hS.sup_eq]; exact le_sup_right

omit [Finite G] in
theorem comm_mem_D (hS : Sl2Pair F N D K K') {k' x : G} (hk' : k' ∈ K') (hx : x ∈ K) :
    k' * x * k'⁻¹ * x⁻¹ ∈ D := by
  have h := hS.comm_le
  rw [commutator_comm] at h
  have := h (commutator_mem_commutator hk' hx)
  rwa [commutatorElement_def] at this

omit [Finite G] in
theorem right_le_normalizer (hS : Sl2Pair F N D K K') : K' ≤ normalizer (K : Set G) := by
  have key : ∀ k' ∈ K', ∀ x ∈ K, k' * x * k'⁻¹ ∈ K := by
    intro k' hk' x hx
    have h2 := mul_mem (D_le_left hS (comm_mem_D hS hk' hx)) hx
    simpa [mul_assoc] using h2
  intro k' hk'
  refine mem_normalizer_of_conj_mem (key k' hk') (fun x hx => ?_)
  have := key k'⁻¹ (inv_mem hk') x hx
  simpa using this

end SL2Aux

theorem Sl2Pair.le_normalizer (hS : Sl2Pair F N D K K') : N ≤ normalizer (K : Set G) := by
  rw [← hS.sup_eq]
  exact sup_le Subgroup.le_normalizer (SL2Aux.right_le_normalizer hS)

namespace SL2Aux

theorem le_normalizer_D (hS : Sl2Pair F N D K K') : N ≤ normalizer (D : Set G) := by
  intro n hn
  have := le_normalizer_inf K K' ⟨hS.le_normalizer hn, hS.symm.le_normalizer hn⟩
  rwa [hS.inf_eq] at this

theorem eq_one_of_forall_comm [CharP F 2] (g : SL(2, F)) (h : ∀ s : SL(2, F), s * g = g * s) :
    g = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hg : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.2 h
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Fintype.card_fin] at hr
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

omit [Finite G] in
theorem D_ne_left (hS : Sl2Pair F N D K K') : D ≠ K := by
  haveI := hS.charTwo
  haveI := sl2_isSimpleGroup_of_charTwo hS.four_le
  obtain ⟨φ, hφ, hker⟩ := hS.isoK
  intro hDK
  obtain ⟨s, hs⟩ := exists_ne (1 : SL(2, F))
  obtain ⟨x, rfl⟩ := hφ s
  apply hs
  rw [map_eq_one_iff hker, hDK]
  exact x.2

omit [Finite G] in
theorem eq_or_eq_left (hS : Sl2Pair F N D K K') {L : Subgroup G} (hDL : D ≤ L) (hLK : L ≤ K)
    (hKL : K ≤ normalizer (L : Set G)) : L = D ∨ L = K := by
  haveI := hS.charTwo
  haveI := sl2_isSimpleGroup_of_charTwo hS.four_le
  obtain ⟨φ, hφ, hker⟩ := hS.isoK
  haveI : (L.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hLK).2 hKL
  have hker' : φ.ker ≤ L.subgroupOf K := by
    rw [hker]
    intro x hx
    exact hDL hx
  rcases eq_ker_or_eq_top φ hφ (L.subgroupOf K) hker' with h | h
  · left
    rw [hker] at h
    have := subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hLK, inf_eq_left.2 (D_le_left hS)] at this
  · right
    exact le_antisymm hLK (subgroupOf_eq_top.1 h)

omit [Finite G] in
theorem mem_D_of_comm (hS : Sl2Pair F N D K K') {k : G} (hk : k ∈ K)
    (h : ∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ D) : k ∈ D := by
  haveI := hS.charTwo
  obtain ⟨φ, hφ, hker⟩ := hS.isoK
  refine (map_eq_one_iff hker ⟨k, hk⟩).1 ?_
  apply eq_one_of_forall_comm
  intro s
  obtain ⟨x, rfl⟩ := hφ s
  have h1 := (map_eq_one_iff hker (⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹ * x⁻¹)).2 (h x x.2)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc φ x * φ ⟨k, hk⟩
      = (φ ⟨k, hk⟩ * φ x * (φ ⟨k, hk⟩)⁻¹ * (φ x)⁻¹)⁻¹ * (φ ⟨k, hk⟩ * φ x) := by group
    _ = φ ⟨k, hk⟩ * φ x := by rw [h1]; simp

theorem mem_right_of_comm (hS : Sl2Pair F N D K K') {n : G} (hn : n ∈ N)
    (h : ∀ x ∈ K, n * x * n⁻¹ * x⁻¹ ∈ D) : n ∈ K' := by
  have hn' : n ∈ K ⊔ K' := hS.sup_eq ▸ hn
  obtain ⟨k, hk, k', hk', rfl⟩ := exists_mul_of_mem_sup (right_le_normalizer hS) hn'
  have hkD : k ∈ D := by
    refine mem_D_of_comm hS hk fun x hx => ?_
    have h1 := comm_mem_D hS hk' hx
    have h2 : k * (k' * x * k'⁻¹ * x⁻¹) * k⁻¹ ∈ D :=
      (mem_normalizer_iff.1 (le_normalizer_D hS (left_le hS hk)) _).1 h1
    have e : k * x * k⁻¹ * x⁻¹ = (k * (k' * x * k'⁻¹ * x⁻¹) * k⁻¹)⁻¹ *
        ((k * k') * x * (k * k')⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem h2) (h x hx)
  exact mul_mem (D_le_right hS hkD) hk'

end SL2Aux

theorem Sl2Pair.ne (hS : Sl2Pair F N D K K') : K ≠ K' := by
  intro h
  apply SL2Aux.D_ne_left hS
  rw [← hS.inf_eq, ← h, inf_idem]

theorem Sl2Pair.conj_factor (hS : Sl2Pair F N D K K') {g : G} (hgN : g ∈ normalizer (N : Set G))
    (hgD : g ∈ normalizer (D : Set G)) :
    K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = K' := by
  generalize hL : K.map (MulAut.conj g).toMonoidHom = L
  have hmemL : ∀ x, x ∈ L ↔ g⁻¹ * x * g ∈ K := fun x => by
    rw [← hL, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hcard : Nat.card L = Nat.card K := by
    rw [← hL]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hDL : D ≤ L := by
    intro d hd
    rw [hmemL]
    exact SL2Aux.D_le_left hS ((mem_normalizer_iff''.1 hgD d).1 hd)
  have hLN : L ≤ N := by
    intro x hx
    rw [hmemL] at hx
    have := (mem_normalizer_iff.1 hgN _).1 (SL2Aux.left_le hS hx)
    simpa [mul_assoc] using this
  have hNL : N ≤ normalizer (L : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro x
    rw [hmemL, hmemL]
    have hn' : g⁻¹ * n * g ∈ N := (mem_normalizer_iff''.1 hgN n).1 hn
    have h1 := mem_normalizer_iff.1 (hS.le_normalizer hn') (g⁻¹ * x * g)
    have e : (g⁻¹ * n * g) * (g⁻¹ * x * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * x * n⁻¹) * g := by
      group
    rw [e] at h1
    exact h1
  have hLK_norm : K ≤ normalizer ((L ⊓ K : Subgroup G) : Set G) := fun k hk =>
    SL2Aux.le_normalizer_inf L K ⟨hNL (SL2Aux.left_le hS hk), Subgroup.le_normalizer hk⟩
  rcases SL2Aux.eq_or_eq_left hS (L := L ⊓ K) (le_inf hDL (SL2Aux.D_le_left hS)) inf_le_right
      hLK_norm with h | h
  · right
    have hcomm : ∀ x ∈ K, ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ D := by
      intro x hx l hl
      rw [← h]
      refine mem_inf.2 ⟨?_, ?_⟩
      · have h1 := (mem_normalizer_iff.1 (hNL (SL2Aux.left_le hS hx)) l⁻¹).1 (inv_mem hl)
        have h2 := mul_mem hl h1
        simpa [mul_assoc] using h2
      · have h1 := (mem_normalizer_iff.1 (hS.le_normalizer (hLN hl)) x).1 hx
        exact mul_mem h1 (inv_mem hx)
    have hLK' : L ≤ K' := fun l hl =>
      SL2Aux.mem_right_of_comm hS (hLN hl) fun x hx => hcomm x hx l hl
    have hK'L : K' ≤ normalizer (L : Set G) := fun k' hk' => hNL (SL2Aux.right_le hS hk')
    rcases SL2Aux.eq_or_eq_left hS.symm hDL hLK' hK'L with h2 | h2
    · exfalso
      refine SL2Aux.D_ne_left hS (Subgroup.eq_of_le_of_card_ge (SL2Aux.D_le_left hS) ?_)
      rw [← hcard, h2]
    · exact h2
  · left
    have hKL : K ≤ L := inf_eq_right.1 h
    exact (Subgroup.eq_of_le_of_card_ge hKL hcard.le).symm

theorem Sl2Pair.relIndex_sylow (hS : Sl2Pair F N D K K') {P : Subgroup G}
    (hP : IsSylowOf 2 P N) (hDP : D ≤ P) : D.relIndex (P ⊓ K) = Nat.card F := by
  haveI := hS.charTwo
  obtain ⟨φ, hφ, hker⟩ := hS.isoK
  have hDK := SL2Aux.D_le_left hS
  have hA : IsSylowOf 2 (P ⊓ K) K :=
    hP.inf_of_le_normalizer (SL2Aux.left_le hS) hS.le_normalizer
  have hAc := hA.card_eq
  have hKc : Nat.card K = Nat.card D * Nat.card SL(2, F) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hker] at h1
    rw [h1, mul_comm]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hP.isPGroup.to_le hDP)
  obtain ⟨m, hm⟩ := SL2Aux.card_eq_two_pow (F := F)
  have hSL := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  obtain ⟨u, hu_def⟩ : ∃ u, u = Nat.card F ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hu_def] at hSL
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := hS.four_le
    rw [hm] at this
    norm_num at this
  have hu : ¬ 2 ∣ u := by
    intro hd
    have h2q : 2 ∣ Nat.card F ^ 2 := by
      rw [hm, ← pow_mul]
      exact dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have h3 : 2 ∣ u + 1 := by rw [hu_def, Nat.sub_add_cancel h1]; exact h2q
    have := (Nat.dvd_add_right hd).1 h3
    omega
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero 2)
  have hKfac : Nat.card K = 2 ^ (a + m) * u := by
    rw [hKc, hSL, ha, pow_add, ← hm]
    ring
  have hfac : (Nat.card K).factorization 2 = a + m := by
    rw [hKfac, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hu0]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hu]
  have hAc' : Nat.card (P ⊓ K : Subgroup G) = 2 ^ (a + m) := by rw [hAc, hfac]
  have hrel := Subgroup.relIndex_mul_card D (P ⊓ K)
  rw [inf_eq_left.2 (le_inf hDP hDK), ha, hAc', pow_add] at hrel
  have h5 : D.relIndex (P ⊓ K) = 2 ^ m := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos two_pos a)
    rw [hrel, mul_comm]
  rw [h5, hm]

namespace SL2Aux

omit [Finite G] in
theorem right_mem_normalizer_inf (hS : Sl2Pair F N D K K') {P : Subgroup G} (hDP : D ≤ P)
    {k' : G} (hk' : k' ∈ K') : k' ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) := by
  have key : ∀ k' ∈ K', ∀ a ∈ P ⊓ K, k' * a * k'⁻¹ ∈ P ⊓ K := by
    intro k' hk' a ha
    have hD := comm_mem_D hS hk' ha.2
    have h1 : k' * a * k'⁻¹ * a⁻¹ ∈ P ⊓ K := mem_inf.2 ⟨hDP hD, D_le_left hS hD⟩
    simpa using mul_mem h1 ha
  refine mem_normalizer_of_conj_mem (key k' hk') (fun a ha => ?_)
  simpa using key k'⁻¹ (inv_mem hk') a ha

theorem exists_qupData_sylow (hS : Sl2Pair F N D K K') {P : Subgroup G} (hP : IsSylowOf 2 P N)
    (hDP : D ≤ P) : ∃ ψ : K →* SL2 F, QupData F D K (P ⊓ K) ψ := by
  haveI := hS.charTwo
  exact exists_qupData hS.isoK (le_inf hDP (D_le_left hS)) inf_le_right
    (hS.relIndex_sylow hP hDP)

theorem factor_mem_normalizer_left (hS : Sl2Pair F N D K K') {P : Subgroup G} (hDP : D ≤ P)
    {k k' : G} (hk' : k' ∈ K') (hm : k * k' ∈ N ⊓ normalizer (P : Set G)) :
    k ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) := by
  have h1 : k * k' ∈ normalizer ((P ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_inf P K ⟨hm.2, hS.le_normalizer hm.1⟩
  have h2 := right_mem_normalizer_inf hS hDP hk'
  simpa using mul_mem h1 (inv_mem h2)

theorem factor_mem_normalizer_right (hS : Sl2Pair F N D K K') {P : Subgroup G} (hDP : D ≤ P)
    {k k' : G} (hk : k ∈ K) (hm : k * k' ∈ N ⊓ normalizer (P : Set G)) :
    k' ∈ normalizer ((P ⊓ K' : Subgroup G) : Set G) := by
  have h1 : k * k' ∈ normalizer ((P ⊓ K' : Subgroup G) : Set G) :=
    le_normalizer_inf P K' ⟨hm.2, hS.symm.le_normalizer hm.1⟩
  have h2 := right_mem_normalizer_inf hS.symm hDP hk
  simpa using mul_mem (inv_mem h2) h1

theorem claim_left (hS : Sl2Pair F N D K K') {P W : Subgroup G} (hP : IsSylowOf 2 P N)
    (hDP : D ≤ P) (hDW : D ≤ W) (hWP : W ≤ P) (hPeq : P = (P ⊓ K) ⊔ (P ⊓ K'))
    (hinv : N ⊓ normalizer (P : Set G) ≤ normalizer (W : Set G)) :
    ¬ W ≤ P ⊓ K' → P ⊓ K ≤ W := by
  haveI := hS.charTwo
  obtain ⟨ψ, hψ⟩ := exists_qupData_sylow hS hP hDP
  intro hWA'
  obtain ⟨w, hwW, hwA'⟩ := Set.not_subset.1 hWA'
  have hPK' : P ⊓ K' ≤ normalizer ((P ⊓ K : Subgroup G) : Set G) := fun a' ha' =>
    right_mem_normalizer_inf hS hDP ha'.2
  have hwP : w ∈ (P ⊓ K) ⊔ (P ⊓ K') := hPeq ▸ hWP hwW
  obtain ⟨a, ha, a', ha', rfl⟩ := exists_mul_of_mem_sup hPK' hwP
  have haD : a ∉ D := fun hD => hwA' (mul_mem (mem_inf.2 ⟨hDP hD, D_le_right hS hD⟩) ha')
  have hnorm : ∀ k : K, ψ k ∈ Bor F → (k : G) ∈ normalizer (W : Set G) := by
    intro k hk
    refine hinv ⟨left_le hS k.2, ?_⟩
    have h1 := (hψ.mem_normalizer_iff_mem_Bor k).2 hk
    have h2 : (k : G) ∈ normalizer ((P ⊓ K' : Subgroup G) : Set G) :=
      right_mem_normalizer_inf hS.symm hDP k.2
    have h3 := mem_normalizer_sup h1 h2
    rwa [← hPeq] at h3
  refine hψ.le_of_comm hS.four_le ha haD hDW hnorm fun k hk => ?_
  have h1 := comm_mem_D hS.symm k.2 ha'.2
  have h2 : a * ((k : G) * a' * (k : G)⁻¹ * a'⁻¹) * a⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_D hS (left_le hS (ha.2))) _).1 h1
  exact comm_mem_of_mul_mem hDW (hnorm k hk) hwW h2

end SL2Aux

theorem Sl2Pair.comm_mem_normalizer (hS : Sl2Pair F N D K K') {P : Subgroup G}
    (hP : IsSylowOf 2 P N) (hDP : D ≤ P) :
    ∀ x ∈ N ⊓ normalizer (P : Set G), ∀ y ∈ N ⊓ normalizer (P : Set G),
      x * y * x⁻¹ * y⁻¹ ∈ P := by
  intro x hx y hy
  obtain ⟨ψ, hψ⟩ := SL2Aux.exists_qupData_sylow hS hP hDP
  obtain ⟨ψ', hψ'⟩ := SL2Aux.exists_qupData_sylow hS.symm hP hDP
  have hx' : x ∈ K ⊔ K' := hS.sup_eq ▸ hx.1
  have hy' : y ∈ K ⊔ K' := hS.sup_eq ▸ hy.1
  obtain ⟨k₁, hk₁, k₁', hk₁', rfl⟩ :=
    SL2Aux.exists_mul_of_mem_sup (SL2Aux.right_le_normalizer hS) hx'
  obtain ⟨k₂, hk₂, k₂', hk₂', rfl⟩ :=
    SL2Aux.exists_mul_of_mem_sup (SL2Aux.right_le_normalizer hS) hy'
  have h1n := SL2Aux.factor_mem_normalizer_left hS hDP hk₁' hx
  have h2n := SL2Aux.factor_mem_normalizer_left hS hDP hk₂' hy
  have h1n' := SL2Aux.factor_mem_normalizer_right hS hDP hk₁ hx
  have h2n' := SL2Aux.factor_mem_normalizer_right hS hDP hk₂ hy
  have hB1 : ψ ⟨k₁, hk₁⟩ ∈ Bor F := (hψ.mem_normalizer_iff_mem_Bor ⟨k₁, hk₁⟩).1 h1n
  have hB2 : ψ ⟨k₂, hk₂⟩ ∈ Bor F := (hψ.mem_normalizer_iff_mem_Bor ⟨k₂, hk₂⟩).1 h2n
  have hB1' : ψ' ⟨k₁', hk₁'⟩ ∈ Bor F := (hψ'.mem_normalizer_iff_mem_Bor ⟨k₁', hk₁'⟩).1 h1n'
  have hB2' : ψ' ⟨k₂', hk₂'⟩ ∈ Bor F := (hψ'.mem_normalizer_iff_mem_Bor ⟨k₂', hk₂'⟩).1 h2n'
  exact SL2Aux.comm_prod_mem (A := P ⊓ K) (A' := P ⊓ K') (D := D)
    (le_inf hDP (SL2Aux.D_le_left hS)) (le_inf hDP (SL2Aux.D_le_right hS)) inf_le_left
    inf_le_left (hψ.comm_mem hB1 hB2) (hψ'.comm_mem hB1' hB2')
    (SL2Aux.comm_mem_D hS.symm hk₁ hk₂') (SL2Aux.comm_mem_D hS hk₁' hk₂)
    (fun d hd => (mem_normalizer_iff.1
      (SL2Aux.le_normalizer_D hS (SL2Aux.left_le hS hk₂)) d).1 hd)
    (fun a ha => (mem_normalizer_iff.1
      (SL2Aux.right_mem_normalizer_inf hS.symm hDP hk₁) a).1 ha)
    (fun a ha => (mem_normalizer_iff.1
      (SL2Aux.right_mem_normalizer_inf hS.symm hDP hk₂) a).1 ha)

theorem Sl2Pair.invariant (hS : Sl2Pair F N D K K') {P W : Subgroup G}
    (hP : IsSylowOf 2 P N) (hDP : D ≤ P) (hDW : D ≤ W) (hWP : W ≤ P)
    (hinv : N ⊓ normalizer (P : Set G) ≤ normalizer (W : Set G)) :
    W = D ∨ W = P ⊓ K ∨ W = P ⊓ K' ∨ W = P := by
  obtain ⟨-, -, hPeq, hAA', -⟩ := sylow_prod hP hS.sup_eq hS.inf_eq hS.comm_le hDP
  have h1 := SL2Aux.claim_left hS hP hDP hDW hWP hPeq hinv
  have h2 := SL2Aux.claim_left hS.symm hP hDP hDW hWP (hPeq.trans (sup_comm _ _)) hinv
  by_cases hA' : W ≤ P ⊓ K'
  · by_cases hA : W ≤ P ⊓ K
    · left
      have h3 : W ≤ (P ⊓ K) ⊓ (P ⊓ K') := le_inf hA hA'
      rw [hAA'] at h3
      exact le_antisymm h3 hDW
    · right; right; left
      exact le_antisymm hA' (h2 hA)
  · by_cases hA : W ≤ P ⊓ K
    · right; left
      exact le_antisymm hA (h1 hA')
    · right; right; right
      exact le_antisymm hWP (hPeq.le.trans (sup_le (h1 hA') (h2 hA)))

end SL2

section Delta

variable {G : Type*} [Group G]

theorem delta_facts {N Q S : Subgroup G} {t : G}
    (hQN : Q ≤ normalizer (N : Set G))
    (hQt : ∀ x ∈ Q, t⁻¹ * x * t ∈ normalizer (N : Set G))
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, y * (t⁻¹ * x * t) * y⁻¹ * (t⁻¹ * x * t)⁻¹ ∈ N)
    (hSN : S ≤ normalizer (N : Set G))
    (hΔ1 : ∀ x ∈ Q, x * (t⁻¹ * x * t) ∈ S ⊔ N)
    (hΔ2 : ∀ x ∈ Q, x * (t⁻¹ * x * t) ∈ N → x ∈ N) :
    (∀ Q' : Subgroup G, Q' ≤ Q → (∀ s ∈ S, ∃ x ∈ Q', s * (x * (t⁻¹ * x * t))⁻¹ ∈ N) →
        Q ≤ Q' ⊔ N) ∧
    ((∀ s ∈ S, ∃ x ∈ Q, s * (x * (t⁻¹ * x * t))⁻¹ ∈ N) →
      ∀ y ∈ Q, y * (t⁻¹ * y * t) ∈ ⁅S, S⁆ ⊔ N → y ∈ ⁅Q, Q⁆ ⊔ N) := by
  set Nn : Subgroup G := normalizer (N : Set G) with hNn
  let π := NormalizerQuotient.proj N
  let ι : ↥Q →* ↥Nn := Subgroup.inclusion hQN
  let κ : ↥Q →* ↥Nn := MonoidHom.mk' (fun x => ⟨t⁻¹ * (x : G) * t, hQt x x.2⟩)
    (fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group))
  let α : ↥Q →* NormalizerQuotient.Bar N := π.comp ι
  let β : ↥Q →* NormalizerQuotient.Bar N := π.comp κ
  have hαβ : ∀ x y : ↥Q, β x * α y = α y * β x := fun x y =>
    (commutator_mem_iff_proj (N := N) (g := (y : G)) (b := t⁻¹ * (x : G) * t)
      (hQN y.2) (hQt x x.2)).2 (hcomm x x.2 y y.2)
  let ψ : ↥Q →* NormalizerQuotient.Bar N := MonoidHom.mk' (fun x => α x * β x) (fun x y => by
    simp only [map_mul]
    calc α x * α y * (β x * β y) = α x * (α y * β x) * β y := by group
      _ = α x * (β x * α y) * β y := by rw [← hαβ x y]
      _ = α x * β x * (α y * β y) := by group)
  have hψ : ∀ (x : ↥Q) (hx : (x : G) * (t⁻¹ * x * t) ∈ Nn),
      ψ x = π ⟨(x : G) * (t⁻¹ * x * t), hx⟩ := fun x hx => by
    change π (ι x) * π (κ x) = _
    rw [← map_mul]
    rfl
  have hmem : ∀ x : ↥Q, (x : G) * (t⁻¹ * x * t) ∈ Nn := fun x =>
    Subgroup.mul_mem _ (hQN x.2) (hQt x x.2)
  have hker : ∀ x : ↥Q, ψ x = 1 → (x : G) ∈ N := fun x hx => by
    rw [hψ x (hmem x), NormalizerQuotient.proj_eq_one_iff] at hx
    exact hΔ2 x x.2 hx
  have hπ : ∀ (a b : ↥Nn), (a : G)⁻¹ * b ∈ N → π a = π b := fun a b h =>
    NormalizerQuotient.proj_eq_proj_iff.2 h
  have hcov : ∀ (s : ↥Nn) (y : ↥Q), (s : G) * ((y : G) * (t⁻¹ * y * t))⁻¹ ∈ N →
      π s = ψ y := fun s y h => by
    rw [hψ y (hmem y)]
    apply hπ
    have h1 : ((y : G) * (t⁻¹ * y * t)) * (s : G)⁻¹ ∈ N := by
      have := Subgroup.inv_mem _ h
      simpa using this
    have h2 := (mem_normalizer_iff.1 (Subgroup.inv_mem _ s.2) _).1 h1
    have e : (s : G)⁻¹ * ((y : G) * (t⁻¹ * y * t)) =
        (s : G)⁻¹ * (((y : G) * (t⁻¹ * y * t)) * (s : G)⁻¹) * (s : G)⁻¹⁻¹ := by group
    show (s : G)⁻¹ * ((y : G) * (t⁻¹ * y * t)) ∈ N
    rw [e]
    exact h2
  refine ⟨?_, ?_⟩
  ·
    intro Q' hQ'Q hQ'cov x hx
    obtain ⟨s, hs, n, hn, hxs⟩ := (mem_sup_iff_of_le_normalizer hSN).1 (hΔ1 x hx)
    obtain ⟨y, hy, hyN⟩ := hQ'cov s hs
    have h1 : ψ ⟨x, hx⟩ = ψ ⟨y, hQ'Q hy⟩ := by
      rw [hψ ⟨x, hx⟩ (hmem _), ← hcov ⟨s, hSN hs⟩ ⟨y, hQ'Q hy⟩ hyN]
      apply hπ
      show ((x : G) * (t⁻¹ * x * t))⁻¹ * s ∈ N
      rw [hxs]
      have e : (s * n)⁻¹ * s = n⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hn
    have h2 : ((⟨y, hQ'Q hy⟩ : ↥Q)⁻¹ * ⟨x, hx⟩ : ↥Q) ∈ (ψ.ker) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : y⁻¹ * x ∈ N := hker _ h2
    have e : x = y * (y⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hy h3
  ·
    intro hcovQ y hy hyF
    have hS'N : ⁅S, S⁆ ≤ normalizer (N : Set G) := commutator_le_of_le hSN hSN
    obtain ⟨s', hs', n', hn', hys⟩ := (mem_sup_iff_of_le_normalizer hS'N).1 hyF
    set Sn : Subgroup ↥Nn := S.subgroupOf Nn with hSn
    have hSS : ⁅S, S⁆ = (⁅Sn, Sn⁆).map Nn.subtype := by
      rw [Subgroup.map_commutator, hSn, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSN]
    have hbS : NormalizerQuotient.bar N S ≤ ψ.range := by
      rintro z ⟨w, hw, rfl⟩
      obtain ⟨x, hx, hxN⟩ := hcovQ (w : G) (Subgroup.mem_subgroupOf.1 hw)
      exact ⟨⟨x, hx⟩, (hcov w ⟨x, hx⟩ hxN).symm⟩
    have h1 : π ⟨s', hS'N hs'⟩ ∈ ⁅ψ.range, ψ.range⁆ := by
      have h2 : (⟨s', hS'N hs'⟩ : ↥Nn) ∈ ⁅Sn, Sn⁆ := by
        have : s' ∈ (⁅Sn, Sn⁆).map Nn.subtype := hSS ▸ hs'
        obtain ⟨w, hw, hws⟩ := this
        have : w = ⟨s', hS'N hs'⟩ := Subtype.ext hws
        exact this ▸ hw
      have h3 : π ⟨s', hS'N hs'⟩ ∈ (⁅Sn, Sn⁆).map π := ⟨_, h2, rfl⟩
      rw [Subgroup.map_commutator] at h3
      exact Subgroup.commutator_mono hbS hbS h3
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator] at h1
    obtain ⟨c, hc, hcs⟩ := h1
    have h4 : ψ c = ψ ⟨y, hy⟩ := by
      rw [hcs, hψ ⟨y, hy⟩ (hmem _)]
      apply hπ
      show (s')⁻¹ * ((y : G) * (t⁻¹ * y * t)) ∈ N
      rw [hys]
      have e : s'⁻¹ * (s' * n') = n' := by group
      rw [e]
      exact hn'
    have h5 : (c⁻¹ * ⟨y, hy⟩ : ↥Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h4, inv_mul_cancel]
    have h6 : (c : G)⁻¹ * y ∈ N := hker _ h5
    have h7 : (c : G) ∈ ⁅Q, Q⁆ := by
      have : ((⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆).map Q.subtype) = ⁅Q, Q⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← this]
      exact ⟨c, hc, rfl⟩
    have e : y = (c : G) * ((c : G)⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem_sup h7 h6

theorem commutator_le_of_sup_of_comm {U R F : Subgroup G} (hRU : R ≤ U)
    (hUR : U ≤ normalizer (R : Set G)) (hFU : F ≤ U) (hRF : R ≤ normalizer (F : Set G))
    (hsup : U ≤ R ⊔ F) (hFF : ∀ a ∈ F, ∀ b ∈ F, a * b * a⁻¹ * b⁻¹ ∈ R) : ⁅U, U⁆ ≤ R := by
  haveI : (R.subgroupOf U).Normal := (normal_subgroupOf_iff_le_normalizer hRU).2 hUR
  let φ : ↥U →* ↥U ⧸ R.subgroupOf U := QuotientGroup.mk' _
  have hφ : ∀ x : ↥U, φ x = 1 ↔ (x : G) ∈ R := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨r₁, hr₁, f₁, hf₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hRF).1 (hsup ha)
  obtain ⟨r₂, hr₂, f₂, hf₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hRF).1 (hsup hb)
  have h1 : φ ⟨r₁ * f₁, ha⟩ = φ ⟨f₁, hFU hf₁⟩ := by
    have : (⟨r₁ * f₁, ha⟩ : ↥U) = ⟨r₁, hRU hr₁⟩ * ⟨f₁, hFU hf₁⟩ := rfl
    rw [this, map_mul, (hφ _).2 hr₁, one_mul]
  have h2 : φ ⟨r₂ * f₂, hb⟩ = φ ⟨f₂, hFU hf₂⟩ := by
    have : (⟨r₂ * f₂, hb⟩ : ↥U) = ⟨r₂, hRU hr₂⟩ * ⟨f₂, hFU hf₂⟩ := rfl
    rw [this, map_mul, (hφ _).2 hr₂, one_mul]
  have h3 : φ ⟨f₁, hFU hf₁⟩ * φ ⟨f₂, hFU hf₂⟩ * (φ ⟨f₁, hFU hf₁⟩)⁻¹ * (φ ⟨f₂, hFU hf₂⟩)⁻¹ = 1 := by
    have := (hφ (⟨f₁, hFU hf₁⟩ * ⟨f₂, hFU hf₂⟩ * ⟨f₁, hFU hf₁⟩⁻¹ * ⟨f₂, hFU hf₂⟩⁻¹)).2
      (hFF f₁ hf₁ f₂ hf₂)
    simpa only [map_mul, map_inv] using this
  have h4 : φ ⟨(r₁ * f₁) * (r₂ * f₂) * (r₁ * f₁)⁻¹ * (r₂ * f₂)⁻¹, Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)⟩ = 1 := by
    have : (⟨(r₁ * f₁) * (r₂ * f₂) * (r₁ * f₁)⁻¹ * (r₂ * f₂)⁻¹, Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)⟩ : ↥U) = ⟨r₁ * f₁, ha⟩ * ⟨r₂ * f₂, hb⟩ * ⟨r₁ * f₁, ha⟩⁻¹ *
          ⟨r₂ * f₂, hb⟩⁻¹ := rfl
    rw [this]
    simp only [map_mul, map_inv, h1, h2]
    exact h3
  exact (hφ _).1 h4

theorem mem_of_fixed_mod [Finite G] {U R F J : Subgroup G}
    (hRU : R ≤ U) (hFU : F ≤ U) (hsup : U ≤ R ⊔ F)
    (hUR : U ≤ normalizer (R : Set G)) (hRF : R ≤ normalizer (F : Set G))
    (hJR : J ≤ normalizer (R : Set G)) (hJF : J ≤ normalizer (F : Set G))
    (hU2 : IsPGroup 2 U) (hJ : Odd (Nat.card J))
    (hfix : F ⊓ centralizer (J : Set G) ≤ R) :
    ∀ x ∈ U, (∀ s ∈ J, x⁻¹ * (s * x * s⁻¹) ∈ R) → x ∈ R := by
  intro x hx hfixx
  have hUeq : U = R ⊔ F := le_antisymm hsup (sup_le hRU hFU)
  have hJU : J ≤ normalizer (U : Set G) := by
    rw [hUeq]
    intro g hg
    exact Common.mem_normalizer_sup (hJR hg) (hJF hg)
  have hcop : ∀ X : Subgroup G, IsPGroup 2 X → (Nat.card J).Coprime (Nat.card X) := fun X hX => by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥X)).1 hX
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hJ)
  have hR2 : IsPGroup 2 R := hU2.to_le hRU
  haveI : Group.IsNilpotent ↥U := hU2.isNilpotent
  haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime hRU hUR hJU hJR
    inferInstance (hcop U hU2) hx hfixx
  have hcR : c ∈ R := by
    obtain ⟨hcU, hcC⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨r, hr, f, hf, hcrf⟩ := (mem_sup_iff_of_le_normalizer hRF).1 (hsup hcU)
    have hrfix : ∀ s ∈ J, r⁻¹ * (s * r * s⁻¹) ∈ R ⊓ F := by
      intro s hs
      have hsr : s * r * s⁻¹ ∈ R := (mem_normalizer_iff.1 (hJR hs) r).1 hr
      have hsf : s * f * s⁻¹ ∈ F := (mem_normalizer_iff.1 (hJF hs) f).1 hf
      have hcs : s * c = c * s := mem_centralizer_iff.1 hcC s hs
      have e : r⁻¹ * (s * r * s⁻¹) = f * (s * f * s⁻¹)⁻¹ := by
        have h1 : s * (r * f) * s⁻¹ = r * f := by
          rw [← hcrf]
          calc s * c * s⁻¹ = c * s * s⁻¹ := by rw [hcs]
            _ = c := by group
        have h2 : s * (r * f) * s⁻¹ = (s * r * s⁻¹) * (s * f * s⁻¹) := by group
        rw [h2] at h1
        calc r⁻¹ * (s * r * s⁻¹)
            = r⁻¹ * ((s * r * s⁻¹) * (s * f * s⁻¹)) * (s * f * s⁻¹)⁻¹ := by group
          _ = r⁻¹ * (r * f) * (s * f * s⁻¹)⁻¹ := by rw [h1]
          _ = f * (s * f * s⁻¹)⁻¹ := by group
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hr) hsr, ?_⟩
      rw [e]
      exact mul_mem hf (inv_mem hsf)
    obtain ⟨c', hc', n', hn', hrc⟩ := exists_mem_inf_centralizer_mul_of_coprime (M := R)
      (N := R ⊓ F) (S := J) inf_le_left
      (fun y hy => Common.mem_normalizer_inf (le_normalizer hy) (hRF hy)) hJR
      (fun s hs => Common.mem_normalizer_inf (hJR hs) (hJF hs)) inferInstance (hcop R hR2) hr
      hrfix
    obtain ⟨hc'R, hc'C⟩ := Subgroup.mem_inf.1 hc'
    obtain ⟨hn'R, hn'F⟩ := Subgroup.mem_inf.1 hn'
    have hnf : n' * f ∈ F ⊓ centralizer (J : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem hn'F hf, ?_⟩
      have : n' * f = c'⁻¹ * c := by
        rw [hcrf, hrc]
        group
      rw [this]
      exact mul_mem (inv_mem hc'C) hcC
    have e : c = c' * (n' * f) := by
      rw [hcrf, hrc]
      group
    rw [e]
    exact mul_mem hc'R (hfix hnf)
  exact mul_mem hcR hn

end Delta

section Decomp

variable {G : Type*} [Group G]

theorem mem_normalizer_of_forall_mem [Finite G] {A : Subgroup G} {g : G}
    (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) : g ∈ normalizer (A : Set G) := by
  have hle : A ≤ Aᵍ[g] := fun x hx => mem_conj_iff.2 (h x hx)
  have heq : A = Aᵍ[g] := Subgroup.eq_of_le_of_card_ge hle (card_conj A g).le
  exact mem_normalizer_of_conj_eq heq.symm

theorem mem_normalizer_of_decomp [Finite G] {P Kp Kq V : Subgroup G} {j k k' : G}
    (hPeq : P = (P ⊓ Kp) ⊔ (P ⊓ Kq)) (hcomm : ⁅Kp, Kq⁆ ≤ V) (hVP : V ≤ P) (hVq : V ≤ Kq)
    (hVk : ∀ v ∈ V, k * v * k⁻¹ ∈ V) (hk : k ∈ Kp) (hk' : k' ∈ Kq) (hjk : j = k * k')
    (hjP : j ∈ normalizer (P : Set G)) : k ∈ normalizer (P : Set G) := by
  have h1 : k ∈ normalizer ((P ⊓ Kp : Subgroup G) : Set G) := by
    apply mem_normalizer_of_forall_mem
    intro q hq
    obtain ⟨hqP, hqK⟩ := Subgroup.mem_inf.1 hq
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hk hqK) (inv_mem hk)⟩
    have hc : k' * q * k'⁻¹ * q⁻¹ ∈ V := by
      apply hcomm
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hk' hqK
    have e : k * q * k⁻¹ = (k * (k' * q * k'⁻¹ * q⁻¹) * k⁻¹)⁻¹ * (j * q * j⁻¹) := by
      rw [hjk]
      group
    rw [e]
    exact mul_mem (inv_mem (hVP (hVk _ hc))) ((mem_normalizer_iff.1 hjP q).1 hqP)
  have h2 : k ∈ normalizer ((P ⊓ Kq : Subgroup G) : Set G) := by
    apply mem_normalizer_of_forall_mem
    intro q hq
    obtain ⟨hqP, hqK⟩ := Subgroup.mem_inf.1 hq
    have hc : k * q * k⁻¹ * q⁻¹ ∈ V := by
      apply hcomm
      exact Subgroup.commutator_mem_commutator hk hqK
    have e : k * q * k⁻¹ = (k * q * k⁻¹ * q⁻¹) * q := by group
    rw [e]
    exact Subgroup.mem_inf.2 ⟨mul_mem (hVP hc) hqP, mul_mem (hVq hc) hqK⟩
  have h3 := Common.mem_normalizer_sup h1 h2
  rwa [← hPeq] at h3

theorem vstep {R V : Subgroup G} {x r' z' j k k' : G}
    (hx : x = r' * z') (hj : j = k * k') (hr' : r' ∈ R) (hVR : V ≤ R)
    (hkR : k ∈ normalizer (R : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hVk : ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (hz : k * z' * k⁻¹ * z'⁻¹ ∈ V) (hkx : k' * x * k'⁻¹ * x⁻¹ ∈ V) :
    x⁻¹ * (j * x * j⁻¹) ∈ R := by
  have h1 : (j * x * j⁻¹) * x⁻¹ = (k * (k' * x * k'⁻¹ * x⁻¹) * k⁻¹) * (k * r' * k⁻¹) *
      (k * z' * k⁻¹ * z'⁻¹) * r'⁻¹ := by
    subst hj hx
    group
  have h2 : (j * x * j⁻¹) * x⁻¹ ∈ R := by
    rw [h1]
    exact mul_mem (mul_mem (mul_mem (hVR (hVk _ hkx)) ((mem_normalizer_iff.1 hkR r').1 hr'))
      (hVR hz)) (inv_mem hr')
  have h3 : x⁻¹ * ((j * x * j⁻¹) * x⁻¹) * x⁻¹⁻¹ ∈ R :=
    (mem_normalizer_iff.1 (inv_mem hxR) _).1 h2
  have e : x⁻¹ * (j * x * j⁻¹) = x⁻¹ * ((j * x * j⁻¹) * x⁻¹) * x⁻¹⁻¹ := by group
  rw [e]
  exact h3

end Decomp

section Zs

variable {Q : Type*} [Group Q]

theorem zs_conj {S : Subgroup Q} {g : Q} (hg : g ∈ normalizer (S : Set Q)) (i : ℕ) :
    ∀ x : Q, x ∈ UCSAux.zs S i → g * x * g⁻¹ ∈ UCSAux.zs S i := by
  induction i with
  | zero =>
    intro x hx
    rw [UCSAux.zs_zero, Subgroup.mem_bot] at hx
    rw [UCSAux.zs_zero, Subgroup.mem_bot, hx]
    group
  | succ i ih =>
    intro x hx
    rw [UCSAux.mem_zs_succ] at hx ⊢
    obtain ⟨hxS, hx⟩ := hx
    refine ⟨(mem_normalizer_iff.1 hg x).1 hxS, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ S := by
      have := (mem_normalizer_iff.1 (inv_mem hg) w).1 hw
      simpa using this
    have h1 := ih _ (hx _ hw')
    have e : g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ =
        (g * x * g⁻¹) * w * (g * x * g⁻¹)⁻¹ * w⁻¹ := by group
    rw [e] at h1
    exact h1

theorem mem_normalizer_zs {S : Subgroup Q} {g : Q} (hg : g ∈ normalizer (S : Set Q)) (i : ℕ) :
    g ∈ normalizer (UCSAux.zs S i : Set Q) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨zs_conj hg i x, fun hx => ?_⟩
  have := zs_conj (inv_mem hg) i _ hx
  simpa [mul_assoc] using this

end Zs

section SL2

variable {F : Type} [Field F] [Finite F]

theorem sl2_isPerfect (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
  CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h4)

end SL2

section PerfectResidual

variable {H : Type*} [Group H]

theorem le_perfectResidual_map_of_perfect {Q Y : Subgroup H} (hQY : Q ≤ Y) (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ (CFSG.perfectResidual Y).map Y.subtype := by
  have hQ' : (Q.subgroupOf Y).map Y.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQY]
  have hperf : ⁅Q.subgroupOf Y, Q.subgroupOf Y⁆ = Q.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, hQ', hQ]
  have h1 : Q.subgroupOf Y ≤ CFSG.perfectResidual Y := by
    refine le_iInf fun n => ?_
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc Q.subgroupOf Y = ⁅Q.subgroupOf Y, Q.subgroupOf Y⁆ := hperf.symm
        _ ≤ ⁅derivedSeries ↥Y n, derivedSeries ↥Y n⁆ := Subgroup.commutator_mono ih ih
  calc Q = (Q.subgroupOf Y).map Y.subtype := hQ'.symm
    _ ≤ (CFSG.perfectResidual Y).map Y.subtype := Subgroup.map_mono h1

end PerfectResidual

section D1Facts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem xBar_normal {q : ℕ} (d : TrialityD4Data L q) (t : G) : (xBar d t).Normal :=
  Subgroup.normalClosure_normal

theorem nOneBar_normal {q : ℕ} (d : TrialityD4Data L q) (t : G) : (nOneBar d t).Normal := by
  haveI := xBar_normal d t
  haveI : (CFSG.perfectResidual ↥(xBar d t)).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  unfold nOneBar
  infer_instance

theorem normalizer_D₅_le_normalizer_nOne {q : ℕ} (d : TrialityD4Data L q) (t : G) :
    normalizer ((yamadaD₅ d t : Subgroup G) : Set G) ≤
      normalizer ((nOne d t : Subgroup G) : Set G) := by
  intro g hg
  haveI := nOneBar_normal d t
  rw [mem_normalizer_iff]
  intro y
  have hgn : ∀ z : G, z ∈ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) ↔
      g * z * g⁻¹ ∈ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := by
    intro z
    constructor
    · intro hz
      exact mul_mem (mul_mem hg hz) (inv_mem hg)
    · intro hz
      have := mul_mem (mul_mem (inv_mem hg) hz) hg
      simpa [mul_assoc] using this
  unfold nOne
  rw [NormalizerQuotient.mem_lift_iff, NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hy, hyN⟩
    refine ⟨(hgn y).1 hy, ?_⟩
    have : NormalizerQuotient.proj (yamadaD₅ d t) ⟨g * y * g⁻¹, (hgn y).1 hy⟩ =
        NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩ *
          NormalizerQuotient.proj (yamadaD₅ d t) ⟨y, hy⟩ *
            (NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact (nOneBar_normal d t).conj_mem _ hyN _
  · rintro ⟨hy, hyN⟩
    refine ⟨(hgn y).2 hy, ?_⟩
    have : NormalizerQuotient.proj (yamadaD₅ d t) ⟨g * y * g⁻¹, hy⟩ =
        NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩ *
          NormalizerQuotient.proj (yamadaD₅ d t) ⟨y, (hgn y).2 hy⟩ *
            (NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this] at hyN
    have := (nOneBar_normal d t).conj_mem _ hyN (NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩)⁻¹
    simpa [mul_assoc] using this

theorem J₆_map_le_cLV {q : ℕ} (d : TrialityD4Data L q) : d.J₆.map L.subtype ≤ cLV d :=
  Subgroup.map_mono inf_le_right

theorem jSixBar_le_kBar {q : ℕ} (d : TrialityD4Data L q) (t : G) : jSixBar d t ≤ kBar d t :=
  NormalizerQuotient.bar_mono (J₆_map_le_cLV d)

theorem four_le_card_Γ (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) : 4 ≤ Nat.card d.Γ := by
  rw [d.card_Γ]
  have h1 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  calc 4 ≤ 2 ^ f := h1
    _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _

theorem kBar_le_nOneBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : kBar d t ≤ nOneBar d t := by
  obtain ⟨-, -, ⟨⟨e⟩, -⟩, -⟩ := D1_centralizer_tbar h d hp
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) d.Γ) :=
    sl2_isPerfect (four_le_card_Γ d hp.two_le)
  haveI : Group.IsPerfect ↥(kBar d t) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hperf : ⁅kBar d t, kBar d t⁆ = kBar d t := Subgroup.isPerfect_iff.1 inferInstance
  have hkx : kBar d t ≤ xBar d t := fun x hx => Subgroup.subset_normalClosure hx
  exact le_perfectResidual_map_of_perfect hkx hperf

theorem pBar_le_nOneBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : pBar d t ≤ nOneBar d t := by
  obtain ⟨-, -, -, ⟨-, -, -, -, -, hcomm⟩⟩ := D1_centralizer_tbar h d hp
  have hJ : jSixBar d t ≤ nOneBar d t := (jSixBar_le_kBar d t).trans (kBar_le_nOneBar h d hp)
  calc pBar d t = ⁅pBar d t, jSixBar d t⁆ := hcomm
    _ ≤ nOneBar d t := by
      refine Subgroup.commutator_le.2 fun a _ j hj => ?_
      have h1 := (nOneBar_normal d t).conj_mem j (hJ hj) a
      have h2 := mul_mem h1 (inv_mem (hJ hj))
      simpa [commutatorElement_def, mul_assoc] using h2

theorem P_le_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaP d t ≤ nOne d t := by
  intro x hx
  unfold nOne
  rw [NormalizerQuotient.mem_lift_iff]
  exact ⟨h.yamadaP_le_normalizer_yamadaD₅ d hp.layer hx,
    pBar_le_nOneBar h d hp (NormalizerQuotient.proj_mem_bar hx)⟩

theorem N1Factor.le_normalizer_conj (d : TrialityD4Data L (2 ^ f)) {K₁ : Subgroup G}
    (hK₁ : IsN1Factor d t K₁) : K₁ᵍ[t] ≤ normalizer ((K₁ : Subgroup G) : Set G) := by
  refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅K₁ᵍ[t], K₁⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [Subgroup.commutator_comm] at h1
  exact hK₁.D₅_le (hK₁.comm_le h1)

theorem N1Factor.card_nOne [Finite G] (d : TrialityD4Data L (2 ^ f)) {K₁ : Subgroup G}
    (hK₁ : IsN1Factor d t K₁) :
    Nat.card (nOne d t) = Nat.card (yamadaD₅ d t) *
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) d.Γ) ^ 2 := by
  have h1 := card_sup_mul_card_inf_eq_D4 (N1Factor.le_normalizer_conj d hK₁)
  rw [hK₁.inf_eq, ← hK₁.sup_eq, card_conj] at h1
  have h2 := IsQuotientIso.card_eq hK₁.iso hK₁.D₅_le
  have hD : 0 < Nat.card (yamadaD₅ d t) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hD
  rw [h1, h2]
  ring

theorem P_sylow_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) : IsSylowOf 2 (yamadaP d t) (nOne d t) := by
  have hle := P_le_nOne h d hp
  obtain ⟨-, -, -, -, -, -, -, hD, -, hP, -⟩ := T4_series_free h d hp
  have hcard := N1Factor.card_nOne d hK₁
  rw [TrialityD4Data.card_SL_two_D4, d.card_Γ, hD] at hcard
  have hf1 : 1 ≤ f := by have := hp.two_le; omega
  have hq : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hQ2 : Even (((2 ^ f) ^ 3) ^ 2) := (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨hq, by omega⟩, by omega⟩)
  have hQ2pos : 1 ≤ ((2 ^ f) ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : Odd ((((2 ^ f) ^ 3) ^ 2 - 1) ^ 2) :=
    (odd_sub_one_of_even hQ2 hQ2pos).pow
  have hrel := Subgroup.relIndex_mul_card (H := yamadaP d t) (K := nOne d t)
  rw [inf_of_le_left hle, hP, hcard] at hrel
  have hrel2 : (yamadaP d t).relIndex (nOne d t) = (((2 ^ f) ^ 3) ^ 2 - 1) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (2 ^ f) ^ 24 by positivity)
    rw [hrel]
    have e1 : ((2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1)) ^ 2 =
        (2 ^ f) ^ 6 * (((2 ^ f) ^ 3) ^ 2 - 1) ^ 2 := by
      rw [mul_pow, ← pow_mul]
    rw [e1]
    have e2 : (2 ^ f) ^ 24 = (2 ^ f) ^ 18 * (2 ^ f) ^ 6 := by rw [← pow_add]
    rw [e2]
    ring
  have hP2 : IsPGroup 2 (yamadaP d t) := by
    refine IsPGroup.of_card (n := f * 24) ?_
    rw [hP, ← pow_mul]
  refine (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨hle, hP2, ?_⟩
  rw [hrel2]
  intro h2
  have := (Nat.odd_iff.1 hodd)
  have h3 : 2 ∣ (((2 ^ f) ^ 3) ^ 2 - 1) ^ 2 := h2
  omega

theorem jZeroG_le_normalizer_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : jZeroG d ≤ normalizer ((yamadaP d t : Subgroup G) : Set G) :=
  fun _ hx => ncs_le_normalizer_yamadaP h d hp.layer
    ⟨Setup.J₀_map_le_centralizer h d hx, Setup.J₀_map_le_normalizer_S d hx⟩

theorem jZeroG_le_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (hJD : jZeroG d ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G)) :
    jZeroG d ≤ nOne d t := by
  intro j hj
  unfold nOne
  rw [NormalizerQuotient.mem_lift_iff]
  refine ⟨hJD hj, kBar_le_nOneBar h d hp (jSixBar_le_kBar d t ?_)⟩
  have hj6 : j ∈ d.J₆.map L.subtype := by
    obtain ⟨x, hx, rfl⟩ := hj
    exact ⟨x, d.J₀_le_J₆ hx, rfl⟩
  exact NormalizerQuotient.proj_mem_bar (X := d.J₆.map L.subtype) hj6

theorem odd_card_jZeroG {q : ℕ} (d : TrialityD4Data L q) :
    Odd (Nat.card (jZeroG d : Subgroup G)) := by
  show Odd (Nat.card (d.J₀.map L.subtype : Subgroup G))
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact d.odd_card_J₀

theorem commutator_D₅_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  have h521 := h.yamada_5_21 d hlay
  exact h.commutator_yamadaD₅_eq d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521

end D1Facts

section TFacts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem t_normalizer_zs (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    (i : ℕ) : t ∈ normalizer ((UCSAux.zs (yamadaP d t) i : Subgroup G) : Set G) :=
  mem_normalizer_zs (h.t_mem_normalizer_yamadaP d hp.layer) i

end TFacts

section Delta

variable {G : Type*} [Group G]

theorem delta_props {P N A S : Subgroup G} {t : G} (ht : t * t = 1)
    (hPt : Pᵍ[t] = P) (hNt : Nᵍ[t] = N) (hAP : A ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hNA : N ≤ A) (hsup : A ⊔ Aᵍ[t] = P) (hinf : A ⊓ Aᵍ[t] = N) (hcomm : ⁅A, Aᵍ[t]⁆ ≤ N)
    (hS : ∀ s ∈ S, s ∈ P ∧ t⁻¹ * s * t = s)
    (hT2 : ∀ a ∈ P, a⁻¹ * (t * a * t⁻¹) ∈ N → a ∈ S ⊔ N) :
    (∀ x ∈ A, x * (t⁻¹ * x * t) ∈ S ⊔ N) ∧ (∀ x ∈ A, x * (t⁻¹ * x * t) ∈ N → x ∈ N) ∧
      (∀ s ∈ S, ∃ x ∈ A, s * (x * (t⁻¹ * x * t))⁻¹ ∈ N) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hNAt : N ≤ Aᵍ[t] := by
    have := conj_mono hNA t
    rwa [hNt] at this
  have hxt : ∀ x ∈ A, t⁻¹ * x * t ∈ Aᵍ[t] := by
    intro x hx
    rw [mem_conj_iff]
    have : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rw [this]
    exact hx
  have hxtP : ∀ x ∈ A, t⁻¹ * x * t ∈ P := by
    intro x hx
    have h1 : x ∈ Pᵍ[t] := by rw [hPt]; exact hAP hx
    have h2 := mem_conj_iff.1 h1
    rw [hti] at h2 ⊢
    exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply hT2
    · exact mul_mem (hAP hx) (hxtP x hx)
    ·
      have e : (x * (t⁻¹ * x * t))⁻¹ * (t * (x * (t⁻¹ * x * t)) * t⁻¹) =
          ⁅(t⁻¹ * x * t)⁻¹, x⁻¹⁆ := by
        rw [hti]
        have h1 : t * (x * (t * x * t)) * t = (t * x * t) * x := by
          have : t * (x * (t * x * t)) * t = (t * x * t) * x * (t * t) := by group
          rw [this, ht, mul_one]
        rw [h1]
        simp only [commutatorElement_def]
        group
      rw [e]
      refine hcomm ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (inv_mem (hxt x hx)) (inv_mem hx)
  · intro x hx hxN
    have h1 : x ∈ Aᵍ[t] := by
      have : x = (x * (t⁻¹ * x * t)) * (t⁻¹ * x * t)⁻¹ := by group
      rw [this]
      exact mul_mem (hNAt hxN) (inv_mem (hxt x hx))
    rw [← hinf]
    exact ⟨hx, h1⟩
  · intro s hs
    obtain ⟨hsP, hst⟩ := hS s hs
    have hAn : A ≤ normalizer (Aᵍ[t] : Set G) := by
      refine ProductN1SylowAux.le_normalizer_of_commutator_mem (X := A) (Y := Aᵍ[t]) ?_
      intro a ha c hc
      have h1 : a * c * a⁻¹ * c⁻¹ ∈ N := hcomm (Subgroup.commutator_mem_commutator ha hc)
      exact hNAt h1
    rw [← hsup] at hsP
    obtain ⟨a, ha, c, hc, hsac⟩ := (mem_sup_iff_of_le_normalizer hAn).1 hsP
    have hc' : t * c * t⁻¹ ∈ A := mem_conj_iff.1 hc
    set b := t * c * t⁻¹ with hb
    have htt : t⁻¹ * t⁻¹ = 1 := by rw [hti, ht]
    have hcb : t⁻¹ * b * t = c := by
      rw [hb]
      have : t⁻¹ * (t * c * t⁻¹) * t = c := by group
      exact this
    have hbc : t⁻¹ * c * t = b := by
      rw [← hcb]
      have : t⁻¹ * (t⁻¹ * b * t) * t = (t⁻¹ * t⁻¹) * b * (t * t) := by group
      rw [this, htt, ht]
      group
    refine ⟨b, hc', ?_⟩
    rw [hcb]
    have h1 : a * c = (t⁻¹ * a * t) * b := by
      have h2 : t⁻¹ * s * t = (t⁻¹ * a * t) * (t⁻¹ * c * t) := by rw [hsac]; group
      rw [hst, hbc, hsac] at h2
      exact h2
    have hbA : b ∈ A := hc'
    have hat : t⁻¹ * a * t ∈ Aᵍ[t] := hxt a ha
    have h3 : b⁻¹ * a ∈ Aᵍ[t] := by
      have h4 : b⁻¹ * (t⁻¹ * a * t) * b ∈ Aᵍ[t] := by
        have := (mem_normalizer_iff.1 (hAn (inv_mem hbA)) (t⁻¹ * a * t)).1 hat
        simpa using this
      have e : b⁻¹ * a = (b⁻¹ * (t⁻¹ * a * t) * b) * c⁻¹ := by
        have h5 : b⁻¹ * a * c = b⁻¹ * (t⁻¹ * a * t) * b := by
          calc b⁻¹ * a * c = b⁻¹ * (a * c) := by group
            _ = b⁻¹ * ((t⁻¹ * a * t) * b) := by rw [h1]
            _ = b⁻¹ * (t⁻¹ * a * t) * b := by group
        rw [← h5]
        group
      rw [e]
      exact mul_mem h4 (inv_mem hc)
    have hnN : b⁻¹ * a ∈ N := by
      rw [← hinf]
      exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hbA) ha, h3⟩
    have e : s * (b * c)⁻¹ = b * (b⁻¹ * a) * b⁻¹ := by
      rw [hsac]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (hPN (hAP hbA)) _).1 hnN

end Delta

section F0

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem F0_sylow' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    (yamadaP d t = qOne d t K₁ ⊔ (qOne d t K₁)ᵍ[t] ∧
      qOne d t K₁ ⊓ (qOne d t K₁)ᵍ[t] = yamadaV₁ d t ∧
      ⁅qOne d t K₁, (qOne d t K₁)ᵍ[t]⁆ ≤ yamadaV₁ d t ∧
      (∀ x ∈ qOne d t K₁, x * (t⁻¹ * x * t) ∈ d.S.map L.subtype ⊔ yamadaV₁ d t) ∧
      (∀ x ∈ qOne d t K₁, x * (t⁻¹ * x * t) ∈ yamadaV₁ d t → x ∈ yamadaV₁ d t) ∧
      (∀ s ∈ d.S.map L.subtype, ∃ x ∈ qOne d t K₁,
        s * (x * (t⁻¹ * x * t))⁻¹ ∈ yamadaV₁ d t)) ∧
    (yamadaY₂ d t = upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 1 ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 1 ∧
      yamadaW₃ d t = upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 2 ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 2 ∧
      yamadaF₄ d t = upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 3) ∧
    (yamadaP d t = rSub d t K ⊔ (rSub d t K)ᵍ[t] ∧
      rSub d t K ⊓ (rSub d t K)ᵍ[t] = yamadaW₃ d t ∧
      ⁅rSub d t K, (rSub d t K)ᵍ[t]⁆ ≤ yamadaW₃ d t ∧
      (∀ x ∈ rSub d t K, x * (t⁻¹ * x * t) ∈ d.S.map L.subtype ⊔ yamadaW₃ d t) ∧
      (∀ x ∈ rSub d t K, x * (t⁻¹ * x * t) ∈ yamadaW₃ d t → x ∈ yamadaW₃ d t) ∧
      (∀ s ∈ d.S.map L.subtype, ∃ x ∈ rSub d t K,
        s * (x * (t⁻¹ * x * t))⁻¹ ∈ yamadaW₃ d t)) ∧
    (yamadaF₄ d t = centerMod (yamadaW₃ d t) (yamadaP d t) ∧
      centerMod (yamadaW₃ d t) (yamadaP d t) =
        centerMod (yamadaW₃ d t) (rSub d t K) ⊔ centerMod (yamadaW₃ d t) ((rSub d t K)ᵍ[t])) := by
  have ht : t * t = 1 := h.t_mul_t
  have hlay := hp.layer
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  obtain ⟨-, -, -, -, -, -, hSC, -, -, -, hF1, hF2, hF3, -⟩ := T4_series_free h d hp
  have hPt : (yamadaP d t)ᵍ[t] = yamadaP d t :=
    conj_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaP d hlay)
  have hVt : (yamadaV₁ d t)ᵍ[t] = yamadaV₁ d t := by
    rw [← hZ1]; exact conj_eq_of_mem_normalizer (t_normalizer_zs h d hp 1)
  have hWt : (yamadaW₃ d t)ᵍ[t] = yamadaW₃ d t := by
    rw [← hZ3]; exact conj_eq_of_mem_normalizer (t_normalizer_zs h d hp 3)
  have hVP : yamadaV₁ d t ≤ yamadaP d t := hZ1 ▸ UCSAux.zs_le _ _
  have hWP : yamadaW₃ d t ≤ yamadaP d t := hZ3 ▸ UCSAux.zs_le _ _
  have hPV : yamadaP d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    hZ1 ▸ UCSAux.le_normalizer_zs _ _
  have hPW : yamadaP d t ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    hZ3 ▸ UCSAux.le_normalizer_zs _ _
  have htP : t ∈ normalizer ((yamadaP d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaP d hlay
  have htV : t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := hZ1 ▸ t_normalizer_zs h d hp 1
  have htY : t ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) := hZ2 ▸ t_normalizer_zs h d hp 2
  have htW : t ∈ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) := hZ3 ▸ t_normalizer_zs h d hp 3
  have htBot : t ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_bot] at hx ⊢
      rw [hx]
      group
    · intro hx
      rw [Subgroup.mem_bot] at hx ⊢
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [e, hx]
      group
  have hH1V : H1Zero t (yamadaV₁ d t) :=
    ProductToolboxAux.h1Zero_of_freeLifted ht htV htBot (ProductToolboxAux.h1Zero_bot t) hF1
  have hH1Y : H1Zero t (yamadaY₂ d t) :=
    ProductToolboxAux.h1Zero_of_freeLifted ht htY htV hH1V hF2
  have hH1W : H1Zero t (yamadaW₃ d t) :=
    ProductToolboxAux.h1Zero_of_freeLifted ht htW htY hH1Y hF3
  have hSP : ∀ s ∈ d.S.map L.subtype, s ∈ yamadaP d t ∧ t⁻¹ * s * t = s := by
    intro s hs
    rw [← hSC] at hs
    obtain ⟨hsP, hsC⟩ := Subgroup.mem_inf.1 hs
    refine ⟨hsP, ?_⟩
    have := (Subgroup.mem_centralizer_singleton_iff.1 hsC)
    calc t⁻¹ * s * t = t⁻¹ * (s * t) := by group
      _ = t⁻¹ * (t * s) := by rw [this]
      _ = s := by group
  have hT2V : ∀ a ∈ yamadaP d t, a⁻¹ * (t * a * t⁻¹) ∈ yamadaV₁ d t →
      a ∈ d.S.map L.subtype ⊔ yamadaV₁ d t := by
    intro a ha hat
    have := T2_lift ht hVP hPV htP htV hH1V a ha hat
    rwa [hSC] at this
  have hT2W : ∀ a ∈ yamadaP d t, a⁻¹ * (t * a * t⁻¹) ∈ yamadaW₃ d t →
      a ∈ d.S.map L.subtype ⊔ yamadaW₃ d t := by
    intro a ha hat
    have := T2_lift ht hWP hPW htP htW hH1W a ha hat
    rwa [hSC] at this
  obtain ⟨⟨hN1, hK'int, hK'comm, -⟩, -⟩ := E2_decomposition h d hp hK₁
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  obtain ⟨-, ⟨hN2, hK4int, hK4comm, -, -, -, -, -⟩, ⟨hW₃K4, -, -, -⟩⟩ :=
    C2_decomposition h d hp hK
  have hPsyl1 := P_sylow_nOne h d hp hK₁
  obtain ⟨-, -, hPeq, hint, hcomm⟩ := sylow_prod hPsyl1 hN1.symm hK'int hK'comm hVP
  have hqt : (qOne d t K₁)ᵍ[t] = yamadaP d t ⊓ (⁅K₁, K₁⁆)ᵍ[t] := by
    unfold qOne
    rw [conj_inf, hPt]
  have hsup1 : qOne d t K₁ ⊔ (qOne d t K₁)ᵍ[t] = yamadaP d t := by
    rw [hqt]; exact hPeq.symm
  have hinf1 : qOne d t K₁ ⊓ (qOne d t K₁)ᵍ[t] = yamadaV₁ d t := by
    rw [hqt]; exact hint
  have hcomm1 : ⁅qOne d t K₁, (qOne d t K₁)ᵍ[t]⁆ ≤ yamadaV₁ d t := by
    rw [hqt]; exact hcomm
  have hVq : yamadaV₁ d t ≤ qOne d t K₁ := by
    rw [← hinf1]; exact inf_le_left
  have hqP : qOne d t K₁ ≤ yamadaP d t := inf_le_left
  have hqtP : (qOne d t K₁)ᵍ[t] ≤ yamadaP d t := by rw [hqt]; exact inf_le_left
  obtain ⟨hd1, hd2, hd3⟩ := delta_props ht hPt hVt hqP hPV hVq hsup1 hinf1 hcomm1 hSP hT2V
  have hucs1 : ∀ i : ℕ, upperCenterMod (yamadaV₁ d t) (yamadaP d t) i =
      upperCenterMod (yamadaV₁ d t) (qOne d t K₁) i ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) i := fun i =>
    upperCenterMod_sup hVq (hinf1 ▸ inf_le_right) (hqP.trans hPV) (hqtP.trans hPV) hsup1 hinf1
      hcomm1 i
  have hZ1' : ∀ i : ℕ, upperCenterMod (yamadaV₁ d t) (yamadaP d t) i =
      (Subgroup.upperCentralSeries ↥(yamadaP d t) (1 + i)).map (yamadaP d t).subtype := by
    intro i
    rw [← hZ1]
    exact upperCenterMod_upperCentralSeries (yamadaP d t) 1 i
  obtain ⟨-, -, hPeq2, hint2, hcomm2⟩ := sylow_prod hSyl2 hN2.symm hK4int hK4comm hWP
  have hrt : (rSub d t K)ᵍ[t] = yamadaP d t ⊓ (kFour d t K)ᵍ[t] := by
    unfold rSub
    rw [conj_inf, hPt]
  have hsup2 : rSub d t K ⊔ (rSub d t K)ᵍ[t] = yamadaP d t := by
    rw [hrt]; exact hPeq2.symm
  have hinf2 : rSub d t K ⊓ (rSub d t K)ᵍ[t] = yamadaW₃ d t := by
    rw [hrt]; exact hint2
  have hcomm2' : ⁅rSub d t K, (rSub d t K)ᵍ[t]⁆ ≤ yamadaW₃ d t := by
    rw [hrt]; exact hcomm2
  have hWr : yamadaW₃ d t ≤ rSub d t K := le_inf hWP hW₃K4
  have hrP : rSub d t K ≤ yamadaP d t := inf_le_left
  have hrtP : (rSub d t K)ᵍ[t] ≤ yamadaP d t := by rw [hrt]; exact inf_le_left
  obtain ⟨he1, he2, he3⟩ := delta_props ht hPt hWt hrP hPW hWr hsup2 hinf2 hcomm2' hSP hT2W
  have hZ4' : centerMod (yamadaW₃ d t) (yamadaP d t) = yamadaF₄ d t := by
    have := upperCenterMod_upperCentralSeries (yamadaP d t) 3 1
    rw [hZ3] at this
    exact this.trans hZ4
  have hcen : centerMod (yamadaW₃ d t) (yamadaP d t) =
      centerMod (yamadaW₃ d t) (rSub d t K) ⊔ centerMod (yamadaW₃ d t) ((rSub d t K)ᵍ[t]) :=
    upperCenterMod_sup hWr (hinf2 ▸ inf_le_right) (hrP.trans hPW) (hrtP.trans hPW) hsup2 hinf2
      hcomm2' 1
  refine ⟨⟨hsup1.symm, hinf1, hcomm1, hd1, hd2, hd3⟩, ⟨?_, ?_, ?_⟩, ⟨hsup2.symm, hinf2, hcomm2',
    he1, he2, he3⟩, hZ4'.symm, hcen⟩
  · rw [← hucs1 1, hZ1' 1]
    exact hZ2.symm
  · rw [← hucs1 2, hZ1' 2]
    exact hZ3.symm
  · rw [← hucs1 3, hZ1' 3]
    exact hZ4.symm

end F0

section F1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem sl2Pair_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    Sl2Pair d.Γ (nOne d t) (yamadaD₅ d t) K₁ (K₁ᵍ[t]) := by
  have hD : (yamadaD₅ d t)ᵍ[t] = yamadaD₅ d t :=
    conj_eq_of_mem_normalizer
      ((E1_char_D5 h d hp hK₁).2.2 (h.t_mem_normalizer_yamadaP d hp.layer))
  refine ⟨d.instCharP, four_le_card_Γ d hp.two_le, hK₁.sup_eq.symm, hK₁.inf_eq, hK₁.comm_le,
    hK₁.iso, ?_⟩
  have := IsQuotientIso.conj hK₁.iso t
  rwa [hD] at this

theorem sl2Pair_nTwo (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    Sl2Pair d.Γ₀ (nTwo d t) (yamadaM₆ d t) (kTwo d t K) ((kTwo d t K)ᵍ[t]) := by
  obtain ⟨⟨hN, hint, hcomm, hiso, -⟩, -, -, hMN⟩ := B1_decomposition h d hp hK
  have hM : (yamadaM₆ d t)ᵍ[t] = yamadaM₆ d t :=
    conj_eq_of_mem_normalizer (hMN (h.t_mem_normalizer_yamadaP d hp.layer))
  have h4 : 4 ≤ Nat.card d.Γ₀ := by
    have := d.card_Γ₀
    rw [show Nat.card d.Γ₀ = 2 ^ f from this]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hp.two_le
  refine ⟨inferInstance, h4, hN.symm, hint, hcomm, hiso, ?_⟩
  have := IsQuotientIso.conj hiso t
  rwa [hM] at this

theorem P_le_normalizer_K₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    yamadaP d t ≤ normalizer (K₁ : Set G) := by
  have hS1 := sl2Pair_nOne h d hp hK₁
  obtain ⟨-, -, hPeq, -, -⟩ := sylow_prod (P_sylow_nOne h d hp hK₁) hS1.sup_eq hS1.inf_eq
    hS1.comm_le (yamadaD₅_le_yamadaP d t)
  calc yamadaP d t = (yamadaP d t ⊓ K₁) ⊔ (yamadaP d t ⊓ K₁ᵍ[t]) := hPeq
    _ ≤ normalizer (K₁ : Set G) :=
      sup_le (inf_le_right.trans le_normalizer)
        (inf_le_right.trans (N1Factor.le_normalizer_conj d hK₁))

theorem F1_one_b (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    nTwo d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
      normalizer ((K₁ : Subgroup G) : Set G) ⊓ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨hgN2, hgP⟩ := Subgroup.mem_inf.1 hg
  have hS1 := sl2Pair_nOne h d hp hK₁
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  have hD : g ∈ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) :=
    (E1_char_D5 h d hp hK₁).2.2 hgP
  have hgN1 : g ∈ normalizer ((nOne d t : Subgroup G) : Set G) :=
    normalizer_D₅_le_normalizer_nOne d t hD
  have fac1 := hS1.conj_factor hgN1 hD
  have fac2 := hS1.symm.conj_factor hgN1 hD
  set M := nTwo d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) with hM
  have hPM : yamadaP d t ≤ M := le_inf hSyl2.le le_normalizer
  have hodd : Odd ((yamadaP d t).relIndex M) := by
    have h1 := Subgroup.relIndex_mul_relIndex (yamadaP d t) M (nTwo d t) hPM inf_le_left
    have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hSyl2).2.2
    rw [Nat.odd_iff]
    by_contra hc
    exact h2 (by rw [← h1]; exact Dvd.dvd.mul_right (by omega) _)
  have hpow := pow_relIndex_mem hPM inf_le_right hg
  have hgK₁ : g ∈ normalizer (K₁ : Set G) :=
    mem_normalizer_of_pow_mem hS1.ne fac1 (Or.comm.1 fac2) hodd
      (P_le_normalizer_K₁ h d hp hK₁ hpow)
  exact Subgroup.mem_inf.2 ⟨hgK₁, mem_normalizer_commutator hgK₁⟩

theorem kFour_le_kTwo (d : TrialityD4Data L (2 ^ f)) (K : Subgroup G) :
    kFour d t K ≤ kTwo d t K := by
  have hcl : ⁅kTwo d t K, kTwo d t K⁆ ≤ kTwo d t K :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  exact sup_le hcl le_sup_left

theorem kFour_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    kFour d t K = ⁅kTwo d t K, kTwo d t K⁆ ⊔ yamadaW₃ d t := by
  obtain ⟨-, ⟨-, -, -, -, -, -, -, hperf⟩, ⟨hW, -, -, -⟩⟩ := C2_decomposition h d hp hK
  have hcl : ⁅kTwo d t K, kTwo d t K⁆ ≤ kTwo d t K :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hK4K2 : kFour d t K ≤ kTwo d t K := sup_le hcl le_sup_left
  apply le_antisymm
  · calc kFour d t K ≤ ⁅kFour d t K, kFour d t K⁆ ⊔ yamadaW₃ d t := hperf
      _ ≤ ⁅kTwo d t K, kTwo d t K⁆ ⊔ yamadaW₃ d t :=
        sup_le_sup_right (Subgroup.commutator_mono hK4K2 hK4K2) _
  · exact sup_le le_sup_left hW

theorem F1_one_a (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    nOne d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
      normalizer ((kTwo d t K : Subgroup G) : Set G) ⊓
        normalizer ((kFour d t K : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨hgN1, hgP⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hp.layer
  set M := nOne d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) with hM
  have hS1 := sl2Pair_nOne h d hp hK₁
  have hS2 := sl2Pair_nTwo h d hp hK
  have hPsyl1 := P_sylow_nOne h d hp hK₁
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  have hPM : yamadaP d t ≤ M := le_inf hPsyl1.le le_normalizer
  have hJP := jZeroG_le_normalizer_P h d hp
  have hJD : jZeroG d ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := fun x hx =>
    (E1_char_D5 h d hp hK₁).2.2 (hJP hx)
  have hJM : jZeroG d ≤ M := le_inf (jZeroG_le_nOne h d hp hJD) hJP
  have hcomm : ∀ m ∈ M, ∀ j ∈ jZeroG d, m * j * m⁻¹ * j⁻¹ ∈ yamadaP d t := fun m hm j hj =>
    hS1.comm_mem_normalizer hPsyl1 (yamadaD₅_le_yamadaP d t) m hm j (hJM hj)
  have hodd : Odd ((yamadaP d t).relIndex M) := by
    have h1 := Subgroup.relIndex_mul_relIndex (yamadaP d t) M (nOne d t) hPM inf_le_left
    have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hPsyl1).2.2
    rw [Nat.odd_iff]
    by_contra hc
    exact h2 (by rw [← h1]; exact Dvd.dvd.mul_right (by omega) _)
  have hPK₂ : yamadaP d t ≤ normalizer ((kTwo d t K : Subgroup G) : Set G) :=
    hSyl2.le.trans hS2.le_normalizer
  obtain ⟨z, hz, p, hpP, rfl⟩ := exists_centralizer_mul hPM hPsyl1.isPGroup inf_le_right hJM
    (odd_card_jZeroG d) hcomm hg
  obtain ⟨hzM, hzC⟩ := Subgroup.mem_inf.1 hz
  have hzP : z ∈ normalizer ((yamadaP d t : Subgroup G) : Set G) := hzM.2
  have hzH : z ∈ normalizer ((jZeroG d : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hzC
  have hzE : z ∈ normalizer ((jZeroLayer d : Subgroup G) : Set G) :=
    Setup.normalizer_le_normalizer_jZeroLayer d hzH
  have hzY : z ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) :=
    hZ2 ▸ mem_normalizer_zs hzP 2
  have hzN₃ : z ∈ normalizer ((nThree d t : Subgroup G) : Set G) :=
    mem_normalizer_oTwoPrimeRes (Common.mem_normalizer_inf hzE (le_normalizer hzY))
  have hzM₆ : z ∈ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) :=
    (B1_decomposition h d hp hK).2.2.2 hzP
  have hzN₂ : z ∈ normalizer ((nTwo d t : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup hzN₃ hzM₆
  have fac1 := hS2.conj_factor hzN₂ hzM₆
  have fac2 := hS2.symm.conj_factor hzN₂ hzM₆
  have hzK₂ : z ∈ normalizer ((kTwo d t K : Subgroup G) : Set G) :=
    mem_normalizer_of_pow_mem hS2.ne fac1 (Or.comm.1 fac2) hodd
      (hPK₂ (pow_relIndex_mem hPM inf_le_right hzM))
  have hgK₂ : z * p ∈ normalizer ((kTwo d t K : Subgroup G) : Set G) :=
    mul_mem hzK₂ (hPK₂ hpP)
  have hgW : z * p ∈ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) := by
    have := mem_normalizer_zs (mul_mem hzP (le_normalizer hpP)) 3
    exact hZ3 ▸ this
  refine Subgroup.mem_inf.2 ⟨hgK₂, ?_⟩
  rw [kFour_eq h d hp hK]
  exact Common.mem_normalizer_sup (mem_normalizer_commutator hgK₂) hgW

theorem D₅_ne_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaD₅ d t ≠ yamadaP d t := by
  obtain ⟨-, -, -, -, -, -, -, hD, -, hP, -⟩ := T4_series_free h d hp
  intro heq
  have h1 : Nat.card (yamadaD₅ d t) = Nat.card (yamadaP d t) := by rw [heq]
  rw [hD, hP] at h1
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hp.two_le; omega)
  have := Nat.pow_lt_pow_right h2 (show 18 < 24 by norm_num)
  omega

theorem F1_two (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K) :
    rSub d t K = qThree d t K ⊔ pCoreOf 2 (kFour d t K) ∧
      yamadaD₅ d t < rSub d t K ⊔ yamadaD₅ d t ∧ rSub d t K ⊔ yamadaD₅ d t < yamadaP d t := by
  have ht : t * t = 1 := h.t_mul_t
  have hlay := hp.layer
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  obtain ⟨-, ⟨hN2, hK4int, hK4comm, -, -, -, -, -⟩, ⟨hW₃K4, hK4O, hM6, hOz⟩⟩ :=
    C2_decomposition h d hp hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hPX, -⟩ := T5_J₀ h d hp
  obtain ⟨-, hQ, hE⟩ := A2_sylow h d hp hK
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  have hPD : yamadaD₅ d t ≤ yamadaP d t := yamadaD₅_le_yamadaP d t
  have hPM : yamadaM₆ d t ≤ yamadaP d t := yamadaM₆_le_yamadaP d t
  have hFD : yamadaF₄ d t ≤ yamadaD₅ d t := Setup.yamadaF₄_le_yamadaD₅_PA d
  have hDM : yamadaD₅ d t ⊓ yamadaM₆ d t = yamadaF₄ d t := h.yamadaD₅_inf_yamadaM₆_eq d hlay
  have hPeq : yamadaP d t = yamadaD₅ d t ⊔ yamadaM₆ d t := rfl
  have hFt : (yamadaF₄ d t)ᵍ[t] = yamadaF₄ d t :=
    conj_eq_of_mem_normalizer (hZ4 ▸ t_normalizer_zs h d hp 4)
  have hPt : (yamadaP d t)ᵍ[t] = yamadaP d t :=
    conj_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaP d hlay)
  have hWP : yamadaW₃ d t ≤ yamadaP d t := hZ3 ▸ UCSAux.zs_le _ _
  have hOt : pCoreOf 2 ((kFour d t K)ᵍ[t]) = (pCoreOf 2 (kFour d t K))ᵍ[t] := pCoreOf_conj _ _
  rw [hOt] at hM6
  set O := pCoreOf 2 (kFour d t K) with hO
  have hOK4 : O ≤ kFour d t K := pCoreOf_le _
  have hOM : O ≤ yamadaM₆ d t := hM6 ▸ le_sup_left
  have hOtM : Oᵍ[t] ≤ yamadaM₆ d t := hM6 ▸ le_sup_right
  have hOP : O ≤ yamadaP d t := hOM.trans hPM
  have hOF : ¬ O ≤ yamadaF₄ d t := by
    intro hOF
    have hOtF : Oᵍ[t] ≤ yamadaF₄ d t := by
      have := conj_mono hOF t
      rwa [hFt] at this
    have hMF : yamadaM₆ d t ≤ yamadaF₄ d t := hM6 ▸ sup_le hOF hOtF
    have hMD : yamadaM₆ d t ≤ yamadaD₅ d t := hMF.trans hFD
    apply D₅_ne_P h d hp
    apply le_antisymm hPD
    rw [hPeq]
    exact sup_le le_rfl hMD
  have hK₃K : kThree d t K ≤ K := (oTwoPrimeRes_le _).trans inf_le_left
  have hQ₃K₃ : qThree d t K ≤ kThree d t K := by
    obtain ⟨-, -, -, hSylQ, -⟩ := hQ
    obtain ⟨-, -, -, -, hEle, hEQ, -⟩ := hE
    have hQN : qThree d t K ≤ normalizer ((eOne d t K : Subgroup G) : Set G) :=
      haveI := hEQ
      Subgroup.le_normalizer_of_normal_subgroupOf hEle
    exact le_oTwoPrimeRes_of_isPGroup (le_inf hSylQ.le hQN) hSylQ.isPGroup
  have hQ₃P : qThree d t K ≤ yamadaP d t :=
    (inf_le_left : qThree d t K ≤ prodX d t).trans (inf_le_left.trans hPD)
  have hPK₃ : yamadaP d t ⊓ kThree d t K = qThree d t K := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxK₃⟩ := Subgroup.mem_inf.1 hx
      have hxH : x ∈ centralizer ((jZeroG d : Subgroup G) : Set G) := hK.le (hK₃K hxK₃)
      have hxX : x ∈ prodX d t := hPX ▸ Subgroup.mem_inf.2 ⟨hxP, hxH⟩
      exact Subgroup.mem_inf.2 ⟨hxX, hK₃K hxK₃⟩
    · exact le_inf hQ₃P hQ₃K₃
  have hON : kFour d t K ≤ normalizer ((O : Subgroup G) : Set G) := le_normalizer_pCoreOf _
  have hK₃K₄ : kThree d t K ≤ kFour d t K := le_sup_right
  have hK₃N : kThree d t K ≤ normalizer ((O : Subgroup G) : Set G) := hK₃K₄.trans hON
  have hR : rSub d t K = qThree d t K ⊔ O := by
    have hK4' : kFour d t K = kThree d t K ⊔ O := hK4O
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxK₄⟩ := Subgroup.mem_inf.1 hx
      rw [hK4', sup_comm, mem_sup_iff_of_le_normalizer' hK₃N] at hxK₄
      obtain ⟨o, ho, k, hk, rfl⟩ := hxK₄
      have hkP : k ∈ yamadaP d t := by
        have := mul_mem (inv_mem (hOP ho)) hxP
        simpa using this
      have hkQ : k ∈ qThree d t K := hPK₃ ▸ Subgroup.mem_inf.2 ⟨hkP, hk⟩
      rw [sup_comm]
      exact mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hkQ)
    · exact sup_le (le_inf hQ₃P (hQ₃K₃.trans hK₃K₄)) (le_inf hOP hOK4)
  have hOR : O ≤ rSub d t K := by rw [hR]; exact le_sup_right
  have hQ₃D : qThree d t K ≤ yamadaD₅ d t :=
    (inf_le_left : qThree d t K ≤ prodX d t).trans inf_le_left
  have hD_lt : yamadaD₅ d t < rSub d t K ⊔ yamadaD₅ d t := by
    refine lt_of_le_of_ne le_sup_right fun heq => ?_
    have hRD : rSub d t K ≤ yamadaD₅ d t := by
      have : rSub d t K ≤ rSub d t K ⊔ yamadaD₅ d t := le_sup_left
      rwa [← heq] at this
    exact hOF (hDM ▸ le_inf (hOR.trans hRD) hOM)
  have hPsyl2 : IsSylowOf 2 (yamadaP d t) (nTwo d t) := hSyl2
  have hK4t : (kFour d t K)ᵍ[t] ≤ normalizer ((kFour d t K : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅(kFour d t K)ᵍ[t], kFour d t K⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    rw [Subgroup.commutator_comm] at h1
    exact hW₃K4 (hK4comm h1)
  have hK4t' : kFour d t K ≤ normalizer (((kFour d t K)ᵍ[t] : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ ⁅kFour d t K, (kFour d t K)ᵍ[t]⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    have hWt : yamadaW₃ d t ≤ (kFour d t K)ᵍ[t] := by
      rw [← hK4int]; exact inf_le_right
    exact hWt (hK4comm h1)
  have hN2K4 : nTwo d t ≤ normalizer ((kFour d t K : Subgroup G) : Set G) := by
    rw [hN2]; exact sup_le le_normalizer hK4t
  have hN2K4t : nTwo d t ≤ normalizer (((kFour d t K)ᵍ[t] : Subgroup G) : Set G) := by
    rw [hN2]; exact sup_le hK4t' le_normalizer
  have hPK4 : yamadaP d t ≤ normalizer ((kFour d t K : Subgroup G) : Set G) :=
    hPsyl2.le.trans hN2K4
  have hPK4t : yamadaP d t ≤ normalizer (((kFour d t K)ᵍ[t] : Subgroup G) : Set G) :=
    hPsyl2.le.trans hN2K4t
  have hPW : yamadaP d t ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) := by
    rw [← hK4int]
    exact fun x hx => Common.mem_normalizer_inf (hPK4 hx) (hPK4t hx)
  have hK4W : kFour d t K ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) := by
    rw [← hK4int]
    exact fun x hx => Common.mem_normalizer_inf (hN2K4 (hN2 ▸ Subgroup.mem_sup_left hx))
      (hN2K4t (hN2 ▸ Subgroup.mem_sup_left hx))
  have hW₃O : yamadaW₃ d t ≤ O :=
    le_pCoreOf_of_normal hW₃K4 hK4W (hPsyl2.isPGroup.to_le hWP)
  have hPO : yamadaP d t ≤ normalizer ((O : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_pCoreOf (hPK4 hx)
  have hPOt : yamadaP d t ≤ normalizer (Oᵍ[t] : Set G) := fun x hx => by
    have := mem_normalizer_pCoreOf (hPK4t hx)
    rwa [hOt] at this
  have hZ3' : UCSAux.zs (yamadaP d t) 3 = yamadaW₃ d t := hZ3
  have hF4mem : ∀ f' ∈ yamadaF₄ d t, ∀ p ∈ yamadaP d t,
      f' * p * f'⁻¹ * p⁻¹ ∈ yamadaW₃ d t := by
    intro f' hf' p hp'
    rw [← hZ4, UCSAux.mem_zs_succ] at hf'
    have := hf'.2 p hp'
    rwa [hZ3'] at this
  have hOtF : ∀ x ∈ Oᵍ[t], x ∈ yamadaM₆ d t → (∃ o ∈ O, ∃ f' ∈ yamadaF₄ d t, x = o * f') →
      x ∈ yamadaF₄ d t := by
    intro x hxOt hxM ⟨o, ho, f', hf', hxeq⟩
    rw [← hZ4, UCSAux.mem_zs_succ]
    refine ⟨hxM |> hPM, fun p hpP => ?_⟩
    rw [hZ3']
    have hc : p * x * p⁻¹ * x⁻¹ ∈ yamadaW₃ d t := by
      have hcOt : p * x * p⁻¹ * x⁻¹ ∈ Oᵍ[t] :=
        mul_mem ((mem_normalizer_iff.1 (hPOt hpP) x).1 hxOt) (inv_mem hxOt)
      have hw : p * f' * p⁻¹ * f'⁻¹ ∈ yamadaW₃ d t := by
        have := inv_mem (hF4mem f' hf' p hpP)
        have e : (f' * p * f'⁻¹ * p⁻¹)⁻¹ = p * f' * p⁻¹ * f'⁻¹ := by group
        rwa [e] at this
      have hcO : p * x * p⁻¹ * x⁻¹ ∈ O := by
        have e : p * x * p⁻¹ * x⁻¹ = (p * o * p⁻¹ * o⁻¹) * (o * (p * f' * p⁻¹ * f'⁻¹) * o⁻¹) := by
          rw [hxeq]; group
        rw [e]
        refine mul_mem ?_ (hW₃O ((mem_normalizer_iff.1 (hPW (hOP ho)) _).1 hw))
        exact mul_mem ((mem_normalizer_iff.1 (hPO hpP) o).1 ho) (inv_mem ho)
      rw [← hK4int]
      exact Subgroup.mem_inf.2 ⟨hOK4 hcO, (conj_mono hOK4 t) hcOt⟩
    have e : x * p * x⁻¹ * p⁻¹ = (p * x * p⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hc
  have hP_lt : rSub d t K ⊔ yamadaD₅ d t < yamadaP d t := by
    refine lt_of_le_of_ne (sup_le inf_le_left hPD) fun heq => ?_
    have hle : yamadaP d t ≤ O ⊔ yamadaD₅ d t := by
      rw [← heq, hR]
      exact sup_le (sup_le (hQ₃D.trans le_sup_right) le_sup_left) le_sup_right
    have hOD : O ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := fun x hx =>
      h.yamadaP_le_normalizer_yamadaD₅ d hlay (hOP hx)
    have hMdec : ∀ x ∈ yamadaM₆ d t, ∃ o ∈ O, ∃ f' ∈ yamadaF₄ d t, x = o * f' := by
      intro x hx
      obtain ⟨o, ho, d', hd', hxeq⟩ :=
        (mem_sup_iff_of_le_normalizer hOD).1 (hle (hPM hx))
      refine ⟨o, ho, d', ?_, hxeq⟩
      rw [← hDM]
      refine Subgroup.mem_inf.2 ⟨hd', ?_⟩
      have : d' = o⁻¹ * x := by rw [hxeq]; group
      rw [this]
      exact mul_mem (inv_mem (hOM ho)) hx
    have hOtF4 : Oᵍ[t] ≤ yamadaF₄ d t := fun x hx =>
      hOtF x hx (hOtM hx) (hMdec x (hOtM hx))
    have hOF4 : O ≤ yamadaF₄ d t := by
      have := conj_mono hOtF4 t
      rwa [conj_conj_of_mul_self ht, hFt] at this
    exact hOF hOF4
  exact ⟨hR, hD_lt, hP_lt⟩

theorem F1_three (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    rSub d t K ⊔ yamadaD₅ d t = aSub d t K₁ ∨ rSub d t K ⊔ yamadaD₅ d t = aSub d t (K₁ᵍ[t]) := by
  have hS1 := sl2Pair_nOne h d hp hK₁
  have hPsyl1 := P_sylow_nOne h d hp hK₁
  have hDP := yamadaD₅_le_yamadaP d t
  obtain ⟨hR, hlt1, hlt2⟩ := F1_two h d hp hK
  have hinv : nOne d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
      normalizer ((rSub d t K ⊔ yamadaD₅ d t : Subgroup G) : Set G) := by
    intro g hg
    have hg1 := (F1_one_a h d hp hK hK₁) hg
    have hgP := (Subgroup.mem_inf.1 hg).2
    have hgR : g ∈ normalizer ((rSub d t K : Subgroup G) : Set G) :=
      Common.mem_normalizer_inf hgP (Subgroup.mem_inf.1 hg1).2
    exact Common.mem_normalizer_sup hgR ((E1_char_D5 h d hp hK₁).2.2 hgP)
  have hPcase := hS1.invariant hPsyl1 hDP le_sup_right (sup_le inf_le_left hDP) hinv
  rcases hPcase with h1 | h1 | h1 | h1
  · exact absurd h1.symm hlt1.ne
  · exact Or.inl h1
  · exact Or.inr h1
  · exact absurd h1 hlt2.ne

theorem IsN1Factor.conj_t (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) : IsN1Factor d t (K₁ᵍ[t]) := by
  have ht : t * t = 1 := h.t_mul_t
  have hD : (yamadaD₅ d t)ᵍ[t] = yamadaD₅ d t :=
    conj_eq_of_mem_normalizer
      ((E1_char_D5 h d hp hK₁).2.2 (h.t_mem_normalizer_yamadaP d hp.layer))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := conj_mono hK₁.D₅_le t
    rwa [hD] at this
  · rw [conj_conj_of_mul_self ht, sup_comm]
    exact hK₁.sup_eq
  · rw [conj_conj_of_mul_self ht, inf_comm]
    exact hK₁.inf_eq
  · rw [conj_conj_of_mul_self ht, Subgroup.commutator_comm]
    exact hK₁.comm_le
  · have := IsQuotientIso.conj hK₁.iso t
    rwa [hD] at this

theorem F1_labelled' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    ∃ K₁' : Subgroup G, Labelled d t K K₁' := by
  rcases F1_three h d hp hK hK₁ with h1 | h1
  · exact ⟨K₁, ⟨hK, hK₁, h1⟩⟩
  · exact ⟨K₁ᵍ[t], ⟨hK, IsN1Factor.conj_t h d hp hK₁, h1⟩⟩

theorem F1_normalizers' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    (nOne d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((kTwo d t K : Subgroup G) : Set G) ⊓
          normalizer ((kFour d t K : Subgroup G) : Set G) ∧
      nTwo d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((K₁ : Subgroup G) : Set G) ⊓ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G)) ∧
    (rSub d t K = qThree d t K ⊔ pCoreOf 2 (kFour d t K) ∧
      yamadaD₅ d t < rSub d t K ⊔ yamadaD₅ d t ∧ rSub d t K ⊔ yamadaD₅ d t < yamadaP d t) ∧
    (rSub d t K ⊔ yamadaD₅ d t = aSub d t K₁ ∨ rSub d t K ⊔ yamadaD₅ d t = aSub d t (K₁ᵍ[t])) :=
  ⟨⟨F1_one_a h d hp hK hK₁, F1_one_b h d hp hK hK₁⟩, F1_two h d hp hK, F1_three h d hp hK hK₁⟩

end F1

section F2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem card_P_mul_card_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    Nat.card (yamadaP d t) * Nat.card (yamadaF₄ d t) =
      Nat.card (yamadaD₅ d t) * Nat.card (yamadaM₆ d t) := by
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaD₅ d t) (B := yamadaM₆ d t)
    (h.yamadaM₆_le_normalizer_yamadaD₅ d hp.layer)
  rw [h.yamadaD₅_inf_yamadaM₆_eq d hp.layer] at h1
  exact h1

theorem card_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    Nat.card (yamadaF₄ d t) = (2 ^ f) ^ 16 := by
  obtain ⟨-, -, -, -, -, -, -, hD, hM, hP, -⟩ := T4_series_free h d hp
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaD₅ d t) (B := yamadaM₆ d t)
    (h.yamadaM₆_le_normalizer_yamadaD₅ d hp.layer)
  rw [h.yamadaD₅_inf_yamadaM₆_eq d hp.layer, hD, hM] at h1
  have hP' : (yamadaD₅ d t ⊔ yamadaM₆ d t) = yamadaP d t := rfl
  rw [hP', hP] at h1
  apply Nat.eq_of_mul_eq_mul_left (show 0 < (2 ^ f) ^ 24 by positivity)
  rw [h1, ← pow_add, ← pow_add]

theorem F₄_facts (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaV₁ d t ≤ yamadaF₄ d t ∧ (yamadaF₄ d t)ᵍ[t] = yamadaF₄ d t := by
  obtain ⟨hZ1, -, -, hZ4⟩ := S5_upperCentralSeries_P h d hp.layer
  refine ⟨?_, conj_eq_of_mem_normalizer (hZ4 ▸ t_normalizer_zs h d hp 4)⟩
  rw [← hZ1, ← hZ4]
  exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))

theorem F2_one (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    yamadaF₄ d t < pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t ∧
      pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t < yamadaD₅ d t ∧
      (yamadaF₄ d t).relIndex (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t) = 2 ^ f ∧
      pCoreOf 2 ⁅K₁, K₁⁆ = ⁅K₁, K₁⁆ ⊓ yamadaD₅ d t := by
  have ht : t * t = 1 := h.t_mul_t
  have hlay := hp.layer
  have hK := hL.comp
  have hK₁ := hL.factor
  obtain ⟨hF4V, hFt⟩ := F₄_facts h d hp
  obtain ⟨-, -, -, -, -, -, -, hD, -, hP, -⟩ := T4_series_free h d hp
  have hPD := yamadaD₅_le_yamadaP d t
  obtain ⟨⟨hN1, hK'int, hK'comm, -⟩, hDsup, hZint, -, hZp⟩ := E2_decomposition h d hp hK₁
  rw [hZp] at hDsup hZint
  have hDt : (yamadaD₅ d t)ᵍ[t] = yamadaD₅ d t :=
    conj_eq_of_mem_normalizer
      ((E1_char_D5 h d hp hK₁).2.2 (h.t_mem_normalizer_yamadaP d hlay))
  have hEpK : pCoreOf 2 ⁅K₁, K₁⁆ ≤ ⁅K₁, K₁⁆ := pCoreOf_le _
  have hEpt : (pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] ≤ (⁅K₁, K₁⁆)ᵍ[t] := conj_mono hEpK t
  have hVEp : yamadaV₁ d t ≤ pCoreOf 2 ⁅K₁, K₁⁆ := hZint ▸ inf_le_left
  have hVEpt : yamadaV₁ d t ≤ (pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] := hZint ▸ inf_le_right
  have hEpD : pCoreOf 2 ⁅K₁, K₁⁆ ≤ yamadaD₅ d t := hDsup ▸ le_sup_left
  have hEptD : (pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] ≤ yamadaD₅ d t := hDsup ▸ le_sup_right
  have hEpN : pCoreOf 2 ⁅K₁, K₁⁆ ≤
      normalizer (((pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun e he y hy => ?_
    exact hVEpt (hK'comm (Subgroup.commutator_mem_commutator (hEpK he) (hEpt hy)))
  have hEp_eq : pCoreOf 2 ⁅K₁, K₁⁆ = ⁅K₁, K₁⁆ ⊓ yamadaD₅ d t := by
    refine le_antisymm (le_inf hEpK hEpD) fun x hx => ?_
    obtain ⟨hxK, hxD⟩ := Subgroup.mem_inf.1 hx
    rw [hDsup] at hxD
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hEpN).1 hxD
    have hbK : b ∈ ⁅K₁, K₁⁆ := by
      have := mul_mem (inv_mem (hEpK ha)) hxK
      simpa using this
    have hbV : b ∈ yamadaV₁ d t := by
      rw [← hK'int]; exact Subgroup.mem_inf.2 ⟨hbK, hEpt hb⟩
    exact mul_mem ha (hVEp hbV)
  have hEpt_eq : (pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] = (⁅K₁, K₁⁆)ᵍ[t] ⊓ yamadaD₅ d t := by
    rw [hEp_eq, conj_inf, hDt]
  obtain ⟨-, ⟨-, -, hF4⟩, -, -⟩ := F0_sylow' h d hp hK hK₁
  have hFD : yamadaF₄ d t ≤ yamadaD₅ d t := Setup.yamadaF₄_le_yamadaD₅_PA d
  have hq1 : yamadaV₁ d t ≤ qOne d t K₁ := by
    have hVP : yamadaV₁ d t ≤ yamadaP d t := by
      obtain ⟨hZ1, -, -, -⟩ := S5_upperCentralSeries_P h d hlay
      exact hZ1 ▸ UCSAux.zs_le _ _
    exact le_inf hVP (hVEp.trans hEpK)
  have hq1t : yamadaV₁ d t ≤ (qOne d t K₁)ᵍ[t] := by
    have := conj_mono hq1 t
    have hVt : (yamadaV₁ d t)ᵍ[t] = yamadaV₁ d t := by
      obtain ⟨hZ1, -, -, -⟩ := S5_upperCentralSeries_P h d hlay
      exact conj_eq_of_mem_normalizer (hZ1 ▸ t_normalizer_zs h d hp 1)
    rwa [hVt] at this
  set Z₃ := upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 with hZ₃
  set Z₃' := upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 3 with hZ₃'
  have hZ3F : Z₃ ≤ yamadaF₄ d t := by rw [hF4]; exact le_sup_left
  have hZ3'F : Z₃' ≤ yamadaF₄ d t := by rw [hF4]; exact le_sup_right
  have hqK : qOne d t K₁ ≤ ⁅K₁, K₁⁆ := inf_le_right
  have hZ3Ep : Z₃ ≤ pCoreOf 2 ⁅K₁, K₁⁆ := by
    rw [hEp_eq]
    exact le_inf ((upperCenterMod_le hq1 3).trans hqK) (hZ3F.trans hFD)
  have hZ3'Ep : Z₃' ≤ (pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] := by
    rw [hEpt_eq]
    exact le_inf ((upperCenterMod_le hq1t 3).trans (conj_mono hqK t)) (hZ3'F.trans hFD)
  have hdec : yamadaF₄ d t ≤ (pCoreOf 2 ⁅K₁, K₁⁆ ⊓ yamadaF₄ d t) ⊔
      ((pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t] ⊓ yamadaF₄ d t) := by
    exact hF4.le.trans (sup_le_sup (le_inf hZ3Ep hZ3F) (le_inf hZ3'Ep hZ3'F))
  have hcomm : ⁅pCoreOf 2 ⁅K₁, K₁⁆, (pCoreOf 2 ⁅K₁, K₁⁆)ᵍ[t]⁆ ≤ yamadaV₁ d t :=
    (Subgroup.commutator_mono hEpK hEpt).trans hK'comm
  have hsq := card_sup_half_sq (P := yamadaD₅ d t) (N := yamadaV₁ d t)
    (H := pCoreOf 2 ⁅K₁, K₁⁆) (F := yamadaF₄ d t) (t := t) hDsup.symm hZint hcomm hVEp hFt hF4V
    (by
      obtain ⟨hZ1, -, -, hZ4⟩ := S5_upperCentralSeries_P h d hlay
      exact hPD.trans (hZ4 ▸ UCSAux.le_normalizer_zs _ _)) hdec
  have hcF := card_F₄ h d hp
  have hq0 : 0 < 2 ^ f := by positivity
  have hcard : Nat.card (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t : Subgroup G) = (2 ^ f) ^ 17 := by
    have h2 : Nat.card (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t : Subgroup G) ^ 2 =
        ((2 ^ f) ^ 17) ^ 2 := by
      rw [hsq, hD, hcF]
      ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  have hq1' : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hp.two_le; omega)
  refine ⟨?_, ?_, ?_, hEp_eq⟩
  · refine lt_of_le_of_ne le_sup_right fun heq => ?_
    have h1 : Nat.card (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t : Subgroup G) = Nat.card (yamadaF₄ d t) :=
      by rw [← heq]
    rw [hcard, hcF] at h1
    have := Nat.pow_lt_pow_right hq1' (show 16 < 17 by norm_num)
    omega
  · refine lt_of_le_of_ne (sup_le hEpD hFD) fun heq => ?_
    have h1 : Nat.card (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t : Subgroup G) = Nat.card (yamadaD₅ d t) :=
      by rw [heq]
    rw [hcard, hD] at h1
    have := Nat.pow_lt_pow_right hq1' (show 17 < 18 by norm_num)
    omega
  · have h1 := Subgroup.relIndex_mul_card (H := yamadaF₄ d t)
      (K := pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t)
    rw [inf_of_le_left le_sup_right, hcard, hcF] at h1
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (2 ^ f) ^ 16 by positivity)
    rw [h1]
    ring

theorem F2_Q₁M₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    qOne d t K₁ ⊔ yamadaM₆ d t = bSub d t K := by
  have ht : t * t = 1 := h.t_mul_t
  have hlay := hp.layer
  have hK := hL.comp
  have hK₁ := hL.factor
  have hlabel := hL.label
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  have hZ3' : UCSAux.zs (yamadaP d t) 3 = yamadaW₃ d t := hZ3
  have hS1 := sl2Pair_nOne h d hp hK₁
  have hS2 := sl2Pair_nTwo h d hp hK
  have hSyl1 := P_sylow_nOne h d hp hK₁
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  obtain ⟨-, ⟨hN2, hK4int, hK4comm, -, -, -, -, -⟩, ⟨hW₃K4, hK4O, hM6, hOz⟩⟩ :=
    C2_decomposition h d hp hK
  obtain ⟨hFlt1, hFlt2, hFrel, hEp_eq⟩ := F2_one h d hp hL
  obtain ⟨hR, hRlt1, hRlt2⟩ := F1_two h d hp hK
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hPX, -⟩ := T5_J₀ h d hp
  obtain ⟨⟨hN1, hK'int, hK'comm, -⟩, hDsup, hZint, -, hZp⟩ := E2_decomposition h d hp hK₁
  have hPD := yamadaD₅_le_yamadaP d t
  have hPM := yamadaM₆_le_yamadaP d t
  have hFD : yamadaF₄ d t ≤ yamadaD₅ d t := Setup.yamadaF₄_le_yamadaD₅_PA d
  have hDM : yamadaD₅ d t ⊓ yamadaM₆ d t = yamadaF₄ d t := h.yamadaD₅_inf_yamadaM₆_eq d hlay
  have hPeqDM : yamadaP d t = yamadaD₅ d t ⊔ yamadaM₆ d t := rfl
  have hPN := (E1_char_D5 h d hp hK₁).2.2
  have hNPM₆ : normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
      normalizer ((yamadaM₆ d t : Subgroup G) : Set G) := (B1_decomposition h d hp hK).2.2.2
  have hPM₆N : yamadaP d t ≤ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) := fun x hx =>
    hNPM₆ (le_normalizer hx)
  have hPsub : yamadaP d t ≤ yamadaP d t := le_rfl
  set Ep := pCoreOf 2 ⁅K₁, K₁⁆ with hEp
  have hEpK : Ep ≤ ⁅K₁, K₁⁆ := pCoreOf_le _
  have hEpD : Ep ≤ yamadaD₅ d t := by rw [hEp_eq]; exact inf_le_right
  have hEpP : Ep ≤ yamadaP d t := hEpD.trans hPD
  have hN₁K' : nOne d t ≤ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_commutator (hS1.le_normalizer hx)
  have hPEp : yamadaP d t ≤ normalizer ((Ep : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_pCoreOf (hN₁K' (P_le_nOne h d hp hx))
  set E' := Ep ⊔ yamadaM₆ d t with hE'
  have hE'P : E' ≤ yamadaP d t := sup_le hEpP hPM
  have hME' : yamadaM₆ d t ≤ E' := le_sup_right
  have hPE' : yamadaP d t ≤ normalizer ((E' : Subgroup G) : Set G) := fun x hx =>
    Common.mem_normalizer_sup (hPEp hx) (hPM₆N hx)
  have hinv : nTwo d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
      normalizer ((E' : Subgroup G) : Set G) := by
    intro g hg
    have h1 := (F1_one_b h d hp hK hK₁) hg
    have hgP := (Subgroup.mem_inf.1 hg).2
    exact Common.mem_normalizer_sup (mem_normalizer_pCoreOf (Subgroup.mem_inf.1 h1).2)
      (hNPM₆ hgP)
  have hMlt : yamadaM₆ d t < E' := by
    refine lt_of_le_of_ne hME' fun heq => ?_
    have hEpM : Ep ≤ yamadaM₆ d t := by rw [heq]; exact le_sup_left
    have : Ep ≤ yamadaF₄ d t := hDM ▸ le_inf hEpD hEpM
    exact hFlt1.ne (le_antisymm le_sup_right (sup_le this le_rfl))
  have hElt : E' < yamadaP d t := by
    refine lt_of_le_of_ne hE'P fun heq => ?_
    have hDle : yamadaD₅ d t ≤ Ep ⊔ yamadaF₄ d t := by
      intro x hx
      have hxP : x ∈ E' := heq ▸ hPD hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer
        (fun y hy => hPM₆N (hEpP hy))).1 hxP
      have hbD : b ∈ yamadaD₅ d t := by
        have := mul_mem (inv_mem (hEpD ha)) hx
        simpa using this
      have hbF : b ∈ yamadaF₄ d t := hDM ▸ Subgroup.mem_inf.2 ⟨hbD, hb⟩
      exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbF)
    exact hFlt2.ne (le_antisymm (sup_le hEpD hFD) hDle)
  have hcases := hS2.invariant hSyl2 hPM le_sup_right hE'P hinv
  have hV₁W : yamadaV₁ d t ≤ yamadaW₃ d t := by
    rw [← hZ1, ← hZ3]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hPW : yamadaP d t ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    hZ3 ▸ UCSAux.le_normalizer_zs _ _
  have hPV : yamadaP d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    hZ1 ▸ UCSAux.le_normalizer_zs _ _
  have hDcomm : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ ≤ yamadaV₁ d t := (commutator_D₅_eq h d hlay).le
  have hK'K₁ : ⁅K₁, K₁⁆ ≤ K₁ := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hQ₃D : qThree d t K ≤ yamadaD₅ d t :=
    (inf_le_left : qThree d t K ≤ prodX d t).trans inf_le_left
  have hOM : pCoreOf 2 (kFour d t K) ≤ yamadaM₆ d t := by rw [hM6]; exact le_sup_left
  have hOP : pCoreOf 2 (kFour d t K) ≤ yamadaP d t := hOM.trans hPM
  have hW₃K₂t : yamadaW₃ d t ≤ (kTwo d t K)ᵍ[t] := by
    have h1 : yamadaW₃ d t ≤ (kFour d t K)ᵍ[t] := hK4int ▸ inf_le_right
    exact h1.trans (conj_mono (kFour_le_kTwo d K) t)
  have hPeq1 : yamadaP d t = (yamadaP d t ⊓ K₁) ⊔ (yamadaP d t ⊓ K₁ᵍ[t]) := by
    obtain ⟨-, -, hPeq, -, -⟩ := sylow_prod hSyl1 hS1.sup_eq hS1.inf_eq hS1.comm_le hPD
    exact hPeq
  have hEBt : E' ≠ yamadaP d t ⊓ (kTwo d t K)ᵍ[t] := by
    intro hE
    have hEpK₂t : Ep ≤ (kTwo d t K)ᵍ[t] := (le_sup_left.trans hE.le).trans inf_le_right
    have hDcen : yamadaD₅ d t ≤ centralizerMod (yamadaW₃ d t) Ep := by
      intro d' hd'
      rw [mem_centralizerMod_iff]
      refine ⟨hPW (hPD hd'), fun e he _ => ?_⟩
      exact hV₁W (hDcomm (Subgroup.commutator_mem_commutator hd' (hEpD he)))
    have hOcen : pCoreOf 2 (kFour d t K) ≤ centralizerMod (yamadaW₃ d t) Ep := by
      intro o ho
      rw [mem_centralizerMod_iff]
      refine ⟨hPW (hOP ho), fun e he heN => ?_⟩
      have hoz : o ∈ zKTwoT d t K := hOz ▸ ho
      exact ((mem_centerMod_iff hW₃K₂t).1 hoz).2.2 e (hEpK₂t he) heN
    have hAcen : yamadaP d t ⊓ K₁ ≤ centralizerMod (yamadaW₃ d t) Ep := by
      have hA : yamadaP d t ⊓ K₁ = rSub d t K ⊔ yamadaD₅ d t := hlabel.symm
      rw [hA, hR]
      exact sup_le (sup_le (hQ₃D.trans hDcen) hOcen) hDcen
    have hVK't : yamadaV₁ d t ≤ (⁅K₁, K₁⁆)ᵍ[t] := hK'int ▸ inf_le_right
    have hK'N : ⁅K₁, K₁⁆ ≤ normalizer (((⁅K₁, K₁⁆)ᵍ[t] : Subgroup G) : Set G) := by
      refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
      exact hVK't (hK'comm (Subgroup.commutator_mem_commutator hx hy))
    have hAtcen : yamadaP d t ⊓ K₁ᵍ[t] ≤ centralizerMod (yamadaW₃ d t) Ep := by
      intro a ha
      obtain ⟨haP, haK⟩ := Subgroup.mem_inf.1 ha
      rw [mem_centralizerMod_iff]
      refine ⟨hPW haP, fun e he _ => ?_⟩
      have haN₁ : a ∈ nOne d t := by rw [hK₁.sup_eq]; exact Subgroup.mem_sup_right haK
      rw [hN1] at haN₁
      obtain ⟨k, hk, k', hk', rfl⟩ := (mem_sup_iff_of_le_normalizer hK'N).1 haN₁
      have hkK₁t : k ∈ K₁ᵍ[t] := by
        have : k = (k * k') * k'⁻¹ := by group
        rw [this]
        exact mul_mem haK (inv_mem (conj_mono hK'K₁ t hk'))
      have hkD : k ∈ yamadaD₅ d t := by
        rw [← hK₁.inf_eq]; exact Subgroup.mem_inf.2 ⟨hK'K₁ hk, hkK₁t⟩
      have hkEp : k ∈ Ep := by rw [hEp_eq]; exact Subgroup.mem_inf.2 ⟨hk, hkD⟩
      have hkP : k ∈ yamadaP d t := hEpP hkEp
      have e1 : k * k' * e * (k * k')⁻¹ * e⁻¹ =
          (k * (k' * e * k'⁻¹ * e⁻¹) * k⁻¹) * (k * e * k⁻¹ * e⁻¹) := by group
      rw [e1]
      refine mul_mem (hV₁W ?_) (hV₁W ?_)
      · have hc : k' * e * k'⁻¹ * e⁻¹ ∈ yamadaV₁ d t := by
          have h1 : k' * e * k'⁻¹ * e⁻¹ ∈ ⁅(⁅K₁, K₁⁆)ᵍ[t], ⁅K₁, K₁⁆⁆ :=
            Subgroup.commutator_mem_commutator hk' (hEpK he)
          rw [Subgroup.commutator_comm] at h1
          exact hK'comm h1
        exact (mem_normalizer_iff.1 (hPV hkP) _).1 hc
      · exact hDcomm (Subgroup.commutator_mem_commutator (hEpD hkEp) (hEpD he))
    have hPcen : yamadaP d t ≤ centralizerMod (yamadaW₃ d t) Ep :=
      hPeq1.le.trans (sup_le hAcen hAtcen)
    have hEpF : Ep ≤ yamadaF₄ d t := by
      intro e he
      rw [← hZ4, UCSAux.mem_zs_succ]
      refine ⟨hEpP he, fun w hw => ?_⟩
      rw [hZ3']
      have h1 := (mem_centralizerMod_iff.1 (hPcen hw)).2 e he (hPW (hEpP he))
      have e2 : e * w * e⁻¹ * w⁻¹ = (w * e * w⁻¹ * e⁻¹)⁻¹ := by group
      rw [e2]
      exact inv_mem h1
    exact hFlt1.ne (le_antisymm le_sup_right (sup_le hEpF le_rfl))
  have hEB : E' = bSub d t K := by
    rcases hcases with h1 | h1 | h1 | h1
    · exact absurd h1 hMlt.ne'
    · exact h1
    · exact absurd h1 hEBt
    · exact absurd h1 hElt.ne
  have hqP : qOne d t K₁ ≤ yamadaP d t := inf_le_left
  have hqK : qOne d t K₁ ≤ ⁅K₁, K₁⁆ := inf_le_right
  have hJP := jZeroG_le_normalizer_P h d hp
  have hJD : jZeroG d ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := fun x hx =>
    hPN (hJP hx)
  have hJN₁ := jZeroG_le_nOne h d hp hJD
  have hJK' : jZeroG d ≤ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) := fun x hx => hN₁K' (hJN₁ hx)
  have hJEp : jZeroG d ≤ normalizer ((Ep : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_pCoreOf (hJK' hx)
  have hJE' : jZeroG d ≤ normalizer ((E' : Subgroup G) : Set G) := fun x hx =>
    Common.mem_normalizer_sup (hJEp hx) (hNPM₆ (hJP hx))
  have hJq : jZeroG d ≤ normalizer ((qOne d t K₁ : Subgroup G) : Set G) := fun x hx =>
    Common.mem_normalizer_inf (hJP hx) (hJK' hx)
  obtain ⟨-, -, -, -, -, -, hPcM, -, -, -, hPX, -⟩ := T5_J₀ h d hp
  have hqE' : qOne d t K₁ ≤ E' := by
    intro x hx
    have hq2 : IsPGroup 2 (qOne d t K₁) := hSyl2.isPGroup.to_le hqP
    haveI : Group.IsNilpotent (qOne d t K₁) := hq2.isNilpotent
    have hcop : Nat.Coprime (Nat.card (jZeroG d : Subgroup G)) (Nat.card (qOne d t K₁)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(qOne d t K₁))).1 hq2
      rw [hn]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 (odd_card_jZeroG d))
    have hfix : ∀ s ∈ jZeroG d, x⁻¹ * (s * x * s⁻¹) ∈ qOne d t K₁ ⊓ E' := by
      intro s hs
      have h1 : x⁻¹ * (s * x * s⁻¹) ∈ qOne d t K₁ :=
        mul_mem (inv_mem hx) ((mem_normalizer_iff.1 (hJq hs) x).1 hx)
      have h2 : x⁻¹ * (s * x * s⁻¹) ∈ yamadaM₆ d t := by
        have hsN : s ∈ normalizer ((yamadaM₆ d t : Subgroup G) : Set G) := hNPM₆ (hJP hs)
        have := (mem_centralizerMod_iff.1 (hPcM (hqP (inv_mem hx)))).2 s hs hsN
        have e : x⁻¹ * s * (x⁻¹)⁻¹ * s⁻¹ = x⁻¹ * (s * x * s⁻¹) := by group
        rwa [e] at this
      exact Subgroup.mem_inf.2 ⟨h1, hME' h2⟩
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_mem_inf_centralizer_mul_of_coprime
      (M := qOne d t K₁) (N := qOne d t K₁ ⊓ E') (S := jZeroG d) inf_le_left
      (fun y hy => Common.mem_normalizer_inf (le_normalizer hy) (hPE' (hqP hy)))
      hJq (fun s hs => Common.mem_normalizer_inf (hJq hs) (hJE' hs)) inferInstance hcop hx hfix
    obtain ⟨hcq, hcC⟩ := Subgroup.mem_inf.1 hc
    have hcX : c ∈ prodX d t := hPX ▸ Subgroup.mem_inf.2 ⟨hqP hcq, hcC⟩
    have hcEp : c ∈ Ep := by
      rw [hEp_eq]
      exact Subgroup.mem_inf.2 ⟨hqK hcq, (inf_le_left : prodX d t ≤ yamadaD₅ d t) hcX⟩
    exact mul_mem (Subgroup.mem_sup_left hcEp) (Subgroup.mem_inf.1 hn).2
  have hEpQ : Ep ≤ qOne d t K₁ := le_inf hEpP hEpK
  rw [← hEB]
  exact le_antisymm (sup_le hqE' hME') (sup_le (hEpQ.trans le_sup_left) le_sup_right)

theorem F2_rest (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    qOne d t K₁ ⊔ yamadaF₄ d t = rSub d t K ⊔ yamadaF₄ d t ∧
      rSub d t K ⊔ yamadaF₄ d t = aSub d t K₁ ⊓ bSub d t K ∧
      Nat.card ↥(aSub d t K₁ ⊓ bSub d t K) = (2 ^ f) ^ 4 * Nat.card (yamadaF₄ d t) := by
  have ht : t * t = 1 := h.t_mul_t
  have hlay := hp.layer
  have hK := hL.comp
  have hK₁ := hL.factor
  have hlabel := hL.label
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  have hS1 := sl2Pair_nOne h d hp hK₁
  have hS2 := sl2Pair_nTwo h d hp hK
  have hSyl1 := P_sylow_nOne h d hp hK₁
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  obtain ⟨-, -, -, -, -, -, -, hD, hM, hP, -⟩ := T4_series_free h d hp
  obtain ⟨hF4V, hFt⟩ := F₄_facts h d hp
  have hcF := card_F₄ h d hp
  have hPF4 : yamadaP d t ≤ normalizer ((yamadaF₄ d t : Subgroup G) : Set G) :=
    hZ4 ▸ UCSAux.le_normalizer_zs _ _
  have hPD := yamadaD₅_le_yamadaP d t
  have hPM := yamadaM₆_le_yamadaP d t
  have hFD : yamadaF₄ d t ≤ yamadaD₅ d t := Setup.yamadaF₄_le_yamadaD₅_PA d
  have hFM : yamadaF₄ d t ≤ yamadaM₆ d t := h.yamadaF₄_le_yamadaM₆_PA d hlay
  have hQM := F2_Q₁M₆ h d hp hL
  obtain ⟨hR, -, -⟩ := F1_two h d hp hK
  have hK'K₁ : ⁅K₁, K₁⁆ ≤ K₁ := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hDA : yamadaD₅ d t ≤ aSub d t K₁ := hlabel ▸ le_sup_right
  have hMB : yamadaM₆ d t ≤ bSub d t K := le_inf hPM le_sup_right
  have hQA : qOne d t K₁ ≤ aSub d t K₁ := inf_le_inf_left _ hK'K₁
  have hQB : qOne d t K₁ ≤ bSub d t K := hQM ▸ le_sup_left
  have hRA : rSub d t K ≤ aSub d t K₁ := hlabel ▸ le_sup_left
  have hRB : rSub d t K ≤ bSub d t K := inf_le_inf_left _ (kFour_le_kTwo d K)
  have hFA : yamadaF₄ d t ≤ aSub d t K₁ := hFD.trans hDA
  have hFB : yamadaF₄ d t ≤ bSub d t K := hFM.trans hMB
  have hAB : aSub d t K₁ ⊔ bSub d t K = yamadaP d t :=
    le_antisymm (sup_le inf_le_left inf_le_left)
      (sup_le (hDA.trans le_sup_left) (hMB.trans le_sup_right) : yamadaD₅ d t ⊔ yamadaM₆ d t ≤ _)
  have hBA : bSub d t K ≤ normalizer ((aSub d t K₁ : Subgroup G) : Set G) := by
    intro x hx
    have hxP : x ∈ yamadaP d t := (Subgroup.mem_inf.1 hx).1
    unfold aSub
    exact Common.mem_normalizer_inf (le_normalizer hxP) (P_le_normalizer_K₁ h d hp hK₁ hxP)
  have h1 := card_sup_mul_card_inf_eq_D4 hBA
  rw [hAB] at h1
  have hAcard : Nat.card (aSub d t K₁) = (2 ^ f) ^ 3 * Nat.card (yamadaD₅ d t) := by
    have h2 := hS1.relIndex_sylow hSyl1 hPD
    have h3 := Subgroup.relIndex_mul_card (H := yamadaD₅ d t) (K := aSub d t K₁)
    rw [inf_of_le_left hDA] at h3
    have h4 : (yamadaD₅ d t).relIndex (aSub d t K₁) = (2 ^ f) ^ 3 := h2.trans d.card_Γ
    rw [← h3, h4]
  have hBcard : Nat.card (bSub d t K) = 2 ^ f * Nat.card (yamadaM₆ d t) := by
    have h2 := hS2.relIndex_sylow hSyl2 hPM
    have h3 := Subgroup.relIndex_mul_card (H := yamadaM₆ d t) (K := bSub d t K)
    rw [inf_of_le_left hMB] at h3
    have h4 : (yamadaM₆ d t).relIndex (bSub d t K) = 2 ^ f :=
      h2.trans (show Nat.card d.Γ₀ = 2 ^ f from d.card_Γ₀)
    rw [← h3, h4]
  have hPFM := card_P_mul_card_F₄ h d hp
  have hUcard : Nat.card ↥(aSub d t K₁ ⊓ bSub d t K) = (2 ^ f) ^ 4 * Nat.card (yamadaF₄ d t) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := yamadaP d t))
    rw [h1, hAcard, hBcard]
    calc (2 ^ f) ^ 3 * Nat.card (yamadaD₅ d t) * (2 ^ f * Nat.card (yamadaM₆ d t))
        = (2 ^ f) ^ 4 * (Nat.card (yamadaD₅ d t) * Nat.card (yamadaM₆ d t)) := by ring
      _ = (2 ^ f) ^ 4 * (Nat.card (yamadaP d t) * Nat.card (yamadaF₄ d t)) := by rw [hPFM]
      _ = Nat.card (yamadaP d t) * ((2 ^ f) ^ 4 * Nat.card (yamadaF₄ d t)) := by ring
  obtain ⟨⟨hsup1, hinf1, hcomm1, -, -, -⟩, ⟨-, -, hF4Q⟩, ⟨hsup2, hinf2, hcomm2, -, -, -⟩, hF4cen,
    hcenR⟩ := F0_sylow' h d hp hK hK₁
  have hVq : yamadaV₁ d t ≤ qOne d t K₁ := hinf1 ▸ inf_le_left
  have hVqt : yamadaV₁ d t ≤ (qOne d t K₁)ᵍ[t] := hinf1 ▸ inf_le_right
  have hdecQ : yamadaF₄ d t ≤
      (qOne d t K₁ ⊓ yamadaF₄ d t) ⊔ ((qOne d t K₁)ᵍ[t] ⊓ yamadaF₄ d t) := by
    have h1 : upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 ≤ yamadaF₄ d t := by
      rw [hF4Q]; exact le_sup_left
    have h2 : upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 3 ≤ yamadaF₄ d t := by
      rw [hF4Q]; exact le_sup_right
    exact hF4Q.le.trans (sup_le_sup (le_inf (upperCenterMod_le hVq 3) h1)
      (le_inf (upperCenterMod_le hVqt 3) h2))
  have hsqQ := card_sup_half_sq (P := yamadaP d t) (N := yamadaV₁ d t) (H := qOne d t K₁)
    (F := yamadaF₄ d t) (t := t) hsup1.symm hinf1 hcomm1 hVq hFt hF4V hPF4 hdecQ
  have hcQ : Nat.card ↥(qOne d t K₁ ⊔ yamadaF₄ d t) = (2 ^ f) ^ 20 := by
    have h2 : Nat.card ↥(qOne d t K₁ ⊔ yamadaF₄ d t) ^ 2 = ((2 ^ f) ^ 20) ^ 2 := by
      rw [hsqQ, hP, hcF]
      ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  have hWr : yamadaW₃ d t ≤ rSub d t K := hinf2 ▸ inf_le_left
  have hWrt : yamadaW₃ d t ≤ (rSub d t K)ᵍ[t] := hinf2 ▸ inf_le_right
  have hWF : yamadaW₃ d t ≤ yamadaF₄ d t := by
    rw [← hZ3, ← hZ4]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hdecR : yamadaF₄ d t ≤ (rSub d t K ⊓ yamadaF₄ d t) ⊔ ((rSub d t K)ᵍ[t] ⊓ yamadaF₄ d t) := by
    have e : yamadaF₄ d t = centerMod (yamadaW₃ d t) (rSub d t K) ⊔
        centerMod (yamadaW₃ d t) ((rSub d t K)ᵍ[t]) := hF4cen.trans hcenR
    have h1 : centerMod (yamadaW₃ d t) (rSub d t K) ≤ yamadaF₄ d t := by
      rw [e]; exact le_sup_left
    have h2 : centerMod (yamadaW₃ d t) ((rSub d t K)ᵍ[t]) ≤ yamadaF₄ d t := by
      rw [e]; exact le_sup_right
    have h3 : centerMod (yamadaW₃ d t) (rSub d t K) ≤ rSub d t K := upperCenterMod_le hWr 1
    have h4 : centerMod (yamadaW₃ d t) ((rSub d t K)ᵍ[t]) ≤ (rSub d t K)ᵍ[t] :=
      upperCenterMod_le hWrt 1
    exact e.le.trans (sup_le_sup (le_inf h3 h1) (le_inf h4 h2))
  have hsqR := card_sup_half_sq (P := yamadaP d t) (N := yamadaW₃ d t) (H := rSub d t K)
    (F := yamadaF₄ d t) (t := t) hsup2.symm hinf2 hcomm2 hWr hFt hWF hPF4 hdecR
  have hcR : Nat.card ↥(rSub d t K ⊔ yamadaF₄ d t) = (2 ^ f) ^ 20 := by
    have h2 : Nat.card ↥(rSub d t K ⊔ yamadaF₄ d t) ^ 2 = ((2 ^ f) ^ 20) ^ 2 := by
      rw [hsqR, hP, hcF]
      ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  have hUc : Nat.card ↥(aSub d t K₁ ⊓ bSub d t K) = (2 ^ f) ^ 20 := by
    rw [hUcard, hcF]
    ring
  have hE1 : qOne d t K₁ ⊔ yamadaF₄ d t = aSub d t K₁ ⊓ bSub d t K :=
    Subgroup.eq_of_le_of_card_ge (sup_le (le_inf hQA hQB) (le_inf hFA hFB)) (by rw [hUc, hcQ])
  have hE2 : rSub d t K ⊔ yamadaF₄ d t = aSub d t K₁ ⊓ bSub d t K :=
    Subgroup.eq_of_le_of_card_ge (sup_le (le_inf hRA hRB) (le_inf hFA hFB)) (by rw [hUc, hcR])
  exact ⟨hE1.trans hE2.symm, hE2, hUcard⟩

theorem F2_auxiliary' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (yamadaF₄ d t < pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t ∧
      pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t < yamadaD₅ d t ∧
      (yamadaF₄ d t).relIndex (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t) = 2 ^ f ∧
      pCoreOf 2 ⁅K₁, K₁⁆ = ⁅K₁, K₁⁆ ⊓ yamadaD₅ d t) ∧
    (qOne d t K₁ ⊔ yamadaM₆ d t = bSub d t K ∧
      qOne d t K₁ ⊔ yamadaF₄ d t = rSub d t K ⊔ yamadaF₄ d t ∧
      rSub d t K ⊔ yamadaF₄ d t = aSub d t K₁ ⊓ bSub d t K ∧
      Nat.card ↥(aSub d t K₁ ⊓ bSub d t K) = (2 ^ f) ^ 4 * Nat.card (yamadaF₄ d t)) :=
  ⟨F2_one h d hp hL, F2_Q₁M₆ h d hp hL, F2_rest h d hp hL⟩

end F2

section F3

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem F3_R_eq' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    rSub d t K = qOne d t K₁ ⊔ yamadaW₃ d t := by
  have ht : t * t = 1 := h.t_mul_t
  have hlay := hp.layer
  have hK := hL.comp
  have hK₁ := hL.factor
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  obtain ⟨-, -, -, hF4C, -, -, hSC, -⟩ := T4_series_free h d hp
  obtain ⟨hF4V, hFt⟩ := F₄_facts h d hp
  obtain ⟨⟨hsup1, hinf1, hcomm1, hΔ1Q, hΔ2Q, hΔ3Q⟩, ⟨-, -, hF4Q⟩,
    ⟨hsup2, hinf2, hcomm2, hΔ1R, hΔ2R, hΔ3R⟩, hF4cen, hcenR⟩ := F0_sylow' h d hp hK hK₁
  have hE1 := (F2_rest h d hp hL).1
  obtain ⟨-, -, -, hSyl2, -⟩ := (A3_structure h d hp hK).2.2
  obtain ⟨-, -, -, -, -, -, -, -, hF4J, -⟩ := T5_J₀ h d hp
  have hPt : (yamadaP d t)ᵍ[t] = yamadaP d t :=
    conj_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaP d hlay)
  have hVP : yamadaV₁ d t ≤ yamadaP d t := hZ1 ▸ UCSAux.zs_le _ _
  have hWP : yamadaW₃ d t ≤ yamadaP d t := hZ3 ▸ UCSAux.zs_le _ _
  have hFP : yamadaF₄ d t ≤ yamadaP d t := hZ4 ▸ UCSAux.zs_le _ _
  have hPV : yamadaP d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    hZ1 ▸ UCSAux.le_normalizer_zs _ _
  have hPW : yamadaP d t ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    hZ3 ▸ UCSAux.le_normalizer_zs _ _
  have hPF4 : yamadaP d t ≤ normalizer ((yamadaF₄ d t : Subgroup G) : Set G) :=
    hZ4 ▸ UCSAux.le_normalizer_zs _ _
  have hV₁W : yamadaV₁ d t ≤ yamadaW₃ d t := by
    rw [← hZ1, ← hZ3]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hY₂W : yamadaY₂ d t ≤ yamadaW₃ d t := by
    rw [← hZ2, ← hZ3]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  have hxt : ∀ (A : Subgroup G), ∀ x ∈ A, t⁻¹ * x * t ∈ Aᵍ[t] := by
    intro A x hx
    rw [mem_conj_iff]
    have : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rw [this]
    exact hx
  have hPtP : ∀ x ∈ yamadaP d t, t⁻¹ * x * t ∈ yamadaP d t := fun x hx => hPt ▸ hxt _ x hx
  have hS_le : (d.S.map L.subtype : Subgroup G) ≤ yamadaP d t ⊓ centralizer ({t} : Set G) :=
    hSC.ge
  have hFS : ⁅d.S.map L.subtype, d.S.map L.subtype⁆ = d.F.map L.subtype := by
    rw [← Subgroup.map_commutator, d.commutator_S_eq]
  have hqt : (qOne d t K₁)ᵍ[t] = yamadaP d t ⊓ (⁅K₁, K₁⁆)ᵍ[t] := by
    unfold qOne
    rw [conj_inf, hPt]
  have hVq : yamadaV₁ d t ≤ qOne d t K₁ := hinf1 ▸ inf_le_left
  have hVqt : yamadaV₁ d t ≤ (qOne d t K₁)ᵍ[t] := hinf1 ▸ inf_le_right
  have hqP : qOne d t K₁ ≤ yamadaP d t := inf_le_left
  have hWr : yamadaW₃ d t ≤ rSub d t K := hinf2 ▸ inf_le_left
  have hrP : rSub d t K ≤ yamadaP d t := inf_le_left
  have hSV : (d.S.map L.subtype : Subgroup G) ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    fun x hx => hPV (Subgroup.mem_inf.1 (hS_le hx)).1
  have hSW : (d.S.map L.subtype : Subgroup G) ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    fun x hx => hPW (Subgroup.mem_inf.1 (hS_le hx)).1
  have hFcomm : ∀ f ∈ yamadaF₄ d t, ∀ a ∈ yamadaP d t, f * a * f⁻¹ * a⁻¹ ∈ yamadaW₃ d t := by
    intro f hf a ha
    have := (mem_centerMod_iff hWP).1 (hF4cen ▸ hf)
    exact this.2.2 a ha (hPW ha)
  have hF4R : yamadaF₄ d t ≤ normalizer ((rSub d t K : Subgroup G) : Set G) :=
    le_normalizer_of_commutator_mem fun f hf r hr => hWr (hFcomm f hf r (hrP hr))
  have hRF4 : rSub d t K ≤ normalizer ((yamadaF₄ d t : Subgroup G) : Set G) :=
    fun x hx => hPF4 (hrP hx)
  have hUR : rSub d t K ⊔ yamadaF₄ d t ≤ normalizer ((rSub d t K : Subgroup G) : Set G) :=
    sup_le le_normalizer hF4R
  have hUP : rSub d t K ⊔ yamadaF₄ d t ≤ yamadaP d t := sup_le hrP hFP
  have hcommU : ⁅rSub d t K ⊔ yamadaF₄ d t, rSub d t K ⊔ yamadaF₄ d t⁆ ≤ rSub d t K :=
    commutator_le_of_sup_of_comm le_sup_left hUR le_sup_right hRF4 le_rfl
      (fun a ha b hb => hWr (hFcomm a ha b (hFP hb)))
  have hQU : qOne d t K₁ ≤ rSub d t K ⊔ yamadaF₄ d t := hE1 ▸ le_sup_left
  have hZQ : upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 ≤ qOne d t K₁ :=
    upperCenterMod_le hVq 3
  have hZ'Q : upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 3 ≤ (qOne d t K₁)ᵍ[t] :=
    upperCenterMod_le hVqt 3
  have hZR : upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 ≤ rSub d t K := by
    intro z hz
    have hzQ := hZQ hz
    have hzF : z ∈ yamadaF₄ d t := by rw [hF4Q]; exact Subgroup.mem_sup_left hz
    have hzt : t⁻¹ * z * t ∈ yamadaF₄ d t := hFt ▸ hxt _ z hzF
    have hΔz : z * (t⁻¹ * z * t) ∈
        ⁅d.S.map L.subtype, d.S.map L.subtype⁆ ⊔ yamadaV₁ d t := by
      obtain ⟨s, hs, v, hv, hsv⟩ := (mem_sup_iff_of_le_normalizer hSV).1 (hΔ1Q z hzQ)
      have hsF : s ∈ yamadaF₄ d t := by
        have : s = (z * (t⁻¹ * z * t)) * v⁻¹ := by rw [hsv]; group
        rw [this]
        exact mul_mem (mul_mem hzF hzt) (inv_mem (hF4V hv))
      have hsFC : s ∈ yamadaF₄ d t ⊓ centralizer ({t} : Set G) :=
        Subgroup.mem_inf.2 ⟨hsF, (Subgroup.mem_inf.1 (hS_le hs)).2⟩
      rw [hF4C, ← hFS] at hsFC
      rw [hsv]
      exact mul_mem (Subgroup.mem_sup_left hsFC) (Subgroup.mem_sup_right hv)
    have hQN : qOne d t K₁ ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
      fun x hx => hPV (hqP hx)
    have hQt : ∀ x ∈ qOne d t K₁, t⁻¹ * x * t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
      fun x hx => hPV (hPtP x (hqP hx))
    have hcommQ : ∀ x ∈ qOne d t K₁, ∀ y ∈ qOne d t K₁,
        y * (t⁻¹ * x * t) * y⁻¹ * (t⁻¹ * x * t)⁻¹ ∈ yamadaV₁ d t :=
      fun x hx y hy => hcomm1 (Subgroup.commutator_mem_commutator hy (hxt _ x hx))
    have hz1 := (delta_facts hQN hQt hcommQ hSV hΔ1Q hΔ2Q).2 hΔ3Q z hzQ hΔz
    have hle : ⁅qOne d t K₁, qOne d t K₁⁆ ⊔ yamadaV₁ d t ≤ rSub d t K :=
      sup_le ((commutator_mono hQU hQU).trans hcommU) (hV₁W.trans hWr)
    exact hle hz1
  have hJP := jZeroG_le_normalizer_P h d hp
  have hPN := (E1_char_D5 h d hp hK₁).2.2
  have hJD : jZeroG d ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) :=
    fun x hx => hPN (hJP hx)
  have hJN₁ := jZeroG_le_nOne h d hp hJD
  obtain ⟨⟨hN1, hK'int, hK'comm, -⟩, -⟩ := E2_decomposition h d hp hK₁
  have hF1 := (F1_normalizers' h d hp hK hK₁).1.1
  have hJ4 : jZeroG d ≤ normalizer ((kFour d t K : Subgroup G) : Set G) := fun x hx =>
    (Subgroup.mem_inf.1 (hF1 (Subgroup.mem_inf.2 ⟨hJN₁ hx, hJP hx⟩))).2
  have hJR : jZeroG d ≤ normalizer ((rSub d t K : Subgroup G) : Set G) := fun x hx =>
    Common.mem_normalizer_inf (hJP hx) (hJ4 hx)
  have hJF : jZeroG d ≤ normalizer ((yamadaF₄ d t : Subgroup G) : Set G) := fun x hx =>
    hZ4 ▸ mem_normalizer_zs (hJP hx) 4
  have hVK't : yamadaV₁ d t ≤ (⁅K₁, K₁⁆)ᵍ[t] := hK'int ▸ inf_le_right
  have hK'N : ⁅K₁, K₁⁆ ≤ normalizer (((⁅K₁, K₁⁆)ᵍ[t] : Subgroup G) : Set G) :=
    le_normalizer_of_commutator_mem fun x hx y hy =>
      hVK't (hK'comm (Subgroup.commutator_mem_commutator hx hy))
  have hK'N₁ : ⁅K₁, K₁⁆ ≤ nOne d t := hN1 ▸ le_sup_left
  have hV₁cen : yamadaV₁ d t ≤ zc (nOne d t) := (E3_commutators h d hp hK₁).1.2
  have hPeq : yamadaP d t =
      (yamadaP d t ⊓ ⁅K₁, K₁⁆) ⊔ (yamadaP d t ⊓ (⁅K₁, K₁⁆)ᵍ[t]) := by
    rw [← hqt]
    exact hsup1
  have hstep : ∀ j ∈ jZeroG d, ∀ x ∈ qOne d t K₁,
      x⁻¹ * (j * x * j⁻¹) ∈ rSub d t K := by
    intro j hj x hxQ
    have hxU : x ∈ rSub d t K ⊔ yamadaF₄ d t := hQU hxQ
    obtain ⟨r, hr, f, hf, hxrf⟩ := (mem_sup_iff_of_le_normalizer hRF4).1 hxU
    have hZZ' : upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 ≤
        normalizer ((upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 3 : Subgroup G) :
          Set G) := by
      refine le_normalizer_of_commutator_mem fun z hz z' hz' => ?_
      refine le_upperCenterMod hVqt 3 (hcomm1 ?_)
      exact Subgroup.commutator_mem_commutator (hZQ hz) (hZ'Q hz')
    obtain ⟨z, hz, z', hz', hfzz⟩ := (mem_sup_iff_of_le_normalizer hZZ').1 (hF4Q ▸ hf)
    have hr' : r * z ∈ rSub d t K := mul_mem hr (hZR hz)
    have hxr'z' : x = (r * z) * z' := by rw [hxrf, hfzz]; group
    obtain ⟨k, hk, k', hk', hjk⟩ := (mem_sup_iff_of_le_normalizer hK'N).1 (hN1 ▸ hJN₁ hj)
    have hVk : ∀ v ∈ yamadaV₁ d t, k * v * k⁻¹ ∈ yamadaV₁ d t := by
      intro v hv
      have hcv := mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hV₁cen hv)).2 k (hK'N₁ hk)
      have : k * v * k⁻¹ = v := by rw [hcv]; group
      rw [this]
      exact hv
    have hkP : k ∈ normalizer ((yamadaP d t : Subgroup G) : Set G) :=
      mem_normalizer_of_decomp hPeq hK'comm hVP hVK't hVk hk hk' hjk (hJP hj)
    have hk4 : k ∈ normalizer ((kFour d t K : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.1 (hF1 (Subgroup.mem_inf.2 ⟨hK'N₁ hk, hkP⟩))).2
    have hkR : k ∈ normalizer ((rSub d t K : Subgroup G) : Set G) :=
      Common.mem_normalizer_inf hkP hk4
    have hz'K : z' ∈ (⁅K₁, K₁⁆)ᵍ[t] := (Subgroup.mem_inf.1 (hqt ▸ hZ'Q hz')).2
    have hxK : x ∈ ⁅K₁, K₁⁆ := (Subgroup.mem_inf.1 hxQ).2
    refine vstep hxr'z' hjk hr' (hV₁W.trans hWr) hkR (hUR hxU) hVk ?_ ?_
    · exact hK'comm (Subgroup.commutator_mem_commutator hk hz'K)
    · exact hK'comm (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hk' hxK)
  have hU2 : IsPGroup 2 ↥(rSub d t K ⊔ yamadaF₄ d t) := hSyl2.isPGroup.to_le hUP
  have hQR : qOne d t K₁ ≤ rSub d t K := fun x hx =>
    mem_of_fixed_mod le_sup_left le_sup_right le_rfl hUR hRF4 hJR hJF hU2 (odd_card_jZeroG d)
      (hF4J.le.trans (hY₂W.trans hWr)) x (hQU hx) (fun s hs => hstep s hs x hx)
  have hRN : rSub d t K ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    fun x hx => hPW (hrP hx)
  have hRt : ∀ x ∈ rSub d t K, t⁻¹ * x * t ∈ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    fun x hx => hPW (hPtP x (hrP hx))
  have hcommR : ∀ x ∈ rSub d t K, ∀ y ∈ rSub d t K,
      y * (t⁻¹ * x * t) * y⁻¹ * (t⁻¹ * x * t)⁻¹ ∈ yamadaW₃ d t :=
    fun x hx y hy => hcomm2 (Subgroup.commutator_mem_commutator hy (hxt _ x hx))
  have hRle : rSub d t K ≤ qOne d t K₁ ⊔ yamadaW₃ d t := by
    refine (delta_facts hRN hRt hcommR hSW hΔ1R hΔ2R).1 (qOne d t K₁) hQR ?_
    intro s hs
    obtain ⟨x, hx, hxV⟩ := hΔ3Q s hs
    exact ⟨x, hx, hV₁W hxV⟩
  exact le_antisymm hRle (sup_le hQR hWr)

end F3

end ProductN1SylowAux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem F0_sylow (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    (yamadaP d t = qOne d t K₁ ⊔ (qOne d t K₁)ᵍ[t] ∧
      qOne d t K₁ ⊓ (qOne d t K₁)ᵍ[t] = yamadaV₁ d t ∧
      ⁅qOne d t K₁, (qOne d t K₁)ᵍ[t]⁆ ≤ yamadaV₁ d t ∧
      (∀ x ∈ qOne d t K₁, x * (t⁻¹ * x * t) ∈ d.S.map L.subtype ⊔ yamadaV₁ d t) ∧
      (∀ x ∈ qOne d t K₁, x * (t⁻¹ * x * t) ∈ yamadaV₁ d t → x ∈ yamadaV₁ d t) ∧
      (∀ s ∈ d.S.map L.subtype, ∃ x ∈ qOne d t K₁,
        s * (x * (t⁻¹ * x * t))⁻¹ ∈ yamadaV₁ d t)) ∧
    (yamadaY₂ d t = upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 1 ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 1 ∧
      yamadaW₃ d t = upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 2 ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 2 ∧
      yamadaF₄ d t = upperCenterMod (yamadaV₁ d t) (qOne d t K₁) 3 ⊔
        upperCenterMod (yamadaV₁ d t) ((qOne d t K₁)ᵍ[t]) 3) ∧
    (yamadaP d t = rSub d t K ⊔ (rSub d t K)ᵍ[t] ∧
      rSub d t K ⊓ (rSub d t K)ᵍ[t] = yamadaW₃ d t ∧
      ⁅rSub d t K, (rSub d t K)ᵍ[t]⁆ ≤ yamadaW₃ d t ∧
      (∀ x ∈ rSub d t K, x * (t⁻¹ * x * t) ∈ d.S.map L.subtype ⊔ yamadaW₃ d t) ∧
      (∀ x ∈ rSub d t K, x * (t⁻¹ * x * t) ∈ yamadaW₃ d t → x ∈ yamadaW₃ d t) ∧
      (∀ s ∈ d.S.map L.subtype, ∃ x ∈ rSub d t K,
        s * (x * (t⁻¹ * x * t))⁻¹ ∈ yamadaW₃ d t)) ∧
    (yamadaF₄ d t = centerMod (yamadaW₃ d t) (yamadaP d t) ∧
      centerMod (yamadaW₃ d t) (yamadaP d t) =
        centerMod (yamadaW₃ d t) (rSub d t K) ⊔ centerMod (yamadaW₃ d t) ((rSub d t K)ᵍ[t])) :=
  ProductN1SylowAux.F0_sylow' h d hp hK hK₁

theorem F1_normalizers (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    (nOne d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((kTwo d t K : Subgroup G) : Set G) ⊓
          normalizer ((kFour d t K : Subgroup G) : Set G) ∧
      nTwo d t ⊓ normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((K₁ : Subgroup G) : Set G) ⊓ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G)) ∧
    (rSub d t K = qThree d t K ⊔ pCoreOf 2 (kFour d t K) ∧
      yamadaD₅ d t < rSub d t K ⊔ yamadaD₅ d t ∧ rSub d t K ⊔ yamadaD₅ d t < yamadaP d t) ∧
    (rSub d t K ⊔ yamadaD₅ d t = aSub d t K₁ ∨ rSub d t K ⊔ yamadaD₅ d t = aSub d t (K₁ᵍ[t])) :=
  ProductN1SylowAux.F1_normalizers' h d hp hK hK₁

theorem F1_labelled (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hK : IsLayerComponent d t K) (hK₁ : IsN1Factor d t K₁) :
    ∃ K₁' : Subgroup G, Labelled d t K K₁' :=
  ProductN1SylowAux.F1_labelled' h d hp hK hK₁

theorem F2_auxiliary (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    (yamadaF₄ d t < pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t ∧
      pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t < yamadaD₅ d t ∧
      (yamadaF₄ d t).relIndex (pCoreOf 2 ⁅K₁, K₁⁆ ⊔ yamadaF₄ d t) = 2 ^ f ∧
      pCoreOf 2 ⁅K₁, K₁⁆ = ⁅K₁, K₁⁆ ⊓ yamadaD₅ d t) ∧
    (qOne d t K₁ ⊔ yamadaM₆ d t = bSub d t K ∧
      qOne d t K₁ ⊔ yamadaF₄ d t = rSub d t K ⊔ yamadaF₄ d t ∧
      rSub d t K ⊔ yamadaF₄ d t = aSub d t K₁ ⊓ bSub d t K ∧
      Nat.card ↥(aSub d t K₁ ⊓ bSub d t K) = (2 ^ f) ^ 4 * Nat.card (yamadaF₄ d t)) :=
  ProductN1SylowAux.F2_auxiliary' h d hp hL

theorem F3_R_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K K₁ : Subgroup G} (hL : Labelled d t K K₁) :
    rSub d t K = qOne d t K₁ ⊔ yamadaW₃ d t :=
  ProductN1SylowAux.F3_R_eq' h d hp hL

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
