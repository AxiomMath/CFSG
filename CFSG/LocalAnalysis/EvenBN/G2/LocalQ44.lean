module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQDefs
import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts
public import CFSG.LocalAnalysis.EvenBN.G2.LocalP41
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_centralizer_mul_of_le_J (d : G2Data L K) {A M N : Subgroup G} (hAJ : A ≤ d.J)
    (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G)) (hAM : A ≤ normalizer (M : Set G))
    (hAN : A ≤ normalizer (N : Set G)) (hM : IsPGroup 2 M) {m : G} (hm : m ∈ M)
    (hfix : ∀ a ∈ A, m⁻¹ * (a * m * a⁻¹) ∈ N) :
    ∃ c ∈ M ⊓ centralizer (A : Set G), ∃ n ∈ N, m = c * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent M := hM.isNilpotent
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hM
  refine Common.exists_mem_inf_centralizer_mul_of_coprime hNM hMN hAM hAN inferInstance ?_ hm hfix
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2
    ((odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hAJ)))

namespace Q44

theorem M_le_M₅ (d : G2Data L K) (t : G) : d.M ≤ yamadaM₅ d t :=
  (le_sup_left : d.M ≤ yamadaM₂ d t).trans
    ((le_sup_right : yamadaM₂ d t ≤ yamadaM₃ d t).trans le_sup_left)

theorem M₂_le_M₅ (d : G2Data L K) (t : G) : yamadaM₂ d t ≤ yamadaM₅ d t :=
  (le_sup_right : yamadaM₂ d t ≤ yamadaM₃ d t).trans le_sup_left

theorem Y₂_le_F₂ (d : G2Data L K) (t : G) : yamadaY₂ d t ≤ yamadaF₂ d t := le_sup_right

theorem F₂_le_F₃ (d : G2Data L K) (t : G) : yamadaF₂ d t ≤ yamadaF₃ d t := le_sup_right

theorem F₂_le_F₄ (d : G2Data L K) (t : G) : yamadaF₂ d t ≤ yamadaF₄ d t := le_sup_right

theorem F₃_le_F₅ (d : G2Data L K) (t : G) : yamadaF₃ d t ≤ yamadaF₅ d t := le_sup_left

theorem F₄_le_F₅ (d : G2Data L K) (t : G) : yamadaF₄ d t ≤ yamadaF₅ d t := le_sup_right

theorem F₂_le_F₅ (d : G2Data L K) (t : G) : yamadaF₂ d t ≤ yamadaF₅ d t :=
  (F₂_le_F₃ d t).trans (F₃_le_F₅ d t)

theorem Y₂_le_F₅ (d : G2Data L K) (t : G) : yamadaY₂ d t ≤ yamadaF₅ d t :=
  (Y₂_le_F₂ d t).trans (F₂_le_F₅ d t)

theorem F_le_F₅ (d : G2Data L K) (t : G) : d.F ≤ yamadaF₅ d t :=
  (le_sup_left : d.F ≤ yamadaF₂ d t).trans (F₂_le_F₅ d t)

theorem W₃_le_F₅ (d : G2Data L K) (t : G) : yamadaW₃ d t ≤ yamadaF₅ d t :=
  (le_sup_left : yamadaW₃ d t ≤ yamadaF₃ d t).trans (F₃_le_F₅ d t)

theorem X₄_le_F₅ (d : G2Data L K) (t : G) : yamadaX₄ d t ≤ yamadaF₅ d t :=
  (le_sup_left : yamadaX₄ d t ≤ yamadaF₄ d t).trans (F₄_le_F₅ d t)

theorem F₅_le_M₅ (d : G2Data L K) (t : G) : yamadaF₅ d t ≤ yamadaM₅ d t :=
  sup_le_sup (sup_le_sup_left (yamadaF₂_le_yamadaM₂ d t) _)
    (sup_le_sup_left (yamadaF₂_le_yamadaM₂ d t) _)

theorem M₅_le_S₅ (d : G2Data L K) (t : G) : yamadaM₅ d t ≤ yamadaS₅ d t := by
  have hMS : d.M ≤ d.S := d.inclusions.2.2.2.2.2.2.2.2.1
  exact sup_le_sup (sup_le_sup_left (sup_le_sup_right hMS _) _)
    (sup_le_sup_left (sup_le_sup_right hMS _) _)

theorem S_le_S₅ (d : G2Data L K) (t : G) : d.S ≤ yamadaS₅ d t :=
  (le_sup_left : d.S ≤ yamadaS₂ d t).trans
    ((le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t).trans le_sup_left)

theorem F₅_le_S₅ (d : G2Data L K) (t : G) : yamadaF₅ d t ≤ yamadaS₅ d t :=
  (F₅_le_M₅ d t).trans (M₅_le_S₅ d t)

theorem R₂_le_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaR₂ d t ≤ yamadaR₅ d t := by
  have hD := hQ.doubling
  exact (h.yamada_5_21_2 hW d hK hD).2.1.trans (h.yamada_5_27_3 hW d hK hD).ge

theorem S_le_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : d.S ≤ yamadaR₅ d t :=
  (le_sup_right : d.S ≤ yamadaR₂ d t).trans (R₂_le_R₅ hW h d hK hQ)

theorem S₅_le_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaS₅ d t ≤ yamadaR₅ d t :=
  (le_sup_left : yamadaS₅ d t ≤ yamadaS₅ d t ⊔ zpowers t).trans
    (h.yamada_5_37_2 hW d hK hQ).2.1.1.le

theorem M₅_le_L₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaM₅ d t ≤ yamadaL₅ d t :=
  (le_sup_left : yamadaM₅ d t ≤ yamadaM₅ d t ⊔ zpowers t).trans
    (h.yamada_5_37_2 hW d hK hQ).2.2.1.1.le

theorem L₅_le_L₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaL₅ d t ≤ yamadaL₆ d t :=
  (h.yamada_5_40_4 hW d hK hQ).le.trans inf_le_left

theorem L₅_le_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaL₅ d t ≤ yamadaR₅ d t :=
  (h.yamada_5_40_4 hW d hK hQ).le.trans inf_le_right

theorem F₅_le_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaF₅ d t ≤ yamadaR₅ d t :=
  (F₅_le_S₅ d t).trans (S₅_le_R₅ hW h d hK hQ)

theorem F₅_le_L₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaF₅ d t ≤ yamadaL₅ d t :=
  (F₅_le_M₅ d t).trans (M₅_le_L₅ hW h d hK hQ)

theorem F₅_le_Cstar (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaF₅ d t ≤ yamadaCstar d t :=
  (((le_sup_left : yamadaF₅ d t ≤ yamadaF₅ d t ⊔ zpowers t).trans
    (h.yamada_5_37_2 hW d hK hQ).2.2.2.2.1.le).trans inf_le_right).trans inf_le_right

theorem commutator_mem_F₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaR₅ d t, ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₂ d t := by
  have hR₅F₂N : yamadaR₅ d t ≤ normalizer (yamadaF₂ d t : Set G) :=
    (h.yamadaR₅_le_yamadaR₆ hW d hK hQ).trans (h.yamadaR₆_le_normalizer_yamadaF₂ hW d hK hQ)
  exact comm_mem_of_mul_self_mem hR₅F₂N fun x hx => h.mul_self_mem_yamadaF₂ hW d hK hQ hx

theorem S_le_normalizer_F₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ normalizer (yamadaF₅ d t : Set G) :=
  le_normalizer_of_forall_commutator_mem (commutator_mem_F₂ hW h d hK hQ) (F₂_le_F₅ d t)
    (S_le_R₅ hW h d hK hQ) (F₅_le_R₅ hW h d hK hQ)

theorem M₅_le_L₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaM₅ d t ≤ yamadaL₆ d t :=
  (M₅_le_L₅ hW h d hK hQ).trans (L₅_le_L₆ hW h d hK hQ)

theorem commutator_mem_M₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaL₆ d t, ∀ y ∈ yamadaL₆ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaM₂ d t := by
  have hD := hQ.doubling
  have hsq : ∀ x ∈ yamadaL₆ d t, x * x ∈ yamadaM₂ d t := by
    intro x hx
    have h1 : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaL₆ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
    rw [h.yamada_5_41_2 hW d hK hQ, sq] at h1
    exact h1
  have hN : yamadaL₆ d t ≤ normalizer (yamadaM₂ d t : Set G) :=
    (yamadaL₆_le d t).trans (h.normalizer_yamadaL₂_le d hK hD).1
  exact comm_mem_of_mul_self_mem hN hsq

theorem F₂_le_R₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaF₂ d t ≤ yamadaR₂ d t :=
  (yamadaF₂_le_yamadaM₂ d t).trans ((h.yamadaM₂_le_yamadaL₂ d hK hD).trans le_sup_left)

theorem W₂_le_F₂ (d : G2Data L K) (t : G) : yamadaW₂ d t ≤ yamadaF₂ d t :=
  sup_le_sup_right d.inclusions.2.2.2.2.1 _

theorem X₂_le_F₂ (d : G2Data L K) (t : G) : yamadaX₂ d t ≤ yamadaF₂ d t :=
  sup_le_sup_right d.inclusions.2.2.2.1 _

theorem W₃_inf_R₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaW₃ d t ⊓ yamadaR₂ d t ≤ yamadaW₂ d t := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨hW₃V₃, -, -, hW₂W₃, htW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, hV₃R₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  intro x hx
  obtain ⟨hxW₃, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hxV₂ : x ∈ yamadaV₂ d t := hV₃R₂.le (Subgroup.mem_inf.2 ⟨hW₃V₃ hxW₃, hxR₂⟩)
  rcases (mem_sup_zpowers_iff_of htt (h.t_mem_normalizer_yamadaW₂ d hK hD).1).1 hxV₂ with
    h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    apply htW₃
    have := mul_mem (inv_mem (hW₂W₃ ha)) hxW₃
    rwa [inv_mul_cancel_left] at this

theorem X₄_inf_R₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaX₄ d t ⊓ yamadaR₂ d t ≤ yamadaX₂ d t := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨hX₄U₄, -, -, hX₂X₄, htX₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨-, -, hU₄R₂, -⟩ := h.yamadaU₄_facts hW d hK hD
  intro x hx
  obtain ⟨hxX₄, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hxU₂ : x ∈ yamadaU₂ d t := hU₄R₂.le (Subgroup.mem_inf.2 ⟨hX₄U₄ hxX₄, hxR₂⟩)
  rcases (mem_sup_zpowers_iff_of htt (h.t_mem_normalizer_yamadaX₂ d hK hD).1).1 hxU₂ with
    h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    apply htX₄
    have := mul_mem (inv_mem (hX₂X₄ ha)) hxX₄
    rwa [inv_mul_cancel_left] at this

theorem F₃_inf_R₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₃ d t ⊓ yamadaR₂ d t ≤ yamadaF₂ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hsetF₃, -, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  intro x hx
  obtain ⟨hxF₃, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hx' : x ∈ ((yamadaF₃ d t : Subgroup G) : Set G) := hxF₃
  rw [hsetF₃] at hx'
  obtain ⟨w, hw, φ, hφ, rfl⟩ := Set.mem_mul.1 hx'
  have hwR₂ : w ∈ yamadaR₂ d t := by
    have := mul_mem hxR₂ (inv_mem (F₂_le_R₂ h d hK hD hφ))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (W₂_le_F₂ d t (W₃_inf_R₂_le hW h d hK hQ (Subgroup.mem_inf.2 ⟨hw, hwR₂⟩))) hφ

theorem F₄_inf_R₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₄ d t ⊓ yamadaR₂ d t ≤ yamadaF₂ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hsetF₄, -, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  intro x hx
  obtain ⟨hxF₄, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hx' : x ∈ ((yamadaF₄ d t : Subgroup G) : Set G) := hxF₄
  rw [hsetF₄] at hx'
  obtain ⟨ξ, hξ, φ, hφ, rfl⟩ := Set.mem_mul.1 hx'
  have hξR₂ : ξ ∈ yamadaR₂ d t := by
    have := mul_mem hxR₂ (inv_mem (F₂_le_R₂ h d hK hD hφ))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (X₂_le_F₂ d t (X₄_inf_R₂_le hW h d hK hQ (Subgroup.mem_inf.2 ⟨hξ, hξR₂⟩))) hφ

theorem F₃_le_R₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaF₃ d t ≤ yamadaR₃ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, ⟨hE₃eq, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  exact ((le_sup_left : yamadaF₃ d t ≤ yamadaF₃ d t ⊔ zpowers t).trans hE₃eq.le).trans
    (inf_le_left.trans le_sup_left)

theorem F₄_le_R₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaF₄ d t ≤ yamadaR₄ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, ⟨hE₄eq, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  exact ((le_sup_left : yamadaF₄ d t ≤ yamadaF₄ d t ⊔ zpowers t).trans hE₄eq.le).trans
    (inf_le_left.trans (h.yamadaL₄_facts hW d hK hD).2.2.2.2.1)

end Q44

open Q44

theorem yamadaM₅_eq_inf (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₅ d t = yamadaL₅ d t ⊓ yamadaS₅ d t ∧
      yamadaR₆ d t ≤ normalizer (yamadaM₅ d t : Set G) := by
  have htt := h.t_mul_t
  obtain ⟨-, ⟨-, hS₅N, htS₅⟩, ⟨hL₅M, hM₅N, htM₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, -, -, hR₅L₅, -⟩ := h.yamada_5_37_1 hW d hK hQ
  have hEq : yamadaM₅ d t = yamadaL₅ d t ⊓ yamadaS₅ d t := by
    refine le_antisymm (le_inf (M₅_le_L₅ hW h d hK hQ) (M₅_le_S₅ d t)) (fun x hx => ?_)
    obtain ⟨hxL, hxS⟩ := Subgroup.mem_inf.1 hx
    rw [← hL₅M] at hxL
    rcases (mem_sup_zpowers_iff_of htt hM₅N).1 hxL with h1 | ⟨a, ha, rfl⟩
    · exact h1
    · exfalso
      apply htS₅
      have := mul_mem (inv_mem (M₅_le_S₅ d t ha)) hxS
      rwa [inv_mul_cancel_left] at this
  refine ⟨hEq, sup_le ?_ ?_⟩
  · exact le_normalizer_of_forall_commutator_mem (commutator_mem_M₂ hW h d hK hQ)
      (M₂_le_M₅ d t) le_rfl (M₅_le_L₆ hW h d hK hQ)
  · intro s hs
    rw [hEq]
    exact Common.mem_normalizer_inf (hR₅L₅ (S_le_R₅ hW h d hK hQ hs))
      (Subgroup.le_normalizer (S_le_S₅ d t hs))

theorem yamadaS₅_eq_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaS₅ d t = d.S ⊔ yamadaF₅ d t ∧ yamadaM₅ d t = d.M ⊔ yamadaF₅ d t ∧
      yamadaD₅ d t = d.D ⊔ yamadaF₅ d t) ∧
    (d.S ⊓ yamadaF₅ d t = d.F ∧ d.M ⊓ yamadaF₅ d t = d.F ∧ d.D ⊓ yamadaF₅ d t = d.F) := by
  have hD := hQ.doubling
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, -, -, hDMF, -⟩ := d.yamada_defs
  have hSF₅ := S_le_normalizer_F₅ hW h d hK hQ
  have hF₅S₅ := F₅_le_S₅ d t
  have hW₃ := W₃_le_F₅ d t
  have hX₄ := X₄_le_F₅ d t
  have hY₂ := Y₂_le_F₅ d t
  have hS₅ : yamadaS₅ d t = d.S ⊔ yamadaF₅ d t := by
    refine le_antisymm (sup_le (sup_le (hW₃.trans le_sup_right) (sup_le le_sup_left
      (hY₂.trans le_sup_right))) (sup_le (hX₄.trans le_sup_right) (sup_le le_sup_left
      (hY₂.trans le_sup_right)))) (sup_le (S_le_S₅ d t) hF₅S₅)
  have hM₅ : yamadaM₅ d t = d.M ⊔ yamadaF₅ d t := by
    refine le_antisymm (sup_le (sup_le (hW₃.trans le_sup_right) (sup_le le_sup_left
      (hY₂.trans le_sup_right))) (sup_le (hX₄.trans le_sup_right) (sup_le le_sup_left
      (hY₂.trans le_sup_right)))) (sup_le (M_le_M₅ d t) (F₅_le_M₅ d t))
  have hSF : d.S ⊓ yamadaF₅ d t = d.F := by
    refine le_antisymm (fun x hx => ?_) (le_inf (hFD.trans hDS) (F_le_F₅ d t))
    obtain ⟨hxS, hxF₅⟩ := Subgroup.mem_inf.1 hx
    have hxD : x ∈ d.D := h.S_inf_yamadaCstar_le_D hW d hK hD
      (Subgroup.mem_inf.2 ⟨hxS, F₅_le_Cstar hW h d hK hQ hxF₅⟩)
    have hxM : x ∈ d.M := by
      rw [← h.yamadaL₆_inf_S hW d hK hQ]
      exact Subgroup.mem_inf.2 ⟨L₅_le_L₆ hW h d hK hQ (F₅_le_L₅ hW h d hK hQ hxF₅), hxS⟩
    rw [← hDMF]
    exact Subgroup.mem_inf.2 ⟨hxD, hxM⟩
  obtain ⟨-, -, ⟨hE₃eq, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, -, ⟨hE₄eq, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  have hF₃D₃ : yamadaF₃ d t ≤ yamadaD₃ d t := by
    refine le_inf (sup_le_sup_left (sup_le_sup_right (hFD.trans hDS) _) _) ?_
    exact ((le_sup_left : yamadaF₃ d t ≤ yamadaF₃ d t ⊔ zpowers t).trans hE₃eq.le).trans
      inf_le_right
  have hF₄D₄ : yamadaF₄ d t ≤ yamadaD₄ d t := by
    refine le_inf (sup_le_sup_left (sup_le_sup_right (hFD.trans hDS) _) _) ?_
    exact ((le_sup_left : yamadaF₄ d t ≤ yamadaF₄ d t ⊔ zpowers t).trans hE₄eq.le).trans
      inf_le_right
  have hF₅D₅ : yamadaF₅ d t ≤ yamadaD₅ d t := sup_le_sup hF₃D₃ hF₄D₄
  have hDD₅ : d.D ≤ yamadaD₅ d t := by
    refine (le_inf ?_ (le_inf ?_ (h.D_le_yamadaCstar d hK hD)) : d.D ≤ yamadaD₃ d t).trans
      le_sup_left
    · exact (hDS.trans (le_sup_left : d.S ≤ yamadaS₂ d t)).trans
        (le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t)
    · exact (hDS.trans (le_sup_right : d.S ≤ yamadaL₃ d t ⊔ d.S))
  refine ⟨⟨hS₅, hM₅, ?_⟩, hSF, ?_, ?_⟩
  · refine le_antisymm (fun x hx => ?_) (sup_le hDD₅ hF₅D₅)
    have hxC : x ∈ yamadaCstar d t := by
      have hC : x ∈ yamadaD₅ d t ⊔ zpowers t := mem_sup_left hx
      rw [(h.yamada_5_37_2 hW d hK hQ).2.2.2.1.1] at hC
      exact (Subgroup.mem_inf.1 hC).2
    have hxS₅ : x ∈ yamadaS₅ d t := (sup_le_sup inf_le_left inf_le_left :
      yamadaD₅ d t ≤ yamadaS₅ d t) hx
    rw [hS₅, sup_comm] at hxS₅
    obtain ⟨a, ha, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSF₅ x hxS₅
    have hsC : s ∈ yamadaCstar d t := by
      have := mul_mem (inv_mem (F₅_le_Cstar hW h d hK hQ ha)) hxC
      rwa [inv_mul_cancel_left] at this
    have hsD : s ∈ d.D := h.S_inf_yamadaCstar_le_D hW d hK hD (Subgroup.mem_inf.2 ⟨hs, hsC⟩)
    exact mul_mem (mem_sup_right ha) (mem_sup_left hsD)
  · exact le_antisymm ((inf_le_inf_right _ hMS).trans hSF.le) (le_inf hFM (F_le_F₅ d t))
  · exact le_antisymm ((inf_le_inf_right _ hDS).trans hSF.le) (le_inf hFD (F_le_F₅ d t))

namespace Q44

theorem wb_mul_self (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.wb * d.wb = 1 := (d.yamada_3_7_G (hK ▸ h.four_le)).2.2.2.1

theorem wb_inv (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.wb⁻¹ = d.wb := inv_eq_of_mul_eq_one_right (wb_mul_self h d hK)

theorem wb_mul_t (h : Setup G L f t) (d : G2Data L K) : d.wb * t = t * d.wb :=
  mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.wb_mem_normalizer.1.1)

theorem wb_conj_t (h : Setup G L f t) (d : G2Data L K) :
    d.wb⁻¹ * t * d.wb = t := by
  calc d.wb⁻¹ * t * d.wb = d.wb⁻¹ * (t * d.wb) := by group
    _ = d.wb⁻¹ * (d.wb * t) := by rw [wb_mul_t h d]
    _ = t := by group

theorem map_wb_map_wb (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (X : Subgroup G) :
    (X.map (MulAut.conj d.wb).toMonoidHom).map (MulAut.conj d.wb).toMonoidHom = X := by
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff, wb_inv h d hK]
  have : d.wb * (d.wb * x * d.wb) * d.wb = x := by
    calc d.wb * (d.wb * x * d.wb) * d.wb = (d.wb * d.wb) * x * (d.wb * d.wb) := by group
      _ = x := by rw [wb_mul_self h d hK]; group
  rw [this]

theorem mem_normalizer_map_conj {X : Subgroup G} {w g : G}
    (hg : w⁻¹ * g * w ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((X.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e : w⁻¹ * (g * y * g⁻¹) * w = (w⁻¹ * g * w) * (w⁻¹ * y * w) * (w⁻¹ * g * w)⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.1 hg (w⁻¹ * y * w)

theorem wb_mem_normalizer_Y₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.wb ∈ normalizer (yamadaY₂ d t : Set G) :=
  (h.normalizer_yamadaL₂_le d hK hD).2 (h.wb_mem_normalizer_yamadaL₂ d)

theorem wb_mem_normalizer_L₆ (h : Setup G L f t) (d : G2Data L K) :
    d.wb ∈ normalizer (yamadaL₆ d t : Set G) :=
  le_normalizer_yamadaL₆ d t (h.wb_mem_normalizer_yamadaL₂ d)

theorem wb_mem_normalizer_L₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wb ∈ normalizer (yamadaL₃ d t : Set G) := by
  rw [← (h.yamada_5_41_4 hW d hK hQ).1]
  exact h.wb_mem_normalizer_yamadaL₂ d

theorem wb_mem_normalizer_M₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wb ∈ normalizer (yamadaM₃ d t : Set G) :=
  (h.yamada_5_41_4 hW d hK hQ).2 (wb_mem_normalizer_L₃ hW h d hK hQ)

theorem wb_mem_normalizer_W₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.wb ∈ normalizer (yamadaW₃ d t : Set G) :=
  h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ hW d hK hQ (wb_mem_normalizer_L₃ hW h d hK hQ)

theorem F_inf_map_wb (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    d.F ⊓ d.F.map (MulAut.conj d.wb).toMonoidHom = d.W ∧
      d.F ⊔ d.F.map (MulAut.conj d.wb).toMonoidHom = d.M := by
  obtain ⟨-, hwW, hwM⟩ := d.wb_mem_normalizer
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  have hWm : d.W.map (MulAut.conj d.wb).toMonoidHom = d.W := map_conj_eq_of_mem_normalizer hwW
  have hMm : d.M.map (MulAut.conj d.wb).toMonoidHom = d.M := map_conj_eq_of_mem_normalizer hwM
  have hFwM : d.F.map (MulAut.conj d.wb).toMonoidHom ≤ d.M :=
    (Subgroup.map_mono hFM).trans hMm.le
  have hsup : d.F ⊔ d.F.map (MulAut.conj d.wb).toMonoidHom = d.M :=
    le_antisymm (sup_le hFM hFwM) (d.M_le_sup_conj.trans (sup_le (sup_le (hWF.trans le_sup_left)
      (hXF.trans le_sup_left)) ((Subgroup.map_mono hXF).trans le_sup_right)))
  refine ⟨?_, hsup⟩
  have hFwN : d.F.map (MulAut.conj d.wb).toMonoidHom ≤ normalizer (d.F : Set G) :=
    hFwM.trans (hMS.trans d.S_le_normalizers.2.2.2.2.1)
  have h1 := Common.card_sup_mul_card_inf_eq (A := d.F) hFwN
  rw [hsup, card_map_conj, d.cards.2.2.2.2.2.2.1, d.cards.2.2.2.2.1] at h1
  have hq : 0 < Nat.card K ^ 5 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have h2 : Nat.card (d.F ⊓ d.F.map (MulAut.conj d.wb).toMonoidHom : Subgroup G) =
      Nat.card K ^ 3 := by
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    rw [h1]
    ring
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hWF (hWm.ge.trans (Subgroup.map_mono hWF)))
    (by rw [h2, d.cards.2.2.2.1])).symm

theorem inv_conj_mem {X : Subgroup G} {w x : G} (hw : w ∈ normalizer (X : Set G)) (hx : x ∈ X) :
    w⁻¹ * x * w ∈ X := by
  have := (mem_normalizer_iff.1 (inv_mem hw) x).1 hx
  rwa [inv_inv] at this

theorem M_inf_F₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.M ⊓ yamadaF₂ d t = d.F := by
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  refine le_antisymm (fun x hx => ?_) (le_inf hFM (le_sup_left : d.F ≤ yamadaF₂ d t))
  obtain ⟨hxM, hxF₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨f₀, hf₀, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_F d hK hD) x hxF₂
  have hyM : y ∈ d.M := by
    have := mul_mem (inv_mem (hFM hf₀)) hxM
    rwa [inv_mul_cancel_left] at this
  have hyY : y ∈ d.Y := (h.M_inf_yamadaY₂ d hK hD).le (Subgroup.mem_inf.2 ⟨hyM, hy⟩)
  exact mul_mem hf₀ (hYX.trans hXF hyY)

theorem F₂_inf_map_wb (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaF₂ d t ⊓ (yamadaF₂ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaW₂ d t := by
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  obtain ⟨hFw, -⟩ := F_inf_map_wb h d hK
  obtain ⟨-, hwW, hwM⟩ := d.wb_mem_normalizer
  have hwY₂ := wb_mem_normalizer_Y₂ h d hK hD
  have hWm : d.W.map (MulAut.conj d.wb).toMonoidHom = d.W := map_conj_eq_of_mem_normalizer hwW
  have hYm : (yamadaY₂ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaY₂ d t :=
    map_conj_eq_of_mem_normalizer hwY₂
  refine le_antisymm (fun x hx => ?_) (le_inf (W₂_le_F₂ d t) (sup_le ?_ ?_))
  · obtain ⟨hxF₂, hxFw⟩ := Subgroup.mem_inf.1 hx
    rw [mem_map_conj_iff] at hxFw
    obtain ⟨f₀, hf₀, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaY₂_le_normalizer_F d hK hD) x hxF₂
    have hy' : d.wb⁻¹ * y * d.wb ∈ yamadaY₂ d t := inv_conj_mem hwY₂ hy
    have hfM : d.wb⁻¹ * f₀ * d.wb ∈ d.M := inv_conj_mem hwM (hFM hf₀)
    have hfF₂ : d.wb⁻¹ * f₀ * d.wb ∈ yamadaF₂ d t := by
      have := mul_mem hxFw (inv_mem (Y₂_le_F₂ d t hy'))
      rwa [show d.wb⁻¹ * (f₀ * y) * d.wb * (d.wb⁻¹ * y * d.wb)⁻¹ = d.wb⁻¹ * f₀ * d.wb by
        group] at this
    have hfF : d.wb⁻¹ * f₀ * d.wb ∈ d.F := (M_inf_F₂ h d hK hD).le (Subgroup.mem_inf.2 ⟨hfM, hfF₂⟩)
    have hfW : f₀ ∈ d.W := by
      rw [← hFw]
      exact Subgroup.mem_inf.2 ⟨hf₀, mem_map_conj_iff.2 hfF⟩
    exact mul_mem (le_sup_left (a := d.W) (b := yamadaY₂ d t) hfW) (le_sup_right (a := d.W) hy)
  · exact hWm.ge.trans (Subgroup.map_mono (hWF.trans le_sup_left))
  · exact hYm.ge.trans (Subgroup.map_mono (Y₂_le_F₂ d t))

theorem L₅_inf_map_wb (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₅ d t ⊓ (yamadaL₅ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaL₃ d t := by
  have hD := hQ.doubling
  have hwL₃ := wb_mem_normalizer_L₃ hW h d hK hQ
  have hL₃m : (yamadaL₃ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaL₃ d t :=
    map_conj_eq_of_mem_normalizer hwL₃
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sup_left : yamadaL₃ d t ≤ yamadaL₅ d t)
    (hL₃m.ge.trans (Subgroup.map_mono le_sup_left)))
  obtain ⟨hxL₅, hxL₅w⟩ := Subgroup.mem_inf.1 hx
  rw [mem_map_conj_iff] at hxL₅w
  have hR₅N : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  obtain ⟨f₂, hf₂, e₁⟩ := (h.yamada_5_21_3 hW d hK hD).1 x
    (hR₅N (L₅_le_R₅ hW h d hK hQ hxL₅))
  obtain ⟨f₂', hf₂', e₂⟩ := (h.yamada_5_21_3 hW d hK hD).1 _
    (hR₅N (L₅_le_R₅ hW h d hK hQ hxL₅w))
  have hwt : d.wb * t * d.wb⁻¹ = t := by rw [wb_mul_t h d]; group
  have e₃ : x * t * x⁻¹ = t * (d.wb * f₂' * d.wb⁻¹) := by
    calc x * t * x⁻¹
        = d.wb * ((d.wb⁻¹ * x * d.wb) * (d.wb⁻¹ * t * d.wb) * (d.wb⁻¹ * x * d.wb)⁻¹) *
            d.wb⁻¹ := by group
      _ = d.wb * ((d.wb⁻¹ * x * d.wb) * t * (d.wb⁻¹ * x * d.wb)⁻¹) * d.wb⁻¹ := by
          rw [wb_conj_t h d]
      _ = d.wb * (t * f₂') * d.wb⁻¹ := by rw [e₂]
      _ = (d.wb * t * d.wb⁻¹) * (d.wb * f₂' * d.wb⁻¹) := by group
      _ = t * (d.wb * f₂' * d.wb⁻¹) := by rw [hwt]
  have hf₂eq : f₂ = d.wb * f₂' * d.wb⁻¹ := mul_left_cancel (e₁.symm.trans e₃)
  have hf₂w : f₂ ∈ (yamadaF₂ d t).map (MulAut.conj d.wb).toMonoidHom := by
    rw [mem_map_conj_iff, hf₂eq]
    simpa [mul_assoc] using hf₂'
  have hf₂W : f₂ ∈ yamadaW₂ d t :=
    (F₂_inf_map_wb h d hK hD).le (Subgroup.mem_inf.2 ⟨hf₂, hf₂w⟩)
  have hxR₆ : x ∈ yamadaR₆ d t :=
    (le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) (L₅_le_L₆ hW h d hK hQ hxL₅)
  have htW₂ := (h.t_mem_normalizer_yamadaW₂ d hK hD).1
  have hcomm : ⁅x, t⁆ ∈ yamadaW₂ d t := by
    have : ⁅x, t⁆ = t * f₂ * t⁻¹ := by
      rw [commutatorElement_def, e₁]
    rw [this]
    exact (mem_normalizer_iff.1 htW₂ f₂).1 hf₂W
  have hxV₂ : x ∈ normalizer (yamadaV₂ d t : Set G) :=
    h.mem_normalizer_yamadaV₂_of_commutator_mem d
      (h.yamadaR₆_le_normalizer_yamadaW₂ hW d hK hQ hxR₆) hcomm
  exact (h.yamada_5_39_1 hW d hK hQ).2.le
    (Subgroup.mem_inf.2 ⟨L₅_le_L₆ hW h d hK hQ hxL₅, hxV₂⟩)

theorem t_mem_normalizer_W₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    t ∈ normalizer (yamadaW₃ d t : Set G) := by
  obtain ⟨-, hV₃N, -, -, -, hV₃eq, -⟩ := h.yamadaW₃_facts hW d hK hD
  exact hV₃N (hV₃eq.le (mem_sup_right (mem_zpowers t)))

theorem t_mem_normalizer_M₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    t ∈ normalizer (yamadaM₃ d t : Set G) :=
  mem_normalizer_sup (t_mem_normalizer_W₃ hW h d hK hD)
    (h.yamadaL₂_le_normalizer_yamadaM₂ d hK hD (h.tM_le_yamadaL₂ d hK
      (mem_sup_right (mem_zpowers t))))

theorem M₅_inf_L₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₅ d t ⊓ yamadaL₃ d t = yamadaM₃ d t := by
  have hD := hQ.doubling
  have htt := h.t_mul_t
  obtain ⟨-, -, -, ⟨hL₃eq, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, -, ⟨-, -, htM₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  refine le_antisymm (fun x hx => ?_)
    (le_inf (le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t)
      ((le_sup_left : yamadaM₃ d t ≤ yamadaM₃ d t ⊔ zpowers t).trans hL₃eq.le))
  obtain ⟨hxM₅, hxL₃⟩ := Subgroup.mem_inf.1 hx
  rcases (mem_sup_zpowers_iff_of htt (t_mem_normalizer_M₃ hW h d hK hD)).1 (hL₃eq.ge hxL₃) with
    h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    apply htM₅
    have := mul_mem (inv_mem ((le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t) ha)) hxM₅
    rwa [inv_mul_cancel_left] at this

theorem M₅_inf_map_wb (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₅ d t ⊓ (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaM₃ d t := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t)
      ((map_conj_eq_of_mem_normalizer (wb_mem_normalizer_M₃ hW h d hK hQ)).ge.trans
        (Subgroup.map_mono (le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t))))
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  have hxL₃ : x ∈ yamadaL₃ d t := (L₅_inf_map_wb hW h d hK hQ).le
    (Subgroup.mem_inf.2 ⟨M₅_le_L₅ hW h d hK hQ hx₁,
      Subgroup.map_mono (M₅_le_L₅ hW h d hK hQ) hx₂⟩)
  exact (M₅_inf_L₃ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hx₁, hxL₃⟩)

theorem card_five (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaR₅ d t) = 2 * Nat.card K ^ 10 ∧ Nat.card (yamadaL₅ d t) = 2 * Nat.card K ^ 9 ∧
      Nat.card (yamadaM₅ d t) = Nat.card K ^ 9 ∧ Nat.card (yamadaS₅ d t) = Nat.card K ^ 10 ∧
      Nat.card (yamadaM₃ d t) = Nat.card K ^ 8 := by
  have hD := hQ.doubling
  obtain ⟨-, ⟨hR₅S, hS₅N, htS₅⟩, ⟨hL₅M, hM₅N, htM₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, hR₅eq, hL₅R₃, hR₅L₅, -, -, -, hcard⟩ := h.yamada_5_37_1 hW d hK hQ
  obtain ⟨-, -, -, ⟨hL₃eq, htM₃⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨hL₃c, hR₃c⟩ := h.card_yamadaL₃_R₃ hW d hK hD
  have hq : 0 < Nat.card K := Nat.card_pos
  have hR₅c : Nat.card (yamadaR₅ d t) = 2 * Nat.card K ^ 10 := by
    rw [hcard, hL₃c]
    ring
  have hL₅c : Nat.card (yamadaL₅ d t) = 2 * Nat.card K ^ 9 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaL₅ d t) (B := yamadaR₃ d t)
      ((hR₅eq ▸ le_sup_right : yamadaR₃ d t ≤ yamadaR₅ d t).trans hR₅L₅)
    rw [← hR₅eq, hL₅R₃, hR₅c, hL₃c, hR₃c] at h1
    have : 0 < 2 * Nat.card K ^ 9 := by positivity
    refine Nat.eq_of_mul_eq_mul_right this ?_
    rw [← h1]
    ring
  have hM₅c : Nat.card (yamadaM₅ d t) = Nat.card K ^ 9 := by
    have := h.card_sup_zpowers hM₅N htM₅
    rw [hL₅M, hL₅c] at this
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) this).symm
  have hS₅c : Nat.card (yamadaS₅ d t) = Nat.card K ^ 10 := by
    have := h.card_sup_zpowers hS₅N htS₅
    rw [hR₅S, hR₅c] at this
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) this).symm
  have hM₃c : Nat.card (yamadaM₃ d t) = Nat.card K ^ 8 := by
    have := h.card_sup_zpowers (t_mem_normalizer_M₃ hW h d hK hD) htM₃
    rw [hL₃eq, hL₃c] at this
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) this).symm
  exact ⟨hR₅c, hL₅c, hM₅c, hS₅c, hM₃c⟩

theorem t_mem_L₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : t ∈ yamadaL₅ d t :=
  (h.yamada_5_37_2 hW d hK hQ).2.2.1.1.le (mem_sup_right (mem_zpowers t))

theorem t_mem_L₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : t ∈ yamadaL₆ d t :=
  L₅_le_L₆ hW h d hK hQ (t_mem_L₅ hW h d hK hQ)

theorem map_wb_M₅_le_L₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom ≤ yamadaL₆ d t :=
  (Subgroup.map_mono (M₅_le_L₆ hW h d hK hQ)).trans
    (map_conj_eq_of_mem_normalizer (wb_mem_normalizer_L₆ h d)).le

theorem L₆_le_normalizer_M₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤ normalizer (yamadaM₅ d t : Set G) :=
  (le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t).trans (yamadaM₅_eq_inf hW h d hK hQ).2

theorem L₆_le_normalizer_map_wb (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaL₆ d t ≤ normalizer ((yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) :=
  fun x hx => mem_normalizer_map_conj
    (L₆_le_normalizer_M₅ hW h d hK hQ (inv_conj_mem (wb_mem_normalizer_L₆ h d) hx))

theorem M₆_le_L₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaM₆ d t ≤ yamadaL₆ d t :=
  sup_le (M₅_le_L₆ hW h d hK hQ) (map_wb_M₅_le_L₆ hW h d hK hQ)

theorem t_mem_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    t ∈ normalizer (yamadaM₆ d t : Set G) := by
  have htM₅N : t ∈ normalizer (yamadaM₅ d t : Set G) := (h.yamada_5_37_2 hW d hK hQ).2.2.1.2.1
  exact mem_normalizer_sup htM₅N (mem_normalizer_map_conj (by rw [wb_conj_t h d]; exact htM₅N))

theorem t_not_mem_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : t ∉ yamadaM₆ d t := by
  intro ht
  obtain ⟨-, -, ⟨-, -, htM₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  have hset : (yamadaM₆ d t : Set G) = (yamadaM₅ d t : Set G) *
      (((yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom : Subgroup G) : Set G) :=
    coe_sup_eq_mul fun a ha => L₆_le_normalizer_map_wb hW h d hK hQ (M₅_le_L₆ hW h d hK hQ ha)
  have ht' : t ∈ ((yamadaM₆ d t : Subgroup G) : Set G) := ht
  rw [hset] at ht'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 ht'
  have hbL₅ : b ∈ yamadaL₅ d t := by
    have : b = a⁻¹ * t := by rw [← hab]; group
    rw [this]
    exact mul_mem (inv_mem (M₅_le_L₅ hW h d hK hQ ha)) (t_mem_L₅ hW h d hK hQ)
  have hbL₃ : b ∈ yamadaL₃ d t := (L₅_inf_map_wb hW h d hK hQ).le
    (Subgroup.mem_inf.2 ⟨hbL₅, Subgroup.map_mono (M₅_le_L₅ hW h d hK hQ) hb⟩)
  have hb' : d.wb⁻¹ * b * d.wb ∈ yamadaM₅ d t := mem_map_conj_iff.1 hb
  have hb'L₃ : d.wb⁻¹ * b * d.wb ∈ yamadaL₃ d t :=
    inv_conj_mem (wb_mem_normalizer_L₃ hW h d hK hQ) hbL₃
  have hb'M₃ := (M₅_inf_L₃ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hb', hb'L₃⟩)
  have hbM₃ : b ∈ yamadaM₃ d t := by
    have : b ∈ (yamadaM₃ d t).map (MulAut.conj d.wb).toMonoidHom := mem_map_conj_iff.2 hb'M₃
    rwa [map_conj_eq_of_mem_normalizer (wb_mem_normalizer_M₃ hW h d hK hQ)] at this
  apply htM₅
  have := mul_mem ha ((le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t) hbM₃)
  rwa [hab] at this

theorem card_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaM₆ d t) = Nat.card K ^ 10 := by
  obtain ⟨-, -, hM₅c, -, hM₃c⟩ := card_five hW h d hK hQ
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaM₅ d t)
    (B := (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom)
    ((map_wb_M₅_le_L₆ hW h d hK hQ).trans (L₆_le_normalizer_M₅ hW h d hK hQ))
  rw [M₅_inf_map_wb hW h d hK hQ, card_map_conj, hM₅c, hM₃c] at h1
  have hq : 0 < Nat.card K ^ 8 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [show yamadaM₆ d t =
    yamadaM₅ d t ⊔ (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom from rfl, h1]
  ring

theorem L₆_eq_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊔ zpowers t = yamadaL₆ d t := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le (M₆_le_L₆ hW h d hK hQ)
    ((zpowers_le).2 (t_mem_L₆ hW h d hK hQ))) ?_
  rw [h.card_sup_zpowers (t_mem_normalizer_M₆ hW h d hK hQ) (t_not_mem_M₆ hW h d hK hQ),
    card_M₆ hW h d hK hQ, h.card_yamadaL₆ hW d hK hQ]

theorem J_le_normalizer_L₆ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.J ≤ normalizer (yamadaL₆ d t : Set G) :=
  (h.J_le_normalizer_yamadaL₂ d hK hD).trans (le_normalizer_yamadaL₆ d t)

theorem J_le_normalizer_M (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : d.J ≤ normalizer (d.M : Set G) := by
  have hD := hQ.doubling
  intro j hj
  rw [← h.yamadaL₆_inf_S hW d hK hQ]
  exact Common.mem_normalizer_inf (J_le_normalizer_L₆ h d hK hD hj)
    (h.J_le_centralizer_inf_normalizer_S d hj).2

theorem J_le_normalizer_five (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaL₅ d t : Set G) ∧ d.J ≤ normalizer (yamadaS₅ d t : Set G) ∧
      d.J ≤ normalizer (yamadaM₅ d t : Set G) := by
  have hD := hQ.doubling
  have hJL₃ : d.J ≤ normalizer (yamadaL₃ d t : Set G) := by
    rw [← (h.yamada_5_41_4 hW d hK hQ).1]
    exact h.J_le_normalizer_yamadaL₂ d hK hD
  obtain ⟨-, -, hJW₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, hJX₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  have hJS₂ := h.J_le_normalizer_yamadaS₂ d hK hD
  have hJL₅ : d.J ≤ normalizer (yamadaL₅ d t : Set G) := fun j hj =>
    mem_normalizer_sup (hJL₃ hj) ((h.J_le_normalizers_four hW d hK hD).1 hj)
  have hJS₅ : d.J ≤ normalizer (yamadaS₅ d t : Set G) := fun j hj =>
    mem_normalizer_sup (mem_normalizer_sup (hJW₃ hj) (hJS₂ hj))
      (mem_normalizer_sup (hJX₄ hj) (hJS₂ hj))
  refine ⟨hJL₅, hJS₅, fun j hj => ?_⟩
  rw [(yamadaM₅_eq_inf hW h d hK hQ).1]
  exact Common.mem_normalizer_inf (hJL₅ hj) (hJS₅ hj)

theorem J_le_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.J ≤ normalizer (yamadaM₆ d t : Set G) := fun j hj =>
  mem_normalizer_sup ((J_le_normalizer_five hW h d hK hQ).2.2 hj)
    (mem_normalizer_map_conj ((J_le_normalizer_five hW h d hK hQ).2.2
      (inv_conj_mem (h.wb_mem_normalizer_J d hK) hj)))

theorem rootGroup_yamadaRoot_le_centralizer_Ji (d : G2Data L K) (i : Fin 6) :
    d.rootGroup (Model.yamadaRoot i) ≤ centralizer (d.Ji i : Set G) := by
  have h := d.image_inf_centralizer (rootSubgroup .G2 K (Model.yamadaRoot i))
    (G2Data.Ji_le_adjointGroup (K := K) i)
  rw [inf_eq_left.2 (Model.rootSubgroup_yamadaRoot_le_centralizer (K := K) i)] at h
  intro x hx
  have hx' : x ∈ d.image (rootSubgroup .G2 K (Model.yamadaRoot i)) := hx
  rw [h] at hx'
  exact hx'.2

theorem S_inf_centralizer_J₄_le_D (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hQ : h.QFacts d) : d.S ⊓ centralizer (d.Ji 3 : Set G) ≤ d.D := by
  rcases hQ.branch with h8 | ⟨hK4, -⟩
  · rw [S_inf_centralizer_Ji_of_four_le d (hK ▸ h.four_le) 3 (Or.inl h8)]
    exact le_sup_left.trans (d.yamada_defs).2.2.2.2.1.le
  · rw [show (d.Ji 3 : Subgroup G) = d.J₁ from (d.yamada_3_9_4_four_G hK4).1.symm,
      d.S_inf_centralizer_J₁_four hK4]
    exact d.sbY_le_D

theorem mem_R₅_of_forall_J₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₆ d t)
    (hfix : ∀ j ∈ d.Ji 3, x⁻¹ * (j * x * j⁻¹) ∈ yamadaR₅ d t) : x ∈ yamadaR₅ d t := by
  have hD := hQ.doubling
  have hFM : d.F ≤ d.M := d.inclusions.2.2.2.2.2.2.1
  have hMS : d.M ≤ d.S := d.inclusions.2.2.2.2.2.2.2.2.1
  obtain ⟨hN, hFN, φ, hφ, hφc⟩ := h.yamada_5_40_3 hW d hK hQ
  have hκ : t * x * t * x⁻¹ ∈ yamadaM₂ d t :=
    h.crossed_mem_yamadaM₂ d hK hD (h.yamadaR₆_le_normalizer_yamadaL₂ d hx)
  obtain ⟨m, hm, y, hy, hmy⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaY₂_le_normalizer_M d hK hD) _ hκ
  have hxt : x * t * x⁻¹ = t * m * y := by
    rw [h.conj_t_eq_mul_crossed x, hmy]
    group
  have hX : φ (QuotientGroup.mk (⟨x, hx⟩ : yamadaR₆ d t)) = QuotientGroup.mk ⟨m, hm⟩ :=
    hφ ⟨x, hx⟩ ⟨m, hm⟩ y hy hxt
  have hJ₄J : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hfixM : ∀ j ∈ d.Ji 3, m⁻¹ * (j * m * j⁻¹) ∈ d.F := by
    intro j hj
    have hjC := h.J_le_centralizer_inf_normalizer_S d (hJ₄J hj)
    obtain ⟨hjx, hjm, e⟩ := hφc j hjC ⟨x, hx⟩ ⟨m, hm⟩ hX
    have h1 : (QuotientGroup.mk (⟨j * x * j⁻¹, hjx⟩ : yamadaR₆ d t) :
        yamadaR₆ d t ⧸ (yamadaR₅ d t).subgroupOf (yamadaR₆ d t)) =
        QuotientGroup.mk (⟨x, hx⟩ : yamadaR₆ d t) := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      have := inv_mem (hfix j hj)
      rwa [mul_inv_rev, inv_inv] at this
    rw [h1, hX] at e
    exact mem_subgroupOf.1 (QuotientGroup.eq.1 e)
  have hMp : IsPGroup 2 d.M := d.isSylowOf_S.isPGroup.to_le hMS
  have hMN : d.M ≤ normalizer (d.F : Set G) := hMS.trans d.S_le_normalizers.2.2.2.2.1
  obtain ⟨c, hc, n, hn, hmcn⟩ := exists_centralizer_mul_of_le_J d hJ₄J hFM hMN
    (fun j hj => J_le_normalizer_M hW h d hK hQ (hJ₄J hj))
    (fun j hj => h.centralizer_inf_normalizer_S_le_normalizer_F d hK hD
      (h.J_le_centralizer_inf_normalizer_S d (hJ₄J hj))) hMp hm hfixM
  have hcF : c ∈ d.F := by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
    exact Subgroup.mem_inf.2 ⟨S_inf_centralizer_J₄_le_D h d hK hQ (Subgroup.mem_inf.2
      ⟨hMS (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩), (Subgroup.mem_inf.1 hc).1⟩
  have hmF : m ∈ d.F := by
    rw [hmcn]
    exact mul_mem hcF hn
  have h1 : φ (QuotientGroup.mk (⟨x, hx⟩ : yamadaR₆ d t)) = 1 := by
    rw [hX, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hmF
  rw [map_eq_one_iff φ φ.injective, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

theorem M₆_inf_centralizer_J₄_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ centralizer (d.Ji 3 : Set G) ≤ yamadaM₅ d t := by
  have htt := h.t_mul_t
  obtain ⟨-, -, ⟨hL₅M, hM₅N, htM₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  intro c hc
  obtain ⟨hcM₆, hcC⟩ := Subgroup.mem_inf.1 hc
  have hcL₆ := M₆_le_L₆ hW h d hK hQ hcM₆
  have hcR₅ : c ∈ yamadaR₅ d t := mem_R₅_of_forall_J₄ hW h d hK hQ
    ((le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) hcL₆) (fun j hj => by
      rw [mem_centralizer_iff.1 hcC j hj, mul_inv_cancel_right, inv_mul_cancel]
      exact one_mem _)
  have hcL₅ : c ∈ yamadaL₅ d t := (h.yamada_5_40_4 hW d hK hQ).ge (Subgroup.mem_inf.2 ⟨hcL₆, hcR₅⟩)
  rw [← hL₅M] at hcL₅
  rcases (mem_sup_zpowers_iff_of htt hM₅N).1 hcL₅ with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    refine t_not_mem_M₆ hW h d hK hQ ?_
    have := mul_mem (inv_mem ((le_sup_left : yamadaM₅ d t ≤ yamadaM₆ d t) ha)) hcM₆
    rwa [inv_mul_cancel_left] at this

theorem commutator_L₆_J_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ⁅yamadaL₆ d t, d.J⁆ ≤ yamadaM₆ d t := by
  refine Subgroup.commutator_le.2 fun x hx j hj => ?_
  have htj : j * t = t * j :=
    mem_centralizer_singleton_iff.1 (h.J_le_centralizer_inf_normalizer_S d hj).1
  have hjM := J_le_normalizer_M₆ hW h d hK hQ hj
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (t_mem_normalizer_M₆ hW h d hK hQ)).1
    ((L₆_eq_sup hW h d hK hQ).ge hx) with h1 | ⟨a, ha, rfl⟩
  · rw [commutatorElement_def, show x * j * x⁻¹ * j⁻¹ = x * (j * x⁻¹ * j⁻¹) by group]
    exact mul_mem h1 ((mem_normalizer_iff.1 hjM x⁻¹).1 (inv_mem h1))
  · have e : t * j * t⁻¹ = j := by rw [← htj]; group
    rw [commutatorElement_def]
    have e2 : a * t * j * (a * t)⁻¹ * j⁻¹ = a * (j * a⁻¹ * j⁻¹) := by
      calc a * t * j * (a * t)⁻¹ * j⁻¹ = a * (t * j * t⁻¹) * a⁻¹ * j⁻¹ := by group
        _ = a * (j * a⁻¹ * j⁻¹) := by rw [e]; group
    rw [e2]
    exact mul_mem ha ((mem_normalizer_iff.1 hjM a⁻¹).1 (inv_mem ha))

theorem S_le_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    d.S ≤ normalizer (yamadaM₆ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  obtain ⟨-, -, -, -, haD, -, -, -, hDMS⟩ := d.yamada_defs
  have hJ₄J : d.Ji 3 ≤ d.J := d.image_mono inf_le_left
  have hSbS : d.rootGroup g2a ≤ d.S := (le_sup_left.trans haD.le).trans hDS
  have hSN := d.S_le_normalizers.2.2.2.2.2.2
  have hS : d.S ≤ d.M ⊔ d.rootGroup g2a :=
    hDMS.ge.trans (sup_le (haD.ge.trans (sup_le le_sup_right (hFM.trans le_sup_left))) le_sup_left)
  have hMM₆ : d.M ≤ yamadaM₆ d t := (M_le_M₅ d t).trans le_sup_left
  have hSb : ∀ u ∈ d.rootGroup g2a, u ∈ normalizer (yamadaM₆ d t : Set G) := by
    intro u hu
    have huS : u ∈ d.S := hSbS hu
    have huC : u ∈ centralizer (d.Ji 3 : Set G) :=
      rootGroup_yamadaRoot_le_centralizer_Ji d 3 hu
    have huL₆ : u ∈ normalizer (yamadaL₆ d t : Set G) := h.S_le_normalizer_yamadaL₆ d huS
    have huJ : u ∈ normalizer ((d.Ji 3 : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ huC
    have huM₅ : u ∈ normalizer (yamadaM₅ d t : Set G) :=
      (yamadaM₅_eq_inf hW h d hK hQ).2 ((le_sup_right : d.S ≤ yamadaR₆ d t) huS)
    have huComm : u ∈ normalizer ((⁅yamadaL₆ d t, d.Ji 3⁆ : Subgroup G) : Set G) :=
      mem_normalizer_commutator huL₆ huJ
    refine mem_normalizer_fintype fun m hm => ?_
    have hfix : ∀ a ∈ d.Ji 3, m⁻¹ * (a * m * a⁻¹) ∈ ⁅yamadaM₆ d t, d.Ji 3⁆ := fun a ha => by
      rw [show m⁻¹ * (a * m * a⁻¹) = ⁅m⁻¹, a⁆ by simp only [commutatorElement_def]; group]
      exact Subgroup.commutator_mem_commutator (inv_mem hm) ha
    have hNM : ⁅yamadaM₆ d t, d.Ji 3⁆ ≤ yamadaM₆ d t :=
      Subgroup.commutator_le.2 fun m' hm' j hj => by
        rw [commutatorElement_def, show m' * j * m'⁻¹ * j⁻¹ = m' * (j * m'⁻¹ * j⁻¹) by group]
        exact mul_mem hm' ((mem_normalizer_iff.1 (J_le_normalizer_M₆ hW h d hK hQ (hJ₄J hj)) m'⁻¹).1
          (inv_mem hm'))
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_mul_of_le_J d hJ₄J hNM
      (le_normalizer_commutator_left _ _) (fun j hj => J_le_normalizer_M₆ hW h d hK hQ (hJ₄J hj))
      (fun j hj => mem_normalizer_commutator (J_le_normalizer_M₆ hW h d hK hQ (hJ₄J hj))
        (Subgroup.le_normalizer hj))
      ((h.isPGroup_yamadaR₆ d).to_le ((M₆_le_L₆ hW h d hK hQ).trans le_sup_left)) hm hfix
    have hcM₅ : c ∈ yamadaM₅ d t := M₆_inf_centralizer_J₄_le hW h d hK hQ hc
    have hn' : u * n * u⁻¹ ∈ yamadaM₆ d t :=
      (Subgroup.commutator_mono le_rfl hJ₄J).trans (commutator_L₆_J_le hW h d hK hQ)
        ((mem_normalizer_iff.1 huComm n).1
          (Subgroup.commutator_mono (M₆_le_L₆ hW h d hK hQ) le_rfl hn))
    have hc' : u * c * u⁻¹ ∈ yamadaM₆ d t :=
      (le_sup_left : yamadaM₅ d t ≤ yamadaM₆ d t) ((mem_normalizer_iff.1 huM₅ c).1 hcM₅)
    rw [show u * (c * n) * u⁻¹ = (u * c * u⁻¹) * (u * n * u⁻¹) by group]
    exact mul_mem hc' hn'
  intro s hs
  obtain ⟨m, hm, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer
    (fun x hx => hSN (hSbS hx)) s (hS hs)
  exact mul_mem (Subgroup.le_normalizer (hMM₆ hm)) (hSb u hu)

end Q44

theorem card_yamada_five_six (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaR₅ d t) = 2 * Nat.card K ^ 10 ∧ Nat.card (yamadaL₅ d t) = 2 * Nat.card K ^ 9 ∧
      Nat.card (yamadaM₅ d t) = Nat.card K ^ 9 ∧ Nat.card (yamadaF₅ d t) = Nat.card K ^ 8 ∧
      Nat.card (yamadaS₅ d t) = Nat.card K ^ 10 ∧ Nat.card (yamadaL₆ d t) = 2 * Nat.card K ^ 10 ∧
      Nat.card (yamadaM₆ d t) = Nat.card K ^ 10 ∧ Nat.card (yamadaS₆ d t) = Nat.card K ^ 11 ∧
      Nat.card (yamadaR₆ d t) = 2 * Nat.card K ^ 11 := by
  obtain ⟨hR₅c, hL₅c, hM₅c, hS₅c, -⟩ := card_five hW h d hK hQ
  obtain ⟨⟨hS₅, -, -⟩, hSF, -, -⟩ := yamadaS₅_eq_sup hW h d hK hQ
  have hq : 0 < Nat.card K := Nat.card_pos
  have hMS : d.M ≤ d.S := d.inclusions.2.2.2.2.2.2.2.2.1
  have hMc := d.cards.2.2.2.2.2.2.1
  have hScard := d.cards.2.2.2.2.2.2.2
  have hFc := d.cards.2.2.2.2.1
  have hF₅c : Nat.card (yamadaF₅ d t) = Nat.card K ^ 8 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaF₅ d t) (B := d.S)
      (S_le_normalizer_F₅ hW h d hK hQ)
    rw [sup_comm, ← hS₅, inf_comm, hSF, hS₅c, hFc, hScard] at h1
    have : 0 < Nat.card K ^ 6 := by positivity
    refine Nat.eq_of_mul_eq_mul_right this ?_
    rw [← h1]
    ring
  have hL₆S := h.yamadaL₆_inf_S hW d hK hQ
  have hM₆S : yamadaM₆ d t ⊓ d.S = d.M :=
    le_antisymm (hL₆S.le.trans' (inf_le_inf_right _ (M₆_le_L₆ hW h d hK hQ)))
      (le_inf ((M_le_M₅ d t).trans le_sup_left) hMS)
  have hL₆c := h.card_yamadaL₆ hW d hK hQ
  have hM₆c := card_M₆ hW h d hK hQ
  have hS₆c : Nat.card (yamadaS₆ d t) = Nat.card K ^ 11 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaM₆ d t) (B := d.S)
      (S_le_normalizer_M₆ hW h d hK hQ)
    rw [hM₆S, hM₆c, hMc, hScard] at h1
    have : 0 < Nat.card K ^ 5 := by positivity
    refine Nat.eq_of_mul_eq_mul_right this ?_
    rw [show yamadaS₆ d t = yamadaM₆ d t ⊔ d.S from rfl, h1]
    ring
  have hR₆c : Nat.card (yamadaR₆ d t) = 2 * Nat.card K ^ 11 := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaL₆ d t) (B := d.S)
      (h.S_le_normalizer_yamadaL₆ d)
    rw [hL₆S, hL₆c, hMc, hScard] at h1
    have : 0 < Nat.card K ^ 5 := by positivity
    refine Nat.eq_of_mul_eq_mul_right this ?_
    rw [show yamadaR₆ d t = yamadaL₆ d t ⊔ d.S from rfl, h1]
    ring
  exact ⟨hR₅c, hL₅c, hM₅c, hF₅c, hS₅c, hL₆c, hM₆c, hS₆c, hR₆c⟩

theorem yamadaE₃_inf_E₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaE₃ d t ⊓ yamadaE₄ d t = yamadaE₂ d t ∧ yamadaF₅ d t ⊓ yamadaR₃ d t = yamadaF₃ d t ∧
      yamadaF₅ d t ⊓ yamadaR₄ d t = yamadaF₄ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨-, -, -, hsetF⟩, -, -, -, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, hR₃R₄, -, -⟩ := (h.yamada_5_27_2 hW d hK hD).1
  obtain ⟨hE₂E₃, -, -, -, hLC₃, -⟩ := h.yamadaE₃_facts hW d hK hD
  obtain ⟨hE₂E₄, -⟩ := h.yamadaE₄_facts hW d hK hD
  obtain ⟨-, -, -, -, hC₂⟩ := h.yamadaR₃_facts hW d hK hD
  have hF₃R₃ := F₃_le_R₃ hW h d hK hQ
  have hF₄R₄ := F₄_le_R₄ hW h d hK hQ
  refine ⟨le_antisymm (fun x hx => ?_) (le_inf hE₂E₃ hE₂E₄), ?_, ?_⟩
  · obtain ⟨hxE₃, hxE₄⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxL₃, hxC₃⟩ := Subgroup.mem_inf.1 hxE₃
    obtain ⟨hxR₃, hxC⟩ := Subgroup.mem_inf.1 hxC₃
    have hxR₄ : x ∈ yamadaR₄ d t := (h.yamadaL₄_facts hW d hK hD).2.2.2.2.1
      (Subgroup.mem_inf.1 hxE₄).1
    have hxR₂ : x ∈ yamadaR₂ d t := by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨hxR₃, hxR₄⟩
    have hxC₂ : x ∈ yamadaC₂ d t := by
      rw [hC₂]
      exact Subgroup.mem_inf.2 ⟨hxC, hxR₂⟩
    exact hLC₃ (Subgroup.mem_inf.2 ⟨hxL₃, hxC₂⟩)
  · refine le_antisymm (fun x hx => ?_) (le_inf (F₃_le_F₅ d t) hF₃R₃)
    obtain ⟨hxF₅, hxR₃⟩ := Subgroup.mem_inf.1 hx
    have hx' : x ∈ ((yamadaF₅ d t : Subgroup G) : Set G) := hxF₅
    rw [hsetF] at hx'
    obtain ⟨f₃, hf₃, f₄, hf₄, rfl⟩ := Set.mem_mul.1 hx'
    have hf₄R₃ : f₄ ∈ yamadaR₃ d t := by
      have := mul_mem (inv_mem (hF₃R₃ hf₃)) hxR₃
      rwa [inv_mul_cancel_left] at this
    have hf₄R₂ : f₄ ∈ yamadaR₂ d t := by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨hf₄R₃, hF₄R₄ hf₄⟩
    exact mul_mem hf₃ (F₂_le_F₃ d t (F₄_inf_R₂_le hW h d hK hQ
      (Subgroup.mem_inf.2 ⟨hf₄, hf₄R₂⟩)))
  · refine le_antisymm (fun x hx => ?_) (le_inf (F₄_le_F₅ d t) hF₄R₄)
    obtain ⟨hxF₅, hxR₄⟩ := Subgroup.mem_inf.1 hx
    have hx' : x ∈ ((yamadaF₅ d t : Subgroup G) : Set G) := hxF₅
    rw [hsetF] at hx'
    obtain ⟨f₃, hf₃, f₄, hf₄, rfl⟩ := Set.mem_mul.1 hx'
    have hf₃R₄ : f₃ ∈ yamadaR₄ d t := by
      have := mul_mem hxR₄ (inv_mem (hF₄R₄ hf₄))
      rwa [mul_inv_cancel_right] at this
    have hf₃R₂ : f₃ ∈ yamadaR₂ d t := by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨hF₃R₃ hf₃, hf₃R₄⟩
    exact mul_mem (F₂_le_F₄ d t (F₃_inf_R₂_le hW h d hK hQ
      (Subgroup.mem_inf.2 ⟨hf₃, hf₃R₂⟩))) hf₄

namespace Q44

theorem F₃_le_sup (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaF₃ d t ≤ yamadaW₃ d t ⊔ d.F := by
  obtain ⟨-, -, -, hW₂W₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  exact sup_le le_sup_left (sup_le le_sup_right
    (((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans hW₂W₃).trans le_sup_left))

theorem coe_eq_mul_of_card {A B P : Subgroup G} (hA : A ≤ P) (hB : B ≤ P)
    (hcard : Nat.card A * Nat.card B = Nat.card P * Nat.card (A ⊓ B : Subgroup G)) :
    (P : Set G) = (A : Set G) * (B : Set G) :=
  (CFSG.SignalizerFunctor.Helpers.subgroup_product_eq_of_card_formula P A B hA hB hcard).symm

theorem F₅_inf_map_wb (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₅ d t ⊓ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaW₃ d t := by
  have hD := hQ.doubling
  obtain ⟨hUY, hYX, hYW, hXF, hWF, hFD, hFM, hDS, hMS, hSL⟩ := d.inclusions
  obtain ⟨hFw, hFwM⟩ := F_inf_map_wb h d hK
  obtain ⟨-, hwW, hwM⟩ := d.wb_mem_normalizer
  have hwL₃ := wb_mem_normalizer_L₃ hW h d hK hQ
  have hwW₃ := wb_mem_normalizer_W₃ hW h d hK hQ
  obtain ⟨-, -, -, hW₂W₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  have hWW₃ : d.W ≤ yamadaW₃ d t := (le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂W₃
  have hR₃ : yamadaR₃ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun x hx =>
    (h.yamadaR₃_le_normalizer_W₃_V₃ hW d hK hQ hx).1
  have hFN : d.F ≤ normalizer (yamadaW₃ d t : Set G) :=
    (hFD.trans hDS).trans ((le_sup_right : d.S ≤ yamadaR₃ d t).trans hR₃)
  have hWm : (yamadaW₃ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaW₃ d t :=
    map_conj_eq_of_mem_normalizer hwW₃
  refine le_antisymm (fun x hx => ?_)
    (le_inf (W₃_le_F₅ d t) (hWm.ge.trans (Subgroup.map_mono (W₃_le_F₅ d t))))
  obtain ⟨hxF₅, hxF₅w⟩ := Subgroup.mem_inf.1 hx
  rw [mem_map_conj_iff] at hxF₅w
  have hxL₃ : x ∈ yamadaL₃ d t := (L₅_inf_map_wb hW h d hK hQ).le (Subgroup.mem_inf.2
    ⟨F₅_le_L₅ hW h d hK hQ hxF₅, mem_map_conj_iff.2 (F₅_le_L₅ hW h d hK hQ hxF₅w)⟩)
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := le_sup_left
  have hxF₃ : x ∈ yamadaF₃ d t :=
    (yamadaE₃_inf_E₄ hW h d hK hQ).2.1.le (Subgroup.mem_inf.2 ⟨hxF₅, hL₃R₃ hxL₃⟩)
  have hx'F₃ : d.wb⁻¹ * x * d.wb ∈ yamadaF₃ d t :=
    (yamadaE₃_inf_E₄ hW h d hK hQ).2.1.le (Subgroup.mem_inf.2 ⟨hxF₅w,
      hL₃R₃ (inv_conj_mem hwL₃ hxL₃)⟩)
  obtain ⟨a, ha, f₀, hf₀, rfl⟩ := Common.exists_mul_of_le_normalizer hFN x
    (F₃_le_sup hW h d hK hD hxF₃)
  obtain ⟨a', ha', f', hf', hxe⟩ := Common.exists_mul_of_le_normalizer hFN _
    (F₃_le_sup hW h d hK hD hx'F₃)
  set a'' := d.wb * a' * d.wb⁻¹ with ha''
  set f'' := d.wb * f' * d.wb⁻¹ with hf''
  have ha''W₃ : a'' ∈ yamadaW₃ d t := (mem_normalizer_iff.1 hwW₃ a').1 ha'
  have hf''w : f'' ∈ d.F.map (MulAut.conj d.wb).toMonoidHom := by
    rw [mem_map_conj_iff]
    simpa [hf'', mul_assoc] using hf'
  have hxe' : a * f₀ = a'' * f'' := by
    have : d.wb * (d.wb⁻¹ * (a * f₀) * d.wb) * d.wb⁻¹ = d.wb * (a' * f') * d.wb⁻¹ := by rw [hxe]
    rw [show d.wb * (d.wb⁻¹ * (a * f₀) * d.wb) * d.wb⁻¹ = a * f₀ by group] at this
    rw [this]
    simp only [ha'', hf'']
    group
  have hf''M : f'' ∈ d.M := (Subgroup.map_mono hFM |>.trans
    (map_conj_eq_of_mem_normalizer hwM).le) hf''w
  have hdiff : f'' * f₀⁻¹ ∈ yamadaW₃ d t := by
    have h1 : a''⁻¹ * a = f'' * f₀⁻¹ := by
      calc a''⁻¹ * a = a''⁻¹ * (a * f₀) * f₀⁻¹ := by group
        _ = a''⁻¹ * (a'' * f'') * f₀⁻¹ := by rw [hxe']
        _ = f'' * f₀⁻¹ := by group
    rw [← h1]
    exact mul_mem (inv_mem ha''W₃) ha
  have hdiffR : f'' * f₀⁻¹ ∈ yamadaR d t := by
    rw [h.yamadaR_eq d]
    exact mem_sup_left (hMS (mul_mem hf''M (inv_mem (hFM hf₀))))
  have hdiffW : f'' * f₀⁻¹ ∈ d.W := (h.yamadaW₃_inf_yamadaR hW d hK hQ).le
    (Subgroup.mem_inf.2 ⟨hdiff, hdiffR⟩)
  have hf''F : f'' ∈ d.F := by
    have h2 := mul_mem (hWF hdiffW) hf₀
    rwa [inv_mul_cancel_right] at h2
  have hf''W : f'' ∈ d.W := by
    rw [← hFw]
    exact Subgroup.mem_inf.2 ⟨hf''F, hf''w⟩
  rw [hxe']
  exact mul_mem ha''W₃ (hWW₃ hf''W)

end Q44

theorem yamada_5_43 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaM₆ d t : Set G) = (yamadaM₅ d t : Set G) *
        ((yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) ∧
      (yamadaS₆ d t : Set G) = (yamadaM₆ d t : Set G) * (d.S : Set G) := by
  refine ⟨coe_sup_eq_mul fun a ha =>
    L₆_le_normalizer_map_wb hW h d hK hQ (M₅_le_L₆ hW h d hK hQ ha), ?_⟩
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ (S_le_normalizer_M₆ hW h d hK hQ)

theorem yamada_5_44_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaM₆ d t ⊔ zpowers t = yamadaL₆ d t ∧ t ∈ normalizer (yamadaM₆ d t : Set G) ∧
      t ∉ yamadaM₆ d t) ∧
    (yamadaS₆ d t ⊔ zpowers t = yamadaR₆ d t ∧ t ∈ normalizer (yamadaS₆ d t : Set G) ∧
      t ∉ yamadaS₆ d t) := by
  have hM₆t := t_mem_normalizer_M₆ hW h d hK hQ
  have htM₆ := t_not_mem_M₆ hW h d hK hQ
  refine ⟨⟨L₆_eq_sup hW h d hK hQ, hM₆t, htM₆⟩, ?_⟩
  have htS : t ∈ normalizer (d.S : Set G) := Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs))
  have hM₆S₆ : yamadaM₆ d t ≤ yamadaS₆ d t := le_sup_left
  have hSS₆ : d.S ≤ yamadaS₆ d t := le_sup_right
  have hL₆R₆ : yamadaL₆ d t ≤ yamadaR₆ d t := le_sup_left
  have hSR₆ : d.S ≤ yamadaR₆ d t := le_sup_right
  refine ⟨le_antisymm (sup_le (sup_le (((M₆_le_L₆ hW h d hK hQ).trans hL₆R₆)) hSR₆)
    ((zpowers_le).2 (hL₆R₆ (t_mem_L₆ hW h d hK hQ)))) (sup_le ?_ (hSS₆.trans le_sup_left)),
    mem_normalizer_sup hM₆t htS, fun htS₆ => htM₆ ?_⟩
  · exact (L₆_eq_sup hW h d hK hQ).ge.trans (sup_le_sup_right hM₆S₆ _)
  · have hset := (yamada_5_43 hW h d hK hQ).2
    have ht' : t ∈ ((yamadaS₆ d t : Subgroup G) : Set G) := htS₆
    rw [hset] at ht'
    obtain ⟨m, hm, s, hs, hms⟩ := Set.mem_mul.1 ht'
    have hsL₆ : s ∈ yamadaL₆ d t := by
      have : s = m⁻¹ * t := by rw [← hms]; group
      rw [this]
      exact mul_mem (inv_mem (M₆_le_L₆ hW h d hK hQ hm)) (t_mem_L₆ hW h d hK hQ)
    have hsM : s ∈ d.M := by
      rw [← h.yamadaL₆_inf_S hW d hK hQ]
      exact Subgroup.mem_inf.2 ⟨hsL₆, hs⟩
    have hsM₆ : s ∈ yamadaM₆ d t := ((M_le_M₅ d t).trans le_sup_left) hsM
    have := mul_mem hm hsM₆
    rwa [hms] at this

theorem yamada_5_44_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t = yamadaF₅ d t ⊔ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom ∧
      (yamadaM₆ d t : Set G) = (yamadaF₅ d t : Set G) *
        ((yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom : Set G) ∧
      yamadaF₅ d t ⊓ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaW₃ d t := by
  obtain ⟨-, hFwM⟩ := F_inf_map_wb h d hK
  have hinf := F₅_inf_map_wb hW h d hK hQ
  obtain ⟨-, -, -, hF₅c, -, -, hM₆c, -, -⟩ := card_yamada_five_six hW h d hK hQ
  have hM₆ : yamadaM₆ d t =
      yamadaF₅ d t ⊔ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom := by
    refine le_antisymm ?_ (sup_le ((F₅_le_M₅ d t).trans le_sup_left)
      ((Subgroup.map_mono (F₅_le_M₅ d t)).trans le_sup_right))
    have hM₅Q : yamadaM₅ d t ≤
        yamadaF₅ d t ⊔ (yamadaF₅ d t).map (MulAut.conj d.wb).toMonoidHom := by
      rw [(yamadaS₅_eq_sup hW h d hK hQ).1.2.1]
      refine sup_le ?_ le_sup_left
      rw [← hFwM]
      exact sup_le_sup (F_le_F₅ d t) (Subgroup.map_mono (F_le_F₅ d t))
    refine sup_le hM₅Q ?_
    have := Subgroup.map_mono (f := (MulAut.conj d.wb).toMonoidHom) hM₅Q
    rwa [Subgroup.map_sup, map_wb_map_wb h d hK, sup_comm] at this
  refine ⟨hM₆, coe_eq_mul_of_card (hM₆ ▸ le_sup_left) (hM₆ ▸ le_sup_right) ?_, hinf⟩
  rw [card_map_conj, hinf, (h.yamada_5_33_3_uniform hW d hK hQ.doubling).2.1, hF₅c, hM₆c]
  ring

namespace Q44

theorem M₆_inf_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ⊓ yamadaR₅ d t = yamadaM₅ d t := by
  have htt := h.t_mul_t
  obtain ⟨-, -, ⟨hL₅M, hM₅N, htM₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  refine le_antisymm (fun x hx => ?_) (le_inf ((le_sup_left : yamadaM₅ d t ≤ yamadaM₆ d t))
    ((M₅_le_L₅ hW h d hK hQ).trans (L₅_le_R₅ hW h d hK hQ)))
  obtain ⟨hxM₆, hxR₅⟩ := Subgroup.mem_inf.1 hx
  have hxL₅ : x ∈ yamadaL₅ d t := (h.yamada_5_40_4 hW d hK hQ).ge
    (Subgroup.mem_inf.2 ⟨M₆_le_L₆ hW h d hK hQ hxM₆, hxR₅⟩)
  rw [← hL₅M] at hxL₅
  rcases (mem_sup_zpowers_iff_of htt hM₅N).1 hxL₅ with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    refine t_not_mem_M₆ hW h d hK hQ ?_
    have := mul_mem (inv_mem ((le_sup_left : yamadaM₅ d t ≤ yamadaM₆ d t) ha)) hxM₆
    rwa [inv_mul_cancel_left] at this

theorem commutator_L₆_S (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaL₆ d t, ∀ s ∈ d.S, x * s * x⁻¹ * s⁻¹ ∈ yamadaM₅ d t := by
  intro x hx s hs
  have hR₅N := (h.yamada_5_40_1 hW d hK hQ).2
  have hsR₅ : s ∈ yamadaR₅ d t := S_le_R₅ hW h d hK hQ hs
  have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
  have key : ∀ m ∈ yamadaM₆ d t, m * s * m⁻¹ * s⁻¹ ∈ yamadaM₅ d t := by
    intro m hm
    rw [← M₆_inf_R₅ hW h d hK hQ]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [show m * s * m⁻¹ * s⁻¹ = m * (s * m⁻¹ * s⁻¹) by group]
      exact mul_mem hm ((mem_normalizer_iff.1 (S_le_normalizer_M₆ hW h d hK hQ hs) m⁻¹).1
        (inv_mem hm))
    · have hmR₆ : m ∈ yamadaR₆ d t :=
        (le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) (M₆_le_L₆ hW h d hK hQ hm)
      have h1 : m * s * m⁻¹ ∈ yamadaR₅ d t := (mem_normalizer_iff.1 (hR₅N hmR₆) s).1 hsR₅
      exact mul_mem h1 (inv_mem hsR₅)
  rcases (mem_sup_zpowers_iff_of h.t_mul_t (t_mem_normalizer_M₆ hW h d hK hQ)).1
    ((L₆_eq_sup hW h d hK hQ).ge hx) with h1 | ⟨a, ha, rfl⟩
  · exact key x h1
  · have e : a * t * s * (a * t)⁻¹ * s⁻¹ = a * s * a⁻¹ * s⁻¹ := by
      calc a * t * s * (a * t)⁻¹ * s⁻¹ = a * (t * s * t⁻¹) * a⁻¹ * s⁻¹ := by group
        _ = a * s * a⁻¹ * s⁻¹ := by rw [← hst]; group
    rw [e]
    exact key a ha

theorem commutator_mem_M₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∀ x ∈ yamadaR₆ d t, ∀ y ∈ yamadaR₆ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaM₅ d t := by
  have hN : yamadaR₆ d t ≤ normalizer (yamadaM₅ d t : Set G) := (yamadaM₅_eq_inf hW h d hK hQ).2
  have hconj : ∀ a ∈ yamadaR₆ d t, ∀ m ∈ yamadaM₅ d t, a * m * a⁻¹ ∈ yamadaM₅ d t :=
    fun a ha m hm => (mem_normalizer_iff.1 (hN ha) m).1 hm
  have hLL : ∀ x ∈ yamadaL₆ d t, ∀ y ∈ yamadaL₆ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaM₅ d t :=
    fun x hx y hy => M₂_le_M₅ d t (commutator_mem_M₂ hW h d hK hQ x hx y hy)
  have hLS := commutator_L₆_S hW h d hK hQ
  have hSS : ∀ s ∈ d.S, ∀ s' ∈ d.S, s * s' * s⁻¹ * s'⁻¹ ∈ yamadaM₅ d t := by
    intro s hs s' hs'
    have := Subgroup.commutator_mem_commutator hs hs'
    rw [(d.yamada_3_12_commutators (hK ▸ h.four_le)).2.2.1] at this
    exact (F₅_le_M₅ d t) (F_le_F₅ d t this)
  intro x hx y hy
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₆ d) x hx
  obtain ⟨l', hl', s', hs', rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₆ d) y hy
  have hl'R₆ : l' ∈ yamadaR₆ d t := (le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) hl'
  have hlR₆ : l ∈ yamadaR₆ d t := (le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) hl
  have e1 : l * s * (l' * s') * (l * s)⁻¹ * (l' * s')⁻¹ =
      l * ((s * l' * s⁻¹ * l'⁻¹) * (l' * (s * s' * s⁻¹ * s'⁻¹) * l'⁻¹)) * l⁻¹ *
        ((l * l' * l⁻¹ * l'⁻¹) * (l' * (l * s' * l⁻¹ * s'⁻¹) * l'⁻¹)) := by group
  rw [e1]
  have h1 : s * l' * s⁻¹ * l'⁻¹ ∈ yamadaM₅ d t := by
    have := inv_mem (hLS l' hl' s hs)
    rwa [show (l' * s * l'⁻¹ * s⁻¹)⁻¹ = s * l' * s⁻¹ * l'⁻¹ by group] at this
  refine mul_mem (hconj l hlR₆ _ (mul_mem h1 (hconj l' hl'R₆ _ (hSS s hs s' hs')))) ?_
  exact mul_mem (hLL l hl l' hl') (hconj l' hl'R₆ _ (hLS l hl s' hs'))

theorem R₆_le_normalizer_of_le {B : Subgroup G} (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hMB : yamadaM₅ d t ≤ B) (hBR : B ≤ yamadaR₆ d t) :
    yamadaR₆ d t ≤ normalizer (B : Set G) :=
  le_normalizer_of_forall_commutator_mem (commutator_mem_M₅ hW h d hK hQ) hMB le_rfl hBR

theorem S₅_le_R₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaS₅ d t ≤ yamadaR₆ d t :=
  (S₅_le_R₅ hW h d hK hQ).trans (h.yamadaR₅_le_yamadaR₆ hW d hK hQ)

theorem S₆_le_R₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaS₆ d t ≤ yamadaR₆ d t :=
  sup_le ((M₆_le_L₆ hW h d hK hQ).trans le_sup_left) le_sup_right

theorem S₅_le_S₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaS₅ d t ≤ yamadaS₆ d t := by
  rw [(yamadaS₅_eq_sup hW h d hK hQ).1.1]
  exact sup_le (S_le_yamadaS₆ d t) ((F₅_le_M₅ d t).trans
    ((yamadaM₅_le_yamadaM₆ d t).trans (yamadaM₆_le_yamadaS₆ d t)))

theorem S₆_inf_R₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ⊓ yamadaR₅ d t = yamadaS₅ d t := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (S₅_le_S₆ hW h d hK hQ) (S₅_le_R₅ hW h d hK hQ))
  obtain ⟨hxS₆, hxR₅⟩ := Subgroup.mem_inf.1 hx
  have hset := (yamada_5_43 hW h d hK hQ).2
  have hx' : x ∈ ((yamadaS₆ d t : Subgroup G) : Set G) := hxS₆
  rw [hset] at hx'
  obtain ⟨m, hm, s, hs, rfl⟩ := Set.mem_mul.1 hx'
  have hmR₅ : m ∈ yamadaR₅ d t := by
    have := mul_mem hxR₅ (inv_mem (S_le_R₅ hW h d hK hQ hs))
    rwa [mul_inv_cancel_right] at this
  have hmM₅ := (M₆_inf_R₅ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hm, hmR₅⟩)
  exact mul_mem (M₅_le_S₅ d t hmM₅) (S_le_S₅ d t hs)

theorem S₅_inf_R₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₅ d t ⊓ yamadaR₂ d t = yamadaS₂ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hsetS, -, -, -⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, -, -, ⟨hR₃eq, -⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, -, -, -, ⟨hR₄eq, -⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨-, hR₃R₄, -, -⟩ := (h.yamada_5_27_2 hW d hK hD).1
  obtain ⟨-, hS₂R₂, -⟩ := h.yamada_5_13_3 d hK hD
  have hS₃R₃ : yamadaS₃ d t ≤ yamadaR₃ d t := le_sup_left.trans hR₃eq.le
  have hS₄R₄ : yamadaS₄ d t ≤ yamadaR₄ d t := le_sup_left.trans hR₄eq.le
  have hR₂R₃ : yamadaR₂ d t ≤ yamadaR₃ d t := hR₃R₄.ge.trans inf_le_left
  refine le_antisymm (fun x hx => ?_) (le_inf ((le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t).trans
    le_sup_left) hS₂R₂)
  obtain ⟨hxS₅, hxR₂⟩ := Subgroup.mem_inf.1 hx
  have hx' : x ∈ ((yamadaS₅ d t : Subgroup G) : Set G) := hxS₅
  rw [hsetS] at hx'
  obtain ⟨s₃, hs₃, s₄, hs₄, rfl⟩ := Set.mem_mul.1 hx'
  have hs₄R₃ : s₄ ∈ yamadaR₃ d t := by
    have := mul_mem (inv_mem (hS₃R₃ hs₃)) (hR₂R₃ hxR₂)
    rwa [inv_mul_cancel_left] at this
  have hs₄R₂ : s₄ ∈ yamadaR₂ d t := by
    rw [← hR₃R₄]
    exact Subgroup.mem_inf.2 ⟨hs₄R₃, hS₄R₄ hs₄⟩
  have hs₄S₂ : s₄ ∈ yamadaS₂ d t := by
    rw [← h.yamadaS₄_inf_yamadaR₂ hW d hK hD]
    exact Subgroup.mem_inf.2 ⟨hs₄, hs₄R₂⟩
  have hs₃R₂ : s₃ ∈ yamadaR₂ d t := by
    have := mul_mem hxR₂ (inv_mem (hS₂R₂ hs₄S₂))
    rwa [mul_inv_cancel_right] at this
  have hs₃S₂ : s₃ ∈ yamadaS₂ d t := by
    rw [← h.yamadaS₃_inf_yamadaR₂ hW d hK hD]
    exact Subgroup.mem_inf.2 ⟨hs₃, hs₃R₂⟩
  exact mul_mem hs₃S₂ hs₄S₂

theorem upperCentralSeries_of_forall {S' U Y : Subgroup G} (hUS : U ≤ S') (hYS : Y ≤ S')
    (hZ : S' ⊓ centralizer (S' : Set G) = U)
    (hiff : ∀ x ∈ S', (x ∈ Y ↔ ∀ g ∈ S', x * g * x⁻¹ * g⁻¹ ∈ U)) :
    (Subgroup.upperCentralSeries S' 1).map S'.subtype = U ∧
      (Subgroup.upperCentralSeries S' 2).map S'.subtype = Y := by
  have hmem1 : ∀ x : S', x ∈ Subgroup.upperCentralSeries S' 1 ↔ (x : G) ∈ U := by
    intro x
    rw [Subgroup.upperCentralSeries_one, ← hZ]
    constructor
    · intro hx
      exact ⟨x.2, mem_centralizer_iff.2 fun y hy =>
        congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)⟩
    · rintro ⟨-, hc⟩
      exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hc y y.2)
  have hmem2 : ∀ x : S', x ∈ Subgroup.upperCentralSeries S' 2 ↔ (x : G) ∈ Y := by
    intro x
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff, hiff x x.2]
    constructor
    · intro hx g hg
      have := (hmem1 _).1 (hx ⟨g, hg⟩)
      simpa [commutatorElement_def] using this
    · intro hx y
      rw [hmem1]
      simpa [commutatorElement_def] using hx y y.2
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem1 y).1 hy
    · intro hx
      exact ⟨⟨x, hUS hx⟩, (hmem1 _).2 hx, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem2 y).1 hy
    · intro hx
      exact ⟨⟨x, hYS hx⟩, (hmem2 _).2 hx, rfl⟩

theorem commutator_mem_of_mem_Z₂ {S' U Y : Subgroup G}
    (hU : (Subgroup.upperCentralSeries S' 1).map S'.subtype = U)
    (hY : (Subgroup.upperCentralSeries S' 2).map S'.subtype = Y) {x : G} (hx : x ∈ Y) {g : G}
    (hg : g ∈ S') : x * g * x⁻¹ * g⁻¹ ∈ U := by
  rw [← hY] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 := Subgroup.mem_upperCentralSeries_succ_iff.1
    (show y ∈ Subgroup.upperCentralSeries S' (1 + 1) from hy) ⟨g, hg⟩
  rw [← hU]
  exact ⟨_, h1, rfl⟩

theorem S₁_le_S₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaS₁ d t ≤ yamadaS₂ d t := by
  rw [h.yamadaS₁_eq_sup d hK hD]
  exact sup_le_sup_left (yamadaU₁_le_yamadaY₂ d t) _

theorem U₁_le_S₂ (d : G2Data L K) (t : G) : yamadaU₁ d t ≤ yamadaS₂ d t :=
  (yamadaU₁_le_yamadaY₂ d t).trans le_sup_right

theorem S₂_le_S₅ (d : G2Data L K) (t : G) : yamadaS₂ d t ≤ yamadaS₅ d t :=
  (le_sup_right : yamadaS₂ d t ≤ yamadaS₃ d t).trans le_sup_left

theorem S₅_le_centralizer_U₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₅ d t ≤ centralizer (yamadaU₁ d t : Set G) :=
  sup_le (h.yamadaS₃_le_centralizer_yamadaU₁_uniform hW d hK hQ.doubling)
    (h.yamadaS₄_le_centralizer_yamadaU₁_uniform hW d hK hQ.doubling)

theorem S₅_center (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₅ d t ⊓ centralizer (yamadaS₅ d t : Set G) = yamadaU₁ d t := by
  have hD := hQ.doubling
  refine le_antisymm (fun z hz => ?_) (le_inf ((U₁_le_S₂ d t).trans (S₂_le_S₅ d t))
    ((Subgroup.le_centralizer_iff).1 (S₅_le_centralizer_U₁ hW h d hK hQ)))
  obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.1 hz
  have hS₁S₅ := (S₁_le_S₂ h d hK hD).trans (S₂_le_S₅ d t)
  have hzR₂ : z ∈ yamadaR₂ d t := by
    rw [← (h.yamada_5_28 hW d hK hD).2.1]
    exact Subgroup.mem_inf.2 ⟨S₅_le_R₅ hW h d hK hQ hzS,
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hS₁S₅ hzC)⟩
  have hzS₂ : z ∈ yamadaS₂ d t := (S₅_inf_R₂ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hzS, hzR₂⟩)
  rw [← (h.yamada_5_13_5 d hK hD).1]
  exact Subgroup.mem_inf.2 ⟨hzS₂, Subgroup.centralizer_le (S₂_le_S₅ d t) hzC⟩

theorem S₅_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G} (hx : x ∈ yamadaS₅ d t) :
    x ∈ yamadaY₂ d t ↔ ∀ g ∈ yamadaS₅ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hsetS, -, -, -⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, hU₃, hY₃⟩ := h.yamada_5_33_1_S₃_uniform hW d hK hQ.doubling
  obtain ⟨-, hU₄, hY₄⟩ := h.yamada_5_33_1_S₄_uniform hW d hK hQ.doubling
  have hU₁C := (Subgroup.le_centralizer_iff).1 (S₅_le_centralizer_U₁ hW h d hK hQ)
  constructor
  · intro hxY g hg
    have hg' : g ∈ ((yamadaS₅ d t : Subgroup G) : Set G) := hg
    rw [hsetS] at hg'
    obtain ⟨s₃, hs₃, s₄, hs₄, rfl⟩ := Set.mem_mul.1 hg'
    have h1 := commutator_mem_of_mem_Z₂ hU₃ hY₃ hxY hs₃
    have h2 := commutator_mem_of_mem_Z₂ hU₄ hY₄ hxY hs₄
    have hs₃' : s₃ ∈ yamadaS₅ d t := (le_sup_left : yamadaS₃ d t ≤ yamadaS₅ d t) hs₃
    have e : x * (s₃ * s₄) * x⁻¹ * (s₃ * s₄)⁻¹ =
        (x * s₃ * x⁻¹ * s₃⁻¹) * (s₃ * (x * s₄ * x⁻¹ * s₄⁻¹) * s₃⁻¹) := by group
    have hc3 : s₃ * (x * s₄ * x⁻¹ * s₄⁻¹) * s₃⁻¹ = x * s₄ * x⁻¹ * s₄⁻¹ := by
      rw [mem_centralizer_iff.1 (hU₁C h2) s₃ hs₃']
      group
    rw [e, hc3]
    exact mul_mem h1 h2
  · intro hc
    have hS₁S₅ := (S₁_le_S₂ h d hK hD).trans (S₂_le_S₅ d t)
    have hxN : x ∈ normalizer (yamadaS₁ d t : Set G) := mem_normalizer_of_conj_mem fun y hy => by
      rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
      refine mul_mem ?_ hy
      have hU₁S₁ : yamadaU₁ d t ≤ yamadaS₁ d t := by
        rw [h.yamadaS₁_eq_sup d hK hD]
        exact le_sup_right
      exact hU₁S₁ (hc y (hS₁S₅ hy))
    have hxR₂ : x ∈ yamadaR₂ d t := by
      rw [← (h.yamada_5_28 hW d hK hD).2.1]
      exact Subgroup.mem_inf.2 ⟨S₅_le_R₅ hW h d hK hQ hx, hxN⟩
    have hxS₂ : x ∈ yamadaS₂ d t := (S₅_inf_R₂ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hx, hxR₂⟩)
    exact (h.mem_yamadaY₂_iff d hK hD hxS₂).2 fun g hg => hc g (S₂_le_S₅ d t hg)

theorem le_centralizer_U₁_of_centralizer_J₁_le_centralizer (h : Setup G L f t) (d : G2Data L K)
    (hD : h.DoublingFacts d) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hJP : d.J₁ ≤ normalizer (P : Set G)) (hPU₁ : P ≤ normalizer (yamadaU₁ d t : Set G))
    (hC : P ⊓ centralizer (d.J₁ : Set G) ≤ centralizer (yamadaU₁ d t : Set G)) :
    P ≤ centralizer (yamadaU₁ d t : Set G) := by
  have hJ₁J : d.J₁ ≤ d.J := d.image_mono inf_le_left
  have hcomm : ⁅P, d.J₁⁆ ≤ centralizer (yamadaU₁ d t : Set G) :=
    (Subgroup.commutator_le).2 fun s hs j hj => mem_centralizer_iff.2 fun u hu => by
      have hu' : s⁻¹ * u * s ∈ yamadaU₁ d t := by
        have := (mem_normalizer_iff.1 (inv_mem (hPU₁ hs)) u).1 hu
        rwa [inv_inv] at this
      have hju : j * u = u * j := mem_centralizer_iff.1 (hD.le_centralizer_J₁ hu) j hj
      have hju' : j * (s⁻¹ * u * s) = (s⁻¹ * u * s) * j :=
        mem_centralizer_iff.1 (hD.le_centralizer_J₁ hu') j hj
      have e1 : j⁻¹ * u = u * j⁻¹ := by
        calc j⁻¹ * u = j⁻¹ * (u * j) * j⁻¹ := by group
          _ = j⁻¹ * (j * u) * j⁻¹ := by rw [hju]
          _ = u * j⁻¹ := by group
      rw [commutatorElement_def]
      calc u * (s * j * s⁻¹ * j⁻¹) = s * ((s⁻¹ * u * s) * j) * s⁻¹ * j⁻¹ := by group
        _ = s * (j * (s⁻¹ * u * s)) * s⁻¹ * j⁻¹ := by rw [hju']
        _ = s * j * s⁻¹ * (u * j⁻¹) := by group
        _ = s * j * s⁻¹ * (j⁻¹ * u) := by rw [e1]
        _ = s * j * s⁻¹ * j⁻¹ * u := by group
  have hJ₁odd : Odd (Nat.card d.J₁) := (odd_card_J d).of_dvd_nat (Subgroup.card_dvd_of_le hJ₁J)
  have hcop : Nat.Coprime (Nat.card d.J₁) (Nat.card P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hJ₁odd)
  have hNP : ⁅P, d.J₁⁆ ≤ P := (Subgroup.commutator_le).2 fun s hs j hj => by
    rw [commutatorElement_def, show s * j * s⁻¹ * j⁻¹ = s * (j * s⁻¹ * j⁻¹) by group]
    exact mul_mem hs ((mem_normalizer_iff.1 (hJP hj) _).1 (inv_mem hs))
  refine (Subgroup.le_centralizer_iff).1 fun u hu => mem_centralizer_iff.2 fun s hs => ?_
  have : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := P) (N := ⁅P, d.J₁⁆) (S := d.J₁) hNP
    (le_normalizer_commutator_left _ _) hJP
    (fun j hj => mem_normalizer_commutator (hJP hj) (Subgroup.le_normalizer hj)) inferInstance
    hcop hs fun j hj => by
      rw [show s⁻¹ * (j * s * j⁻¹) = ⁅s⁻¹, j⁆ by simp only [commutatorElement_def]; group]
      exact Subgroup.commutator_mem_commutator (inv_mem hs) hj
  have e1 : c * u = u * c := (mem_centralizer_iff.1 (hC hc) u hu).symm
  have e2 : n * u = u * n := (mem_centralizer_iff.1 (hcomm hn) u hu).symm
  calc c * n * u = c * (n * u) := by group
    _ = c * (u * n) := by rw [e2]
    _ = c * u * n := by group
    _ = u * c * n := by rw [e1]
    _ = u * (c * n) := by group

theorem le_centralizer_U₁_of_centralizer_J₁_le (h : Setup G L f t) (d : G2Data L K)
    (hD : h.DoublingFacts d) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hJP : d.J₁ ≤ normalizer (P : Set G)) (hPU₁ : P ≤ normalizer (yamadaU₁ d t : Set G))
    (hC : P ⊓ centralizer (d.J₁ : Set G) ≤ yamadaU₁ d t) :
    P ≤ centralizer (yamadaU₁ d t : Set G) :=
  le_centralizer_U₁_of_centralizer_J₁_le_centralizer h d hD hP hJP hPU₁ fun x hx =>
    mem_centralizer_iff.2 fun u hu => hD.mul_comm hu (hC hx)

theorem S₂_le_S₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaS₂ d t ≤ yamadaS₆ d t :=
  (S₂_le_S₅ d t).trans (S₅_le_S₆ hW h d hK hQ)

theorem U₁_le_S₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) : yamadaU₁ d t ≤ yamadaS₆ d t :=
  (U₁_le_S₂ d t).trans (S₂_le_S₆ hW h d hK hQ)

theorem Y₂_le_S₂ (d : G2Data L K) (t : G) : yamadaY₂ d t ≤ yamadaS₂ d t := le_sup_right

theorem S₆_le_normalizer_S₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ≤ normalizer (yamadaS₅ d t : Set G) :=
  (S₆_le_R₆ hW h d hK hQ).trans (R₆_le_normalizer_of_le hW h d hK hQ (M₅_le_S₅ d t)
    (S₅_le_R₆ hW h d hK hQ))

theorem S₆_le_normalizer_U₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ≤ normalizer (yamadaU₁ d t : Set G) := fun x hx => by
  rw [← S₅_center hW h d hK hQ]
  have := S₆_le_normalizer_S₅ hW h d hK hQ hx
  exact Common.mem_normalizer_inf this (mem_normalizer_centralizer this)

theorem R₆_inf_centralizer_J₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    yamadaR₆ d t ⊓ centralizer (d.J₁ : Set G) = yamadaU₁ d t ⊔ zpowers t := by
  have hQ := h.qFacts_of_eight d hK h8
  have hD := hQ.doubling
  refine h.eq_yamadaU₁_sup_of_isPGroup d hK h8 ((h.isPGroup_yamadaR₆ d).to_le inf_le_left)
    inf_le_right (le_inf (sup_le ?_ ?_) (sup_le hD.le_centralizer_J₁ ?_))
  · exact ((U₁_le_S₂ d t).trans (S₂_le_S₅ d t)).trans (S₅_le_R₆ hW h d hK hQ)
  · exact (zpowers_le).2 ((le_sup_left : yamadaL₆ d t ≤ yamadaR₆ d t) (t_mem_L₆ hW h d hK hQ))
  · exact (zpowers_le).2 (mem_centralizer_iff.2 fun j hj =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hj)))

theorem S₆_le_centralizer_U₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ≤ centralizer (yamadaU₁ d t : Set G) := by
  rcases hQ.branch with h8 | ⟨hK4, -⟩
  swap
  ·
    have hD := hQ.doubling
    have hJ₁₄ : d.J₄ = d.J₁ := (d.yamada_3_9_4_four_G hK4).1.symm
    refine le_centralizer_U₁_of_centralizer_J₁_le_centralizer h d hD
      ((h.isPGroup_yamadaR₆ d).to_le (S₆_le_R₆ hW h d hK hQ)) (fun j hj => ?_)
      (S₆_le_normalizer_U₁ hW h d hK hQ) (fun x hx => ?_)
    · have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
      exact mem_normalizer_sup (J_le_normalizer_M₆ hW h d hK hQ hjJ)
        (h.J_le_centralizer_inf_normalizer_S d hjJ).2
    · obtain ⟨hxS₆, hxC⟩ := Subgroup.mem_inf.1 hx
      have hxR₅ : x ∈ yamadaR₅ d t := mem_R₅_of_forall_J₄ hW h d hK hQ
        (S₆_le_R₆ hW h d hK hQ hxS₆) fun j hj => by
          have hj₁ : j ∈ d.J₁ := hJ₁₄ ▸ (show j ∈ d.J₄ from hj)
          rw [mem_centralizer_iff.1 hxC j hj₁, mul_inv_cancel_right, inv_mul_cancel]
          exact one_mem _
      exact S₅_le_centralizer_U₁ hW h d hK hQ
        ((S₆_inf_R₅ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hxS₆, hxR₅⟩))
  have hD := hQ.doubling
  have hCR := R₆_inf_centralizer_J₁ hW h d hK h8
  refine le_centralizer_U₁_of_centralizer_J₁_le h d hD
    ((h.isPGroup_yamadaR₆ d).to_le (S₆_le_R₆ hW h d hK hQ)) (fun j hj => ?_)
    (S₆_le_normalizer_U₁ hW h d hK hQ) (fun x hx => ?_)
  · have hjJ : j ∈ d.J := d.image_mono inf_le_left hj
    exact mem_normalizer_sup (J_le_normalizer_M₆ hW h d hK hQ hjJ)
      (h.J_le_centralizer_inf_normalizer_S d hjJ).2
  · obtain ⟨hxS₆, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxT : x ∈ yamadaU₁ d t ⊔ zpowers t := by
      rw [← hCR]
      exact Subgroup.mem_inf.2 ⟨S₆_le_R₆ hW h d hK hQ hxS₆, hxC⟩
    have htU₁ : t ∈ normalizer (yamadaU₁ d t : Set G) := (h.t_mem_normalizer_yamadaU₁ d hK hD).1
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htU₁).1 hxT with h1 | ⟨u, hu, rfl⟩
    · exact h1
    · exfalso
      refine (yamada_5_44_1 hW h d hK hQ).2.2.2 ?_
      have := mul_mem (inv_mem (U₁_le_S₆ hW h d hK hQ hu)) hxS₆
      rwa [inv_mul_cancel_left] at this

theorem S₆_center (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaS₆ d t ⊓ centralizer (yamadaS₆ d t : Set G) = yamadaU₁ d t := by
  refine le_antisymm (fun z hz => ?_) (le_inf (U₁_le_S₆ hW h d hK hQ)
    ((Subgroup.le_centralizer_iff).1 (S₆_le_centralizer_U₁ hW h d hK hQ)))
  obtain ⟨hzS, hzC⟩ := Subgroup.mem_inf.1 hz
  have hzR₅ : z ∈ yamadaR₅ d t := by
    rw [← (h.yamada_5_42 hW d hK hQ).2.1]
    exact Subgroup.mem_inf.2 ⟨S₆_le_R₆ hW h d hK hQ hzS, Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (S₂_le_S₆ hW h d hK hQ) hzC)⟩
  have hzS₅ : z ∈ yamadaS₅ d t := (S₆_inf_R₅ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hzS, hzR₅⟩)
  rw [← S₅_center hW h d hK hQ]
  exact Subgroup.mem_inf.2 ⟨hzS₅, Subgroup.centralizer_le (S₅_le_S₆ hW h d hK hQ) hzC⟩

theorem map_wb_M₆ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    (yamadaM₆ d t).map (MulAut.conj d.wb).toMonoidHom = yamadaM₆ d t := by
  show (yamadaM₅ d t ⊔ (yamadaM₅ d t).map (MulAut.conj d.wb).toMonoidHom).map
    (MulAut.conj d.wb).toMonoidHom = _
  rw [Subgroup.map_sup, map_wb_map_wb h d hK, sup_comm]
  rfl

theorem M₆_le_centralizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G) := by
  have hwb : d.wb ∈ normalizer (yamadaM₆ d t : Set G) :=
    mem_normalizer_of_map_conj_eq (map_wb_M₆ h d hK)
  have hU₁M₆ : yamadaU₁ d t ≤ centralizer (yamadaM₆ d t : Set G) :=
    (Subgroup.le_centralizer_iff).1 ((yamadaM₆_le_yamadaS₆ d t).trans
      (S₆_le_centralizer_U₁ hW h d hK hQ))
  rw [← Subgroup.le_centralizer_iff]
  refine sup_le hU₁M₆ fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine mem_centralizer_iff.2 fun m hm => ?_
  have hm' : d.wb⁻¹ * m * d.wb ∈ yamadaM₆ d t := inv_conj_mem hwb hm
  have e := mem_centralizer_iff.1 (hU₁M₆ hu) _ hm'
  calc m * (d.wb * u * d.wb⁻¹) = d.wb * ((d.wb⁻¹ * m * d.wb) * u) * d.wb⁻¹ := by group
    _ = d.wb * (u * (d.wb⁻¹ * m * d.wb)) * d.wb⁻¹ := by rw [e]
    _ = d.wb * u * d.wb⁻¹ * m := by group

theorem S₆_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G} (hx : x ∈ yamadaS₆ d t) :
    x ∈ yamadaY₂ d t ↔ ∀ g ∈ yamadaS₆ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaU₁ d t := by
  have hD := hQ.doubling
  have hU₁C := (Subgroup.le_centralizer_iff).1 (S₆_le_centralizer_U₁ hW h d hK hQ)
  constructor
  · intro hxY g hg
    have hset := (yamada_5_43 hW h d hK hQ).2
    have hg' : g ∈ ((yamadaS₆ d t : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨m, hm, s, hs, rfl⟩ := Set.mem_mul.1 hg'
    have hmS₆ : m ∈ yamadaS₆ d t := yamadaM₆_le_yamadaS₆ d t hm
    have hxm : x * m = m * x := mem_centralizer_iff.1 (M₆_le_centralizer_Y₂ hW h d hK hQ hm) x hxY
    have hxsU : x * s * x⁻¹ * s⁻¹ ∈ yamadaU₁ d t :=
      (h.mem_yamadaY₂_iff d hK hD (Y₂_le_S₂ d t hxY)).1 hxY s
        ((le_sup_left : d.S ≤ yamadaS₂ d t) hs)
    have e : x * (m * s) * x⁻¹ * (m * s)⁻¹ =
        (x * m * x⁻¹ * m⁻¹) * (m * (x * s * x⁻¹ * s⁻¹) * m⁻¹) := by group
    have hc : m * (x * s * x⁻¹ * s⁻¹) * m⁻¹ = x * s * x⁻¹ * s⁻¹ := by
      rw [mem_centralizer_iff.1 (hU₁C hxsU) m hmS₆]
      group
    rw [e, hc, hxm, show m * x * x⁻¹ * m⁻¹ = 1 by group, one_mul]
    exact hxsU
  · intro hc
    have hxN : x ∈ normalizer (yamadaS₂ d t : Set G) := mem_normalizer_of_conj_mem fun y hy => by
      rw [show x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y by group]
      exact mul_mem (U₁_le_S₂ d t (hc y (S₂_le_S₆ hW h d hK hQ hy))) hy
    have hxR₅ : x ∈ yamadaR₅ d t := by
      rw [← (h.yamada_5_42 hW d hK hQ).2.1]
      exact Subgroup.mem_inf.2 ⟨S₆_le_R₆ hW h d hK hQ hx, hxN⟩
    have hxS₅ : x ∈ yamadaS₅ d t := (S₆_inf_R₅ hW h d hK hQ).le (Subgroup.mem_inf.2 ⟨hx, hxR₅⟩)
    exact (S₅_iff hW h d hK hQ hxS₅).2 fun g hg => hc g (S₅_le_S₆ hW h d hK hQ hg)

theorem X₄_le_centralizer_Y₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaX₄ d t ≤ centralizer (yamadaY₂ d t : Set G) :=
  ((le_sup_left : yamadaX₄ d t ≤ yamadaM₄ d t).trans ((le_sup_right :
    yamadaM₄ d t ≤ yamadaM₅ d t).trans (yamadaM₅_le_yamadaM₆ d t))).trans
    (M₆_le_centralizer_Y₂ hW h d hK hQ)

end Q44

theorem yamadaX₄_eq_inf_centralizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaX₄ d t = yamadaR₄ d t ⊓ centralizer (yamadaX₂ d t : Set G) :=
  (h.yamadaX₄_core hW d hK hQ.doubling
    (X₄_le_centralizer_Y₂ hW h d hK hQ)).2.2.1.symm

theorem yamada_5_45_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ((Subgroup.upperCentralSeries (yamadaS₅ d t) 1).map (yamadaS₅ d t).subtype = yamadaU₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₆ d t) 1).map (yamadaS₆ d t).subtype =
        yamadaU₁ d t) ∧
    ((Subgroup.upperCentralSeries (yamadaS₅ d t) 2).map (yamadaS₅ d t).subtype = yamadaY₂ d t ∧
      (Subgroup.upperCentralSeries (yamadaS₆ d t) 2).map (yamadaS₆ d t).subtype =
        yamadaY₂ d t) := by
  obtain ⟨h1, h2⟩ := upperCentralSeries_of_forall ((U₁_le_S₂ d t).trans (S₂_le_S₅ d t))
    ((Y₂_le_S₂ d t).trans (S₂_le_S₅ d t)) (S₅_center hW h d hK hQ)
    fun x hx => S₅_iff hW h d hK hQ hx
  obtain ⟨h3, h4⟩ := upperCentralSeries_of_forall (U₁_le_S₆ hW h d hK hQ)
    ((Y₂_le_S₂ d t).trans (S₂_le_S₆ hW h d hK hQ)) (S₆_center hW h d hK hQ)
    fun x hx => S₆_iff hW h d hK hQ hx
  exact ⟨⟨h1, h3⟩, h2, h4⟩

theorem yamada_5_45_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ (Subgroup.upperCentralSeries (yamadaM₆ d t) 1).map (yamadaM₆ d t).subtype := by
  have hC := M₆_le_centralizer_Y₂ hW h d hK hQ
  intro y hy
  have hyM₆ : y ∈ yamadaM₆ d t :=
    ((Y₂_le_F₅ d t).trans ((F₅_le_M₅ d t).trans (yamadaM₅_le_yamadaM₆ d t))) hy
  refine ⟨⟨y, hyM₆⟩, ?_, rfl⟩
  rw [Subgroup.upperCentralSeries_one]
  refine mem_center_iff.2 fun z => Subtype.ext ?_
  exact (mem_centralizer_iff.1 (hC z.2) y hy).symm

theorem yamada_5_45_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    CFSG.IsElementaryAbelian 2 (yamadaX₄ d t) ∧ Nat.card (yamadaX₄ d t) = Nat.card K ^ 6 ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
        normalizer (yamadaX₄ d t : Set G) := by
  obtain ⟨h1, h2, -, h4⟩ := h.yamadaX₄_core hW d hK hQ.doubling
    (X₄_le_centralizer_Y₂ hW h d hK hQ)
  exact ⟨h1, h2, h4⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
