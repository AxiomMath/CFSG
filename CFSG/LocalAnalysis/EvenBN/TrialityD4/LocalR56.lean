module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6Two
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR5Cover
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalS4Centre

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Generic

variable {X : Type*} [Group X]

@[expose] noncomputable def modCentralizerSub (A F : Subgroup X) : Subgroup X where
  carrier := {x | x ∈ normalizer (F : Set X) ∧ ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ F}
  mul_mem' := by
    rintro x y ⟨hx, hxA⟩ ⟨hy, hyA⟩
    show x * y ∈ normalizer (F : Set X) ∧ ∀ a ∈ A, x * y * a * (x * y)⁻¹ * a⁻¹ ∈ F
    refine ⟨mul_mem hx hy, fun a ha => ?_⟩
    have e : x * y * a * (x * y)⁻¹ * a⁻¹ =
        (x * (y * a * y⁻¹ * a⁻¹) * x⁻¹) * (x * a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 hx _).1 (hyA a ha)) (hxA a ha)
  one_mem' := by
    show (1 : X) ∈ normalizer (F : Set X) ∧ ∀ a ∈ A, (1 : X) * a * (1 : X)⁻¹ * a⁻¹ ∈ F
    refine ⟨one_mem _, fun a _ => ?_⟩
    rw [show (1 : X) * a * (1 : X)⁻¹ * a⁻¹ = 1 by group]
    exact one_mem _
  inv_mem' := by
    rintro x ⟨hx, hxA⟩
    show x⁻¹ ∈ normalizer (F : Set X) ∧ ∀ a ∈ A, x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ ∈ F
    refine ⟨inv_mem hx, fun a ha => ?_⟩
    have e : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem hx) _).1 (inv_mem (hxA a ha))

theorem mem_modCentralizerSub {A F : Subgroup X} {x : X} :
    x ∈ modCentralizerSub A F ↔ x ∈ normalizer (F : Set X) ∧ ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ F :=
  Iff.rfl

theorem comm_mem_mul_of_normalizer {F : Subgroup X} {x μ a : X}
    (hμ : μ ∈ normalizer (F : Set X)) (h1 : x * μ * x⁻¹ * μ⁻¹ ∈ F)
    (h2 : x * a * x⁻¹ * a⁻¹ ∈ F) : x * (μ * a) * x⁻¹ * (μ * a)⁻¹ ∈ F := by
  have e : x * (μ * a) * x⁻¹ * (μ * a)⁻¹ =
      (x * μ * x⁻¹ * μ⁻¹) * (μ * (x * a * x⁻¹ * a⁻¹) * μ⁻¹) := by group
  rw [e]
  exact mul_mem h1 ((mem_normalizer_iff.1 hμ _).1 h2)

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem mem_modCentralizerSub_yamadaS₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hxF : x ∈ normalizer (yamadaF₄ d t : Set G))
    (hM : ∀ μ ∈ yamadaM₄ d t, x * μ * x⁻¹ * μ⁻¹ ∈ yamadaF₄ d t)
    (hD : ∀ a ∈ yamadaD₄ d t, x * a * x⁻¹ * a⁻¹ ∈ yamadaF₄ d t) :
    x ∈ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
  refine mem_modCentralizerSub.2 ⟨hxF, fun σ hσ => ?_⟩
  have hσ' : σ ∈ ((yamadaM₄ d t ⊔ yamadaD₄ d t : Subgroup G) : Set G) := by
    rw [← h.yamadaS₄_eq_sup_yamadaD₄ d hlay]
    exact hσ
  have hD₄N : yamadaD₄ d t ≤ normalizer (yamadaM₄ d t : Set G) := fun a ha =>
    h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay ((inf_le_left : yamadaD₄ d t ≤ yamadaR₄ d t) ha)
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD₄N, Set.mem_mul] at hσ'
  obtain ⟨μ, hμ, a, ha, rfl⟩ := hσ'
  exact comm_mem_mul_of_normalizer (h.yamadaM₄_le_normalizer_yamadaF₄_R5 d hlay hμ) (hM μ hμ)
    (hD a ha)

theorem commutator_mem_yamadaF₄_of_mem_yamadaR₅
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t) :
    ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t := by
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
  have hR₅R₄ : yamadaR₅ d t ≤ normalizer (yamadaR₄ d t : Set G) :=
    (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.2.2
  have hD₅V₁ : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t :=
    (h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521).1
  have hSN : ∀ s ∈ d.S.map L.subtype, s ∈ normalizer (yamadaF₄ d t : Set G) := fun s hs => by
    have hsR₄ : s ∈ yamadaR₄ d t := h.S_map_le_yamadaR₄_R4 d hlay hs
    have hsC₅ : s ∈ normalizer (yamadaC₅ d t : Set G) :=
      le_normalizer_yamadaC₅ d t (h.S_le_normalizer_yamadaC₁ d hs)
    have hsV₁ : s ∈ normalizer (centralizer (yamadaV₁ d t : Set G) : Set G) :=
      mem_normalizer_centralizer_C8 (S_le_normalizer_yamadaV₁ d h593 hs)
    exact Common.mem_normalizer_inf (h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay hsR₄)
      (Common.mem_normalizer_inf (le_normalizer hsR₄) (Common.mem_normalizer_inf hsC₅ hsV₁))
  have hST : d.S.map L.subtype ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := fun s hs =>
    mem_modCentralizerSub.2 ⟨hSN s hs, fun σ hσ => hS₄c s (h.S_map_le_yamadaS₄_R4 d hlay hs) σ hσ⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have htT : t ∈ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) :=
    mem_modCentralizerSub.2 ⟨h.t_mem_normalizer_yamadaF₄ d hlay, fun σ hσ => by
      rw [htinv]
      exact htS₄ σ hσ⟩
  have hD₅N : ∀ y ∈ yamadaD₅ d t, y ∈ normalizer (yamadaR₄ d t : Set G) ∧
      y ∈ normalizer (yamadaY₂ d t : Set G) := by
    intro y hy
    have hyR₅ : y ∈ yamadaR₅ d t := mem_sup_left (mem_inf.1 hy).1
    have hyR₄ : y ∈ normalizer (yamadaR₄ d t : Set G) := hR₅R₄ hyR₅
    have hyV : y ∈ centralizer (yamadaV₁ d t : Set G) := (mem_inf.1 hy).2
    have hyS₄ : y ∈ normalizer (yamadaS₄ d t : Set G) :=
      Common.mem_normalizer_inf hyR₄
        (mem_normalizer_centralizer_C8 (Subgroup.centralizer_le_normalizer _ hyV))
    exact ⟨hyR₄, (mem_inf.1 (h.normalizer_yamadaS₄_le_two d hlay hyS₄)).2⟩
  have hD₅T : yamadaD₅ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
    intro y hy
    obtain ⟨hyR₄, hyY₂⟩ := hD₅N y hy
    have hyC₅ : y ∈ yamadaC₅ d t := (mem_inf.1 hy).1
    have hyV : y ∈ centralizer (yamadaV₁ d t : Set G) := (mem_inf.1 hy).2
    have hyM₄ : y ∈ normalizer (yamadaM₄ d t : Set G) :=
      Common.mem_normalizer_inf hyR₄ (mem_normalizer_centralizer_C8 hyY₂)
    have hyD₄ : y ∈ normalizer (yamadaD₄ d t : Set G) :=
      Common.mem_normalizer_inf hyR₄ (le_normalizer hy)
    refine h.mem_modCentralizerSub_yamadaS₄ d hlay (Common.mem_normalizer_inf hyM₄ hyD₄) ?_ ?_
    ·
      intro μ hμ
      have hμR₄ : μ ∈ yamadaR₄ d t := (inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) hμ
      have hμY₂ : μ ∈ centralizer (yamadaY₂ d t : Set G) :=
        (inf_le_right : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G)) hμ
      have hμV : μ ∈ centralizer (yamadaV₁ d t : Set G) :=
        centralizer_le (yamadaV₁_le_yamadaY₂ (t := t) d) hμY₂
      have hμC₅ : μ ∈ normalizer (yamadaC₅ d t : Set G) :=
        h.yamadaR₅_le_normalizer_yamadaC₅ d ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hμR₄)
      have hR : y * μ * y⁻¹ * μ⁻¹ ∈ yamadaR₄ d t :=
        mul_mem ((mem_normalizer_iff.1 hyR₄ μ).1 hμR₄) (inv_mem hμR₄)
      have hY : y * μ * y⁻¹ * μ⁻¹ ∈ centralizer (yamadaY₂ d t : Set G) :=
        mul_mem ((mem_normalizer_iff.1 (mem_normalizer_centralizer_C8 hyY₂) μ).1 hμY₂)
          (inv_mem hμY₂)
      have hC : y * μ * y⁻¹ * μ⁻¹ ∈ yamadaC₅ d t := by
        rw [show y * μ * y⁻¹ * μ⁻¹ = y * (μ * y⁻¹ * μ⁻¹) by group]
        exact mul_mem hyC₅ ((mem_normalizer_iff.1 hμC₅ y⁻¹).1 (inv_mem hyC₅))
      have hV : y * μ * y⁻¹ * μ⁻¹ ∈ centralizer (yamadaV₁ d t : Set G) :=
        mul_mem (mul_mem (mul_mem hyV hμV) (inv_mem hyV)) (inv_mem hμV)
      exact mem_inf.2 ⟨mem_inf.2 ⟨hR, hY⟩, mem_inf.2 ⟨hR, mem_inf.2 ⟨hC, hV⟩⟩⟩
    ·
      intro a ha
      have h1 : ⁅y, a⁆ ∈ ⁅yamadaD₅ d t, yamadaD₅ d t⁆ :=
        commutator_mem_commutator hy ((inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t) ha)
      rw [hD₅V₁, commutatorElement_def] at h1
      exact h.yamadaV₁_le_yamadaF₄_R5 d hlay h1
  have hR₅T : yamadaR₅ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
    show yamadaC₅ d t ⊔ d.S.map L.subtype ≤ _
    refine sup_le ?_ hST
    rw [(h.yamada_5_20 d hlay).1]
    exact sup_le hD₅T (zpowers_le.2 htT)
  intro x hx s hs
  exact (mem_modCentralizerSub.1 (hR₅T hx)).2 s hs

theorem commutator_mem_yamadaF₄_of_mem_yamadaR₆
    (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hM₄ : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t)
    (hR₆D₄ : yamadaR₆ d t ≤ normalizer (yamadaD₄ d t : Set G) ⊓
      normalizer (yamadaF₄ d t : Set G)) :
    ∀ x ∈ yamadaR₆ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t := by
  have hMM₄ : d.M.map L.subtype ≤ yamadaM₄ d t := by
    rw [hM₄]
    exact le_sup_left
  have hMN : d.M.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) := fun u hu =>
    h.yamadaM₄_le_normalizer_yamadaF₄_R5 d hlay (hMM₄ hu)
  have hST : d.S.map L.subtype ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := fun s hs =>
    mem_modCentralizerSub.2 ⟨(mem_inf.1 (hR₆D₄ (S_map_le_yamadaR₆ d t hs))).2,
      fun σ hσ => hS₄c s (h.S_map_le_yamadaS₄_R4 d hlay hs) σ hσ⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have htT : t ∈ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) :=
    mem_modCentralizerSub.2 ⟨h.t_mem_normalizer_yamadaF₄ d hlay, fun σ hσ => by
      rw [htinv]
      exact htS₄ σ hσ⟩
  have hM₆T : yamadaM₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
    intro m hm
    have hmR₆ : m ∈ yamadaR₆ d t := yamadaL₆_le_yamadaR₆ d t (yamadaM₆_le_yamadaL₆ d t hm)
    have hmN := mem_inf.1 (hR₆D₄ hmR₆)
    refine h.mem_modCentralizerSub_yamadaS₄ d hlay hmN.2 ?_ ?_
    ·
      intro μ hμ
      have hμ' : μ ∈ ((d.M.map L.subtype ⊔ yamadaF₄ d t : Subgroup G) : Set G) := by
        rw [← hM₄]
        exact hμ
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hMN, Set.mem_mul] at hμ'
      obtain ⟨u, hu, g, hg, rfl⟩ := hμ'
      have hmT₆ : m ∈ yamadaT₆ d t := by
        rw [← h.yamadaL₆_eq_yamadaT₆ d hlay]
        exact yamadaM₆_le_yamadaL₆ d t hm
      have huF : m * u * m⁻¹ * u⁻¹ ∈ yamadaF₄ d t :=
        h.yamadaW₃_le_yamadaF₄_R5 d hlay
          (h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay hmT₆
            (h.yamadaM_map_le_yamadaM₃_R5 d hlay hu))
      have hgF : m * g * m⁻¹ * g⁻¹ ∈ yamadaF₄ d t :=
        mul_mem ((mem_normalizer_iff.1 hmN.2 g).1 hg) (inv_mem hg)
      exact comm_mem_mul_of_normalizer (hMN hu) huF hgF
    ·
      intro a ha
      have hmC : m ∈ centralizer (yamadaY₂ d t : Set G) :=
        (inf_le_right : yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G)) hm
      have haR₄ : a ∈ yamadaR₄ d t := (inf_le_left : yamadaD₄ d t ≤ yamadaR₄ d t) ha
      have haC : a ∈ normalizer (centralizer (yamadaY₂ d t : Set G) : Set G) :=
        mem_normalizer_centralizer_C8 (h.yamadaR₄_le_normalizer_yamadaY₂_R4 d hlay haR₄)
      have hD : m * a * m⁻¹ * a⁻¹ ∈ yamadaD₄ d t :=
        mul_mem ((mem_normalizer_iff.1 hmN.1 a).1 ha) (inv_mem ha)
      have hR : m * a * m⁻¹ * a⁻¹ ∈ yamadaR₄ d t :=
        (inf_le_left : yamadaD₄ d t ≤ yamadaR₄ d t) hD
      have hC : m * a * m⁻¹ * a⁻¹ ∈ centralizer (yamadaY₂ d t : Set G) := by
        rw [show m * a * m⁻¹ * a⁻¹ = m * (a * m⁻¹ * a⁻¹) by group]
        exact mul_mem hmC ((mem_normalizer_iff.1 haC m⁻¹).1 (inv_mem hmC))
      exact mem_inf.2 ⟨mem_inf.2 ⟨hR, hC⟩, hD⟩
  have hL₆T : yamadaL₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
    rw [(h.yamada_5_29_1_of_layerHyp d hlay).1]
    exact sup_le hM₆T (zpowers_le.2 htT)
  have hR₆T : yamadaR₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
    show yamadaL₆ d t ⊔ d.S.map L.subtype ≤ _
    exact sup_le hL₆T hST
  intro x hx s hs
  exact (mem_modCentralizerSub.1 (hR₆T hx)).2 s hs

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
