module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYTwentyOne

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaR₅ (d : G2Data L K) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaR₂ d t : Set G))

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_mem_yamadaR₅star_inv_mul (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaR₂ d t : Set G)) :
    ∃ g₁ ∈ yamadaR₅star d t,
      g₁⁻¹ * g ∈ yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) := by
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hR₅ := h.yamadaR₅star_le_normalizer_yamadaR₂ hW d hK hD
  obtain ⟨x, hx, e⟩ := (h.yamada_5_21_3 hW d hK hD).1 g hg
  obtain ⟨g₁, hg₁, y, hy, e₁⟩ := h.exists_mem_yamadaR₅star_conj_eq d hK hD hx
  have hg₁Y : g₁ ∈ normalizer (yamadaY₂ d t : Set G) := hFY (hEF (hRE (hR₅ hg₁)))
  refine ⟨g₁, hg₁, (h.mem_normalizer_yamadaR₂_conj_iff hW d hK hD).1
    ⟨mul_mem (inv_mem (hR₅ hg₁)) hg, g₁⁻¹ * y⁻¹ * g₁, ?_, ?_⟩⟩
  · have := (mem_normalizer_iff.1 (inv_mem hg₁Y) y⁻¹).1 (inv_mem hy)
    rwa [inv_inv] at this
  · have e₂ : t * x = g₁ * t * g₁⁻¹ * y⁻¹ := by
      rw [e₁]
      group
    calc g₁⁻¹ * g * t * (g₁⁻¹ * g)⁻¹ = g₁⁻¹ * (g * t * g⁻¹) * g₁ := by group
      _ = g₁⁻¹ * (g₁ * t * g₁⁻¹ * y⁻¹) * g₁ := by rw [e, e₂]
      _ = t * (g₁⁻¹ * y⁻¹ * g₁) := by group

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₅star (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaR₅star d t : Set G) := fun c hc => by
  obtain ⟨hNS₁, -, hNS₃⟩ := h.centralizer_inf_normalizer_S_le d hK hD
  obtain ⟨hct, hcS⟩ := Subgroup.mem_inf.1 hc
  have hcR : c ∈ normalizer (yamadaRstar d t : Set G) :=
    mem_normalizer_sup (LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hNS₁ hc)) hcS
  have hcL₂ : c ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
      (Subgroup.mem_inf.2 ⟨hct, hNS₃ hc⟩))
  have hcE₁ : c ∈ normalizer (yamadaE₁ d t : Set G) := Common.mem_normalizer_inf hcL₂ (hNS₁ hc)
  exact Common.mem_normalizer_inf hcR (Subgroup.le_normalizer hcE₁)

theorem normalizer_yamadaR₂_eq_mul (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) = (yamadaR₅star d t : Set G) *
      ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  obtain ⟨-, hR₂R₅, hR₅, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hset := (h.yamada_5_21_3 hW d hK hD).2.2.2.2
  ext g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨g₁, hg₁, hc⟩ := h.exists_mem_yamadaR₅star_inv_mul hW d hK hD hg
    have hc' : g₁⁻¹ * g ∈ ((yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer (d.S : Set G)) : Subgroup G) : Set G) := hc
    rw [hset] at hc'
    obtain ⟨r, hr, c, hc, hrc⟩ := Set.mem_mul.1 hc'
    refine Set.mem_mul.2 ⟨g₁ * r, mul_mem hg₁ (hR₂R₅ hr), c, hc, ?_⟩
    rw [mul_assoc, hrc, mul_inv_cancel_left]
  · obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg
    exact mul_mem (hR₅ hx) (hNR₂ hc)

theorem yamadaR₅_inf_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaR₅ d t ⊓ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ≤ yamadaR d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  exact h.le_yamadaR_of_normal d hK inf_le_right
    (fun g hg => Common.mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (hNR₂ hg)) (Subgroup.le_normalizer hg))
    ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)

theorem yamada_5_27_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) : yamadaR₅ d t = yamadaR₅star d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hR₂R₅, hR₅, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hset := h.normalizer_yamadaR₂_eq_mul hW d hK hD
  have hNR₅ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅star d hK hD
  have hUN : normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaR₅star d t : Set G) :=
    fun g hg => by
      have hg' : g ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) := hg
      rw [hset] at hg'
      obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg'
      exact mul_mem (Subgroup.le_normalizer hx) (hNR₅ hc)
  have hle : yamadaR₅star d t ≤ yamadaR₅ d t :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hR₅ hUN
      ((h.isPGroup_yamadaRstar d).to_le inf_le_left)
  refine le_antisymm (fun z hz => ?_) hle
  have hz' : z ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _ hz
  rw [hset] at hz'
  obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hz'
  have hcR₅ : c ∈ yamadaR₅ d t := by
    have := mul_mem (inv_mem (hle hx)) hz
    rwa [inv_mul_cancel_left] at this
  have hcR := h.yamadaR₅_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hcR₅, hc⟩)
  exact mul_mem hx (hR₂R₅ ((h.yamadaR₂_inf_centralizer d hK).1 hcR))

theorem yamada_5_27_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaR₂ d t : Set G) =
        yamadaR₅ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ∧
      ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) = (yamadaR₅ d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) ∧
      yamadaR₅ d t ⊓ centralizer ({t} : Set G) = yamadaR d t := by
  have hR₅ := h.yamada_5_27_3 hW d hK hD
  have hset := h.normalizer_yamadaR₂_eq_mul hW d hK hD
  rw [← hR₅] at hset
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  obtain ⟨-, hR₂R₅, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hR₅V : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le hR₅V hNR₂), hset,
    le_antisymm (fun x hx => ?_) ?_⟩
  · have hg' : g ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.1 hg'
    exact mul_mem (mem_sup_left hx) (mem_sup_right hc)
  · obtain ⟨hxR₅, hxC⟩ := Subgroup.mem_inf.1 hx
    rw [← (h.yamadaR₂_inf_centralizer d hK).2]
    refine Subgroup.mem_inf.2 ⟨(h.mem_yamadaR₂_iff hW d hK hD).2 ⟨(Subgroup.mem_inf.1
      (hR₅.le hxR₅)).1, ?_⟩, hxC⟩
    rw [show t * x * t * x⁻¹ = t * (x * t) * x⁻¹ by group, (mem_centralizer_singleton_iff.1 hxC),
      show t * (t * x) * x⁻¹ = t * t by group, h.t_mul_t]
    exact one_mem _
  · rw [← (h.yamadaR₂_inf_centralizer d hK).2]
    exact inf_le_inf_right _ (hR₂R₅.trans hR₅.ge)

theorem crossed_conj_mem_of_mem_yamadaR₅star (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {H : Subgroup G}
    (hY₁H : yamadaY₁ d t ≤ H) (hHF : H ≤ d.F ⊔ yamadaU₁ d t)
    (hFH : d.F ⊔ yamadaU₁ d t ≤ normalizer (H : Set G)) {z g : G}
    (hz : z ∈ yamadaR₅star d t) (hgR : g ∈ yamadaRstar d t) (hg : t * g * t * g⁻¹ ∈ H) :
    t * (z * g * z⁻¹) * t * (z * g * z⁻¹)⁻¹ ∈ H := by
  obtain ⟨hzR, hzκ⟩ := (h.mem_yamadaR₅star_iff d hK hD).1 hz
  have hzgR : z * g * z⁻¹ ∈ yamadaRstar d t := mul_mem (mul_mem hzR hgR) (inv_mem hzR)
  rw [h.crossed_conj' z g]
  have h1 : z * (t * g * t * g⁻¹) * z⁻¹ * (t * g * t * g⁻¹)⁻¹ ∈ yamadaY₁ d t :=
    (h.commutator_mem_of_mem_yamadaRstar d hK hD hzR).2 _ (hHF hg)
  have h2 : (z * g * z⁻¹) * (t * z * t * z⁻¹)⁻¹ * (z * g * z⁻¹)⁻¹ * (t * z * t * z⁻¹)⁻¹⁻¹ ∈
      yamadaY₁ d t :=
    (h.commutator_mem_of_mem_yamadaRstar d hK hD hzgR).2 _ (inv_mem hzκ)
  rw [show t * z * t * z⁻¹ * (z * (t * g * t * g⁻¹) * z⁻¹) *
      (z * g * z⁻¹ * (t * z * t * z⁻¹)⁻¹ * (z * g * z⁻¹)⁻¹) =
    (t * z * t * z⁻¹) * ((z * (t * g * t * g⁻¹) * z⁻¹ * (t * g * t * g⁻¹)⁻¹) *
      (t * g * t * g⁻¹) * ((z * g * z⁻¹) * (t * z * t * z⁻¹)⁻¹ * (z * g * z⁻¹)⁻¹ *
        (t * z * t * z⁻¹)⁻¹⁻¹)) * (t * z * t * z⁻¹)⁻¹ by group]
  exact (mem_normalizer_iff.1 (hFH hzκ) _).1 (mul_mem (mul_mem (hY₁H h1) hg) (hY₁H h2))

theorem F₁_le_normalizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    d.F ⊔ yamadaU₁ d t ≤ normalizer (yamadaW₁ d t : Set G) ∧
      d.F ⊔ yamadaU₁ d t ≤ normalizer (yamadaX₁ d t : Set G) := by
  obtain ⟨-, hYX, hYW, hXF, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hFS : d.F ≤ d.S := hFD.trans hDS
  exact ⟨sup_le (hFS.trans (h.S_le_normalizer_sup d hK hD hYW (hWF.trans hFD) (Or.inr hWF)))
      (le_sup_right.trans Subgroup.le_normalizer),
    sup_le (hFS.trans (h.S_le_normalizer_sup d hK hD hYX (hXF.trans hFD) (Or.inr hXF)))
      (le_sup_right.trans Subgroup.le_normalizer)⟩

theorem yamadaR₅_le_normalizer (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₅ d t ≤ normalizer (yamadaR₃ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaR₄ d t : Set G) := by
  obtain ⟨-, hYX, hYW, hXF, hWF, -⟩ := d.inclusions
  obtain ⟨hFW, hFX⟩ := h.F₁_le_normalizer d hK hD
  rw [h.yamada_5_27_3 hW d hK hD, h.yamada_5_23_4 hW d hK hD, h.yamada_5_25_4 hW d hK hD]
  refine ⟨fun z hz => mem_normalizer_of_conj_mem fun g hg => ?_,
    fun z hz => mem_normalizer_of_conj_mem fun g hg => ?_⟩
  · obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₃star_iff d hK hD).1 hg
    have hzR := ((h.mem_yamadaR₅star_iff d hK hD).1 hz).1
    refine (h.mem_yamadaR₃star_iff d hK hD).2 ⟨mul_mem (mul_mem hzR hgR) (inv_mem hzR), ?_⟩
    exact h.crossed_conj_mem_of_mem_yamadaR₅star d hK hD (sup_le_sup_right hYW _)
      (sup_le_sup_right hWF _) hFW hz hgR hgκ
  · obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₄star_iff d hK hD).1 hg
    have hzR := ((h.mem_yamadaR₅star_iff d hK hD).1 hz).1
    refine (h.mem_yamadaR₄star_iff d hK hD).2 ⟨mul_mem (mul_mem hzR hgR) (inv_mem hzR), ?_⟩
    exact h.crossed_conj_mem_of_mem_yamadaR₅star d hK hD (sup_le_sup_right hYX _)
      (sup_le_sup_right hXF _) hFX hz hgR hgκ

theorem F_inf_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : d.F ⊓ yamadaY₂ d t = d.Y := by
  obtain ⟨-, hYX, -, hXF, -⟩ := d.inclusions
  refine le_antisymm ?_ (le_inf (hYX.trans hXF) (h.Y_le_yamadaY₂ d hK hD))
  rw [← h.yamadaY₂_inf_centralizer d hK hD, inf_comm]
  exact inf_le_inf_left _ ((d.image_le _).trans h.L_le_centralizer)

theorem centralizer_inf_normalizer_S_le_normalizer_F (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (d.F : Set G) := by
  intro c hc
  obtain ⟨hcW, hcX⟩ := Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hc)
  rw [← (d.yamada_defs).2.2.2.1]
  exact mem_normalizer_sup hcX hcW

theorem yamada_5_27_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (yamadaR₅ d t = yamadaR₃ d t ⊔ yamadaR₄ d t ∧ yamadaR₃ d t ⊓ yamadaR₄ d t = yamadaR₂ d t ∧
      yamadaR₅ d t ≤ normalizer (yamadaR₃ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaR₄ d t : Set G)) ∧
    ∃ _ : ((yamadaR₂ d t).subgroupOf (yamadaR₅ d t)).Normal,
      ∃ _ : (d.Y.subgroupOf d.F).Normal,
        ∃ φ : yamadaR₅ d t ⧸ (yamadaR₂ d t).subgroupOf (yamadaR₅ d t) ≃*
          d.F ⧸ d.Y.subgroupOf d.F,
        (∀ (x : yamadaR₅ d t) (a : d.F), ∀ y ∈ yamadaY₂ d t,
          (x : G) * t * (x : G)⁻¹ = t * a * y → φ (QuotientGroup.mk x) = QuotientGroup.mk a) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G),
          ∀ (x : yamadaR₅ d t) (a : d.F), φ (QuotientGroup.mk x) = QuotientGroup.mk a →
            ∃ (hx : c * x * c⁻¹ ∈ yamadaR₅ d t) (ha : c * a * c⁻¹ ∈ d.F),
              φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, ha⟩ := by
  obtain ⟨-, hYX, -, hXF, -, -, hFM, -⟩ := d.inclusions
  have hYF : d.Y ≤ d.F := hYX.trans hXF
  have hR₅ := h.yamada_5_27_3 hW d hK hD
  obtain ⟨hR₂eq, hR₂R₅, -, hR₅eq, -⟩ := h.yamada_5_21_2 hW d hK hD
  have hU₁Y₂ := yamadaU₁_le_yamadaY₂ d t
  have hY₁Y₂ : yamadaY₁ d t ≤ yamadaY₂ d t := sup_le (h.Y_le_yamadaY₂ d hK hD) hU₁Y₂
  have hFY₂ : d.F ≤ centralizer (yamadaY₂ d t : Set G) :=
    hFM.trans (h.M_le_centralizer_yamadaY₂ d hK hD)
  have hYFn : (d.Y.subgroupOf d.F).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hYF).2 fun a ha => ?_
    have : a ∈ L ⊓ normalizer (d.Y : Set G) := by
      rw [(d.yamada_3_13_3_G).1]
      exact mem_sup_left (hFM ha)
    exact (Subgroup.mem_inf.1 this).2
  have huniq : ∀ {a₁ a₂ η₁ η₂ : G}, a₁ ∈ d.F → a₂ ∈ d.F → η₁ ∈ yamadaY₂ d t →
      η₂ ∈ yamadaY₂ d t → a₁ * η₁ = a₂ * η₂ → a₁⁻¹ * a₂ ∈ d.Y := by
    intro a₁ a₂ η₁ η₂ ha₁ ha₂ hη₁ hη₂ e
    rw [← h.F_inf_yamadaY₂ d hK hD]
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₁) ha₂, ?_⟩
    rw [show a₁⁻¹ * a₂ = η₁ * η₂⁻¹ by
      calc a₁⁻¹ * a₂ = a₁⁻¹ * (a₂ * η₂) * η₂⁻¹ := by group
        _ = a₁⁻¹ * (a₁ * η₁) * η₂⁻¹ := by rw [e]
        _ = η₁ * η₂⁻¹ := by group]
    exact mul_mem hη₁ (inv_mem hη₂)
  have hR₅R : ∀ x : yamadaR₅ d t, (x : G) ∈ yamadaRstar d t := fun x =>
    ((h.mem_yamadaR₅star_iff d hK hD).1 (hR₅.le x.2)).1
  have hκF : ∀ x : yamadaR₅ d t, t * (x : G) * t * (x : G)⁻¹ ∈ d.F ⊔ yamadaU₁ d t := fun x =>
    ((h.mem_yamadaR₅star_iff d hK hD).1 (hR₅.le x.2)).2
  have hdec : ∀ x : yamadaR₅ d t, ∃ a ∈ d.F, ∃ η ∈ yamadaY₂ d t,
      t * (x : G) * t * (x : G)⁻¹ = a * η := fun x =>
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_F d hK hD) _
      (sup_le_sup_left hU₁Y₂ _ (hκF x))
  choose af haf ηf hηf hfe using hdec
  let ψ : yamadaR₅ d t →* d.F ⧸ d.Y.subgroupOf d.F :=
    { toFun := fun x => QuotientGroup.mk ⟨af x, haf x⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        have e : (1 : G) * 1 = af 1 * ηf 1 := by
          rw [← hfe 1]
          show (1 : G) * 1 = t * 1 * t * (1 : G)⁻¹
          rw [mul_one, inv_one, mul_one, mul_one, h.t_mul_t]
        have := huniq (one_mem _) (haf 1) (one_mem _) (hηf 1) e
        rwa [inv_one, one_mul] at this
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        show (af (x * y))⁻¹ * (af x * af y) ∈ d.Y
        have hz : (x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹)⁻¹ ∈
            yamadaY₂ d t :=
          hY₁Y₂ ((h.commutator_mem_of_mem_yamadaRstar d hK hD (hR₅R x)).2 _ (hκF y))
        have hcomm : (ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
            (t * y * t * (y : G)⁻¹)⁻¹)) * af y =
            af y * (ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
              (t * y * t * (y : G)⁻¹)⁻¹)) :=
          (mem_centralizer_iff.1 (hFY₂ (haf y)) _ (mul_mem (hηf x) hz))
        have e : af (x * y) * ηf (x * y) = (af x * af y) * (ηf x *
            ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ * (t * y * t * (y : G)⁻¹)⁻¹) *
              ηf y) := by
          rw [← hfe (x * y)]
          show t * ((x : G) * y) * t * ((x : G) * y)⁻¹ = _
          rw [h.crossed_mul' (x : G) y]
          calc t * x * t * (x : G)⁻¹ * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹) =
                t * x * t * (x : G)⁻¹ * (((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹) * (t * y * t * (y : G)⁻¹)) := by group
            _ = af x * ηf x * (((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹) * (af y * ηf y)) := by rw [hfe x, hfe y]
            _ = af x * ((ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹)) * af y) * ηf y := by group
            _ = af x * (af y * (ηf x * ((x : G) * (t * y * t * (y : G)⁻¹) * (x : G)⁻¹ *
                  (t * y * t * (y : G)⁻¹)⁻¹))) * ηf y := by rw [hcomm]
            _ = _ := by group
        exact huniq (haf (x * y)) (mul_mem (haf x) (haf y)) (hηf (x * y))
          (mul_mem (mul_mem (hηf x) hz) (hηf y)) e }
  have hψ : ∀ x : yamadaR₅ d t, ψ x = QuotientGroup.mk ⟨af x, haf x⟩ := fun _ => rfl
  have hform : ∀ (x : yamadaR₅ d t) (a : d.F), ∀ y ∈ yamadaY₂ d t,
      (x : G) * t * (x : G)⁻¹ = t * a * y → ψ x = QuotientGroup.mk a := by
    intro x a y hy e
    rw [hψ, QuotientGroup.eq, mem_subgroupOf]
    refine huniq (haf x) a.2 (hηf x) hy ?_
    rw [← hfe x, show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, e,
      ← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
  have hker : ψ.ker = (yamadaR₂ d t).subgroupOf (yamadaR₅ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hx
      refine (h.mem_yamadaR₂_iff hW d hK hD).2 ⟨hR₅R x, ?_⟩
      obtain ⟨φ, hφ, u, hu, e⟩ := Common.exists_mul_of_le_normalizer
        (h.yamadaU₁_le_normalizer_of_le_D d hK hD d.inclusions.2.2.2.2.2.1) _ (hκF x)
      have h1 := huniq (haf x) hφ (hηf x) (hU₁Y₂ hu) ((hfe x).symm.trans e)
      have hφY : φ ∈ d.Y := by
        have := mul_mem hx h1
        rwa [mul_inv_cancel_left] at this
      rw [e]
      exact mul_mem (mem_sup_left hφY) (mem_sup_right hu)
    · intro hx
      have h1 := ((h.mem_yamadaR₂_iff hW d hK hD).1 hx).2
      have h2 := huniq (haf x) (one_mem _) (hηf x) (hY₁Y₂ h1) (by rw [← hfe x, one_mul])
      have := inv_mem h2
      rwa [mul_one, inv_inv] at this
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg, u, hu, e⟩ := (h.yamada_5_21_1 d hK hD).2.2.2 a
      (by rw [h.yamadaF₁_eq_sup d hK hD]; exact mem_sup_left a.2)
    exact ⟨⟨g, hR₅.ge hg⟩, hform ⟨g, hR₅.ge hg⟩ a u (hU₁Y₂ hu) e⟩
  have hR₂n : ((yamadaR₂ d t).subgroupOf (yamadaR₅ d t)).Normal := hker ▸ ψ.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφdef
  have hφ : ∀ x : yamadaR₅ d t, φ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  have hR₃ := h.yamada_5_23_4 hW d hK hD
  have hR₄ := h.yamada_5_25_4 hW d hK hD
  refine ⟨⟨by rw [hR₅, hR₃, hR₄, hR₅eq], by rw [hR₃, hR₄, hR₂eq],
    (h.yamadaR₅_le_normalizer hW d hK hD).1, (h.yamadaR₅_le_normalizer hW d hK hD).2⟩,
    hR₂n, hYFn, φ, fun x a y hy e => (hφ x).trans (hform x a y hy e), ?_⟩
  intro c hc x a hxa
  obtain ⟨hct, -⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  have hcR₅ : c ∈ normalizer (yamadaR₅ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hNR₂ hc)
  have hcF := h.centralizer_inf_normalizer_S_le_normalizer_F d hK hD hc
  have hcY := (h.centralizer_inf_normalizer_S_le d hK hD).2.2 hc
  have hcY₂ := hFY (hEF (hRE (hNR₂ hc)))
  have hx : c * x * c⁻¹ ∈ yamadaR₅ d t := (mem_normalizer_iff.1 hcR₅ x).1 x.2
  have ha : c * a * c⁻¹ ∈ d.F := (mem_normalizer_iff.1 hcF a).1 a.2
  refine ⟨hx, ha, ?_⟩
  rw [hφ, hψ, QuotientGroup.eq, mem_subgroupOf] at hxa
  have hcte : c * t = t * c := mem_centralizer_singleton_iff.1 hct
  have hct' : c⁻¹ * t * c = t := by rw [mul_assoc, ← hcte, inv_mul_cancel_left]
  have hcafF : c * af x * c⁻¹ ∈ d.F := (mem_normalizer_iff.1 hcF _).1 (haf x)
  rw [hφ, hform ⟨_, hx⟩ ⟨_, hcafF⟩ (c * ηf x * c⁻¹) ((mem_normalizer_iff.1 hcY₂ _).1 (hηf x)) ?_,
    QuotientGroup.eq, mem_subgroupOf]
  · show (c * af x * c⁻¹)⁻¹ * (c * a * c⁻¹) ∈ d.Y
    rw [show (c * af x * c⁻¹)⁻¹ * (c * a * c⁻¹) = c * ((af x)⁻¹ * a) * c⁻¹ by group]
    exact (mem_normalizer_iff.1 hcY _).1 hxa
  · show c * x * c⁻¹ * t * (c * x * c⁻¹)⁻¹ = t * (c * af x * c⁻¹) * (c * ηf x * c⁻¹)
    calc c * x * c⁻¹ * t * (c * x * c⁻¹)⁻¹ = c * x * (c⁻¹ * t * c) * (x : G)⁻¹ * c⁻¹ := by group
      _ = c * ((x : G) * t * (x : G)⁻¹) * c⁻¹ := by rw [hct']; group
      _ = c * (t * (t * x * t * (x : G)⁻¹)) * c⁻¹ := by rw [h.conj_t_eq_mul_crossed (x : G)]
      _ = c * (t * (af x * ηf x)) * c⁻¹ := by rw [hfe x]
      _ = (c * t * c⁻¹) * (c * af x * c⁻¹) * (c * ηf x * c⁻¹) := by group
      _ = t * (c * af x * c⁻¹) * (c * ηf x * c⁻¹) := by rw [hcte, mul_inv_cancel_right]

theorem yamadaS₁_sup_yamadaC₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaS₁ d t ⊔ yamadaC₁ d t = yamadaR₁ d t ∧ yamadaM₁ d t ⊔ yamadaC₁ d t = yamadaR₁ d t := by
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have hDC₁ : d.D ≤ yamadaC₁ d t := (le_sup_right : d.D ≤ yamadaD₁ d t).trans
    (h.yamadaD₁_le_yamadaC₁ d hK)
  have hS₁ := h.yamadaS₁_eq_sup d hK hD
  have hM₁R₁ : yamadaM₁ d t ≤ yamadaR₁ d t := inf_le_left.trans inf_le_right
  have hMM₁ : d.M ≤ yamadaM₁ d t := le_inf (le_sup_left.trans (h.tM_le_yamadaL₁ d hK))
    (d.inclusions.2.2.2.2.2.2.2.2.1.trans le_sup_left)
  refine ⟨?_, le_antisymm (sup_le hM₁R₁ le_sup_left) (sup_le le_sup_right ?_)⟩
  · rw [hS₁]
    exact le_antisymm (sup_le (sup_le le_sup_right (hU₁C₁.trans le_sup_left)) le_sup_left)
      (sup_le le_sup_right (le_sup_left.trans le_sup_left))
  · rw [← (d.yamada_defs).2.2.2.2.2.2.2.2]
    exact sup_le (hDC₁.trans le_sup_right) (hMM₁.trans le_sup_left)

theorem yamadaR₂_le_normalizer_S₁_M₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t ≤ normalizer (yamadaS₁ d t : Set G) ∧
      yamadaR₂ d t ≤ normalizer (yamadaM₁ d t : Set G) := by
  obtain ⟨hR₂, -⟩ := h.yamadaR₂_eq_yamadaR₁_sup d hK hD
  obtain ⟨hS₁R₁, -, hR₁S₁, -⟩ := h.yamadaS₁_spec d hK
  have hS₁ := h.yamadaS₁_eq_sup d hK hD
  have hY₁S₁ : yamadaY₁ d t ≤ yamadaS₁ d t := by
    rw [hS₁]
    exact sup_le_sup_right (d.inclusions.2.1.trans (d.inclusions.2.2.2.1.trans
      (d.inclusions.2.2.2.2.2.1.trans d.inclusions.2.2.2.2.2.2.2.1))) _
  have hY₂S₁ : yamadaY₂ d t ≤ normalizer (yamadaS₁ d t : Set G) := fun y hy =>
    mem_normalizer_of_conj_mem fun s hs => by
      have := h.commutator_mem_yamadaY₁ d hK hD (hS₁R₁ hs) hy
      rw [show y * s * y⁻¹ = (s * y * s⁻¹ * y⁻¹)⁻¹ * s by group]
      exact mul_mem (inv_mem (hY₁S₁ this)) hs
  have hS₁N : yamadaR₂ d t ≤ normalizer (yamadaS₁ d t : Set G) := by
    rw [hR₂]
    exact sup_le hR₁S₁ hY₂S₁
  have hL₂N : yamadaR₂ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
    sup_le Subgroup.le_normalizer (h.S_le_normalizer_yamadaL₂ d)
  have hR₁N := (h.yamada_5_6_1 d hK).2.2.1
  exact ⟨hS₁N, fun r hr => Common.mem_normalizer_inf (Common.mem_normalizer_inf (hL₂N hr)
    (hR₁N hr)) (hS₁N hr)⟩

theorem yamada_5_28 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₅ d t ⊓ normalizer (yamadaR₁ d t : Set G) = yamadaR₂ d t ∧
      yamadaR₅ d t ⊓ normalizer (yamadaS₁ d t : Set G) = yamadaR₂ d t ∧
      yamadaR₅ d t ⊓ normalizer (yamadaM₁ d t : Set G) = yamadaR₂ d t := by
  have hR₅ := h.yamada_5_27_3 hW d hK hD
  obtain ⟨-, hR₂R₅', -⟩ := h.yamada_5_21_2 hW d hK hD
  have hR₂R₅ : yamadaR₂ d t ≤ yamadaR₅ d t := hR₂R₅'.trans hR₅.ge
  have hR₅C₁ : yamadaR₅ d t ≤ normalizer (yamadaC₁ d t : Set G) := fun z hz =>
    h.yamadaRstar_le_normalizer d ((h.mem_yamadaR₅star_iff d hK hD).1 (hR₅.le hz)).1
  obtain ⟨h53a, -, h53c⟩ := h.yamada_5_17_3 hW d hK hD
  obtain ⟨hS₁C₁, hM₁C₁⟩ := h.yamadaS₁_sup_yamadaC₁ d hK hD
  obtain ⟨hR₂S₁, hR₂M₁⟩ := h.yamadaR₂_le_normalizer_S₁_M₁ d hK hD
  have h1 : yamadaR₅ d t ⊓ normalizer (yamadaR₁ d t : Set G) = yamadaR₂ d t := by
    refine le_antisymm (fun z hz => ?_) (le_inf hR₂R₅ (h.yamada_5_6_1 d hK).2.2.1)
    obtain ⟨hzR₅, hzN⟩ := Subgroup.mem_inf.1 hz
    have hz' : z ∈ ((normalizer (yamadaR₁ d t : Set G) : Subgroup G) : Set G) := hzN
    rw [h53a, h53c] at hz'
    obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.1 hz'
    have hcR₅ : c ∈ yamadaR₅ d t := by
      have := mul_mem (inv_mem (hR₂R₅ hr)) hzR₅
      rwa [inv_mul_cancel_left] at this
    have hcR := h.yamadaR₅_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hcR₅, hc⟩)
    exact mul_mem hr ((h.yamadaR₂_inf_centralizer d hK).1 hcR)
  refine ⟨h1, le_antisymm (fun z hz => ?_) (le_inf hR₂R₅ hR₂S₁),
    le_antisymm (fun z hz => ?_) (le_inf hR₂R₅ hR₂M₁)⟩
  · obtain ⟨hzR₅, hzN⟩ := Subgroup.mem_inf.1 hz
    rw [← h1]
    refine Subgroup.mem_inf.2 ⟨hzR₅, ?_⟩
    rw [← hS₁C₁]
    exact mem_normalizer_sup hzN (hR₅C₁ hzR₅)
  · obtain ⟨hzR₅, hzN⟩ := Subgroup.mem_inf.1 hz
    rw [← h1]
    refine Subgroup.mem_inf.2 ⟨hzR₅, ?_⟩
    rw [← hM₁C₁]
    exact mem_normalizer_sup hzN (hR₅C₁ hzR₅)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
