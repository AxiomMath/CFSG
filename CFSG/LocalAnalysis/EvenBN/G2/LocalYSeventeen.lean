module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYSixteen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type} [Group G] [Finite G] {t : G}

theorem mem_normalizer_sup_zpowers_of_conj_mem {A : Subgroup G} {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgt : g * t * g⁻¹ ∈ A ⊔ zpowers t) :
    g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : A ⊔ zpowers t ≤ (A ⊔ zpowers t).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => mem_sup_left ((mem_normalizer_iff.1 hgA a).1 ha)) ((zpowers_le).2 hgt)
  exact hle hx

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Light

theorem mem_normalizer_of_mem_normalizer_sup_t (h : Setup G L f t) {E : Subgroup G}
    (hEL : E ≤ L) {c : G} (hc : c ∈ centralizer ({t} : Set G))
    (hcE : c ∈ normalizer ((E ⊔ zpowers t : Subgroup G) : Set G)) :
    c ∈ normalizer (E : Set G) := by
  refine mem_normalizer_of_conj_mem fun s hs => ?_
  have h1 : c * s * c⁻¹ ∈ E ⊔ zpowers t := (mem_normalizer_iff.1 hcE s).1 (mem_sup_left hs)
  have h2 : c * s * c⁻¹ ∈ L :=
    (mem_normalizer_iff.1 (h.centralizer_le_normalizer hc) s).1 (hEL hs)
  rcases (h.mem_sup_zpowers_iff hEL).1 h1 with h3 | h3
  · exact h3
  · have := mul_mem (hEL h3) (inv_mem h2)
    rw [mul_inv_cancel_right] at this
    exact absurd this h.t_not_mem_L

end Light

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaY₂_le_normalizer_F (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≤ normalizer (d.F : Set G) := fun y hy =>
  mem_normalizer_of_conj_mem fun x hx => by
    obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
    rw [mem_centralizer_iff.1 ((hFM.trans (h.M_le_centralizer_yamadaY₂ d hK hD)) hx) y hy,
      mul_inv_cancel_right]
    exact hx

theorem yamadaF₂_center (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaF₂ d t ⊓ centralizer (yamadaF₂ d t : Set G) = yamadaY₂ d t := by
  obtain ⟨-, -, -, -, -, -, hFM, -⟩ := d.inclusions
  have hFY₂ : d.F ≤ centralizer (yamadaY₂ d t : Set G) :=
    hFM.trans (h.M_le_centralizer_yamadaY₂ d hK hD)
  refine le_antisymm (fun z hz => ?_) (le_inf le_sup_right ?_)
  · obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨φ, hφ, y, hy, rfl⟩ :=
      Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_F d hK hD) _ hz₁
    have hφZ : φ ∈ d.F ⊓ centralizer (d.F : Set G) := by
      refine ⟨hφ, mem_centralizer_iff.2 fun x hx => ?_⟩
      have h1 := mem_centralizer_iff.1 hz₂ x (mem_sup_left hx)
      have h2 : x * y = y * x := (mem_centralizer_iff.1 (hFY₂ hx) y hy).symm
      calc x * φ = x * (φ * y) * y⁻¹ := by group
        _ = φ * y * x * y⁻¹ := by rw [h1]
        _ = φ * (y * x) * y⁻¹ := by group
        _ = φ * (x * y) * y⁻¹ := by rw [h2]
        _ = φ * x := by group
    rw [(d.yamada_3_12_centers).2.2.2] at hφZ
    exact mul_mem (h.Y_le_yamadaY₂ d hK hD hφZ) hy
  · rw [← Subgroup.le_centralizer_iff]
    refine sup_le (fun y hy => mem_centralizer_iff.2 fun x hx => ?_) fun y hy =>
      mem_centralizer_iff.2 fun x hx => h.yamadaY₂_mul_comm d hK hD hx hy
    exact mem_centralizer_iff.1 (hFY₂ hy) x hx

theorem normalizer_yamadaR₂_le (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaE₂ d t : Set G) ∧
      normalizer (yamadaE₂ d t : Set G) ≤ normalizer (yamadaF₂ d t : Set G) ∧
      normalizer (yamadaF₂ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := by
  refine ⟨?_, ?_, ?_⟩
  · have := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (Subgroup.upperCentralSeries (yamadaR₂ d t) 3)
    rwa [(h.yamada_5_15_2 d hK hD).2.2] at this
  · have := normalizer_le_normalizer_thompsonSubgroup (yamadaE₂ d t)
    rwa [h.yamada_5_15_4 d hK hD] at this
  · have := normalizer_le_normalizer_center (yamadaF₂ d t)
    rwa [h.yamadaF₂_center d hK hD] at this

theorem t_mem_normalizer_yamadaF₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ normalizer (yamadaF₂ d t : Set G) ∧ t ∉ yamadaF₂ d t := by
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine ⟨mem_normalizer_sup (mem_normalizer_of_conj_mem fun x hx => ?_)
    (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂), fun ht =>
      h.t_not_mem_yamadaM₂ d hK hD ((h.yamadaE₂_le_yamadaL₂ d hK hD).1 ht)⟩
  rw [← mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hx)),
    mul_inv_cancel_right]
  exact hx

theorem exists_conj_t_eq_of_mem_normalizer_yamadaE₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hg : g ∈ normalizer (yamadaE₂ d t : Set G)) :
    ∃ x ∈ yamadaF₂ d t, g * t * g⁻¹ = t * x := by
  obtain ⟨htN, htF₂⟩ := h.t_mem_normalizer_yamadaF₂ d hK hD
  have htt := h.t_mul_t
  have hgF₂ := (h.normalizer_yamadaR₂_le d hK hD).2.1 hg
  have hgt : g * t * g⁻¹ ∈ yamadaF₂ d t ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  rcases (mem_sup_zpowers_iff_of htt htN).1 hgt with h1 | ⟨x, hx, e⟩
  · exfalso
    refine htF₂ ?_
    have := (mem_normalizer_iff.1 (inv_mem hgF₂) _).1 h1
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  · refine ⟨t * x * t, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 htN x).1 hx
      rwa [inv_eq_of_mul_eq_one_right htt] at this
    · rw [e, ← mul_assoc, ← mul_assoc, htt, one_mul]

theorem yamadaE₂_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaE₂ d t ⊓ centralizer ({t} : Set G) = d.F ⊔ zpowers t := by
  obtain ⟨-, hYX, -, hXF, -⟩ := d.inclusions
  have hFL : d.F ≤ L := d.image_le _
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le_sup_right le_sup_left _)
    (sup_le (hFL.trans h.L_le_centralizer) ((zpowers_le).2 (mem_centralizer_singleton_iff.2 rfl))))
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨htN, -⟩ := h.t_mem_normalizer_yamadaF₂ d hK hD
  obtain ⟨z, hz, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htN) x hx₁
  obtain ⟨φ, hφ, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_F d hK hD) z hz
  have hτt : τ ∈ centralizer ({t} : Set G) := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    exact zpow_mem (mem_centralizer_singleton_iff.2 rfl) k
  have hyt : y ∈ centralizer ({t} : Set G) := by
    have := mul_mem (mul_mem (inv_mem (h.L_le_centralizer (hFL hφ))) hx₂) (inv_mem hτt)
    rwa [show φ⁻¹ * (φ * y * τ) * τ⁻¹ = y by group] at this
  have hyY : y ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact ⟨hy, hyt⟩
  exact mul_mem (mem_sup_left (mul_mem hφ (hXF (hYX hyY)))) (mem_sup_right hτ)

theorem exists_mem_yamadaR₅star_conj_eq (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaF₂ d t) :
    ∃ g ∈ yamadaR₅star d t, ∃ y ∈ yamadaY₂ d t, g * t * g⁻¹ = t * x * y := by
  obtain ⟨φ, hφ, y, hy, rfl⟩ :=
    Common.exists_mul_of_le_normalizer (h.yamadaY₂_le_normalizer_F d hK hD) x hx
  have hφF₁ : φ ∈ yamadaF₁ d t := by
    rw [h.yamadaF₁_eq_sup d hK hD]
    exact mem_sup_left hφ
  obtain ⟨g, hg, u, hu, e⟩ := (h.yamada_5_21_1 d hK hD).2.2.2 φ hφF₁
  refine ⟨g, hg, y⁻¹ * u, mul_mem (inv_mem hy) (yamadaU₁_le_yamadaY₂ d t hu), ?_⟩
  rw [e]
  group

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaR₂ d t : Set G) ∧
      yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ≤
        normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
  have hNS₃ := (h.centralizer_inf_normalizer_S_le d hK hD).2.2
  have hNC : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := fun x hx =>
    h.centralizer_inf_normalizer_Y_le d (Subgroup.mem_inf.2 ⟨hx.1, hNS₃ hx⟩)
  refine ⟨fun x hx => mem_normalizer_sup (le_normalizer_yamadaL₂ d t (hNC hx)) hx.2,
    sup_le (sup_le (yamadaL₂_le d t) fun s hs => hNC (Subgroup.mem_inf.2
      ⟨h.L_le_centralizer (d.image_le _ hs), Subgroup.le_normalizer hs⟩)) hNC⟩

theorem centralizer_inf_normalizer_F_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.F : Set G) ≤ normalizer (d.S : Set G) ∧
      centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
        normalizer (d.W : Set G) ⊓ normalizer (d.X : Set G) := by
  obtain ⟨hX, hF, hS⟩ := d.yamada_3_13_1_G
  obtain ⟨hY, hW', -⟩ := d.yamada_3_13_3_G
  have hNS₃ := (h.centralizer_inf_normalizer_S_le d hK hD).2.2
  constructor
  · intro c hc
    obtain ⟨hct, hcF⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨g, hgL, hg⟩ :=
      h.exists_mem_L_inv_mul_mem_normalizer d hK (h.centralizer_le_normalizer hct)
    have hxF : g⁻¹ * c ∈ normalizer (d.F : Set G) :=
      hg (Model.F K) fun k => Model.map_entrywise_F _
    have hxS : g⁻¹ * c ∈ normalizer (d.S : Set G) :=
      hg (Model.S K) fun k => Model.map_entrywise_S _
    have hgF : g ∈ L ⊓ normalizer (d.F : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hgL, ?_⟩
      have := mul_mem hcF (inv_mem hxF)
      rwa [show c * (g⁻¹ * c)⁻¹ = g by group] at this
    rw [hF, ← hS] at hgF
    rw [show c = g * (g⁻¹ * c) by group]
    exact mul_mem (Subgroup.mem_inf.1 hgF).2 hxS
  · intro c hc
    obtain ⟨hct, hcS⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨g, hgL, hg⟩ :=
      h.exists_mem_L_inv_mul_mem_normalizer d hK (h.centralizer_le_normalizer hct)
    have hxW : g⁻¹ * c ∈ normalizer (d.W : Set G) :=
      hg (Model.W K) fun k => Model.map_entrywise_W _
    have hxX : g⁻¹ * c ∈ normalizer (d.X : Set G) :=
      hg (Model.X K) fun k => Model.map_entrywise_X _
    have hxS : g⁻¹ * c ∈ normalizer (d.S : Set G) :=
      hg (Model.S K) fun k => Model.map_entrywise_S _
    have hgS : g ∈ L ⊓ normalizer (d.S : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hgL, ?_⟩
      have := mul_mem hcS (inv_mem hxS)
      rwa [show c * (g⁻¹ * c)⁻¹ = g by group] at this
    have hgX : g ∈ L ⊓ normalizer (d.X : Set G) := by
      rw [hX, ← hS]
      exact hgS
    have hgW : g ∈ L ⊓ normalizer (d.W : Set G) := by
      rw [hW', ← hY]
      exact Subgroup.mem_inf.2 ⟨hgL, hNS₃ (Subgroup.mem_inf.2
        ⟨h.L_le_centralizer hgL, (Subgroup.mem_inf.1 hgS).2⟩)⟩
    rw [show c = g * (g⁻¹ * c) by group]
    exact Subgroup.mem_inf.2 ⟨mul_mem (Subgroup.mem_inf.1 hgW).2 hxW,
      mul_mem (Subgroup.mem_inf.1 hgX).2 hxX⟩

theorem exists_conj_t_eq_of_mem_normalizer_sup (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G}
    (hgY : g ∈ normalizer (yamadaY₂ d t : Set G))
    (hg : g ∈ normalizer ((yamadaY₂ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ y ∈ yamadaY₂ d t, g * t * g⁻¹ = t * y := by
  have htt := h.t_mul_t
  have htY₂ : t ∈ normalizer (yamadaY₂ d t : Set G) := h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD
    (h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t)))
  have hgt := (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  rcases (mem_sup_zpowers_iff_of htt htY₂).1 hgt with h1 | ⟨a, ha, e⟩
  · exfalso
    have := (mem_normalizer_iff.1 (inv_mem hgY) _).1 h1
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact h.t_not_mem_yamadaM₂ d hK hD ((le_sup_right : yamadaY₂ d t ≤ yamadaM₂ d t) this)
  · refine ⟨t * a * t, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 htY₂ a).1 ha
      rwa [inv_eq_of_mul_eq_one_right htt] at this
    · rw [e, ← mul_assoc, ← mul_assoc, htt, one_mul]

theorem mem_normalizer_yamadaR₂_conj_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} :
    (g ∈ normalizer (yamadaR₂ d t : Set G) ∧ ∃ y ∈ yamadaY₂ d t, g * t * g⁻¹ = t * y) ↔
      g ∈ yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) := by
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  obtain ⟨hNR₂, hRN⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  have h52 := h.yamada_5_17_2 hW d hK hD
  constructor
  · rintro ⟨hg, y, hy, e⟩
    have hgN : g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [← h52]
      refine mem_normalizer_sup_zpowers_of_conj_mem (hFY (hEF (hRE hg))) ?_
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hy)
    have hgN' : g ∈ ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) :
        Set G) := hgN
    rw [(h.yamada_5_5_1 d hK).2.2.1] at hgN'
    obtain ⟨l, hl, c, hc, rfl⟩ := Set.mem_mul.1 hgN'
    have hlR₂ : l ∈ yamadaR₂ d t := mem_sup_left hl
    have hcR₂ : c ∈ normalizer (yamadaR₂ d t : Set G) := by
      have := mul_mem (inv_mem (Subgroup.le_normalizer hlR₂)) hg
      rwa [inv_mul_cancel_left] at this
    obtain ⟨hct, -⟩ := Subgroup.mem_inf.1 hc
    have hcR : c ∈ normalizer ((d.S ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [← h.yamadaR_eq d, ← (h.yamadaR₂_inf_centralizer d hK).2]
      exact Common.mem_normalizer_inf hcR₂ (Subgroup.le_normalizer hct)
    exact mul_mem (mem_sup_left hlR₂) (mem_sup_right (Subgroup.mem_inf.2
      ⟨hct, h.mem_normalizer_of_mem_normalizer_sup_t (d.image_le _) hct hcR⟩))
  · intro hg
    have hgR₂ : g ∈ normalizer (yamadaR₂ d t : Set G) := (sup_le Subgroup.le_normalizer hNR₂) hg
    refine ⟨hgR₂, h.exists_conj_t_eq_of_mem_normalizer_sup d hK hD (hFY (hEF (hRE hgR₂))) ?_⟩
    rw [h52]
    exact hRN hg

theorem yamada_5_21_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    (∀ g ∈ normalizer (yamadaR₂ d t : Set G), ∃ x ∈ yamadaF₂ d t, g * t * g⁻¹ = t * x) ∧
    (∀ x ∈ yamadaF₂ d t, ∃ g ∈ normalizer (yamadaR₂ d t : Set G), ∃ y ∈ yamadaY₂ d t,
      g * t * g⁻¹ = t * x * y) ∧
    (∀ g : G, (g ∈ normalizer (yamadaR₂ d t : Set G) ∧
        ∃ y ∈ yamadaY₂ d t, g * t * g⁻¹ = t * y) ↔
      g ∈ yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G))) ∧
    normalizer (yamadaR₂ d t : Set G) ⊓
        normalizer ((yamadaY₂ d t ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ∧
    ((yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) : Subgroup G) :
        Set G) =
      (yamadaR₂ d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  obtain ⟨-, hRN⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  have hiff := fun g => h.mem_normalizer_yamadaR₂_conj_iff hW d hK hD (g := g)
  have h53 := h.yamada_5_17_3 hW d hK hD
  refine ⟨fun g hg => h.exists_conj_t_eq_of_mem_normalizer_yamadaE₂ d hK hD (hRE hg),
    fun x hx => ?_, hiff, le_antisymm (fun g hg => ?_) fun g hg => ?_,
    by rw [← h53.2.1]; exact h53.2.2⟩
  · obtain ⟨g, hg, y, hy, e⟩ := h.exists_mem_yamadaR₅star_conj_eq d hK hD hx
    exact ⟨g, h.yamadaR₅star_le_normalizer_yamadaR₂ hW d hK hD hg, y, hy, e⟩
  · obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
    exact (hiff g).1 ⟨hg₁, h.exists_conj_t_eq_of_mem_normalizer_sup d hK hD
      (hFY (hEF (hRE hg₁))) hg₂⟩
  · refine Subgroup.mem_inf.2 ⟨((hiff g).2 hg).1, ?_⟩
    rw [h.yamada_5_17_2 hW d hK hD]
    exact hRN hg

theorem yamada_5_21_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    normalizer (yamadaR₂ d t : Set G) = normalizer (yamadaE₂ d t : Set G) ∧
      normalizer (yamadaR₂ d t : Set G) ≤
        normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaX₂ d t : Set G) := by
  obtain ⟨-, hYX, hYW, hXF, hWF, hFD, -⟩ := d.inclusions
  have hR₅ := h.yamadaR₅star_le_normalizer_yamadaR₂ hW d hK hD
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  obtain ⟨hNR₂, -⟩ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₂ d hK hD
  have hred : ∀ g ∈ normalizer (yamadaE₂ d t : Set G), ∃ g₁ ∈ yamadaR₅star d t,
      g₁⁻¹ * g ∈ normalizer (yamadaY₂ d t : Set G) ∧
        ∃ y ∈ yamadaY₂ d t, g₁⁻¹ * g * t * (g₁⁻¹ * g)⁻¹ = t * y := by
    intro g hg
    obtain ⟨x, hx, e⟩ := h.exists_conj_t_eq_of_mem_normalizer_yamadaE₂ d hK hD hg
    obtain ⟨g₁, hg₁, y, hy, e₁⟩ := h.exists_mem_yamadaR₅star_conj_eq d hK hD hx
    have hg₁Y : g₁ ∈ normalizer (yamadaY₂ d t : Set G) := hFY (hEF (hRE (hR₅ hg₁)))
    refine ⟨g₁, hg₁, mul_mem (inv_mem hg₁Y) (hFY (hEF hg)), g₁⁻¹ * y⁻¹ * g₁, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem hg₁Y) y⁻¹).1 (inv_mem hy)
      rwa [inv_inv] at this
    · have e₂ : t * x = g₁ * t * g₁⁻¹ * y⁻¹ := by
        rw [e₁]
        group
      calc g₁⁻¹ * g * t * (g₁⁻¹ * g)⁻¹ = g₁⁻¹ * (g * t * g⁻¹) * g₁ := by group
        _ = g₁⁻¹ * (g₁ * t * g₁⁻¹ * y⁻¹) * g₁ := by rw [e, e₂]
        _ = t * (g₁⁻¹ * y⁻¹ * g₁) := by group
  have hNE : normalizer (yamadaE₂ d t : Set G) ≤ normalizer (yamadaR₂ d t : Set G) := by
    intro g hg
    obtain ⟨g₁, hg₁, hy₀Y, y, hy, e⟩ := hred g hg
    have hy₀E : g₁⁻¹ * g ∈ normalizer (yamadaE₂ d t : Set G) :=
      mul_mem (inv_mem (hRE (hR₅ hg₁))) hg
    have hy₀N : g₁⁻¹ * g ∈ ((normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G) :
        Subgroup G) : Set G) := by
      show g₁⁻¹ * g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) : Set G)
      rw [← h.yamada_5_17_2 hW d hK hD]
      refine mem_normalizer_sup_zpowers_of_conj_mem hy₀Y ?_
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hy)
    rw [(h.yamada_5_5_1 d hK).2.2.1] at hy₀N
    obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_mul.1 hy₀N
    obtain ⟨hct, -⟩ := Subgroup.mem_inf.1 hc
    have hlR₂ : l ∈ yamadaR₂ d t := mem_sup_left hl
    have hcE : c ∈ normalizer (yamadaE₂ d t : Set G) := by
      have := mul_mem (inv_mem (hRE (Subgroup.le_normalizer hlR₂))) hy₀E
      rwa [← hlc, inv_mul_cancel_left] at this
    have hcF : c ∈ normalizer ((d.F ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [← h.yamadaE₂_inf_centralizer d hK hD]
      exact Common.mem_normalizer_inf hcE (Subgroup.le_normalizer hct)
    have hcS := (h.centralizer_inf_normalizer_F_le d hK hD).1 (Subgroup.mem_inf.2
      ⟨hct, h.mem_normalizer_of_mem_normalizer_sup_t (d.image_le _) hct hcF⟩)
    have hy₀R : g₁⁻¹ * g ∈ normalizer (yamadaR₂ d t : Set G) := by
      rw [← hlc]
      exact mul_mem (Subgroup.le_normalizer hlR₂) (hNR₂ (Subgroup.mem_inf.2 ⟨hct, hcS⟩))
    have := mul_mem (hR₅ hg₁) hy₀R
    rwa [mul_inv_cancel_left] at this
  refine ⟨le_antisymm hRE hNE, fun g hg => ?_⟩
  have hU₁Y₂ := yamadaU₁_le_yamadaY₂ d t
  have hNY₂ : normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) :=
    hRE.trans (hEF.trans hFY)
  have hW₂ : yamadaW₂ d t = yamadaW₁ d t ⊔ yamadaY₂ d t := by
    rw [yamadaW₂, yamadaW₁, sup_assoc, sup_eq_right.2 hU₁Y₂]
  have hX₂ : yamadaX₂ d t = yamadaX₁ d t ⊔ yamadaY₂ d t := by
    rw [yamadaX₂, yamadaX₁, sup_assoc, sup_eq_right.2 hU₁Y₂]
  have hRW : yamadaRstar d t ⊓ normalizer (yamadaR₂ d t : Set G) ≤
      normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaX₂ d t : Set G) := fun x hx => by
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    rw [hW₂, hX₂]
    exact Subgroup.mem_inf.2 ⟨mem_normalizer_sup (h.yamadaRstar_le_normalizer_sup d hK hD hYW
      (hWF.trans hFD) (Or.inr hWF) hx₁) (hNY₂ hx₂), mem_normalizer_sup
        (h.yamadaRstar_le_normalizer_sup d hK hD hYX (hXF.trans hFD) (Or.inr hXF) hx₁)
        (hNY₂ hx₂)⟩
  have hCW : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaX₂ d t : Set G) := fun x hx => by
    obtain ⟨hxW, hxX⟩ := Subgroup.mem_inf.1 ((h.centralizer_inf_normalizer_F_le d hK hD).2 hx)
    have hxY₂ := hNY₂ (hNR₂ hx)
    exact Subgroup.mem_inf.2 ⟨mem_normalizer_sup hxW hxY₂, mem_normalizer_sup hxX hxY₂⟩
  obtain ⟨g₁, hg₁, -, y, hy, e⟩ := hred g (hRE hg)
  have hg₁R : g₁ ∈ normalizer (yamadaR₂ d t : Set G) := hR₅ hg₁
  have hy₀ := (h.mem_normalizer_yamadaR₂_conj_iff hW d hK hD).1
    ⟨mul_mem (inv_mem hg₁R) hg, y, hy, e⟩
  have h1 : g₁ ∈ normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaX₂ d t : Set G) :=
    hRW (Subgroup.mem_inf.2 ⟨((h.mem_yamadaR₅star_iff d hK hD).1 hg₁).1, hg₁R⟩)
  have h2 : g₁⁻¹ * g ∈ normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaX₂ d t : Set G) :=
    (sup_le (fun r hr => hRW (Subgroup.mem_inf.2 ⟨h.yamadaR₂_le_yamadaRstar d hK hD hr,
      Subgroup.le_normalizer hr⟩)) hCW) hy₀
  have := mul_mem h1 h2
  rwa [mul_inv_cancel_left] at this

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
