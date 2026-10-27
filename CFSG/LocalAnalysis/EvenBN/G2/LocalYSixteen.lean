module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFourteen
public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFifteen

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaR₃star (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaRstar d t ⊓ normalizer ((yamadaW₁ d t ⊔ zpowers t : Subgroup G) : Set G)

@[expose] noncomputable def yamadaR₄star (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaRstar d t ⊓ normalizer ((yamadaX₁ d t ⊔ zpowers t : Subgroup G) : Set G)

@[expose] noncomputable def yamadaR₅star (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaRstar d t ⊓ normalizer (yamadaE₁ d t : Set G)

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Light

theorem crossed_mul' (h : Setup G L f t) (g k : G) :
    t * (g * k) * t * (g * k)⁻¹ = t * g * t * g⁻¹ * (g * (t * k * t * k⁻¹) * g⁻¹) := by
  have htt := h.t_mul_t
  calc t * (g * k) * t * (g * k)⁻¹ = t * g * (t * t) * k * t * k⁻¹ * g⁻¹ := by
        rw [htt, mul_one]; group
    _ = _ := by group

theorem crossed_inv' (h : Setup G L f t) (g : G) :
    t * g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * (t * g * t * g⁻¹)⁻¹ * g := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  calc t * g⁻¹ * t * g⁻¹⁻¹ = t⁻¹ * g⁻¹ * t⁻¹ * g := by rw [htinv, inv_inv]
    _ = _ := by group

theorem conj_t_eq_mul_crossed (h : Setup G L f t) (g : G) :
    g * t * g⁻¹ = t * (t * g * t * g⁻¹) := by
  have htt := h.t_mul_t
  rw [show t * (t * g * t * g⁻¹) = (t * t) * g * t * g⁻¹ by group, htt, one_mul]

theorem crossed_conj' (h : Setup G L f t) (g x : G) :
    t * (g * x * g⁻¹) * t * (g * x * g⁻¹)⁻¹ =
      t * g * t * g⁻¹ * (g * (t * x * t * x⁻¹) * g⁻¹) *
        (g * x * g⁻¹ * (t * g * t * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  calc t * (g * x * g⁻¹) * t * (g * x * g⁻¹)⁻¹ =
      t * g * x * g⁻¹ * t⁻¹ * g * x⁻¹ * g⁻¹ := by rw [htinv]; group
    _ = t * g * t * g⁻¹ * (g * (t⁻¹ * x * t * x⁻¹) * g⁻¹) *
        (g * x * g⁻¹ * (t * g * t * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹) := by group
    _ = _ := by rw [htinv]

end Light

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem yamadaRstar_le_normalizer (h : Setup G L f t) (d : G2Data L K) :
    yamadaRstar d t ≤ normalizer (yamadaC₁ d t : Set G) := by
  refine sup_le (LieType.BorelTits.pCoreOf_le 2 _) fun s hs => le_normalizer_yamadaC₁ d t
    (h.centralizer_inf_normalizer_U_le d ⟨h.L_le_centralizer (d.image_le _ hs),
      mem_normalizer_of_conj_mem fun u hu => ?_⟩)
  have hu' : u ∈ d.S ⊓ centralizer (d.S : Set G) := by
    rw [(d.yamada_3_12_centers).1]
    exact hu
  rw [mem_centralizer_iff.1 hu'.2 s hs, mul_inv_cancel_right]
  exact hu

theorem yamadaCstar_le_normalizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {H : Subgroup G} (hU₁H : yamadaU₁ d t ≤ H)
    (hHD₁ : H ≤ yamadaD₁ d t) : yamadaCstar d t ≤ normalizer (H : Set G) := by
  rw [h.yamadaCstar_eq d hK hD]
  intro c hc
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have := ((h.mem_yamadaV d hK hD).1 hc).2 x (hHD₁ hx)
  rw [show c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x by group]
  exact mul_mem (hU₁H this) hx

theorem S_le_normalizer_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {Q : Subgroup G} (hYQ : d.Y ≤ Q) (hQD : Q ≤ d.D)
    (hQ : d.F ≤ Q ∨ Q ≤ d.F) : d.S ≤ normalizer ((Q ⊔ yamadaU₁ d t : Subgroup G) : Set G) := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, -, -, hXF, hWF, hFD, -, hDS, -⟩ := d.inclusions
  intro s hs
  refine mem_normalizer_sup (mem_normalizer_of_conj_mem fun x hx => ?_)
    (h.S_le_normalizer_yamadaU₁ d hK hD hs)
  have hcomm : s * x * s⁻¹ * x⁻¹ ∈ Q := by
    rcases hQ with hFQ | hQF
    · have : s * x * s⁻¹ * x⁻¹ ∈ ⁅d.S, d.S⁆ := commutator_mem_commutator hs (hDS (hQD hx))
      rw [(d.yamada_3_12_commutators (by omega)).2.2.1] at this
      exact hFQ this
    · have := ((d.mem_F_iff_commutator (by omega) (hDS (hFD (hQF hx)))).1 (hQF hx) s hs)
      have h1 : s * x * s⁻¹ * x⁻¹ = ⁅x, s⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact hYQ (inv_mem this)
  rw [show s * x * s⁻¹ = s * x * s⁻¹ * x⁻¹ * x by group]
  exact mul_mem hcomm hx

theorem yamadaRstar_le_normalizer_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {Q : Subgroup G} (hYQ : d.Y ≤ Q) (hQD : Q ≤ d.D)
    (hQ : d.F ≤ Q ∨ Q ≤ d.F) :
    yamadaRstar d t ≤ normalizer ((Q ⊔ yamadaU₁ d t : Subgroup G) : Set G) := by
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  exact sup_le (h.yamadaCstar_le_normalizer d hK hD le_sup_right
    (sup_le (hQD.trans hDD₁) (hD.spec).1)) (h.S_le_normalizer_sup d hK hD hYQ hQD hQ)

omit [Finite K] in
theorem S_le_normalizer_yamadaCstar (h : Setup G L f t) (d : G2Data L K) :
    d.S ≤ normalizer (yamadaCstar d t : Set G) :=
  (le_sup_right.trans (h.yamadaRstar_le_normalizer d)).trans
    (LieType.BorelTits.le_normalizer_pCoreOf 2 _)

omit [Finite K] in
theorem yamadaU₁_le_normalizer_of_le_D (h : Setup G L f t) (d : G2Data L K)
    (_hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {Q : Subgroup G} (hQD : Q ≤ d.D) :
    yamadaU₁ d t ≤ normalizer (Q : Set G) :=
  le_normalizer_of_conj_mem fun u hu x hx => by
    rw [mem_centralizer_iff.1 (hD.D_le_centralizer (hQD hx)) u hu,
      mul_inv_cancel_right]
    exact hx

theorem commutator_mem_of_mem_yamadaRstar (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} (hg : g ∈ yamadaRstar d t) :
    (∀ δ ∈ yamadaD₁ d t, g * δ * g⁻¹ * δ⁻¹ ∈ d.F ⊔ yamadaU₁ d t) ∧
      ∀ x ∈ d.F ⊔ yamadaU₁ d t, g * x * g⁻¹ * x⁻¹ ∈ yamadaY₁ d t := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -⟩ := d.inclusions
  have hCV := h.yamadaCstar_eq d hK hD
  obtain ⟨hU₁D₁, -, -⟩ := hD.spec
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hSU₁ := h.S_le_centralizer_yamadaU₁ d hK hD
  obtain ⟨c, hc, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaCstar d) g hg
  have hcV := ((h.mem_yamadaV d hK hD).1 (hCV ▸ hc)).2
  have e : ∀ x : G, c * s * x * (c * s)⁻¹ * x⁻¹ =
      c * (s * x * s⁻¹ * x⁻¹) * c⁻¹ * (c * x * c⁻¹ * x⁻¹) := fun x => by group
  have hsc : ∀ {a b : G}, b ∈ yamadaU₁ d t → s * (a * b) * s⁻¹ * (a * b)⁻¹ =
      s * a * s⁻¹ * a⁻¹ := fun {a b} hb => by
    have hsb : s * b = b * s := (mem_centralizer_iff.1 (hSU₁ hs) b hb).symm
    have hsb' : b * s⁻¹ = s⁻¹ * b := by
      calc b * s⁻¹ = s⁻¹ * (s * b) * s⁻¹ := by group
        _ = s⁻¹ * b := by rw [hsb]; group
    calc s * (a * b) * s⁻¹ * (a * b)⁻¹ = s * a * (b * s⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = s * a * (s⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hsb']
      _ = s * a * s⁻¹ * a⁻¹ := by group
  refine ⟨fun δ hδ => ?_, fun x hx => ?_⟩
  · rw [e]
    refine mul_mem ?_ (mem_sup_right (hcV δ hδ))
    refine (mem_normalizer_iff.1 (h.yamadaCstar_le_normalizer d hK hD le_sup_right
      (sup_le (hFD.trans hDD₁) hU₁D₁) hc) _).1 ?_
    rw [hD.D₁_eq] at hδ
    obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaU₁_le_normalizer_of_le_D d hK hD le_rfl) δ hδ
    rw [hsc hb]
    have : s * a * s⁻¹ * a⁻¹ ∈ ⁅d.S, d.S⁆ := commutator_mem_commutator hs (hDS ha)
    rw [(d.yamada_3_12_commutators (by omega)).2.2.1] at this
    exact mem_sup_left this
  · rw [e]
    refine mul_mem ?_ (mem_sup_right (hcV x ((sup_le (hFD.trans hDD₁) hU₁D₁) hx)))
    refine (mem_normalizer_iff.1 (h.yamadaCstar_le_normalizer d hK hD le_sup_right
      (sup_le ((d.inclusions.2.1.trans (d.inclusions.2.2.2.1.trans hFD)).trans hDD₁) hU₁D₁)
        hc) _).1 ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.yamadaU₁_le_normalizer_of_le_D d hK hD hFD) x hx
    rw [hsc hb]
    have := (d.mem_F_iff_commutator (by omega) (hDS (hFD ha))).1 ha s hs
    have h1 : s * a * s⁻¹ * a⁻¹ = ⁅a, s⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact mem_sup_left (inv_mem this)

theorem t_mem_yamadaRstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : t ∈ yamadaRstar d t :=
  mem_sup_left ((h.yamadaCstar_eq d hK hD) ▸ h.yamadaC₁_le_yamadaV d hK hD (h.t_mem_yamadaC₁ d hK))

theorem mem_yamadaRstar_inf_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {H : Subgroup G} (hHD₁ : H ≤ yamadaD₁ d t)
    (hRH : yamadaRstar d t ≤ normalizer (H : Set G)) {g : G} :
    g ∈ yamadaRstar d t ⊓ normalizer ((H ⊔ zpowers t : Subgroup G) : Set G) ↔
      g ∈ yamadaRstar d t ∧ t * g * t * g⁻¹ ∈ H := by
  have htt := h.t_mul_t
  have htH : t ∈ normalizer (H : Set G) := hRH (h.t_mem_yamadaRstar d hK hD)
  constructor
  · rintro ⟨hgR, hgN⟩
    refine ⟨hgR, ?_⟩
    have hgt : g * t * g⁻¹ ∈ H ⊔ zpowers t :=
      (mem_normalizer_iff.1 hgN t).1 (mem_sup_right (mem_zpowers t))
    rcases (mem_sup_zpowers_iff_of htt htH).1 hgt with h1 | ⟨x, hx, e⟩
    · exfalso
      refine h.t_not_mem_yamadaD₁ d hK ?_
      have hgD₁ := (h.normalizer_yamadaC₁_le d hK hD).1 (h.yamadaRstar_le_normalizer d hgR)
      have := (mem_normalizer_iff.1 (inv_mem hgD₁) _).1 (hHD₁ h1)
      rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      rw [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group, e]
      have := (mem_normalizer_iff.1 htH x).1 hx
      rw [htinv, mul_assoc] at this
      exact this
  · rintro ⟨hgR, hκ⟩
    refine ⟨hgR, mem_normalizer_of_conj_mem fun x hx => ?_⟩
    obtain ⟨y, hy, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer ((zpowers_le).2 htH) x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rw [show g * (y * t ^ k) * g⁻¹ = g * y * g⁻¹ * (g * t * g⁻¹) ^ k by rw [conj_zpow]; group,
      h.conj_t_eq_mul_crossed g]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 (hRH hgR) y).1 hy))
      (zpow_mem (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)) k)

theorem mem_yamadaR₃star_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {g : G} :
    g ∈ yamadaR₃star d t ↔ g ∈ yamadaRstar d t ∧ t * g * t * g⁻¹ ∈ yamadaW₁ d t := by
  obtain ⟨-, -, hYW, -, hWF, hFD, -⟩ := d.inclusions
  exact h.mem_yamadaRstar_inf_iff d hK hD
    (sup_le ((hWF.trans hFD).trans le_sup_right) (hD.spec).1)
    (h.yamadaRstar_le_normalizer_sup d hK hD hYW (hWF.trans hFD) (Or.inr hWF))

theorem mem_yamadaR₄star_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {g : G} :
    g ∈ yamadaR₄star d t ↔ g ∈ yamadaRstar d t ∧ t * g * t * g⁻¹ ∈ yamadaX₁ d t := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  exact h.mem_yamadaRstar_inf_iff d hK hD
    (sup_le ((hXF.trans hFD).trans le_sup_right) (hD.spec).1)
    (h.yamadaRstar_le_normalizer_sup d hK hD hYX (hXF.trans hFD) (Or.inr hXF))

theorem mem_yamadaR₅star_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {g : G} :
    g ∈ yamadaR₅star d t ↔ g ∈ yamadaRstar d t ∧ t * g * t * g⁻¹ ∈ d.F ⊔ yamadaU₁ d t := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have := h.mem_yamadaRstar_inf_iff d hK hD
    (sup_le (hFD.trans le_sup_right) (hD.spec).1)
    (h.yamadaRstar_le_normalizer_sup d hK hD (hYX.trans hXF) hFD (Or.inl le_rfl)) (g := g)
  rwa [← h.yamadaE₁_eq_sup d hK hD] at this

theorem yamadaRstar_inf_centralizer_le (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaRstar d t ⊓ centralizer ({t} : Set G) ≤ yamadaR₁ d t := by
  intro x hx
  obtain ⟨hxR, hxt⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨c, hc, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaCstar d) x hxR
  have hct : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem hxt (inv_mem (h.L_le_centralizer (d.image_le _ hs)))
    rwa [mul_inv_cancel_right] at this
  have hcR : c ∈ yamadaRstar d t := mem_sup_left hc
  have hcN : c ∈ yamadaRstar d t ⊓
      normalizer ((yamadaU₁ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    refine (h.mem_yamadaRstar_inf_iff d hK hD (hD.spec).1 ?_).2 ⟨hcR, ?_⟩
    · exact fun g hg => (h.normalizer_yamadaC₁_le d hK hD).2
        ((h.normalizer_yamadaC₁_le d hK hD).1 (h.yamadaRstar_le_normalizer d hg))
    · rw [show t * c * t * c⁻¹ = t * (c * t) * c⁻¹ by group,
        mem_centralizer_singleton_iff.1 hct, show t * (t * c) * c⁻¹ = t * t by group,
        h.t_mul_t]
      exact one_mem _
  have hcC₁ : c ∈ yamadaC₁ d t := by
    rw [← (h.yamada_5_19 d hK hD).1.2.2]
    refine ⟨hc, ?_⟩
    rw [← h.yamada_5_17_1 d hK hD]
    exact hcN.2
  exact mul_mem (mem_sup_left hcC₁) (mem_sup_right hs)

omit [Finite K] in
theorem yamadaW₁_inf_yamadaX₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaW₁ d t ⊓ yamadaX₁ d t = yamadaY₁ d t := by
  obtain ⟨-, hYX, hYW, hXF, hWF, hFD, -⟩ := d.inclusions
  obtain ⟨-, -, hU₁D⟩ := hD.spec
  refine le_antisymm (fun z hz => ?_) (le_inf (sup_le_sup_right hYW _) (sup_le_sup_right hYX _))
  obtain ⟨hzW, hzX⟩ := Subgroup.mem_inf.1 hz
  obtain ⟨w, hw, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaU₁_le_normalizer_of_le_D d hK hD (hWF.trans hFD)) _ hzW
  obtain ⟨x, hx, u', hu', e⟩ := Common.exists_mul_of_le_normalizer
    (h.yamadaU₁_le_normalizer_of_le_D d hK hD (hXF.trans hFD)) _ hzX
  have h1 : x⁻¹ * w ∈ d.U := by
    rw [← hU₁D]
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (inv_mem (hFD (hXF hx))) (hFD (hWF hw))⟩
    rw [show x⁻¹ * w = u' * u⁻¹ by
      calc x⁻¹ * w = x⁻¹ * (w * u) * u⁻¹ := by group
        _ = x⁻¹ * (x * u') * u⁻¹ := by rw [e]
        _ = u' * u⁻¹ := by group]
    exact mul_mem hu' (inv_mem hu)
  have hwX : w ∈ d.X := by
    rw [show w = x * (x⁻¹ * w) by group]
    exact mul_mem hx (hYX (d.inclusions.1 h1))
  have hwY : w ∈ d.Y := by
    rw [← (d.yamada_defs).2.2.2.2.2.2.1]
    exact ⟨hwX, hw⟩
  exact mul_mem (mem_sup_left hwY) (mem_sup_right hu)

theorem yamadaR₂_le_yamadaRstar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaR₂ d t ≤ yamadaRstar d t := by
  obtain ⟨hR₂, -⟩ := h.yamadaR₂_eq_yamadaR₁_sup d hK hD
  obtain ⟨hC₂, -⟩ := h.yamadaC₂_eq_sup d hK hD
  have hC₂C : yamadaC₂ d t ≤ yamadaCstar d t := by
    rw [(h.yamada_5_19 d hK hD).2.2.2.2.1]
    exact inf_le_left
  rw [hR₂, hC₂] at *
  refine sup_le (sup_le ((le_sup_left.trans hC₂C).trans le_sup_left) le_sup_right) ?_
  rw [hC₂] at hC₂C
  exact (le_sup_right.trans hC₂C).trans le_sup_left

theorem mem_yamadaR₂_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} :
    g ∈ yamadaR₂ d t ↔ g ∈ yamadaRstar d t ∧ t * g * t * g⁻¹ ∈ yamadaY₁ d t := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have hiff := h.mem_yamadaRstar_inf_iff d hK hD (H := yamadaY₁ d t)
    (sup_le ((hYX.trans (hXF.trans hFD)).trans le_sup_right) (hD.spec).1)
    (h.yamadaRstar_le_normalizer_sup d hK hD le_rfl (hYX.trans (hXF.trans hFD))
      (Or.inr (hYX.trans hXF))) (g := g)
  obtain ⟨-, h2, h3⟩ := h.yamada_5_17_3 hW d hK hD
  rw [← hiff]
  constructor
  · intro hg
    exact ⟨h.yamadaR₂_le_yamadaRstar d hK hD hg, by rw [h2]; exact mem_sup_left hg⟩
  · rintro ⟨hgR, hgN⟩
    have hg' : g ∈ ((normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) :
        Subgroup G) : Set G) := hgN
    rw [h3] at hg'
    obtain ⟨r, hr, n, hn, rfl⟩ := Set.mem_mul.1 hg'
    have hnR : n ∈ yamadaRstar d t := by
      have := mul_mem (inv_mem (h.yamadaR₂_le_yamadaRstar d hK hD hr)) hgR
      rwa [inv_mul_cancel_left] at this
    have hnR₁ := h.yamadaRstar_inf_centralizer_le d hK hD ⟨hnR, hn.1⟩
    exact mul_mem hr ((h.yamada_5_6_1 d hK).2.1 hnR₁)

theorem exists_mem_yamadaCstar_conj (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {H : Subgroup G} (hU₁H : yamadaU₁ d t ≤ H) (hHD₁ : H ≤ yamadaD₁ d t)
    {w : G} (hw : w ∈ H) :
    ∃ x ∈ yamadaRstar d t, t * x * t * x⁻¹ ∈ H ∧ ∃ u ∈ yamadaU₁ d t, x * t * x⁻¹ = t * w * u := by
  obtain ⟨x, hx, u, hu, e⟩ := (h.yamada_5_19 d hK hD).2.1.2 w (hHD₁ hw)
  refine ⟨x, mem_sup_left hx, ?_, u, hu, e⟩
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e,
    show t * (t * w * u) = (t * t) * w * u by group, h.t_mul_t, one_mul]
  exact mul_mem hw (hU₁H hu)

theorem yamada_5_21_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ((∀ g ∈ yamadaR₃star d t, ∃ w ∈ yamadaW₁ d t, g * t * g⁻¹ = t * w) ∧
      ∀ w ∈ yamadaW₁ d t, ∃ g ∈ yamadaR₃star d t, ∃ u ∈ yamadaU₁ d t,
        g * t * g⁻¹ = t * w * u) ∧
    ((∀ g ∈ yamadaR₄star d t, ∃ x ∈ yamadaX₁ d t, g * t * g⁻¹ = t * x) ∧
      ∀ x ∈ yamadaX₁ d t, ∃ g ∈ yamadaR₄star d t, ∃ u ∈ yamadaU₁ d t,
        g * t * g⁻¹ = t * x * u) ∧
    ((∀ g ∈ yamadaR₅star d t, ∃ x ∈ yamadaF₁ d t, g * t * g⁻¹ = t * x) ∧
      ∀ x ∈ yamadaF₁ d t, ∃ g ∈ yamadaR₅star d t, ∃ u ∈ yamadaU₁ d t,
        g * t * g⁻¹ = t * x * u) := by
  obtain ⟨-, hYX, hYW, hXF, hWF, hFD, -⟩ := d.inclusions
  obtain ⟨hU₁D₁, -, -⟩ := hD.spec
  have hDD₁ : d.D ≤ yamadaD₁ d t := le_sup_right
  have hF₁ := h.yamadaF₁_eq_sup d hK hD
  refine ⟨⟨fun g hg => ⟨_, ((h.mem_yamadaR₃star_iff d hK hD).1 hg).2,
      h.conj_t_eq_mul_crossed g⟩, fun w hw => ?_⟩,
    ⟨fun g hg => ⟨_, ((h.mem_yamadaR₄star_iff d hK hD).1 hg).2,
      h.conj_t_eq_mul_crossed g⟩, fun w hw => ?_⟩,
    ⟨fun g hg => ⟨_, hF₁ ▸ ((h.mem_yamadaR₅star_iff d hK hD).1 hg).2,
      h.conj_t_eq_mul_crossed g⟩, fun w hw => ?_⟩⟩
  · obtain ⟨x, hx, hκ, u, hu, e⟩ := h.exists_mem_yamadaCstar_conj d hK hD le_sup_right
      (sup_le ((hWF.trans hFD).trans hDD₁) hU₁D₁) hw
    exact ⟨x, (h.mem_yamadaR₃star_iff d hK hD).2 ⟨hx, hκ⟩, u, hu, e⟩
  · obtain ⟨x, hx, hκ, u, hu, e⟩ := h.exists_mem_yamadaCstar_conj d hK hD le_sup_right
      (sup_le ((hXF.trans hFD).trans hDD₁) hU₁D₁) hw
    exact ⟨x, (h.mem_yamadaR₄star_iff d hK hD).2 ⟨hx, hκ⟩, u, hu, e⟩
  · rw [hF₁] at hw
    obtain ⟨x, hx, hκ, u, hu, e⟩ := h.exists_mem_yamadaCstar_conj d hK hD le_sup_right
      (sup_le (hFD.trans hDD₁) hU₁D₁) hw
    exact ⟨x, (h.mem_yamadaR₅star_iff d hK hD).2 ⟨hx, hκ⟩, u, hu, e⟩

theorem yamadaR₅star_le_normalizer_yamadaR₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₅star d t ≤ normalizer (yamadaR₂ d t : Set G) := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  intro c hc
  obtain ⟨hcR, hcκ⟩ := (h.mem_yamadaR₅star_iff d hK hD).1 hc
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxR, hxκ⟩ := (h.mem_yamadaR₂_iff hW d hK hD).1 hx
  have hgR : c * x * c⁻¹ ∈ yamadaRstar d t := mul_mem (mul_mem hcR hxR) (inv_mem hcR)
  refine (h.mem_yamadaR₂_iff hW d hK hD).2 ⟨hgR, ?_⟩
  rw [h.crossed_conj' c x]
  have hY₁N := h.yamadaRstar_le_normalizer_sup d hK hD le_rfl (hYX.trans (hXF.trans hFD))
    (Or.inr (hYX.trans hXF))
  have h1 : c * (t * x * t * x⁻¹) * c⁻¹ ∈ yamadaY₁ d t :=
    (mem_normalizer_iff.1 (hY₁N hcR) _).1 hxκ
  set κc := t * c * t * c⁻¹ with hκc
  have h2 : (c * x * c⁻¹) * κc⁻¹ * (c * x * c⁻¹)⁻¹ * κc ∈ yamadaY₁ d t :=
    ((h.commutator_mem_of_mem_yamadaRstar d hK hD hgR).2 _ (inv_mem hcκ))
      |> fun h3 => by rwa [inv_inv] at h3
  have hκD₁ : κc ∈ yamadaD₁ d t :=
    h.crossed_mem_yamadaD₁ d hK hD (h.yamadaRstar_le_normalizer d hcR)
  have hC₁R : yamadaC₁ d t ≤ yamadaRstar d t :=
    ((h.yamadaCstar_eq d hK hD) ▸ h.yamadaC₁_le_yamadaV d hK hD).trans le_sup_left
  have hD₁Y₁ : yamadaD₁ d t ≤ normalizer (yamadaY₁ d t : Set G) := fun δ hδ =>
    hY₁N (hC₁R (h.yamadaD₁_le_yamadaC₁ d hK hδ))
  rw [show κc * (c * (t * x * t * x⁻¹) * c⁻¹) * (c * x * c⁻¹ * κc⁻¹ * (c * x * c⁻¹)⁻¹) =
    κc * (c * (t * x * t * x⁻¹) * c⁻¹ * (c * x * c⁻¹ * κc⁻¹ * (c * x * c⁻¹)⁻¹ * κc)) * κc⁻¹ by
      group]
  exact (mem_normalizer_iff.1 (hD₁Y₁ hκD₁) _).1 (mul_mem h1 h2)

theorem yamadaRstar_le_normalizer_yamadaR₅star (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaRstar d t ≤ normalizer (yamadaR₅star d t : Set G) := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have hF₁N := h.yamadaRstar_le_normalizer_sup d hK hD (hYX.trans hXF) hFD (Or.inl le_rfl)
  have hC₁R : yamadaC₁ d t ≤ yamadaRstar d t :=
    ((h.yamadaCstar_eq d hK hD) ▸ h.yamadaC₁_le_yamadaV d hK hD).trans le_sup_left
  intro g hg
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxR, hxκ⟩ := (h.mem_yamadaR₅star_iff d hK hD).1 hx
  have hgxR : g * x * g⁻¹ ∈ yamadaRstar d t := mul_mem (mul_mem hg hxR) (inv_mem hg)
  refine (h.mem_yamadaR₅star_iff d hK hD).2 ⟨hgxR, ?_⟩
  rw [h.crossed_conj' g x]
  set κg := t * g * t * g⁻¹ with hκg
  have hκD₁ : κg ∈ yamadaD₁ d t :=
    h.crossed_mem_yamadaD₁ d hK hD (h.yamadaRstar_le_normalizer d hg)
  have h1 : g * (t * x * t * x⁻¹) * g⁻¹ ∈ d.F ⊔ yamadaU₁ d t :=
    (mem_normalizer_iff.1 (hF₁N hg) _).1 hxκ
  have h2 : (g * x * g⁻¹) * κg⁻¹ * (g * x * g⁻¹)⁻¹ * κg ∈ d.F ⊔ yamadaU₁ d t := by
    have := (h.commutator_mem_of_mem_yamadaRstar d hK hD hgxR).1 _ (inv_mem hκD₁)
    rwa [inv_inv] at this
  rw [show κg * (g * (t * x * t * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * κg⁻¹ * (g * x * g⁻¹)⁻¹) =
    κg * (g * (t * x * t * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * κg⁻¹ * (g * x * g⁻¹)⁻¹ * κg)) * κg⁻¹ by
      group]
  exact (mem_normalizer_iff.1 (hF₁N (hC₁R (h.yamadaD₁_le_yamadaC₁ d hK hκD₁))) _).1
    (mul_mem h1 h2)

theorem exists_mul_of_mem_yamadaR₅star (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {g : G} (hg : g ∈ yamadaR₅star d t) :
    ∃ c ∈ yamadaR₃star d t, ∃ y ∈ yamadaR₄star d t, g = c * y := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨-, hYX, hYW, hXF, hWF, hFD, -, hDS, -⟩ := d.inclusions
  obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₅star_iff d hK hD).1 hg
  have hWX : d.X ≤ normalizer (d.W : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun w hw => by
      have := (d.mem_F_iff_commutator (by omega) (hDS (hFD (hWF hw)))).1 (hWF hw) x
        (hDS (hFD (hXF hx)))
      have h1 : x * w * x⁻¹ = ⁅w, x⁆⁻¹ * w := by
        rw [commutatorElement_def]
        group
      rw [h1]
      exact mul_mem (hYW (inv_mem this)) hw
  have hU₁F := h.yamadaU₁_le_normalizer_of_le_D d hK hD hFD
  obtain ⟨φ, hφ, u, hu, hκe⟩ := Common.exists_mul_of_le_normalizer hU₁F _ hgκ
  rw [← (d.yamada_defs).2.2.2.1, sup_comm] at hφ
  obtain ⟨w, hw, x, hx, rfl⟩ := Common.exists_mul_of_le_normalizer hWX φ hφ
  obtain ⟨-, h1⟩ := (h.yamada_5_21_1 d hK hD).1
  obtain ⟨c, hc, u', hu', hce⟩ := h1 w (mem_sup_left hw)
  have hcR := ((h.mem_yamadaR₃star_iff d hK hD).1 hc).1
  refine ⟨c, hc, c⁻¹ * g, (h.mem_yamadaR₄star_iff d hK hD).2 ⟨mul_mem (inv_mem hcR) hgR, ?_⟩,
    by group⟩
  have hX₁N := h.yamadaRstar_le_normalizer_sup d hK hD hYX (hXF.trans hFD) (Or.inr hXF)
  have hκc : t * c * t * c⁻¹ = w * u' := by
    rw [show t * c * t * c⁻¹ = t * (c * t * c⁻¹) by group, hce,
      show t * (t * w * u') = (t * t) * w * u' by group, h.t_mul_t, one_mul]
  rw [h.crossed_mul' c⁻¹ g, h.crossed_inv' c, hκc, hκe,
    show c⁻¹ * (w * u')⁻¹ * c * (c⁻¹ * (w * x * u) * c⁻¹⁻¹) =
      c⁻¹ * (u'⁻¹ * (x * u)) * c⁻¹⁻¹ by group]
  exact (mem_normalizer_iff.1 (hX₁N (inv_mem hcR)) _).1
    (mul_mem (mem_sup_right (inv_mem hu')) (mul_mem (mem_sup_left hx) (mem_sup_right hu)))

theorem yamada_5_21_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t = yamadaR₃star d t ⊓ yamadaR₄star d t ∧ yamadaR₂ d t ≤ yamadaR₅star d t ∧
      yamadaR₅star d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      yamadaR₅star d t = yamadaR₃star d t ⊔ yamadaR₄star d t ∧
      (yamadaR₅star d t : Set G) = (yamadaR₃star d t : Set G) * (yamadaR₄star d t : Set G) ∧
      yamadaRstar d t ≤ normalizer (yamadaR₅star d t : Set G) := by
  obtain ⟨-, hYX, hYW, hXF, hWF, -⟩ := d.inclusions
  have hF₁W : yamadaW₁ d t ≤ d.F ⊔ yamadaU₁ d t := sup_le_sup_right hWF _
  have hF₁X : yamadaX₁ d t ≤ d.F ⊔ yamadaU₁ d t := sup_le_sup_right hXF _
  have hR₃R₅ : yamadaR₃star d t ≤ yamadaR₅star d t := fun g hg => by
    obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₃star_iff d hK hD).1 hg
    exact (h.mem_yamadaR₅star_iff d hK hD).2 ⟨hgR, hF₁W hgκ⟩
  have hR₄R₅ : yamadaR₄star d t ≤ yamadaR₅star d t := fun g hg => by
    obtain ⟨hgR, hgκ⟩ := (h.mem_yamadaR₄star_iff d hK hD).1 hg
    exact (h.mem_yamadaR₅star_iff d hK hD).2 ⟨hgR, hF₁X hgκ⟩
  have hR₂ : yamadaR₂ d t = yamadaR₃star d t ⊓ yamadaR₄star d t := by
    ext g
    rw [Subgroup.mem_inf, h.mem_yamadaR₂_iff hW d hK hD, h.mem_yamadaR₃star_iff d hK hD,
      h.mem_yamadaR₄star_iff d hK hD, ← h.yamadaW₁_inf_yamadaX₁ d hK hD]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2.1⟩, h1, h2.2⟩, fun ⟨⟨h1, h2⟩, _, h3⟩ => ⟨h1, h2, h3⟩⟩
  have hset : (yamadaR₅star d t : Set G) =
      (yamadaR₃star d t : Set G) * (yamadaR₄star d t : Set G) := by
    ext g
    constructor
    · intro hg
      obtain ⟨c, hc, y, hy, rfl⟩ := h.exists_mul_of_mem_yamadaR₅star d hK hD hg
      exact Set.mem_mul.2 ⟨c, hc, y, hy, rfl⟩
    · intro hg
      obtain ⟨c, hc, y, hy, rfl⟩ := Set.mem_mul.1 hg
      exact mul_mem (hR₃R₅ hc) (hR₄R₅ hy)
  refine ⟨hR₂, hR₂ ▸ inf_le_left.trans hR₃R₅, h.yamadaR₅star_le_normalizer_yamadaR₂ hW d hK hD,
    le_antisymm (fun g hg => ?_) (sup_le hR₃R₅ hR₄R₅), hset,
    h.yamadaRstar_le_normalizer_yamadaR₅star d hK hD⟩
  obtain ⟨c, hc, y, hy, rfl⟩ := h.exists_mul_of_mem_yamadaR₅star d hK hD hg
  exact mul_mem (mem_sup_left hc) (mem_sup_right hy)

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
