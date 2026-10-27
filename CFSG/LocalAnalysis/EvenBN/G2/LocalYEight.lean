module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYSeven

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaW₂ (d : G2Data L K) (t : G) : Subgroup G :=
  d.W ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaX₂ (d : G2Data L K) (t : G) : Subgroup G :=
  d.X ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaF₂ (d : G2Data L K) (t : G) : Subgroup G :=
  d.F ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaD₂ (d : G2Data L K) (t : G) : Subgroup G :=
  d.D ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaV₂ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaW₂ d t ⊔ zpowers t

@[expose] noncomputable def yamadaU₂ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaX₂ d t ⊔ zpowers t

@[expose] noncomputable def yamadaE₂ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaF₂ d t ⊔ zpowers t

@[expose] noncomputable def yamadaC₂ (d : G2Data L K) (t : G) : Subgroup G :=
  yamadaD₂ d t ⊔ zpowers t

end Defs

section Generic

variable {G : Type*} [Group G]

theorem map_upperCentralSeries_succ {P Z Z' : Subgroup G} {n : ℕ}
    (hZ : (Subgroup.upperCentralSeries P n).map P.subtype = Z) (hZ'P : Z' ≤ P)
    (h : ∀ x ∈ P, x ∈ Z' ↔ ∀ g ∈ P, x * g * x⁻¹ * g⁻¹ ∈ Z) :
    (Subgroup.upperCentralSeries P (n + 1)).map P.subtype = Z' := by
  have hmem : ∀ y : P, y ∈ Subgroup.upperCentralSeries P n ↔ (y : G) ∈ Z := fun y => by
    rw [← hZ]
    exact (mem_map_iff_mem P.subtype_injective).symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_upperCentralSeries_succ_iff] at hy
    refine (h y y.2).2 fun g hg => ?_
    have := (hmem _).1 (hy ⟨g, hg⟩)
    simpa [commutatorElement_def] using this
  · intro hx
    refine ⟨⟨x, hZ'P hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_upperCentralSeries_succ_iff]
    intro g
    rw [hmem]
    simpa [commutatorElement_def] using (h x (hZ'P hx)).1 hx g g.2

theorem map_upperCentralSeries_zero (P : Subgroup G) :
    (Subgroup.upperCentralSeries P 0).map P.subtype = ⊥ := by
  rw [Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem map_upperCentralSeries_one (P : Subgroup G) :
    (Subgroup.upperCentralSeries P 1).map P.subtype = P ⊓ centralizer (P : Set G) := by
  refine map_upperCentralSeries_succ (map_upperCentralSeries_zero P) inf_le_left fun x hx => ?_
  constructor
  · rintro ⟨-, hc⟩ g hg
    rw [mem_bot, ← mem_centralizer_iff.1 hc g hg]
    group
  · intro h'
    refine ⟨hx, mem_centralizer_iff.2 fun g hg => ?_⟩
    have := h' g hg
    rw [mem_bot] at this
    calc g * x = (x * g * x⁻¹ * g⁻¹)⁻¹ * (x * g) := by group
      _ = x * g := by rw [this, inv_one, one_mul]

end Generic

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

variable
  [Finite K] [CharP K 2]

theorem mem_F_iff_commutator (hK : 4 ≤ Nat.card K) {s : G} (hs : s ∈ d.S) :
    s ∈ d.F ↔ ∀ s' ∈ d.S, ⁅s, s'⁆ ∈ d.Y := by
  obtain ⟨-, hY, hF⟩ := d.yamada_3_12_upperCentralSeries hK
  have h1 : s ∈ d.F ↔ (⟨s, hs⟩ : d.S) ∈ Subgroup.upperCentralSeries d.S 3 := by
    rw [← hF, ← mem_map_iff_mem d.S.subtype_injective]
    rfl
  rw [h1, show (3 : ℕ) = 2 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  constructor
  · intro h s' hs'
    have h2 := h ⟨s', hs'⟩
    rw [← mem_map_iff_mem d.S.subtype_injective, hY] at h2
    exact h2
  · intro h y
    rw [← mem_map_iff_mem d.S.subtype_injective, hY]
    exact h y y.2

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaR₂_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t ≤ normalizer (yamadaY₂ d t : Set G) :=
  sup_le (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD) (h.S_le_normalizer_yamadaY₂ d hK hD)

theorem yamadaR₂_le_normalizer_Y (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaR₂ d t ≤ normalizer (d.Y : Set G) := fun r hr =>
  mem_normalizer_of_conj_mem fun w hw => by
    have := mul_mem (d.inclusions.1 (h.conj_mul_inv_mem_U d hK hr hw)) hw
    rwa [inv_mul_cancel_right] at this

theorem yamadaY₂_le_yamadaR₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ≤ yamadaR₂ d t :=
  (h.yamadaY₂_le_yamadaL₂ d hK hD).trans le_sup_left

theorem yamadaY₁_le_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₁ d t ≤ yamadaY₂ d t :=
  sup_le (h.Y_le_yamadaY₂ d hK hD) (yamadaU₁_le_yamadaY₂ d t)

theorem yamadaY₁_le_yamadaR₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₁ d t ≤ yamadaR₁ d t := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  exact sup_le ((hYX.trans (hXF.trans (hFD.trans hDS))).trans le_sup_right)
    ((h.yamadaU₁_le_yamadaC₁ d hK hD).trans le_sup_left)

theorem yamadaY₁_inf_centralizer (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₁ d t ⊓ centralizer ({t} : Set G) = d.Y := by
  refine le_antisymm ?_ (le_inf le_sup_left ((d.image_le _).trans h.L_le_centralizer))
  rw [← h.yamadaY₂_inf_centralizer d hK hD]
  exact inf_le_inf_right _ (h.yamadaY₁_le_yamadaY₂ d hK hD)

theorem yamadaY₂_inf_yamadaR₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaY₂ d t ⊓ yamadaR₁ d t = yamadaY₁ d t := by
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  have hcY := h.cosetData_tY d hK
  have hV : ∀ {g : G}, g ∈ yamadaL₂ d t → g ∈ normalizer ((d.Y ⊔ zpowers t : Subgroup G) :
      Set G) ⊓ centralizer (d.Y : Set G) := fun hg => ⟨yamadaL₂_le d t hg, hL₂Y hg⟩
  refine le_antisymm (fun y hy => ?_)
    (le_inf (h.yamadaY₁_le_yamadaY₂ d hK hD) (h.yamadaY₁_le_yamadaR₁ d hK hD))
  obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.1 hy
  have hκ := (h.mem_yamadaR₁_iff d hK (h.yamadaY₂_le_yamadaR₂ d hK hD hy₁)).1 hy₂
  obtain ⟨u, hu, v, hv, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.map_wb_yamadaU₁_le_normalizer d hK hD) y hy₁
  have hvL₂ := h.map_wb_yamadaU₁_le_yamadaL₂ d hK hD hv
  have huL₂ := h.yamadaU₁_le_yamadaL₂ d hK hD hu
  obtain ⟨u', hu', rfl⟩ := hv
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hκ hvL₂ ⊢
  rw [hcY.crossed_mul_of_mem (hV huL₂) (hV hvL₂)] at hκ
  obtain ⟨h1, -⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu
  obtain ⟨h2, e2⟩ := h.crossed_mem_of_mem_yamadaU₁ d hK hD hu'
  rw [e2] at hκ
  have h3 : d.wb * (u'⁻¹ * t * u' * t) * d.wb⁻¹ ∈ d.U := by
    have := mul_mem (inv_mem h1) hκ
    rwa [inv_mul_cancel_left] at this
  have h4 := d.eq_one_of_wb_conj_mem_U h2 h3
  have hu'U := h.mem_U_of_crossed_eq_one d hK hD hu' h4
  obtain ⟨hUY, -⟩ := d.inclusions
  exact mul_mem (mem_sup_right hu) (mem_sup_left
    ((mem_normalizer_iff.1 d.wb_mem_normalizer.1.2 u').1 (hUY hu'U)))

theorem commutator_mem_yamadaY₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {r y : G} (hr : r ∈ yamadaR₁ d t) (hy : y ∈ yamadaY₂ d t) :
    r * y * r⁻¹ * y⁻¹ ∈ yamadaY₁ d t := by
  rw [← h.yamadaY₂_inf_yamadaR₁ d hK hD]
  have hrR₂ : r ∈ yamadaR₂ d t := (h.yamada_5_6_1 d hK).2.1 hr
  have hyR₂ := h.yamadaY₂_le_yamadaR₂ d hK hD hy
  refine Subgroup.mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1
    (h.yamadaR₂_le_normalizer_yamadaY₂ d hK hD hrR₂) y).1 hy) (inv_mem hy), ?_⟩
  rw [show r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) by group]
  exact mul_mem hr ((mem_normalizer_iff.1 ((h.yamada_5_6_1 d hK).2.2.1 hyR₂) r⁻¹).1 (inv_mem hr))

theorem yamadaR₂_eq_yamadaR₁_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaR₂ d t = yamadaR₁ d t ⊔ yamadaY₂ d t ∧
      yamadaR₁ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, -, hR₂, -, -⟩ := h.yamada_5_13_3 d hK hD
  have hSR₁ : d.S ≤ yamadaR₁ d t := le_sup_right
  have htR₁ : t ∈ yamadaR₁ d t := mem_sup_left (h.t_mem_yamadaC₁ d hK)
  refine ⟨le_antisymm ?_ (sup_le (h.yamada_5_6_1 d hK).2.1 (h.yamadaY₂_le_yamadaR₂ d hK hD)),
    ((h.yamada_5_6_1 d hK).2.1).trans (h.yamadaR₂_le_normalizer_yamadaY₂ d hK hD)⟩
  rw [hR₂]
  exact sup_le (sup_le (hSR₁.trans le_sup_left) le_sup_right)
    ((zpowers_le).2 (mem_sup_left htR₁))

theorem yamadaE₁_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaE₁ d t = d.F ⊔ yamadaU₁ d t ⊔ zpowers t := by
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨-, -, -, -, -, hFD, hFM, -⟩ := d.inclusions
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have hU₁L₂ := h.yamadaU₁_le_yamadaL₂ d hK hD
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have htC₁ := h.t_mem_yamadaC₁ d hK
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL₂, hxC₁⟩ := Subgroup.mem_inf.1 hx
    have htN : zpowers t ≤ normalizer (yamadaD₁ d t : Set G) :=
      (zpowers_le).2 (h.yamadaC₁_le_normalizer_yamadaD₁ d hK htC₁)
    rw [(h.yamada_5_8_1 d hK).2.1] at hxC₁
    obtain ⟨δ₁, hδ₁, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hxC₁
    rw [hD.D₁_eq] at hδ₁
    have hU₁N : yamadaU₁ d t ≤ normalizer (d.D : Set G) :=
      hU₁C₁.trans (h.yamadaC₁_le_normalizer_D d hK)
    obtain ⟨δ, hδ, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer hU₁N δ₁ hδ₁
    have hτL₂ : τ ∈ yamadaL₂ d t := (zpowers_le.2 htL₂) hτ
    have hδL₂ : δ ∈ yamadaL₂ d t := by
      have := mul_mem (mul_mem hxL₂ (inv_mem hτL₂)) (inv_mem (hU₁L₂ hu))
      rwa [show δ * u * τ * τ⁻¹ * u⁻¹ = δ by group] at this
    have hδF : δ ∈ d.F := by
      rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
      refine ⟨hδ, ?_⟩
      have hδtM : δ ∈ d.M ⊔ zpowers t := by
        rw [← hL₂t]
        exact ⟨hδL₂, h.L_le_centralizer (d.image_le _ hδ)⟩
      rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hδtM with h1 | h1
      · exact h1
      · exfalso
        refine h.t_not_mem_L ?_
        have := mul_mem (d.image_le _ h1) (inv_mem (d.image_le _ hδ))
        rwa [mul_inv_cancel_right] at this
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hδF)) (mem_sup_left (mem_sup_right hu)))
      (mem_sup_right hτ)
  · refine sup_le (sup_le (le_inf ((hFM.trans le_sup_left).trans (h.tM_le_yamadaL₂ d hK))
      ((hFD.trans le_sup_left).trans (h.tD_le_yamadaC₁ d hK))) (le_inf hU₁L₂ hU₁C₁))
      ((zpowers_le).2 ⟨htL₂, htC₁⟩)

theorem exists_decomp_yamadaR₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₁ d t) :
    ∃ s ∈ d.S, ∃ τ ∈ zpowers t, ∃ u ∈ yamadaU₁ d t, x = s * τ * u ∧
      ∀ g ∈ d.S, x * g * x⁻¹ * g⁻¹ = s * g * s⁻¹ * g⁻¹ := by
  obtain ⟨hR₁, hRN⟩ := h.yamadaR₁_eq_sup d hK hD
  rw [hR₁] at hx
  obtain ⟨r, hr, u, hu, rfl⟩ := Common.exists_mul_of_le_normalizer' hRN x hx
  have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
  obtain ⟨s, hs, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htS r hr
  refine ⟨s, hs, τ, hτ, u, hu, rfl, fun g hg => ?_⟩
  have hτg : τ * g = g * τ := (commute_of_mem_zpowers hτ (h.S_le_centralizer d hg)).symm
  have hug : u * g = g * u := mem_centralizer_iff.1 (h.S_le_centralizer_yamadaU₁ d hK hD hg) u hu
  calc s * τ * u * g * (s * τ * u)⁻¹ * g⁻¹ = s * τ * (u * g) * u⁻¹ * τ⁻¹ * s⁻¹ * g⁻¹ := by group
    _ = s * τ * (g * u) * u⁻¹ * τ⁻¹ * s⁻¹ * g⁻¹ := by rw [hug]
    _ = s * (τ * g) * τ⁻¹ * s⁻¹ * g⁻¹ := by group
    _ = s * (g * τ) * τ⁻¹ * s⁻¹ * g⁻¹ := by rw [hτg]
    _ = s * g * s⁻¹ * g⁻¹ := by group

theorem commutator_mem_of_mem_yamadaC₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {N : Subgroup G} (hUN : d.U ≤ N)
    (hN : yamadaC₁ d t ≤ normalizer (N : Set G)) {x : G} (hx : x ∈ yamadaC₁ d t)
    (hxS : ∀ s ∈ d.S, x * s * x⁻¹ * s⁻¹ ∈ N) {g : G} (hg : g ∈ yamadaR₁ d t) :
    x * g * x⁻¹ * g⁻¹ ∈ N := by
  have hEU := h.elemModulo_U_yamadaC₁ d hK
  have hSC₁ : d.S ≤ normalizer (yamadaC₁ d t : Set G) :=
    (le_sup_right : d.S ≤ yamadaR₁ d t).trans (h.yamadaR₁_le_normalizer d hK).1
  obtain ⟨c, hc, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSC₁ g hg
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ d.U := by
    have := (hEU x hx c hc).2
    rwa [commutatorElement_def] at this
  rw [show x * (c * s) * x⁻¹ * (c * s)⁻¹ =
    (x * c * x⁻¹ * c⁻¹) * (c * (x * s * x⁻¹ * s⁻¹) * c⁻¹) by group]
  exact mul_mem (hUN h1) ((mem_normalizer_iff.1 (hN hc) _).1 (hxS s hs))

theorem mem_tY₁_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₁ d t) :
    x ∈ yamadaY₁ d t ⊔ zpowers t ↔ ∀ g ∈ yamadaR₁ d t, x * g * x⁻¹ * g⁻¹ ∈ d.U := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hC₁U, -, -, -⟩ := h.two_core_C₁ d hK
  obtain ⟨-, hYX, -, hXF, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hYC₁ : d.Y ≤ yamadaC₁ d t :=
    (hYX.trans (hXF.trans hFD)).trans (le_sup_left.trans (h.tD_le_yamadaC₁ d hK))
  have hYR₁ : d.Y ≤ yamadaR₁ d t := hYC₁.trans le_sup_left
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have htC₁ := h.t_mem_yamadaC₁ d hK
  have hCN : yamadaC₁ d t ≤ normalizer (d.U : Set G) :=
    hC₁U.trans (Subgroup.centralizer_le_normalizer _)
  have hB : ∀ g ∈ yamadaR₁ d t, ∀ b ∈ d.U, g * b * g⁻¹ ∈ d.U := fun g hg b hb =>
    (mem_normalizer_iff.1 (((h.yamadaR₁_le_normalizer_tU d).trans
      (h.normalizer_tU_le_normalizer_U d hK)) hg) b).1 hb
  have key := fun {x : G} (hx : x ∈ yamadaC₁ d t) (hxS : ∀ s ∈ d.S, x * s * x⁻¹ * s⁻¹ ∈ d.U) =>
    fun g (hg : g ∈ yamadaR₁ d t) => h.commutator_mem_of_mem_yamadaC₁ d hK le_rfl hCN hx hxS hg
  have hone : ∀ {x : G}, (∀ s ∈ d.S, x * s = s * x) → ∀ s ∈ d.S, x * s * x⁻¹ * s⁻¹ ∈ d.U :=
    fun {x} hxS s hs => by
      rw [hxS s hs, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  constructor
  · intro hxZ
    set Z := Common.centralizerMod (yamadaR₁ d t) (yamadaR₁ d t) d.U
      (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hB with hZdef
    have hle : yamadaY₁ d t ⊔ zpowers t ≤ Z := by
      refine sup_le (sup_le (fun y hy => ⟨hYR₁ hy, key (hYC₁ hy) fun s hs => ?_⟩)
        (fun u hu => ⟨hU₁C₁.trans le_sup_left hu, key (hU₁C₁ hu) (hone fun s hs => ?_)⟩))
        ((zpowers_le).2 ⟨mem_sup_left htC₁, key htC₁ (hone fun s hs => ?_)⟩)
      · have := (d.mem_Y_iff_commutator hK4 (hYX.trans (hXF.trans (hFD.trans hDS)) hy)).1 hy s hs
        rwa [commutatorElement_def] at this
      · exact (mem_centralizer_iff.1 (h.S_le_centralizer_yamadaU₁ d hK hD hs) u hu)
      · exact (mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)).symm
    exact (hle hxZ).2
  · intro hc
    obtain ⟨s, hs, τ, hτ, u, hu, rfl, hcomm⟩ := h.exists_decomp_yamadaR₁ d hK hD hx
    have hsY : s ∈ d.Y := by
      rw [d.mem_Y_iff_commutator hK4 hs]
      intro g hg
      rw [commutatorElement_def, ← hcomm g hg]
      exact hc g ((le_sup_right : d.S ≤ yamadaR₁ d t) hg)
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hsY)) (mem_sup_right hτ))
      (mem_sup_left (mem_sup_right hu))

theorem zpowers_le_normalizer_yamadaY₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    zpowers t ≤ normalizer (yamadaY₁ d t : Set G) :=
  (zpowers_le).2 (mem_normalizer_sup (Subgroup.centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun _ hy => mem_centralizer_singleton_iff.1
      (h.L_le_centralizer (d.image_le _ hy))))
    (hD.yamadaC₁_le_normalizer hK (h.t_mem_yamadaC₁ d hK)))

theorem mem_Y_of_mem_tY₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {z : G} (hzS : z ∈ d.S) (hz : z ∈ yamadaY₁ d t ⊔ zpowers t) :
    z ∈ d.Y := by
  obtain ⟨y, hy, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.zpowers_le_normalizer_yamadaY₁ d hK hD) z hz
  have hτC : τ ∈ centralizer ({t} : Set G) := (zpowers_le.2 h.t_mem_centralizer) hτ
  have hyY : y ∈ d.Y := by
    rw [← h.yamadaY₁_inf_centralizer d hK hD]
    refine ⟨hy, ?_⟩
    have := mul_mem (h.S_le_centralizer d hzS) (inv_mem hτC)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases h.zpow_eq_one_or_eq k with hk | hk
  · rw [hk, mul_one]
    exact hyY
  · exfalso
    rw [hk] at hzS
    refine h.t_not_mem_L ?_
    have := mul_mem (inv_mem (d.image_le _ hyY)) (d.image_le _ hzS)
    rwa [inv_mul_cancel_left] at this

theorem commutator_mem_Y_of_mem_yamadaE₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x g : G} (hx : x ∈ yamadaE₁ d t)
    (hg : g ∈ yamadaR₁ d t) : x * g * x⁻¹ * g⁻¹ ∈ d.Y := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hUY, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hYN : yamadaC₁ d t ≤ normalizer (d.Y : Set G) :=
    (h.yamadaC₁_le_yamadaR₂ d hK).trans (h.yamadaR₂_le_normalizer_Y d hK)
  have hR₁N : yamadaR₁ d t ≤ normalizer (d.Y : Set G) :=
    ((h.yamada_5_6_1 d hK).2.1).trans (h.yamadaR₂_le_normalizer_Y d hK)
  have hB : ∀ g ∈ yamadaR₁ d t, ∀ b ∈ d.Y, g * b * g⁻¹ ∈ d.Y := fun g hg b hb =>
    (mem_normalizer_iff.1 (hR₁N hg) b).1 hb
  set Z := Common.centralizerMod (yamadaR₁ d t) (yamadaR₁ d t) d.Y
    (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hB with hZdef
  have hone : ∀ {x : G}, (∀ s ∈ d.S, x * s = s * x) → ∀ s ∈ d.S, x * s * x⁻¹ * s⁻¹ ∈ d.Y :=
    fun {x} hxS s hs => by
      rw [hxS s hs, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hFC₁ : d.F ≤ yamadaC₁ d t := (hFD.trans le_sup_left).trans (h.tD_le_yamadaC₁ d hK)
  have hU₁C₁ := h.yamadaU₁_le_yamadaC₁ d hK hD
  have htC₁ := h.t_mem_yamadaC₁ d hK
  have key := fun {x : G} (hx : x ∈ yamadaC₁ d t) (hxS : ∀ s ∈ d.S, x * s * x⁻¹ * s⁻¹ ∈ d.Y) =>
    fun g (hg : g ∈ yamadaR₁ d t) => h.commutator_mem_of_mem_yamadaC₁ d hK hUY hYN hx hxS hg
  have hle : yamadaE₁ d t ≤ Z := by
    rw [h.yamadaE₁_eq_sup d hK hD]
    refine sup_le (sup_le (fun y hy => ⟨mem_sup_left (hFC₁ hy), key (hFC₁ hy) fun s hs => ?_⟩)
      (fun u hu => ⟨mem_sup_left (hU₁C₁ hu), key (hU₁C₁ hu) (hone fun s hs => ?_)⟩))
      ((zpowers_le).2 ⟨mem_sup_left htC₁, key htC₁ (hone fun s hs => ?_)⟩)
    · have := (d.mem_F_iff_commutator hK4 ((hFD.trans hDS) hy)).1 hy s hs
      rwa [commutatorElement_def] at this
    · exact (mem_centralizer_iff.1 (h.S_le_centralizer_yamadaU₁ d hK hD hs) u hu)
    · exact (mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)).symm
  exact (hle hx).2 g hg

theorem mem_yamadaE₁_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₁ d t) :
    x ∈ yamadaE₁ d t ↔ ∀ g ∈ yamadaR₁ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₁ d t ⊔ zpowers t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  refine ⟨fun hxE g hg => mem_sup_left (mem_sup_left
    (h.commutator_mem_Y_of_mem_yamadaE₁ d hK hD hxE hg)), fun hc => ?_⟩
  obtain ⟨s, hs, τ, hτ, u, hu, rfl, hcomm⟩ := h.exists_decomp_yamadaR₁ d hK hD hx
  have hsF : s ∈ d.F := by
    rw [d.mem_F_iff_commutator hK4 hs]
    intro g hg
    rw [commutatorElement_def]
    refine h.mem_Y_of_mem_tY₁ d hK hD (mul_mem (mul_mem (mul_mem hs hg) (inv_mem hs))
      (inv_mem hg)) ?_
    rw [← hcomm g hg]
    exact hc g ((le_sup_right : d.S ≤ yamadaR₁ d t) hg)
  rw [h.yamadaE₁_eq_sup d hK hD]
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hsF)) (mem_sup_right hτ))
    (mem_sup_left (mem_sup_right hu))

theorem exists_mem_yamadaU₁_not_mem_U (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) : ∃ u ∈ yamadaU₁ d t, u ∉ d.U := by
  have h4K : 4 ≤ Nat.card K := hK ▸ h.four_le
  have hU₁U : ¬ yamadaU₁ d t ≤ d.U := by
    intro hle'
    have h1 := Subgroup.card_le_of_le hle'
    rw [(hD.yamada_5_10_1).2.2, d.cards.1] at h1
    have h2 : 1 < Nat.card K := by omega
    nlinarith
  exact Set.not_subset.1 hU₁U

theorem mem_yamadaY₁_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₂ d t) :
    x ∈ yamadaY₁ d t ↔ ∀ g ∈ yamadaR₂ d t, x * g * x⁻¹ * g⁻¹ ∈ d.U := by
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  have hcY := h.cosetData_tY d hK
  obtain ⟨hR₂, hR₁N⟩ := h.yamadaR₂_eq_yamadaR₁_sup d hK hD
  have hY₁R₁ := h.yamadaY₁_le_yamadaR₁ d hK hD
  have hY₁Y₂ := h.yamadaY₁_le_yamadaY₂ d hK hD
  have htR₂ : t ∈ yamadaR₂ d t := (h.yamada_5_6_1 d hK).2.1 (mem_sup_left (h.t_mem_yamadaC₁ d hK))
  constructor
  · intro hxY g hg
    rw [hR₂] at hg
    obtain ⟨r, hr, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hR₁N g hg
    have hxy : x * y = y * x := h.yamadaY₂_mul_comm d hK hD (hY₁Y₂ hxY) hy
    have hxr := (h.mem_tY₁_iff d hK hD (hY₁R₁ hxY)).1 (mem_sup_left hxY) r hr
    rw [show x * (r * y) * x⁻¹ * (r * y)⁻¹ = x * r * (y * x⁻¹) * y⁻¹ * r⁻¹ by group,
      show y * x⁻¹ = x⁻¹ * y by
        calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
          _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hxy]
          _ = x⁻¹ * y := by group,
      show x * r * (x⁻¹ * y) * y⁻¹ * r⁻¹ = x * r * x⁻¹ * r⁻¹ by group]
    exact hxr
  · intro hc
    have hxR₁ : x ∈ yamadaR₁ d t := by
      have h1 := hc t htR₂
      have h2 : x⁻¹ ∈ yamadaR₁ d t := by
        rw [h.mem_yamadaR₁_iff d hK (inv_mem hx), inv_inv]
        rwa [show t⁻¹ = t from inv_eq_of_mul_eq_one_right h.t_mul_t] at h1
      simpa using inv_mem h2
    have hxt := (h.mem_tY₁_iff d hK hD hxR₁).2 fun g hg => hc g ((h.yamada_5_6_1 d hK).2.1 hg)
    obtain ⟨y, hy, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer
      (h.zpowers_le_normalizer_yamadaY₁ d hK hD) x hxt
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk, mul_one]
      exact hy
    · exfalso
      rw [hk] at hc
      obtain ⟨hUY, -⟩ := d.inclusions
      obtain ⟨u, hu, huU⟩ := h.exists_mem_yamadaU₁_not_mem_U d hK hD
      set v := d.wb * u * d.wb⁻¹ with hvdef
      have hv : v ∈ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom := ⟨u, hu, rfl⟩
      have hvY₂ : v ∈ yamadaY₂ d t := mem_sup_right hv
      have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
      have htv : t * v * t⁻¹ ∈ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom :=
        (mem_normalizer_iff.1 (h.yamadaL₂_le_normalizer_map_wb d hK hD htL₂) v).1 hv
      have hyw : y * (t * v * t⁻¹) = (t * v * t⁻¹) * y :=
        h.yamadaY₂_mul_comm d hK hD (hY₁Y₂ hy) (mem_sup_right htv)
      have h1 := hc v (h.yamadaY₂_le_yamadaR₂ d hK hD hvY₂)
      have e : y * t * v * (y * t)⁻¹ * v⁻¹ = t * v * t⁻¹ * v⁻¹ := by
        calc y * t * v * (y * t)⁻¹ * v⁻¹ = (y * (t * v * t⁻¹)) * y⁻¹ * v⁻¹ := by group
          _ = ((t * v * t⁻¹) * y) * y⁻¹ * v⁻¹ := by rw [hyw]
          _ = t * v * t⁻¹ * v⁻¹ := by group
      rw [e] at h1
      have h2 : t * v * t⁻¹ * v⁻¹ ∈
          yamadaU₁ d t ⊓ (yamadaU₁ d t).map (MulAut.conj d.wb).toMonoidHom :=
        Subgroup.mem_inf.2 ⟨(hD.spec).2.1 h1, mul_mem htv (inv_mem hv)⟩
      rw [h.yamadaU₁_inf_map_wb d hK hD, mem_bot] at h2
      have hvC : v * t = t * v := by
        calc v * t = (t * v * t⁻¹ * v⁻¹)⁻¹ * (t * v) := by group
          _ = t * v := by rw [h2, inv_one, one_mul]
      have hwbt : d.wb * t = t * d.wb :=
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.wb_mem_normalizer.1.1)
      have hwbt' : d.wb⁻¹ * t = t * d.wb⁻¹ := by
        calc d.wb⁻¹ * t = d.wb⁻¹ * (t * d.wb) * d.wb⁻¹ := by group
          _ = d.wb⁻¹ * (d.wb * t) * d.wb⁻¹ := by rw [hwbt]
          _ = t * d.wb⁻¹ := by group
      apply huU
      rw [← hD.inf_centralizer]
      refine ⟨hu, mem_centralizer_singleton_iff.2 ?_⟩
      have hu' : u = d.wb⁻¹ * v * d.wb := by rw [hvdef]; group
      rw [hu']
      calc d.wb⁻¹ * v * d.wb * t = d.wb⁻¹ * v * (d.wb * t) := by group
        _ = d.wb⁻¹ * v * (t * d.wb) := by rw [hwbt]
        _ = d.wb⁻¹ * (v * t) * d.wb := by group
        _ = d.wb⁻¹ * (t * v) * d.wb := by rw [hvC]
        _ = (d.wb⁻¹ * t) * v * d.wb := by group
        _ = (t * d.wb⁻¹) * v * d.wb := by rw [hwbt']
        _ = t * (d.wb⁻¹ * v * d.wb) := by group

theorem yamadaR₂_le_normalizer_yamadaY₁ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₂ d t ≤ normalizer (yamadaY₁ d t : Set G) := fun r hr => by
  rw [← h.yamadaY₂_inf_yamadaR₁ d hK hD]
  exact Common.mem_normalizer_inf (h.yamadaR₂_le_normalizer_yamadaY₂ d hK hD hr)
    ((h.yamada_5_6_1 d hK).2.2.1 hr)

theorem yamadaR₂_eq_sup_yamadaY₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaR₂ d t = (d.S ⊔ zpowers t) ⊔ yamadaY₂ d t ∧
      d.S ⊔ zpowers t ≤ normalizer (yamadaY₂ d t : Set G) := by
  obtain ⟨-, -, hR₂, -, -⟩ := h.yamada_5_13_3 d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine ⟨?_, sup_le (h.S_le_normalizer_yamadaY₂ d hK hD)
    ((zpowers_le).2 (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂))⟩
  rw [hR₂]
  apply le_antisymm <;>
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left)

theorem mem_yamadaE₂_iff (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₂ d t) :
    x ∈ yamadaE₂ d t ↔ ∀ g ∈ yamadaR₂ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₁ d t := by
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  have hcY := h.cosetData_tY d hK
  obtain ⟨hR₂, hR₁N⟩ := h.yamadaR₂_eq_yamadaR₁_sup d hK hD
  have hY₁N := h.yamadaR₂_le_normalizer_yamadaY₁ d hK hD
  obtain ⟨hUY, -, -, -, -, hFD, hFM, hDS, -, -⟩ := d.inclusions
  have hY₁ : d.Y ≤ yamadaY₁ d t := le_sup_left
  have hR₁R₂ := (h.yamada_5_6_1 d hK).2.1
  have hMY₂ := h.M_le_centralizer_yamadaY₂ d hK hD
  have hSR₂ : d.S ≤ yamadaR₂ d t := le_sup_right
  have htC₁ := h.t_mem_yamadaC₁ d hK
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have key : ∀ {x : G}, (∀ r ∈ yamadaR₁ d t, x * r * x⁻¹ * r⁻¹ ∈ yamadaY₁ d t) →
      (∀ y ∈ yamadaY₂ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaY₁ d t) →
      ∀ g ∈ yamadaR₂ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₁ d t := by
    intro x h1 h2 g hg
    rw [hR₂] at hg
    obtain ⟨r, hr, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hR₁N g hg
    rw [show x * (r * y) * x⁻¹ * (r * y)⁻¹ =
      (x * r * x⁻¹ * r⁻¹) * (r * (x * y * x⁻¹ * y⁻¹) * r⁻¹) by group]
    exact mul_mem (h1 r hr) ((mem_normalizer_iff.1 (hY₁N (hR₁R₂ hr)) _).1 (h2 y hy))
  have hB : ∀ g ∈ yamadaR₂ d t, ∀ b ∈ yamadaY₁ d t, g * b * g⁻¹ ∈ yamadaY₁ d t :=
    fun g hg b hb => (mem_normalizer_iff.1 (hY₁N hg) b).1 hb
  have hone : ∀ {x y : G}, x * y = y * x → x * y * x⁻¹ * y⁻¹ ∈ yamadaY₁ d t := fun {x y} e => by
    rw [e, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hE : ∀ {x : G}, x ∈ yamadaE₂ d t →
      ∀ g ∈ yamadaR₂ d t, x * g * x⁻¹ * g⁻¹ ∈ yamadaY₁ d t := by
    set Z := Common.centralizerMod (yamadaR₂ d t) (yamadaR₂ d t) (yamadaY₁ d t)
      (fun g hg y hy => mul_mem (mul_mem hg hy) (inv_mem hg)) hB with hZdef
    have hle : yamadaE₂ d t ≤ Z := by
      refine sup_le (sup_le (fun f hf => ⟨hSR₂ ((hFD.trans hDS) hf), key (fun r hr => ?_)
        (fun y hy => ?_)⟩) (fun y hy => ⟨h.yamadaY₂_le_yamadaR₂ d hK hD hy,
          key (fun r hr => ?_) (fun y' hy' => ?_)⟩))
        ((zpowers_le).2 ⟨hR₁R₂ (mem_sup_left htC₁), key (fun r hr => ?_) (fun y hy => ?_)⟩)
      · refine hY₁ (h.commutator_mem_Y_of_mem_yamadaE₁ d hK hD ?_ hr)
        rw [h.yamadaE₁_eq_sup d hK hD]
        exact mem_sup_left (mem_sup_left hf)
      · exact hone (mem_centralizer_iff.1 (hMY₂ (hFM hf)) y hy).symm
      · have := h.commutator_mem_yamadaY₁ d hK hD hr hy
        rw [show y * r * y⁻¹ * r⁻¹ = (r * y * r⁻¹ * y⁻¹)⁻¹ by group]
        exact inv_mem this
      · exact hone (h.yamadaY₂_mul_comm d hK hD hy hy')
      · exact hY₁ (hUY ((h.mem_tY₁_iff d hK hD (mem_sup_left htC₁)).1
          (mem_sup_right (mem_zpowers t)) r hr))
      · have hyL₂ := h.yamadaY₂_le_yamadaL₂ d hK hD hy
        have hκ : y⁻¹⁻¹ * t * y⁻¹ * t ∈ d.Y := hcY.crossed_mem_of_mem
          ⟨yamadaL₂_le d t (inv_mem hyL₂), hL₂Y (inv_mem hyL₂)⟩
        have hc' := hcY.comm_of_mem hκ
        have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
        have e : t * y * t⁻¹ * y⁻¹ = y⁻¹⁻¹ * t * y⁻¹ * t := by
          calc t * y * t⁻¹ * y⁻¹ = t * (y⁻¹⁻¹ * t * y⁻¹ * t) * t⁻¹ := by
                conv_lhs => rw [ht']
                group
            _ = (y⁻¹⁻¹ * t * y⁻¹ * t) * t * t⁻¹ := by rw [hc']
            _ = y⁻¹⁻¹ * t * y⁻¹ * t := by group
        rw [e]
        exact hY₁ hκ
    intro x hx
    exact (hle hx).2
  refine ⟨fun hxE => hE hxE, fun hc => ?_⟩
  obtain ⟨hR₂', hRN⟩ := h.yamadaR₂_eq_sup_yamadaY₂ d hK hD
  rw [hR₂'] at hx
  obtain ⟨r, hr, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hRN x hx
  have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
  obtain ⟨s, hs, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htS r hr
  have hrR₂ : s * τ ∈ yamadaR₂ d t := by
    rw [h.yamadaR₂_eq_sup_yamadaY₂ d hK hD |>.1]
    exact mem_sup_left hr
  have hyE : y ∈ yamadaE₂ d t := mem_sup_left (mem_sup_right hy)
  have hsF : s ∈ d.F := by
    rw [d.mem_F_iff_commutator hK4 hs]
    intro g hg
    have hτg : τ * g = g * τ := (commute_of_mem_zpowers hτ (h.S_le_centralizer d hg)).symm
    have h1 := hc g (hSR₂ hg)
    have h2 := hE hyE g (hSR₂ hg)
    have h3 : s * τ * g * (s * τ)⁻¹ * g⁻¹ ∈ yamadaY₁ d t := by
      rw [show s * τ * g * (s * τ)⁻¹ * g⁻¹ = ((s * τ) * (y * g * y⁻¹ * g⁻¹) * (s * τ)⁻¹)⁻¹ *
        (s * τ * y * g * (s * τ * y)⁻¹ * g⁻¹) by group]
      exact mul_mem (inv_mem ((mem_normalizer_iff.1 (hY₁N hrR₂) _).1 h2)) h1
    have e : s * τ * g * (s * τ)⁻¹ * g⁻¹ = s * g * s⁻¹ * g⁻¹ := by
      calc s * τ * g * (s * τ)⁻¹ * g⁻¹ = s * (τ * g) * τ⁻¹ * s⁻¹ * g⁻¹ := by group
        _ = s * (g * τ) * τ⁻¹ * s⁻¹ * g⁻¹ := by rw [hτg]
        _ = s * g * s⁻¹ * g⁻¹ := by group
    rw [e] at h3
    rw [commutatorElement_def, ← h.yamadaY₁_inf_centralizer d hK hD]
    exact ⟨h3, h.S_le_centralizer d (mul_mem (mul_mem (mul_mem hs hg) (inv_mem hs))
      (inv_mem hg))⟩
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hsF)) (mem_sup_right hτ))
    (mem_sup_left (mem_sup_right hy))

theorem yamada_5_15_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    (Subgroup.upperCentralSeries (yamadaR₁ d t) 1).map (yamadaR₁ d t).subtype = d.U ∧
      (Subgroup.upperCentralSeries (yamadaR₁ d t) 2).map (yamadaR₁ d t).subtype =
        yamadaY₁ d t ⊔ zpowers t ∧
      (Subgroup.upperCentralSeries (yamadaR₁ d t) 3).map (yamadaR₁ d t).subtype =
        yamadaE₁ d t := by
  have h1 : (Subgroup.upperCentralSeries (yamadaR₁ d t) 1).map (yamadaR₁ d t).subtype = d.U := by
    rw [map_upperCentralSeries_one, (h.yamada_5_3_5 d hK).2]
  have h2 : (Subgroup.upperCentralSeries (yamadaR₁ d t) 2).map (yamadaR₁ d t).subtype =
      yamadaY₁ d t ⊔ zpowers t :=
    map_upperCentralSeries_succ h1 (sup_le (h.yamadaY₁_le_yamadaR₁ d hK hD)
      ((zpowers_le).2 (mem_sup_left (h.t_mem_yamadaC₁ d hK))))
      fun x hx => h.mem_tY₁_iff d hK hD hx
  exact ⟨h1, h2, map_upperCentralSeries_succ h2 (inf_le_right.trans le_sup_left)
    fun x hx => h.mem_yamadaE₁_iff d hK hD hx⟩

theorem yamada_5_15_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype = d.U ∧
      (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype =
        yamadaY₁ d t ∧
      (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
        yamadaE₂ d t := by
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hY₂R₂ := h.yamadaY₂_le_yamadaR₂ d hK hD
  have htR₂ : t ∈ yamadaR₂ d t :=
    (h.yamada_5_6_1 d hK).2.1 (mem_sup_left (h.t_mem_yamadaC₁ d hK))
  have h1 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype = d.U := by
    rw [map_upperCentralSeries_one, (h.yamada_5_5_4 d hK).2]
  have h2 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype =
      yamadaY₁ d t :=
    map_upperCentralSeries_succ h1 ((h.yamadaY₁_le_yamadaY₂ d hK hD).trans hY₂R₂)
      fun x hx => h.mem_yamadaY₁_iff d hK hD hx
  refine ⟨h1, h2, map_upperCentralSeries_succ h2 (sup_le (sup_le
    (((hFD.trans hDS).trans (le_sup_right : d.S ≤ yamadaR₂ d t))) hY₂R₂) ((zpowers_le).2 htR₂))
    fun x hx => h.mem_yamadaE₂_iff d hK hD hx⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
