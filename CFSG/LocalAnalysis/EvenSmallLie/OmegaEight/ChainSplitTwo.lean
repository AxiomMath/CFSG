module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitLevi
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitHigh
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitZ

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem card_THX {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G}
    {ψ : V6 → G} {p u : Fin 6 → G} {x₀ : G} [Finite G] (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) :
    Nat.card (U ⊔ zpowers x₀ ⊔ zpowers t : Subgroup G) = 16384 := by
  rw [hS.sp.card_sup hS.S₀_le_H₀, hS.inputs.card_S₀]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {W : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) 2 W) {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 W ψ Φ)
  (hrept : Rep Φ t (-1)) {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀)
  (hrepU : ∀ h ∈ U ⊔ zpowers ρ, ∃ i < 128, Rep Φ h (toMat4 (tilGet ε i)))
include hS hC hΦ hrept hρ hrepU

theorem exists_rep_TX [Finite G] {c : G} (hc : c ∈ W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) :
    ∃ j < 128, ∃ s : Bool,
      Rep Φ c (if s then -toMat4 (tilGet ε j) else toMat4 (tilGet ε j)) := by
  obtain ⟨w, hw, y, hy, hc'⟩ := exists_mul_of_mem_sup_normalizer (hC.TH_le_normalizerX hS) hc
  have hwr : Rep Φ w 1 := hΦ.rep_of_mem_A hC.level.comm hw
  obtain ⟨m, hm, hym | hym⟩ := hS.mem_TH_rho hρ hy
  · obtain ⟨j, hj, hmj⟩ := hrepU m hm
    refine ⟨j, hj, false, ?_⟩
    have := Coord4.rep_mul hwr hmj
    rwa [one_mul, ← hym, ← hc'] at this
  · obtain ⟨j, hj, hmj⟩ := hrepU m hm
    refine ⟨j, hj, true, ?_⟩
    have := Coord4.rep_mul hwr (Coord4.rep_mul hmj hrept)
    rwa [one_mul, mul_neg_one, ← hym, ← hc'] at this

omit hrepU in
theorem mem_W_of_repX [Finite G] {c : G} (hc : c ∈ W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t))
    (h1 : Rep Φ c 1) : c ∈ W := by
  have hR := hS.rad
  obtain ⟨w, hw, y, hy, hc'⟩ := exists_mul_of_mem_sup_normalizer (hC.TH_le_normalizerX hS) hc
  have hwr : Rep Φ w 1 := hΦ.rep_of_mem_A hC.level.comm hw
  have hy1 : Rep Φ y 1 := fun v => by
    have h2 := h1 v
    have h3 := hwr v
    rw [one_mulVec] at h2 h3 ⊢
    rw [hc'] at h2
    calc y * Φ v * y⁻¹ = w⁻¹ * (w * y * Φ v * (w * y)⁻¹) * w := by group
      _ = w⁻¹ * Φ v * w := by rw [h2]
      _ = Φ v := by
        calc w⁻¹ * Φ v * w = w⁻¹ * (w * Φ v * w⁻¹) * w := by rw [h3]
          _ = Φ v := by group
  have hQ : ∀ m ∈ U ⊔ zpowers ρ, Rep Φ m 1 → m ∈ Q := by
    intro m hm hm1
    refine mem_Q_of_Urho hS hρ hm fun q hq => ?_
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have := hΦ.conj_ψ_of_rep hm1 v
    rw [Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at this
    calc m * ψ v = m * ψ v * m⁻¹ * m := by group
      _ = ψ v * m := by rw [this]
  rw [hc']
  obtain ⟨m, hm, hym | hym⟩ := hS.mem_TH_rho hρ hy
  · rw [hym] at hy1 ⊢
    exact mul_mem hw (hC.level.Q_le (hQ m hm hy1))
  · exfalso
    rw [hym] at hy1 hy
    have hmtQ : m * t ∈ Q ⊔ zpowers t := by
      rw [← hS.shape.centralizer_eq]
      refine ⟨mem_centralizer_singleton_iff.2 (hS.commute_of_mem_TH hy),
        mem_centralizer_iff.2 fun q hq => ?_⟩
      obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
      have := hΦ.conj_ψ_of_rep hy1 v
      rw [Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at this
      calc ψ v * (m * t) = m * t * ψ v * (m * t)⁻¹ * (m * t) := by rw [this]
        _ = m * t * ψ v := by group
    obtain ⟨q, hq, h2 | h2⟩ := (hS.shape.mem_sup_iff hR.Q_le_L).1 hmtQ
    · apply hS.t_not_mem_Urho hρ
      have : t = m⁻¹ * q := by rw [← h2]; group
      rw [this]
      exact mul_mem (inv_mem hm) (mem_sup_left (hR.Q_le_U hq))
    · have hm' : m = q := mul_right_cancel h2
      have hmr : Rep Φ m 1 := hm' ▸ hΦ.rep_of_mem_A hC.level.comm (hC.level.Q_le hq)
      have ht1 : Rep Φ t 1 := fun v => by
        have h3 := hy1 v
        have h4 := hmr v
        rw [one_mulVec] at h3 h4 ⊢
        calc t * Φ v * t⁻¹ = m⁻¹ * (m * t * Φ v * (m * t)⁻¹) * m := by group
          _ = m⁻¹ * Φ v * m := by rw [h3]
          _ = Φ v := by
            calc m⁻¹ * Φ v * m = m⁻¹ * (m * Φ v * m⁻¹) * m := by rw [h4]
              _ = Φ v := by group
      have h5 := hΦ.rep_unique ht1 hrept
      have h6 := congrFun (congrFun h5 0) 0
      simp only [Matrix.one_apply_eq, Matrix.neg_apply] at h6
      exact absurd h6 (by decide)

omit hrept hρ hrepU in
theorem realizeX [Finite G]
    (hw : ∀ w, Rep Φ (wordElt p w) (prodW ε (c0Mat ε) w)) (hρX : Rep Φ ρ (toMat4 (xTil ε))) :
    ∀ j < 128, ∃ y ∈ U ⊔ zpowers ρ, Rep Φ y (toMat4 (tilGet ε j)) := by
  have hR := hS.rad
  have hlink := hS.inputs.link
  have hB : Level Q 2 W := hC.level
  have hPQ : ∀ x ∈ P, x ∈ centralizer (Q : Set G) → x ∈ Q := fun x hx hc =>
    hS.mem_Q_of_mem_P hx hc
  have hgen : ∀ g < 7, ∃ y ∈ U ⊔ zpowers ρ, Rep Φ y (toMat4 (tilGen ε g)) := by
    intro g hg
    by_cases hg6 : g < 6
    · refine ⟨u ⟨g, hg6⟩, mem_sup_left (hlink.u_mem _), ?_⟩
      have hkP := hR.U_le_P (hlink.u_mem ⟨g, hg6⟩)
      obtain ⟨hwk, -⟩ := (tab_facts ε).2.2.1 g hg6
      simp only [tilGen, hg6, ↓reduceIte, toMat4_prod4]
      refine rep_of_mem_P hR hPQ hB hΦ hw hkP fun v => ?_
      rw [(hR.lin_eq_iff (hR.P_le_normalizer hkP) _ _).2 (hlink.u_act ⟨g, hg6⟩ v), hwk]
      rw [urRows_eq_uRows]
    · refine ⟨ρ, mem_sup_right (mem_zpowers ρ), ?_⟩
      simp only [tilGen, hg6, ↓reduceIte]
      exact hρX
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst hj0
      exact ⟨1, one_mem _, by rw [(tab_facts ε).1, toMat4_one4]; exact Coord4.rep_one⟩
    · obtain ⟨i, hi, g, hg, hji⟩ := tree_facts ε hj hj0
      obtain ⟨y, hy, hyi⟩ := ih i hi (by omega)
      obtain ⟨z, hz, hzg⟩ := hgen g hg
      refine ⟨z * y, mul_mem hz hy, ?_⟩
      rw [hji, toMat4_mul4]
      exact Coord4.rep_mul hzg hyi

omit hrept hrepU in
theorem isInvol4_of_repX [Finite G] {h : G} (hh : h ∈ U ⊔ zpowers ρ) (hhQ : h ∉ Q)
    (hh2 : h * h ∈ Q) {i : ℕ} (hhi : Rep Φ h (toMat4 (tilGet ε i))) :
    isInvol4 (tilGet ε i) = true := by
  have hR := hS.rad
  have hact := hΦ.conj_ψ_of_rep hhi
  simp only [isInvol4, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor
  · apply red2_eq_id6
    have h1 : toMat4 (tilGet ε i) * toMat4 (tilGet ε i) = 1 :=
      hΦ.rep_unique (Coord4.rep_mul hhi hhi) (hΦ.rep_of_mem_A hC.level.comm (hC.level.Q_le hh2))
    rw [toMat4_mul4, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · by_contra hid
    apply hhQ
    refine mem_Q_of_Urho hS hρ hh fun q hq => ?_
    obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
    have := hact v
    rw [← toMat_red2, show red2 (tilGet ε i) = id6 by simpa using hid, toMat_id6,
      one_mulVec] at this
    calc h * ψ v = h * ψ v * h⁻¹ * h := by group
      _ = ψ v * h := by rw [this]

omit hΦ hrept hρ hrepU in
theorem card_centralizer_geX [Finite G] {g : G}
    (hodd : Odd ((W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)).relIndex (centralizer {g * t * g⁻¹}))) :
    16384 ≤ Nat.card ((W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) ⊓ centralizer {g * t * g⁻¹} :
      Subgroup G) := by
  set B : Subgroup G := (U ⊔ zpowers x₀ ⊔ zpowers t).map (MulAut.conj g).toMonoidHom
  have hBc : Nat.card B = 16384 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_THX hS]
  have hB2 : IsPGroup 2 B := hS.isPGroup_TH.map _
  have hBC : B ≤ centralizer {g * t * g⁻¹} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hyt := hS.commute_of_mem_TH hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hyt]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
  have := card_le_of_odd_relIndex (hC.isPGroup_TX hS) hB2 hBC hodd
  rwa [hBc] at this

omit hS hΦ hrept hρ hrepU in
theorem inf_centralizer_eqX {b h : G} (hb : b ∈ W) :
    ((W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) ⊓ centralizer {b * h}) ⊓ W =
      W ⊓ centralizer ({h} : Set G) := by
  ext w
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨-, hc⟩, hw⟩
    refine ⟨hw, ?_⟩
    have h1 := hC.level.comm w hw b hb
    have : b * (w * h) = b * (h * w) := by
      calc b * (w * h) = w * (b * h) := by rw [← mul_assoc, ← h1, mul_assoc]
        _ = b * h * w := hc
        _ = b * (h * w) := mul_assoc _ _ _
    exact mul_left_cancel this
  · rintro ⟨hw, hc⟩
    refine ⟨⟨mem_sup_left hw, ?_⟩, hw⟩
    have h1 := hC.level.comm w hw b hb
    calc w * (b * h) = b * (w * h) := by rw [← mul_assoc, h1, mul_assoc]
      _ = b * h * w := by rw [hc, mul_assoc]

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
