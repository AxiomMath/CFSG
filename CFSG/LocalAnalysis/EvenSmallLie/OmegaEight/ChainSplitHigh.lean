module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitRho
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitAbel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitFix
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitRep

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

theorem Coord4.conj_ψ_of_rep {B : Subgroup G} {ψ : V6 → G} {Φ : (Fin 6 → ZMod 4) → G}
    (hΦ : Coord4 B ψ Φ) {g : G} {F : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hF : Rep Φ g F)
    (u : V6) : g * ψ u * g⁻¹ = ψ (F.map red4 *ᵥ u) := by
  have h1 := hΦ.sq (liftV u)
  rw [red_liftV] at h1
  rw [← h1, show g * (Φ (liftV u) * Φ (liftV u)) * g⁻¹ =
    (g * Φ (liftV u) * g⁻¹) * (g * Φ (liftV u) * g⁻¹) by group, hF, hΦ.sq, map_red4_mulVec,
    red_liftV]

theorem card_fix_Q {Q : Subgroup G} {ψ : V6 → G} (hψi : Function.Injective ψ)
    (hψm : ∀ v, ψ v ∈ Q) (hmψ : ∀ x ∈ Q, ∃ v, ψ v = x) {g : G}
    {M : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hM : ∀ u, g * ψ u * g⁻¹ = ψ (M *ᵥ u)) :
    Nat.card (Q ⊓ centralizer ({g} : Set G) : Subgroup G) =
      (Finset.univ.filter fun v : V6 => M *ᵥ v = v).card := by
  have hmem : ∀ v : V6, M *ᵥ v = v → ψ v ∈ Q ⊓ centralizer ({g} : Set G) := by
    intro v hv
    refine ⟨hψm v, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hM v
    rw [hv] at h1
    calc ψ v * g = g * ψ v * g⁻¹ * g := by rw [h1]
      _ = g * ψ v := by group
  rw [← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun v => ⟨ψ v.1, hmem v.1 (Finset.mem_filter.1 v.2).2⟩) ⟨?_, ?_⟩)
  · intro v w h
    exact Subtype.ext (hψi (congrArg Subtype.val h))
  · rintro ⟨x, hxQ, hxc⟩
    obtain ⟨v, hv⟩ := hmψ x hxQ
    have hc := mem_centralizer_singleton_iff.1 hxc
    refine ⟨⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hψi ?_⟩⟩, Subtype.ext hv⟩
    rw [← hM, hv, ← hc, mul_inv_cancel_right]

theorem card_fix_B {B : Subgroup G} {ψ : V6 → G} {Φ : (Fin 6 → ZMod 4) → G}
    (hΦ : Coord4 B ψ Φ) {g : G} {F : Matrix (Fin 6) (Fin 6) (ZMod 4)} (hF : Rep Φ g F) :
    Nat.card (B ⊓ centralizer ({g} : Set G) : Subgroup G) =
      (Finset.univ.filter fun v : Fin 6 → ZMod 4 => F *ᵥ v = v).card := by
  have hmem : ∀ v, F *ᵥ v = v → Φ v ∈ B ⊓ centralizer ({g} : Set G) := by
    intro v hv
    refine ⟨hΦ.mem v, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hF v
    rw [hv] at h1
    calc Φ v * g = g * Φ v * g⁻¹ * g := by rw [h1]
      _ = g * Φ v := by group
  rw [← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun v => ⟨Φ v.1, hmem v.1 (Finset.mem_filter.1 v.2).2⟩) ⟨?_, ?_⟩)
  · intro v w h
    exact Subtype.ext (hΦ.injective (congrArg Subtype.val h))
  · rintro ⟨x, hxB, hxc⟩
    obtain ⟨v, hv⟩ := hΦ.surj x hxB
    have hc := mem_centralizer_singleton_iff.1 hxc
    refine ⟨⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hΦ.injective ?_⟩⟩, Subtype.ext hv⟩
    rw [← hF, hv, ← hc, mul_inv_cancel_right]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {k : ℕ} {A : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) k A)
include hS

omit hC in
theorem mem_Q_of_Urho {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀) {h : G} (hh : h ∈ U ⊔ zpowers ρ)
    (hc : ∀ q ∈ Q, h * q = q * h) : h ∈ Q := by
  have h1 : h ∈ Q ⊔ zpowers t := by
    rw [← hS.shape.centralizer_eq]
    exact ⟨mem_centralizer_singleton_iff.2 (hS.commute_of_mem_TH (hS.Urho_le_TH hρ hh)),
      mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩
  obtain ⟨q, hq, h2 | h2⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 h1
  · exact h2 ▸ hq
  · exfalso
    apply hS.t_not_mem_Urho hρ
    have := mul_mem (inv_mem (mem_sup_left (hS.rad.Q_le_U hq) : q ∈ U ⊔ zpowers ρ)) hh
    rwa [h2, ← mul_assoc, inv_mul_cancel, one_mul] at this

include hC

theorem false_of_terminal_highX [Finite G]
    (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hT : Terminal t (P ⊔ zpowers x₀) k A) (hk : 3 ≤ k) :
    False := by
  have hR := hS.rad
  have hQ := hR.card_Q
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => hR.Q_mul_self hq
  obtain ⟨Φ, hΦ, -, -, ρ, hρ, -, hrepU⟩ := hC.exists_coordB hS
  obtain ⟨g, -, b, hb, h, hh, hbh, hhQ, hh2⟩ := hC.exists_conj_decompX hS hρ hG hnab hT
  obtain ⟨i, hi, hhi⟩ := hrepU h hh
  have hB := hC.levelB hS
  have hact := hΦ.conj_ψ_of_rep hhi
  have hinvol : isInvol4 (tilGet ε i) = true := by
    simp only [isInvol4, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    constructor
    · apply red2_eq_id6
      have h1 : toMat4 (tilGet ε i) * toMat4 (tilGet ε i) = 1 :=
        hΦ.rep_unique (Coord4.rep_mul hhi hhi) (hΦ.rep_of_mem_A hB.comm (hB.Q_le hh2))
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
  obtain ⟨hc6, -⟩ := inv_facts ε hi hinvol
  have hcQ : Nat.card (Q ⊓ centralizer ({h} : Set G) : Subgroup G) =
      fix2c (red2 (tilGet ε i)) := by
    rw [card_fix_Q hR.ψ_inj hR.ψ_mem hR.mem_ψ (M := toMat 6 6 (red2 (tilGet ε i)))
      (fun u => by rw [toMat_red2]; exact hact u), card_fix2]
  have hcB : Nat.card (pw A (2 ^ (k - 2)) ⊓ centralizer ({h} : Set G) : Subgroup G) =
      fix4c (tilGet ε i) := by
    rw [card_fix_B hΦ hhi, card_fix4]
  have hhA : ∀ x ∈ A, h * x * h⁻¹ ∈ A := fun x hx =>
    (mem_normalizer_iff.1 (hC.Urho_le_normalizerX hS hρ hh) x).1 hx
  have hinvA : ∀ x ∈ A, h * (h * x * h⁻¹) * h⁻¹ = x := by
    intro x hx
    have hc := hC.level.comm _ (hC.level.Q_le hh2) x hx
    calc h * (h * x * h⁻¹) * h⁻¹ = (h * h) * x * (h * h)⁻¹ := by group
      _ = x := by rw [hc, mul_inv_cancel_right]
  have hstep := card_fix_step' hQ hQ2 hC.level hhA hinvA
  have hBle : pw A (2 ^ (k - 2)) ≤ pw A 2 := by
    have e : k - 2 = (k - 3) + 1 := by omega
    rw [e, pow_succ', ← pw_pw hC.level.comm]
    exact pw_le _ _
  have hmono := card_le_of_le (inf_le_inf_right (centralizer ({h} : Set G)) hBle)
  have hab : 2 * Nat.card (A ⊓ centralizer ({h} : Set G) : Subgroup G) ≤ 256 := by
    refine two_mul_card_le' (t := t) (g := g) (fun B hB hB2 hBc => hS.abelBound hB hB2 hBc)
      hS.shape.mul_self (hC.isPGroup_A.to_le inf_le_left)
      (fun x hx y hy => hC.level.comm x hx.1 y hy.1) ?_ ?_
    · intro d hd
      rw [hbh]
      have h1 := hC.level.comm d hd.1 b hb
      have h2 := mem_centralizer_singleton_iff.1 hd.2
      calc d * (b * h) = b * (d * h) := by rw [← mul_assoc, h1, mul_assoc]
        _ = b * h * d := by rw [h2, mul_assoc]
    · exact fun hu => hC.conj_not_mem_AX hS g hu.1
  rw [hcB] at hmono
  rw [hcQ] at hstep
  have h1 : Nat.card (A ⊓ centralizer ({h} : Set G) : Subgroup G) * fix2c (red2 (tilGet ε i)) ≤
      128 * fix2c (red2 (tilGet ε i)) := Nat.mul_le_mul_right _ (by omega)
  omega

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain
