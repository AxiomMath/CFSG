module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InCount
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_singer {U W Z D : Subgroup G} {e : ℕ} (he : 2 ≤ e)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU2 : ∀ a ∈ U, a ^ 2 = 1)
    (hWU : W ≤ U) (hZW : Z ≤ W)
    (hDW : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W)
    (hDZ : ∀ d ∈ D, ∀ z ∈ Z, d * z = z * d)
    (hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hfpf : ∀ d ∈ D, d ≠ 1 → ∀ u ∈ U, d * u * d⁻¹ * u⁻¹ ∈ Z → u ∈ Z)
    (hDcard : Nat.card D = 2 ^ e - 1) (hWZ : Z.relIndex W = 2 ^ e) :
    ⁅W, D⁆ ≤ W ∧ (∀ a ∈ ⁅W, D⁆, ∀ b ∈ ⁅W, D⁆, a * b = b * a) ∧ (∀ a ∈ ⁅W, D⁆, a ^ 2 = 1) ∧
      Nat.card (⁅W, D⁆ : Subgroup G) = 2 ^ e ∧ ⁅W, D⁆ ⊓ Z = ⊥ ∧
      ActsRegularlyOn D (nonIdentity ⁅W, D⁆) := by
  classical
  have hW_comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => hUc a (hWU ha) b (hWU hb)
  have h2pos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have : 4 ≤ 2 ^ e :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  obtain ⟨δ, hδ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  obtain ⟨d₀, hd₀D, hd₀1⟩ : ∃ d₀ : G, d₀ ∈ D ∧ d₀ ≠ 1 :=
    ⟨(δ : G), δ.2, fun h => hδ (Subtype.ext h)⟩
  have hcomm_mem : ∀ w ∈ W, ⁅w, d₀⁆ ∈ W := by
    intro w hw
    have e : ⁅w, d₀⁆ = w * (d₀ * w⁻¹ * d₀⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hw (hDW d₀ hd₀D w⁻¹ (W.inv_mem hw))
  have hmul : ∀ w w' : W, ⁅((w * w' : W) : G), d₀⁆ = ⁅(w : G), d₀⁆ * ⁅(w' : G), d₀⁆ := by
    intro w w'
    have e1 : ⁅((w * w' : W) : G), d₀⁆ =
        (w : G) * ⁅(w' : G), d₀⁆ * (w : G)⁻¹ * ⁅(w : G), d₀⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul]; group
    rw [e1]
    have hcw : (w : G) * ⁅(w' : G), d₀⁆ = ⁅(w' : G), d₀⁆ * (w : G) :=
      hW_comm _ w.2 _ (hcomm_mem _ w'.2)
    have hcc : ⁅(w' : G), d₀⁆ * ⁅(w : G), d₀⁆ = ⁅(w : G), d₀⁆ * ⁅(w' : G), d₀⁆ :=
      hW_comm _ (hcomm_mem _ w'.2) _ (hcomm_mem _ w.2)
    calc (w : G) * ⁅(w' : G), d₀⁆ * (w : G)⁻¹ * ⁅(w : G), d₀⁆
        = ⁅(w' : G), d₀⁆ * ⁅(w : G), d₀⁆ := by rw [hcw]; group
      _ = ⁅(w : G), d₀⁆ * ⁅(w' : G), d₀⁆ := hcc
  let φ : ↥W →* G := MonoidHom.mk' (fun w : ↥W => ⁅(w : G), d₀⁆) hmul
  have hφ : ∀ w : ↥W, φ w = ⁅(w : G), d₀⁆ := fun _ => rfl
  have hker : φ.ker = Z.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ]
    constructor
    · intro h1
      have h2 : (w : G) * d₀ = d₀ * (w : G) := commutatorElement_eq_one_iff_mul_comm.1 h1
      have hc : d₀ * (w : G) * d₀⁻¹ * (w : G)⁻¹ = 1 := by rw [← h2]; group
      exact hfpf d₀ hd₀D hd₀1 w (hWU w.2) (hc ▸ Z.one_mem)
    · intro hz
      exact commutatorElement_eq_one_iff_mul_comm.2 (hDZ d₀ hd₀D w hz).symm
  have hcardW : Nat.card W = 2 ^ e * Nat.card Z := by
    have := Subgroup.relIndex_mul_card (H := Z) (K := W)
    rw [inf_eq_left.mpr hZW, hWZ] at this
    exact this.symm
  have hkerc : Nat.card φ.ker = Nat.card Z := by
    rw [hker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hrange : Nat.card φ.range = 2 ^ e := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkerc, hcardW] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (mul_comm _ _))
  have hZ''W : φ.range ≤ W := by
    rintro y ⟨w, rfl⟩
    exact hcomm_mem w w.2
  have hZZ : φ.range ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨w, rfl⟩, hyZ⟩
    have hyZ' : ⁅(w : G), d₀⁆ ∈ Z := hyZ
    have h1 : d₀ * (w : G) * d₀⁻¹ * (w : G)⁻¹ ∈ Z := by
      have e : d₀ * (w : G) * d₀⁻¹ * (w : G)⁻¹ = (⁅(w : G), d₀⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]; exact Z.inv_mem hyZ'
    have hwZ : (w : G) ∈ Z := hfpf d₀ hd₀D hd₀1 w (hWU w.2) h1
    have h2 : ⁅(w : G), d₀⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hDZ d₀ hd₀D w hwZ).symm
    show φ w ∈ (⊥ : Subgroup G)
    rw [hφ, h2]; exact Subgroup.one_mem _
  have hinv : ∀ d ∈ D, ∀ y ∈ φ.range, d * y * d⁻¹ ∈ φ.range := by
    rintro d hd y ⟨w, rfl⟩
    have hcd : d * d₀ = d₀ * d := hDcomm d hd d₀ hd₀D
    have hd0 : d * d₀ * d⁻¹ = d₀ := by rw [hcd]; group
    have hw' : d * (w : G) * d⁻¹ ∈ W := hDW d hd w w.2
    refine ⟨⟨d * (w : G) * d⁻¹, hw'⟩, ?_⟩
    rw [hφ]
    show ⁅d * (w : G) * d⁻¹, d₀⁆ = d * ⁅(w : G), d₀⁆ * d⁻¹
    calc ⁅d * (w : G) * d⁻¹, d₀⁆ = ⁅d * (w : G) * d⁻¹, d * d₀ * d⁻¹⁆ := by rw [hd0]
      _ = d * ⁅(w : G), d₀⁆ * d⁻¹ := by simp only [commutatorElement_def]; group
  have hinv' : ∀ d ∈ D, ∀ y ∈ φ.range, d⁻¹ * y * d ∈ φ.range := by
    intro d hd y hy
    have := hinv d⁻¹ (D.inv_mem hd) y hy
    simpa using this
  have hN : φ.range ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_commute fun a ha b hb => hW_comm a (hZW ha) b (hZ''W hb)
  have hsup : Z ⊔ φ.range = W := by
    apply le_antisymm (sup_le hZW hZ''W)
    have h := card_sup_mul_card_inf hN
    rw [hZZ, Subgroup.card_bot, mul_one, hrange, sup_comm] at h
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hZW hZ''W) ?_).symm.le
    rw [h, hcardW]
  have hEq : ⁅W, D⁆ = φ.range := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro w hw d hd
      have hwmem : w ∈ Z ⊔ φ.range := by rw [hsup]; exact hw
      obtain ⟨z, hz, y, hy, hwzy⟩ := (mem_sup_iff_of_le_normalizer hN).1 hwmem
      have hzd : d * z = z * d := hDZ d hd z hz
      have hzdz : z * d * z⁻¹ = d := by rw [← hzd]; group
      have hzy : z * y = y * z := hW_comm z (hZW hz) y (hZ''W hy)
      have hw' : w = y * z := by rw [hwzy, hzy]
      have e : ⁅y * z, d⁆ = y * (d * y⁻¹ * d⁻¹) := by
        simp only [commutatorElement_def]
        have : y * z * d * (y * z)⁻¹ * d⁻¹ = y * (z * d * z⁻¹) * y⁻¹ * d⁻¹ := by group
        rw [this, hzdz]
        group
      rw [hw', e]
      have := hinv d hd y⁻¹ (φ.range.inv_mem hy)
      exact φ.range.mul_mem hy this
    · rintro y ⟨w, rfl⟩
      exact Subgroup.commutator_mem_commutator w.2 hd₀D
  rw [hEq]
  refine ⟨hZ''W, fun a ha b hb => hW_comm a (hZ''W ha) b (hZ''W hb),
    fun a ha => hU2 a (hWU (hZ''W ha)), hrange, hZZ, ?_⟩
  have hfree : ∀ a ∈ D, a ≠ 1 → ∀ y ∈ φ.range, a⁻¹ * y * a = y → y = 1 := by
    intro a ha ha1 y hy hay
    have h1 : a⁻¹ * y * (a⁻¹)⁻¹ * y⁻¹ ∈ Z := by
      rw [inv_inv, hay, mul_inv_cancel]; exact Z.one_mem
    have hyZ : y ∈ Z :=
      hfpf a⁻¹ (D.inv_mem ha) (fun h => ha1 (inv_eq_one.1 h)) y (hWU (hZ''W hy)) h1
    have : y ∈ φ.range ⊓ Z := ⟨hy, hyZ⟩
    rw [hZZ, Subgroup.mem_bot] at this
    exact this
  have hcard' : Nat.card φ.range = Nat.card D + 1 := by
    rw [hrange, hDcard]; omega
  refine ⟨?_, ?_, ?_⟩
  · rintro b hb z ⟨hz, hz1⟩
    refine ⟨hinv' b hb z hz, fun h => hz1 ?_⟩
    have := congrArg (fun w => b * w * b⁻¹) h
    simpa [mul_assoc] using this
  · rintro z ⟨hz, hz1⟩ z' ⟨hz', hz1'⟩
    exact transitive_of_free_of_card hinv' hfree hcard' hz hz1 hz' hz1'
  · rintro z ⟨hz, hz1⟩ b hb hbz
    by_contra hb1
    exact hz1 (hfree b hb hb1 z hz hbz)

end CFSG.QuasithinUnique.Lin2
