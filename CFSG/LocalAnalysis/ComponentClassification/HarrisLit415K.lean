module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415KB0
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415KB

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem conj_mem_of_normalizer_W_of {X : Type} [Group X] [Finite X] {β t z₁ z : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X)) (ht2 : t * t = 1)
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    {W : Subgroup X} (hW : IsSylowOf 2 W (centralizer {β})) (htW : t ∈ W) (hz₁W : z₁ ∈ W)
    (hz₁2 : z₁ ^ 2 = 1) (hz₁ne : z₁ ≠ t * z₁ * t⁻¹) (hzz : z = z₁ * (t * z₁ * t⁻¹))
    (hmk : ∀ hz₁ : z₁ ∈ centralizer ({β} : Set X),
      (QuotientGroup.mk ⟨z₁, hz₁⟩ : MBar β) ∈ Kb₁)
    (hcomm : ∀ y ∈ W, ∀ hy : y ∈ centralizer ({β} : Set X), y * z₁ = z₁ * y ↔
      Kb₁.map (MulAut.conj (QuotientGroup.mk ⟨y, hy⟩ : MBar β)).toMonoidHom = Kb₁)
    (hmul : ∀ y ∈ W, y * z₁ ≠ z₁ * y → y * t * z₁ = z₁ * (y * t))
    (hW₀z₂ : ∀ y ∈ W, y * z₁ = z₁ * y → y * (t * z₁ * t⁻¹) = (t * z₁ * t⁻¹) * y)
    (hzW : ∀ y ∈ W, y * z = z * y) {Ds : Subgroup X} (hDsW : Ds ≤ W)
    (hDsyl : IsSylowOf 2 (barOf (centralizer {β}) Ds)
      (layer (MBar β) ⊓ centralizer {(QuotientGroup.mk ⟨t, htM⟩ : MBar β)}))
    {m : ℕ} (hm : 2 ≤ m) (eDs : ↥Ds ≃* DihedralGroup (2 ^ m)) (hzDs : z ∈ Ds)
    (hzc : ∀ d ∈ Ds, z * d = d * z) (hA : AutPSL2RCentralizerInput) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlie : Blueprint.LieModel ↥Kb₁ .PSL 2 p n)
    (h8 : 8 ≤ Nat.card ↥(barOf (centralizer {β}) W ⊓ Kb₁))
    (hQ : pCore 2 (MBar β) =
      centralizer ((layer (MBar β) : Subgroup (MBar β)) : Set (MBar β)))
    (hQ4 : Nat.card ↥(pCore 2 (MBar β)) ≤ 4)
    (hQt : pCore 2 (MBar β) ⊓ centralizer {(QuotientGroup.mk ⟨t, htM⟩ : MBar β)} =
      zpowers (betaBar β))
    (hβW : β ∈ W) (hβ1 : β ≠ 1) (hβ2 : β * β = 1)
    (h42h : ∀ E : Subgroup X, E ≤ W ⊓ centralizer {t} →
      (∀ g ∈ W ⊓ centralizer {t}, ∀ e ∈ E, g * e * g⁻¹ ∈ E) → z ∉ E → ∀ e ∈ E, e ^ 2 = 1)
    {g : X} (hg : g ∈ normalizer (W : Set X)) :
    g * z₁ * g⁻¹ = z₁ ∨ g * z₁ * g⁻¹ = t * z₁ * t⁻¹ := by
  by_contra hno
  push Not at hno
  obtain ⟨hnab, hcen, B₀, hB₀W, hB₀c, hB₀n, hZB₀, hB₀2, hZsq, hZ4, hmemZ⟩ :=
    exists_B₀_of htM ht2 hprod hW htW hz₁W hz₁2 hz₁ne hzz hmk hcomm hmul hW₀z₂ hDsW hDsyl hm eDs
      hzDs hzc
  set Z := zpowers z₁ ⊔ zpowers (t * z₁ * t⁻¹) with hZdef
  have hz₂W : t * z₁ * t⁻¹ ∈ W := mul_mem (mul_mem htW hz₁W) (inv_mem htW)
  have hz₂2' : (t * z₁ * t⁻¹) * (t * z₁ * t⁻¹) = 1 := by
    rw [show t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ ^ 2) * t⁻¹ by rw [sq]; group, hz₁2]
    group
  have hz₁2' : z₁ * z₁ = 1 := by rw [← sq]; exact hz₁2
  have hz₁1 : z₁ ≠ 1 := fun h1 => hz₁ne (by rw [h1]; group)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [hzz] at h1
    apply hz₁ne
    calc z₁ = (t * z₁ * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = t * z₁ * t⁻¹ := inv_eq_of_mul_eq_one_right hz₂2'
  have hZ2 : ∀ x ∈ Z, x ^ 2 = 1 := fun x hx => (hB₀2 x (hZB₀ hx)).mpr hx
  have hgW : ∀ y ∈ W, g * y * g⁻¹ ∈ W := fun y hy => (mem_normalizer_iff.mp hg y).mp hy
  have hgW' : ∀ y ∈ W, g⁻¹ * y * g ∈ W := fun y hy => by
    have := (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
    rwa [inv_inv] at this
  set B := B₀.map (MulAut.conj g).toMonoidHom with hBdef
  set Y := Z.map (MulAut.conj g).toMonoidHom with hYdef
  have hmemB : ∀ x, x ∈ B ↔ g⁻¹ * x * g ∈ B₀ := by
    intro x
    rw [hBdef, Subgroup.mem_map_equiv]
    simp
  have hmemY : ∀ x, x ∈ Y ↔ g⁻¹ * x * g ∈ Z := by
    intro x
    rw [hYdef, Subgroup.mem_map_equiv]
    simp
  have hBW : B ≤ W := fun x hx => by
    have h1 := hgW _ (hB₀W ((hmemB x).mp hx))
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h1 := hB₀c _ ((hmemB a).mp ha) _ ((hmemB b).mp hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  have hBn : ∀ y ∈ W, ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro y hy b hb
    rw [hmemB]
    have h1 := hB₀n _ (hgW' y hy) _ ((hmemB b).mp hb)
    rwa [show g⁻¹ * y * g * (g⁻¹ * b * g) * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * b * y⁻¹) * g by
      group] at h1
  have hYB : Y ≤ B := map_mono hZB₀
  have hY4 : Nat.card Y = 4 := by
    rw [hYdef, Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ4]
  have hY2 : ∀ b ∈ B, b ^ 2 = 1 ↔ b ∈ Y := by
    intro b hb
    have h1 : (g⁻¹ * b * g) ^ 2 = g⁻¹ * b ^ 2 * g := by rw [sq, sq]; group
    rw [hmemY, ← hB₀2 _ ((hmemB b).mp hb), h1]
    constructor
    · intro h2
      rw [h2]
      group
    · intro h2
      calc b ^ 2 = g * (g⁻¹ * b ^ 2 * g) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
  have hYsq : ∀ y ∈ Y, ∃ b ∈ B, b ^ 2 = y := by
    intro y hy
    obtain ⟨x, hxB₀, hx2⟩ := hZsq _ ((hmemY y).mp hy)
    refine ⟨g * x * g⁻¹, (hmemB _).mpr (by
      rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
      exact hxB₀), ?_⟩
    rw [conj_pow, hx2]
    group
  have hgz : g * z₁ * g⁻¹ ≠ z := by
    intro h1
    have h2 : z₁ = g⁻¹ * z * g := by rw [← h1]; group
    have h3 := hzW _ (hgW' t htW)
    apply hz₁ne
    have h4 : t * z₁ = z₁ * t := by
      have h5 : g⁻¹ * t * g * z = z * (g⁻¹ * t * g) := h3
      have h6 : t * (g⁻¹ * z * g) = (g⁻¹ * z * g) * t := by
        have h7 := hzW _ (hgW t htW)
        have h8 : g * t * g⁻¹ * z = z * (g * t * g⁻¹) := h7
        calc t * (g⁻¹ * z * g) = g⁻¹ * ((g * t * g⁻¹) * z) * g := by group
          _ = g⁻¹ * (z * (g * t * g⁻¹)) * g := by rw [h8]
          _ = (g⁻¹ * z * g) * t := by group
      rw [h2]
      exact h6
    calc z₁ = z₁ * t * t⁻¹ := by group
      _ = t * z₁ * t⁻¹ := by rw [← h4]
  have hz₁B : z₁ ∉ B := by
    intro hz₁B
    have hz₁Y : z₁ ∈ Y := (hY2 z₁ hz₁B).mp hz₁2
    have hz₂Y : t * z₁ * t⁻¹ ∈ Y := by
      have h1 : t * z₁ * t⁻¹ ∈ B := hBn t htW z₁ hz₁B
      exact (hY2 _ h1).mp (by rw [sq]; exact hz₂2')
    have hZY : Z ≤ Y := sup_le (zpowers_le.mpr hz₁Y) (zpowers_le.mpr hz₂Y)
    have hZY' : Z = Y := eq_of_le_of_card_ge hZY (by rw [hY4, hZ4])
    have h1 : g * z₁ * g⁻¹ ∈ Y := by
      rw [hmemY, show g⁻¹ * (g * z₁ * g⁻¹) * g = z₁ by group]
      exact mem_sup_left (mem_zpowers z₁)
    rw [← hZY'] at h1
    rcases hmemZ _ h1 with h2 | h2 | h2 | h2
    · apply hz₁1
      calc z₁ = g⁻¹ * (g * z₁ * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · exact hno.1 h2
    · exact hno.2 h2
    · exact hgz h2
  have hz₂B : t * z₁ * t⁻¹ ∉ B := by
    intro h1
    apply hz₁B
    have h2 := hBn t htW _ h1
    rwa [show t * (t * z₁ * t⁻¹) * t⁻¹ = (t * t) * z₁ * (t * t)⁻¹ by group, ht2,
      show (1 : X) * z₁ * 1⁻¹ = z₁ by group] at h2
  have hz2 : z ^ 2 = 1 := hZ2 z (by
    rw [hzz]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)))
  exact false_of_B htM ht2 hprod hW htW hz₁W hzz hz1 hz2 hmk hnab hcen hA hp hp2 hlie h8 hQ hQ4
    hQt hβW hβ1 hβ2 h42h hBW hBc hBn hYB hY4 hY2 hYsq hz₁B hz₂B

end L415

end CFSG.ComponentClassification.HarrisLit
