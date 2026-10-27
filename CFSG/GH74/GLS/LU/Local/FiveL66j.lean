module

public import CFSG.GH74.GLS.LU.Local.FiveL66i
public import CFSG.GH74.GLS.LU.Local.FiveL66g
public import CFSG.GH74.GLS.LU.Local.FiveL83c

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section NN

variable {G : Type} [Group G] [Finite G] {z u : G}

theorem mem_NN_of_conj_mem_UU (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {g : G}
    (h1 : g * z * g⁻¹ ∈ UU z u) (h2 : g * u * g⁻¹ ∈ UU z u) : g ∈ NN z u := by
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro k hk
  rcases (mem_UU_iff hz2 hu2 hzu).mp hk with h | h | h | h
  · rw [h]; simp
  · rw [h]; exact h1
  · rw [h]; exact h2
  · have e : g * k * g⁻¹ = (g * z * g⁻¹) * (g * u * g⁻¹) := by rw [h]; group
    rw [e]
    exact (UU z u).mul_mem h1 h2

theorem N_trans_of (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {x : G}
    (hxN : x ∈ NN z u) (hxz : x * z * x⁻¹ = u) (hxu : x * u * x⁻¹ = z * u) :
    ∀ a ∈ UU z u, a ≠ 1 → ∀ b ∈ UU z u, b ≠ 1 → ∃ n ∈ NN z u, n * a * n⁻¹ = b := by
  have hm : ∀ a ∈ UU z u, a ≠ 1 → ∃ m ∈ NN z u, m * z * m⁻¹ = a := by
    intro a ha ha1
    rcases (mem_UU_iff hz2 hu2 hzu).mp ha with h | h | h | h
    · exact absurd h ha1
    · exact ⟨1, (NN z u).one_mem, by rw [h]; simp⟩
    · exact ⟨x, hxN, by rw [h]; exact hxz⟩
    · refine ⟨x * x, (NN z u).mul_mem hxN hxN, ?_⟩
      calc x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
        _ = a := by rw [hxz, hxu, h]
  intro a ha ha1 b hb hb1
  obtain ⟨ma, hma, hmaz⟩ := hm a ha ha1
  obtain ⟨mb, hmb, hmbz⟩ := hm b hb hb1
  refine ⟨mb * ma⁻¹, (NN z u).mul_mem hmb ((NN z u).inv_mem hma), ?_⟩
  calc mb * ma⁻¹ * a * (mb * ma⁻¹)⁻¹ = mb * (ma⁻¹ * (ma * z * ma⁻¹) * ma) * mb⁻¹ := by
        rw [hmaz]; group
    _ = b := by rw [← hmbz]; group

end NN

section NormH

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ : G} {Gs : Type} [Group Gs] {z' t' u' : Gs} {S' : Sylow 2 Gs} {K₁' K₂' : Subgroup Gs}
  {ψ : ↥(Cz z) ≃* ↥(Cz z')}

theorem ModelPic.N_normH (c : FiveCtx G p f z S K₁ K₂ t u)
    (pic : ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ)
    (b66 : Five66W z t u K₁ K₂ H w₁) {X₁ : Subgroup G} (b82 : Five82W z t u K₁ K₂ H w₁ X₁)
    {Y : Subgroup G} (b83 : Five83 z t u H X₁ Y) : ∀ n ∈ NN z u, cjL n H = H := by
  intro n hn
  have cfg : Cfg2W G p f z S K₁ K₂ t u H w₁ X₁ := ⟨c, b66, b82⟩
  have hz2 : z * z = 1 := c.hs.z_sq
  have hu2 : u * u = 1 := c.hs.u_sq
  have hzu : z * u = u * z := c.hs.zu_comm
  have hC := c.card_Cz
  have hzU : z ∈ UU z u := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hs₀ : n⁻¹ * z * n ∈ UU z u := conj_mem_UU_of_mem_NN hn hzU
  have hs₀1 : n⁻¹ * z * n ≠ 1 := by
    intro h
    apply c.z_ne_one
    calc z = n * (n⁻¹ * z * n) * n⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases (mem_UU_iff hz2 hu2 hzu).mp hs₀ with h | h | h | h
  · exact absurd h hs₀1
  ·
    refine pic.normH_aux hC b66 hn (R₀ := XX t X₁) ?_ cfg.XX_card2 cfg.hinv_XX
    rw [h]; exact cfg.XX_le_Cz
  ·
    have hwz : w₁ * z * w₁⁻¹ = z := by
      calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [c.hc.cz₁ b66.w₁_mem]
        _ = z := by group
    have hwzu : w₁ * (z * u) * w₁⁻¹ = u := by
      calc w₁ * (z * u) * w₁⁻¹ = (w₁ * z * w₁⁻¹) * (w₁ * u * w₁⁻¹) := by group
        _ = z * (u * z) := by rw [hwz, b66.w₁_u]
        _ = (z * u) * z := by group
        _ = (u * z) * z := by rw [hzu]
        _ = u * (z * z) := by group
        _ = u := by rw [hz2, mul_one]
    have hw₁N : w₁ ∈ NN z u := by
      refine mem_NN_of_conj_mem_UU hz2 hu2 hzu ?_ ?_
      · rw [hwz]; exact hzU
      · rw [b66.w₁_u]
        exact (UU z u).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)) hzU
    have hw1H : cjL w₁ H = H :=
      pic.normH_of_normK b66 hw₁N (cjL_eq_of_mem_normalizer (Subgroup.le_normalizer b66.w₁_mem))
        (cjL_eq_of_comm (fun a ha => c.hc.comm w₁ b66.w₁_mem a ha))
    have hle : cjL w₁ Y ≤ centralizer ({n⁻¹ * z * n} : Set G) := by
      rw [h]
      intro y hy
      have hy' : w₁⁻¹ * y * w₁ ∈ Y := mem_cjL.mp hy
      have hy1 := Subgroup.mem_centralizer_singleton_iff.mp (b83.Y_syl.1 hy')
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc y * u = y * (w₁ * (z * u) * w₁⁻¹) := by rw [hwzu]
        _ = w₁ * ((w₁⁻¹ * y * w₁) * (z * u)) * w₁⁻¹ := by group
        _ = w₁ * ((z * u) * (w₁⁻¹ * y * w₁)) * w₁⁻¹ := by rw [hy1]
        _ = (w₁ * (z * u) * w₁⁻¹) * y := by group
        _ = u * y := by rw [hwzu]
    refine pic.normH_aux hC b66 hn (R₀ := cjL w₁ Y) hle ?_ (HInv.conj hw1H b83.Y_H)
    rw [card_cjL]; exact b83.Y_card
  ·
    refine pic.normH_aux hC b66 hn (R₀ := Y) ?_ b83.Y_card b83.Y_H
    rw [h]; exact b83.Y_syl.1

end NormH

end CFSG.GH74.GLS.LU.Local.Five
