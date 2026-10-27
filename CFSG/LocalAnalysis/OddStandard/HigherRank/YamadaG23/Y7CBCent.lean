module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBDef

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7c_conj_normalizes_F (c : Ctx7 G L) (hb : B7Std c) {h : G}
    (hhH : h ∈ c.s.H) (hhX : h ∈ y7cX c.s) :
    h ∈ normalizer (c.s.fr.F : Set G) := by
  have h1 : h ∈ normalizer (c.s.H : Set G) := Subgroup.le_normalizer hhH
  have h2 : h ∈ normalizer (M3 c.s : Set G) := hhX
  have h3 : h ∈ normalizer ((c.s.H ⊓ M3 c.s : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  rwa [y54_H_inf_M3 c.toCtx5 hb.hH] at h3

private theorem y7c_NLF_eq_JF' {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.F = JF s := by
  have h := hH.hLF.fact18.2.2.2.2.2.2.1.1
  rw [f3_zL_eq_bot hH, sup_bot_eq] at h
  simpa only [JF] using h

private theorem y7c_JF_le_X' (c : Ctx7 G L) (hb : B7Std c) : JF c.s ≤ y7cX c.s := by
  rw [y7cX, Subgroup.le_set_normalizer_iff]
  intro j hj m hm
  rw [← y7c_NLF_eq_JF' hb.hH] at hj
  exact y54_N_norm_M3 c.toCtx5 hb.hH j (y54_NL_le_N hb.hH hj) m hm

private theorem y7c_X0_le_X' (c : Ctx7 G L) (hb : B7Std c) : f4X0 c.s ≤ y7cX c.s := by
  have hN : f4N c.s ≤ y7cX c.s := by
    intro n hn
    rw [y7cX, Subgroup.mem_set_normalizer_iff]
    intro m
    constructor
    · intro hm
      exact y54_N_norm_M3 c.toCtx5 hb.hH n hn m hm
    · intro hm
      have hn' : n⁻¹ ∈ f4N c.s := (f4N c.s).inv_mem hn
      have h := y54_N_norm_M3 c.toCtx5 hb.hH n⁻¹ hn' (n * m * n⁻¹) hm
      rwa [show n⁻¹ * (n * m * n⁻¹) * n⁻¹⁻¹ = m by group] at h
  intro x hx
  obtain ⟨hxH, hxF⟩ := Subgroup.mem_inf.mp hx
  exact hN (Subgroup.mem_inf.mpr
    ⟨hxH, Subgroup.centralizer_le_normalizer (c.s.fr.F : Set G) hxF⟩)

theorem y7c_coset_cent (c : Ctx7 G L) (hb : B7Std c) {y : G}
    (h : y * c.s.t * y⁻¹ * c.s.t⁻¹ ∈ M3 c.s) : ∃ w ∈ M3 c.s, w⁻¹ * y ∈ c.s.H := by
  have ht2 : c.s.t ^ 2 = 1 := y7c_t_sq c.s
  have ht2' : c.s.t * c.s.t = 1 := by simpa [pow_two] using ht2
  set u : G := y * c.s.t * y⁻¹ * c.s.t⁻¹ with hu
  have huM : u ∈ M3 c.s := by simpa [hu] using h
  have hu2 : u ^ 2 = 1 := (y7c_M3_elem c hb.hH hb.fact57).2 u huM
  have hu2' : u * u = 1 := by simpa [pow_two] using hu2
  have hut : u * c.s.t = y * c.s.t * y⁻¹ := by rw [hu]; group
  have hsq : (u * c.s.t) * (u * c.s.t) = 1 := by
    rw [hut, ← pow_two]
    have h2 : (y * c.s.t * y⁻¹) ^ 2 = y * c.s.t ^ 2 * y⁻¹ := by
      rw [pow_two, pow_two]; group
    rw [h2, ht2]
    group
  have hcomm : u * c.s.t = c.s.t * u := by
    have h1 : (u * c.s.t)⁻¹ = u * c.s.t := inv_eq_of_mul_eq_one_right hsq
    calc u * c.s.t = (u * c.s.t)⁻¹ := h1.symm
      _ = c.s.t⁻¹ * u⁻¹ := mul_inv_rev _ _
      _ = c.s.t * u := by
        rw [inv_eq_of_mul_eq_one_right ht2', inv_eq_of_mul_eq_one_right hu2']
  have huH : u ∈ c.s.H := by
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  have huF : u ∈ c.s.fr.F := by
    rw [← y54_H_inf_M3 c.toCtx5 hb.hH]
    exact Subgroup.mem_inf.mpr ⟨huH, huM⟩
  have hyt : y * c.s.t * y⁻¹ ∈ c.s.tCoset c.s.fr.F := by
    refine ⟨u, huF, ?_⟩
    rw [hu]; group
  have hconj : y * c.s.t * y⁻¹ ∈ conjClass (M3 c.s) c.s.t := by
    rwa [y54_conjClass_M3 c.toCtx5 hb.hH]
  simp only [conjClass, Set.mem_setOf_eq] at hconj
  obtain ⟨w, hwM, hwconj⟩ := hconj
  refine ⟨w, hwM, ?_⟩
  rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
  have hwt : (w⁻¹ * y) * c.s.t * (w⁻¹ * y)⁻¹ = c.s.t := by
    calc (w⁻¹ * y) * c.s.t * (w⁻¹ * y)⁻¹
        = w⁻¹ * (y * c.s.t * y⁻¹) * w := by group
      _ = w⁻¹ * (w * c.s.t * w⁻¹) * w := by rw [hwconj]
      _ = c.s.t := by group
  calc (w⁻¹ * y) * c.s.t
      = ((w⁻¹ * y) * c.s.t * (w⁻¹ * y)⁻¹) * (w⁻¹ * y) := by group
    _ = c.s.t * (w⁻¹ * y) := by rw [hwt]

theorem y7c_comm_mem_M3 (c : Ctx7 G L) (hb : B7Std c) {y : G} (hy : y ∈ y7cX c.s)
    (h : y7cPi c.s ⟨y, hy⟩ * y7cTC c hb = y7cTC c hb * y7cPi c.s ⟨y, hy⟩) :
    y * c.s.t * y⁻¹ * c.s.t⁻¹ ∈ M3 c.s := by
  have htX : c.s.t ∈ y7cX c.s := y7c_t_mem_X c hb
  have hmem : y * c.s.t * y⁻¹ * c.s.t⁻¹ ∈ y7cX c.s :=
    (y7cX c.s).mul_mem
      ((y7cX c.s).mul_mem ((y7cX c.s).mul_mem hy htX) ((y7cX c.s).inv_mem hy))
      ((y7cX c.s).inv_mem htX)
  rw [← y7cPi_eq_one_iff c.s ⟨y * c.s.t * y⁻¹ * c.s.t⁻¹, hmem⟩]
  have hx : (⟨y * c.s.t * y⁻¹ * c.s.t⁻¹, hmem⟩ : ↥(y7cX c.s)) =
      ⟨y, hy⟩ * ⟨c.s.t, htX⟩ * ⟨y, hy⟩⁻¹ * ⟨c.s.t, htX⟩⁻¹ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  simp only [hx, map_mul, map_inv]
  rw [h]
  group

theorem y7c_B_cent (c : Ctx7 G L) (hb : B7Std c) :
    ∀ x : y7cGam c.s, x * y7cTC c hb = y7cTC c hb * x →
      ∃ j ∈ y7cJC c, ∃ q ∈ y7cQC c, x = j * q := by
  intro x hx
  obtain ⟨y, rfl⟩ := y7cPi_surjective c.s x
  have hyX : (y : G) ∈ y7cX c.s := y.2
  have hcomm : y * c.s.t * y⁻¹ * c.s.t⁻¹ ∈ M3 c.s :=
    y7c_comm_mem_M3 c hb y.2 hx
  obtain ⟨w, hwM, hwyH⟩ := y7c_coset_cent c hb hcomm
  have hwX : w ∈ y7cX c.s := y7c_M3_le_X c.s hwM
  have hhX : (w⁻¹ * y : G) ∈ y7cX c.s :=
    (y7cX c.s).mul_mem ((y7cX c.s).inv_mem hwX) hyX
  have hhH : (w⁻¹ * y : G) ∈ c.s.H := hwyH
  have hhN : (w⁻¹ * y : G) ∈ f4N c.s :=
    ⟨hhH, y7c_conj_normalizes_F c hb hhH hhX⟩
  obtain ⟨n₁, hn₁, x₀, hx₀, hn_eq⟩ := y54_N_eq hb.hH (w⁻¹ * y) hhN
  have hn₁JF : n₁ ∈ JF c.s := by
    rw [y7c_NLF_eq_JF' hb.hH] at hn₁
    exact hn₁
  have hn₁X : n₁ ∈ y7cX c.s := y7c_JF_le_X' c hb hn₁JF
  have hx₀X : x₀ ∈ y7cX c.s := y7c_X0_le_X' c hb hx₀
  refine ⟨y7cPi c.s ⟨n₁, hn₁X⟩, ?_, y7cPi c.s ⟨x₀, hx₀X⟩, ?_, ?_⟩
  · rw [mem_y7cImg]
    exact ⟨⟨n₁, hn₁X⟩, hn₁JF, rfl⟩
  · rw [mem_y7cImg]
    exact ⟨⟨x₀, hx₀X⟩, hx₀, rfl⟩
  · have hy_eq : (y : G) = w * (n₁ * x₀) := by
      rw [← hn_eq]; group
    have hsub : (y : ↥(y7cX c.s)) = ⟨w, hwX⟩ * ⟨n₁, hn₁X⟩ * ⟨x₀, hx₀X⟩ := by
      ext
      simp only [Subgroup.coe_mul, Subtype.coe_mk, hy_eq]
      group
    have hw1 : y7cPi c.s ⟨w, hwX⟩ = 1 := (y7cPi_eq_one_iff c.s ⟨w, hwX⟩).mpr hwM
    simp only [hsub, map_mul, hw1, one_mul]

end CFSG.OddStandard.HigherRank.YamadaG23
