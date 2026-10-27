module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y5a (s : Setting3 G L) : G := s.fr.a₁ * s.fr.b₁ * s.fr.b₂

private abbrev w0 : FreeGroup (Fin 6) := FreeGroup.of 0
private abbrev w1 : FreeGroup (Fin 6) := FreeGroup.of 1
private abbrev w2 : FreeGroup (Fin 6) := FreeGroup.of 2
private abbrev w3 : FreeGroup (Fin 6) := FreeGroup.of 3
private abbrev w4 : FreeGroup (Fin 6) := FreeGroup.of 4
private abbrev w5 : FreeGroup (Fin 6) := FreeGroup.of 5

private theorem y5_key {G : Type*} [Group G] {c d g z : G} (hz : z ^ 2 = 1) (hd : d ^ 2 = z)
    (h : c * g * c⁻¹ * g⁻¹ = c * d * z) : g * c * g⁻¹ = d := by
  have hd4 : d ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hd, hz]
  have hdz : (d * z)⁻¹ = d := by
    rw [inv_eq_iff_mul_eq_one, ← hd]
    calc (d * d ^ 2) * d = d ^ 4 := by group
      _ = 1 := hd4
  have h1 : g * c⁻¹ * g⁻¹ = d * z := by
    have h2 : c * (g * c⁻¹ * g⁻¹) = c * (d * z) := by
      calc c * (g * c⁻¹ * g⁻¹) = c * g * c⁻¹ * g⁻¹ := by group
        _ = c * d * z := h
        _ = c * (d * z) := by group
    exact mul_left_cancel h2
  calc g * c * g⁻¹ = (g * c⁻¹ * g⁻¹)⁻¹ := by group
    _ = (d * z)⁻¹ := by rw [h1]
    _ = d := hdz

private theorem y5_z_comm_S {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {x : G} (hx : x ∈ s.fr.S) : s.fr.z * x = x * s.fr.z := by
  have hcen : cen s.fr.S = s.fr.Z := hH.hLF.fact14.1.1
  have hz : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    have hmem : s.fr.z ∈ cen s.fr.S := hcen.symm ▸ Subgroup.mem_zpowers s.fr.z
    exact (Subgroup.mem_inf.mp hmem).2
  exact (Subgroup.mem_centralizer_iff.mp hz x hx).symm

private theorem y5_a1_b1 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.a₁ * s.fr.b₁ * s.fr.a₁⁻¹ = s.fr.z * s.fr.b₁ := by
  have hsrel := s3_srel hH.hS hH.hZ s
  calc s.fr.a₁ * s.fr.b₁ * s.fr.a₁⁻¹ = ⁅s.fr.a₁, s.fr.b₁⁆ * s.fr.b₁ := by
        rw [commutatorElement_def]; group
    _ = s.fr.z * s.fr.b₁ := by rw [hsrel.comm1]

private theorem y5_a1_b2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹ = s.fr.b₂ := by
  have hsrel := s3_srel hH.hS hH.hZ s
  calc s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹ = ⁅s.fr.a₁, s.fr.b₂⁆ * s.fr.b₂ := by
        rw [commutatorElement_def]; group
    _ = s.fr.b₂ := by rw [hsrel.a1b2, one_mul]

private theorem y5_a1_w {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹ =
      s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  calc s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹
      = (s.fr.a₁ * s.fr.b₁ * s.fr.a₁⁻¹) * (s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹) := by group
    _ = (s.fr.z * s.fr.b₁) * s.fr.b₂ := by rw [y5_a1_b1 hH, y5_a1_b2 hH]
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by group

private theorem y5_w_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (s.fr.b₁ * s.fr.b₂) ^ 2 = 1 := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hc : Commute s.fr.b₁ s.fr.b₂ := commutatorElement_eq_one_iff_commute.mp hsrel.b1b2
  calc (s.fr.b₁ * s.fr.b₂) ^ 2 = s.fr.b₁ ^ 2 * s.fr.b₂ ^ 2 := hc.mul_pow 2
    _ = s.fr.z * s.fr.z := by rw [show s.fr.b₁ ^ 2 = s.fr.z from rfl, hsrel.b2_sq]
    _ = 1 := by rw [← pow_two, hsrel.z_sq]

private theorem y5_mem_cenB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {v : G} (hv : v ∈ cen s.fr.B) :
    v = 1 ∨ v = s.fr.z ∨ v = s.fr.b₁ * s.fr.b₂ ∨ v = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  obtain ⟨w, hwV, hzV, hwne1, hzne1, hwnez, hwsq, hzsq, hwz, henum⟩ := f3_V_elems hH
  have hcen : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hH.hLF.fact14.2.2.1.1
  have hw0V : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := by
    rw [hcen]; exact Subgroup.subset_closure (by simp)
  have hcyc : ¬ IsCyclic ↥(cen s.fr.B) := hH.hLF.fact14.2.2.1.2.2.2.1
  have hzz : s.fr.z * s.fr.z = 1 := by rw [← pow_two, hzsq]
  have hzzw : s.fr.z * (s.fr.z * w) = w := by
    calc s.fr.z * (s.fr.z * w) = (s.fr.z * s.fr.z) * w := by group
      _ = 1 * w := by rw [hzz]
      _ = w := one_mul w
  have hw0ne1 : s.fr.b₁ * s.fr.b₂ ≠ 1 := by
    intro h1
    apply hcyc
    rw [hcen, h1]
    exact Subgroup.isCyclic_of_le (H' := Subgroup.zpowers s.fr.z) (by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers s.fr.z)
  have hw0nez : s.fr.b₁ * s.fr.b₂ ≠ s.fr.z := by
    intro h1
    apply hcyc
    rw [hcen, h1]
    exact Subgroup.isCyclic_of_le (H' := Subgroup.zpowers s.fr.z) (by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_zpowers s.fr.z
      · exact Subgroup.mem_zpowers s.fr.z)
  have hw0cases := henum (s.fr.b₁ * s.fr.b₂) hw0V
  rcases henum v hv with h1 | hz | hw | hzw
  · exact Or.inl h1
  · exact Or.inr (Or.inl hz)
  · rcases hw0cases with h0 | h0 | h0 | h0
    · exact absurd h0 hw0ne1
    · exact absurd h0 hw0nez
    · exact Or.inr (Or.inr (Or.inl (hw.trans h0.symm)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc v = w := hw
        _ = s.fr.z * (s.fr.z * w) := hzzw.symm
        _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by rw [← h0]
  · rcases hw0cases with h0 | h0 | h0 | h0
    · exact absurd h0 hw0ne1
    · exact absurd h0 hw0nez
    · exact Or.inr (Or.inr (Or.inr (by rw [hzw, h0])))
    · exact Or.inr (Or.inr (Or.inl (by rw [hzw, ← h0])))

private theorem y5_rel_a1 {s : Setting3 G L} {g : G}
    (hrel : ∀ r ∈ Frame.rels11, FreeGroup.lift (frameWith s g).gens11 r = 1) :
    s.fr.a₁ * g * s.fr.a₁⁻¹ * g⁻¹ = s.fr.a₁ * s.fr.a₂ * s.fr.z := by
  have hr := hrel (⁅w0, w5⁆ * (w0 * w2 * w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
  have hr' : s.fr.a₁ * g * s.fr.a₁⁻¹ * g⁻¹ * (s.fr.a₁ * s.fr.a₂ * s.fr.z)⁻¹ = 1 := by
    simpa [SFrame.z, Frame.gens11, frameWith, commutatorElement_def, map_mul, map_inv, map_pow]
      using hr
  exact mul_inv_eq_one.mp hr'

private theorem y5_rel_a2 {s : Setting3 G L} {g : G}
    (hrel : ∀ r ∈ Frame.rels11, FreeGroup.lift (frameWith s g).gens11 r = 1) :
    s.fr.a₂ * g * s.fr.a₂⁻¹ * g⁻¹ = s.fr.a₁ * s.fr.a₂ * s.fr.z := by
  have hr := hrel (⁅w2, w5⁆ * (w0 * w2 * w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
  have hr' : s.fr.a₂ * g * s.fr.a₂⁻¹ * g⁻¹ * (s.fr.a₁ * s.fr.a₂ * s.fr.z)⁻¹ = 1 := by
    simpa [SFrame.z, Frame.gens11, frameWith, commutatorElement_def, map_mul, map_inv, map_pow]
      using hr
  exact mul_inv_eq_one.mp hr'

private theorem y5_rel_b1 {s : Setting3 G L} {g : G}
    (hrel : ∀ r ∈ Frame.rels11, FreeGroup.lift (frameWith s g).gens11 r = 1) :
    s.fr.b₁ * g * s.fr.b₁⁻¹ * g⁻¹ = s.fr.b₁ * s.fr.b₂ * s.fr.z := by
  have hr := hrel (⁅w1, w5⁆ * (w1 * w3 * w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
  have hr' : s.fr.b₁ * g * s.fr.b₁⁻¹ * g⁻¹ * (s.fr.b₁ * s.fr.b₂ * s.fr.z)⁻¹ = 1 := by
    simpa [SFrame.z, Frame.gens11, frameWith, commutatorElement_def, map_mul, map_inv, map_pow]
      using hr
  exact mul_inv_eq_one.mp hr'

private theorem y5_rel_b2 {s : Setting3 G L} {g : G}
    (hrel : ∀ r ∈ Frame.rels11, FreeGroup.lift (frameWith s g).gens11 r = 1) :
    s.fr.b₂ * g * s.fr.b₂⁻¹ * g⁻¹ = s.fr.b₁ * s.fr.b₂ * s.fr.z := by
  have hr := hrel (⁅w3, w5⁆ * (w1 * w3 * w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
  have hr' : s.fr.b₂ * g * s.fr.b₂⁻¹ * g⁻¹ * (s.fr.b₁ * s.fr.b₂ * s.fr.z)⁻¹ = 1 := by
    simpa [SFrame.z, Frame.gens11, frameWith, commutatorElement_def, map_mul, map_inv, map_pow]
      using hr
  exact mul_inv_eq_one.mp hr'

private theorem y5_rel_h0 {s : Setting3 G L} {g : G}
    (hrel : ∀ r ∈ Frame.rels11, FreeGroup.lift (frameWith s g).gens11 r = 1) :
    s.fr.h₀ * g * s.fr.h₀⁻¹ * g⁻¹ = s.fr.z := by
  have hr := hrel (⁅w4, w5⁆ * (w1 ^ 2)⁻¹) (by rw [Frame.rels11]; decide)
  have hr' : s.fr.h₀ * g * s.fr.h₀⁻¹ * g⁻¹ * (s.fr.z)⁻¹ = 1 := by
    simpa [SFrame.z, Frame.gens11, frameWith, commutatorElement_def, map_mul, map_inv, map_pow]
      using hr
  exact mul_inv_eq_one.mp hr'

theorem y5a_mem_A (s : Setting3 G L) : y5a s ∈ s.fr.A :=
  mul_mem (mul_mem (s3_a₁_mem_A s) (s3_b₁_mem_A s)) (s3_b₂_mem_A s)

theorem y5a_mem_S (s : Setting3 G L) : y5a s ∈ s.fr.S :=
  s3_a₁b₁b₂_mem_S s

theorem y5a_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : y5a s ^ 2 = 1 := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have h1 : y5a s = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁ := by
    rw [y5a]
    calc s.fr.a₁ * s.fr.b₁ * s.fr.b₂
        = (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹) * s.fr.a₁ := by group
      _ = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁ := by rw [y5_a1_w hH]
  have h2 : s.fr.a₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁⁻¹ = s.fr.b₁ * s.fr.b₂ := by
    have hza : s.fr.a₁ * s.fr.z = s.fr.z * s.fr.a₁ :=
      (y5_z_comm_S hH (s3_a₁_mem_S s)).symm
    have hAz : s.fr.a₁ * s.fr.z * s.fr.a₁⁻¹ = s.fr.z := by rw [hza]; group
    have hzz : s.fr.z * s.fr.z = 1 := by rw [← pow_two, hsrel.z_sq]
    calc s.fr.a₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁⁻¹
        = (s.fr.a₁ * s.fr.z * s.fr.a₁⁻¹) * (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹) := by
          group
      _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by rw [hAz, y5_a1_w hH]
      _ = (s.fr.z * s.fr.z) * (s.fr.b₁ * s.fr.b₂) := by group
      _ = s.fr.b₁ * s.fr.b₂ := by rw [hzz, one_mul]
  calc y5a s ^ 2 = ((s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁) *
        ((s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁) := by rw [pow_two, h1]
    _ = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) *
        (s.fr.a₁ * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₁⁻¹) * s.fr.a₁ ^ 2 := by group
    _ = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.b₁ * s.fr.b₂) * s.fr.z := by
          rw [h2, show s.fr.a₁ ^ 2 = s.fr.z from hsrel.a1_sq]
    _ = 1 := by
          have hww : (s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂) = 1 := by
            rw [← pow_two]; exact y5_w_sq hH
          have hre : (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.b₁ * s.fr.b₂) * s.fr.z
              = s.fr.z * ((s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂)) * s.fr.z := by group
          have hzz : s.fr.z * s.fr.z = 1 := by rw [← pow_two, hsrel.z_sq]
          rw [hre, hww, mul_one, hzz]

theorem y5a_conj_z {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y5a s * s.fr.z * (y5a s)⁻¹ = s.fr.z := by
  have hcomm := y5_z_comm_S hH (y5a_mem_S s)
  calc y5a s * s.fr.z * (y5a s)⁻¹ = s.fr.z * y5a s * (y5a s)⁻¹ := by rw [hcomm]
    _ = s.fr.z := by group

theorem y5a_conj_w {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y5a s * (s.fr.b₁ * s.fr.b₂) * (y5a s)⁻¹ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := by
  have hww : (s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂) = 1 := by
    rw [← pow_two]; exact y5_w_sq hH
  have hwinv : (s.fr.b₁ * s.fr.b₂)⁻¹ = s.fr.b₁ * s.fr.b₂ :=
    inv_eq_of_mul_eq_one_right hww
  calc y5a s * (s.fr.b₁ * s.fr.b₂) * (y5a s)⁻¹
      = (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂)) * (s.fr.b₁ * s.fr.b₂) *
          (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂))⁻¹ := by rw [y5a]; group
    _ = (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂)) * (s.fr.b₁ * s.fr.b₂) *
          ((s.fr.b₁ * s.fr.b₂)⁻¹ * s.fr.a₁⁻¹) := by rw [mul_inv_rev]
    _ = (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂)) * (s.fr.b₁ * s.fr.b₂) *
          ((s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹) := by rw [hwinv]
    _ = s.fr.a₁ * ((s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂)) *
          ((s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹) := by group
    _ = s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * s.fr.a₁⁻¹ := by rw [hww]; group
    _ = s.fr.z * (s.fr.b₁ * s.fr.b₂) := y5_a1_w hH

theorem y5a_conj_V {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ w ∈ cen s.fr.B, w ≠ 1 → w ≠ s.fr.z → y5a s * w * (y5a s)⁻¹ = s.fr.z * w := by
  intro v hv hv1 hvz
  have hz := y5a_conj_z hH
  have hw0 := y5a_conj_w hH
  have hcomm := y5_z_comm_S hH (y5a_mem_S s)
  rcases y5_mem_cenB hH hv with h1 | hz' | hw0' | hzw0
  · exact absurd h1 hv1
  · exact absurd hz' hvz
  · rw [hw0']; exact hw0
  · rw [hzw0]
    calc y5a s * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (y5a s)⁻¹
        = (y5a s * s.fr.z) * (s.fr.b₁ * s.fr.b₂) * (y5a s)⁻¹ := by group
      _ = (s.fr.z * y5a s) * (s.fr.b₁ * s.fr.b₂) * (y5a s)⁻¹ := by rw [hcomm]
      _ = s.fr.z * (y5a s * (s.fr.b₁ * s.fr.b₂) * (y5a s)⁻¹) := by group
      _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by rw [hw0]

theorem y5a_mem_normB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y5a s ∈ normIn L s.fr.B := by
  have haS : y5a s ∈ s.fr.S := y5a_mem_S s
  have haN : y5a s ∈ normIn s.H s.fr.B := f3_T_le_N hH (s3_S_le_T s haS)
  exact Subgroup.mem_inf.mpr ⟨s3_S_le_L s haS, (Subgroup.mem_inf.mp haN).2⟩

theorem y5_g_swap {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hact : ActsAs L g s.fr'.σ) :
    g * s.fr.a₁ * g⁻¹ = s.fr.a₂ ∧ g * s.fr.a₂ * g⁻¹ = s.fr.a₁ ∧
      g * s.fr.b₁ * g⁻¹ = s.fr.b₂ ∧ g * s.fr.b₂ * g⁻¹ = s.fr.b₁ ∧
      g * s.fr.z * g⁻¹ = s.fr.z ∧ g * s.fr.h₀ * g⁻¹ = s.fr.z * s.fr.h₀ := by
  obtain ⟨hrel, -⟩ := (hH.hLF.sigma g hg2 hact).2.2
  have hsrel := s3_srel hH.hS hH.hZ s
  have hc12 : s.fr.a₁ * s.fr.a₂ = s.fr.a₂ * s.fr.a₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.a1a2).eq
  have hc12b : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.b1b2).eq
  have ha1 : g * s.fr.a₁ * g⁻¹ = s.fr.a₂ := y5_key hsrel.z_sq hsrel.a2_sq (y5_rel_a1 hrel)
  have ha2 : g * s.fr.a₂ * g⁻¹ = s.fr.a₁ :=
    y5_key hsrel.z_sq hsrel.a1_sq (by rw [y5_rel_a2 hrel, hc12])
  have hb1 : g * s.fr.b₁ * g⁻¹ = s.fr.b₂ := y5_key hsrel.z_sq hsrel.b2_sq (y5_rel_b1 hrel)
  have hb2 : g * s.fr.b₂ * g⁻¹ = s.fr.b₁ :=
    y5_key hsrel.z_sq (show s.fr.b₁ ^ 2 = s.fr.z from rfl) (by rw [y5_rel_b2 hrel, hc12b])
  have hz : g * s.fr.z * g⁻¹ = s.fr.z := by
    have hb1sq : g * s.fr.b₁ ^ 2 * g⁻¹ = s.fr.b₂ ^ 2 := by
      calc g * s.fr.b₁ ^ 2 * g⁻¹ = (g * s.fr.b₁ * g⁻¹) ^ 2 := by
            rw [pow_two, pow_two]; group
        _ = s.fr.b₂ ^ 2 := by rw [hb1]
    calc g * s.fr.z * g⁻¹ = g * s.fr.b₁ ^ 2 * g⁻¹ := rfl
      _ = s.fr.b₂ ^ 2 := hb1sq
      _ = s.fr.z := hsrel.b2_sq
  have hh0 : g * s.fr.h₀ * g⁻¹ = s.fr.z * s.fr.h₀ := by
    have h00 : s.fr.h₀ * s.fr.h₀ = 1 := by rw [← pow_two, hsrel.h0_sq]
    have h0inv : s.fr.h₀⁻¹ = s.fr.h₀ := inv_eq_of_mul_eq_one_right h00
    have hA : s.fr.h₀ * g * s.fr.h₀⁻¹ = s.fr.z * g := by
      calc s.fr.h₀ * g * s.fr.h₀⁻¹
          = (s.fr.h₀ * g * s.fr.h₀⁻¹ * g⁻¹) * g := by group
        _ = s.fr.z * g := by rw [y5_rel_h0 hrel]
    have hB : g * s.fr.h₀⁻¹ = s.fr.h₀ * s.fr.z * g := by
      calc g * s.fr.h₀⁻¹ = (s.fr.h₀ * s.fr.h₀) * (g * s.fr.h₀⁻¹) := by rw [h00, one_mul]
        _ = s.fr.h₀ * (s.fr.h₀ * g * s.fr.h₀⁻¹) := by group
        _ = s.fr.h₀ * (s.fr.z * g) := by rw [hA]
        _ = s.fr.h₀ * s.fr.z * g := by group
    have hC : g * s.fr.h₀ * g⁻¹ = s.fr.h₀ * s.fr.z := by
      calc g * s.fr.h₀ * g⁻¹ = g * s.fr.h₀⁻¹ * g⁻¹ := by rw [h0inv]
        _ = (g * s.fr.h₀⁻¹) * g⁻¹ := by group
        _ = (s.fr.h₀ * (s.fr.z * g)) * g⁻¹ := by rw [hB]; group
        _ = s.fr.h₀ * s.fr.z := by group
    rw [hC]
    exact (y5_z_comm_S hH (s3_h₀_mem_S s)).symm
  exact ⟨ha1, ha2, hb1, hb2, hz, hh0⟩

theorem y5_comm_a_g {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hact : ActsAs L g s.fr'.σ) :
    ⁅y5a s, g⁆ = s.fr.a₁ * s.fr.a₂ * s.fr.z := by
  obtain ⟨ha1, ha2, hb1, hb2, hz, hh0⟩ := y5_g_swap hH hg2 hact
  have hsrel := s3_srel hH.hS hH.hZ s
  have hc12b : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.b1b2).eq
  have hww : (s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂) = 1 := by
    rw [← pow_two]; exact y5_w_sq hH
  have hwinv : (s.fr.b₁ * s.fr.b₂)⁻¹ = s.fr.b₁ * s.fr.b₂ :=
    inv_eq_of_mul_eq_one_right hww
  have ha2inv : s.fr.a₂⁻¹ = s.fr.a₂ * s.fr.z := by
    rw [inv_eq_iff_mul_eq_one]
    calc s.fr.a₂ * (s.fr.a₂ * s.fr.z) = (s.fr.a₂ * s.fr.a₂) * s.fr.z := by group
      _ = s.fr.z * s.fr.z := by
            have h : s.fr.a₂ * s.fr.a₂ = s.fr.z := by rw [← pow_two, hsrel.a2_sq]
            rw [h]
      _ = 1 := by rw [← pow_two, hsrel.z_sq]
  have hga : g * y5a s * g⁻¹ = s.fr.a₂ * (s.fr.b₁ * s.fr.b₂) := by
    have hconj : g * y5a s * g⁻¹ = s.fr.a₂ * s.fr.b₂ * s.fr.b₁ := by
      rw [y5a]
      rw [show g * (s.fr.a₁ * s.fr.b₁ * s.fr.b₂) * g⁻¹
          = (g * s.fr.a₁ * g⁻¹) * (g * s.fr.b₁ * g⁻¹) * (g * s.fr.b₂ * g⁻¹)
          from by group]
      rw [ha1, hb1, hb2]
    rw [hconj]
    calc s.fr.a₂ * s.fr.b₂ * s.fr.b₁ = s.fr.a₂ * (s.fr.b₂ * s.fr.b₁) := by group
      _ = s.fr.a₂ * (s.fr.b₁ * s.fr.b₂) := by rw [hc12b.symm]
  have hmain : (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₂ * (s.fr.b₁ * s.fr.b₂))⁻¹
      = s.fr.a₁ * s.fr.a₂ * s.fr.z := by
    rw [mul_inv_rev, hwinv]
    calc s.fr.a₁ * (s.fr.b₁ * s.fr.b₂) * ((s.fr.b₁ * s.fr.b₂) * s.fr.a₂⁻¹)
        = s.fr.a₁ * ((s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂)) * s.fr.a₂⁻¹ := by group
      _ = s.fr.a₁ * s.fr.a₂⁻¹ := by rw [hww]; group
      _ = s.fr.a₁ * (s.fr.a₂ * s.fr.z) := by rw [ha2inv]
      _ = s.fr.a₁ * s.fr.a₂ * s.fr.z := by group
  rw [commutatorElement_def]
  calc y5a s * g * (y5a s)⁻¹ * g⁻¹ = y5a s * (g * y5a s * g⁻¹)⁻¹ := by group
    _ = (s.fr.a₁ * (s.fr.b₁ * s.fr.b₂)) * (s.fr.a₂ * (s.fr.b₁ * s.fr.b₂))⁻¹ := by
          rw [hga, y5a]; group
    _ = s.fr.a₁ * s.fr.a₂ * s.fr.z := hmain

theorem y5_g_cent_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hact : ActsAs L g s.fr'.σ) :
    ∀ f ∈ s.fr.F, g * f * g⁻¹ = f := by
  obtain ⟨ha1, ha2, hb1, hb2, hz, hh0⟩ := y5_g_swap hH hg2 hact
  have hsrel := s3_srel hH.hS hH.hZ s
  have hc12 : s.fr.a₁ * s.fr.a₂ = s.fr.a₂ * s.fr.a₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.a1a2).eq
  have hc12b : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.b1b2).eq
  intro f hf
  rw [SFrame.F] at hf
  refine Subgroup.closure_induction (p := fun f _ => g * f * g⁻¹ = f) ?_ ?_ ?_ ?_ hf
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [show g * (s.fr.a₁ * s.fr.a₂) * g⁻¹
          = (g * s.fr.a₁ * g⁻¹) * (g * s.fr.a₂ * g⁻¹) from by group]
      rw [ha1, ha2]
      exact hc12.symm
    · rw [show g * (s.fr.b₁ * s.fr.b₂) * g⁻¹
          = (g * s.fr.b₁ * g⁻¹) * (g * s.fr.b₂ * g⁻¹) from by group]
      rw [hb1, hb2]
      exact hc12b.symm
    · exact hz
  · group
  · intro x y _ _ hx hy
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) from by group, hx, hy]
  · intro x _ hx
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ from by group, hx]

theorem y5_g_cent_V {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hact : ActsAs L g s.fr'.σ) :
    ∀ v ∈ cen s.fr.B, g * v * g⁻¹ = v := by
  obtain ⟨ha1, ha2, hb1, hb2, hz, hh0⟩ := y5_g_swap hH hg2 hact
  have hsrel := s3_srel hH.hS hH.hZ s
  have hc12b : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    (commutatorElement_eq_one_iff_commute.mp hsrel.b1b2).eq
  have hcen : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hH.hLF.fact14.2.2.1.1
  have hb1b2 : g * (s.fr.b₁ * s.fr.b₂) * g⁻¹ = s.fr.b₁ * s.fr.b₂ := by
    rw [show g * (s.fr.b₁ * s.fr.b₂) * g⁻¹
        = (g * s.fr.b₁ * g⁻¹) * (g * s.fr.b₂ * g⁻¹) from by group]
    rw [hb1, hb2]
    exact hc12b.symm
  intro v hv
  rw [hcen] at hv
  refine Subgroup.closure_induction (p := fun v _ => g * v * g⁻¹ = v) ?_ ?_ ?_ ?_ hv
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hb1b2
    · exact hz
  · group
  · intro x y _ _ hx hy
    rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) from by group, hx, hy]
  · intro x _ hx
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ from by group, hx]

end CFSG.OddStandard.HigherRank.YamadaG23
