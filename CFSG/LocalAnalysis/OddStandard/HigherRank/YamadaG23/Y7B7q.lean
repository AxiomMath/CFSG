module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7p

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_cosets_W_BM (c : Ctx7 G L) (hb : B5Std c) :
    ∀ a ∈ y7bW c.s, ∀ b ∈ y7bW c.s, a ∈ y7bBM c.s ∨ b ∈ y7bBM c.s ∨ a⁻¹ * b ∈ y7bBM c.s := by
  intro a ha b hbW
  obtain ⟨w₁, hw₁, ha | ha⟩ := (y7b_mem_W c hb).mp ha
  · exact Or.inl (ha ▸ hw₁)
  · obtain ⟨w₂, hw₂, hb2 | hb2⟩ := (y7b_mem_W c hb).mp hbW
    · exact Or.inr (Or.inl (hb2 ▸ hw₂))
    · refine Or.inr (Or.inr ?_)
      have hmem : w₁⁻¹ * w₂ ∈ y7bBM c.s :=
        (y7bBM c.s).mul_mem ((y7bBM c.s).inv_mem hw₁) hw₂
      have hmem' : c.s.t⁻¹ * (w₁⁻¹ * w₂) * c.s.t ∈ y7bBM c.s :=
        ((Subgroup.mem_normalizer_iff''.mp (y7b_t_norm_BM c hb)) (w₁⁻¹ * w₂)).mp hmem
      rw [ha, hb2]
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hmem'

theorem y7b_extCtx2 (c : Ctx7 G L) (hb : B5Std c) :
    ExtCtx (y7bBM c.s) (y7bW c.s) (C7 c.s) (normIn L c.s.fr.B) := by
  refine ⟨y7b_BM_le_W c hb, y7b_W_le_C7 c hb, ?_, ?_, ?_, ?_, ?_, y7b_cosets_W_BM c hb⟩
  · intro n hn y hy
    exact (y7b_C7_normal c hb).2 n ⟨s3_L_le_H c.s hb.hH.hS hn.1, hn.2⟩ y hy
  · intro y hy p hp
    exact y7b_X_norm_BM c hb y (y7b_X7_le_X c (y7b_C7_le_X7 c hb hy)) p hp
  · intro n hn p hp
    exact y7b_X_norm_BM c hb n
      (y7b_N_le_X c hb ⟨s3_L_le_H c.s hb.hH.hS hn.1, hn.2⟩) p hp
  · intro y hy a ha
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.mem_inf.mp (y7b_X7_le_X c (y7b_C7_le_X7 c hb hy))).1 a).mp ha
  · intro n hn a ha
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.mem_inf.mp (y7b_N_le_X c hb ⟨s3_L_le_H c.s hb.hH.hS hn.1, hn.2⟩)).1 a).mp ha

theorem y7b_cover2 (c : Ctx7 G L) (hb : B5Std c) {u : G} (hu : u ∈ C7 c.s)
    (hut : ⁅u, c.s.t⁆ ∉ M3 c.s) :
    ∀ y ∈ C7 c.s, y ∈ y7bW c.s ∨
      ∃ m ∈ normIn L c.s.fr.B, ∃ a ∈ y7bW c.s, y = m * u * m⁻¹ * a := by
  obtain ⟨k, hkN, -, -, htrans, -, -⟩ := y7b_exists_k c hb
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hkY : k ∈ normalizer (C7 c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => (y7b_C7_normal c hb).2 k hkNH x hx
  have hZ : ∀ y ∈ C7 c.s, ⁅y, c.s.t⁆ ∈ M3 c.s → y ∈ y7bW c.s := by
    intro y hy hyt
    have hyX0 : y ∈ y7bX0 c.s := (y7b_X0_iff c hb (y7b_C7_le_X7 c hb hy)).mpr hyt
    have hmem : y ∈ C7 c.s ⊓ y7bX0 c.s := Subgroup.mem_inf.mpr ⟨hy, hyX0⟩
    rwa [y7b_C7_inf_X0 c hb] at hmem
  have hcov := y7b_cover_gen c hb hkN htrans (Y := C7 c.s) (Z := y7bW c.s)
    (y7b_C7_le_X7 c hb) hkY hZ hu hut
  intro y hy
  rcases hcov y hy with h | ⟨i, a, ha, hy_eq⟩
  · exact Or.inl h
  · exact Or.inr ⟨k ^ i, Subgroup.pow_mem (normIn L c.s.fr.B) hkN i, a, ha, hy_eq⟩

theorem y7b_C7_sq_mem_BM (c : Ctx7 G L) (hb : B5Std c) : ∀ y ∈ C7 c.s, y ^ 2 ∈ y7bBM c.s := by
  obtain ⟨u, hu, hut, hu2, -, -⟩ := y7b_exists_seed2 c hb
  exact ext_sq (y7b_extCtx2 c hb) hu (Subgroup.mem_sup_right hu2) (y7b_cover2 c hb hu hut)

theorem y7b_C7_comm_mem_BM (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ C7 c.s, ∀ y' ∈ C7 c.s, ⁅y, y'⁆ ∈ y7bBM c.s :=
  ext_comm_mem (y7b_extCtx2 c hb) (y7b_C7_sq_mem_BM c hb)

theorem y7b_hfix2 (c : Ctx7 G L) (hb : B5Std c) {k : G} (hkN : k ∈ normIn L c.s.fr.B)
    (hfp : ∀ u ∈ y7bBM c.s, u⁻¹ * (k * u * k⁻¹) ∈ M3 c.s → u ∈ M3 c.s) :
    ∀ y ∈ C7 c.s, y⁻¹ * (k * y * k⁻¹) ∈ y7bW c.s → y ∈ y7bW c.s := by
  intro y hy h
  have hyX0 : y ∈ y7bX0 c.s :=
    y7b_hfix1 c hb hkN hfp y (y7b_C7_le_X7 c hb hy) (y7b_W_le_X0 c hb h)
  have hmem : y ∈ C7 c.s ⊓ y7bX0 c.s := Subgroup.mem_inf.mpr ⟨hy, hyX0⟩
  rwa [y7b_C7_inf_X0 c hb] at hmem

theorem y7b_M7_inf_W (c : Ctx7 G L) (hb : B5Std c) : M7 c.s ⊓ y7bW c.s = y7bBM c.s := by
  obtain ⟨k, hkN, hk3, -, -, hfp, hknorm⟩ := y7b_exists_k c hb
  have hkn : ∀ n ∈ normIn L c.s.fr.B, ∃ p ∈ y7bBM c.s,
      n * k * n⁻¹ = k * p ∨ n * k * n⁻¹ = k⁻¹ * p := by
    intro n hn
    obtain ⟨b, hbB, hbk⟩ := hknorm n hn
    exact ⟨b, Subgroup.mem_sup_left hbB, hbk⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM7, hxW⟩ := Subgroup.mem_inf.mp hx
    rw [M7] at hxM7
    exact ext_nu (y7b_extCtx2 c hb) (y7b_C7_sq_mem_BM c hb) hkN
      (by rw [hk3]; exact (y7bBM c.s).one_mem) hkn (y7b_hfix2 c hb hkN hfp) x hxW hxM7
  · refine le_inf ?_ (y7b_BM_le_W c hb)
    rw [M7]
    exact le_sup_right

theorem y7b_BM_le_M7 (c : Ctx7 G L) (hb : B5Std c) : y7bBM c.s ≤ M7 c.s := by
  rw [M7]
  exact le_sup_right

theorem y7b_M7_le_C7 (c : Ctx7 G L) (hb : B5Std c) : M7 c.s ≤ C7 c.s := by
  rw [M7]
  refine sup_le ?_ ((y7b_BM_le_W c hb).trans (y7b_W_le_C7 c hb))
  rw [Subgroup.commutator_le]
  intro y hy n hn
  have hnH : n ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hn.1, hn.2⟩
  have h1 : n * y⁻¹ * n⁻¹ ∈ C7 c.s := (y7b_C7_normal c hb).2 n hnH y⁻¹ ((C7 c.s).inv_mem hy)
  have h2 : y * (n * y⁻¹ * n⁻¹) ∈ C7 c.s := (C7 c.s).mul_mem hy h1
  rw [show ⁅y, n⁆ = y * (n * y⁻¹ * n⁻¹) by rw [commutatorElement_def]; group]
  exact h2

theorem y7b_M7_normal (c : Ctx7 G L) (hb : B5Std c) :
    (∀ y ∈ C7 c.s, ∀ x ∈ M7 c.s, y * x * y⁻¹ ∈ M7 c.s) ∧
      ∀ n ∈ normIn L c.s.fr.B, ∀ x ∈ M7 c.s, n * x * n⁻¹ ∈ M7 c.s := by
  unfold M7
  exact ext_normal (y7b_extCtx2 c hb)

end CFSG.OddStandard.HigherRank.YamadaG23
