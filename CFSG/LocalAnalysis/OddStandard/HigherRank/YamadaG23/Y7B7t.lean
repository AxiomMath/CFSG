module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7s

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M7_sq_mem_M3 (c : Ctx7 G L) (hb : B5Std c) : ∀ y ∈ M7 c.s, y ^ 2 ∈ M3 c.s := by
  obtain ⟨u, huM7, hut, hu2, -⟩ := y7b_exists_seed3 c hb
  obtain ⟨k, hkN, -, -, htrans, -, -⟩ := y7b_exists_k c hb
  have hLH : L ≤ c.s.H := s3_L_le_H c.s hb.hH.hS
  have hM7X7 : M7 c.s ≤ X7 c.s := (y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb)
  have hkM7 : k ∈ normalizer (M7 c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => (y7b_M7_normal c hb).2 k hkN x hx
  have hZ : ∀ y ∈ M7 c.s, ⁅y, c.s.t⁆ ∈ M3 c.s → y ∈ y7bBM c.s := by
    intro y hyM7 hyt
    have hyX7 : y ∈ X7 c.s := hM7X7 hyM7
    have h1 : y ∈ C7 c.s ⊓ y7bX0 c.s :=
      Subgroup.mem_inf.mpr ⟨y7b_M7_le_C7 c hb hyM7, (y7b_X0_iff c hb hyX7).mpr hyt⟩
    rw [y7b_C7_inf_X0 c hb] at h1
    have h2 : y ∈ M7 c.s ⊓ y7bW c.s := Subgroup.mem_inf.mpr ⟨hyM7, h1⟩
    rwa [y7b_M7_inf_W c hb] at h2
  have hcov := y7b_cover_gen c hb hkN htrans (Y := M7 c.s) (Z := y7bBM c.s)
    hM7X7 hkM7 hZ huM7 hut
  intro y hy
  rcases hcov y hy with hyBM | ⟨i, a, haBM, hy_eq⟩
  · exact y7b_BM_sq_mem_M3 c hb y hyBM
  · have hkiN : k ^ i ∈ normIn L c.s.fr.B := Subgroup.pow_mem _ hkN i
    have hkiNM3 : k ^ i ∈ normalizer (M3 c.s : Set G) :=
      y7b_N_le_NM3 c hb ⟨hLH hkiN.1, hkiN.2⟩
    have huiM7 : k ^ i * u * (k ^ i)⁻¹ ∈ M7 c.s :=
      (y7b_M7_normal c hb).2 (k ^ i) hkiN u huM7
    have huiX7 : k ^ i * u * (k ^ i)⁻¹ ∈ X7 c.s := hM7X7 huiM7
    have huiNM3 : k ^ i * u * (k ^ i)⁻¹ ∈ normalizer (M3 c.s : Set G) :=
      (Subgroup.mem_inf.mp (y7b_X7_le_X c huiX7)).2
    have hui2 : (k ^ i * u * (k ^ i)⁻¹) ^ 2 ∈ M3 c.s := by
      have h := (Subgroup.mem_normalizer_iff.mp hkiNM3 (u ^ 2)).mp hu2
      have heq : (k ^ i * u * (k ^ i)⁻¹) ^ 2 = k ^ i * u ^ 2 * (k ^ i)⁻¹ := by
        rw [conj_pow]
      rwa [heq]
    have ha2 : a ^ 2 ∈ M3 c.s := y7b_BM_sq_mem_M3 c hb a haBM
    have hcomm : ⁅a, k ^ i * u * (k ^ i)⁻¹⁆ ∈ M3 c.s := by
      have h := ((y7b_mem_X7 c hb).mp huiX7).2 a haBM
      simpa only [commutatorElement_inv] using (M3 c.s).inv_mem h
    have hconj : (k ^ i * u * (k ^ i)⁻¹) * ⁅a, k ^ i * u * (k ^ i)⁻¹⁆ *
        (k ^ i * u * (k ^ i)⁻¹)⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp huiNM3 _).mp hcomm
    rw [hy_eq]
    have hkey : (k ^ i * u * (k ^ i)⁻¹ * a) ^ 2 =
        ((k ^ i * u * (k ^ i)⁻¹) * ⁅a, k ^ i * u * (k ^ i)⁻¹⁆ *
          (k ^ i * u * (k ^ i)⁻¹)⁻¹) * (k ^ i * u * (k ^ i)⁻¹) ^ 2 * a ^ 2 := by
      set w : G := k ^ i * u * (k ^ i)⁻¹
      rw [commutatorElement_def, pow_two]
      group
    rw [hkey]
    exact (M3 c.s).mul_mem ((M3 c.s).mul_mem hconj hui2) ha2

theorem y7b_M7_secProp (c : Ctx7 G L) (hb : B5Std c) :
    SecProp (M7 c.s) (M3 c.s) (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y)) := by
  refine y7b_secProp_of_sq_mem ?_ ?_ (y7b_M7_sq_mem_M3 c hb)
  · exact (le_sup_right : M3 c.s ≤ y7bBM c.s).trans (y7b_BM_le_M7 c hb)
  · intro v hv n hn
    have hvX : v ∈ y7bX c.s :=
      y7b_X7_le_X c ((y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb) hv)
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hvX).2 n).mp hn

theorem y7b_g_comm_BM (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ a ∈ y7bBM c.s, ⁅c.g, a⁆ ∈ M3 c.s := by
  intro a ha
  obtain ⟨b, hbB, m, hmM3, rfl⟩ := (y7b_mem_BM c hb).mp ha
  have hF : c.s.fr.F ≤ M3 c.s := by rw [← y7b_B_inf_M3 c hb]; exact inf_le_right
  have hgb : ⁅c.g, b⁆ ∈ c.s.fr.F :=
    y7b_g_comm_NL c hb hRT b ⟨f3_B_le_L c.s hbB, Subgroup.le_normalizer hbB⟩
  have hgm : ⁅c.g, m⁆ = 1 := by
    rw [commutatorElement_def, y7b_g_cent_M3 c hb hRT m hmM3]
    group
  have hkey : ⁅c.g, b * m⁆ = ⁅c.g, b⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, hgm]
    group
  rw [hkey]
  exact hF hgb

theorem y7b_g_comm_M7 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ m ∈ M7 c.s, ⁅c.g, m⁆ ∈ M3 c.s := by
  obtain ⟨u, huM7, hut, -, hgu⟩ := y7b_exists_seed3 c hb
  obtain ⟨k, hkN, -, -, htrans, -, -⟩ := y7b_exists_k c hb
  have hLH : L ≤ c.s.H := s3_L_le_H c.s hb.hH.hS
  have hM7X7 : M7 c.s ≤ X7 c.s := (y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb)
  have hkM7 : k ∈ normalizer (M7 c.s : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => (y7b_M7_normal c hb).2 k hkN x hx
  have hZ : ∀ y ∈ M7 c.s, ⁅y, c.s.t⁆ ∈ M3 c.s → y ∈ y7bBM c.s := by
    intro y hyM7 hyt
    have hyX7 : y ∈ X7 c.s := hM7X7 hyM7
    have h1 : y ∈ C7 c.s ⊓ y7bX0 c.s :=
      Subgroup.mem_inf.mpr ⟨y7b_M7_le_C7 c hb hyM7, (y7b_X0_iff c hb hyX7).mpr hyt⟩
    rw [y7b_C7_inf_X0 c hb] at h1
    have h2 : y ∈ M7 c.s ⊓ y7bW c.s := Subgroup.mem_inf.mpr ⟨hyM7, h1⟩
    rwa [y7b_M7_inf_W c hb] at h2
  have hcov := y7b_cover_gen c hb hkN htrans (Y := M7 c.s) (Z := y7bBM c.s)
    hM7X7 hkM7 hZ huM7 hut
  have hF : c.s.fr.F ≤ M3 c.s := by rw [← y7b_B_inf_M3 c hb]; exact inf_le_right
  intro m hm
  rcases hcov m hm with hmBM | ⟨i, a, haBM, hm_eq⟩
  · exact y7b_g_comm_BM c hb hRT m hmBM
  · have hkiN : k ^ i ∈ normIn L c.s.fr.B := Subgroup.pow_mem _ hkN i
    have hkiNM3 : k ^ i ∈ normalizer (M3 c.s : Set G) :=
      y7b_N_le_NM3 c hb ⟨hLH hkiN.1, hkiN.2⟩
    have huiM7 : k ^ i * u * (k ^ i)⁻¹ ∈ M7 c.s :=
      (y7b_M7_normal c hb).2 (k ^ i) hkiN u huM7
    have huiX7 : k ^ i * u * (k ^ i)⁻¹ ∈ X7 c.s := hM7X7 huiM7
    have huiNM3 : k ^ i * u * (k ^ i)⁻¹ ∈ normalizer (M3 c.s : Set G) :=
      (Subgroup.mem_inf.mp (y7b_X7_le_X c huiX7)).2
    have hcu : ⁅c.g, u⁆ ∈ M3 c.s := hgu hRT
    have hfM3 : ⁅c.g, k ^ i⁆ ∈ M3 c.s :=
      hF (y7b_g_comm_NL c hb hRT (k ^ i) hkiN)
    have hxcu : k ^ i * ⁅c.g, u⁆ * (k ^ i)⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp hkiNM3 ⁅c.g, u⁆).mp hcu
    have hui_f : (k ^ i * u * (k ^ i)⁻¹) * (⁅c.g, k ^ i⁆)⁻¹ *
        (k ^ i * u * (k ^ i)⁻¹)⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp huiNM3 (⁅c.g, k ^ i⁆)⁻¹).mp
        ((M3 c.s).inv_mem hfM3)
    have hgui : ⁅c.g, k ^ i * u * (k ^ i)⁻¹⁆ ∈ M3 c.s := by
      have hkey : c.g * (k ^ i * u * (k ^ i)⁻¹) * c.g⁻¹ =
          ⁅c.g, k ^ i⁆ * (k ^ i * ⁅c.g, u⁆ * (k ^ i)⁻¹) *
            (k ^ i * u * (k ^ i)⁻¹) * (⁅c.g, k ^ i⁆)⁻¹ := by
        set x : G := k ^ i
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [commutatorElement_def, hkey]
      have heq : (⁅c.g, k ^ i⁆ * (k ^ i * ⁅c.g, u⁆ * (k ^ i)⁻¹) *
            (k ^ i * u * (k ^ i)⁻¹) * (⁅c.g, k ^ i⁆)⁻¹) *
            (k ^ i * u * (k ^ i)⁻¹)⁻¹ =
          ⁅c.g, k ^ i⁆ * (k ^ i * ⁅c.g, u⁆ * (k ^ i)⁻¹) *
            ((k ^ i * u * (k ^ i)⁻¹) * (⁅c.g, k ^ i⁆)⁻¹ *
              (k ^ i * u * (k ^ i)⁻¹)⁻¹) := by
        set x : G := k ^ i
        group
      rw [heq]
      exact (M3 c.s).mul_mem ((M3 c.s).mul_mem hfM3 hxcu) hui_f
    have haM3 : ⁅c.g, a⁆ ∈ M3 c.s := y7b_g_comm_BM c hb hRT a haBM
    have ha_conj : (k ^ i * u * (k ^ i)⁻¹) * ⁅c.g, a⁆ *
        (k ^ i * u * (k ^ i)⁻¹)⁻¹ ∈ M3 c.s :=
      (Subgroup.mem_normalizer_iff.mp huiNM3 ⁅c.g, a⁆).mp haM3
    rw [hm_eq, commutatorElement_mul_right_eq_mul_conj]
    have heq2 : ⁅c.g, k ^ i * u * (k ^ i)⁻¹⁆ * (k ^ i * u * (k ^ i)⁻¹) * ⁅c.g, a⁆ *
          (k ^ i * u * (k ^ i)⁻¹)⁻¹ =
        ⁅c.g, k ^ i * u * (k ^ i)⁻¹⁆ *
          ((k ^ i * u * (k ^ i)⁻¹) * ⁅c.g, a⁆ * (k ^ i * u * (k ^ i)⁻¹)⁻¹) := by
      set x : G := k ^ i
      group
    rw [heq2]
    exact (M3 c.s).mul_mem hgui ha_conj

end CFSG.OddStandard.HigherRank.YamadaG23
