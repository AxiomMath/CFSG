module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3K

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem conj_mem_cen {B : Subgroup G} {n v : G} (hn : n ∈ normalizer (B : Set G))
    (hv : v ∈ cen B) : n * v * n⁻¹ ∈ cen B := by
  obtain ⟨hvB, hvc⟩ := Subgroup.mem_inf.mp hv
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn v).mp hvB, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hvc ⊢
  intro b hb
  have hb' : n⁻¹ * b * n ∈ B :=
    (Subgroup.mem_normalizer_iff''.mp hn b).mp hb
  have hcomm := hvc (n⁻¹ * b * n) hb'
  calc b * (n * v * n⁻¹) = n * ((n⁻¹ * b * n) * v) * n⁻¹ := by group
    _ = n * (v * (n⁻¹ * b * n)) * n⁻¹ := by rw [hcomm]
    _ = (n * v * n⁻¹) * b := by group

private theorem mul_comm_of_conj {a b : G} (h : a * b * a⁻¹ = b) : b * a = a * b :=
  (mul_inv_eq_iff_eq_mul.mp h).symm

theorem f3_N_decomp {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ f3N s, ∃ ℓ ∈ normIn L s.fr.B, ∃ a ∈ f3X0 s, n = ℓ * a := by
  intro n hn
  obtain ⟨hnH, hnN⟩ := Subgroup.mem_inf.mp hn
  obtain ⟨w, hwV, hzV, hw1, hz1, hwz, _hw2, hz2, _hwz_comm, hVenum⟩ := f3_V_elems hH
  have hz2mul : s.fr.z * s.fr.z = 1 := by rw [← pow_two, hz2]
  have hnzV : n * s.fr.z * n⁻¹ ∈ cen s.fr.B := conj_mem_cen hnN hzV
  have hnz1 : n * s.fr.z * n⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc s.fr.z = n⁻¹ * (n * s.fr.z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  obtain ⟨k, hk, _hk3, _hk1, _hkfix, hktrans, _hknorm⟩ := f3_exists_k hH
  obtain ⟨i, hi⟩ := hktrans s.fr.z hzV hz1 (n * s.fr.z * n⁻¹) hnzV hnz1
  have hki : k ^ i ∈ normIn L s.fr.B := Subgroup.pow_mem _ hk i
  have hkiN : k ^ i ∈ normalizer (s.fr.B : Set G) := (Subgroup.mem_inf.mp hki).2
  have hmz : ((k ^ i)⁻¹ * n) * s.fr.z * ((k ^ i)⁻¹ * n)⁻¹ = s.fr.z := by
    calc ((k ^ i)⁻¹ * n) * s.fr.z * ((k ^ i)⁻¹ * n)⁻¹
        = (k ^ i)⁻¹ * (n * s.fr.z * n⁻¹) * (k ^ i) := by group
      _ = (k ^ i)⁻¹ * (k ^ i * s.fr.z * (k ^ i)⁻¹) * (k ^ i) := by rw [← hi]
      _ = s.fr.z := by group
  have hmN : (k ^ i)⁻¹ * n ∈ normalizer (s.fr.B : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hkiN) hnN
  have hmwV : ((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹ ∈ cen s.fr.B :=
    conj_mem_cen hmN hwV
  have hmw1 : ((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹ ≠ 1 := by
    intro h
    apply hw1
    calc w = ((k ^ i)⁻¹ * n)⁻¹ * (((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹)
          * ((k ^ i)⁻¹ * n) := by group
      _ = 1 := by rw [h]; group
  have hmz' : ((k ^ i)⁻¹ * n)⁻¹ * s.fr.z * ((k ^ i)⁻¹ * n) = s.fr.z := by
    have h : ((k ^ i)⁻¹ * n)⁻¹ * (((k ^ i)⁻¹ * n) * s.fr.z * ((k ^ i)⁻¹ * n)⁻¹)
        * ((k ^ i)⁻¹ * n) = s.fr.z := by group
    rwa [hmz] at h
  have hmwz : ((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹ ≠ s.fr.z := by
    intro h
    apply hwz
    calc w = ((k ^ i)⁻¹ * n)⁻¹ * (((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹)
          * ((k ^ i)⁻¹ * n) := by group
      _ = ((k ^ i)⁻¹ * n)⁻¹ * s.fr.z * ((k ^ i)⁻¹ * n) := by rw [h]
      _ = s.fr.z := hmz'
  rcases hVenum (((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹) hmwV with h1 | h2 | h3 | h4
  · exact absurd h1 hmw1
  · exact absurd h2 hmwz
  ·
    refine ⟨k ^ i, hki, (k ^ i)⁻¹ * n, ?_, by group⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem s.H
        (s3_L_le_H s hH.hS (Subgroup.inv_mem L (Subgroup.mem_inf.mp hki).1)) hnH
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rcases hVenum v hv with hv1 | hvz | hvw | hvzw
      · rw [hv1]; group
      · rw [hvz]; exact mul_comm_of_conj hmz
      · rw [hvw]; exact mul_comm_of_conj h3
      · rw [hvzw]; exact mul_comm_of_conj (by
          calc ((k ^ i)⁻¹ * n) * (s.fr.z * w) * ((k ^ i)⁻¹ * n)⁻¹
              = (((k ^ i)⁻¹ * n) * s.fr.z * ((k ^ i)⁻¹ * n)⁻¹)
                * (((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹) := by group
            _ = s.fr.z * w := by rw [hmz, h3])
  ·
    obtain ⟨τ, _hτT, hτS, hτN, hτprop⟩ := f3_exists_tau hH
    have hA := lfactsA_of_setting hH.hS hH.hZ s
    have hzcen : s.fr.z ∈ cen s.fr.S := by
      rw [s3_cen_S s hA]; exact Subgroup.mem_zpowers s.fr.z
    have hzcent := (Subgroup.mem_inf.mp hzcen).2
    have hτz : τ * s.fr.z * τ⁻¹ = s.fr.z := by
      have hcomm : τ * s.fr.z = s.fr.z * τ :=
        Subgroup.mem_centralizer_iff.mp hzcent τ hτS
      rw [hcomm]; group
    have hτz' : τ⁻¹ * s.fr.z * τ = s.fr.z := by
      have h : τ⁻¹ * (τ * s.fr.z * τ⁻¹) * τ = s.fr.z := by group
      rwa [hτz] at h
    have hzwV : s.fr.z * w ∈ cen s.fr.B := Subgroup.mul_mem _ hzV hwV
    have hzw1 : s.fr.z * w ≠ 1 := by
      intro h
      apply hwz
      calc w = (s.fr.z * s.fr.z) * w := by rw [hz2mul, one_mul]
        _ = s.fr.z * (s.fr.z * w) := by group
        _ = s.fr.z * 1 := by rw [h]
        _ = s.fr.z := by rw [mul_one]
    have hzwz : s.fr.z * w ≠ s.fr.z := by
      intro h
      apply hw1
      have h' : s.fr.z * w = s.fr.z * 1 := by rw [h, mul_one]
      exact mul_left_cancel h'
    have hτ_w : τ * w * τ⁻¹ = s.fr.z * w := hτprop w hwV hw1 hwz
    have hτ_zw : τ * (s.fr.z * w) * τ⁻¹ = w := by
      have h := hτprop (s.fr.z * w) hzwV hzw1 hzwz
      rwa [show s.fr.z * (s.fr.z * w) = w from by
        calc s.fr.z * (s.fr.z * w) = (s.fr.z * s.fr.z) * w := by group
          _ = w := by rw [hz2mul, one_mul]] at h
    have hτ_w' : τ⁻¹ * w * τ = s.fr.z * w := by
      have h : τ⁻¹ * (τ * (s.fr.z * w) * τ⁻¹) * τ = s.fr.z * w := by group
      rwa [hτ_zw] at h
    have hτ_zw' : τ⁻¹ * (s.fr.z * w) * τ = w := by
      have h : τ⁻¹ * (τ * w * τ⁻¹) * τ = w := by group
      rwa [hτ_w] at h
    have hm_zw : ((k ^ i)⁻¹ * n) * (s.fr.z * w) * ((k ^ i)⁻¹ * n)⁻¹ = w := by
      calc ((k ^ i)⁻¹ * n) * (s.fr.z * w) * ((k ^ i)⁻¹ * n)⁻¹
          = (((k ^ i)⁻¹ * n) * s.fr.z * ((k ^ i)⁻¹ * n)⁻¹)
            * (((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹) := by group
        _ = s.fr.z * (s.fr.z * w) := by rw [hmz, h4]
        _ = w := by
              calc s.fr.z * (s.fr.z * w) = (s.fr.z * s.fr.z) * w := by group
                _ = w := by rw [hz2mul, one_mul]
    refine ⟨k ^ i * τ, ?_, τ⁻¹ * ((k ^ i)⁻¹ * n), ?_, by group⟩
    ·
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem L (Subgroup.mem_inf.mp hki).1 (s3_S_le_L s hτS)
      · exact Subgroup.mul_mem _ hkiN hτN
    ·
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mul_mem s.H
          (Subgroup.inv_mem s.H (s3_L_le_H s hH.hS (s3_S_le_L s hτS)))
          (Subgroup.mul_mem s.H
            (Subgroup.inv_mem s.H (s3_L_le_H s hH.hS (Subgroup.mem_inf.mp hki).1)) hnH)
      · rw [Subgroup.mem_centralizer_iff]
        intro v hv
        rcases hVenum v hv with hv1 | hvz | hvw | hvzw
        · rw [hv1]; group
        · rw [hvz]; exact mul_comm_of_conj (by
            calc τ⁻¹ * ((k ^ i)⁻¹ * n) * s.fr.z * (τ⁻¹ * ((k ^ i)⁻¹ * n))⁻¹
                = τ⁻¹ * (((k ^ i)⁻¹ * n) * s.fr.z * ((k ^ i)⁻¹ * n)⁻¹) * τ := by group
              _ = τ⁻¹ * s.fr.z * τ := by rw [hmz]
              _ = s.fr.z := hτz')
        · rw [hvw]; exact mul_comm_of_conj (by
            calc τ⁻¹ * ((k ^ i)⁻¹ * n) * w * (τ⁻¹ * ((k ^ i)⁻¹ * n))⁻¹
                = τ⁻¹ * (((k ^ i)⁻¹ * n) * w * ((k ^ i)⁻¹ * n)⁻¹) * τ := by group
              _ = τ⁻¹ * (s.fr.z * w) * τ := by rw [h4]
              _ = w := hτ_zw')
        · rw [hvzw]; exact mul_comm_of_conj (by
            calc τ⁻¹ * ((k ^ i)⁻¹ * n) * (s.fr.z * w) * (τ⁻¹ * ((k ^ i)⁻¹ * n))⁻¹
                = τ⁻¹ * (((k ^ i)⁻¹ * n) * (s.fr.z * w) * ((k ^ i)⁻¹ * n)⁻¹) * τ := by group
              _ = τ⁻¹ * w * τ := by rw [hm_zw]
              _ = s.fr.z * w := hτ_w')

end CFSG.OddStandard.HigherRank.YamadaG23
