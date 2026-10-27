module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Phi

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y56_conj_t_of_phi {s : Setting3 G L} {x : G} (hx : f3phi s x = s.fr.z) :
    x * s.t * x⁻¹ = s.fr.z * s.t := by
  have ht2 : s.t * s.t = 1 := by
    have h := pow_orderOf_eq_one s.t
    rwa [s.t_order, pow_two] at h
  have htinv : s.t⁻¹ = s.t := inv_eq_of_mul_eq_one_right ht2
  unfold f3phi at hx
  rw [htinv] at hx
  calc x * s.t * x⁻¹ = x * s.t * x⁻¹ * 1 := (mul_one _).symm
    _ = x * s.t * x⁻¹ * (s.t * s.t) := by rw [ht2]
    _ = (x * s.t * x⁻¹ * s.t) * s.t := by group
    _ = s.fr.z * s.t := by rw [hx]

theorem y56_N_fix_z {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ e4N s, n * s.fr.z * n⁻¹ = s.fr.z := by
  intro n hn
  obtain ⟨hv0V, hzV, hv0_1, hz_1, hv0z, _⟩ := y56_v0 hH
  have hVE : cen s.fr.B ≤ s.fr.E := y56_V_le_E hH
  have hv0E : s.fr.b₁ * s.fr.b₂ ∈ s.fr.E := hVE hv0V
  have hzE : s.fr.z ∈ s.fr.E := y56_z_mem_E hH
  have hzsq : s.fr.z * s.fr.z = 1 := by
    have h := y56_E_sq hH s.fr.z hzE
    rwa [pow_two] at h
  have hnH : n ∈ s.H := (Subgroup.mem_inf.mp hn).1
  have hnN : n ∈ Subgroup.normalizer (s.fr.E : Set G) := (Subgroup.mem_inf.mp hn).2
  have hwE : n * s.fr.z * n⁻¹ ∈ s.fr.E :=
    (Subgroup.mem_normalizer_iff.mp hnN s.fr.z).mp hzE
  have hw1 : n * s.fr.z * n⁻¹ ≠ 1 := by
    intro h
    exact hz_1 (by
      calc s.fr.z = n⁻¹ * (n * s.fr.z * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
  have hfix : ∀ m ∈ normIn L s.fr.E, m * (n * s.fr.z * n⁻¹) * m⁻¹ = n * s.fr.z * n⁻¹ := by
    intro m hm
    have hmL : m ∈ L := (Subgroup.mem_inf.mp hm).1
    have hmN : m ∈ Subgroup.normalizer (s.fr.E : Set G) := (Subgroup.mem_inf.mp hm).2
    have hninvL : n⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem (s3_H_le_N s hH.hS hnH)
    have hconjL : n⁻¹ * m * n ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp hninvL m).mp hmL
    have hninvN : n⁻¹ ∈ Subgroup.normalizer (s.fr.E : Set G) :=
      (Subgroup.normalizer (s.fr.E : Set G)).inv_mem hnN
    have hconjN : n⁻¹ * m * n ∈ Subgroup.normalizer (s.fr.E : Set G) :=
      (Subgroup.normalizer (s.fr.E : Set G)).mul_mem
        ((Subgroup.normalizer (s.fr.E : Set G)).mul_mem hninvN hmN) hnN
    have hzfix := y56_NE_le_Cz hH (n⁻¹ * m * n) (Subgroup.mem_inf.mpr ⟨hconjL, hconjN⟩)
    calc m * (n * s.fr.z * n⁻¹) * m⁻¹
        = n * ((n⁻¹ * m * n) * s.fr.z * (n⁻¹ * m * n)⁻¹) * n⁻¹ := by group
      _ = n * s.fr.z * n⁻¹ := by rw [hzfix]
  have hzv0E : s.fr.z * (s.fr.b₁ * s.fr.b₂) ∈ s.fr.E := s.fr.E.mul_mem hzE hv0E
  have hzv0_1 : s.fr.z * (s.fr.b₁ * s.fr.b₂) ≠ 1 := by
    intro h
    have h1 : s.fr.z = s.fr.b₁ * s.fr.b₂ := by
      calc s.fr.z = s.fr.z * 1 := (mul_one _).symm
        _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by rw [h, mul_one]
        _ = (s.fr.z * s.fr.z) * (s.fr.b₁ * s.fr.b₂) := by group
        _ = 1 * (s.fr.b₁ * s.fr.b₂) := by rw [hzsq]
        _ = s.fr.b₁ * s.fr.b₂ := one_mul _
    exact hv0z h1.symm
  have hzv0z : s.fr.z * (s.fr.b₁ * s.fr.b₂) ≠ s.fr.z := by
    intro h
    have h1 : s.fr.b₁ * s.fr.b₂ = 1 := by
      calc s.fr.b₁ * s.fr.b₂ = 1 * (s.fr.b₁ * s.fr.b₂) := (one_mul _).symm
        _ = (s.fr.z * s.fr.z) * (s.fr.b₁ * s.fr.b₂) := by rw [hzsq]
        _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by group
        _ = s.fr.z * s.fr.z := by rw [h]
        _ = 1 := hzsq
    exact hv0_1 h1
  obtain ⟨v, hvE, hv1, hvz, hvw⟩ : ∃ v ∈ s.fr.E, v ≠ 1 ∧ v ≠ s.fr.z ∧
      v ≠ n * s.fr.z * n⁻¹ := by
    by_cases h : s.fr.b₁ * s.fr.b₂ = n * s.fr.z * n⁻¹
    · refine ⟨s.fr.z * (s.fr.b₁ * s.fr.b₂), hzv0E, hzv0_1, hzv0z, ?_⟩
      rw [h]
      intro hc
      exact hz_1 (by
        calc s.fr.z = (s.fr.z * (n * s.fr.z * n⁻¹)) * (n * s.fr.z * n⁻¹)⁻¹ := by group
          _ = (n * s.fr.z * n⁻¹) * (n * s.fr.z * n⁻¹)⁻¹ := by rw [hc]
          _ = 1 := mul_inv_cancel _)
    · exact ⟨s.fr.b₁ * s.fr.b₂, hv0E, hv0_1, hv0z, h⟩
  by_contra hne
  obtain ⟨m, hm, hmconj⟩ := y56_NE_trans hH (n * s.fr.z * n⁻¹) hwE hw1 hne v hvE hv1 hvz
  exact hvw ((hfix m hm).symm.trans hmconj).symm

theorem y56_N_eq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ n ∈ e4N s, ∃ n₁ ∈ normIn L s.fr.E, ∃ x ∈ e4X0 s, n = n₁ * x := by
  intro n hn
  obtain ⟨hnH, hnN⟩ := Subgroup.mem_inf.mp hn
  have hfixz : ∀ f : ↥s.fr.E, (f : G) = s.fr.z →
      ((((s.fr.E).normalizerMonoidHom ⟨n, hnN⟩) f : ↥s.fr.E) : G) = s.fr.z := by
    intro f hf
    have hcoe : ((((s.fr.E).normalizerMonoidHom ⟨n, hnN⟩) f : ↥s.fr.E) : G) =
        n * (f : G) * n⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe (H := s.fr.E) ⟨n, hnN⟩ f
    rw [hcoe, hf]
    exact y56_N_fix_z hH n hn
  obtain ⟨n₁, hn₁, hsurj⟩ := y56_aut_surj hH ((s.fr.E).normalizerMonoidHom ⟨n, hnN⟩) hfixz
  refine ⟨n₁, hn₁, n₁⁻¹ * n, ?_, by group⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact s.H.mul_mem (s.H.inv_mem (s3_L_le_H s hH.hS (Subgroup.mem_inf.mp hn₁).1)) hnH
  · rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hαf : ((((s.fr.E).normalizerMonoidHom ⟨n, hnN⟩) ⟨f, hf⟩ : ↥s.fr.E) : G) =
        n * f * n⁻¹ := by
      simpa using Subgroup.normalizerMonoidHom_apply_apply_coe (H := s.fr.E) ⟨n, hnN⟩ ⟨f, hf⟩
    have hconj : (n₁⁻¹ * n) * f * (n₁⁻¹ * n)⁻¹ = f := by
      have h := hsurj ⟨f, hf⟩
      rw [hαf] at h
      calc (n₁⁻¹ * n) * f * (n₁⁻¹ * n)⁻¹ = n₁⁻¹ * (n * f * n⁻¹) * n₁ := by group
        _ = n₁⁻¹ * (n₁ * f * n₁⁻¹) * n₁ := by rw [h]
        _ = f := by group
    calc f * (n₁⁻¹ * n) = ((n₁⁻¹ * n) * f * (n₁⁻¹ * n)⁻¹) * (n₁⁻¹ * n) := by rw [hconj]
      _ = (n₁⁻¹ * n) * f := by group

theorem y56_comm_E {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ⁅s.fr.E, normIn L s.fr.E⁆ = s.fr.E := by
  set K : Subgroup G := ⁅s.fr.E, normIn L s.fr.E⁆ with hKdef
  have hKE : K ≤ s.fr.E := by
    rw [hKdef, Subgroup.commutator_le]
    intro f hf b hb
    have hbN : b ∈ Subgroup.normalizer (s.fr.E : Set G) := (Subgroup.mem_inf.mp hb).2
    have hbf : b * f⁻¹ * b⁻¹ ∈ s.fr.E :=
      (Subgroup.mem_normalizer_iff.mp hbN f⁻¹).mp (s.fr.E.inv_mem hf)
    rw [show ⁅f, b⁆ = f * (b * f⁻¹ * b⁻¹) by rw [commutatorElement_def]; group]
    exact s.fr.E.mul_mem hf hbf
  have hKinv : ∀ b ∈ normIn L s.fr.E, ∀ k ∈ K, b * k * b⁻¹ ∈ K := by
    intro b hb k hk
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := by
      rw [hKdef]
      exact Subgroup.normalizer_commutator_ge_right (H₁ := s.fr.E)
        (H₂ := normIn L s.fr.E) hb
    exact (Subgroup.mem_normalizer_iff.mp hbN k).mp hk
  obtain ⟨hv0V, hzV, hv0_1, _, hv0z, _⟩ := y56_v0 hH
  have hVE : cen s.fr.B ≤ s.fr.E := y56_V_le_E hH
  have hv0E : s.fr.b₁ * s.fr.b₂ ∈ s.fr.E := hVE hv0V
  have hzE : s.fr.z ∈ s.fr.E := y56_z_mem_E hH
  have hv0sq : (s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂) = 1 := by
    have h := y56_E_sq hH (s.fr.b₁ * s.fr.b₂) hv0E
    rwa [pow_two] at h
  have hVcard : Nat.card ↥(cen s.fr.B) = 4 := by
    have h := (f3_V_isE2 hH).2
    rw [h]; norm_num
  have hEcard : Nat.card ↥s.fr.E = 8 := by
    have h := (y56_E_isE3 hH).2
    rw [h]; norm_num
  have hproper : (cen s.fr.B).subgroupOf s.fr.E ≠ ⊤ := by
    intro htop
    have h2 : Nat.card ↥((cen s.fr.B).subgroupOf s.fr.E) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv).trans hVcard
    have h3 : Nat.card ↥((cen s.fr.B).subgroupOf s.fr.E) = 8 := by
      rw [htop]
      exact (Nat.card_congr (Subgroup.topEquiv).toEquiv).trans hEcard
    omega
  obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top ((cen s.fr.B).subgroupOf s.fr.E) hproper
  have he'E : (x : G) ∈ s.fr.E := x.2
  have he'V : (x : G) ∉ cen s.fr.B := fun hxV => hx (Subgroup.mem_subgroupOf.mpr hxV)
  have he'1 : (x : G) ≠ 1 := fun h => he'V (by rw [h]; exact Subgroup.one_mem _)
  have he'z : (x : G) ≠ s.fr.z := fun h => he'V (by rw [h]; exact hzV)
  have hv0e'E : s.fr.b₁ * s.fr.b₂ * (x : G) ∈ s.fr.E := s.fr.E.mul_mem hv0E he'E
  have hv0e'V : s.fr.b₁ * s.fr.b₂ * (x : G) ∉ cen s.fr.B := by
    intro h
    exact he'V (by
      have hmem := (cen s.fr.B).mul_mem hv0V h
      rw [show (x : G) = (s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂ * (x : G)) by
        rw [← mul_assoc, hv0sq, one_mul]]
      exact hmem)
  have hv0e'1 : s.fr.b₁ * s.fr.b₂ * (x : G) ≠ 1 :=
    fun h => hv0e'V (by rw [h]; exact Subgroup.one_mem _)
  have hv0e'z : s.fr.b₁ * s.fr.b₂ * (x : G) ≠ s.fr.z :=
    fun h => hv0e'V (by rw [h]; exact hzV)
  obtain ⟨n', hn', hn'conj⟩ := y56_NE_trans hH (x : G) he'E he'1 he'z
    (s.fr.b₁ * s.fr.b₂ * (x : G)) hv0e'E hv0e'1 hv0e'z
  have hv0K : s.fr.b₁ * s.fr.b₂ ∈ K := by
    have hmem : ⁅n', (x : G)⁆ ∈ K := by
      have h := K.inv_mem (Subgroup.commutator_mem_commutator he'E hn')
      rwa [commutatorElement_inv] at h
    have heq : ⁅n', (x : G)⁆ = s.fr.b₁ * s.fr.b₂ := by
      rw [commutatorElement_def, hn'conj]
      group
    rwa [heq] at hmem
  have hKtrans : ∀ v ∈ s.fr.E, v ≠ 1 → v ≠ s.fr.z → v ∈ K := by
    intro v hvE hv1 hvz
    obtain ⟨m, hm, hmconj⟩ :=
      y56_NE_trans hH (s.fr.b₁ * s.fr.b₂) hv0E hv0_1 hv0z v hvE hv1 hvz
    rw [← hmconj]
    exact hKinv m hm _ hv0K
  apply le_antisymm hKE
  intro f hf
  by_cases hf1 : f = 1
  · rw [hf1]; exact K.one_mem
  · by_cases hfz : f = s.fr.z
    · have hzsq : s.fr.z * s.fr.z = 1 := by
        have h := y56_E_sq hH s.fr.z hzE
        rwa [pow_two] at h
      have hzv0E : s.fr.z * (s.fr.b₁ * s.fr.b₂) ∈ s.fr.E := s.fr.E.mul_mem hzE hv0E
      have hzv0_1 : s.fr.z * (s.fr.b₁ * s.fr.b₂) ≠ 1 := by
        intro h
        have h1 : s.fr.z = s.fr.b₁ * s.fr.b₂ := by
          calc s.fr.z = s.fr.z * 1 := (mul_one _).symm
            _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by rw [h, mul_one]
            _ = (s.fr.z * s.fr.z) * (s.fr.b₁ * s.fr.b₂) := by group
            _ = 1 * (s.fr.b₁ * s.fr.b₂) := by rw [hzsq]
            _ = s.fr.b₁ * s.fr.b₂ := one_mul _
        exact hv0z h1.symm
      have hzv0z : s.fr.z * (s.fr.b₁ * s.fr.b₂) ≠ s.fr.z := by
        intro h
        have h1 : s.fr.b₁ * s.fr.b₂ = 1 := by
          calc s.fr.b₁ * s.fr.b₂ = 1 * (s.fr.b₁ * s.fr.b₂) := (one_mul _).symm
            _ = (s.fr.z * s.fr.z) * (s.fr.b₁ * s.fr.b₂) := by rw [hzsq]
            _ = s.fr.z * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by group
            _ = s.fr.z * s.fr.z := by rw [h]
            _ = 1 := hzsq
        exact hv0_1 h1
      have hzv0K : s.fr.z * (s.fr.b₁ * s.fr.b₂) ∈ K := hKtrans _ hzv0E hzv0_1 hzv0z
      have hzv0_eq : s.fr.z = (s.fr.b₁ * s.fr.b₂) * (s.fr.z * (s.fr.b₁ * s.fr.b₂)) := by
        rw [y56_E_comm hH (s.fr.b₁ * s.fr.b₂) hv0E (s.fr.z * (s.fr.b₁ * s.fr.b₂)) hzv0E]
        calc s.fr.z = s.fr.z * 1 := (mul_one _).symm
          _ = s.fr.z * ((s.fr.b₁ * s.fr.b₂) * (s.fr.b₁ * s.fr.b₂)) := by rw [hv0sq]
          _ = (s.fr.z * (s.fr.b₁ * s.fr.b₂)) * (s.fr.b₁ * s.fr.b₂) := by group
      rw [hfz]
      exact hzv0_eq.symm ▸ K.mul_mem hv0K hzv0K
    · exact hKtrans f hf hf1 hfz

theorem y56_NE_fix_d (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ n ∈ normIn L c.s.fr.E, ⁅n, c.d⁆ ∈ e4Q c.s := by
  intro n hn
  have hNA : normIn L c.s.fr.E ≤ normIn L c.s.fr.A := (hH.hLF.fact18).2.2.1.2.1
  have hnA : n ∈ normIn L c.s.fr.A := hNA hn
  have hnH : n ∈ c.s.H := s3_L_le_H c.s hH.hS (Subgroup.mem_inf.mp hnA).1
  have hnNA : n ∈ normIn c.s.H c.s.fr.A :=
    Subgroup.mem_inf.mpr ⟨hnH, (Subgroup.mem_inf.mp hnA).2⟩
  have hnN : n ∈ e4N c.s := y56_NL_le_N hH hn
  have hnorm : n ∈ Subgroup.normalizer (C0 c.e : Set G) :=
    (y53_fact hH).2.1 (Subgroup.mem_sup_left hnNA)
  have hwC0 : n * c.d * n⁻¹ ∈ C0 c.e :=
    (Subgroup.mem_normalizer_iff.mp hnorm c.d).mp c.d_mem
  have hphiw : f3phi c.s (n * c.d * n⁻¹) = c.s.fr.z := by
    rw [y56_phi_conj hH n hnN c.d, y56_phi_d c hH, y56_NE_le_Cz hH n hn]
  have hdt : c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t :=
    y56_conj_t_of_phi (s := c.s) (y56_phi_d c hH)
  have hwt : (n * c.d * n⁻¹) * c.s.t * (n * c.d * n⁻¹)⁻¹ = c.s.fr.z * c.s.t :=
    y56_conj_t_of_phi (s := c.s) hphiw
  have hwz : (n * c.d * n⁻¹) * c.s.fr.z * (n * c.d * n⁻¹)⁻¹ = c.s.fr.z := by
    have hc : c.s.fr.z * (n * c.d * n⁻¹) = (n * c.d * n⁻¹) * c.s.fr.z :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwC0).2 c.s.fr.z (s3_z_mem_A c.s)
    rw [← hc]; group
  have hzsq : c.s.fr.z * c.s.fr.z = 1 := by
    have h := y56_E_sq hH c.s.fr.z (y56_z_mem_E hH)
    rwa [pow_two] at h
  have hxeq : ⁅n, c.d⁆ = (n * c.d * n⁻¹) * c.d := by
    have hdd : c.d * c.d = 1 := by
      have h := pow_orderOf_eq_one c.d
      rwa [c.d_order, pow_two] at h
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hdd]
  have hxt : ⁅n, c.d⁆ * c.s.t * (⁅n, c.d⁆)⁻¹ = c.s.t := by
    rw [hxeq]
    calc ((n * c.d * n⁻¹) * c.d) * c.s.t * ((n * c.d * n⁻¹) * c.d)⁻¹
        = (n * c.d * n⁻¹) * (c.d * c.s.t * c.d⁻¹) * (n * c.d * n⁻¹)⁻¹ := by group
      _ = (n * c.d * n⁻¹) * (c.s.fr.z * c.s.t) * (n * c.d * n⁻¹)⁻¹ := by rw [hdt]
      _ = ((n * c.d * n⁻¹) * c.s.fr.z * (n * c.d * n⁻¹)⁻¹) *
          ((n * c.d * n⁻¹) * c.s.t * (n * c.d * n⁻¹)⁻¹) := by group
      _ = c.s.fr.z * (c.s.fr.z * c.s.t) := by rw [hwz, hwt]
      _ = c.s.t := by rw [← mul_assoc, hzsq, one_mul]
  have hxH : ⁅n, c.d⁆ ∈ c.s.H := by
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
    calc ⁅n, c.d⁆ * c.s.t = (⁅n, c.d⁆ * c.s.t * (⁅n, c.d⁆)⁻¹) * ⁅n, c.d⁆ := by group
      _ = c.s.t * ⁅n, c.d⁆ := by rw [hxt]
  have hxC0 : ⁅n, c.d⁆ ∈ C0 c.e := by
    rw [hxeq]
    exact (C0 c.e).mul_mem hwC0 c.d_mem
  have hxT1 : ⁅n, c.d⁆ ∈ c.e.T₁ := (Subgroup.mem_inf.mp hxC0).1
  have hxT : ⁅n, c.d⁆ ∈ c.s.T := by
    rw [← s3_inf_H_T1 c.s c.e]
    exact Subgroup.mem_inf.mpr ⟨hxT1, hxH⟩
  have hxzt : ⁅n, c.d⁆ ∈ zt c.s := by
    rw [← c.intro5.centT]
    exact Subgroup.mem_inf.mpr ⟨hxT, (Subgroup.mem_inf.mp hxC0).2⟩
  have hztQ : zt c.s ≤ e4Q c.s := by
    rw [zt, Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_sup_left (y56_z_mem_E hH)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)
  exact hztQ hxzt

end CFSG.OddStandard.HigherRank.YamadaG23
