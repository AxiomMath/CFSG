module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2V2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Hlp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_NLA_fix_z {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {k : G}
    (hk : k ∈ normIn L s.fr.A) : k * s.fr.z * k⁻¹ = s.fr.z := by
  have hkc : k ∈ centEl L s.fr.z := by
    rw [← hH.hLF.fact18.1.1]
    exact hk
  have hmem : k ∈ centralizer ({s.fr.z} : Set G) := hkc.2
  rw [Subgroup.mem_centralizer_iff] at hmem
  rw [← hmem s.fr.z (Set.mem_singleton s.fr.z)]
  group

theorem y7a_k_norm_M4 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {k : G}
    (hkA : k ∈ normIn L c.s.fr.A) (hkE : k ∈ normIn L c.s.fr.E) :
    ∀ x ∈ M4 c.e, k * x * k⁻¹ ∈ M4 c.e := by
  intro x hx
  have hkX : k ∈ y7aX c := y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH hkA)
  exact y7a_conj_mem_centIn (fun a ha => (y56_C4_cand c.toCtx5 hH).2.2.1 k hkE a ha)
    (Subgroup.mem_inf.mp hkX).2 hx

private lemma y7a_mem_Z_iff {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {u : G} :
    u ∈ s.fr.Z ↔ u = 1 ∨ u = s.fr.z := by
  classical
  rw [SFrame.Z, mem_zpowers_iff_mem_range_orderOf, s3_z_order s (lfactsA_of_setting hH.hS hH.hZ s)]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩

theorem y7a_k_not_norm_U (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) {k : G} (hkA : k ∈ normIn L c.s.fr.A) (hkE : k ∈ normIn L c.s.fr.E)
    (hfpf : ∀ f ∈ c.s.fr.E, k * f * k⁻¹ * f⁻¹ ∈ c.s.fr.Z → f ∈ c.s.fr.Z) :
    ¬ ∀ x ∈ c.s.fr.E ⊔ V2 c.e, k * x * k⁻¹ ∈ c.s.fr.E ⊔ V2 c.e := by
  intro hU
  obtain ⟨-, u, huV, hub⟩ := y7a_V2_data c hH hF h71
  obtain ⟨hbB, hzB, hb1, hz1, hbz, henum⟩ := y56_v0 hH
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkA).1
  have hkt : k * c.s.t * k⁻¹ = c.s.t := by
    rw [s3_comm_t_of_mem_L c.s hkL]
    group
  have hcomm : ∀ e ∈ c.s.fr.E, ∀ v ∈ V2 c.e, e * v = v * e := fun e he v hv =>
    (((y7a_V2_mem_iff c hH hF h71 v).mp hv).2.1 e he).symm
  obtain ⟨e', he', v', hv', hkuev⟩ :=
    y7a_sup_elems hcomm _
      (hU u ((le_sup_right : V2 c.e ≤ c.s.fr.E ⊔ V2 c.e) huV))
  have h1 : ⁅k * u * k⁻¹, c.s.t⁆ = k * (c.s.fr.b₁ * c.s.fr.b₂) * k⁻¹ := by
    rw [← hub]
    calc ⁅k * u * k⁻¹, c.s.t⁆ = ⁅k * u * k⁻¹, k * c.s.t * k⁻¹⁆ := by rw [hkt]
      _ = k * ⁅u, c.s.t⁆ * k⁻¹ := by simp only [commutatorElement_def]; group
  have hw : ⁅v', c.s.t⁆ ∈ cen c.s.fr.B := y7a_V2_comm_t c hH hF h71 v' hv'
  have he't : ⁅e', c.s.t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (y56_t_comm_E c.s e' he')
  have hew : e' * ⁅v', c.s.t⁆ = ⁅v', c.s.t⁆ * e' := y56_E_comm hH e' he' _ (y56_V_le_E hH hw)
  have h2 : ⁅e' * v', c.s.t⁆ = ⁅v', c.s.t⁆ := by
    calc ⁅e' * v', c.s.t⁆ = e' * ⁅v', c.s.t⁆ * e'⁻¹ * ⁅e', c.s.t⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅v', c.s.t⁆ := by rw [he't, hew]; group
  have h3 : k * (c.s.fr.b₁ * c.s.fr.b₂) * k⁻¹ = ⁅v', c.s.t⁆ := by
    rw [← h1, hkuev, h2]
  have hbE : c.s.fr.b₁ * c.s.fr.b₂ ∈ c.s.fr.E := y56_V_le_E hH hbB
  have hkz : k * c.s.fr.z * k⁻¹ = c.s.fr.z := y7a_NLA_fix_z hH hkA
  have hZb : (k * (c.s.fr.b₁ * c.s.fr.b₂) * k⁻¹ * (c.s.fr.b₁ * c.s.fr.b₂)⁻¹ ∈ c.s.fr.Z) →
      False := by
    intro hmem
    rcases (y7a_mem_Z_iff hH).mp (hfpf _ hbE hmem) with h | h
    · exact hb1 h
    · exact hbz h
  rcases henum _ hw with h | h | h | h
  ·
    apply hb1
    calc c.s.fr.b₁ * c.s.fr.b₂
        = k⁻¹ * (k * (c.s.fr.b₁ * c.s.fr.b₂) * k⁻¹) * k := by group
      _ = 1 := by rw [h3, h]; group
  ·
    apply hbz
    calc c.s.fr.b₁ * c.s.fr.b₂
        = k⁻¹ * (k * (c.s.fr.b₁ * c.s.fr.b₂) * k⁻¹) * k := by group
      _ = k⁻¹ * (k * c.s.fr.z * k⁻¹) * k := by rw [h3, h, hkz]
      _ = c.s.fr.z := by group
  ·
    apply hZb
    rw [h3, h]
    simp only [mul_inv_cancel]
    exact Subgroup.one_mem _
  ·
    apply hZb
    rw [h3, h]
    have : c.s.fr.z * (c.s.fr.b₁ * c.s.fr.b₂) * (c.s.fr.b₁ * c.s.fr.b₂)⁻¹ = c.s.fr.z := by group
    rw [this]
    exact Subgroup.mem_zpowers c.s.fr.z

end CFSG.OddStandard.HigherRank.YamadaG23
