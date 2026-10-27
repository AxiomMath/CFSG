module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21C1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Generation

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

theorem Lv2520.exists_involution_SCx (h : Lv2520 N t zK) (hp : CaseCParams N t zK R) {a : G}
    (haSK : a ∈ N.S ⊓ N.K) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    ∃ b ∈ N.SCx, b ≠ 1 ∧ b * b = 1 ∧ ∀ k ∈ N.K, k * a = a * k → k * b = b * k := by
  have haS : a ∈ N.S := haSK.1
  have haK : a ∈ N.K := haSK.2
  have haS0 : a ∈ N.S0 := h.SK_le_S0 haSK
  have himg := h.caseC_img_eq hp.ds hp.nonab
  have hπ : actS N.K N.S h.S_le_normalizer a ∈ (h.sBar hp.ds).img N.SCx := by
    rw [himg]
    exact (h.sBar hp.ds).pi_mem_img haS0 haS
  obtain ⟨b, hbB, hbS, hb⟩ := (h.sBar hp.ds).mem_img.mp hπ
  have hc : a⁻¹ * b ∈ N.SC := ((h.sBar hp.ds).pi_eq_iff haS hbS).mp hb.symm
  have hcK := h.SC_commutes hc
  have hbac : b = a * (a⁻¹ * b) := by group
  have hca : (a⁻¹ * b) * a = a * (a⁻¹ * b) := hcK a haK
  refine ⟨b, hbB, ?_, ?_, ?_⟩
  · intro hb1
    have hac : a ∈ N.SC := by
      have := N.SC.inv_mem hc
      rw [hb1, mul_one, inv_inv] at this
      exact this
    exact ha1 (h.K_inf_SC_eq_bot_mem haK hac)
  · have hcc : (a⁻¹ * b) * (a⁻¹ * b) ∈ N.SC := N.SC.mul_mem hc hc
    have hbb : b * b = (a⁻¹ * b) * (a⁻¹ * b) := by
      calc b * b = a * (a⁻¹ * b) * (a * (a⁻¹ * b)) := by rw [← hbac]
        _ = a * (((a⁻¹ * b) * a) * (a⁻¹ * b)) := by group
        _ = a * ((a * (a⁻¹ * b)) * (a⁻¹ * b)) := by rw [hca]
        _ = (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) := by group
        _ = (a⁻¹ * b) * (a⁻¹ * b) := by rw [ha2, one_mul]
    have h3 : b * b ∈ N.SCx ⊓ N.SC := ⟨N.SCx.mul_mem hbB hbB, hbb ▸ hcc⟩
    rw [h.SCx_inf_SC, Subgroup.mem_bot] at h3
    exact h3
  · intro k hk hka
    have hck : (a⁻¹ * b) * k = k * (a⁻¹ * b) := hcK k hk
    calc k * b = k * (a * (a⁻¹ * b)) := by rw [← hbac]
      _ = (k * a) * (a⁻¹ * b) := by group
      _ = (a * k) * (a⁻¹ * b) := by rw [hka]
      _ = a * ((a⁻¹ * b) * k) := by rw [hck]; group
      _ = (a * (a⁻¹ * b)) * k := by group
      _ = b * k := by rw [← hbac]

end Generation

theorem caseCGeneration : CaseCGeneration := by
  intro G _ _ T M hs N t zK R h hfam hp
  have hos : OutSetting N.K N.H N.S := h.outSetting hfam
  have hkey : ∀ a ∈ N.S ⊓ N.K, a ≠ 1 → a ^ 2 = 1 →
      N.K ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.closure
        {k : G | k ∈ N.K ∧ ∃ j ∈ N.SCx, j ≠ 1 ∧ j * j = 1 ∧ k * j = j * k} := by
    intro a haSK ha1 ha2 k hk
    obtain ⟨b, hbB, hb1, hb2, hbk⟩ := h.exists_involution_SCx hp haSK ha1 (by rwa [← pow_two])
    exact Subgroup.subset_closure ⟨hk.1, b, hbB, hb1, hb2,
      hbk k hk.1 (Subgroup.mem_centralizer_singleton_iff.mp hk.2)⟩
  rcases hfam with hX | ⟨⟨e6⟩, -⟩
  · exact l2pGen G N.K (N.S ⊓ N.K) hX (Out21.isSylowTwoOf_inf hos) _ hkey
  · exact Out21.A6.a6Gen e6 (Out21.isSylowTwoOf_inf hos) hkey

end CFSG.QuasithinUnique
