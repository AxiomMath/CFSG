module

public import CFSG.CGT.Stroth77.Stroth32Normal

public section

namespace CFSG.CGT.Stroth77

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)}

theorem t100_scalar_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {f : G}
    (hf : f ∈ hS.R1 dD.uv dD.t) (hpf : hS.proj dD.ρ f * f⁻¹ ∈ D) :
    ∃ y : ℤ, ∀ v, dD.thetaT (hS.R_le_normalizer hf.1) v = y • v := by
  obtain ⟨d, hd, y, p, hn⟩ := h.exists_normal100 hS hm hfus hf hpf
  refine ⟨y, fun v => ?_⟩
  have hfN := hS.R_le_normalizer hf.1
  have hdN : d ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hd
  have := hn.scalar v
  rwa [dD.thetaT_congr _ (mul_mem hfN hdN) rfl, dD.thetaT_mul hfN hdN,
    dD.thetaT_of_mem hdN hd] at this

theorem t100_conj_mem_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hρR : ∀ e ∈ hS.R1 dD.uv dD.t, hS.proj dD.ρ e * e⁻¹ ∈ D) {g e : G} (hg : g ∈ hS.R)
    (he : e ∈ hS.R1 dD.uv dD.t) : g⁻¹ * e * g ∈ hS.R1 dD.uv dD.t := by
  obtain ⟨y, hy⟩ := h.t100_scalar_R1 hS hm hfus he (hρR e he)
  have hgN := hS.R_le_normalizer hg
  have heN := hS.R_le_normalizer he.1
  have hcR : g⁻¹ * e * g ∈ hS.R := mul_mem (mul_mem (inv_mem hg) he.1) hg
  have hcN := hS.R_le_normalizer hcR
  have h1 : ∀ v, dD.thetaT hcN v = dD.thetaT heN v := fun v => by
    rw [dD.thetaT_congr hcN (mul_mem (mul_mem (inv_mem hgN) heN) hgN) rfl, dD.thetaT_conj heN hgN]
    simp only [hy]
    rw [map_zsmul, dD.thetaT_thetaT_inv]
  have h2 : g⁻¹ * e * g * e⁻¹ ∈ D := by
    refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S hcR) (inv_mem (hS.R_le_S he.1)))
      (mul_mem hcN (inv_mem heN)) fun v => ?_
    rw [dD.thetaT_mul hcN (inv_mem heN), h1, dD.thetaT_inv_thetaT]
  have := mul_mem (t100_D_le_R1 hS h2) he
  simpa using this

theorem t100_R_le_normalizer_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hρR : ∀ e ∈ hS.R1 dD.uv dD.t, hS.proj dD.ρ e * e⁻¹ ∈ D) :
    hS.R ≤ Subgroup.normalizer ((hS.R1 dD.uv dD.t : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro e
  refine ⟨fun he => h.t100_conj_mem_R1 hS hm hfus hρR hg he, fun he => ?_⟩
  have := h.t100_conj_mem_R1 hS hm hfus hρR (inv_mem hg) he
  rwa [show g⁻¹⁻¹ * (g⁻¹ * e * g) * g⁻¹ = e by group] at this

theorem t100_R1_eq_R (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hρR : ∀ e ∈ hS.R1 dD.uv dD.t, hS.proj dD.ρ e * e⁻¹ ∈ D) : hS.R1 dD.uv dD.t = hS.R := by
  refine le_antisymm (fun f hf => hf.1) fun f hfR => ?_
  by_contra hf
  have hlt : hS.R1 dD.uv dD.t < hS.R :=
    lt_of_le_of_ne (fun e he => he.1) fun heq => hf (by rw [heq]; exact hfR)
  obtain ⟨f, hfR, hfR1, huv, ht⟩ :=
    h.exists_mem_R_conj_mem_R1 hS (h.t100_R_le_normalizer_R1 hS hm hfus hρR) hlt
  have hinv : ∀ {x : G}, x * x = 1 → f⁻¹ * x * f * (f⁻¹ * x * f) = 1 := by
    intro x hx2
    calc f⁻¹ * x * f * (f⁻¹ * x * f) = f⁻¹ * (x * x) * f := by group
      _ = 1 := by rw [hx2]; group
  have key : ∀ {x : G}, f⁻¹ * x * f * x⁻¹ ∈ hS.R1 dD.uv dD.t → f⁻¹ * x * f * x⁻¹ ∉ D →
      ∃ e d : G, ∃ y : ℤ, Normal100 hS dD e y 1 ∧ d ∈ D ∧ f⁻¹ * x * f = e * d * x := by
    intro x hg hgD
    obtain ⟨d, hd, y, hn⟩ := h.t100_exists_normal_one hS hm hfus hg (hρR _ hg) hgD
    exact ⟨_, d⁻¹, y, hn, inv_mem hd, by group⟩
  by_cases huvD : f⁻¹ * dD.uv * f * dD.uv⁻¹ ∈ D
  · by_cases htD : f⁻¹ * dD.t * f * dD.t⁻¹ ∈ D
    · exact hfR1 ⟨hfR, huvD, htD⟩
    · obtain ⟨e, d, y, hn, hd, hfx⟩ := key ht htD
      exact hn.mul_t_sq_ne_one h hd (by rw [← hfx]; exact hinv dD.t_sq)
  · obtain ⟨e, d, y, hn, hd, hfx⟩ := key huv huvD
    exact hn.mul_uv_sq_ne_one h hd (by rw [← hfx]; exact hinv dD.uv_sq)

theorem t100_classify_R (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hρR : ∀ e ∈ hS.R1 dD.uv dD.t, hS.proj dD.ρ e * e⁻¹ ∈ D) :
    hS.R = D ∨
      ∃ e ∈ hS.R, hS.R = D ⊔ Subgroup.zpowers e ∧
        e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
        e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
        ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
          (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
            e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
            e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
            e * e = (dD.c : G) ^ 2 ^ (m - 1))) := by
  have hRR := h.t100_R1_eq_R hS hm hfus hρR
  rcases h.t100_classify_R1 hS hm hfus hρR with h1 | ⟨e, y, hn, h2, hy⟩
  · exact Or.inl (by rw [← hRR, h1])
  · exact Or.inr ⟨e, hn.mem.1, by rw [← hRR, h2], hn.rels h hm hy⟩

end StrothFrame.IsD

end CFSG.CGT.Stroth77
