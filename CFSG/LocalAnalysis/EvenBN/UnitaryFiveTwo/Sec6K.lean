module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Tr
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6M
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3G
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6PGrp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7NR
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6M

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer L44Sylow
open scoped commutatorElement

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Z₂K_le_YK : Z₂K ≤ YK := by
  rintro _ ⟨a, b, c, e, z, ⟨ha, he⟩, rfl⟩
  subst ha he
  exact ⟨0, b, c, z, rfl⟩

theorem linear_K_inputs (h : d.Hyp) (hK : d.KLinear) :
    (∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) ∧
      (∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) := by
  obtain ⟨φ, -⟩ := hK.graphField
  have hK₃ : d.K₃ ≤ d.K := by
    rw [← hK.centralizer_eq]
    exact inf_le_left
  have hYK : d.Y ≤ d.K := h.Y_le_K hK₃ (Data.Lev_le_zpowers_sup_K₃ d)
  have hMK : d.M ≤ d.K := h.M_le_K hYK hK₃
  have hX₂K : d.X₂ ≤ d.K := (d.pull_mono X₂sub_le_K₃sub').trans hK₃
  have hFK : d.F ≤ d.K := d.F_le_K₃.trans hK₃
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥d.S := IsPGroup.of_card (n := 10) d.card_S
  have hX₂2 : IsPGroup 2 ↥d.X₂ := hS2.to_le X₂_le_S'
  have hY2 : IsPGroup 2 ↥d.Y := IsPGroup.of_card (n := 8) h.card_Y'
  have hXY : IsPGroup 2 ↥(d.X₂ ⊔ d.Y) := PGrp.isPGroup_sup_of_le_normalizer hX₂2 hY2
    (fun x hx => h.S_le_normalizer_Y (X₂_le_S' hx))
  obtain ⟨χ, hχinj, hχK, -, hAQ⟩ := exists_chi_of_pGroup φ hXY (sup_le hX₂K hYK)
  have hXQ : d.X₂ ≤ PK.map χ := le_sup_left.trans hAQ
  have hYQ : d.Y ≤ PK.map χ := le_sup_right.trans hAQ
  have hY : d.Y = YK.map χ := eq_map_YK hχinj hYQ (fun x hx y hy => h.Y_comm hx hy)
    (fun x hx => h.Y_sq hx) h.card_Y'
  have hW : ZK.map χ = d.W := by
    have hle : ZK.map χ ≤ d.W := by
      rintro _ ⟨z, hz, rfl⟩
      have hzY : χ z ∈ d.Y := by
        rw [hY]
        exact ⟨z, ZK_le_YK hz, rfl⟩
      refine ⟨hzY, mem_centralizer_iff.2 fun s hs => ?_⟩
      have hA : d.A₂ ≤ centralizer ({χ z} : Set G) := fun a ha =>
        mem_centralizer_singleton_iff.2 (h.Y_comm_A₂ hzY ha)
      have hX : d.X₂ ≤ centralizer ({χ z} : Set G) := fun x hx =>
        mem_centralizer_singleton_iff.2 (map_ZK_comm (hXQ hx) ⟨z, hz, rfl⟩)
      rw [d.S_eq_sup] at hs
      exact mem_centralizer_singleton_iff.1 ((sup_le hA hX) hs)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective hχinj, card_ZK, h.sec4_9_W.1]
  have hMQ : d.M ≤ PK.map χ := by
    have hMmem : ∀ {m : G}, m ∈ d.M ↔ m ∈ d.D₁ ∧ m * d.e₂ = d.e₂ * m := fun {m} => by
      show m ∈ d.D₁ ⊓ centralizer ({d.e₂} : Set G) ↔ _
      rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]
    have hFnorm : d.F ≤ normalizer (d.M : Set G) := by
      intro f hf
      have hfS : f ∈ d.S := F_le_S hf
      have hfD : f ∈ normalizer (d.D₁ : Set G) := h.R_le_normalizer_D₁ (mem_sup_left hfS)
      have hfe : d.e₂ * f = f * d.e₂ := e₂_comm_F hf
      have hfe' : f⁻¹ * d.e₂ = d.e₂ * f⁻¹ := by
        calc f⁻¹ * d.e₂ = f⁻¹ * (d.e₂ * f) * f⁻¹ := by group
          _ = f⁻¹ * (f * d.e₂) * f⁻¹ := by rw [hfe]
          _ = d.e₂ * f⁻¹ := by group
      refine mem_normalizer_fintype fun m hm => ?_
      obtain ⟨hmD, hme⟩ := hMmem.1 hm
      refine hMmem.2 ⟨(mem_normalizer_iff.1 hfD m).1 hmD, ?_⟩
      calc f * m * f⁻¹ * d.e₂ = f * m * (f⁻¹ * d.e₂) := by group
        _ = f * m * (d.e₂ * f⁻¹) := by rw [hfe']
        _ = f * (m * d.e₂) * f⁻¹ := by group
        _ = f * (d.e₂ * m) * f⁻¹ := by rw [hme]
        _ = (f * d.e₂) * m * f⁻¹ := by group
        _ = (d.e₂ * f) * m * f⁻¹ := by rw [hfe]
        _ = d.e₂ * (f * m * f⁻¹) := by group
    have hF2 : IsPGroup 2 ↥d.F := IsPGroup.of_card (n := 4) d.card_F
    have hD2 : IsPGroup 2 ↥d.D₁ := IsPGroup.of_card (n := 14) h.card_D₁
    have hM2 : IsPGroup 2 ↥d.M := hD2.to_le M_le_D₁
    have hFM2 : IsPGroup 2 ↥(d.F ⊔ d.M) := PGrp.isPGroup_sup_of_le_normalizer hF2 hM2 hFnorm
    have hT2 : IsPGroup 2 ↥((d.F ⊔ d.M).comap χ) := hFM2.comap_of_injective χ hχinj
    have hFMW : d.F ⊔ d.M ≤ centralizer (d.W : Set G) := by
      refine sup_le (F_le_S.trans S_le_centralizer_W) (M_le_D₁.trans ?_)
      exact fun x hx => (Subgroup.mem_inf.1 hx).2
    have hC : ∀ x ∈ (d.F ⊔ d.M).comap χ, ∀ z ∈ ZK, x * z = z * x := by
      intro x hx z hz
      have hzW : χ z ∈ d.W := hW ▸ ⟨z, hz, rfl⟩
      have := mem_centralizer_iff.1 (hFMW (Subgroup.mem_comap.1 hx)) (χ z) hzW
      apply hχinj
      rw [map_mul, map_mul]
      exact this.symm
    have hnc : ∃ x ∈ (d.F ⊔ d.M).comap χ ⊓ PK, ∃ y ∈ (d.F ⊔ d.M).comap χ ⊓ PK,
        x * y * x⁻¹ * y⁻¹ ∉ ZK := by
      obtain ⟨f, hfF, hfZ⟩ : ∃ f ∈ d.F, f ∉ d.Z₂ := by
        by_contra hcon
        push_neg at hcon
        have := Subgroup.card_le_of_le (show d.F ≤ d.Z₂ from hcon)
        rw [d.card_F, card_Z₂] at this
        norm_num at this
      obtain ⟨ξ, hξF, rfl⟩ := hfF
      have hξZ : ξ ∉ Z₂sub := fun hξ => hfZ ⟨ξ, hξ, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c : F4, x₂SU c * ξ * (x₂SU c)⁻¹ * ξ⁻¹ ∉ ZX₄sub := by
        by_contra hcon
        push_neg at hcon
        exact hξZ (mem_Z₂sub_of_comm hξF hcon)
      have haX : d.ι (x₂SU c) ∈ d.X₂ := ⟨x₂SU c, x₂SU_mem c, rfl⟩
      have haM : d.ι (x₂SU c) ∈ d.M :=
        hMmem.2 ⟨h.A₁_le_D₁ (X₂_le_A₁ haX), X₂_comm_e₂ haX⟩
      obtain ⟨p, hpP, hpa⟩ := hXQ haX
      have hfY : d.ι ξ ∈ d.Y := h.F_le_Y ⟨ξ, hξF, rfl⟩
      rw [hY] at hfY
      obtain ⟨q, hqY, hqf⟩ := hfY
      refine ⟨p, ⟨?_, hpP⟩, q, ⟨?_, YK_le_PK hqY⟩, ?_⟩
      · show χ p ∈ d.F ⊔ d.M
        rw [hpa]
        exact mem_sup_right haM
      · show χ q ∈ d.F ⊔ d.M
        rw [hqf]
        exact mem_sup_left ⟨ξ, hξF, rfl⟩
      · intro hZ
        have hL : d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * (d.ι ξ)⁻¹ =
            d.ι (x₂SU c * ξ * (x₂SU c)⁻¹ * ξ⁻¹) := by
          simp
        have hW' : d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * (d.ι ξ)⁻¹ ∈ d.W := by
          rw [← hW]
          refine ⟨_, hZ, ?_⟩
          simp [hpa, hqf]
        have hH : d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * (d.ι ξ)⁻¹ ∈ d.H :=
          h.L_le_H (hL ▸ d.ι_mem _)
        have hZX : d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * (d.ι ξ)⁻¹ ∈ d.W ⊓ d.H :=
          ⟨hW', hH⟩
        rw [h.sec4_9_W.2.1, hL] at hZX
        exact hc (d.ι_mem_pull_iff.1 hZX)
    have hle := le_PK_of_pGroup hT2 hC hnc
    intro m hm
    obtain ⟨x, hx⟩ := hχK m (hMK hm)
    exact ⟨x, hle (by show χ x ∈ d.F ⊔ d.M; rw [hx]; exact mem_sup_right hm), hx⟩
  have hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G) := fun m hm =>
    mem_normalizer_fintype fun y hy => by
      rw [hY] at hy ⊢
      exact map_YK_conj (hMQ hm) hy
  have hV₂ : Z₂K.map χ = d.V₂ := by
    have hle : Z₂K.map χ ≤ d.V₂ := by
      rintro _ ⟨z, hz, rfl⟩
      have hzY : χ z ∈ d.Y := by
        rw [hY]
        exact ⟨z, Z₂K_le_YK hz, rfl⟩
      have hx : ∀ c : F4, d.ι (x₂SU c) * χ z * (d.ι (x₂SU c))⁻¹ * (χ z)⁻¹ ∈ d.W := fun c => by
        rw [← hW]
        exact map_Z₂K_comm (hXQ ⟨x₂SU c, x₂SU_mem c, rfl⟩) ⟨z, hz, rfl⟩
      exact h.mem_V₂_of_x₂ hzY (hx 1) (hx F4.ω)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective hχinj, card_Z₂K, h.card_V₂]
  refine ⟨hKY, fun v hv m hm => ?_⟩
  rw [← hV₂] at hv
  have := map_Z₂K_comm (hMQ hm) hv
  rwa [hW] at this

theorem M_le_normalizer_Y_linear (h : d.Hyp) (hK : d.KLinear) :
    ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G) :=
  (h.linear_K_inputs hK).1

theorem comm_M_V₂_mem_W_linear (h : d.Hyp) (hK : d.KLinear) :
    ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W :=
  (h.linear_K_inputs hK).2

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
