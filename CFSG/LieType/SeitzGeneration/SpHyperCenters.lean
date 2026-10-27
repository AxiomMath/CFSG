module

public import CFSG.LieType.SeitzGeneration.SpHyperRad

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.CTP
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K] {W : Submodule K (Fin r ⊕ Fin r → K)}
  {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0} {H : Subgroup (StatedSp r K)}
  {C₀ : Submodule K (Fin r ⊕ Fin r → K)}

theorem exists_pairing_one (hcompl : IsCompl (spPerp W) C₀) {c : Fin r ⊕ Fin r → K}
    (hc : c ∈ C₀) (hc0 : c ≠ 0) : ∃ w ∈ W, spForm r K w c = 1 := by
  have hnot : ¬ c ∈ spPerp W := fun h =>
    hc0 (Submodule.disjoint_def.1 hcompl.disjoint c h hc)
  have : ∃ w ∈ W, spForm r K w c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnot fun w hw => hcon w hw
  obtain ⟨w, hw, hwc⟩ := this
  refine ⟨(spForm r K w c)⁻¹ • w, W.smul_mem _ hw, ?_⟩
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hwc]

theorem transCenter_of_ne (hcompl : IsCompl (spPerp W) C₀) (hQ : spRad W hW ≤ H)
    (hC : ∀ c ∈ C₀, TransCenter H c) {y c₀ : Fin r ⊕ Fin r → K} (hy : y ∈ spPerp W)
    (hc₀ : c₀ ∈ C₀) (hc₀0 : c₀ ≠ 0) : TransCenter H (y + c₀) := by
  obtain ⟨w, hw, hwc⟩ := exists_pairing_one hcompl hc₀ hc₀0
  have hww : spForm r K w w = 0 := spForm_isAlt.self_eq_zero w
  have hyw : spForm r K y w = 0 := spForm_perp_comm hy hw
  have hcw : spForm r K c₀ w = -1 := by rw [← spForm_isAlt.neg_eq, hwc]
  have hg : spSiegel w y (-1) ∈ H := hQ (spSiegel_mem_spRad hw hy (-1))
  have hz : TransCenter H (spEnd (spSiegel w y (-1)) c₀) := (hC c₀ hc₀).map hg
  rw [spEnd_spSiegel (hy w hw), hcw] at hz
  have hz' : TransCenter H (c₀ + (-1 : K) • ((-1 : K) • y + spForm r K c₀ y • w)) := hz
  set b₀ : K := spForm r K c₀ y with hb₀
  have hT : spTransvection w (-b₀) ∈ H := hQ (spTransvection_mem_spRad hw _)
  have h2 := hz'.map hT
  rw [spEnd_spTransvection] at h2
  convert h2 using 1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hww, hyw,
    hcw]
  module

theorem transCenter_of_perp (hW0 : W ≠ ⊥) (hcompl : IsCompl (spPerp W) C₀)
    (hQ : spRad W hW ≤ H) (hC : ∀ c ∈ C₀, TransCenter H c) {y : Fin r ⊕ Fin r → K}
    (hy : y ∈ spPerp W) : TransCenter H y := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨x, hx⟩ : ∃ x, spForm r K w₀ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hw₀0 (spForm_nondegenerate.1 w₀ h)
  have hx' : x ∈ spPerp W ⊔ C₀ := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y', hy', c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx
    rw [add_zero]
    exact hy' w₀ hw₀
  obtain ⟨w, hw, hwc⟩ := exists_pairing_one hcompl hc hc0
  have hwP : w ∈ spPerp W := fun x hx => hW x hx w hw
  have hcc : spForm r K c c = 0 := spForm_isAlt.self_eq_zero c
  have hz2 : TransCenter H ((-1 : K) • c) := (hC c hc).smul _
  by_cases hyc : spForm r K y c = 0
  · have hz1 : TransCenter H (y + w + c) :=
      transCenter_of_ne hcompl hQ hC ((spPerp W).add_mem hy hwP) hc hc0
    have hB : spForm r K (y + w + c) ((-1 : K) • c) ≠ 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul, hyc, hwc, hcc]
      norm_num
    have hyw : TransCenter H (y + w) := by
      have := hz1.add hz2 hB
      convert this using 1
      module
    intro t'
    have hE : spSiegel w y (-t') ∈ H := hQ (spSiegel_mem_spRad hw hy (-t'))
    have hTw : spTransvection w (-t') ∈ H := hQ (spTransvection_mem_spRad hw _)
    have hTwy : spTransvection (w + y) t' ∈ H := by rw [add_comm]; exact hyw t'
    have hid : spTransvection y t' = spTransvection w (-t') * spTransvection (w + y) t' *
        spSiegel w y (-t') := by
      have e1 : spTransvection w t' = (spTransvection w (-t'))⁻¹ := by
        rw [spTransvection_inv, neg_neg]
      have e2 : spTransvection (w + y) (-t') = (spTransvection (w + y) t')⁻¹ := by
        rw [spTransvection_inv]
      simp only [spSiegel, neg_neg, e2, e1]
      group
    rw [hid]
    exact H.mul_mem (H.mul_mem hTw hTwy) hE
  · have hz1 : TransCenter H (y + c) := transCenter_of_ne hcompl hQ hC hy hc hc0
    have hB : spForm r K (y + c) ((-1 : K) • c) ≠ 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul, hcc]
      simpa using hyc
    have := hz1.add hz2 hB
    convert this using 1
    module

theorem eq_top_of_spRad_of_centers (hW0 : W ≠ ⊥) (hcompl : IsCompl (spPerp W) C₀)
    (hQ : spRad W hW ≤ H) (hC : ∀ c ∈ C₀, TransCenter H c) : H = ⊤ := by
  apply eq_top_of_transCenter
  intro v
  have hv : v ∈ spPerp W ⊔ C₀ := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
  by_cases hc0 : c = 0
  · subst hc0
    rw [add_zero]
    exact transCenter_of_perp hW0 hcompl hQ hC hy
  · exact transCenter_of_ne hcompl hQ hC hy hc hc0

end CFSG.LieType.SeitzGeneration
