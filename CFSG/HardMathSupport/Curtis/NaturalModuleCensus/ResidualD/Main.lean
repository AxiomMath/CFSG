module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD.Levi
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeTwistedD.NaturalModule
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBarFull
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix

variable {n : ℕ}

theorem false_of_stable_subspace (hn : 4 ≤ n) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) {J : Subgroup Y} {v : Y}
    (hvJ : v ∈ J) (hv3 : v ^ 3 = 1) (hfix : ∀ g : Y, g * v = v * g → g ∈ J)
    (W : Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2))
    (hWQ : ∀ w ∈ W, StatedQuadPlus n (ZMod 2) w = 0) (hWdim : 2 ≤ Module.finrank (ZMod 2) W)
    (hWst : ∀ y ∈ J, ∀ A : StatedOmega (StatedQuadPlus n (ZMod 2)),
      (QuotientGroup.mk A : StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) = e y →
      ∀ w ∈ W, ((A : GL (Fin n ⊕ Fin n) (ZMod 2)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) *ᵥ w ∈ W) : False := by
  obtain ⟨M0, hM0⟩ := QuotientGroup.mk_surjective (e v)
  have hM3 : M0 ^ 3 = 1 := by
    apply eq_of_mk_eq_plus (n := n) (F := ZMod 2) (by omega)
    rw [QuotientGroup.mk_pow, hM0, ← map_pow, hv3, map_one]
    rfl
  have hMQ := preserves_of_mem_statedOmega (Q₀ := StatedQuadPlus n (ZMod 2)) M0.2
  have hMW := fun w hw => hWst v hvJ M0 hM0 w hw
  have hM3' : (M0 : GL (Fin n ⊕ Fin n) (ZMod 2)) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hM3
  have hC : ∀ g ∈ StatedOmega (StatedQuadPlus n (ZMod 2)),
      g * (M0 : GL (Fin n ⊕ Fin n) (ZMod 2)) = (M0 : GL (Fin n ⊕ Fin n) (ZMod 2)) * g →
      ∀ w ∈ W, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) *ᵥ w ∈ W := by
    intro g hg hcomm w hw
    set gΩ : StatedOmega (StatedQuadPlus n (ZMod 2)) := ⟨g, hg⟩ with hgΩ
    set y : Y := e.symm (QuotientGroup.mk gΩ) with hydef
    have hcomm' : (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) *
        e v = e v * QuotientGroup.mk gΩ := by
      rw [← hM0, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hcomm
    have hyv : y * v = v * y := by
      apply e.injective
      rw [map_mul, map_mul, hydef, MulEquiv.apply_symm_apply]
      exact hcomm'
    exact hWst y (hfix y hyv) gΩ (by simp [hydef]) w hw
  refine false_of_invariant_totSingular_two (K := ZMod 2) (ι := Fin n ⊕ Fin n) (Nat.card_zmod 2)
    (quadPlusForm n (ZMod 2)) ?_ W hWQ hWdim (M0 : GL (Fin n ⊕ Fin n) (ZMod 2)) hMQ hM3' hMW hC
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem false_of_fixBarFull_omegaPlus (hn4 : 4 ≤ n) (hn5 : n ≤ 5) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) {J : Subgroup Y} {v : Y}
    (h : FixBarFull J 3 v) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ, -⟩ := h.base.parab
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  let T' : Sylow 2 Y := hT.2.1.toSylow hidx
  obtain ⟨Ag, I, ⟨k0, hk0⟩, hst, hgen⟩ := exists_conj_data_plus hn4 e T' J hNJ h.base.ne_top
  have hvJ : v ∈ J := perfectJoin_le J h.base.join
  by_cases hex : ∃ k : Fin n, k ∉ I ∧ k.val ≠ 0
  · obtain ⟨k, hkI, hk0'⟩ := hex
    obtain ⟨W, hWQ, hWdim, hWst⟩ := hst k hkI
    exact false_of_stable_subspace hn4 e hvJ h.base.pow h.fix_all W hWQ (hWdim hk0') hWst
  · push Not at hex
    have hI : ∀ k : Fin n, k.val ≠ 0 → k ∈ I := fun k hk => by
      by_contra hkI
      exact hk (hex k hkI)
    rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
    · refine false_of_cyc_levi_nodes hn4 e h.base.cyc Ag (h := 1) (a := 2) (b := 3) leviMat_four ?_
      rintro i (rfl | rfl | rfl)
      · exact hgen _ (hI _ (by decide))
      · exact hgen _ (hI _ (by decide))
      · exact hgen _ (hI _ (by decide))
    · refine false_of_cyc_levi_nodes hn4 e h.base.cyc Ag (h := 2) (a := 3) (b := 4) leviMat_five ?_
      rintro i (rfl | rfl | rfl)
      · exact hgen _ (hI _ (by decide))
      · exact hgen _ (hI _ (by decide))
      · exact hgen _ (hI _ (by decide))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD
