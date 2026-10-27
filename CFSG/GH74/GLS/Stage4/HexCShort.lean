module

public import CFSG.GH74.GLS.Stage4.HexCNorm

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem short_uA (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (hC : Hex6Comm root)
    (c : E.F) {a : G} (ha : a ∈ root 5) : ⁅phi6 r₁ r₂ E.φ (sl2U c), a⁆ = 1 := by
  have hy : phi6 r₁ r₂ E.φ (sl2U c) ∈ root (5 + 1) := by simpa using phi6_U_mem R E c
  have := hC.adj 5 (by norm_num) (by norm_num) a ha _ hy
  exact commutatorElement_eq_one_iff_mul_comm.2 this.symm

theorem short_lB (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (hC : Hex6Comm root)
    (c : E.F) {b : G} (hb : b ∈ root 1) : ⁅phi6 r₁ r₂ E.φ (sl2L c), b⁆ = 1 := by
  have hz' := r2_neg6_mem R (phi6_L_mem R E c)
  have hb' := r2_one_mem R hb
  have hz'' : r₂ * phi6 r₁ r₂ E.φ (sl2L c) * r₂⁻¹ ∈ root (5 + 1) := by simpa using hz'
  have h := hC.adj 5 (by norm_num) (by norm_num) _ hb' _ hz''
  refine commutatorElement_eq_one_iff_mul_comm.2 ?_
  refine comm_via r₂⁻¹ ?_
  simpa using h.symm

theorem short_uB (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (c : E.F) {b : G}
    (hb : b ∈ root 1) :
    ∃ a ∈ root 5, a⁻¹ * ⁅phi6 r₁ r₂ E.φ (sl2U c), b⁆ ∈ Vsub root 2 4 := by
  have h := rgd2_octComm R 1 6 (by norm_num) (by norm_num) (by norm_num) b hb _ (phi6_U_mem R E c)
  have hV : ⁅b, phi6 r₁ r₂ E.φ (sl2U c)⁆ ∈ Vsub root 2 5 := by
    refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 6, root k) ≤ Vsub root 2 5) h
    have := Set.mem_Ioo.1 hk
    exact root_le_Vsub (by omega) (by omega)
  have hV' : ⁅phi6 r₁ r₂ E.φ (sl2U c), b⁆ ∈ Vsub root 2 5 := by
    rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ hV
  obtain ⟨n, hn, a, ha, he⟩ := exists_mul_of_mem_V25 R hV'
  refine ⟨a, ha, ?_⟩
  rw [he]
  have := root5_norm R (root 5 |>.inv_mem ha) hn
  simpa [mul_assoc] using this

theorem short_lA (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (c : E.F) {a : G}
    (ha : a ∈ root 5) :
    ∃ b ∈ root 1, b⁻¹ * ⁅phi6 r₁ r₂ E.φ (sl2L c), a⁆ ∈ Vsub root 2 4 := by
  have hz' := r2_neg6_mem R (phi6_L_mem R E c)
  have ha' := r2_five_mem R ha
  have h := rgd2_octComm R 1 6 (by norm_num) (by norm_num) (by norm_num) _ ha' _ hz'
  have hV : ⁅r₂ * a * r₂⁻¹, r₂ * phi6 r₁ r₂ E.φ (sl2L c) * r₂⁻¹⁆ ∈ Vsub root 2 5 := by
    refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 6, root k) ≤ Vsub root 2 5) h
    have := Set.mem_Ioo.1 hk
    exact root_le_Vsub (by omega) (by omega)
  have hV' : ⁅r₂ * phi6 r₁ r₂ E.φ (sl2L c) * r₂⁻¹, r₂ * a * r₂⁻¹⁆ ∈ Vsub root 2 5 := by
    rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ hV
  have h14 := r2_inv_mem_Vsub R (i := 2) (j := 5) (by norm_num) (by norm_num) hV'
  have e : r₂⁻¹ * ⁅r₂ * phi6 r₁ r₂ E.φ (sl2L c) * r₂⁻¹, r₂ * a * r₂⁻¹⁆ * r₂ =
      ⁅phi6 r₁ r₂ E.φ (sl2L c), a⁆ := by
    simp only [commutatorElement_def]; group
  norm_num at h14
  rw [e] at h14
  obtain ⟨b, hb, n, hn, he⟩ := exists_mul_of_mem_V14 R h14
  refine ⟨b, hb, ?_⟩
  rw [he]
  simpa using hn

end CFSG.GH74.GLS.Stage4.Hex
