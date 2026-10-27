module

public import CFSG.GH74.GLS.Stage2.Final.ModelE

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

structure ClsFacts (M : ModelData F) : Prop where
  refl_D : ∀ a b : GL (Fin 2) F, a ∈ M.U2 → b ∈ M.U2 → a * a = 1 → b * b = 1 → a ≠ 1 → a ≠ -1 →
    b ≠ 1 → b ≠ -1 → ConjMod M (diagGL a b) (xyGL F)
  plus_W : ∀ a ∈ M.U2, ConjMod M (swapGL F * diagGL a a⁻¹) (xyGL F)
  minus_D : ∀ a b : GL (Fin 2) F, a ∈ M.U2 → b ∈ M.U2 → a * a = -1 → b * b = -1 →
    (a : Matrix (Fin 2) (Fin 2) F).det = 1 → (b : Matrix (Fin 2) (Fin 2) F).det = 1 →
    ConjMod M (diagGL a b) (swapGL F * yGL F)
  minus_W : ∀ a ∈ M.U2, ConjMod M (swapGL F * diagGL a (-a⁻¹)) (swapGL F * yGL F)
  no_scalar_i : ∀ l : Fˣ, sc2 l ∈ M.U2 → l * l ≠ -1

theorem isConj_wy_of_ConjMod {M : ModelData F} {g : GL (Fin 4) F} (hg : g ∈ M.K4)
    (h : ConjMod M g (swapGL F * yGL F)) : IsConj (tP M * yP M) (mkP M ⟨g, hg⟩) := by
  have hwy : swapGL F * yGL F ∈ M.K4 := M.K4.mul_mem M.swapGL_mem_K4 M.yGL_mem_K4
  have := isConj_of_ConjMod hg hwy h
  rw [tP_mul_yP]
  exact this.symm

theorem diagGL_eq_neg_one {a b : GL (Fin 2) F} (h : diagGL a b = xGL F) : a = -1 ∧ b = -1 :=
  diagGL_inj h

theorem D_plus_conj {M : ModelData F} (hC : ClsFacts M) (h2 : (2 : F) ≠ 0) {a b : GL (Fin 2) F}
    (ha : a ∈ M.U2) (hb : b ∈ M.U2)
    (hdet : (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1)
    (haa : a * a = 1) (hbb : b * b = 1) (hnz : ¬ ∃ s : Fˣ, diagGL a b = sc4 s) :
    ConjMod M (diagGL a b) (xyGL F) := by
  have hK : diagGL a b ∈ M.K4 := M.diagGL_mem_K4_iff.2 ⟨ha, hb, hdet⟩
  have hc1 : ∀ x : GL (Fin 2) F, x * x = 1 → x * x = sc2 (1 : Fˣ) := fun x h => by rw [h, sc2_one]
  rcases ch_sq (hc1 a haa) with ⟨l, hl, hll⟩ | ⟨hta, hda⟩ <;>
    rcases ch_sq (hc1 b hbb) with ⟨m, hm, hmm⟩ | ⟨htb, hdb⟩
  ·
    have hml : m = l ∨ m = -l := by
      have h0 : ((m : F) - l) * ((m : F) + l) = 0 := by
        have e1 := congrArg (fun u : Fˣ => (u : F)) hll
        have e2 := congrArg (fun u : Fˣ => (u : F)) hmm
        simp only [Units.val_mul] at e1 e2
        linear_combination e2 - e1
      rcases mul_eq_zero.1 h0 with h | h
      · left; exact Units.ext (by linear_combination h)
      · right; exact Units.ext (by simp; linear_combination h)
    rcases hml with h | h
    · exact absurd ⟨l, by rw [hl, hm, h, scalar4_eq]⟩ hnz
    · have hsc : sc2 m = sc2 l * (-1 : GL (Fin 2) F) := by
        rw [← CFSG.GH74.L5U5.scalar_neg_one_eq (F := F) 2, ← map_mul, h, mul_neg_one]
      have heq : diagGL a b = sc4 l * xyGL F := by
        rw [hl, hm, hsc, show (sc4 l : GL (Fin 4) F) = diagGL (sc2 l) (sc2 l) from scalar4_eq l, xyGL,
          diagGL_mul, mul_one]
      have hs4 : sc4 l ∈ M.K4 := by
        have : sc4 l = diagGL a b * (xyGL F)⁻¹ := by rw [heq]; group
        rw [this]
        exact M.K4.mul_mem hK (M.K4.inv_mem M.xyGL_mem_K4)
      exact ⟨1, M.K4.one_mem, l, hs4, by rw [inv_one, mul_one, one_mul]; exact heq⟩
  · exfalso
    have e1 := congrArg (fun u : Fˣ => (u : F)) hll
    simp only [Units.val_mul, Units.val_one] at e1
    rw [hl, det_sc2, hdb] at hdet
    simp only [Units.val_one] at hdet
    apply h2
    linear_combination -hdet - e1
  · exfalso
    have e2 := congrArg (fun u : Fˣ => (u : F)) hmm
    simp only [Units.val_mul, Units.val_one] at e2
    rw [hm, det_sc2, hda] at hdet
    simp only [Units.val_one] at hdet
    apply h2
    linear_combination -hdet - e2
  · obtain ⟨ha1, ham⟩ := ne_one_of_trace_zero h2 hta
    obtain ⟨hb1, hbm⟩ := ne_one_of_trace_zero h2 htb
    exact hC.refl_D a b ha hb haa hbb ha1 ham hb1 hbm

theorem D_minus_conj {M : ModelData F} (hC : ClsFacts M) (h2 : (2 : F) ≠ 0) {a b : GL (Fin 2) F}
    (ha : a ∈ M.U2) (hb : b ∈ M.U2) (haa : a * a = -1) (hbb : b * b = -1) :
    ConjMod M (diagGL a b) (swapGL F * yGL F) := by
  have hc1 : ∀ x : GL (Fin 2) F, x * x = -1 → x * x = sc2 (-1 : Fˣ) := fun x h => by
    rw [h, sc2_neg_one]
  rcases ch_sq (hc1 a haa) with ⟨l, hl, hll⟩ | ⟨hta, hda⟩
  · exact absurd hll (hC.no_scalar_i l (hl ▸ ha))
  rcases ch_sq (hc1 b hbb) with ⟨m, hm, hmm⟩ | ⟨htb, hdb⟩
  · exact absurd hmm (hC.no_scalar_i m (hm ▸ hb))
  simp only [Units.val_neg, Units.val_one, neg_neg] at hda hdb
  exact hC.minus_D a b ha hb haa hbb hda hdb

theorem W_plus_conj {M : ModelData F} (hC : ClsFacts M) {a b : GL (Fin 2) F} (ha : a ∈ M.U2)
    (hab : a * b = 1) : ConjMod M (swapGL F * diagGL a b) (xyGL F) := by
  have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  rw [hb]
  exact hC.plus_W a ha

theorem W_minus_conj {M : ModelData F} (hC : ClsFacts M) {a b : GL (Fin 2) F} (ha : a ∈ M.U2)
    (hab : a * b = -1) : ConjMod M (swapGL F * diagGL a b) (swapGL F * yGL F) := by
  have hb : b = -a⁻¹ := by
    have : b = a⁻¹ * (-1) := by rw [← hab]; group
    rw [this, mul_neg_one]
  rw [hb]
  exact hC.minus_W a ha

theorem isConj_y_of_ConjMod' {M : ModelData F} {n : ↥M.K4}
    (h : ConjMod M (n : GL (Fin 4) F) (xyGL F)) : IsConj (yP M) (mkP M n) := by
  have := isConj_of_ConjMod n.2 M.xyGL_mem_K4 h
  have e : (⟨xyGL F, M.xyGL_mem_K4⟩ : ↥M.K4) = M.xyK := rfl
  rw [e, mkP_xyK] at this
  exact this.symm

theorem isConj_wy_of_ConjMod' {M : ModelData F} {n : ↥M.K4}
    (h : ConjMod M (n : GL (Fin 4) F) (swapGL F * yGL F)) : IsConj (tP M * yP M) (mkP M n) :=
  isConj_wy_of_ConjMod n.2 h

theorem inv_classes [Finite F] {M : ModelData F} (hG : GoodModel M) (hZ : ZsTwo M)
    (hC : ClsFacts M) {n : ↥M.K4} (hn : n ∈ Nsub M) (hsq : mkP M n * mkP M n = 1)
    (hne : mkP M n ≠ 1) :
    IsConj (yP M) (mkP M n) ∨ IsConj (tP M * yP M) (mkP M n) := by
  have h2 := hG.two_ne_zero
  have hnsq : n * n ∈ Zs M := (QuotientGroup.eq_one_iff (n * n)).1 (by
    show mkP M (n * n) = 1
    rw [map_mul]; exact hsq)
  have hZn : (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (1 : GL (Fin 2) F) 1 ∨
      (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (-1 : GL (Fin 2) F) (-1) := by
    rcases hZ _ hnsq with h | h
    · left; rw [diagGL_one]; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  rcases (mem_Nsub_iff_D M).1 hn with hD | hW
  ·
    have hcomm : (n : GL (Fin 4) F) * yGL F = yGL F * n := congrArg Subtype.val (mem_Dsub.1 hD)
    obtain ⟨a, b, hab, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 n.2 hcomm
    have hnn : (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (a * a) (b * b) := by
      rw [hab, diagGL_mul]
    rw [hnn] at hZn
    rcases hZn with h1 | h1
    · obtain ⟨haa, hbb⟩ := diagGL_inj h1
      left
      by_cases hnz : ∃ s : Fˣ, diagGL a b = sc4 s
      · exfalso
        apply hne
        obtain ⟨s, hs⟩ := hnz
        refine (QuotientGroup.eq_one_iff _).2 (mem_Zs.2 ⟨s, ?_⟩)
        rw [← hs, ← hab]
      · exact isConj_y_of_ConjMod' (by rw [hab]; exact D_plus_conj hC h2 ha hb hdet haa hbb hnz)
    · obtain ⟨haa, hbb⟩ := diagGL_inj h1
      right
      exact isConj_wy_of_ConjMod' (by rw [hab]; exact D_minus_conj hC h2 ha hb haa hbb)
  ·
    have hcomm : ((M.wK * n : ↥M.K4) : GL (Fin 4) F) * yGL F =
        yGL F * ((M.wK * n : ↥M.K4) : GL (Fin 4) F) := congrArg Subtype.val (mem_Dsub.1 hW)
    obtain ⟨a, b, hab, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 (M.wK * n).2 hcomm
    have hn' : (n : GL (Fin 4) F) = swapGL F * diagGL a b := by
      rw [← hab]
      show (n : GL (Fin 4) F) = swapGL F * (swapGL F * n)
      rw [← mul_assoc, swapGL_mul_self, one_mul]
    have hsq' : (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = diagGL (b * a) (a * b) := by
      calc (n : GL (Fin 4) F) * (n : GL (Fin 4) F) = swapGL F * diagGL a b * (swapGL F * diagGL a b) := by
            rw [← hn']
        _ = (swapGL F * diagGL a b * (swapGL F)⁻¹) * diagGL a b := by rw [swapGL_inv]; group
        _ = diagGL b a * diagGL a b := by rw [swapGL_mul_diagGL_mul_inv]
        _ = diagGL (b * a) (a * b) := diagGL_mul b a a b
    rw [hsq'] at hZn
    rcases hZn with h1 | h1
    · obtain ⟨-, hab2⟩ := diagGL_inj h1
      left
      exact isConj_y_of_ConjMod' (by rw [hn']; exact W_plus_conj hC ha hab2)
    · obtain ⟨-, hab2⟩ := diagGL_inj h1
      right
      exact isConj_wy_of_ConjMod' (by rw [hn']; exact W_minus_conj hC ha hab2)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
