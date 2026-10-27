module

public import CFSG.GH74.GLS.Stage2.Final.ModelConjLU
public import CFSG.GH74.GLS.Stage2.Final.ModelOdd

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

abbrev sc4 : Fˣ →* GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4)

structure LUFacts (M : ModelData F) : Prop where
  refl_conj : ∀ a ∈ M.U2, a * a = 1 → a ≠ 1 → a ≠ -1 → ∃ x ∈ M.H2, x * a * x⁻¹ = dRefl F
  perm_conj : ∃ k ∈ M.K4, k * diagGL (dRefl F) (dRefl F) * k⁻¹ = xyGL F
  w_conj : ∃ k ∈ M.K4, k * swapGL F * k⁻¹ = xyGL F
  ns_conj : ∀ a ∈ M.U2, ∃ k ∈ M.K4, k * swapGL F * k⁻¹ = swapGL F * diagGL a a⁻¹

@[expose] def ConjMod (M : ModelData F) (g g' : GL (Fin 4) F) : Prop :=
  ∃ k ∈ M.K4, ∃ s : Fˣ, sc4 s ∈ M.K4 ∧ k * g * k⁻¹ = sc4 s * g'

theorem ConjMod.of_conj {M : ModelData F} {g g' : GL (Fin 4) F} {k : GL (Fin 4) F} (hk : k ∈ M.K4)
    (h : k * g * k⁻¹ = g') : ConjMod M g g' :=
  ⟨k, hk, 1, by rw [map_one]; exact M.K4.one_mem, by rw [map_one, one_mul]; exact h⟩

theorem ConjMod.trans {M : ModelData F} {g g₁ g₂ : GL (Fin 4) F} (h₁ : ConjMod M g g₁)
    (h₂ : ConjMod M g₁ g₂) : ConjMod M g g₂ := by
  obtain ⟨k₁, hk₁, s₁, hs₁, e₁⟩ := h₁
  obtain ⟨k₂, hk₂, s₂, hs₂, e₂⟩ := h₂
  refine ⟨k₂ * k₁, M.K4.mul_mem hk₂ hk₁, s₁ * s₂, by rw [map_mul]; exact M.K4.mul_mem hs₁ hs₂, ?_⟩
  calc k₂ * k₁ * g * (k₂ * k₁)⁻¹ = k₂ * (k₁ * g * k₁⁻¹) * k₂⁻¹ := by group
    _ = k₂ * (sc4 s₁ * g₁) * k₂⁻¹ := by rw [e₁]
    _ = sc4 s₁ * (k₂ * g₁ * k₂⁻¹) := by
        have := scalar_comm s₁ k₂
        calc k₂ * (sc4 s₁ * g₁) * k₂⁻¹ = (k₂ * sc4 s₁) * g₁ * k₂⁻¹ := by group
          _ = (sc4 s₁ * k₂) * g₁ * k₂⁻¹ := by rw [this]
          _ = sc4 s₁ * (k₂ * g₁ * k₂⁻¹) := by group
    _ = sc4 s₁ * (sc4 s₂ * g₂) := by rw [e₂]
    _ = sc4 (s₁ * s₂) * g₂ := by rw [map_mul, mul_assoc]

theorem mkP_xyK (M : ModelData F) : mkP M M.xyK = yP M := by
  have hx : mkP M M.xK = 1 := (QuotientGroup.eq_one_iff _).2 (xK_mem_Zs M)
  rw [← M.xK_mul_yK, map_mul, hx, one_mul]

theorem sc4_mem_Zs {M : ModelData F} {s : Fˣ} (hs : sc4 s ∈ M.K4) :
    (⟨sc4 s, hs⟩ : ↥M.K4) ∈ Zs M :=
  mem_Zs.2 ⟨s, rfl⟩

theorem mkP_sc4 {M : ModelData F} {s : Fˣ} (hs : sc4 s ∈ M.K4) :
    mkP M ⟨sc4 s, hs⟩ = 1 :=
  (QuotientGroup.eq_one_iff _).2 (sc4_mem_Zs hs)

theorem isConj_of_ConjMod {M : ModelData F} {g g' : GL (Fin 4) F} (hg : g ∈ M.K4) (hg' : g' ∈ M.K4)
    (h : ConjMod M g g') : IsConj (mkP M ⟨g, hg⟩) (mkP M ⟨g', hg'⟩) := by
  obtain ⟨k, hk, s, hs, e⟩ := h
  rw [isConj_iff]
  refine ⟨mkP M ⟨k, hk⟩, ?_⟩
  have h1 : (⟨k, hk⟩ : ↥M.K4) * ⟨g, hg⟩ * (⟨k, hk⟩ : ↥M.K4)⁻¹ = ⟨sc4 s, hs⟩ * ⟨g', hg'⟩ :=
    Subtype.ext e
  rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul, mkP_sc4 hs, one_mul]


theorem trace_sc2 (c : Fˣ) :
    ((sc2 c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 2 * (c : F) := by
  simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem ne_one_of_trace_zero (h2 : (2 : F) ≠ 0) {a : GL (Fin 2) F}
    (ht : (a : Matrix (Fin 2) (Fin 2) F).trace = 0) : a ≠ 1 ∧ a ≠ -1 := by
  constructor
  · intro h
    rw [h] at ht
    simp at ht
    exact h2 ht
  · intro h
    rw [h] at ht
    simp at ht
    exact h2 ht

theorem diagGL_sc2_mul (c : Fˣ) (a b : GL (Fin 2) F) :
    diagGL (sc2 c * a) (sc2 c * b) = sc4 c * diagGL a b := by
  rw [show (sc4 c : GL (Fin 4) F) = diagGL (sc2 c) (sc2 c) from scalar4_eq c, diagGL_mul]

theorem sc4_mem_of_sc2_mem {M : ModelData F} {i : Fˣ} (hi : sc2 i ∈ M.U2)
    (hi2 : i * i * (i * i) = 1) : sc4 i ∈ M.K4 := by
  rw [show (sc4 i : GL (Fin 4) F) = diagGL (sc2 i) (sc2 i) from scalar4_eq i, M.diagGL_mem_K4_iff]
  refine ⟨hi, hi, ?_⟩
  rw [det_sc2]
  have h := congrArg (fun u : Fˣ => (u : F)) hi2
  simp only [Units.val_mul, Units.val_one] at h
  linear_combination h


theorem D_refl {M : ModelData F} (hF : LUFacts M) {a b : GL (Fin 2) F} (ha : a ∈ M.U2) (hb : b ∈ M.U2)
    (haa : a * a = 1) (hbb : b * b = 1) (ha1 : a ≠ 1) (ham : a ≠ -1) (hb1 : b ≠ 1) (hbm : b ≠ -1) :
    ConjMod M (diagGL a b) (xyGL F) := by
  obtain ⟨x, hxH, hx⟩ := hF.refl_conj a ha haa ha1 ham
  obtain ⟨y, hyH, hy⟩ := hF.refl_conj b hb hbb hb1 hbm
  obtain ⟨hxU, hxd⟩ := (M.mem_H2 x).1 hxH
  obtain ⟨hyU, hyd⟩ := (M.mem_H2 y).1 hyH
  have hk : diagGL x y ∈ M.K4 := M.diagGL_mem_K4_iff.2 ⟨hxU, hyU, by rw [hxd, hyd, one_mul]⟩
  have h1 : diagGL x y * diagGL a b * (diagGL x y)⁻¹ = diagGL (dRefl F) (dRefl F) := by
    rw [diagGL_inv, diagGL_mul, diagGL_mul, hx, hy]
  obtain ⟨k₂, hk₂, hk₂c⟩ := hF.perm_conj
  exact (ConjMod.of_conj hk h1).trans (ConjMod.of_conj hk₂ hk₂c)


theorem trace_sc2_mul (c : Fˣ) (a : GL (Fin 2) F) :
    ((sc2 c * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (c : F) * (a : Matrix (Fin 2) (Fin 2) F).trace := by
  have h : ((sc2 c * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (a : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul]
    simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rw [h, Matrix.trace_smul, smul_eq_mul]

theorem sc2_inv_mem {M : ModelData F} {i : Fˣ} (hi : sc2 i ∈ M.U2) : sc2 i⁻¹ ∈ M.U2 := by
  rw [← sc2_inv]
  exact M.U2.inv_mem hi

theorem sq_norm_neg {i c : Fˣ} (hii : i * i = -1) (hc : c = -1) {a : GL (Fin 2) F}
    (h : a * a = sc2 c) : (sc2 i⁻¹ * a) * (sc2 i⁻¹ * a) = 1 := by
  have e : sc2 i⁻¹ * a * (sc2 i⁻¹ * a) = sc2 (i⁻¹ * i⁻¹) * (a * a) := by
    calc sc2 i⁻¹ * a * (sc2 i⁻¹ * a) = sc2 i⁻¹ * (a * sc2 i⁻¹) * a := by group
      _ = sc2 i⁻¹ * (sc2 i⁻¹ * a) * a := by rw [← sc2_comm i⁻¹ a]
      _ = sc2 i⁻¹ * sc2 i⁻¹ * (a * a) := by group
      _ = sc2 (i⁻¹ * i⁻¹) * (a * a) := by rw [sc2_mul]
  rw [e, h, sc2_mul]
  have : i⁻¹ * i⁻¹ * c = 1 := by
    rw [← mul_inv, hii, hc, inv_neg, inv_one, neg_mul_neg, one_mul]
  rw [this, sc2_one]

theorem D_case {M : ModelData F} (hF : LUFacts M) (h2 : (2 : F) ≠ 0)
    (hno8 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ 4 ≠ -1) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    {a b : GL (Fin 2) F} (ha : a ∈ M.U2) (hb : b ∈ M.U2)
    (hdet : (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1)
    {c : Fˣ} (hca : a * a = sc2 c) (hcb : b * b = sc2 c)
    (hnz : ¬ ∃ s : Fˣ, diagGL a b = sc4 s) : ConjMod M (diagGL a b) (xyGL F) := by
  have hK : diagGL a b ∈ M.K4 := M.diagGL_mem_K4_iff.2 ⟨ha, hb, hdet⟩
  rcases ch_sq hca with ⟨l, hl, hll⟩ | ⟨hta, hda⟩ <;> rcases ch_sq hcb with ⟨m, hm, hmm⟩ | ⟨htb, hdb⟩
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
  ·
    exfalso
    have e1 := congrArg (fun u : Fˣ => (u : F)) hll
    simp only [Units.val_mul] at e1
    rw [hl, det_sc2, hdb] at hdet
    apply hno8 l (by rw [← hl]; exact ha)
    apply Units.ext
    have : (l : F) ^ 4 = -1 := by
      rw [← e1] at hdet
      linear_combination -hdet
    simpa using this
  · exfalso
    have e1 := congrArg (fun u : Fˣ => (u : F)) hmm
    simp only [Units.val_mul] at e1
    rw [hm, det_sc2, hda] at hdet
    apply hno8 m (by rw [← hm]; exact hb)
    apply Units.ext
    have : (m : F) ^ 4 = -1 := by
      rw [← e1] at hdet
      linear_combination -hdet
    simpa using this
  ·
    have hcc : c * c = 1 := by
      apply Units.ext
      rw [hda, hdb] at hdet
      simp only [Units.val_mul, Units.val_one]
      linear_combination hdet
    obtain ⟨ha1, ham⟩ := ne_one_of_trace_zero h2 hta
    obtain ⟨hb1, hbm⟩ := ne_one_of_trace_zero h2 htb
    rcases units_sq_eq_one hcc with hc | hc
    · rw [hc, sc2_one] at hca hcb
      exact D_refl hF ha hb hca hcb ha1 ham hb1 hbm
    · obtain ⟨i, hii, hiU⟩ := hi
      have hii4 : i * i * (i * i) = 1 := by rw [hii]; simp
      have hsc : sc2 i⁻¹ ∈ M.U2 := sc2_inv_mem hiU
      have ha' : sc2 i⁻¹ * a ∈ M.U2 := M.U2.mul_mem hsc ha
      have hb' : sc2 i⁻¹ * b ∈ M.U2 := M.U2.mul_mem hsc hb
      have hta' : ((sc2 i⁻¹ * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        rw [trace_sc2_mul, hta, mul_zero]
      have htb' : ((sc2 i⁻¹ * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        rw [trace_sc2_mul, htb, mul_zero]
      obtain ⟨ha1', ham'⟩ := ne_one_of_trace_zero h2 hta'
      obtain ⟨hb1', hbm'⟩ := ne_one_of_trace_zero h2 htb'
      have h1 := D_refl hF ha' hb' (sq_norm_neg hii hc hca) (sq_norm_neg hii hc hcb) ha1' ham' hb1' hbm'
      refine ConjMod.trans ?_ h1
      refine ⟨1, M.K4.one_mem, i, sc4_mem_of_sc2_mem hiU hii4, ?_⟩
      rw [inv_one, mul_one, one_mul, ← diagGL_sc2_mul, ← mul_assoc, ← mul_assoc, sc2_mul,
        mul_inv_cancel, sc2_one, one_mul, one_mul]


theorem W_one {M : ModelData F} (hF : LUFacts M) {a : GL (Fin 2) F} (ha : a ∈ M.U2) :
    ConjMod M (swapGL F * diagGL a a⁻¹) (xyGL F) := by
  obtain ⟨k, hk, hkc⟩ := hF.ns_conj a ha
  obtain ⟨k₂, hk₂, hk₂c⟩ := hF.w_conj
  have h1 : ConjMod M (swapGL F * diagGL a a⁻¹) (swapGL F) :=
    ConjMod.of_conj (M.K4.inv_mem hk) (by rw [← hkc]; group)
  exact h1.trans (ConjMod.of_conj hk₂ hk₂c)

theorem W_case {M : ModelData F} (hF : LUFacts M) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    {a b : GL (Fin 2) F} (ha : a ∈ M.U2) {c : Fˣ} (hab : a * b = sc2 c) (hcc : c * c = 1) :
    ConjMod M (swapGL F * diagGL a b) (xyGL F) := by
  rcases units_sq_eq_one hcc with hc | hc
  · rw [hc, sc2_one] at hab
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
    rw [hb']
    exact W_one hF ha
  · obtain ⟨i, hii, hiU⟩ := hi
    have hii4 : i * i * (i * i) = 1 := by rw [hii]; simp
    have hsc : sc2 i⁻¹ ∈ M.U2 := sc2_inv_mem hiU
    have hab' : (sc2 i⁻¹ * a) * (sc2 i⁻¹ * b) = 1 := by
      calc (sc2 i⁻¹ * a) * (sc2 i⁻¹ * b) = sc2 i⁻¹ * (a * sc2 i⁻¹) * b := by group
        _ = sc2 i⁻¹ * (sc2 i⁻¹ * a) * b := by rw [← sc2_comm i⁻¹ a]
        _ = sc2 i⁻¹ * sc2 i⁻¹ * (a * b) := by group
        _ = 1 := by
          rw [hab, sc2_mul, sc2_mul]
          have : i⁻¹ * i⁻¹ * c = 1 := by
            rw [← mul_inv, hii, hc, inv_neg, inv_one, neg_mul_neg, one_mul]
          rw [this, sc2_one]
    have hb'' : sc2 i⁻¹ * b = (sc2 i⁻¹ * a)⁻¹ := eq_inv_of_mul_eq_one_right hab'
    have h1 := W_one hF (M.U2.mul_mem hsc ha)
    rw [← hb''] at h1
    refine ConjMod.trans ⟨1, M.K4.one_mem, i, sc4_mem_of_sc2_mem hiU hii4, ?_⟩ h1
    have hc4 : sc4 i * diagGL (sc2 i⁻¹ * a) (sc2 i⁻¹ * b) = diagGL a b := by
      rw [← diagGL_sc2_mul, ← mul_assoc, ← mul_assoc, sc2_mul, mul_inv_cancel, sc2_one, one_mul,
        one_mul]
    rw [inv_one, mul_one, one_mul]
    calc swapGL F * diagGL a b = swapGL F * (sc4 i * diagGL (sc2 i⁻¹ * a) (sc2 i⁻¹ * b)) := by
          rw [hc4]
      _ = sc4 i * (swapGL F * diagGL (sc2 i⁻¹ * a) (sc2 i⁻¹ * b)) := by
          rw [← mul_assoc, scalar_comm i (swapGL F), mul_assoc]


theorem inv_Nsub_conj_y {M : ModelData F} (hF : LUFacts M) (h2 : (2 : F) ≠ 0)
    (hno8 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ 4 ≠ -1) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    {n : ↥M.K4} (hn : n ∈ Nsub M) (hsq : mkP M n * mkP M n = 1) (hne : mkP M n ≠ 1) :
    IsConj (yP M) (mkP M n) := by
  have hnsq : n * n ∈ Zs M := (QuotientGroup.eq_one_iff (n * n)).1 (by
    show mkP M (n * n) = 1
    rw [map_mul]; exact hsq)
  obtain ⟨c, hc⟩ := mem_Zs.1 hnsq
  have hcGL : sc4 c = (n : GL (Fin 4) F) * (n : GL (Fin 4) F) := hc
  have hfin : ∀ (hCM : ConjMod M (n : GL (Fin 4) F) (xyGL F)), IsConj (yP M) (mkP M n) := fun hCM => by
    have := isConj_of_ConjMod n.2 M.xyGL_mem_K4 hCM
    have e : (⟨xyGL F, M.xyGL_mem_K4⟩ : ↥M.K4) = M.xyK := rfl
    rw [e, mkP_xyK] at this
    exact this.symm
  rcases (mem_Nsub_iff_D M).1 hn with hD | hW
  · have hcomm : (n : GL (Fin 4) F) * yGL F = yGL F * n := congrArg Subtype.val (mem_Dsub.1 hD)
    obtain ⟨a, b, hab, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 n.2 hcomm
    have hsq' : diagGL (a * a) (b * b) = diagGL (sc2 c) (sc2 c) := by
      rw [← diagGL_mul, ← hab, ← hcGL, scalar4_eq]
    obtain ⟨hca, hcb⟩ := diagGL_inj hsq'
    have hnz : ¬ ∃ s : Fˣ, diagGL a b = sc4 s := by
      rintro ⟨s, hs⟩
      apply hne
      refine (QuotientGroup.eq_one_iff _).2 (mem_Zs.2 ⟨s, ?_⟩)
      rw [← hs, ← hab]
    exact hfin (by rw [hab]; exact D_case hF h2 hno8 hi ha hb hdet hca hcb hnz)
  · have hcomm : ((M.wK * n : ↥M.K4) : GL (Fin 4) F) * yGL F =
        yGL F * ((M.wK * n : ↥M.K4) : GL (Fin 4) F) :=
      congrArg Subtype.val (mem_Dsub.1 hW)
    obtain ⟨a, b, hab, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 (M.wK * n).2 hcomm
    have hn' : (n : GL (Fin 4) F) = swapGL F * diagGL a b := by
      rw [← hab]
      show (n : GL (Fin 4) F) = swapGL F * (swapGL F * n)
      rw [← mul_assoc, swapGL_mul_self, one_mul]
    have hsq' : diagGL (b * a) (a * b) = diagGL (sc2 c) (sc2 c) := by
      rw [← scalar4_eq, hcGL, hn']
      calc diagGL (b * a) (a * b) = diagGL b a * diagGL a b := (diagGL_mul b a a b).symm
        _ = (swapGL F * diagGL a b * (swapGL F)⁻¹) * diagGL a b := by
            rw [swapGL_mul_diagGL_mul_inv]
        _ = swapGL F * diagGL a b * (swapGL F * diagGL a b) := by
            rw [swapGL_inv]; group
    obtain ⟨hba, hab2⟩ := diagGL_inj hsq'
    have hcc : c * c = 1 := by
      apply Units.ext
      have h1 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F).det) hab2
      simp only [Units.val_mul, Matrix.det_mul, det_sc2] at h1
      rw [hdet] at h1
      simp only [Units.val_mul, Units.val_one]
      linear_combination -h1
    exact hfin (by rw [hn']; exact W_case hF hi ha hab2 hcc)


theorem exists_conj_mem_Cg [Finite F] (M : ModelData F) (hodd : Odd (Nsub M).index) {u : PG M}
    (hu : orderOf u = 2) : ∃ g : PG M, g * u * g⁻¹ ∈ Subgroup.centralizer {yP M} := by
  have hodd' : Odd (Subgroup.centralizer {yP M}).index := by rw [index_C]; exact hodd
  obtain ⟨S, hS⟩ := sylow_of_odd_index (Subgroup.centralizer {yP M}) hodd'
    (default : Sylow 2 ↥(Subgroup.centralizer {yP M}))
  have hzp : IsPGroup 2 (Subgroup.zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hu, pow_one]
  obtain ⟨T, hT⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PG M) S T
  have hcoe : ((g • S : Sylow 2 (PG M)) : Subgroup (PG M)) =
      (S : Subgroup (PG M)).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have huT : u ∈ (T : Subgroup (PG M)) := hT (Subgroup.mem_zpowers u)
  rw [← hg, hcoe] at huT
  obtain ⟨s, hs, hsu⟩ := Subgroup.mem_map.1 huT
  refine ⟨g⁻¹, ?_⟩
  have hsu' : g * s * g⁻¹ = u := hsu
  have : g⁻¹ * u * g⁻¹⁻¹ = s := by rw [← hsu']; group
  rw [this]
  rw [hS] at hs
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hs
  exact t.2

theorem all_inv_conj_y [Finite F] {M : ModelData F} (hF : LUFacts M) (h2 : (2 : F) ≠ 0)
    (hno8 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ 4 ≠ -1) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    (hodd : Odd (Nsub M).index) {u : PG M} (hu : orderOf u = 2) : IsConj (yP M) u := by
  obtain ⟨g, hg⟩ := exists_conj_mem_Cg M hodd hu
  rw [centralizer_yP] at hg
  obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.1 hg
  have hnu' : mkP M n = g * u * g⁻¹ := hnu
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have hsq : mkP M n * mkP M n = 1 := by
    rw [hnu']
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hne : mkP M n ≠ 1 := by
    intro h
    rw [hnu'] at h
    have : u = 1 := by
      have e : u = g⁻¹ * (g * u * g⁻¹) * g := by group
      rw [e, h]; group
    rw [this, orderOf_one] at hu
    omega
  have h1 := inv_Nsub_conj_y hF h2 hno8 hi hn hsq hne
  rw [hnu'] at h1
  exact h1.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)


theorem isConj_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : G}
    (h : IsConj (e a) (e b)) : IsConj a b := by
  have := MonoidHom.map_isConj e.symm.toMonoidHom h
  simpa using this

theorem luFacts_lin (h2 : (2 : F) ≠ 0) : LUFacts (ModelData.lin F) where
  refl_conj a _ ha h1 hm1 := by
    obtain ⟨x, hxdet, hx⟩ := refl_conj_lin h2 ha h1 hm1
    exact ⟨x, ((ModelData.lin F).mem_H2 x).2 ⟨Subgroup.mem_top _, hxdet⟩, hx⟩
  perm_conj := perm_conj_lin
  w_conj := w_conj_lin h2
  ns_conj a _ := ns_conj_lin h2 a

theorem luFacts_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) : LUFacts (ModelData.uni hF) where
  refl_conj a haU ha h1 hm1 := by
    obtain ⟨x, hxU, hxdet, hx⟩ := refl_conj_uni hF hp2 haU ha h1 hm1
    exact ⟨x, ((ModelData.uni hF).mem_H2 x).2 ⟨hxU, hxdet⟩, hx⟩
  perm_conj := perm_conj_uni hF
  w_conj := w_conj_uni hF hp2
  ns_conj a ha := ns_conj_uni hF hp2 a ha

theorem orderOf_eq_eight (h2 : (2 : F) ≠ 0) {l : Fˣ} (h : l ^ 4 = -1) : orderOf l = 8 := by
  have hn1 : (-1 : Fˣ) ≠ 1 := by
    intro h'
    have := congrArg (fun u : Fˣ => (u : F)) h'
    simp only [Units.val_neg, Units.val_one] at this
    apply h2
    linear_combination -this
  have h8 : l ^ 8 = 1 := by
    have : l ^ 8 = (l ^ 4) ^ 2 := by rw [← pow_mul]
    rw [this, h]; simp
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := l) (by norm_num; rw [h]; exact hn1)
    (by norm_num; exact h8)
  simpa using this

theorem hno8_lin [Finite F] (h2 : (2 : F) ≠ 0) (h8 : Nat.card F % 8 = 5) :
    ∀ l : Fˣ, sc2 l ∈ (ModelData.lin F).U2 → l ^ 4 ≠ -1 := by
  intro l _ hl
  have hord := orderOf_eq_eight h2 hl
  have hdvd : orderOf l ∣ Nat.card F - 1 := by
    rw [← Nat.card_units]; exact orderOf_dvd_natCard l
  rw [hord] at hdvd
  have hpos : 0 < Nat.card F := Nat.card_pos
  omega

theorem hno8_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) (h8 : p ^ f % 8 = 3) :
    ∀ l : Fˣ, sc2 l ∈ (ModelData.uni hF).U2 → l ^ 4 ≠ -1 := by
  intro l hlU hl
  have hord := orderOf_eq_eight h2 hl
  have h1 : l ^ (p ^ f + 1) = 1 := (sc2_mem_uni_iff hF l).1 hlU
  have hdvd : orderOf l ∣ p ^ f + 1 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at hdvd
  omega

theorem hi_lin [Finite F] (h4 : Nat.card F % 4 = 1) :
    ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ (ModelData.lin F).U2 := by
  have : Fintype F := Fintype.ofFinite F
  have hsq : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.2 (by
    rw [← Nat.card_eq_fintype_card]; omega)
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  refine ⟨Units.mk0 r hr0, Units.ext (by simpa using hr.symm), Subgroup.mem_top _⟩

theorem hi_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (h8 : p ^ f % 8 = 3) :
    ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ (ModelData.uni hF).U2 := by
  have : Fintype F := Fintype.ofFinite F
  have hq4 : (p ^ f) ^ 2 % 4 = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f = 8 * m + 3 := ⟨p ^ f / 8, by omega⟩
    rw [hm]
    ring_nf
    omega
  have hsq : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.2 (by
    rw [← Nat.card_eq_fintype_card, hF]; omega)
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hii : Units.mk0 r hr0 * Units.mk0 r hr0 = -1 := Units.ext (by simpa using hr.symm)
  refine ⟨Units.mk0 r hr0, hii, (sc2_mem_uni_iff hF _).2 ?_⟩
  have h4 : (Units.mk0 r hr0) ^ 4 = 1 := by
    have : (Units.mk0 r hr0) ^ 4 = (Units.mk0 r hr0 * Units.mk0 r hr0) ^ 2 := by
      rw [← pow_two, ← pow_mul]
    rw [this, hii]; simp
  obtain ⟨m, hm⟩ : 4 ∣ p ^ f + 1 := by omega
  rw [hm, pow_mul, h4, one_pow]

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem modelOneClass : ModelOneClass := by
  intro Gs _ _ p f hp hp2 hcases u v hu hv
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have : Fact p.Prime := ⟨hp⟩
  rcases hcases with ⟨h8, hL⟩ | ⟨h8, hU⟩
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have e' : Gs ≃* PG (ModelData.lin F) := e
    have hall : ∀ x : PG (ModelData.lin F), orderOf x = 2 → IsConj (yP (ModelData.lin F)) x :=
      fun x hx => all_inv_conj_y (luFacts_lin h2) h2 (hno8_lin h2 (by rw [hF]; exact h8))
        (hi_lin (by rw [hF]; omega)) (odd_index_Nsub _ h2 (ModelOrd.odd_index_lin F h2)) hx
    have hu' : orderOf (e' u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (e' v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    exact isConj_of_equiv e' ((hall _ hu').symm.trans (hall _ hv'))
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    have e' : Gs ≃* PG (ModelData.uni hF) := e
    have hall : ∀ x : PG (ModelData.uni hF), orderOf x = 2 → IsConj (yP (ModelData.uni hF)) x :=
      fun x hx => all_inv_conj_y (luFacts_uni hF hp2) h2 (hno8_uni hF h2 h8) (hi_uni hF h8)
        (odd_index_Nsub _ h2 (ModelOrd.odd_index_uni hF hp2)) hx
    have hu' : orderOf (e' u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (e' v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    exact isConj_of_equiv e' ((hall _ hu').symm.trans (hall _ hv'))

end CFSG.GH74.GLS.Stage2.Final
