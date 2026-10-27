module

public import CFSG.GH74.GLS.Stage2.Final.ModelIVKGen

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

theorem D_mem_E {M : ModelData F}
    (hno8 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ 4 ≠ -1) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    {a b : GL (Fin 2) F} (ha : a ∈ M.U2) (hb : b ∈ M.U2)
    (hdet : (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1)
    {c : Fˣ} (hca : a * a = sc2 c) (hcb : b * b = sc2 c) :
    mkP M ⟨diagGL a b, M.diagGL_mem_K4_iff.2 ⟨ha, hb, hdet⟩⟩ ∈ K1 M ⊔ K2 M := by
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
    · have hs : diagGL a b = sc4 l := by rw [hl, hm, h, scalar4_eq]
      have hs4 : sc4 l ∈ M.K4 := hs ▸ hK
      have : mkP M ⟨diagGL a b, hK⟩ = 1 := by
        have : (⟨diagGL a b, hK⟩ : ↥M.K4) = ⟨sc4 l, hs4⟩ := Subtype.ext hs
        rw [this]; exact mkP_sc4 hs4
      rw [this]; exact Subgroup.one_mem _
    · have hsc : sc2 m = sc2 l * (-1 : GL (Fin 2) F) := by
        rw [← CFSG.GH74.L5U5.scalar_neg_one_eq (F := F) 2, ← map_mul, h, mul_neg_one]
      have heq : diagGL a b = sc4 l * xyGL F := by
        rw [hl, hm, hsc, show (sc4 l : GL (Fin 4) F) = diagGL (sc2 l) (sc2 l) from scalar4_eq l, xyGL,
          diagGL_mul, mul_one]
      have hs4 : sc4 l ∈ M.K4 := by
        have : sc4 l = diagGL a b * (xyGL F)⁻¹ := by rw [heq]; group
        rw [this]
        exact M.K4.mul_mem hK (M.K4.inv_mem M.xyGL_mem_K4)
      have : mkP M ⟨diagGL a b, hK⟩ = yP M := by
        have : (⟨diagGL a b, hK⟩ : ↥M.K4) = ⟨sc4 l, hs4⟩ * M.xyK := Subtype.ext heq
        rw [this, map_mul, mkP_sc4 hs4, one_mul, mkP_xyK]
      rw [this, ← iota1_negOne M]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
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
    rcases units_sq_eq_one hcc with hc | hc
    ·
      obtain ⟨i, hii, hiU⟩ := hi
      have hi2 : (i : F) ^ 2 = -1 := by
        have := congrArg (fun u : Fˣ => (u : F)) hii
        simp only [Units.val_mul, Units.val_neg, Units.val_one] at this
        linear_combination this
      have ha' : sc2 i * a ∈ M.U2 := M.U2.mul_mem hiU ha
      have hb' : sc2 i * b ∈ M.U2 := M.U2.mul_mem hiU hb
      have hda' : ((sc2 i * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [Units.val_mul, Matrix.det_mul, det_sc2, hda, hc, hi2]
        simp
      have hdb' : ((sc2 i * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [Units.val_mul, Matrix.det_mul, det_sc2, hdb, hc, hi2]
        simp
      have hxa : sc2 i * a ∈ M.H2 := (M.mem_H2 _).2 ⟨ha', hda'⟩
      have hxb : sc2 i * b ∈ M.H2 := (M.mem_H2 _).2 ⟨hb', hdb'⟩
      have hK' : diagGL (sc2 i * a) (sc2 i * b) ∈ M.K4 :=
        M.diagGL_mem_K4_iff.2 ⟨ha', hb', by rw [hda', hdb', one_mul]⟩
      have heq : mkP M ⟨diagGL a b, hK⟩ = mkP M ⟨diagGL (sc2 i * a) (sc2 i * b), hK'⟩ :=
        (mkP_diag_eq_iff hK hK').2 ⟨i, rfl, rfl⟩
      rw [heq, ← iota_mul_eq_mkP_diag M ⟨sc2 i * a, hxa⟩ ⟨sc2 i * b, hxb⟩ hK']
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    ·
      have hda1 : ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [hda, hc]; simp
      have hdb1 : ((b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
        rw [hdb, hc]; simp
      have hxa : a ∈ M.H2 := (M.mem_H2 _).2 ⟨ha, hda1⟩
      have hxb : b ∈ M.H2 := (M.mem_H2 _).2 ⟨hb, hdb1⟩
      rw [← iota_mul_eq_mkP_diag M ⟨a, hxa⟩ ⟨b, hxb⟩ hK]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem invol_C0_mem_E {M : ModelData F} (h2 : (2 : F) ≠ 0)
    (hno8 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ 4 ≠ -1) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    {x : PG M} (hx : x ∈ C0 M) (hx2 : x * x = 1) : x ∈ K1 M ⊔ K2 M := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨a, b, hab, haU, hbU, hdet⟩ :=
    M.exists_diagGL_of_comm h2 g.2 (congrArg Subtype.val (mem_Dsub.1 hg))
  have hK : diagGL a b ∈ M.K4 := M.diagGL_mem_K4_iff.2 ⟨haU, hbU, hdet⟩
  have hg2 : g * g ∈ Zs M := by
    have h1 : mkP M (g * g) = 1 := by rw [map_mul]; exact hx2
    exact (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨c, hc⟩ := mem_Zs.1 hg2
  have hsq : diagGL (sc2 c) (sc2 c) = diagGL (a * a) (b * b) := by
    rw [← scalar4_eq, ← diagGL_mul, ← hab]
    exact hc
  obtain ⟨hca, hcb⟩ := diagGL_inj hsq
  have hgeq : g = ⟨diagGL a b, hK⟩ := Subtype.ext hab
  rw [hgeq]
  exact D_mem_E hno8 hi haU hbU hdet hca.symm hcb.symm

theorem C0_le_normalizer_K1 {M : ModelData F} (h2 : (2 : F) ≠ 0) {x : PG M} (hx : x ∈ C0 M) :
    x ∈ Subgroup.normalizer (K1 M : Set (PG M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact C0_conj_K1 M h2 hx hh
  · intro hh
    have := C0_conj_K1 M h2 ((C0 M).inv_mem hx) hh
    simpa [mul_assoc] using this

theorem invol_Cg_N1_mem_E [Finite F] {M : ModelData F} (hG : GoodModel M)
    (hno8 : ∀ l : Fˣ, sc2 l ∈ M.U2 → l ^ 4 ≠ -1) (hi : ∃ i : Fˣ, i * i = -1 ∧ sc2 i ∈ M.U2)
    {x : PG M} (hxC : x ∈ Cg M) (hxN : x ∈ Subgroup.normalizer (K1 M : Set (PG M))) (hx2 : x * x = 1) :
    x ∈ K1 M ⊔ K2 M := by
  have h2 := hG.two_ne_zero
  have hxC' : x ∈ Subgroup.centralizer ({yP M} : Set (PG M)) := hxC
  rw [centralizer_yP] at hxC'
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hxC'
  rcases (mem_Nsub_iff_D M).1 hg with hgD | hgD
  · exact invol_C0_mem_E h2 hno8 hi ⟨g, hgD, rfl⟩ hx2
  · exfalso
    have hd : mkP M (M.wK * g) ∈ C0 M := ⟨_, hgD, rfl⟩
    have hdN := C0_le_normalizer_K1 h2 hd
    have hww := wK_mul_self M
    have hwinv : M.wK⁻¹ = M.wK := inv_eq_of_mul_eq_one_right hww
    have hteq0 : mkP M g = tP M * mkP M (M.wK * g) := by
      rw [tP, ← map_mul, ← mul_assoc, hww, one_mul]
    have hteq : tP M = mkP M g * (mkP M (M.wK * g))⁻¹ := by
      rw [hteq0]; exact (mul_inv_cancel_right _ _).symm
    apply tP_not_mem_normalizer hG
    rw [hteq]
    exact Subgroup.mul_mem _ hxN ((Subgroup.normalizer (K1 M : Set (PG M))).inv_mem hdN)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
