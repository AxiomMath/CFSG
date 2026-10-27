module

public import CFSG.Certificates.Kernel.J4TreeTop.WalkCover
public import CFSG.Certificates.Kernel.J4TreeTop.Node1Sound

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem commE_eq (T : Tabs) (K Ki : ℕ) :
    commE T K Ki = commV T K Ki ((List.range 11).map (2 ^ ·)) := by
  unfold commE commV
  rw [List.map_map]
  rfl

theorem xorSel_eq_xm : ∀ (L : List ℕ) (I : ℕ), xorSel L I = xm L I
  | [], _ => rfl
  | c :: L, I => by rw [xorSel, xm_cons, xorSel_eq_xm L]

theorem eclassOK_cons {T : Tabs} {z e : ℕ} {D : List ℕ} (h : eclassOK T z e D = true) :
    ∃ Ki m : ℕ, ∃ l : List ℕ, D = Ki :: m :: l := by
  rcases D with _ | ⟨Ki, _ | ⟨m, l⟩⟩
  · simp [eclassOK] at h
  · simp [eclassOK] at h
  · exact ⟨Ki, m, l, rfl⟩

theorem treeElt_z0 (z : ℕ) : burnsideJ4NP_treeElt (z, 0) = eta uJ 11 z := by
  unfold burnsideJ4NP_treeElt
  rw [Kel_zero, mul_one]


theorem eclass_marked {T : Tabs} (hT : tabsOK T = true) {z : ℕ} (hz : z < 2048)
    {D : ℕ → List ℕ} (hD : ∀ e < 1024, eclassOK T z e (D e) = true) {x : J} (hxP : x ∈ P0)
    (hxz : x * eta uJ 11 z = eta uJ 11 z * x) (hsq : x * x = 1) (hx1 : x ≠ 1)
    (hxz1 : x ≠ eta uJ 11 z) :
    ∃ e < 1024, ∃ Ki m : ℕ, ∃ l : List ℕ, D e = Ki :: m :: l ∧ ∃ I < 2 ^ m,
      ((l.drop m).headD 0).testBit I = true ∧ ∃ d : ℕ, ∃ y : J,
        PK y (ccT T (xorSel (l.take m) I, e)) ∧
        (eta uJ 11 d * x * (eta uJ 11 d)⁻¹ = y ∨
          eta uJ 11 d * x * (eta uJ 11 d)⁻¹ = y * eta uJ 11 z) := by
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hEm : ∀ v, eta uJ 11 v ∈ Eg uJ 11 := fun v => eta_mem_Eg 11 le_rfl v
  obtain ⟨c, hc, e, he, rfl⟩ := exists_eta_mul_Kel j4Facts.mat j4Facts hxP
  obtain ⟨Ki, m, l, hDe⟩ := eclassOK_cons (hD e he)
  have hDe' := hD e he
  rw [hDe] at hDe'
  obtain ⟨hinv, -, hlen, hcs, hspan, hleaf⟩ := eclassOK_spec hDe'
  have hvs : ∀ v ∈ (List.range 11).map (2 ^ ·), v < 2048 := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hv
    rw [List.mem_range] at hj
    calc 2 ^ j < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hj
      _ = 2048 := by norm_num
  have hzs : ∀ c ∈ [z], c < 2048 := fun c hc' => by
    rw [List.mem_singleton] at hc'
    rw [hc']
    exact hz
  have hsp : XSpan ([z].map (fun c => translK (T.eta c)) ++
      commV T (T.kel e) Ki ((List.range 11).map (2 ^ ·)) ++
      (l.take m).map (fun c => translK (T.eta c))) (tau (eta uJ 11 c)) := by
    have := spanAll_spec hspan (tau (eta uJ 11 c)) (lt_of_lt_of_le (tau_lt _) (by norm_num))
    rw [commE_eq] at this
    exact this
  obtain ⟨I₁, I₂, I₃, hI₃, hconj⟩ := conj_marked hT he hinv hzs hvs hcs hsp
  rw [hlen] at hI₃
  set g := eta uJ 11 (xm ((List.range 11).map (2 ^ ·)) I₂) with hg
  set w := eta uJ 11 (xm [z] I₁) with hw
  set s := xm (l.take m) I₃ with hs
  set x := eta uJ 11 c * Kel e with hx
  set y := eta uJ 11 s * Kel e with hy
  have hgE : g ∈ Eg uJ 11 := hEm _
  have hwz : w = 1 ∨ w = eta uJ 11 z := by
    have h0 : xm ([] : List ℕ) (I₁ / 2) = 0 := rfl
    rw [hw, xm_cons, h0]
    split_ifs
    · rw [Nat.xor_zero]
      exact Or.inr rfl
    · rw [Nat.xor_zero, eta_zero]
      exact Or.inl rfl
  have hwE : w ∈ Eg uJ 11 := hEm _
  have hww : w * w = 1 := Eg_sq hEl hwE
  have hgz : g * eta uJ 11 z = eta uJ 11 z * g := Eg_comm hEl hgE (hEm z)
  have hgw : g * w = w * g := Eg_comm hEl hgE hwE
  have hgz' : g⁻¹ * eta uJ 11 z = eta uJ 11 z * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgz, mul_assoc, mul_inv_cancel, mul_one]
  have hx'z : g * x * g⁻¹ * eta uJ 11 z = eta uJ 11 z * (g * x * g⁻¹) := by
    calc g * x * g⁻¹ * eta uJ 11 z = g * x * (g⁻¹ * eta uJ 11 z) := by group
      _ = g * (x * eta uJ 11 z) * g⁻¹ := by rw [hgz']; group
      _ = g * (eta uJ 11 z * x) * g⁻¹ := by rw [hxz]
      _ = (g * eta uJ 11 z) * x * g⁻¹ := by group
      _ = eta uJ 11 z * (g * x * g⁻¹) := by rw [hgz]; group
  have hx'w : g * x * g⁻¹ * w = w * (g * x * g⁻¹) := by
    rcases hwz with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]
      exact hx'z
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  have hyx : y = w * (g * x * g⁻¹) := by
    rw [hconj, ← mul_assoc, hww, one_mul]
  have hysq : y * y = 1 := by
    rw [hyx]
    calc w * (g * x * g⁻¹) * (w * (g * x * g⁻¹))
        = w * ((g * x * g⁻¹) * w) * (g * x * g⁻¹) := by group
      _ = w * w * ((g * x * g⁻¹) * (g * x * g⁻¹)) := by rw [hx'w]; group
      _ = 1 := by rw [hww, hx'2, one_mul]
  have hsl : s < 2048 :=
    lt_of_lt_of_le (xm_lt (k := 11) (fun c hc' => by have := hcs c hc'; omega) I₃) (by norm_num)
  have hypr : PK y (prodFrom (T.kel e) ((l.take m).map fun c => M (M Ki (T.eta c)) (T.kel e)) I₃) := by
    have := pk_rep hT he hinv hcs (pk_kel hT he) I₃
    rw [← hs] at this
    have e1 : Kel e * ((Kel e)⁻¹ * eta uJ 11 s * Kel e) = y := by rw [hy]; group
    rw [e1] at this
    exact this
  have hycc : PK y (ccT T (xorSel (l.take m) I₃, e)) := by
    rw [xorSel_eq_xm]
    exact pk_mul (pk_eta hT hsl) (pk_kel hT he)
  have h1 : e ≠ 0 ∨ I₃ ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨he0, hI0⟩ := hcon
    have hy1 : y = 1 := by rw [hy, hs, hI0, xm_zero, eta_zero, he0, Kel_zero, one_mul]
    have hx'1 : g * x * g⁻¹ = w := by
      have := hconj
      rw [hy1, mul_one] at this
      exact this
    have hxw : x = w := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * w * g := by rw [hx'1]
        _ = g⁻¹ * (g * w) := by rw [mul_assoc, ← hgw]
        _ = w := by group
    rcases hwz with h | h
    · exact hx1 (hxw.trans h)
    · exact hxz1 (hxw.trans h)
  have hbit := eclass_leaf_sound (hleaf I₃ hI₃) hypr hysq h1
  have hfin : g * x * g⁻¹ = y ∨ g * x * g⁻¹ = y * eta uJ 11 z := by
    rcases hwz with h | h
    · left
      rw [hconj, h, one_mul]
    · right
      have hyz : y * eta uJ 11 z = eta uJ 11 z * y := by
        rw [hyx, h]
        calc eta uJ 11 z * (g * x * g⁻¹) * eta uJ 11 z
            = eta uJ 11 z * ((g * x * g⁻¹) * eta uJ 11 z) := by group
          _ = eta uJ 11 z * (eta uJ 11 z * (g * x * g⁻¹)) := by rw [hx'z]
      rw [hconj, h, ← hyz]
  exact ⟨e, he, Ki, m, l, hDe, I₃, hI₃, hbit, xm ((List.range 11).map (2 ^ ·)) I₂, y, hycc, hfin⟩

theorem node1_cover {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {z : ℕ}
    (hz : coordOK (z, 0) = true) {g : C1Glob} (hg : c1GlobOK T z g = true) {D R : ℕ → List ℕ}
    (hD : ∀ e < 1024, eclassOK T z e (D e) = true)
    (hR : ∀ e < 1024, cover1OK T z e g (D e) (R e) = true) {x : J} (hxP : x ∈ P0)
    (hxz : x ∈ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)}) (hsq : x * x = 1)
    (hx1 : x ≠ 1) (hxz1 : x ≠ burnsideJ4NP_treeElt (z, 0)) :
    (∃ n ∈ Hj ⊓ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)},
        burnsideJ4NP_treeTest (burnsideJ4NP_encJ (n * x * n⁻¹)) = false ∧
        burnsideJ4NP_treeTest
          (burnsideJ4NP_encJ (n * x * n⁻¹ * burnsideJ4NP_treeElt (z, 0))) = false) ∨
      ∃ j < topNode1.children.length,
        ∃ n ∈ Hj ⊓ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)},
        n * x * n⁻¹ = burnsideJ4NP_treeElt (topNode1.children.getD j default).y ∨
          n * x * n⁻¹ = burnsideJ4NP_treeElt (topNode1.children.getD j default).y *
            burnsideJ4NP_treeElt (z, 0) := by
  have hEl : Elem uJ 11 := elem_uJ j4Facts.mat
  have hz' : z < 2048 := by
    unfold coordOK at hz
    simp only [Bool.and_eq_true, Nat.blt_eq] at hz
    exact hz.1
  have hz0 := treeElt_z0 z
  rw [hz0] at hxz hxz1 ⊢
  have hzz : eta uJ 11 z * eta uJ 11 z = 1 := eta_sq hEl z
  have hxz' : x * eta uJ 11 z = eta uJ 11 z * x :=
    (Subgroup.mem_centralizer_iff.mp hxz (eta uJ 11 z) (Set.mem_singleton _)).symm
  obtain ⟨e, he, Ki, m, l, hDe, I, -, hbit, d, y, hy, hc'⟩ :=
    eclass_marked hT hz' hD hxP hxz' hsq hx1 hxz1
  have hRe := hR e he
  rw [hDe] at hRe
  have hcov := cover1_sound hT hsx hz hg hRe hbit hy
  rw [hz0] at hcov
  have huE : eta uJ 11 d ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl d
  have huC : eta uJ 11 d ∈ Hj ⊓ Subgroup.centralizer {eta uJ 11 z} :=
    Subgroup.mem_inf.mpr ⟨Eg_le_Hj huE, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact Eg_comm hEl (eta_mem_Eg 11 le_rfl z) huE⟩
  rcases hcov with ⟨ht1, ht2⟩ | ⟨j, hj, n, hn, hnj⟩
  · left
    refine ⟨eta uJ 11 d, huC, ?_⟩
    rcases hc' with h | h
    · rw [h]
      exact ⟨ht1, ht2⟩
    · rw [h, mul_assoc, hzz, mul_one]
      exact ⟨ht2, ht1⟩
  · right
    have hnz : n * eta uJ 11 z * n⁻¹ = eta uJ 11 z := by
      rw [← Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2 (eta uJ 11 z)
        (Set.mem_singleton _), mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨j, hj, n * eta uJ 11 d, Subgroup.mul_mem _ hn huC, ?_⟩
    have e1 : n * eta uJ 11 d * x * (n * eta uJ 11 d)⁻¹ =
        n * (eta uJ 11 d * x * (eta uJ 11 d)⁻¹) * n⁻¹ := by group
    rw [e1]
    rcases hc' with h | h
    · rw [h]
      exact hnj
    · rw [h]
      have e2 : n * (y * eta uJ 11 z) * n⁻¹ = n * y * n⁻¹ * (n * eta uJ 11 z * n⁻¹) := by group
      rw [e2, hnz]
      rcases hnj with h' | h'
      · rw [h']
        exact Or.inr rfl
      · rw [h', mul_assoc, hzz, mul_one]
        exact Or.inl rfl

end CFSG.KC.J4TreeT
