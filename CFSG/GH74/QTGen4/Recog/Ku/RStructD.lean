module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructB
public import CFSG.GH74.QTGen4.Recog.Ku.RStruct
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.GH74.QTGen4.Ku

theorem alt_zero_of_order3 {F A : Type} [Field F] [Group A] (hcomm : ∀ x y : A, x * y = y * x)
    (B : A → A → F)
    (hl : ∀ x x' y, B (x * x') y = B x y + B x' y)
    (hr : ∀ x y y', B x (y * y') = B x y + B x y')
    (halt : ∀ x, B x x = 0)
    (N : A →* A) (μ : F) (hμ : μ ≠ 1)
    (hB : ∀ x y, B (N x) (N y) = μ * B x y)
    (hN3 : ∀ x, N (N (N x)) = x)
    (hfix : ∀ x, N x = x → x = 1)
    (hcov : ∀ x, x ≠ 1 → ∀ y, y = 1 ∨ y = x ∨ y = N x ∨ y = N (N x)) :
    ∀ x y, B x y = 0 := by
  have hr1 : ∀ z, B z 1 = 0 := fun z => by
    have h := hr z 1 1
    simpa using h
  have hl1 : ∀ y, B 1 y = 0 := fun y => by
    have h := hl 1 1 y
    simpa using h
  have hinv : ∀ x y, B x y⁻¹ = -B x y := fun x y => by
    have h := hr x y y⁻¹
    rw [mul_inv_cancel, hr1] at h
    linear_combination (-1 : F) * h
  intro x y
  by_cases hx : x = 1
  · subst hx
    exact hl1 y
  have hu0 : N (N x) * N x * x = 1 := by
    apply hfix
    rw [map_mul, map_mul, hN3, mul_assoc, hcomm x]
  have hu : N (N x) = (x * N x)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hcomm x (N x), ← mul_assoc]
    exact hu0
  have hsym : B (N x) x = -B x (N x) := by
    have h := halt (x * N x)
    simp only [hl, hr, halt] at h
    linear_combination h
  have hμt : (μ - 1) * B x (N x) = 0 := by
    have e1 := hB x (N x)
    have e2 : B (N x) (N (N x)) = -B (N x) x := by
      rw [hu, hinv, hr, halt, add_zero]
    rw [e2, hsym] at e1
    linear_combination (-1 : F) * e1
  have ht0 : B x (N x) = 0 := by
    rcases mul_eq_zero.mp hμt with h | h
    · exact absurd (sub_eq_zero.mp h) hμ
    · exact h
  rcases hcov x hx y with h | h | h | h
  · rw [h]; exact hr1 x
  · rw [h]; exact halt x
  · rw [h]; exact ht0
  · have e : B x (N (N x)) = -(B x x + B x (N x)) := by
      rw [hu, hinv, hr]
    rw [h]
    linear_combination e - halt x - ht0

theorem det_scale_of_fix {F : Type} [Field F] {D : Matrix (Fin 2) (Fin 2) F}
    (hdet : D 0 0 * D 1 1 - D 0 1 * D 1 0 = 1) {a p q : F}
    (e0 : a * p = D 0 0 * p + D 0 1 * q) (e1 : a * q = D 1 0 * p + D 1 1 * q)
    (x0 x1 : F) :
    a * (p * (D 1 0 * x0 + D 1 1 * x1) - q * (D 0 0 * x0 + D 0 1 * x1)) = p * x1 - q * x0 := by
  linear_combination (D 1 0 * x0 + D 1 1 * x1) * e0 - (D 0 0 * x0 + D 0 1 * x1) * e1
    + (p * x1 - q * x0) * hdet

theorem trace_zero_of_fix {F : Type} [Field F] (h2 : (2 : F) = 0) {a b c d p q : F}
    (hdet : a * d - b * c = 1) (h1 : a * p + b * q = p) (h1' : c * p + d * q = q)
    (hne : p ≠ 0 ∨ q ≠ 0) : a + d = 0 := by
  have hX : (a - 1) * (d - 1) - b * c = 0 := by
    have hdp : ((a - 1) * (d - 1) - b * c) * p = 0 := by
      linear_combination (d - 1) * h1 - b * h1'
    have hdq : ((a - 1) * (d - 1) - b * c) * q = 0 := by
      linear_combination (a - 1) * h1' - c * h1
    rcases hne with hp | hq
    · exact (mul_eq_zero.mp hdp).resolve_right hp
    · exact (mul_eq_zero.mp hdq).resolve_right hq
  linear_combination (-1 : F) * hX + hdet + h2

theorem mat_comm_of_fix {F : Type} [Field F] (h2 : (2 : F) = 0)
    {a b c d a' b' c' d' p q : F}
    (hdet : a * d - b * c = 1) (hdet' : a' * d' - b' * c' = 1)
    (h1 : a * p + b * q = p) (h1' : c * p + d * q = q)
    (h1'' : a' * p + b' * q = p) (h1''' : c' * p + d' * q = q)
    (hne : p ≠ 0 ∨ q ≠ 0) :
    a * a' + b * c' = a' * a + b' * c ∧ a * b' + b * d' = a' * b + b' * d ∧
      c * a' + d * c' = c' * a + d' * c ∧ c * b' + d * d' = c' * b + d' * d := by
  have ht := trace_zero_of_fix h2 hdet h1 h1' hne
  have ht' := trace_zero_of_fix h2 hdet' h1'' h1''' hne
  have hd : d = a := by linear_combination ht - a * h2
  have hd' : d' = a' := by linear_combination ht' - a' * h2
  rw [hd] at h1' ⊢
  rw [hd'] at h1''' ⊢
  have hoff := offdiag_comm_of_fix h2 h1 h1' h1'' h1''' hne
  refine ⟨by linear_combination hoff, by ring, by ring, by linear_combination (-1 : F) * hoff⟩

section Commutator

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem conjD_one {L V : Subgroup G} {n : ℕ} (D : NatL2Data L V n) (w : Fin 2 → D.K) :
    D.conj 1 w = w := by
  change Additive.ofMul (D.E (conjAct V 1 (D.E.symm (Additive.toMul w)))) = w
  rw [map_one, MulAut.one_apply, MulEquiv.apply_symm_apply]
  rfl

theorem conjD_mul_inv {L V : Subgroup G} {n : ℕ} (D : NatL2Data L V n)
    (g : Subgroup.normalizer (V : Set G)) (w : Fin 2 → D.K) :
    D.conj g (D.conj g⁻¹ w) = w := by
  rw [← D.conj_mul, mul_inv_cancel, conjD_one]

theorem conj_comm_triv {L V : Subgroup G} {n : ℕ} (D : NatL2Data L V n)
    (g k : Subgroup.normalizer (V : Set G))
    (hcomm : ∀ w, D.conj g (D.conj k w) = D.conj k (D.conj g w)) :
    ∀ u, D.conj (g * k * g⁻¹ * k⁻¹) u = u := by
  intro u
  obtain ⟨c, hc⟩ : ∃ c, c = g * k * g⁻¹ * k⁻¹ := ⟨_, rfl⟩
  rw [← hc]
  have hstar : ∀ w, D.conj c (D.conj k (D.conj g w)) = D.conj k (D.conj g w) := by
    intro w
    have e2 : c * k * g = g * k := by rw [hc]; group
    calc D.conj c (D.conj k (D.conj g w)) = D.conj (c * k * g) w := by rw [D.conj_mul, D.conj_mul]
      _ = D.conj (g * k) w := by rw [e2]
      _ = D.conj g (D.conj k w) := D.conj_mul g k w
      _ = D.conj k (D.conj g w) := hcomm w
  have hu := hstar (D.conj g⁻¹ (D.conj k⁻¹ u))
  rw [conjD_mul_inv, conjD_mul_inv] at hu
  exact hu

theorem mem_centralizer_of_conj_triv {L V : Subgroup G} {n : ℕ} (D : NatL2Data L V n)
    (c : Subgroup.normalizer (V : Set G)) (hc : ∀ u, D.conj c u = u) (v : ↥V) :
    (v : G) * (c : G) = (c : G) * v := by
  have key := D.conj_apply c v
  rw [hc] at key
  have h1 := D.E.injective (Multiplicative.toAdd.injective key)
  have h2 := congrArg (fun x : ↥V => (x : G)) h1
  simp only [conjAct_apply_coe'] at h2
  calc (v : G) * (c : G) = ((c : G) * v * (c : G)⁻¹) * c := by rw [← h2]
    _ = c * v := by group

theorem fix_entries {F : Type} [Field F] (X : Matrix (Fin 2) (Fin 2) F) (w : Fin 2 → F)
    (hX : X.mulVec w = w) :
    X 0 0 * w 0 + X 0 1 * w 1 = w 0 ∧ X 1 0 * w 0 + X 1 1 * w 1 = w 1 := by
  have h0 := congrFun hX 0
  have h1 := congrFun hX 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  exact ⟨h0, h1⟩

theorem mulVec_comm_of_fix {F : Type} [Field F] (h2 : (2 : F) = 0)
    {a b c d a' b' c' d' p q : F}
    (hdet : a * d - b * c = 1) (hdet' : a' * d' - b' * c' = 1)
    (h1 : a * p + b * q = p) (h1' : c * p + d * q = q)
    (h1'' : a' * p + b' * q = p) (h1''' : c' * p + d' * q = q)
    (hne : p ≠ 0 ∨ q ≠ 0) (x0 x1 : F) :
    a * (a' * x0 + b' * x1) + b * (c' * x0 + d' * x1) =
        a' * (a * x0 + b * x1) + b' * (c * x0 + d * x1) ∧
      c * (a' * x0 + b' * x1) + d * (c' * x0 + d' * x1) =
        c' * (a * x0 + b * x1) + d' * (c * x0 + d * x1) := by
  obtain ⟨e1, e2, e3, e4⟩ := mat_comm_of_fix h2 hdet hdet' h1 h1' h1'' h1''' hne
  exact ⟨by linear_combination x0 * e1 + x1 * e2, by linear_combination x0 * e3 + x1 * e4⟩

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem kuR_normalizer (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M) :
    r ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  h.oTwoUpper_le_normalizer_V (kuR_le hr)

theorem conj_comm_of_mem (h : KuHyp G T M H P z) {r s : G} (hr : r ∈ kuR T M)
    (hs : s ∈ kuR T M) (w : Fin 2 → h.mNat.data.K) :
    h.mNat.data.conj ⟨r, h.kuR_normalizer hr⟩ (h.mNat.data.conj ⟨s, h.kuR_normalizer hs⟩ w) =
      h.mNat.data.conj ⟨s, h.kuR_normalizer hs⟩ (h.mNat.data.conj ⟨r, h.kuR_normalizer hr⟩ w) := by
  obtain ⟨w0, hw0, hfix⟩ := h.exists_fixed_vec
  obtain ⟨A, hA⟩ := h.mNat.data.exists_matrix_of_mem ⟨r, h.kuR_normalizer hr⟩ (kuR_le hr)
  obtain ⟨B, hB⟩ := h.mNat.data.exists_matrix_of_mem ⟨s, h.kuR_normalizer hs⟩ (kuR_le hs)
  have hAw := hfix ⟨r, h.kuR_normalizer hr⟩ hr
  have hBw := hfix ⟨s, h.kuR_normalizer hs⟩ hs
  rw [hA] at hAw
  rw [hB] at hBw
  have hdA := A.2
  have hdB := B.2
  rw [Matrix.det_fin_two] at hdA hdB
  obtain ⟨a1, a2⟩ := fix_entries _ _ hAw
  obtain ⟨b1, b2⟩ := fix_entries _ _ hBw
  obtain ⟨e1, e2⟩ := mulVec_comm_of_fix h.two_eq_zero_natK hdA hdB a1 a2 b1 b2
    (h.fixed_vec_ne w0 hw0) (w 0) (w 1)
  simp only [hA, hB]
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination e1
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination e2

theorem comm_mem_pCore (h : KuHyp G T M H P z) {r s : G} (hr : r ∈ kuR T M)
    (hs : s ∈ kuR T M) : r * s * r⁻¹ * s⁻¹ ∈ pCoreOf 2 M := by
  have hrM : r ∈ M := oTwoUpper_le M (kuR_le hr)
  have hsM : s ∈ M := oTwoUpper_le M (kuR_le hs)
  have hM : r * s * r⁻¹ * s⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hrM hsM) (M.inv_mem hrM)) (M.inv_mem hsM)
  have hcent : r * s * r⁻¹ * s⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hc := conj_comm_triv h.mNat.data ⟨r, h.kuR_normalizer hr⟩ ⟨s, h.kuR_normalizer hs⟩
      (fun w => h.conj_comm_of_mem hr hs w)
    exact mem_centralizer_of_conj_triv h.mNat.data _ hc ⟨v, hv⟩
  have key : r * s * r⁻¹ * s⁻¹ ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) := ⟨hM, hcent⟩
  rwa [h.mCent] at key

theorem comm_mem_kuV2_of_V (h : KuHyp G T M H P z) {r : G} (hr : r ∈ kuR T M)
    (v : ↥(pCoreOf 2 M)) :
    r * (v : G) * r⁻¹ * (v : G)⁻¹ ∈ kuV2 T M := by
  obtain ⟨w0, hw0, hfix⟩ := h.exists_fixed_vec
  have hrN : r ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := h.kuR_normalizer hr
  obtain ⟨A, hA⟩ := h.mNat.data.exists_matrix_of_mem ⟨r, hrN⟩ (kuR_le hr)
  have hAw : (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec w0 = w0 := by
    rw [← hA]; exact hfix ⟨r, hrN⟩ hr
  obtain ⟨e1, e2⟩ := fix_entries _ _ hAw
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → h.mNat.data.K, x = Multiplicative.toAdd (h.mNat.data.E v) :=
    ⟨_, rfl⟩
  obtain ⟨t, ht1, ht2⟩ := fix_span (v₁ := x 0) (v₂ := x 1) h.two_eq_zero_natK hdet e1 e2
    (h.fixed_vec_ne w0 hw0)
  let u : ↥(pCoreOf 2 M) := conjAct (pCoreOf 2 M) ⟨r, hrN⟩ v * v⁻¹
  have hu : (u : G) = r * (v : G) * r⁻¹ * (v : G)⁻¹ := by
    simp [u, conjAct_apply_coe', mul_assoc]
  have hE : Multiplicative.toAdd (h.mNat.data.E u) =
      (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec x - x := by
    have h1 := h.mNat.data.conj_apply ⟨r, hrN⟩ v
    rw [hA, ← hx] at h1
    simp only [u, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [← h1, ← hx]
    abel
  have hvec : (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec x - x = t • w0 := by
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination ht1
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination ht2
  rw [← hu]
  refine (h.mem_kuV2_iff_fix u).mpr ?_
  rw [hE, hvec, mem_kuFix]
  intro g' hg'
  obtain ⟨B, hB⟩ := h.mNat.data.exists_matrix_of_mem g' (kuR_le hg')
  have hBw := hfix g' hg'
  rw [hB] at hBw ⊢
  rw [Matrix.mulVec_smul, hBw]

end KuHyp

end Commutator

end CFSG.GH74.QTGen4.Ku
