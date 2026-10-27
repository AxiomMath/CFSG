module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LinearAlgebra

open Matrix

theorem cocycle_eq_zero_of_mem_centralizer {Γ M : Type*} [Group Γ] [AddCommGroup M]
    [DistribMulAction Γ M] (δ : Γ → M) (hδ : ∀ g h : Γ, δ (g * h) = δ g + g • δ h)
    (t : Γ) (ht : ∀ m : M, t • m = m → m = 0) (h0 : δ t = 0) :
    ∀ c : Γ, c * t = t * c → δ c = 0 := by
  intro c hct
  have h1 : δ (c * t) = δ c := by rw [hδ c t, h0, smul_zero, add_zero]
  have h2 : δ (t * c) = t • δ c := by rw [hδ t c, h0, zero_add]
  have h3 : t • δ c = δ c := by rw [← h2, ← h1, hct]
  exact ht (δ c) h3

open scoped Classical

section Helpers

variable {F : Type*} [Field F] {N : ℕ}

private def weight (lam mu : Fˣ) (s : Finset (Fin N)) : Fin N → Fˣ :=
  fun i => if i ∈ s then lam else mu

private lemma prod_weight (lam mu : Fˣ) (s : Finset (Fin N)) :
    ∏ i, weight lam mu s i = lam ^ s.card * mu ^ (N - s.card) := by
  classical
  have hsplit : ∏ i, weight lam mu s i =
      (∏ i, if i ∈ s then lam else 1) * (∏ i, if i ∈ s then 1 else mu) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> simp [weight, hi]
  rw [hsplit]
  have h1 : (∏ i : Fin N, if i ∈ s then lam else 1) = lam ^ s.card := by
    rw [Finset.prod_ite_mem_eq s (fun _ => lam)]
    exact Finset.prod_const lam
  have h2 : (∏ i : Fin N, if i ∈ s then 1 else mu) = mu ^ (N - s.card) := by
    have h2a : (∏ i : Fin N, if i ∈ s then (1 : Fˣ) else mu) =
        ∏ i : Fin N, if i ∈ sᶜ then mu else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [hi, Finset.mem_compl]
    rw [h2a, Finset.prod_ite_mem_eq sᶜ (fun _ => mu), Finset.prod_const]
    congr 1
    rw [Finset.card_compl, Fintype.card_fin]
  rw [h1, h2]

private def diagSL (w : Fin N → Fˣ) (h : ∏ i, w i = 1) :
    SpecialLinearGroup (Fin N) F :=
  ⟨Matrix.diagonal (fun i => (w i : F)), by
    rw [Matrix.det_diagonal]
    rw [← Units.coe_prod]
    rw [h]
    rfl⟩

private lemma diagSL_coe (w : Fin N → Fˣ) (h : ∏ i, w i = 1) :
    (diagSL w h : Matrix (Fin N) (Fin N) F) = Matrix.diagonal (fun i => (w i : F)) := rfl

private lemma diagSL_smul_apply (w : Fin N → Fˣ) (h : ∏ i, w i = 1)
    (v : Fin N → F) (i : Fin N) :
    (diagSL w h • v) i = (w i : F) * v i := by
  rw [Matrix.SpecialLinearGroup.smul_def, diagSL_coe]
  exact Matrix.mulVec_diagonal _ _ _

private lemma diagSL_mul_comm (w w' : Fin N → Fˣ)
    (h : ∏ i, w i = 1) (h' : ∏ i, w' i = 1) :
    diagSL w h * diagSL w' h' = diagSL w' h' * diagSL w h := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [diagSL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  ring

private lemma diagSL_smul_fixed (w : Fin N → Fˣ) (h : ∏ i, w i = 1)
    (hw : ∀ i, w i ≠ 1) (v : Fin N → F)
    (hv : diagSL w h • v = v) : v = 0 := by
  funext i
  have hi := congrFun hv i
  rw [diagSL_smul_apply] at hi
  have hne : (w i : F) - 1 ≠ 0 := by
    intro hz
    exact hw i (Units.ext (sub_eq_zero.mp hz))
  have hzero : ((w i : F) - 1) * v i = 0 := by
    rw [sub_mul, one_mul, hi, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

private lemma diag_mul_transvection (w : Fin N → Fˣ) {i j : Fin N} (hijw : w i = w j)
    (b : F) :
    Matrix.diagonal (fun k => (w k : F)) * Matrix.transvection i j b =
      Matrix.transvection i j b * Matrix.diagonal (fun k => (w k : F)) := by
  ext a c
  rw [Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hac : a = i ∧ c = j
  · obtain ⟨rfl, rfl⟩ := hac
    simp only [Matrix.diagonal_apply, Matrix.single_apply, Matrix.add_apply, ite_true,
      eq_self_iff_true]
    rw [hijw]
    ring
  · have hs : Matrix.single i j b a c = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hac ⟨rfl, rfl⟩
    rw [hs, mul_zero, zero_mul, add_zero]

private lemma transvection_mul_diagSL_eq (w : Fin N → Fˣ) (h : ∏ i, w i = 1)
    {i j : Fin N} (hij : i ≠ j) (b : F) (hijw : w i = w j) :
    SpecialLinearGroup.transvection hij b * diagSL w h =
      diagSL w h * SpecialLinearGroup.transvection hij b := by
  ext a c
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp only [diagSL, Matrix.SpecialLinearGroup.transvection_coe]
  exact congrFun (congrFun (diag_mul_transvection w hijw b).symm a) c

private lemma eq_zero_of_cocycle_vanishing_transvections
    (c : SpecialLinearGroup (Fin N) F → Fin N → F)
    (hc : ∀ g h, c (g * h) = c g + g • c h)
    (htrans : ∀ (i j : Fin N) (hij : i ≠ j) (b : F),
      c (SpecialLinearGroup.transvection hij b) = 0) :
    ∀ g, c g = 0 := by
  classical
  have h1 : c 1 = 0 := by
    have h := hc 1 1
    rw [mul_one, one_smul] at h
    exact add_left_cancel (a := c 1) (b := c 1) (c := 0) (by rw [add_zero]; exact h.symm)
  let K : Subgroup (SpecialLinearGroup (Fin N) F) :=
    { carrier := {g | c g = 0}
      one_mem' := h1
      mul_mem' := by
        intro g h hg hh
        change c (g * h) = 0
        rw [hc g h, hg, hh, smul_zero, add_zero]
      inv_mem' := by
        intro g hg
        change c g⁻¹ = 0
        have h := hc g⁻¹ g
        rw [inv_mul_cancel, h1, hg, smul_zero, add_zero] at h
        exact h.symm }
  have hle : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin N) F → SpecialLinearGroup (Fin N) F)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    rw [TransvectionStruct.toSpecialLinearGroup_def]
    exact htrans t.i t.j t.hij t.c
  have htop : (⊤ : Subgroup (SpecialLinearGroup (Fin N) F)) ≤ K := by
    rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (K := F) (ι := Fin N)]
    exact hle
  intro g
  exact htop trivial

private lemma sl_cocycle_vanishes_of_family
    (c : SpecialLinearGroup (Fin N) F → Fin N → F)
    (hc : ∀ g h, c (g * h) = c g + g • c h)
    (t : SpecialLinearGroup (Fin N) F) (htfpf : ∀ v : Fin N → F, t • v = v → v = 0)
    (ht : c t = 0)
    (D : ∀ i j : Fin N, i ≠ j → SpecialLinearGroup (Fin N) F)
    (hDfpf : ∀ (i j : Fin N) (hij : i ≠ j), ∀ v : Fin N → F,
      D i j hij • v = v → v = 0)
    (hDt : ∀ (i j : Fin N) (hij : i ≠ j), D i j hij * t = t * D i j hij)
    (hDx : ∀ (i j : Fin N) (hij : i ≠ j) (b : F),
      SpecialLinearGroup.transvection hij b * D i j hij =
        D i j hij * SpecialLinearGroup.transvection hij b) :
    ∀ g, c g = 0 := by
  have hcent := cocycle_eq_zero_of_mem_centralizer c hc t htfpf ht
  have htrans : ∀ (i j : Fin N) (hij : i ≠ j) (b : F),
      c (SpecialLinearGroup.transvection hij b) = 0 := by
    intro i j hij b
    have hDc : c (D i j hij) = 0 := hcent (D i j hij) (hDt i j hij)
    exact cocycle_eq_zero_of_mem_centralizer c hc (D i j hij) (hDfpf i j hij) hDc
      (SpecialLinearGroup.transvection hij b) (hDx i j hij b)
  exact eq_zero_of_cocycle_vanishing_transvections c hc htrans

private lemma weight_ne_one (lam mu : Fˣ) (s : Finset (Fin N))
    (hlam : lam ≠ 1) (hmu : mu ≠ 1) : ∀ i, weight lam mu s i ≠ 1 := by
  intro i
  unfold weight
  split_ifs with hi
  · exact hlam
  · exact hmu

private lemma exists_ne_ne {N : ℕ} (i j : Fin N) (hij : i ≠ j) (hN : 3 ≤ N) :
    ∃ p : Fin N, p ≠ i ∧ p ≠ j := by
  have hcard : ({i, j} : Finset (Fin N)).card < (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_pair_eq_two_iff.mpr hij, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨p, ?_, ?_⟩ <;> intro h <;> exact hp (by simp [h])

private lemma exists_preimage_diagSL
    (c : SpecialLinearGroup (Fin N) F → Fin N → F)
    (w : Fin N → Fˣ) (h : ∏ i, w i = 1) (hw : ∀ i, w i ≠ 1) :
    ∃ a : Fin N → F,
      (diagSL w h : Matrix (Fin N) (Fin N) F) *ᵥ a - a = c (diagSL w h) := by
  refine ⟨fun i => c (diagSL w h) i * ((w i : F) - 1)⁻¹, funext fun i => ?_⟩
  have hne : (w i : F) - 1 ≠ 0 := by
    intro hz; exact hw i (Units.ext (sub_eq_zero.mp hz))
  rw [Pi.sub_apply, diagSL_coe, Matrix.mulVec_diagonal]
  have hcalc : (w i : F) * (c (diagSL w h) i * ((w i : F) - 1)⁻¹) -
      c (diagSL w h) i * ((w i : F) - 1)⁻¹ = ((w i : F) - 1) *
        (c (diagSL w h) i * ((w i : F) - 1)⁻¹) := by ring
  rw [hcalc, ← mul_assoc, mul_comm ((w i : F) - 1) (c (diagSL w h) i), mul_assoc,
    mul_inv_cancel₀ hne, mul_one]

private lemma exists_coboundary_of_family
    (c : SpecialLinearGroup (Fin N) F → Fin N → F)
    (hc : ∀ g h, c (g * h) = c g + (g : Matrix (Fin N) (Fin N) F) *ᵥ c h)
    (t : SpecialLinearGroup (Fin N) F) (htfpf : ∀ v : Fin N → F, t • v = v → v = 0)
    (D : ∀ i j : Fin N, i ≠ j → SpecialLinearGroup (Fin N) F)
    (hDfpf : ∀ (i j : Fin N) (hij : i ≠ j), ∀ v : Fin N → F, D i j hij • v = v → v = 0)
    (hDt : ∀ (i j : Fin N) (hij : i ≠ j), D i j hij * t = t * D i j hij)
    (hDx : ∀ (i j : Fin N) (hij : i ≠ j) (b : F),
      SpecialLinearGroup.transvection hij b * D i j hij =
        D i j hij * SpecialLinearGroup.transvection hij b)
    (ha : ∃ a : Fin N → F, (t : Matrix (Fin N) (Fin N) F) *ᵥ a - a = c t) :
    ∃ a : Fin N → F, ∀ g, c g = (g : Matrix (Fin N) (Fin N) F) *ᵥ a - a := by
  obtain ⟨a, ha⟩ := ha
  let c' : SpecialLinearGroup (Fin N) F → Fin N → F :=
    fun g => c g - ((g : Matrix (Fin N) (Fin N) F) *ᵥ a - a)
  have hc' : ∀ g h, c' (g * h) = c' g + g • c' h := by
    intro g h
    rw [SpecialLinearGroup.smul_def]
    change c (g * h) - (((g * h) : Matrix (Fin N) (Fin N) F) *ᵥ a - a) =
      (c g - ((g : Matrix (Fin N) (Fin N) F) *ᵥ a - a)) +
        (g : Matrix (Fin N) (Fin N) F) *ᵥ
          (c h - ((h : Matrix (Fin N) (Fin N) F) *ᵥ a - a))
    rw [hc g h]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_add]
    abel
  have hc't : c' t = 0 := by
    change c t - ((t : Matrix (Fin N) (Fin N) F) *ᵥ a - a) = 0
    rw [ha, sub_self]
  have hvan : ∀ g, c' g = 0 :=
    sl_cocycle_vanishes_of_family c' hc' t htfpf hc't D hDfpf hDt hDx
  refine ⟨a, fun g => ?_⟩
  have hg := hvan g
  change c g - ((g : Matrix (Fin N) (Fin N) F) *ᵥ a - a) = 0 at hg
  exact sub_eq_zero.mp hg

private lemma coboundary_of_diag_data {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {N : ℕ} (hN : 3 ≤ N)
    (c : SpecialLinearGroup (Fin N) F → Fin N → F)
    (hc : ∀ g h, c (g * h) = c g + (g : Matrix (Fin N) (Fin N) F) *ᵥ c h) :
    ∃ a : Fin N → F, ∀ g, c g = (g : Matrix (Fin N) (Fin N) F) *ᵥ a - a := by
  classical
  haveI : NeZero N := ⟨by omega⟩
  have hchar : ringChar F = 2 := ringChar.eq_iff.mpr (inferInstance : CharP F 2)
  obtain ⟨μ, hμgen⟩ := IsCyclic.exists_generator (α := Fˣ)
  set m : ℕ := Fintype.card F - 1 with hm
  have hμorder : orderOf μ = m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμgen, Nat.card_eq_fintype_card,
      Fintype.card_units, hm]
  have hm3 : 3 ≤ m := by rw [hm]; omega
  have hnotboth : ¬ (m ∣ (N - 1) ∧ m ∣ (N - 2)) := by
    rintro ⟨h1, h2⟩
    have hdvd : m ∣ ((N - 1) - (N - 2)) := Nat.dvd_sub h1 h2
    have hsub : (N - 1) - (N - 2) = 1 := by omega
    rw [hsub] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hdiv_of_pow : ∀ n, μ ^ n = 1 → m ∣ n := by
    intro n h
    have := (orderOf_dvd_iff_pow_eq_one).mpr h
    rwa [hμorder] at this
  have hμpow_ne : ∀ n, ¬ m ∣ n → μ ^ n ≠ 1 := fun n hn h => hn (hdiv_of_pow n h)
  by_cases h2 : m ∣ (N - 2)
  ·
    have h1 : ¬ m ∣ (N - 1) := fun h1 => hnotboth ⟨h1, h2⟩
    have hμN1 : μ ^ (N - 1) ≠ 1 := hμpow_ne (N - 1) h1
    have hμne : μ ≠ 1 := fun h => hμN1 (by rw [h, one_pow])
    let lam : Fˣ := (μ ^ (N - 1))⁻¹
    have hlam : lam ≠ 1 := by
      intro h
      apply hμN1
      have hx : (μ ^ (N - 1))⁻¹ = 1 := by simpa [lam] using h
      have := congrArg (fun x : Fˣ => x⁻¹) hx
      simpa using this
    have hprod : lam ^ 1 * μ ^ (N - 1) = 1 := by simp [lam]
    let w0 : Fin N → Fˣ := weight lam μ ({0} : Finset (Fin N))
    have hw0 : ∏ i, w0 i = 1 := by
      rw [prod_weight, Finset.card_singleton]
      simpa using hprod
    have hw0ne : ∀ i, w0 i ≠ 1 := weight_ne_one lam μ _ hlam hμne
    have htpf : ∀ v : Fin N → F, diagSL w0 hw0 • v = v → v = 0 :=
      diagSL_smul_fixed w0 hw0 hw0ne
    obtain ⟨a, ha⟩ := exists_preimage_diagSL c w0 hw0 hw0ne
    let D : ∀ i j : Fin N, i ≠ j → SpecialLinearGroup (Fin N) F := fun i j hij =>
      diagSL (weight lam μ ({Classical.choose (exists_ne_ne i j hij hN)} :
        Finset (Fin N))) (by
        rw [prod_weight, Finset.card_singleton]
        simpa using hprod)
    refine exists_coboundary_of_family c hc (diagSL w0 hw0) htpf D ?_ ?_ ?_ ⟨a, ha⟩
    · intro i j hij v hv
      exact diagSL_smul_fixed _ _ (weight_ne_one lam μ _ hlam hμne) v hv
    · intro i j hij
      exact diagSL_mul_comm _ _ _ _
    · intro i j hij b
      apply transvection_mul_diagSL_eq
      have hp := Classical.choose_spec (exists_ne_ne i j hij hN)
      have hpi : ¬ (i ∈ ({Classical.choose (exists_ne_ne i j hij hN)} :
          Finset (Fin N))) := by
        intro h
        have hi : i = Classical.choose (exists_ne_ne i j hij hN) := by simpa using h
        exact hp.1 hi.symm
      have hpj : ¬ (j ∈ ({Classical.choose (exists_ne_ne i j hij hN)} :
          Finset (Fin N))) := by
        intro h
        have hj : j = Classical.choose (exists_ne_ne i j hij hN) := by simpa using h
        exact hp.2 hj.symm
      unfold weight
      rw [if_neg hpi, if_neg hpj]
  ·
    have hμN2 : μ ^ (N - 2) ≠ 1 := hμpow_ne (N - 2) h2
    have hμne : μ ≠ 1 := fun h => hμN2 (by rw [h, one_pow])
    obtain ⟨r, hr⟩ :=
      FiniteField.isSquare_of_char_two hchar (((μ ^ (N - 2))⁻¹ : Fˣ) : F)
    have hrne : r ≠ 0 := by
      intro h0
      have hv : (((μ ^ (N - 2))⁻¹ : Fˣ) : F) = 0 := by rw [hr, h0, mul_zero]
      exact (Units.ne_zero ((μ ^ (N - 2))⁻¹)) hv
    let lam : Fˣ := Units.mk0 r hrne
    have hlam2 : lam * lam = (μ ^ (N - 2))⁻¹ := by
      apply Units.ext
      change r * r = (((μ ^ (N - 2))⁻¹ : Fˣ) : F)
      rw [← hr]
    have hlam : lam ≠ 1 := by
      intro h
      have hx : (μ ^ (N - 2))⁻¹ = 1 := by rw [← hlam2, h, one_mul]
      apply hμN2
      have := congrArg (fun x : Fˣ => x⁻¹) hx
      simpa using this
    have hprod : lam ^ 2 * μ ^ (N - 2) = 1 := by
      rw [pow_two, hlam2, inv_mul_cancel]
    have h01 : (0 : Fin N) ≠ 1 := by
      intro hh
      have hv := congrArg Fin.val hh
      rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)] at hv
      omega
    let w0 : Fin N → Fˣ := weight lam μ ({0, 1} : Finset (Fin N))
    have hw0 : ∏ i, w0 i = 1 := by
      rw [prod_weight, Finset.card_pair_eq_two_iff.mpr h01]
      simpa using hprod
    have hw0ne : ∀ i, w0 i ≠ 1 := weight_ne_one lam μ _ hlam hμne
    have htpf : ∀ v : Fin N → F, diagSL w0 hw0 • v = v → v = 0 :=
      diagSL_smul_fixed w0 hw0 hw0ne
    obtain ⟨a, ha⟩ := exists_preimage_diagSL c w0 hw0 hw0ne
    let D : ∀ i j : Fin N, i ≠ j → SpecialLinearGroup (Fin N) F := fun i j hij =>
      diagSL (weight lam μ ({i, j} : Finset (Fin N))) (by
        rw [prod_weight, Finset.card_pair_eq_two_iff.mpr hij]
        simpa using hprod)
    refine exists_coboundary_of_family c hc (diagSL w0 hw0) htpf D ?_ ?_ ?_ ⟨a, ha⟩
    · intro i j hij v hv
      exact diagSL_smul_fixed _ _ (weight_ne_one lam μ _ hlam hμne) v hv
    · intro i j hij
      exact diagSL_mul_comm _ _ _ _
    · intro i j hij b
      apply transvection_mul_diagSL_eq
      unfold weight
      rw [if_pos (by simp), if_pos (by simp)]

end Helpers

theorem exists_eq_mulVec_sub_of_cocycle_sl {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (hF : 4 ≤ Fintype.card F) {N : ℕ} (hN : 3 ≤ N)
    (c : SpecialLinearGroup (Fin N) F → Fin N → F)
    (hc : ∀ g h, c (g * h) = c g + (g : Matrix (Fin N) (Fin N) F) *ᵥ c h) :
    ∃ a : Fin N → F, ∀ g, c g = (g : Matrix (Fin N) (Fin N) F) *ᵥ a - a :=
  coboundary_of_diag_data hF hN c hc

end CFSG.LinearAlgebra
