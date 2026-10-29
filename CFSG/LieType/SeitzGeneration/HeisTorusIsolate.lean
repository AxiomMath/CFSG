module

public import CFSG.LieType.SeitzGeneration.HeisTorusDefs

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] {p : ℕ}

theorem mul_eq_zero_of_rootSuppIn {I : Finset (Fin p)} {N M : Matrix (Fin p) (Fin p) F}
    (hN : RootSuppIn I N) (hM : RootSuppIn I M) : N * M = 0 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : N a b = 0
  · simp [h1]
  · by_cases h2 : M b c = 0
    · simp [h2]
    · exact ((hN a b h1).2 (hM b c h2).1).elim

theorem diagonal_mul_diagonal_inv_eq_one {t : Fin p → F} (ht : ∀ i, t i ≠ 0) :
    diagonal t * diagonal t⁻¹ = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp [ht i]

theorem diag_conj_one_add_mul_one_sub {I : Finset (Fin p)} {M : Matrix (Fin p) (Fin p) F}
    (hM : RootSuppIn I M) {t : Fin p → F} (ht : ∀ i, t i ≠ 0) :
    diagonal t * (1 + M) * diagonal t⁻¹ * (1 - M) =
      1 + Matrix.of (fun a b => (t a / t b - 1) * M a b) := by
  have hDD : diagonal t * diagonal t⁻¹ = 1 := diagonal_mul_diagonal_inv_eq_one ht
  have hentry : ∀ a b, (diagonal t * M * diagonal t⁻¹) a b = t a * M a b * (t b)⁻¹ := by
    intro a b
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hNsupp : RootSuppIn I (diagonal t * M * diagonal t⁻¹) := by
    intro a b hab
    rw [hentry] at hab
    exact hM a b fun h => hab (by simp [h])
  have hNM : (diagonal t * M * diagonal t⁻¹) * M = 0 :=
    mul_eq_zero_of_rootSuppIn hNsupp hM
  have h1 : diagonal t * (1 + M) * diagonal t⁻¹ = 1 + diagonal t * M * diagonal t⁻¹ := by
    rw [mul_add, mul_one, add_mul, hDD]
  have h2 : (1 + diagonal t * M * diagonal t⁻¹) * (1 - M) =
      1 - M + diagonal t * M * diagonal t⁻¹ := by
    rw [add_mul, one_mul, mul_sub, mul_one, hNM, sub_zero]
  rw [h1, h2]
  ext a b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, hentry]
  ring

theorem isolate_coe_inv_eq_of_mul_eq_one (A : SpecialLinearGroup (Fin p) F)
    {B : Matrix (Fin p) (Fin p) F} (h : (A : Matrix (Fin p) (Fin p) F) * B = 1) :
    ((A⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) = B := by
  have hA : ((A⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) *
      (A : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc ((A⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F)
      = ((A⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) *
          ((A : Matrix (Fin p) (Fin p) F) * B) := by rw [h, mul_one]
    _ = (((A⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) *
          (A : Matrix (Fin p) (Fin p) F)) * B := (mul_assoc _ _ _).symm
    _ = B := by rw [hA, one_mul]

theorem exists_conj_mem_of_rootSuppIn {K : Subgroup (SpecialLinearGroup (Fin p) F)}
    (hK : ContainsDiagTorus K) {I : Finset (Fin p)} {M : Matrix (Fin p) (Fin p) F}
    (hM : RootSuppIn I M) {g : SpecialLinearGroup (Fin p) F} (hg : g ∈ K)
    (hgM : (g : Matrix (Fin p) (Fin p) F) = 1 + M) {t : Fin p → F} (ht : ∀ i, t i ≠ 0)
    (htdet : ∏ i, t i = 1) :
    ∃ g' ∈ K, (g' : Matrix (Fin p) (Fin p) F) =
      1 + Matrix.of (fun a b => (t a / t b - 1) * M a b) := by
  obtain ⟨d, hd⟩ : ∃ d : SpecialLinearGroup (Fin p) F,
      (d : Matrix (Fin p) (Fin p) F) = diagonal t :=
    ⟨⟨diagonal t, by rw [Matrix.det_diagonal, htdet]⟩, rfl⟩
  have hdK : d ∈ K := hK d ⟨t, hd⟩
  have hdinv : ((d⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal t⁻¹ :=
    isolate_coe_inv_eq_of_mul_eq_one d (by rw [hd]; exact diagonal_mul_diagonal_inv_eq_one ht)
  have hid : (1 + M) * (1 - M) = 1 := by
    rw [show (1 + M) * (1 - M) = 1 - M * M by noncomm_ring,
      mul_eq_zero_of_rootSuppIn hM hM, sub_zero]
  have hginv : ((g⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 - M :=
    isolate_coe_inv_eq_of_mul_eq_one g (by rw [hgM]; exact hid)
  refine ⟨d * g * d⁻¹ * g⁻¹, K.mul_mem (K.mul_mem (K.mul_mem hdK hg) (K.inv_mem hdK))
    (K.inv_mem hg), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, hd, hgM, hdinv, hginv]
  exact diag_conj_one_add_mul_one_sub hM ht

theorem exists_single_mem_of_suppIn (hp : 5 ≤ p) {l : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    {K : Subgroup (SpecialLinearGroup (Fin p) F)} (hK : ContainsDiagTorus K)
    {I : Finset (Fin p)} {M : Matrix (Fin p) (Fin p) F} (hM : RootSuppIn I M)
    {a₀ b₀ : Fin p} (hab : M a₀ b₀ ≠ 0)
    (h1M : ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + M) :
    ∃ c : F, c ≠ 0 ∧ ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + Matrix.single a₀ b₀ c := by
  classical
  have hsupp₀ : a₀ ∈ I ∧ b₀ ∉ I := hM a₀ b₀ hab
  have hne₀ : a₀ ≠ b₀ := by
    intro h
    apply hsupp₀.2
    rw [← h]
    exact hsupp₀.1
  suffices H : ∀ n : ℕ, ∀ N : Matrix (Fin p) (Fin p) F,
      (Finset.univ.filter fun ab : Fin p × Fin p => N ab.1 ab.2 ≠ 0).card = n →
        RootSuppIn I N → N a₀ b₀ ≠ 0 → (∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) = 1 + N) →
          ∃ c : F, c ≠ 0 ∧ ∃ g ∈ K,
            (g : Matrix (Fin p) (Fin p) F) = 1 + Matrix.single a₀ b₀ c by
    exact H _ M rfl hM hab h1M
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih N hcard hN hN0 hgN
  by_cases hex : ∃ a b, (a, b) ≠ (a₀, b₀) ∧ N a b ≠ 0
  · obtain ⟨a, b, hne, hab'⟩ := hex
    have hsa : a ∈ I ∧ b ∉ I := hN a b hab'
    obtain ⟨x, hx, hxa, hxb⟩ : ∃ x, (x = a₀ ∨ x = b₀) ∧ x ≠ a ∧ x ≠ b := by
      by_cases h : a₀ = a ∨ a₀ = b
      · have ha₀a : a₀ = a := by
          rcases h with h | h
          · exact h
          · exfalso
            apply hsa.2
            rw [← h]
            exact hsupp₀.1
        refine ⟨b₀, Or.inr rfl, ?_, ?_⟩
        · intro h
          apply hsupp₀.2
          rw [h]
          exact hsa.1
        · intro h
          apply hne
          rw [ha₀a, h]
      · push Not at h
        exact ⟨a₀, Or.inl rfl, h.1, h.2⟩
    obtain ⟨m, hm⟩ : ∃ m : Fin p, m ∉ ({a, b, a₀, b₀} : Finset (Fin p)) := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin p)) ⊆ {a, b, a₀, b₀} := fun m _ => hcon m
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 : ({a, b, a₀, b₀} : Finset (Fin p)).card ≤ 4 := Finset.card_le_four
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨hma, hmb, hma₀, hmb₀⟩ := hm
    have hxm : x ≠ m := by
      rcases hx with hx | hx
      · rw [hx]
        exact fun h => hma₀ h.symm
      · rw [hx]
        exact fun h => hmb₀ h.symm
    obtain ⟨t, ht_def⟩ : ∃ t : Fin p → F,
        t = fun i => (if i = x then l else 1) * (if i = m then l⁻¹ else 1) := ⟨_, rfl⟩
    have htne : ∀ i, t i ≠ 0 := by
      intro i
      simp only [ht_def]
      split_ifs <;> simp [hl0]
    have htval : ∀ i, i ≠ x → i ≠ m → t i = 1 := by
      intro i h1 h2
      simp [ht_def, h1, h2]
    have htx : t x = l := by simp [ht_def, hxm]
    have htdet : ∏ i, t i = 1 := by
      simp only [ht_def]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
      simp [hl0]
    have hratio : t a₀ / t b₀ - 1 ≠ 0 := by
      rcases hx with hx | hx
      · have h1 : t a₀ = l := by
          rw [← hx]
          exact htx
        have h2 : t b₀ = 1 := by
          apply htval
          · intro h
            exact hne₀ (h.trans hx).symm
          · exact Ne.symm hmb₀
        rw [h1, h2, div_one]
        exact sub_ne_zero.mpr hl1
      · have h1 : t b₀ = l := by
          rw [← hx]
          exact htx
        have h2 : t a₀ = 1 := by
          apply htval
          · intro h
            exact hne₀ (h.trans hx)
          · exact Ne.symm hma₀
        rw [h1, h2]
        intro h
        have h' : (1 : F) / l = 1 := sub_eq_zero.mp h
        exact hl1 ((div_eq_one_iff_eq hl0).mp h').symm
    have hta : t a = 1 := htval a (Ne.symm hxa) (Ne.symm hma)
    have htb : t b = 1 := htval b (Ne.symm hxb) (Ne.symm hmb)
    have hN'supp : RootSuppIn I (Matrix.of fun i j => (t i / t j - 1) * N i j) := by
      intro i j hij
      rw [Matrix.of_apply] at hij
      exact hN i j fun h => hij (by simp [h])
    have hN'0 : (Matrix.of fun i j => (t i / t j - 1) * N i j) a₀ b₀ ≠ 0 := by
      rw [Matrix.of_apply]
      exact mul_ne_zero hratio hN0
    have hsub : Finset.univ.filter (fun ab : Fin p × Fin p =>
        (Matrix.of fun i j => (t i / t j - 1) * N i j) ab.1 ab.2 ≠ 0) ⊆
        Finset.univ.filter (fun ab : Fin p × Fin p => N ab.1 ab.2 ≠ 0) := by
      intro ab hab''
      obtain ⟨-, hab'''⟩ := Finset.mem_filter.mp hab''
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hab''' ?_⟩
      simp [h]
    have hss : Finset.univ.filter (fun ab : Fin p × Fin p =>
        (Matrix.of fun i j => (t i / t j - 1) * N i j) ab.1 ab.2 ≠ 0) ⊂
        Finset.univ.filter (fun ab : Fin p × Fin p => N ab.1 ab.2 ≠ 0) := by
      rw [Finset.ssubset_iff_of_subset hsub]
      refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab'⟩, fun hmem => ?_⟩
      obtain ⟨-, hmem'⟩ := Finset.mem_filter.mp hmem
      apply hmem'
      simp [hta, htb]
    have hlt : (Finset.univ.filter (fun ab : Fin p × Fin p =>
        (Matrix.of fun i j => (t i / t j - 1) * N i j) ab.1 ab.2 ≠ 0)).card < n := by
      rw [← hcard]
      exact Finset.card_lt_card hss
    have hgN' : ∃ g ∈ K, (g : Matrix (Fin p) (Fin p) F) =
        1 + Matrix.of fun i j => (t i / t j - 1) * N i j := by
      obtain ⟨g, hg, hgN⟩ := hgN
      exact exists_conj_mem_of_rootSuppIn hK hN hg hgN htne htdet
    obtain ⟨c, hc, g', hg', hg'eq⟩ :=
      ih _ hlt (Matrix.of fun i j => (t i / t j - 1) * N i j) rfl hN'supp hN'0 hgN'
    exact ⟨c, hc, g', hg', hg'eq⟩
  ·
    push Not at hex
    refine ⟨N a₀ b₀, hN0, ?_⟩
    obtain ⟨g, hg, hgN'⟩ := hgN
    refine ⟨g, hg, ?_⟩
    rw [hgN']
    congr 1
    ext i j
    rw [Matrix.single_apply]
    by_cases hij : a₀ = i ∧ b₀ = j
    · obtain ⟨rfl, rfl⟩ := hij
      simp
    · rw [if_neg hij]
      exact hex i j fun h => hij ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩

end CFSG.LieType.SeitzGeneration
