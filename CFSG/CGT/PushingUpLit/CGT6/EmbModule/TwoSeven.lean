module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NormMap

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 Matrix

theorem exists_odd_fpf (K : Type*) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (hodd : Odd (Nat.card K - 1)) :
    ∃ d : SpecialLinearGroup (Fin 2) K, ∃ m : ℕ, Odd m ∧ d ^ m = 1 ∧
      (∀ M : Matrix (Fin 2) (Fin 2) K, (d : Matrix (Fin 2) (Fin 2) K) * M = M → M = 0) ∧
      ∀ M : Matrix (Fin 2) (Fin 2) K, M * (d : Matrix (Fin 2) (Fin 2) K).transpose = M → M = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : 3 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨l, hl0, hl1⟩ : ∃ l : K, l ≠ 0 ∧ l ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon x hx]
    have := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    simp at this
    omega
  have hlm : l ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one l hl0
  have hli1 : l⁻¹ ≠ 1 := by
    intro h
    apply hl1
    rw [inv_eq_one] at h
    exact h
  let d : SpecialLinearGroup (Fin 2) K :=
    ⟨Matrix.diagonal ![l, l⁻¹], by simp [Matrix.det_diagonal, Fin.prod_univ_two, hl0]⟩
  refine ⟨d, Fintype.card K - 1, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]; exact hodd
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h1 := Matrix.SpecialLinearGroup.coe_pow d (Fintype.card K - 1)
    have h2 : ((d : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![l, l⁻¹] := rfl
    rw [h1, h2, Matrix.diagonal_pow]
    fin_cases i <;> fin_cases j <;> simp [hlm, inv_pow]
  · intro M hM
    ext i j
    have h := congrFun (congrFun hM i) j
    fin_cases i
    · simp [d, Matrix.mul_apply, Matrix.diagonal_apply] at h
      have : (l - 1) * M 0 j = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hl1
      · simpa using h1
    · simp [d, Matrix.mul_apply, Matrix.diagonal_apply] at h
      have : (l⁻¹ - 1) * M 1 j = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) hli1
      · simpa using h1
  · intro M hM
    ext i j
    have h := congrFun (congrFun hM i) j
    fin_cases j
    · simp [d, Matrix.mul_apply, Matrix.diagonal_apply] at h
      have : M i 0 * (l - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · simpa using h1
      · exact absurd (sub_eq_zero.mp h1) hl1
    · simp [d, Matrix.mul_apply, Matrix.diagonal_apply] at h
      have : M i 1 * (l⁻¹ - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h1 | h1
      · simpa using h1
      · exact absurd (sub_eq_zero.mp h1) hli1

theorem sl2_mult_trivial (K : Type*) [Field K] (h4 : ∃ s : Finset K, s.card = 4) {M : Type*}
    [CommGroup M] (χ : SpecialLinearGroup (Fin 2) K → M) (hχ : ∀ s t, χ (s * t) = χ s * χ t) :
    ∀ s, χ s = 1 := by
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  let f : SpecialLinearGroup (Fin 2) K →* M := MonoidHom.mk' χ hχ
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  intro s
  have : (⟨f s, s, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

theorem half_split {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {Γ : Type*} [Group Γ] (ρ : Γ →* MulAut V) {S : Type*} [Group S]
    (A B : Subgroup V)
    (hAt : ∀ g : Γ, ∀ a ∈ A, ρ g a = a) (hVB : ∀ (g : Γ) (v : V), ρ g v * v⁻¹ ∈ B)
    (e e' : S →* Γ) (hcomm : ∀ s t, e s * e' t = e' t * e s) (d : S) {m : ℕ} (hm : Odd m)
    (hdm : d ^ m = 1) (hfix : ∀ b ∈ B, ρ (e d) b = b → b ∈ A)
    (hperf : ∀ χ : S → V, (∀ s t, χ (s * t) = χ s * χ t) → ∀ s, χ s = 1)
    (K : Subgroup (MulAut V)) [Fintype ↥K] (hK : K = Subgroup.zpowers (ρ (e d))) :
    Odd (Fintype.card ↥K) ∧ (normK K).ker ≤ B ∧ A ≤ fixV K ∧
    (∀ b ∈ B, b ∈ fixV K → b ∈ A) ∧ (∀ t, ∀ c ∈ fixV K, ρ (e' t) c = c) ∧
    (∀ t, ∀ w ∈ (normK K).ker, ρ (e' t) w ∈ (normK K).ker) ∧
    (∀ t v, ρ (e' t) v * v⁻¹ ∈ (normK K).ker) := by
  classical
  have hKmem : ∀ k ∈ K, ∃ j : ℤ, k = ρ ((e d) ^ j) := by
    intro k hk
    rw [hK] at hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨j, by rw [map_zpow]⟩
  have hodd : Odd (Fintype.card ↥K) := by
    have hc : Nat.card ↥K = orderOf (ρ (e d)) := by
      rw [← Nat.card_zpowers]; exact congrArg (fun H : Subgroup (MulAut V) => Nat.card ↥H) hK
    rw [← Nat.card_eq_fintype_card, hc]
    refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, ← map_pow, hdm, map_one, map_one]
  have hcommK : ∀ t, ∀ k ∈ K, ∀ v : V, ρ (e' t) (k v) = k (ρ (e' t) v) := by
    intro t k hk v
    obtain ⟨j, rfl⟩ := hKmem k hk
    have hc : (e d) ^ j * e' t = e' t * (e d) ^ j := by
      have h1 : Commute (e d) (e' t) := hcomm d t
      exact (h1.zpow_left j).eq
    have := congrArg (fun g : Γ => ρ g v) hc
    simp only [map_mul, MulAut.mul_apply] at this
    exact this.symm
  have hKB : ∀ k ∈ K, ∀ v : V, k v * v⁻¹ ∈ B := by
    intro k hk v
    obtain ⟨j, rfl⟩ := hKmem k hk
    exact hVB _ v
  have h1 : (normK K).ker ≤ B := by
    intro w hw
    have hprod : ∏ k : ↥K, ((k : MulAut V) w * w⁻¹) ∈ B :=
      Subgroup.prod_mem _ fun k _ => hKB k k.2 w
    have : ∏ k : ↥K, ((k : MulAut V) w * w⁻¹) = (normK K w) * (w⁻¹) ^ Fintype.card ↥K := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, normK_apply]
    rw [this, MonoidHom.mem_ker.mp hw, one_mul, inv_pow, pow_odd_eq_self hV _ hodd] at hprod
    simpa using hprod
  have hAC : A ≤ fixV K := by
    intro a ha k hk
    obtain ⟨j, rfl⟩ := hKmem k hk
    exact hAt _ a ha
  have hBC : ∀ b ∈ B, b ∈ fixV K → b ∈ A := fun b hb hbC =>
    hfix b hb (hbC (ρ (e d)) (by rw [hK]; exact Subgroup.mem_zpowers _))
  have hfixt : ∀ t, ∀ c ∈ fixV K, ρ (e' t) c = c := by
    intro t0 c hc
    have hCinv : ∀ t, ρ (e' t) c ∈ fixV K := by
      intro t k hk
      rw [← hcommK t k hk c, hc k hk]
    have hχA : ∀ t, ρ (e' t) c * c⁻¹ ∈ A := by
      intro t
      refine hBC _ (hVB _ c) ?_
      exact Subgroup.mul_mem _ (hCinv t) (Subgroup.inv_mem _ hc)
    have hχ : ∀ s t, ρ (e' (s * t)) c * c⁻¹ = (ρ (e' s) c * c⁻¹) * (ρ (e' t) c * c⁻¹) := by
      intro s t
      have h2 : ρ (e' t) c = (ρ (e' t) c * c⁻¹) * c := by group
      have h3 : ρ (e' (s * t)) c = ρ (e' s) (ρ (e' t) c) := by
        rw [map_mul, map_mul]; rfl
      rw [h3]
      conv_lhs => rw [h2]
      rw [map_mul, hAt _ _ (hχA t)]
      ac_rfl
    have := hperf (fun t => ρ (e' t) c * c⁻¹) hχ t0
    exact mul_inv_eq_one.mp this
  have hinvW : ∀ t, ∀ w ∈ (normK K).ker, ρ (e' t) w ∈ (normK K).ker := by
    intro t w hw
    rw [MonoidHom.mem_ker, normK_apply]
    have : ∀ k : ↥K, (k : MulAut V) (ρ (e' t) w) = ρ (e' t) ((k : MulAut V) w) := fun k =>
      (hcommK t k k.2 w).symm
    simp only [this]
    rw [← map_prod, ← normK_apply, MonoidHom.mem_ker.mp hw, map_one]
  refine ⟨hodd, h1, hAC, hBC, hfixt, hinvW, ?_⟩
  intro t v
  have hdec : v = (v * (normK K v)⁻¹) * normK K v := by group
  have hW : v * (normK K v)⁻¹ ∈ (normK K).ker := normK_div_mem_ker K hodd hV v
  have hC : normK K v ∈ fixV K := normK_mem_fixV K v
  have h4 : ρ (e' t) v * v⁻¹ = ρ (e' t) (v * (normK K v)⁻¹) * (v * (normK K v)⁻¹)⁻¹ := by
    conv_lhs => rw [hdec]
    rw [map_mul, hfixt t _ hC]
    group
  rw [h4]
  exact Subgroup.mul_mem _ (hinvW t _ hW) (Subgroup.inv_mem _ hW)

theorem emb_two_seven (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G : Subgroup (MulAut V)) (n : ℕ) (hn : 2 ≤ n)
    (hind : ∀ A B : Subgroup V, GInv G A → GInv G B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (A B : Subgroup V) (_hAB : A ≤ B) (_hA : GInv G A) (hB : GInv G B)
    (hAt : ∀ g ∈ G, ∀ a ∈ A, g a = a) (hVB : ∀ g ∈ G, ∀ v : V, g v * v⁻¹ ∈ B)
    (hnat : IsNatSectionBy (omegaPlusAct n) G B A) : A = ⊥ ∧ B = ⊤ := by
  classical
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  let ρ : ↥G →* MulAut V := G.subtype
  have hAt' : ∀ g : ↥G, ∀ a ∈ A, ρ g a = a := fun g a ha => hAt g g.2 a ha
  have hVB' : ∀ (g : ↥G) (v : V), ρ g v * v⁻¹ ∈ B := fun g v => hVB g g.2 v
  have hB' : ∀ (g : ↥G), ∀ b ∈ B, ρ g b ∈ B := fun g b hb => hB g g.2 b hb
  have hcardF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2n' : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hoddF : Odd (Nat.card (Fq n) - 1) := by
    rw [hcardF]
    have hpos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
    exact ⟨2 ^ (n - 1) - 1, by omega⟩
  obtain ⟨d, m, hm, hdm, hfpfL, hfpfR⟩ := exists_odd_fpf (Fq n) (by omega) hoddF
  have h4 : ∃ s : Finset (Fq n), s.card = 4 := by
    have : Fintype (Fq n) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fq n)))
      (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h2n)
    exact ⟨s, hs⟩
  have hperf := sl2_mult_trivial (Fq n) h4 (M := V)
  let e₁ : SpecialLinearGroup (Fin 2) (Fq n) →* ↥G := θ.symm.toMonoidHom.comp (MonoidHom.inl _ _)
  let e₂ : SpecialLinearGroup (Fin 2) (Fq n) →* ↥G := θ.symm.toMonoidHom.comp (MonoidHom.inr _ _)
  have hcomm12 : ∀ s t, e₁ s * e₂ t = e₂ t * e₁ s := by
    intro s t
    apply θ.injective
    simp [e₁, e₂]
  have hcomm21 : ∀ s t, e₂ s * e₁ t = e₁ t * e₂ s := fun s t => (hcomm12 t s).symm
  have hdec : ∀ g : ↥G, ∃ s t, g = e₁ s * e₂ t := by
    intro g
    refine ⟨(θ g).1, (θ g).2, ?_⟩
    apply θ.injective
    simp [e₁, e₂]
  have hact : ∀ (x : ↥G) (b : V) (hb : b ∈ B), β ⟨ρ x b, hB' x b hb⟩ =
      omegaPlusAct n (θ x) (β ⟨b, hb⟩) := fun x b hb => hβe x ⟨b, hb⟩ _
  have hAmem : ∀ (b : V) (hb : b ∈ B), β ⟨b, hb⟩ = 1 → b ∈ A := by
    intro b hb h1
    have : (⟨b, hb⟩ : ↥B) ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at this
    exact this
  have hfix₁ : ∀ b ∈ B, ρ (e₁ d) b = b → b ∈ A := by
    intro b hb hfix
    have h1 := hact (e₁ d) b hb
    have h2 : β ⟨ρ (e₁ d) b, hB' _ b hb⟩ = β ⟨b, hb⟩ := by
      congr 1; exact Subtype.ext hfix
    have hθ : θ (e₁ d) = (d, 1) := by simp [e₁]
    rw [h2, hθ] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    have h5 : (d : Matrix (Fin 2) (Fin 2) (Fq n)) * Multiplicative.toAdd (β ⟨b, hb⟩) =
        Multiplicative.toAdd (β ⟨b, hb⟩) := by simpa [omegaPlusAct] using h3.symm
    have h4 := hfpfL _ h5
    apply hAmem b hb
    apply Multiplicative.toAdd.injective
    simpa using h4
  have hfix₂ : ∀ b ∈ B, ρ (e₂ d) b = b → b ∈ A := by
    intro b hb hfix
    have h1 := hact (e₂ d) b hb
    have h2 : β ⟨ρ (e₂ d) b, hB' _ b hb⟩ = β ⟨b, hb⟩ := by
      congr 1; exact Subtype.ext hfix
    have hθ : θ (e₂ d) = (1, d) := by simp [e₂]
    rw [h2, hθ] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    have h5 : Multiplicative.toAdd (β ⟨b, hb⟩) * (d : Matrix (Fin 2) (Fin 2) (Fq n)).transpose =
        Multiplicative.toAdd (β ⟨b, hb⟩) := by simpa [omegaPlusAct] using h3.symm
    have h4 := hfpfR _ h5
    apply hAmem b hb
    apply Multiplicative.toAdd.injective
    simpa using h4
  have hFin : ∀ K : Subgroup (MulAut V), Fintype ↥K := fun K => Fintype.ofFinite _
  obtain ⟨hodd1, hW1B, hAC1, hBC1, hfix1, hinv1, hdiv1⟩ := half_split hV ρ A B hAt' hVB' e₁ e₂
    hcomm12 d hm hdm hfix₁ hperf (Subgroup.zpowers (ρ (e₁ d))) rfl
  obtain ⟨hodd2, hW2B, hAC2, hBC2, hfix2, hinv2, hdiv2⟩ := half_split hV ρ A B hAt' hVB' e₂ e₁
    hcomm21 d hm hdm hfix₂ hperf (Subgroup.zpowers (ρ (e₂ d))) rfl
  let K₁ : Subgroup (MulAut V) := Subgroup.zpowers (ρ (e₁ d))
  let K₂ : Subgroup (MulAut V) := Subgroup.zpowers (ρ (e₂ d))
  have hK₂ : ∀ k ∈ K₂, ∃ t, k = ρ (e₂ t) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨d ^ j, by rw [map_zpow, map_zpow]⟩
  have hK₁ : ∀ k ∈ K₁, ∃ t, k = ρ (e₁ t) := by
    intro k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨d ^ j, by rw [map_zpow, map_zpow]⟩
  have hWW : (normK K₂).ker ≤ (normK K₁).ker := by
    intro w hw
    rw [eq_prod_of_mem_ker_normK K₂ hodd2 hV hw]
    refine Subgroup.prod_mem _ fun k _ => Subgroup.inv_mem _ ?_
    obtain ⟨t, ht⟩ := hK₂ k k.2
    rw [ht]
    exact hdiv1 t w
  have hWW' : (normK K₁).ker ≤ (normK K₂).ker := by
    intro w hw
    rw [eq_prod_of_mem_ker_normK K₁ hodd1 hV hw]
    refine Subgroup.prod_mem _ fun k _ => Subgroup.inv_mem _ ?_
    obtain ⟨t, ht⟩ := hK₁ k k.2
    rw [ht]
    exact hdiv2 t w
  have hWeq : (normK K₂).ker = (normK K₁).ker := le_antisymm hWW hWW'
  have hCC : fixV K₁ ≤ fixV K₂ := by
    intro c hc k hk
    obtain ⟨t, rfl⟩ := hK₂ k hk
    exact hfix1 t c hc
  have hCC' : fixV K₂ ≤ fixV K₁ := by
    intro c hc k hk
    obtain ⟨t, rfl⟩ := hK₁ k hk
    exact hfix2 t c hc
  have hCeq : fixV K₂ = fixV K₁ := le_antisymm hCC' hCC
  have hgsplit : ∀ g ∈ G, ∀ v : V, ∃ s t, g v = ρ (e₁ s) (ρ (e₂ t) v) := by
    intro g hg v
    obtain ⟨s, t, hst⟩ := hdec ⟨g, hg⟩
    refine ⟨s, t, ?_⟩
    have : ρ ⟨g, hg⟩ v = ρ (e₁ s * e₂ t) v := by rw [← hst]
    rw [map_mul] at this
    exact this
  have hWinv : ∀ g ∈ G, ∀ w ∈ (normK K₁).ker, g w ∈ (normK K₁).ker := by
    intro g hg w hw
    obtain ⟨s, t, h1⟩ := hgsplit g hg w
    rw [h1]
    have h2 : ρ (e₂ t) w ∈ (normK K₁).ker := hinv1 t w hw
    have h3 : ρ (e₁ s) (ρ (e₂ t) w) ∈ (normK K₂).ker := hinv2 s _ (hWeq ▸ h2)
    rwa [hWeq] at h3
  have hCinv : ∀ g ∈ G, ∀ c ∈ fixV K₁, g c = c := by
    intro g hg c hc
    obtain ⟨s, t, h1⟩ := hgsplit g hg c
    rw [h1, hfix1 t c hc]
    exact hfix2 s c (hCeq ▸ hc)
  have hsup : (normK K₁).ker ⊔ fixV K₁ = ⊤ := normK_ker_sup_fixV K₁ hodd1 hV
  have hinf : (normK K₁).ker ⊓ fixV K₁ = ⊥ := normK_ker_inf_fixV K₁ hodd1 hV
  have hCG : ∀ g ∈ G, ∀ c ∈ fixV K₁, g c ∈ fixV K₁ := by
    intro g hg c hc
    rw [hCinv g hg c hc]
    exact hc
  rcases hind _ _ hWinv hCG hinf hsup with hW | hC
  ·
    exfalso
    have hBA : ∀ b ∈ B, b ∈ A := by
      intro b hb
      have hdiv : b * (normK K₁ b)⁻¹ ∈ (normK K₁).ker := normK_div_mem_ker K₁ hodd1 hV b
      rw [hW, Subgroup.mem_bot, mul_inv_eq_one] at hdiv
      have hbC : b ∈ fixV K₁ := by rw [hdiv]; exact normK_mem_fixV K₁ b
      exact hBC1 b hb hbC
    obtain ⟨b, hb⟩ := hβs (Multiplicative.ofAdd 1)
    have h1 : β b = 1 := by
      have : (b : V) ∈ A := hBA b b.2
      have : b ∈ β.ker := by rw [hβk, Subgroup.mem_subgroupOf]; exact this
      exact this
    rw [h1] at hb
    have h2 : (1 : Matrix (Fin 2) (Fin 2) (Fq n)) = 0 := Multiplicative.ofAdd.injective hb.symm
    have h3 := congrFun (congrFun h2 0) 0
    simp at h3
  ·
    rw [hC, sup_bot_eq] at hsup
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro a ha
      have := hAC1 ha
      rwa [hC] at this
    · rw [eq_top_iff]
      intro v _
      exact hW1B (by rw [hsup]; trivial)

end CFSG.CGT.PushingUpLit.CGT6
