module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseIDim6
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Dim4

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

section Frames

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N]
  {BN : LinearMap.BilinForm K N}

structure CaseI.Frame (BN : LinearMap.BilinForm K N) (a b c c' : N) : Prop where
  ab : BN a b = 1
  cc : BN c c' = 1
  ac : BN a c = 0
  ac' : BN a c' = 0
  bc : BN b c = 0
  bc' : BN b c' = 0

theorem CaseI.Frame.linearIndependent (hBN : BN.IsAlt) {a b c c' : N}
    (F : CaseI.Frame BN a b c c') : LinearIndependent K ![a, b, c, c'] :=
  linearIndependent_of_hyperbolic_pairs hBN F.ab F.cc F.ac F.ac' F.bc F.bc'

theorem CaseI.Frame.li_ac (hBN : BN.IsAlt) {a b c c' : N} (F : CaseI.Frame BN a b c c') :
    LinearIndependent K ![a, c] := by
  have h := CaseI.linearIndependent_pair_of_family (F.linearIndependent hBN)
    (i := (0 : Fin 4)) (j := 2) (by decide)
  simpa using h

theorem CaseI.Frame.li_ac' (hBN : BN.IsAlt) {a b c c' : N} (F : CaseI.Frame BN a b c c') :
    LinearIndependent K ![a, c'] := by
  have h := CaseI.linearIndependent_pair_of_family (F.linearIndependent hBN)
    (i := (0 : Fin 4)) (j := 3) (by decide)
  simpa using h

theorem CaseI.Frame.li_bc (hBN : BN.IsAlt) {a b c c' : N} (F : CaseI.Frame BN a b c c') :
    LinearIndependent K ![b, c] := by
  have h := CaseI.linearIndependent_pair_of_family (F.linearIndependent hBN)
    (i := (1 : Fin 4)) (j := 2) (by decide)
  simpa using h

theorem CaseI.Frame.li_bc' (hBN : BN.IsAlt) {a b c c' : N} (F : CaseI.Frame BN a b c c') :
    LinearIndependent K ![b, c'] := by
  have h := CaseI.linearIndependent_pair_of_family (F.linearIndependent hBN)
    (i := (1 : Fin 4)) (j := 3) (by decide)
  simpa using h

theorem CaseI.Frame.shift [CharP K 2] (hBN : BN.IsAlt) {a b c c' : N}
    (F : CaseI.Frame BN a b c c') : CaseI.Frame BN a (b + c) c (c' + a) := by
  have hca : BN c a = 0 := by rw [← hBN.neg_eq a c, F.ac, neg_zero]
  have hba : BN b a = 1 := by rw [← hBN.neg_eq a b, F.ab, CharTwo.neg_eq]
  refine ⟨?_, ?_, F.ac, ?_, ?_, ?_⟩
  · rw [map_add, F.ab, F.ac, add_zero]
  · rw [map_add, F.cc, hca, add_zero]
  · rw [map_add, F.ac', hBN.self_eq_zero, add_zero]
  · rw [map_add, LinearMap.add_apply, F.bc, hBN.self_eq_zero, add_zero]
  · have h2 : (1 : K) + 1 = 0 := by
      rw [one_add_one_eq_two]
      exact CharTwo.two_eq_zero
    simp only [map_add, LinearMap.add_apply]
    rw [F.bc', F.cc, hba, hca]
    linear_combination h2

theorem exists_frame_of_finrank_four [CharP K 2] [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (h4 : finrank K N = 4) :
    ∃ a b c c' : N, CaseI.Frame BN a b c c' := by
  obtain ⟨m, b, hb⟩ := hBN.exists_basis_toMatrix_eq_J hBNnd
  have hdim : finrank K N = m + m := by
    rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
  obtain rfl : m = 2 := by omega
  have hB : ∀ x y, BN (b x) (b y) = Matrix.J (Fin 2) K x y := fun x y => by
    rw [← hb, LinearMap.BilinForm.toMatrix_apply]
  refine ⟨b (Sum.inl 0), b (Sum.inr 0), b (Sum.inl 1), b (Sum.inr 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hB, Matrix.J, CharTwo.neg_eq]
  · simp [hB, Matrix.J, CharTwo.neg_eq]
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J]

end Frames

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

theorem CaseI.axis_sup_eq (hs : Setting hBN Qf ρ) (hI : CaseI hBN ρ) {a b c c' : N}
    (F : CaseI.Frame BN a b c c') {l m n p : K} (hl : l ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hp : p ≠ 0) :
    axis hBN ρ a l ⊔ axis hBN ρ b m = axis hBN ρ c n ⊔ axis hBN ρ c' p ∧
      finrank K ↥(axis hBN ρ c n ⊔ axis hBN ρ c' p) = 4 := by
  have hli := F.linearIndependent hBN
  have ha : a ≠ 0 := by simpa using hli.ne_zero (0 : Fin 4)
  have hb : b ≠ 0 := by simpa using hli.ne_zero (1 : Fin 4)
  have hc : c ≠ 0 := by simpa using hli.ne_zero (2 : Fin 4)
  have hc' : c' ≠ 0 := by simpa using hli.ne_zero (3 : Fin 4)
  have hcc : BN c c' ≠ 0 := by rw [F.cc]; exact one_ne_zero
  have hab : BN a b ≠ 0 := by rw [F.ab]; exact one_ne_zero
  obtain ⟨-, -, -, hfin, -⟩ := corollary_one_three hs.nondeg (hs.siegel c hc n hn)
    (hs.siegel c' hc' p hp) (CaseI.pow_four_ne_one hs hcc hn hp)
  obtain ⟨-, -, -, hfin', -⟩ := corollary_one_three hs.nondeg (hs.siegel a ha l hl)
    (hs.siegel b hb m hm) (CaseI.pow_four_ne_one hs hab hl hm)
  have hle : axis hBN ρ a l ⊔ axis hBN ρ b m ≤ axis hBN ρ c n ⊔ axis hBN ρ c' p :=
    sup_le
      (CaseI.axis_le_sup hs hcc ha hl hn hp (hI.inf_ne_bot_of_scalars (F.li_ac hBN) F.ac hl hn)
        (hI.inf_ne_bot_of_scalars (F.li_ac' hBN) F.ac' hl hp))
      (CaseI.axis_le_sup hs hcc hb hm hn hp (hI.inf_ne_bot_of_scalars (F.li_bc hBN) F.bc hm hn)
        (hI.inf_ne_bot_of_scalars (F.li_bc' hBN) F.bc' hm hp))
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle (hfin'.trans hfin.symm), hfin⟩

theorem CaseI.axis_le_Y (hs : Setting hBN Qf ρ) (hI : CaseI hBN ρ) {a b c c' : N}
    (F : CaseI.Frame BN a b c c') {x : N} (hx : x = a ∨ x = b ∨ x = c ∨ x = c') (l : K) :
    axis hBN ρ x l ≤ axis hBN ρ a 1 ⊔ axis hBN ρ b 1 := by
  by_cases hl : l = 0
  · rw [hl, axis_zero_scalar hs.nondegN]
    exact bot_le
  have h1 : ∀ {l m n p : K}, l ≠ 0 → m ≠ 0 → n ≠ 0 → p ≠ 0 →
      axis hBN ρ a l ⊔ axis hBN ρ b m = axis hBN ρ a 1 ⊔ axis hBN ρ b 1 := fun hl hm hn hp =>
    ((CaseI.axis_sup_eq hs hI F hl hm hn hp).1).trans
      ((CaseI.axis_sup_eq hs hI F one_ne_zero one_ne_zero hn hp).1).symm
  have h2 : ∀ {n p : K}, n ≠ 0 → p ≠ 0 →
      axis hBN ρ c n ⊔ axis hBN ρ c' p = axis hBN ρ a 1 ⊔ axis hBN ρ b 1 := fun hn hp =>
    ((CaseI.axis_sup_eq hs hI F one_ne_zero one_ne_zero hn hp).1).symm
  rcases hx with rfl | rfl | rfl | rfl
  · exact le_sup_left.trans (h1 hl one_ne_zero one_ne_zero one_ne_zero).le
  · exact le_sup_right.trans (h1 one_ne_zero hl one_ne_zero one_ne_zero).le
  · exact le_sup_left.trans (h2 hl one_ne_zero).le
  · exact le_sup_right.trans (h2 one_ne_zero hl).le

theorem CaseI.eq_top_of_axes_le (hs : Setting hBN Qf ρ) (hdim : finrank K N = 4) {a b c c' : N}
    (F : CaseI.Frame BN a b c c') {Y : Submodule K V}
    (hY : ∀ x ∈ ({a, b, c, c', b + c} : Set N), ∀ l : K, axis hBN ρ x l ≤ Y) : Y = ⊤ := by
  by_contra hne
  have hpos : 0 < finrank K (LinearMap.BilinForm.orthogonal (polarBilin Qf) Y) := by
    have h := finrank_orthogonal_polar hs.nondeg Y
    have hlt := Submodule.finrank_lt hne
    omega
  obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hfix : ∀ x ∈ ({a, b, c, c', b + c} : Set N), ∀ l : K, ρ (Tsp hBN x l) v = v := by
    intro x hx l
    have h := LinearMap.BilinForm.orthogonal_le (hY x hx l) hv
    rw [axis, ← ker_sub_one_eq_orthogonal_movedSpace hs.nondeg (hs.iso (Tsp hBN x l))] at h
    simpa [sub_eq_zero] using h
  have hle : Subgroup.closure {t : Gsp BN | ∃ x ∈ ({a, b, c, c', b + c} : Set N), ∃ l : K,
      t = Tsp hBN x l} ≤ rhoFixSubgroup ρ (Submodule.span K {v}) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, l, rfl⟩ w hw
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, hfix x hx l]
  rw [closure_Tsp_five_eq_top hBN hs.nondegN hdim F.ab F.cc F.ac F.ac' F.bc F.bc'] at hle
  exact hv0 (Subtype.ext (hs.fix v fun g =>
    hle (Subgroup.mem_top g) v (Submodule.mem_span_singleton_self v)))

theorem CaseI.finrank_eq_four (hs : Setting hBN Qf ρ) (hI : CaseI hBN ρ)
    (hdim : finrank K N = 4) {a b c c' : N} (F : CaseI.Frame BN a b c c') :
    finrank K V = 4 := by
  have F2 := F.shift hBN
  set Y₁ := axis hBN ρ a 1 ⊔ axis hBN ρ b 1 with hY₁
  set Y₂ := axis hBN ρ a 1 ⊔ axis hBN ρ (b + c) 1 with hY₂
  have hY₁4 : finrank K Y₁ = 4 := by
    have h := CaseI.axis_sup_eq hs hI F one_ne_zero one_ne_zero one_ne_zero one_ne_zero
    rw [hY₁, h.1]
    exact h.2
  have hY₂4 : finrank K Y₂ = 4 := by
    have h := CaseI.axis_sup_eq hs hI F2 one_ne_zero one_ne_zero one_ne_zero one_ne_zero
    rw [hY₂, h.1]
    exact h.2
  have hle₁ : ∀ x : N, (x = a ∨ x = b ∨ x = c ∨ x = c') → ∀ l : K, axis hBN ρ x l ≤ Y₁ :=
    fun x hx l => CaseI.axis_le_Y hs hI F hx l
  have hle₂ : ∀ x : N, (x = a ∨ x = b + c ∨ x = c ∨ x = c' + a) → ∀ l : K, axis hBN ρ x l ≤ Y₂ :=
    fun x hx l => CaseI.axis_le_Y hs hI F2 hx l
  have htop : Y₁ ⊔ Y₂ = ⊤ := by
    refine CaseI.eq_top_of_axes_le hs hdim F fun x hx l => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx | hx
    · exact (hle₁ x (Or.inl hx) l).trans le_sup_left
    · exact (hle₁ x (Or.inr (Or.inl hx)) l).trans le_sup_left
    · exact (hle₁ x (Or.inr (Or.inr (Or.inl hx))) l).trans le_sup_left
    · exact (hle₁ x (Or.inr (Or.inr (Or.inr hx))) l).trans le_sup_left
    · exact (hle₂ x (Or.inr (Or.inl hx)) l).trans le_sup_right
  obtain ⟨l, n, hl, hn, hne⟩ := exists_axis_ne hs (F.li_ac hBN)
  have ha : a ≠ 0 := by simpa using (F.linearIndependent hBN).ne_zero (0 : Fin 4)
  have hc : c ≠ 0 := by simpa using (F.linearIndependent hBN).ne_zero (2 : Fin 4)
  have hmeet := hI.inf_ne_bot_of_scalars (F.li_ac hBN) F.ac hl hn
  have h1 : finrank K ↥(axis hBN ρ a l ⊓ axis hBN ρ c n) = 1 :=
    finrank_inf_eq_one_of_finrank_two (CaseI.finrank_axis hs ha hl) (CaseI.finrank_axis hs hc hn)
      hne hmeet
  have h3 : finrank K ↥(axis hBN ρ a l ⊔ axis hBN ρ c n) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (axis hBN ρ a l) (axis hBN ρ c n)
    rw [h1, CaseI.finrank_axis hs ha hl, CaseI.finrank_axis hs hc hn] at h
    omega
  have hle : axis hBN ρ a l ⊔ axis hBN ρ c n ≤ Y₁ ⊓ Y₂ :=
    le_inf (sup_le (hle₁ a (Or.inl rfl) l) (hle₁ c (Or.inr (Or.inr (Or.inl rfl))) n))
      (sup_le (hle₂ a (Or.inl rfl) l) (hle₂ c (Or.inr (Or.inr (Or.inl rfl))) n))
  have h3' : 3 ≤ finrank K ↥(Y₁ ⊓ Y₂) := h3 ▸ Submodule.finrank_mono hle
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Y₁ Y₂
  rw [htop, finrank_top, hY₁4, hY₂4] at hsum
  have hge : 4 ≤ finrank K V := hY₁4 ▸ Submodule.finrank_le Y₁
  have hev : Even (finrank K V) := by
    exact LinearMap.BilinForm.IsAlt.even_finrank (B := polarBilin Qf)
      (fun x => polar_self_eq_zero x) (nondegenerate_polarBilin hs.nondeg)
  obtain ⟨r, hr⟩ := hev
  omega

theorem CaseI.axis_eq_axis_one (hs : Setting hBN Qf ρ) (h4 : finrank K V = 4) {x : N}
    (hx : x ≠ 0) {l : K} (hl : l ≠ 0) : axis hBN ρ x l = axis hBN ρ x 1 := by
  by_contra hne
  exact not_le_orthogonal_of_ne_of_finrank_four hs.nondeg h4 (CaseI.finrank_axis hs hx hl)
    (axis_totallySingular hs x 1) (CaseI.finrank_axis hs hx one_ne_zero)
    (axis_totallySingular hs x l) hne (axis_le_orthogonal_axis_self hs x l 1)

theorem false_of_caseI_of_finrank_four (hs : Setting hBN Qf ρ) (hI : CaseI hBN ρ)
    (hdim : finrank K N = 4) : False := by
  obtain ⟨a, b, c, c', F⟩ := exists_frame_of_finrank_four hBN hs.nondegN hdim
  have h4 := CaseI.finrank_eq_four hs hI hdim F
  have hli := F.li_ac hBN
  have hac := F.ac
  have hca : BN c a = 0 := by rw [← hBN.neg_eq a c, hac, neg_zero]
  have li1 : LinearIndependent K ![a, a + c] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro u v huv
    have h := hli (u + v) v (by rw [← huv]; module)
    exact ⟨by linear_combination h.1 - h.2, h.2⟩
  have li2 : LinearIndependent K ![c, a + c] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro u v huv
    have h := hli v (u + v) (by rw [← huv]; module)
    exact ⟨by linear_combination h.2 - h.1, h.1⟩
  have o1 : BN a (a + c) = 0 := by rw [map_add, hBN.self_eq_zero, hac, add_zero]
  have o2 : BN c (a + c) = 0 := by rw [map_add, hca, hBN.self_eq_zero, add_zero]
  have hne : ∀ {x y : N}, LinearIndependent K ![x, y] → axis hBN ρ x 1 ≠ axis hBN ρ y 1 := by
    intro x y hxy heq
    have hx : x ≠ 0 := by simpa using hxy.ne_zero (0 : Fin 2)
    have hy : y ≠ 0 := by simpa using hxy.ne_zero (1 : Fin 2)
    exact false_of_axis_eq hs hxy fun l m hl hm => by
      rw [CaseI.axis_eq_axis_one hs h4 hx hl, CaseI.axis_eq_axis_one hs h4 hy hm, heq]
  have ha : a ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have hc : c ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have hac0 : a + c ≠ 0 := by simpa using li1.ne_zero (1 : Fin 2)
  exact false_of_three_totallySingular_planes_pairwise_meet hs.nondeg h4
    (CaseI.finrank_axis hs ha one_ne_zero) (CaseI.finrank_axis hs hc one_ne_zero)
    (CaseI.finrank_axis hs hac0 one_ne_zero) (axis_totallySingular hs a 1)
    (axis_totallySingular hs c 1) (axis_totallySingular hs (a + c) 1) (hne hli) (hne li1)
    (hne li2) (hI a c hli hac) (hI a (a + c) li1 o1) (hI c (a + c) li2 o2)

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
