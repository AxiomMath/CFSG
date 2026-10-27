module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Open.StatedAPI
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem excTL_par_aux {F : Type*} [Field F] {b c e q r t : F} (hne : q ≠ 0 ∨ r ≠ 0 ∨ t ≠ 0)
    (h1 : b * r = q * c) (h2 : b * t = q * e) (h3 : c * t = r * e) :
    ∃ μ : F, b = μ * q ∧ c = μ * r ∧ e = μ * t := by
  rcases hne with hq | hr | ht
  · refine ⟨b / q, by field_simp, ?_, ?_⟩
    · field_simp; linear_combination -h1
    · field_simp; linear_combination -h2
  · refine ⟨c / r, ?_, by field_simp, ?_⟩
    · field_simp; linear_combination h1
    · field_simp; linear_combination -h3
  · refine ⟨e / t, ?_, ?_, by field_simp⟩
    · field_simp; linear_combination h2
    · field_simp; linear_combination h3

theorem excTL_commute_of_commute_nonscalar {F : Type*} [Field F] {u v w : Matrix (Fin 2) (Fin 2) F}
    (hw : w 0 1 ≠ 0 ∨ w 1 0 ≠ 0 ∨ w 0 0 ≠ w 1 1)
    (hu : u * w = w * u) (hv : v * w = w * v) : u * v = v * u := by
  have hw' : w 0 1 ≠ 0 ∨ w 1 0 ≠ 0 ∨ w 0 0 - w 1 1 ≠ 0 := by
    rcases hw with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (sub_ne_zero.2 h))
  have e1 := congrFun (congrFun hu 0) 0
  have e2 := congrFun (congrFun hu 0) 1
  have e3 := congrFun (congrFun hu 1) 0
  have f1 := congrFun (congrFun hv 0) 0
  have f2 := congrFun (congrFun hv 0) 1
  have f3 := congrFun (congrFun hv 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3 f1 f2 f3
  obtain ⟨μ, hb, hc, he⟩ := excTL_par_aux hw' (b := u 0 1) (c := u 1 0) (e := u 0 0 - u 1 1)
    (by linear_combination e1) (by linear_combination -e2) (by linear_combination e3)
  obtain ⟨ν, hb', hc', he'⟩ := excTL_par_aux hw' (b := v 0 1) (c := v 1 0) (e := v 0 0 - v 1 1)
    (by linear_combination f1) (by linear_combination -f2) (by linear_combination f3)
  have ha : u 0 0 = u 1 1 + μ * (w 0 0 - w 1 1) := by linear_combination he
  have ha' : v 0 0 = v 1 1 + ν * (w 0 0 - w 1 1) := by linear_combination he'
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two,
    Fin.zero_eta, Fin.mk_one] <;> simp only [ha, ha', hb, hc, hb', hc'] <;> ring

theorem excTL_comm_mul_central {S : Type*} [Group S] {x z g : S} (hz : z ∈ Subgroup.center S) :
    ⁅x * z, g⁆ = ⁅x, g⁆ := by
  have h : z * g * z⁻¹ = g := by
    rw [mul_inv_eq_iff_eq_mul, ← Subgroup.mem_center_iff.1 hz g]
  simp only [commutatorElement_def, mul_inv_rev]
  calc x * z * g * (z⁻¹ * x⁻¹) * g⁻¹ = x * (z * g * z⁻¹) * x⁻¹ * g⁻¹ := by group
    _ = x * g * x⁻¹ * g⁻¹ := by rw [h]

theorem excTL_comm_mul_of_central {S : Type*} [Group S] {x y g : S}
    (hy : ⁅y, g⁆ ∈ Subgroup.center S) : ⁅x * y, g⁆ = ⁅x, g⁆ * ⁅y, g⁆ := by
  calc ⁅x * y, g⁆ = x * ⁅y, g⁆ * (g * x⁻¹ * g⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅y, g⁆ * x * (g * x⁻¹ * g⁻¹) := by rw [← Subgroup.mem_center_iff.1 hy x]
    _ = ⁅y, g⁆ * ⁅x, g⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅x, g⁆ * ⁅y, g⁆ := by
        have hc := Subgroup.mem_center_iff.1 hy ⁅x, g⁆
        exact hc.symm

theorem excTL_exists_comm_hom {S : Type*} [Group S] (Z : Subgroup S) [Z.Normal]
    (hZ : Z ≤ Subgroup.center S) {H : Type*} [Group H] (f : H →* S ⧸ Z) (ĝ : S)
    (hf : ∀ a, Commute (f a) (QuotientGroup.mk' Z ĝ)) :
    ∃ (l : H → S) (ε : H →* S), (∀ a, QuotientGroup.mk' Z (l a) = f a) ∧
      (∀ a, ε a = ⁅l a, ĝ⁆) ∧ (∀ a, ε a ∈ Z) := by
  choose l hl using fun a => QuotientGroup.mk'_surjective Z (f a)
  have hcent : ∀ a, ⁅l a, ĝ⁆ ∈ Z := fun a => by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement, hl a]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hf a).eq
  refine ⟨l, MonoidHom.mk' (fun a => ⁅l a, ĝ⁆) fun a b => ?_, hl, fun a => rfl, hcent⟩
  have h1 : QuotientGroup.mk' Z (l (a * b)) = QuotientGroup.mk' Z (l a * l b) := by
    rw [hl, map_mul, map_mul, hl, hl]
  obtain ⟨z, hz, hzeq⟩ : ∃ z ∈ Z, l (a * b) = l a * l b * z :=
    ⟨(l a * l b)⁻¹ * l (a * b), QuotientGroup.eq.1 h1.symm, by group⟩
  rw [hzeq, excTL_comm_mul_central (hZ hz), excTL_comm_mul_of_central (hZ (hcent b))]

theorem excTL_scalar_mul_self {F : Type} [Field F] {w : ↥(StatedSL 2 F)}
    (hw : w ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) : w * w = 1 := by
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hw
  have hdet := det_of_mem_statedSL w.2
  rw [← hc] at hdet
  have h2 : (c : F) * c = 1 := by
    have := Matrix.GeneralLinearGroup.det_scalar (n := Fin 2) c
    simpa [pow_two] using (congrArg Units.val this).symm.trans (by simpa using hdet)
  have hcc : c * c = 1 := Units.ext h2
  apply Subtype.ext
  change (w : GL (Fin 2) F) * w = 1
  rw [← hc, ← map_mul, hcc, map_one]

theorem excTL_scalar_three {F : Type} [Field F] {x y z : ↥(StatedSL 2 F)}
    (hx : x ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    (hy : y ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    (hz : z ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) :
    x = y ∨ x = z ∨ y = z := by
  obtain ⟨cx, hcx⟩ := Subgroup.mem_subgroupOf.1 hx
  obtain ⟨cy, hcy⟩ := Subgroup.mem_subgroupOf.1 hy
  obtain ⟨cz, hcz⟩ := Subgroup.mem_subgroupOf.1 hz
  have sq : ∀ (w : ↥(StatedSL 2 F)) (c : Fˣ),
      Matrix.GeneralLinearGroup.scalar (Fin 2) c = (w : GL (Fin 2) F) →
        (c : F) = 1 ∨ (c : F) = -1 := by
    intro w c hc
    have hdet := det_of_mem_statedSL w.2
    rw [← hc] at hdet
    have h2 : (c : F) * c = 1 := by
      have := Matrix.GeneralLinearGroup.det_scalar (n := Fin 2) c
      simpa [pow_two] using (congrArg Units.val this).symm.trans (by simpa using hdet)
    exact mul_self_eq_one_iff.1 h2
  have eq : ∀ (a b : ↥(StatedSL 2 F)) (ca cb : Fˣ),
      Matrix.GeneralLinearGroup.scalar (Fin 2) ca = (a : GL (Fin 2) F) →
      Matrix.GeneralLinearGroup.scalar (Fin 2) cb = (b : GL (Fin 2) F) → (ca : F) = cb → a = b := by
    intro a b ca cb ha hb h
    exact Subtype.ext (by rw [← ha, ← hb, Units.ext h])
  rcases sq x cx hcx with h | h <;> rcases sq y cy hcy with h' | h' <;>
    rcases sq z cz hcz with h'' | h'' <;>
    first
    | exact Or.inl (eq x y cx cy hcx hcy (h.trans h'.symm))
    | exact Or.inr (Or.inl (eq x z cx cz hcx hcz (h.trans h''.symm)))
    | exact Or.inr (Or.inr (eq y z cy cz hcy hcz (h'.trans h''.symm)))

theorem excTL_ker_index_le_two {F : Type} [Field F] {H : Type*} [Group H]
    (ε : H →* ↥(StatedSL 2 F))
    (hε : ∀ a, ε a ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) :
    ε.ker.index ≤ 2 := by
  rw [Subgroup.index_ker]
  by_contra h
  push Not at h
  have : Finite ε.range := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite ε.range
  obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : ε.range, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    Fintype.two_lt_card_iff.1 (by rw [← Nat.card_eq_fintype_card]; exact h)
  have hmem : ∀ x : ε.range, (x : ↥(StatedSL 2 F)) ∈
      (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := by
    rintro ⟨_, a, rfl⟩
    exact hε a
  rcases excTL_scalar_three (hmem a) (hmem b) (hmem c) with h | h | h
  · exact hab (Subtype.ext h)
  · exact hac (Subtype.ext h)
  · exact hbc (Subtype.ext h)

theorem excTL_exists_ne_one_of_index_le_two {H : Type*} [Group H] (hH : 3 ≤ Nat.card H)
    {K : Subgroup H} (hK : K.index ≤ 2) : ∃ a ∈ K, a ≠ 1 := by
  have h1 := K.card_mul_index
  have hcard : 2 ≤ Nat.card K := by
    by_contra hlt
    push Not at hlt
    have : Nat.card K * K.index ≤ 1 * 2 := Nat.mul_le_mul (by omega) hK
    omega
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨a, ha⟩, h⟩ := exists_ne (1 : K)
  exact ⟨a, ha, fun h' => h (Subtype.ext h')⟩

theorem excTL_not_scalar {F : Type} [Field F] {g : ↥(StatedSL 2 F)}
    (hg : g ∉ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) :
    ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 ∨
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∨
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 ≠
          ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h01, h10, h00⟩ := hcon
  have hdet := det_of_mem_statedSL g.2
  rw [Matrix.det_fin_two, h01, h10, h00] at hdet
  have hc : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := fun h => by
    rw [h] at hdet
    simp at hdet
  apply hg
  refine Subgroup.mem_subgroupOf.2 ⟨Units.mk0 _ hc, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, h01, h10, h00]

theorem excTL_commute_lift {F : Type} [Field F] {ĝ u v : ↥(StatedSL 2 F)}
    (hĝ : ĝ ∉ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    (hu : u * ĝ = ĝ * u) (hv : v * ĝ = ĝ * v) : u * v = v * u := by
  have toMat : ∀ x y : ↥(StatedSL 2 F), x * y = y * x →
      ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((y : GL (Fin 2) F) : Matrix _ _ F) =
        ((y : GL (Fin 2) F) : Matrix _ _ F) * ((x : GL (Fin 2) F) : Matrix _ _ F) := by
    intro x y h
    have := congrArg (fun t : ↥(StatedSL 2 F) => ((t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  exact Subtype.ext (Units.ext (excTL_commute_of_commute_nonscalar (excTL_not_scalar hĝ)
    (toMat _ _ hu) (toMat _ _ hv)))

theorem excTL_psl2_kernel_data {F : Type} [Field F] {H : Type*} [Group H] (ĝ : ↥(StatedSL 2 F))
    (f : H →* StatedProj (StatedSL 2 F))
    (hf : ∀ a, Commute (f a) (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf
      (StatedSL 2 F)) ĝ)) :
    ∃ (l : H → ↥(StatedSL 2 F)) (K : Subgroup H), K.index ≤ 2 ∧ (∀ y z : H, ⁅y, z⁆ ∈ K) ∧
      (∀ y z : H, y ∈ K ∨ z ∈ K ∨ y * z ∈ K) ∧
      (∀ a, QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) (l a) = f a) ∧
        ∀ a ∈ K, l a * ĝ = ĝ * l a := by
  obtain ⟨l, ε, hl, hε, hZ⟩ := excTL_exists_comm_hom
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    (statedScalars_subgroupOf_le_center _) f ĝ hf
  refine ⟨l, ε.ker, excTL_ker_index_le_two ε hZ, fun y z => ?_, fun y z => ?_, hl, fun a ha => ?_⟩
  · rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 (statedScalars_subgroupOf_le_center _ (hZ y)) (ε z)).symm
  · by_cases hy : y ∈ ε.ker
    · exact Or.inl hy
    by_cases hz : z ∈ ε.ker
    · exact Or.inr (Or.inl hz)
    refine Or.inr (Or.inr ?_)
    rw [MonoidHom.mem_ker] at hy hz ⊢
    have h1 : (1 : ↥(StatedSL 2 F)) ∈ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) :=
      one_mem _
    rcases excTL_scalar_three (hZ y) (hZ z) h1 with h | h | h
    · rw [map_mul, ← h]
      exact excTL_scalar_mul_self (hZ y)
    · exact absurd h hy
    · exact absurd h hz
  · have := hε a
    rw [MonoidHom.mem_ker.1 ha] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this.symm

theorem excTL_psl2_abelian_index_two {F : Type} [Field F] {H : Type*} [Group H]
    {g : StatedProj (StatedSL 2 F)} (hg : g ≠ 1) (f : H →* StatedProj (StatedSL 2 F))
    (hf : ∀ a, Commute (f a) g) :
    ∃ K : Subgroup H, K.index ≤ 2 ∧ (∀ y z : H, ⁅y, z⁆ ∈ K) ∧
      (∀ y z : H, y ∈ K ∨ z ∈ K ∨ y * z ∈ K) ∧ ∀ a ∈ K, ∀ b ∈ K, Commute (f a) (f b) := by
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk'_surjective ((StatedScalars (Fin 2) F).subgroupOf
    (StatedSL 2 F)) g
  have hĝ : ĝ ∉ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := fun h =>
    hg ((QuotientGroup.eq_one_iff ĝ).2 h)
  obtain ⟨l, K, hK, hK1, hK2, hl, hc⟩ := excTL_psl2_kernel_data ĝ f hf
  refine ⟨K, hK, hK1, hK2, fun a ha b hb => ?_⟩
  rw [← hl a, ← hl b]
  exact Commute.map (excTL_commute_lift hĝ (hc a ha) (hc b hb)) _

theorem excTL_psl2_index_two {F : Type} [Field F] {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    {g : StatedProj (StatedSL 2 F)} (hg : g ≠ 1) (f₁ : H₁ →* StatedProj (StatedSL 2 F))
    (f₂ : H₂ →* StatedProj (StatedSL 2 F)) (h₁ : ∀ a, Commute (f₁ a) g)
    (h₂ : ∀ a, Commute (f₂ a) g) :
    ∃ (K₁ : Subgroup H₁) (K₂ : Subgroup H₂), K₁.index ≤ 2 ∧ K₂.index ≤ 2 ∧
      ∀ a ∈ K₁, ∀ b ∈ K₂, Commute (f₁ a) (f₂ b) := by
  obtain ⟨ĝ, rfl⟩ := QuotientGroup.mk'_surjective ((StatedScalars (Fin 2) F).subgroupOf
    (StatedSL 2 F)) g
  have hĝ : ĝ ∉ (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := fun h =>
    hg ((QuotientGroup.eq_one_iff ĝ).2 h)
  obtain ⟨l₁, K₁, hK₁, -, -, hl₁, hc₁⟩ := excTL_psl2_kernel_data ĝ f₁ h₁
  obtain ⟨l₂, K₂, hK₂, -, -, hl₂, hc₂⟩ := excTL_psl2_kernel_data ĝ f₂ h₂
  refine ⟨K₁, K₂, hK₁, hK₂, fun a ha b hb => ?_⟩
  rw [← hl₁ a, ← hl₂ b]
  exact Commute.map (excTL_commute_lift hĝ (hc₁ a ha) (hc₂ b hb)) _

theorem excTL_psl2_exists_commute {F : Type} [Field F] {H : Type*} [Group H]
    (hH : 3 ≤ Nat.card H) {g : StatedProj (StatedSL 2 F)} (hg : g ≠ 1)
    (f₁ f₂ : H →* StatedProj (StatedSL 2 F))
    (h₁ : ∀ a, Commute (f₁ a) g) (h₂ : ∀ a, Commute (f₂ a) g) :
    ∃ a b : H, a ≠ 1 ∧ b ≠ 1 ∧ Commute (f₁ a) (f₂ b) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hc⟩ := excTL_psl2_index_two hg f₁ f₂ h₁ h₂
  obtain ⟨a, ha, ha1⟩ := excTL_exists_ne_one_of_index_le_two hH hK₁
  obtain ⟨b, hb, hb1⟩ := excTL_exists_ne_one_of_index_le_two hH hK₂
  exact ⟨a, b, ha1, hb1, hc a ha b hb⟩

theorem excTL_false_of_heis {G : Type*} [Group G] {F : Type} [Field F]
    (φ : (G ⧸ Subgroup.center G) ≃* StatedProj (StatedSL 2 F))
    {H : Type*} [Group H] (hH : 3 ≤ Nat.card H) (x y : H →* G) (c : G)
    (hc : c ∉ Subgroup.center G) (hx : ∀ s, Commute (x s) c) (hy : ∀ t, Commute (y t) c)
    (hxy : ∀ s t, s ≠ 1 → t ≠ 1 → ⁅x s, y t⁆ ∉ Subgroup.center G) : False := by
  have hg : φ (QuotientGroup.mk' (Subgroup.center G) c) ≠ 1 := fun h => hc
    ((QuotientGroup.eq_one_iff c).1 (φ.injective (h.trans (map_one φ).symm)))
  obtain ⟨a, b, ha, hb, hab⟩ := excTL_psl2_exists_commute hH hg
    ((φ : (G ⧸ Subgroup.center G) →* _).comp ((QuotientGroup.mk' (Subgroup.center G)).comp x))
    ((φ : (G ⧸ Subgroup.center G) →* _).comp ((QuotientGroup.mk' (Subgroup.center G)).comp y))
    (fun s => ((hx s).map (QuotientGroup.mk' (Subgroup.center G))).map φ.toMonoidHom)
    (fun t => ((hy t).map (QuotientGroup.mk' (Subgroup.center G))).map φ.toMonoidHom)
  refine hxy a b ha hb ?_
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
  refine commutatorElement_eq_one_iff_mul_comm.2 (φ.injective ?_)
  simpa using hab.eq

end CFSG.HardMathSupport.Dickson.Sec6.I1431
