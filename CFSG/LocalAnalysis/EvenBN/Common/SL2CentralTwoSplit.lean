module

public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Matrix CFSG.LieType.Steinberg CFSG.SectionRank.EvenCover
  CFSG.LieType.Steinberg.CentralExt.SL2Closed
open scoped MatrixGroups commutatorElement

namespace SL2Split

variable {k : Type} [Field k]

theorem sl2_eq_upper_lower_upper (s : Matrix.SpecialLinearGroup (Fin 2) k)
    (h : (s : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    s = sl2Upper (((s : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) / (s : Matrix (Fin 2) (Fin 2) k) 1 0) *
      sl2Lower ((s : Matrix (Fin 2) (Fin 2) k) 1 0) *
      sl2Upper (((s : Matrix (Fin 2) (Fin 2) k) 1 1 - 1) / (s : Matrix (Fin 2) (Fin 2) k) 1 0) := by
  have hdet := s.2
  rw [Matrix.det_fin_two] at hdet
  ext x y
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  fin_cases x <;> fin_cases y
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    linear_combination (-1 : k) * hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

theorem sl2_eq_prod (s : Matrix.SpecialLinearGroup (Fin 2) k) :
    ∃ e a b c : k, s = sl2Lower e * sl2Upper a * sl2Lower b * sl2Upper c := by
  have hlow0 : sl2Lower (0 : k) = 1 := by
    ext x y
    fin_cases x <;> fin_cases y <;> rfl
  by_cases h : (s : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · set s' := sl2Lower (1 : k) * s with hs'_def
    have hdet := s.2
    rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
    have h' : (s' : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
      simp only [s', Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, Matrix.mul_apply,
        Fin.sum_univ_two]
      simp [h]
      exact left_ne_zero_of_mul_eq_one hdet
    have hs' := sl2_eq_upper_lower_upper s' h'
    refine ⟨-1, ((s' : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) / (s' : Matrix (Fin 2) (Fin 2) k) 1 0,
      (s' : Matrix (Fin 2) (Fin 2) k) 1 0,
      ((s' : Matrix (Fin 2) (Fin 2) k) 1 1 - 1) / (s' : Matrix (Fin 2) (Fin 2) k) 1 0, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc (sl2Upper _), ← hs', hs'_def, ← mul_assoc,
      show sl2Lower (-1 : k) * sl2Lower 1 = 1 by
        ext x y
        fin_cases x <;> fin_cases y <;> simp [Matrix.mul_apply, Fin.sum_univ_two, coe_sl2Lower],
      one_mul]
  · refine ⟨0, ((s : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) / (s : Matrix (Fin 2) (Fin 2) k) 1 0,
      (s : Matrix (Fin 2) (Fin 2) k) 1 0,
      ((s : Matrix (Fin 2) (Fin 2) k) 1 1 - 1) / (s : Matrix (Fin 2) (Fin 2) k) 1 0, ?_⟩
    rw [hlow0, one_mul]
    exact sl2_eq_upper_lower_upper s h

theorem sl2Rels_sub_eq_top : (sl2Rels k).sub = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod s
  exact mul_mem (mul_mem (mul_mem ((sl2Rels k).y_mem_sub e) ((sl2Rels k).x_mem_sub a))
    ((sl2Rels k).y_mem_sub b)) ((sl2Rels k).x_mem_sub c)

end SL2Split

variable {k : Type} [Field k] [Finite k]

theorem exists_section_of_central_sl2 (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9)
    {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin 2) k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin 2) k →* E, ∀ g, π (σ g) = g := by
  obtain ⟨u, hu0, hu1⟩ := exists_sq_ne_one hk
  obtain ⟨φ, hφ⟩ := (sl2Rels k).exists_section_of_central (by omega) hk9 hu0 hu1 sl2_cells_one
    sl2_cells_two hπ hcen
  let e : SpecialLinearGroup (Fin 2) k ≃* (sl2Rels k).sub :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr SL2Split.sl2Rels_sub_eq_top.symm)
  exact ⟨φ.comp e.toMonoidHom, fun g => hφ (e g)⟩

theorem commutator_inf_ker_eq_bot_sl2 (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9)
    {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin 2) k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : commutator E ⊓ π.ker = ⊥ := by
  obtain ⟨σ, hσ⟩ := exists_section_of_central_sl2 hk hk9 hπ hcen
  have hz : ∀ u : E, (σ (π u))⁻¹ * u ∈ π.ker := fun u => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  have hdec : ∀ u : E, u = σ (π u) * ((σ (π u))⁻¹ * u) := fun u => by group
  have hcomm : ∀ u v : E, ⁅u, v⁆ ∈ σ.range := fun u v => by
    have e1 : ⁅u, v⁆ = ⁅σ (π u), σ (π v)⁆ := by
      conv_lhs => rw [hdec u, hdec v]
      rw [CFSG.LieType.Steinberg.CentralExt.TorusLift.commutatorElement_mul_central_left
          (hcen (hz u)),
        CFSG.LieType.Steinberg.CentralExt.TorusLift.commutatorElement_mul_central_right
          (hcen (hz v))]
    rw [e1, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hle : commutator E ≤ σ.range := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro u _ v _
    exact hcomm u v
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨s, rfl⟩ := hle hx1
  rw [MonoidHom.mem_ker, hσ] at hx2
  rw [hx2, map_one]
  exact Subgroup.one_mem _

theorem ker_eq_bot_of_perfect_central_sl2 (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9)
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* SpecialLinearGroup (Fin 2) k}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  have h := commutator_inf_ker_eq_bot_sl2 hk hk9 hπ hcen
  rwa [Group.IsPerfect.commutator_eq_top (G := E), top_inf_eq] at h

theorem ker_eq_bot_of_perfect_central_sl2_two_pow {m : ℕ} (hm : 3 ≤ m)
    (hk : Nat.card k = 2 ^ m) {E : Type*} [Group E] [Group.IsPerfect E]
    {π : E →* SpecialLinearGroup (Fin 2) k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  refine ker_eq_bot_of_perfect_central_sl2 ?_ ?_ hπ hcen
  · rw [hk]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · intro h9
    have h2 : 2 ∣ Nat.card k := by
      rw [hk]
      exact dvd_pow_self 2 (by omega)
    rw [h9] at h2
    omega

theorem commutator_inf_le_of_sl2_quotient (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9)
    {K : Type*} [Group K] {D E : Subgroup K} (hED : E ≤ D) (hKD : ⁅(⊤ : Subgroup K), D⁆ ≤ E)
    (φ : K →* SpecialLinearGroup (Fin 2) k) (hφ : Function.Surjective φ) (hker : φ.ker = D) :
    commutator K ⊓ D ≤ E := by
  have hEn : E.Normal := by
    refine ⟨fun e he g => ?_⟩
    have h1 : ⁅g, e⁆ ∈ E := hKD (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (hED he))
    have h2 : g * e * g⁻¹ = ⁅g, e⁆ * e := by rw [commutatorElement_def]; group
    rw [h2]
    exact mul_mem h1 he
  have hEφ : E ≤ φ.ker := hker ▸ hED
  let ψ : K ⧸ E →* SpecialLinearGroup (Fin 2) k := QuotientGroup.lift E φ hEφ
  have hψ : Function.Surjective ψ := fun s => by
    obtain ⟨x, rfl⟩ := hφ s
    exact ⟨(x : K ⧸ E), rfl⟩
  have hψcen : ψ.ker ≤ Subgroup.center (K ⧸ E) := by
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker] at hz
    have hxD : x ∈ D := by
      rw [← hker, MonoidHom.mem_ker]
      exact hz
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h2 : (y * x)⁻¹ * (x * y) = ⁅x⁻¹, y⁻¹⁆ := by rw [commutatorElement_def]; group
    rw [h2, ← commutatorElement_inv]
    exact inv_mem (hKD (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (inv_mem hxD)))
  have hbot := commutator_inf_ker_eq_bot_sl2 hk hk9 hψ hψcen
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  have hmem : (x : K ⧸ E) ∈ commutator (K ⧸ E) := by
    have h1 : Subgroup.map (QuotientGroup.mk' E) (commutator K) = commutator (K ⧸ E) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective E)]
    rw [← h1]
    exact ⟨x, hx1, rfl⟩
  have hker' : (x : K ⧸ E) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    change φ x = 1
    rw [← MonoidHom.mem_ker, hker]
    exact hx2
  have : (x : K ⧸ E) ∈ commutator (K ⧸ E) ⊓ ψ.ker := Subgroup.mem_inf.2 ⟨hmem, hker'⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at this
  exact this

theorem commutator_inf_le_of_sl2_quotient_subgroup (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9)
    {G : Type*} [Group G] {K D E : Subgroup G} (hED : E ≤ D) (hKD : ⁅K, D⁆ ≤ E)
    (φ : ↥K →* SpecialLinearGroup (Fin 2) k) (hφ : Function.Surjective φ)
    (hker : φ.ker = D.subgroupOf K) : ⁅K, K⁆ ⊓ D ≤ E := by
  have hmain := commutator_inf_le_of_sl2_quotient (K := ↥K) (D := D.subgroupOf K)
    (E := E.subgroupOf K) hk hk9
    (fun x hx => Subgroup.mem_subgroupOf.2 (hED (Subgroup.mem_subgroupOf.1 hx))) (by
      rw [Subgroup.commutator_le]
      intro g _ d hd
      rw [Subgroup.mem_subgroupOf]
      exact hKD (Subgroup.commutator_mem_commutator g.2 (Subgroup.mem_subgroupOf.1 hd))) φ hφ hker
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  have hxK : x ∈ K := Subgroup.commutator_le_of_le le_rfl le_rfl hx1
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ commutator ↥K := by
    have hle : ⁅K, K⁆ ≤ (commutator ↥K).map K.subtype := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact ⟨⁅⟨a, ha⟩, ⟨b, hb⟩⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx1
    have : y = ⟨x, hxK⟩ := Subtype.ext hyx
    rwa [← this]
  have := hmain (Subgroup.mem_inf.2 ⟨hmem, Subgroup.mem_subgroupOf.2 hx2⟩)
  exact Subgroup.mem_subgroupOf.1 this

theorem commutator_inf_le_of_sl2_two_pow_quotient {m : ℕ} (hm : 3 ≤ m)
    (hk : Nat.card k = 2 ^ m) {G : Type*} [Group G] {K D E : Subgroup G} (hED : E ≤ D)
    (hKD : ⁅K, D⁆ ≤ E) (φ : ↥K →* SpecialLinearGroup (Fin 2) k) (hφ : Function.Surjective φ)
    (hker : φ.ker = D.subgroupOf K) : ⁅K, K⁆ ⊓ D ≤ E := by
  refine commutator_inf_le_of_sl2_quotient_subgroup ?_ ?_ hED hKD φ hφ hker
  · rw [hk]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  · intro h9
    have h2 : 2 ∣ Nat.card k := by
      rw [hk]
      exact dvd_pow_self 2 (by omega)
    rw [h9] at h2
    omega

end CFSG.LocalAnalysis.EvenBN.Common
