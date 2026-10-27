module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Module.ZMod

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzCorner

section Additive

variable {M : Type*} [AddCommGroup M]

theorem eq_zero_of_two_nsmul_eq_zero {m₁ m₂ m₃ : M} (h₁ : 2 • m₁ ≠ 0)
    (h₂ : ∀ e₁ : ℕ, e₁ < 2 → 2 • (m₂ + e₁ • m₁) ≠ 0)
    (h₃ : ∀ e₁ e₂ : ℕ, e₁ < 2 → e₂ < 2 → 2 • (m₃ + e₁ • m₁ + e₂ • m₂) ≠ 0)
    {e₁ e₂ e₃ : ℕ} (he₁ : e₁ < 2) (he₂ : e₂ < 2) (he₃ : e₃ < 2)
    (h : 2 • (e₁ • m₁ + e₂ • m₂ + e₃ • m₃) = 0) : e₁ = 0 ∧ e₂ = 0 ∧ e₃ = 0 := by
  interval_cases e₃
  · interval_cases e₂
    · interval_cases e₁
      · exact ⟨rfl, rfl, rfl⟩
      · exact absurd (by simpa using h) h₁
    · simp only [zero_smul, one_smul, add_zero] at h
      exact absurd (by rw [← h, add_comm]) (h₂ e₁ he₁)
  · simp only [one_smul] at h
    exact absurd (by rw [← h]; congr 1; abel) (h₃ e₁ e₂ he₁ he₂)

theorem exists_eq_add_two_mul (x : ZMod 4) :
    ∃ e δ : ℕ, e < 2 ∧ δ < 2 ∧ x = (e : ZMod 4) + 2 * (δ : ZMod 4) := by
  fin_cases x
  · exact ⟨0, 0, by norm_num, by norm_num, rfl⟩
  · exact ⟨1, 0, by norm_num, by norm_num, rfl⟩
  · exact ⟨0, 1, by norm_num, by norm_num, rfl⟩
  · exact ⟨1, 1, by norm_num, by norm_num, rfl⟩

theorem exists_not_mem_of_ncard_lt [Finite M] {S : Set M} (hS : S.ncard < Nat.card M) :
    ∃ x : M, x ∉ S := by
  by_contra hall
  have hS' : S = Set.univ := Set.eq_univ_of_forall fun x => by
    by_contra hx
    exact hall ⟨x, hx⟩
  rw [hS', Set.ncard_univ] at hS
  exact lt_irrefl _ hS

theorem ncard_translate_le [Finite M] (S : Set M) (m : M) :
    ((fun x => x - m) '' S).ncard ≤ S.ncard :=
  Set.ncard_image_le (Set.toFinite S)

theorem exists_addEquiv_zmod_four [Finite M] (h4 : ∀ x : M, 4 • x = 0)
    (hcard : Nat.card M = 64) (h2 : ∀ x : M, 2 • x = 0 → ∃ y : M, x = 2 • y) :
    Nonempty (M ≃+ (Fin 3 → ZMod 4)) := by
  classical
  have h22 : ∀ x : M, 2 • (2 • x) = 0 := fun x => by
    rw [smul_smul]
    exact h4 x
  let φ : M →+ M :=
    { toFun := fun x => 2 • x, map_zero' := nsmul_zero 2, map_add' := fun x y => nsmul_add x y 2 }
  have hmemD : ∀ x : M, x ∈ (φ.ker : Set M) ↔ 2 • x = 0 := fun x => AddMonoidHom.mem_ker
  have hrange : φ.range = φ.ker := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨y, rfl⟩
      exact (hmemD _).mpr (h22 y)
    · obtain ⟨y, hy⟩ := h2 x ((hmemD x).mp hx)
      exact ⟨y, hy.symm⟩
  have hD : (φ.ker : Set M).ncard = 8 := by
    have h1 : Nat.card M = Nat.card φ.ker * Nat.card φ.range := by
      rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
    rw [hrange, hcard] at h1
    rw [← Nat.card_coe_set_eq]
    obtain ⟨n, hn⟩ : ∃ n, Nat.card φ.ker = n := ⟨_, rfl⟩
    show Nat.card φ.ker = 8
    rw [hn] at h1 ⊢
    have hle : n ≤ 8 := by nlinarith
    interval_cases n <;> omega
  set D : Set M := (φ.ker : Set M) with hDdef
  obtain ⟨m₁, hm₁⟩ := exists_not_mem_of_ncard_lt (S := D) (by rw [hD, hcard]; norm_num)
  have h₁ : 2 • m₁ ≠ 0 := fun h => hm₁ ((hmemD m₁).mpr h)
  have hS₂ : (D ∪ (fun x => x - m₁) '' D).ncard < Nat.card M := by
    have a1 := ncard_translate_le D m₁
    have u1 := Set.ncard_union_le D ((fun x => x - m₁) '' D)
    rw [hcard]
    omega
  obtain ⟨m₂, hm₂⟩ := exists_not_mem_of_ncard_lt hS₂
  have h₂ : ∀ e₁ : ℕ, e₁ < 2 → 2 • (m₂ + e₁ • m₁) ≠ 0 := by
    intro e₁ he₁ h
    interval_cases e₁
    · exact hm₂ (Or.inl ((hmemD _).mpr (by simpa using h)))
    · exact hm₂ (Or.inr ⟨m₂ + m₁, (hmemD _).mpr (by simpa using h), add_sub_cancel_right _ _⟩)
  have hS₃ : (((D ∪ (fun x => x - m₁) '' D) ∪ (fun x => x - m₂) '' D) ∪
      (fun x => x - (m₁ + m₂)) '' D).ncard < Nat.card M := by
    have a1 := ncard_translate_le D m₁
    have a2 := ncard_translate_le D m₂
    have a3 := ncard_translate_le D (m₁ + m₂)
    have u1 := Set.ncard_union_le D ((fun x => x - m₁) '' D)
    have u2 := Set.ncard_union_le (D ∪ (fun x => x - m₁) '' D) ((fun x => x - m₂) '' D)
    have u3 := Set.ncard_union_le ((D ∪ (fun x => x - m₁) '' D) ∪ (fun x => x - m₂) '' D)
      ((fun x => x - (m₁ + m₂)) '' D)
    rw [hcard]
    omega
  obtain ⟨m₃, hm₃⟩ := exists_not_mem_of_ncard_lt hS₃
  have h₃ : ∀ e₁ e₂ : ℕ, e₁ < 2 → e₂ < 2 → 2 • (m₃ + e₁ • m₁ + e₂ • m₂) ≠ 0 := by
    intro e₁ e₂ he₁ he₂ h
    interval_cases e₁ <;> interval_cases e₂
    · exact hm₃ (Or.inl (Or.inl (Or.inl ((hmemD _).mpr (by simpa using h)))))
    · exact hm₃ (Or.inl (Or.inr ⟨m₃ + m₂, (hmemD _).mpr (by simpa using h), add_sub_cancel_right _ _⟩))
    · exact hm₃ (Or.inl (Or.inl (Or.inr ⟨m₃ + m₁, (hmemD _).mpr (by simpa using h), add_sub_cancel_right _ _⟩)))
    · exact hm₃ (Or.inr ⟨m₃ + (m₁ + m₂), (hmemD _).mpr (by simpa [add_assoc] using h), add_sub_cancel_right _ _⟩)
  let _ : Module (ZMod 4) M := AddCommGroup.zmodModule h4
  have hfin3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  let ψ : (Fin 3 → ZMod 4) →+ M :=
    { toFun := fun a => a 0 • m₁ + a 1 • m₂ + a 2 • m₃
      map_zero' := by simp
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul]; abel }
  have hψ : ∀ a : Fin 3 → ZMod 4, ψ a = a 0 • m₁ + a 1 • m₂ + a 2 • m₃ := fun a => rfl
  have hcast : ∀ (δ : ℕ) (m : M), (δ : ZMod 4) • m = δ • m := fun δ m =>
    Nat.cast_smul_eq_nsmul (ZMod 4) δ m
  have key : ∀ a : Fin 3 → ZMod 4, 2 • ψ a = 0 →
      ∀ i, ∃ δ : ℕ, δ < 2 ∧ a i = 2 * (δ : ZMod 4) := by
    intro a ha
    obtain ⟨e₀, δ₀, he₀, hδ₀, ha₀⟩ := exists_eq_add_two_mul (a 0)
    obtain ⟨e₁, δ₁, he₁, hδ₁, ha₁⟩ := exists_eq_add_two_mul (a 1)
    obtain ⟨e₂, δ₂, he₂, hδ₂, ha₂⟩ := exists_eq_add_two_mul (a 2)
    have hψa : ψ a = (e₀ • m₁ + e₁ • m₂ + e₂ • m₃) + 2 • (δ₀ • m₁ + δ₁ • m₂ + δ₂ • m₃) := by
      rw [hψ, ha₀, ha₁, ha₂]
      simp only [add_smul, mul_smul, two_smul, hcast]
      abel
    have h2e : 2 • (e₀ • m₁ + e₁ • m₂ + e₂ • m₃) = 0 := by
      rw [hψa, nsmul_add, h22, add_zero] at ha
      exact ha
    obtain ⟨z0, z1, z2⟩ := eq_zero_of_two_nsmul_eq_zero h₁ h₂ h₃ he₀ he₁ he₂ h2e
    intro i
    rcases hfin3 i with rfl | rfl | rfl
    · exact ⟨δ₀, hδ₀, by rw [ha₀, z0]; simp⟩
    · exact ⟨δ₁, hδ₁, by rw [ha₁, z1]; simp⟩
    · exact ⟨δ₂, hδ₂, by rw [ha₂, z2]; simp⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    choose δ hδ2 hδa using key a (by rw [ha, nsmul_zero])
    have hψa : ψ a = 2 • (δ 0 • m₁ + δ 1 • m₂ + δ 2 • m₃) := by
      rw [hψ, hδa 0, hδa 1, hδa 2]
      simp only [mul_smul, two_smul, hcast]
      abel
    rw [hψa] at ha
    obtain ⟨z0, z1, z2⟩ := eq_zero_of_two_nsmul_eq_zero h₁ h₂ h₃ (hδ2 0) (hδ2 1) (hδ2 2) ha
    funext i
    rcases hfin3 i with rfl | rfl | rfl
    · simp [hδa, z0]
    · simp [hδa, z1]
    · simp [hδa, z2]
  have hc : Nat.card (Fin 3 → ZMod 4) = 64 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le (by rw [hc, hcard])
  exact ⟨(AddEquiv.ofBijective ψ hbij).symm⟩

end Additive

section Det

noncomputable def det₄ (f : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4)) : ZMod 4 :=
  LinearMap.det (f.toZModLinearMap 4)

theorem det₄_comp (f g : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4)) :
    det₄ (f.comp g) = det₄ f * det₄ g := by
  unfold det₄
  rw [← LinearMap.det_comp]
  rfl

theorem det₄_id : det₄ (AddMonoidHom.id (Fin 3 → ZMod 4)) = 1 := by
  unfold det₄
  exact LinearMap.det_id

theorem det₄_neg : det₄ (-AddMonoidHom.id (Fin 3 → ZMod 4)) = -1 := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  unfold det₄
  have e : (-AddMonoidHom.id (Fin 3 → ZMod 4)).toZModLinearMap 4 =
      (-1 : ZMod 4) • LinearMap.id := by
    ext x i
    simp
  rw [e, LinearMap.det_smul, LinearMap.det_id, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]
  norm_num

theorem neg_one_ne_one_zmod_four : (-1 : ZMod 4) ≠ 1 := by decide

end Det

section Group

variable {G : Type*} [Group G]

theorem exists_ker_of_inv [Finite G] {W H : Subgroup G}
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (h4 : ∀ x ∈ W, x ^ 4 = 1)
    (hcard : Nat.card W = 64) (h2 : ∀ x ∈ W, x ^ 2 = 1 → ∃ y ∈ W, x = y ^ 2)
    (hH : H ≤ normalizer (W : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).Normal ∧ ⁅H, H⁆ ≤ K ∧
      (∀ h ∈ H, (∀ w ∈ W, h * w * h⁻¹ = w) → h ∈ K) ∧
      (∀ h ∈ H, (∀ w ∈ W, h * w * h⁻¹ = w⁻¹) → h ∉ K) := by
  classical
  let _ : CommGroup W :=
    { (inferInstance : Group W) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have : Finite (Additive W) := Finite.of_equiv W Additive.ofMul
  have h4' : ∀ x : Additive W, 4 • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using h4 _ (Additive.toMul x).2)
  have h2' : ∀ x : Additive W, 2 • x = 0 → ∃ y : Additive W, x = 2 • y := by
    intro x hx
    have hx' : ((Additive.toMul x : W) : G) ^ 2 = 1 := by
      have := congrArg (fun z : Additive W => ((Additive.toMul z : W) : G)) hx
      simpa using this
    obtain ⟨y, hy, hxy⟩ := h2 _ (Additive.toMul x).2 hx'
    refine ⟨Additive.ofMul ⟨y, hy⟩, Additive.toMul.injective ?_⟩
    rw [toMul_nsmul, toMul_ofMul]
    exact Subtype.ext (by simpa using hxy)
  have hcard' : Nat.card (Additive W) = 64 := by rw [Nat.card_congr Additive.toMul, hcard]
  obtain ⟨e⟩ := exists_addEquiv_zmod_four h4' hcard' h2'
  have hmem : ∀ h : H, ∀ w : W, (h : G) * w * (h : G)⁻¹ ∈ W := fun h w =>
    (mem_normalizer_iff.mp (hH h.2) w).mp w.2
  let cW : H → Additive W →+ Additive W := fun h =>
    { toFun := fun x => Additive.ofMul ⟨(h : G) * (Additive.toMul x : W) * (h : G)⁻¹,
        hmem h (Additive.toMul x)⟩
      map_zero' := by
        apply Additive.toMul.injective
        simp
      map_add' := fun x y => by
        apply Additive.toMul.injective
        apply Subtype.ext
        simp only [toMul_ofMul, toMul_add, Subgroup.coe_mul]
        group }
  have hcW : ∀ h : H, ∀ x : Additive W,
      ((Additive.toMul (cW h x) : W) : G) = (h : G) * (Additive.toMul x : W) * (h : G)⁻¹ :=
    fun h x => rfl
  let F : H → (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) := fun h =>
    e.toAddMonoidHom.comp ((cW h).comp e.symm.toAddMonoidHom)
  have hF1 : F 1 = AddMonoidHom.id _ := by
    refine AddMonoidHom.ext fun x => ?_
    show e (cW 1 (e.symm x)) = x
    have : cW 1 (e.symm x) = e.symm x := by
      apply Additive.toMul.injective
      exact Subtype.ext (by rw [hcW]; simp)
    rw [this, AddEquiv.apply_symm_apply]
  have hFmul : ∀ h₁ h₂ : H, F (h₁ * h₂) = (F h₁).comp (F h₂) := by
    intro h₁ h₂
    refine AddMonoidHom.ext fun x => ?_
    show e (cW (h₁ * h₂) (e.symm x)) = e (cW h₁ (e.symm (e (cW h₂ (e.symm x)))))
    rw [AddEquiv.symm_apply_apply]
    congr 1
    apply Additive.toMul.injective
    exact Subtype.ext (by rw [hcW, hcW, hcW]; simp only [coe_mul, mul_inv_rev]; group)
  let χ₀ : H →* ZMod 4 :=
    { toFun := fun h => det₄ (F h)
      map_one' := by simp only [hF1, det₄_id]
      map_mul' := fun h₁ h₂ => by simp only [hFmul, det₄_comp] }
  let χ : H →* (ZMod 4)ˣ := χ₀.toHomUnits
  have hχ : ∀ h : H, ((χ h : (ZMod 4)ˣ) : ZMod 4) = det₄ (F h) := fun h => rfl
  refine ⟨χ.ker.map H.subtype, map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · show ((χ.ker.map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  · have hc := Abelianization.commutator_subset_ker χ
    calc ⁅H, H⁆ = (commutator H).map H.subtype := by
          rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
      _ ≤ χ.ker.map H.subtype := map_mono hc
  · intro h hh hcen
    refine ⟨⟨h, hh⟩, ?_, rfl⟩
    have hF : F ⟨h, hh⟩ = AddMonoidHom.id _ := by
      refine AddMonoidHom.ext fun x => ?_
      show e (cW ⟨h, hh⟩ (e.symm x)) = x
      have : cW ⟨h, hh⟩ (e.symm x) = e.symm x := by
        apply Additive.toMul.injective
        exact Subtype.ext (by rw [hcW]; exact hcen _ (Additive.toMul (e.symm x)).2)
      rw [this, AddEquiv.apply_symm_apply]
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext (by rw [hχ, hF, det₄_id, Units.val_one])
  · intro h hh hinv hK
    obtain ⟨k, hk, hkh⟩ := hK
    have hk' : k = ⟨h, hh⟩ := Subtype.ext hkh
    subst hk'
    have hF : F ⟨h, hh⟩ = -AddMonoidHom.id _ := by
      refine AddMonoidHom.ext fun x => ?_
      show e (cW ⟨h, hh⟩ (e.symm x)) = -x
      have : cW ⟨h, hh⟩ (e.symm x) = -e.symm x := by
        apply Additive.toMul.injective
        exact Subtype.ext (by rw [hcW]; simpa using hinv _ (Additive.toMul (e.symm x)).2)
      rw [this, map_neg, AddEquiv.apply_symm_apply]
    have h1 := congrArg (fun u : (ZMod 4)ˣ => (u : ZMod 4)) (MonoidHom.mem_ker.mp hk)
    simp only [hχ, hF, det₄_neg, Units.val_one] at h1
    exact neg_one_ne_one_zmod_four h1

end Group

end SzCorner

end CFSG.SeitzReduction.RankOne
