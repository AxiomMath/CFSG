module

public import CFSG.Fischer.Classification.Recognition.R3Order
public import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.Fischer.Classification.Recognition.R3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification F3

variable {n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}

section Transitive

variable (f) in
def Moves (a z z' : Fin n → ZMod 3) : Prop :=
  ∃ g ∈ F3.reflGroup f, ∃ ε : ZMod 3, ε * ε = 1 ∧ F3.act g a = ε • a ∧ F3.act g z = ε • z'

theorem Moves.trans {a z z' z'' : Fin n → ZMod 3} (h₁ : Moves f a z z') (h₂ : Moves f a z' z'') :
    Moves f a z z'' := by
  obtain ⟨g₁, hg₁, ε₁, hε₁, ha₁, hz₁⟩ := h₁
  obtain ⟨g₂, hg₂, ε₂, hε₂, ha₂, hz₂⟩ := h₂
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ε₁ * ε₂, ?_, ?_, ?_⟩
  · calc ε₁ * ε₂ * (ε₁ * ε₂) = (ε₁ * ε₁) * (ε₂ * ε₂) := by ring
      _ = 1 := by rw [hε₁, hε₂, one_mul]
  · rw [F3.act_mul, ha₁, F3.act_smul, ha₂, smul_smul, mul_comm]
  · rw [F3.act_mul, hz₁, F3.act_smul, hz₂, smul_smul, mul_comm]

theorem moves_smul {a z : Fin n → ZMod 3} (ha : f a a = 1) (hza : f z a = 0)
    {c : ZMod 3} (hc : c * c = 1) : Moves f a z (c • z) := by
  have hc' : c = 1 ∨ c = -1 := by revert c; decide
  rcases hc' with rfl | rfl
  · exact ⟨1, one_mem _, 1, by decide, by rw [F3.act_one, one_smul],
      by rw [F3.act_one, one_smul, one_smul]⟩
  · refine ⟨F3.refl f a, F3.refl_mem_reflGroup a, -1, by decide, ?_, ?_⟩
    · rw [F3.act_refl_self ha, neg_one_smul]
    · rw [F3.act_refl_of_perp ha hza, smul_smul, show (-1 : ZMod 3) * -1 = 1 by decide, one_smul]

theorem moves_of_pair (hf : IsF3Form f) {a z z' : Fin n → ZMod 3} (ha : f a a = 1)
    (hzz : f z z = 0) (hza : f z a = 0) (hz'z' : f z' z' = 0) (hz'a : f z' a = 0)
    (hzz' : f z z' ≠ 0) : Moves f a z z' := by
  have hz'z : f z' z = f z z' := hf.symm _ _
  have hc : f z z' = 1 ∨ f z z' = -1 := by revert hzz'; generalize f z z' = c; revert c; decide
  rcases hc with h | h
  · set u := z - z'
    have hu : f u u = 1 := by
      simp only [u, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hzz, hz'z', h,
        hz'z]
      linear_combination (-1 : ZMod 3) * three_eq_zero
    have hua : f a u = 0 := by
      rw [hf.symm]
      simp only [u, LinearMap.BilinForm.sub_left, hza, hz'a, sub_zero]
    refine ⟨F3.refl f u, F3.refl_mem_reflGroup u, 1, by decide, ?_, ?_⟩
    · rw [F3.act_refl hu, hua, zero_smul, add_zero, one_smul]
    · rw [F3.act_refl hu, one_smul]
      have : f z u = -1 := by
        simp only [u, LinearMap.BilinForm.sub_right, hzz, h, zero_sub]
      rw [this]
      simp only [u]
      module
  · set u := z + z'
    have hu : f u u = 1 := by
      simp only [u, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hzz, hz'z', h,
        hz'z]
      linear_combination (-1 : ZMod 3) * three_eq_zero
    have hua : f a u = 0 := by
      rw [hf.symm]
      simp only [u, LinearMap.BilinForm.add_left, hza, hz'a, add_zero]
    refine ⟨F3.refl f a * F3.refl f u, mul_mem (F3.refl_mem_reflGroup a) (F3.refl_mem_reflGroup u),
      -1, by decide, ?_, ?_⟩
    · rw [F3.act_mul, F3.act_refl hu, hua, zero_smul, add_zero, F3.act_refl_self ha,
        neg_one_smul]
    · have hzu : f z u = -1 := by
        simp only [u, LinearMap.BilinForm.add_right, hzz, h, zero_add]
      have h1 : F3.act (F3.refl f u) z = -z' := by
        rw [F3.act_refl hu, hzu]
        simp only [u]
        module
      have hz'a' : f (-z') a = 0 := by rw [LinearMap.BilinForm.neg_left, hz'a, neg_zero]
      rw [F3.act_mul, h1, F3.act_refl_of_perp ha hz'a', neg_one_smul]

theorem moves_of_isotropic (hf : IsF3Form f) {a z z' : Fin n → ZMod 3} (ha : f a a = 1)
    (hz : z ≠ 0) (hzz : f z z = 0) (hza : f z a = 0) (hz' : z' ≠ 0) (hz'z' : f z' z' = 0)
    (hz'a : f z' a = 0) : Moves f a z z' := by
  by_cases hzz' : f z z' = 0
  · by_cases hind : ∃ c : ZMod 3, z' = c • z
    · obtain ⟨c, rfl⟩ := hind
      have hc : c ≠ 0 := by rintro rfl; exact hz' (zero_smul _ z)
      exact moves_smul ha hza (F3.mul_self_of_ne_zero hc)
    · push Not at hind
      obtain ⟨x, hxx, hxa, hxz, hxz'⟩ :=
        F3.exists_isotropic_pairings hf ha hz hzz hza hz'a hzz' hind 1
      refine (moves_of_pair hf ha hzz hza hxx hxa ?_).trans
        (moves_of_pair hf ha hxx hxa hz'z' hz'a (by rw [hxz']; exact one_ne_zero))
      rw [hf.symm, hxz]
      exact one_ne_zero
  · exact moves_of_pair hf ha hzz hza hz'z' hz'a hzz'

theorem exists_isotropic_of_not_commute (hf : IsF3Form f) {a b : Fin n → ZMod 3}
    (ha : f a a = 1) (hb : f b b = 1)
    (hab : F3.refl f a * F3.refl f b ≠ F3.refl f b * F3.refl f a) :
    ∃ s : ZMod 3, s * s = 1 ∧ ∃ z, z ≠ 0 ∧ f z z = 0 ∧ f z a = 0 ∧ s • b = a + z := by
  rw [Ne, F3.refl_commute_iff hf ha hb] at hab
  push Not at hab
  obtain ⟨hab0, hba, hbna⟩ := hab
  have hba0 : f b a ≠ 0 := by rwa [hf.symm]
  have hs := F3.mul_self_of_ne_zero hba0
  have hs' : f b a = 1 ∨ f b a = -1 := by revert hba0; generalize f b a = c; revert c; decide
  refine ⟨f b a, hs, f b a • b - a, ?_, ?_, ?_, by abel⟩
  · intro h
    have h1 : f b a • b = a := sub_eq_zero.1 h
    rcases hs' with h2 | h2 <;> rw [h2] at h1
    · exact hba (by rw [one_smul] at h1; exact h1)
    · exact hbna (by rw [neg_one_smul] at h1; rw [← h1, neg_neg])
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hb, ha, hf.symm a b]
    linear_combination (-1 : ZMod 3) * hs
  · simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, ha]
    linear_combination hs

theorem exists_conj_refl_pair (hf : IsF3Form f) (hn : 4 ≤ n) {a b a' b' : Fin n → ZMod 3}
    (ha : f a a = 1) (hb : f b b = 1) (ha' : f a' a' = 1) (hb' : f b' b' = 1)
    (hab : F3.refl f a * F3.refl f b ≠ F3.refl f b * F3.refl f a)
    (hab' : F3.refl f a' * F3.refl f b' ≠ F3.refl f b' * F3.refl f a') :
    ∃ g ∈ F3.reflGroup f, g * F3.refl f a * g⁻¹ = F3.refl f a' ∧
      g * F3.refl f b * g⁻¹ = F3.refl f b' := by
  obtain ⟨g₀, hg₀, hg₀a⟩ := exists_mem_act_eq hf hn ha ha'
  have hiso₀ := F3.isIsom_of_mem hf hg₀
  set b₁ := F3.act g₀ b with hb₁def
  have hb₁ : f b₁ b₁ = 1 := by rw [hiso₀.norm, hb]
  have hab₁ : F3.refl f a' * F3.refl f b₁ ≠ F3.refl f b₁ * F3.refl f a' := by
    rw [← hg₀a, hb₁def, ← F3.conj_refl hiso₀, ← F3.conj_refl hiso₀]
    intro h
    apply hab
    calc F3.refl f a * F3.refl f b
        = g₀⁻¹ * (g₀ * F3.refl f a * g₀⁻¹ * (g₀ * F3.refl f b * g₀⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * (g₀ * F3.refl f b * g₀⁻¹ * (g₀ * F3.refl f a * g₀⁻¹)) * g₀ := by rw [h]
      _ = F3.refl f b * F3.refl f a := by group
  obtain ⟨s, hs, z, hz, hzz, hza, hsz⟩ := exists_isotropic_of_not_commute hf ha' hb₁ hab₁
  obtain ⟨s', hs', z', hz', hz'z', hz'a, hsz'⟩ := exists_isotropic_of_not_commute hf ha' hb' hab'
  obtain ⟨g₁, hg₁, ε, hε, h1a, h1z⟩ := moves_of_isotropic hf ha' hz hzz hza hz' hz'z' hz'a
  have hiso₁ := F3.isIsom_of_mem hf hg₁
  have hne : ∀ c : ZMod 3, c * c = 1 → c ≠ 0 := fun c hc h => by
    rw [h, mul_zero] at hc
    exact zero_ne_one hc
  refine ⟨g₁ * g₀, mul_mem hg₁ hg₀, ?_, ?_⟩
  · rw [show g₁ * g₀ * F3.refl f a * (g₁ * g₀)⁻¹ = g₁ * (g₀ * F3.refl f a * g₀⁻¹) * g₁⁻¹ by
      group, F3.conj_refl hiso₀, hg₀a, F3.conj_refl hiso₁, h1a, F3.refl_smul (hne ε hε)]
  · rw [show g₁ * g₀ * F3.refl f b * (g₁ * g₀)⁻¹ = g₁ * (g₀ * F3.refl f b * g₀⁻¹) * g₁⁻¹ by
      group, F3.conj_refl hiso₀, F3.conj_refl hiso₁, ← hb₁def]
    have h2 : s • F3.act g₁ b₁ = ε • (s' • b') := by
      rw [← F3.act_smul, hsz, F3.act_add, h1a, h1z, hsz', smul_add]
    have h3 : F3.act g₁ b₁ = (s * ε * s') • b' := by
      calc F3.act g₁ b₁ = (s * s) • F3.act g₁ b₁ := by rw [hs, one_smul]
        _ = s • (s • F3.act g₁ b₁) := by rw [mul_smul]
        _ = (s * ε * s') • b' := by rw [h2, smul_smul, smul_smul, mul_assoc]
    rw [h3, F3.refl_smul (mul_ne_zero (mul_ne_zero (hne s hs) (hne ε hε)) (hne s' hs'))]

end Transitive

theorem exists_conj_not_commute {Y : Type*} [Group Y] {K : Subgroup Y}
    (hK : CFSG.Open.IsQuasisimple K) {t : Y} (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hnc : ∃ k ∈ K, t * k ≠ k * t) : ∃ k ∈ K, k⁻¹ * t * k * t ≠ t * (k⁻¹ * t * k) := by
  by_contra! hall
  set F : Set Y := {y | ∃ k ∈ K, y = k⁻¹ * t * k}
  have hF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
    have h := hall (k₂ * k₁⁻¹) (mul_mem hk₂ (inv_mem hk₁))
    calc k₁⁻¹ * t * k₁ * (k₂⁻¹ * t * k₂)
        = k₁⁻¹ * (t * ((k₂ * k₁⁻¹)⁻¹ * t * (k₂ * k₁⁻¹))) * k₁ := by group
      _ = k₁⁻¹ * ((k₂ * k₁⁻¹)⁻¹ * t * (k₂ * k₁⁻¹) * t) * k₁ := by rw [h]
      _ = k₂⁻¹ * t * k₂ * (k₁⁻¹ * t * k₁) := by group
  set A := Subgroup.closure F
  have hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have h1 : A ≤ Subgroup.centralizer F := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      exact fun y hy => hF y hy x hx
    have h2 : A ≤ Subgroup.centralizer (A : Set Y) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.1 (h1 hy) x hx).symm
    exact fun a ha b hb => Subgroup.mem_centralizer_iff.1 (h2 hb) a ha
  set δ : Y → Y := fun k => k⁻¹ * t * k * t⁻¹
  have hδK : ∀ k ∈ K, δ k ∈ K := fun k hk => by
    have : δ k = k⁻¹ * (t * k * t⁻¹) := by simp only [δ]; group
    rw [this]
    exact mul_mem (inv_mem hk) (htK k hk)
  have htF : t ∈ F := ⟨1, one_mem _, by group⟩
  have hδA : ∀ k ∈ K, δ k ∈ A := fun k hk =>
    mul_mem (Subgroup.subset_closure ⟨k, hk, rfl⟩) (inv_mem (Subgroup.subset_closure htF))
  set H := Subgroup.closure (δ '' K)
  have hHK : H ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hδK k hk
  have hHA : H ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hδA k hk
  have hHn : (H.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hHK]
    intro h x hh hx
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      have : x * δ k * x⁻¹ = δ (k * x⁻¹) * (δ x⁻¹)⁻¹ := by simp only [δ]; group
      rw [this]
      exact mul_mem (Subgroup.subset_closure ⟨_, mul_mem hk (inv_mem hx), rfl⟩)
        (inv_mem (Subgroup.subset_closure ⟨_, inv_mem hx, rfl⟩))
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul y z _ _ hy hz =>
      have : x * (y * z) * x⁻¹ = x * y * x⁻¹ * (x * z * x⁻¹) := by group
      rw [this]
      exact mul_mem hy hz
    | inv y _ hy =>
      have : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hy
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (localCores_isQuasisimple hK) hHn with
    h | h
  · exact IsQuasisimple.not_le_of_comm hK hA ((Subgroup.subgroupOf_eq_top.1 h).trans hHA)
  ·
    have hcen : ∀ k ∈ K, ∀ x ∈ K, δ k * x = x * δ k := fun k hk x hx => by
      have hmem : (⟨δ k, hδK k hk⟩ : K) ∈ H.subgroupOf K :=
        Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure ⟨k, hk, rfl⟩)
      have := Subgroup.mem_center_iff.1 (h hmem) ⟨x, hx⟩
      exact (congrArg Subtype.val this).symm
    let φ : K →* Subgroup.center K :=
      { toFun := fun k => ⟨⟨δ k, hδK k k.2⟩, Subgroup.mem_center_iff.2 fun x =>
          Subtype.ext (hcen k k.2 x x.2).symm⟩
        map_one' := by
          apply Subtype.ext; apply Subtype.ext
          simp only [δ, OneMemClass.coe_one, inv_one, one_mul, mul_one, mul_inv_cancel]
        map_mul' := fun k₁ k₂ => by
          apply Subtype.ext; apply Subtype.ext
          simp only [Subgroup.coe_mul]
          have h1 : δ ((k₁ : Y) * k₂) = (k₂ : Y)⁻¹ * δ k₁ * k₂ * δ k₂ := by simp only [δ]; group
          have h2 : (k₂ : Y)⁻¹ * δ k₁ * k₂ = δ k₁ := by
            rw [mul_assoc, hcen k₁ k₁.2 k₂ k₂.2, inv_mul_cancel_left]
          rw [h1, h2] }
    obtain ⟨k, hk, hkt⟩ := hnc
    have hker : (⟨k, hk⟩ : K) ∈ φ.ker := by
      apply Abelianization.commutator_subset_ker φ
      rw [hK.1]
      trivial
    rw [MonoidHom.mem_ker] at hker
    have h1 : δ k = 1 := congrArg (fun x : Subgroup.center K => ((x : K) : Y)) hker
    apply hkt
    have h2 : k⁻¹ * t * k = t := by
      calc k⁻¹ * t * k = δ k * t := by simp only [δ]; group
        _ = t := by rw [h1, one_mul]
    calc t * k = k * (k⁻¹ * t * k) := by group
      _ = k * t := by rw [h2]

theorem reflElt_mul_self (a : Fin n → ZMod 3) : reflElt f a * reflElt f a = 1 :=
  Subtype.ext (F3.refl_mul_self a)

theorem reflElt_neg (a : Fin n → ZMod 3) : reflElt f (-a) = reflElt f a :=
  Subtype.ext (F3.refl_neg a)

theorem reflElt_commute_iff {a b : Fin n → ZMod 3} :
    reflElt f a * reflElt f b = reflElt f b * reflElt f a ↔
      F3.refl f a * F3.refl f b = F3.refl f b * F3.refl f a :=
  Subtype.ext_iff

section Normal

variable {K : Subgroup (F3.reflGroup f)}

theorem exists_reflElt_not_commute (hK : CFSG.Open.IsQuasisimple K) :
    ∃ a, f a a = 1 ∧ ∃ k ∈ K, reflElt f a * k ≠ k * reflElt f a := by
  by_contra! hall
  have hcen : ∀ k ∈ K, k ∈ Subgroup.center (F3.reflGroup f) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer
        (Subgroup.closure (Subtype.val ⁻¹' F3.reflSet f : Set (F3.reflGroup f)) : Set _) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨a, ha, hax⟩ := F3.mem_reflSet_iff.1 hx
      have : x = reflElt f a := Subtype.ext hax.symm
      rw [this]
      exact hall a ha k hk
    rw [Subgroup.closure_closure_coe_preimage] at hk'
    exact Subgroup.mem_center_iff.2 fun y => Subgroup.mem_centralizer_iff.1 hk' y trivial
  exact IsQuasisimple.not_le_of_comm hK (A := K)
    (fun x _ y hy => Subgroup.mem_center_iff.1 (hcen y hy) x) le_rfl

theorem reflElt_mul_mem (hf : IsF3Form f) (hn : 4 ≤ n) (hKn : K.Normal)
    (hK : CFSG.Open.IsQuasisimple K) {a b : Fin n → ZMod 3} (ha : f a a = 1) (hb : f b b = 1) :
    reflElt f a * reflElt f b ∈ K := by
  obtain ⟨a₀, ha₀, k, hk, hnc⟩ := exists_reflElt_not_commute hK
  have htK : ∀ x ∈ K, reflElt f a₀ * x * (reflElt f a₀)⁻¹ ∈ K := fun x hx =>
    hKn.conj_mem x hx _
  obtain ⟨k', hk', hk'nc⟩ := exists_conj_not_commute hK htK ⟨k, hk, hnc⟩
  have hiso := F3.isIsom_of_mem hf (k'⁻¹).2
  set b₀ := F3.act ((k'⁻¹ : F3.reflGroup f) : GL (Fin n) (ZMod 3)) a₀
  have hb₀ : f b₀ b₀ = 1 := by rw [hiso.norm, ha₀]
  have hconj : k'⁻¹ * reflElt f a₀ * k' = reflElt f b₀ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_reflElt, coe_reflElt, ← F3.conj_refl hiso,
      Subgroup.coe_inv, inv_inv]
  rw [hconj] at hk'nc
  have hmem₀ : reflElt f a₀ * reflElt f b₀ ∈ K := by
    have : reflElt f a₀ * reflElt f b₀ =
        reflElt f a₀ * k'⁻¹ * (reflElt f a₀)⁻¹ * k' := by
      rw [← hconj, inv_eq_of_mul_eq_one_right (reflElt_mul_self a₀)]
      group
    rw [this]
    exact mul_mem (hKn.conj_mem _ (inv_mem hk') _) hk'
  have hab₀ : F3.refl f a₀ * F3.refl f b₀ ≠ F3.refl f b₀ * F3.refl f a₀ := fun h =>
    hk'nc (reflElt_commute_iff.2 h).symm
  have hnc' : ∀ a' b', f a' a' = 1 → f b' b' = 1 →
      F3.refl f a' * F3.refl f b' ≠ F3.refl f b' * F3.refl f a' →
        reflElt f a' * reflElt f b' ∈ K := by
    intro a' b' ha' hb' hab'
    obtain ⟨g, hg, h1, h2⟩ := exists_conj_refl_pair hf hn ha₀ hb₀ ha' hb' hab₀ hab'
    have : reflElt f a' * reflElt f b' =
        ⟨g, hg⟩ * (reflElt f a₀ * reflElt f b₀) * (⟨g, hg⟩ : F3.reflGroup f)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_reflElt]
      rw [← h1, ← h2]
      group
    rw [this]
    exact hKn.conj_mem _ hmem₀ _
  by_cases hab : F3.refl f a * F3.refl f b = F3.refl f b * F3.refl f a
  · rcases (F3.refl_commute_iff hf ha hb).1 hab with h | rfl | rfl
    · obtain ⟨c, hc, hca, hcb⟩ := F3.exists_norm_one_ne_zero_ne_zero hf hn ha hb h
      have hac : f a c ≠ 0 := by rwa [hf.symm]
      have h1 : F3.refl f a * F3.refl f c ≠ F3.refl f c * F3.refl f a := by
        rw [Ne, F3.refl_commute_iff hf ha hc]
        push Not
        refine ⟨hac, fun h' => ?_, fun h' => ?_⟩
        · rw [h', h] at hcb
          exact hcb rfl
        · rw [h', LinearMap.BilinForm.neg_left, h, neg_zero] at hcb
          exact hcb rfl
      have h2 : F3.refl f c * F3.refl f b ≠ F3.refl f b * F3.refl f c := by
        rw [Ne, F3.refl_commute_iff hf hc hb]
        push Not
        refine ⟨hcb, fun h' => ?_, fun h' => ?_⟩
        · rw [h'] at h
          exact hac h
        · rw [h', LinearMap.BilinForm.neg_right, neg_eq_zero] at h
          exact hac h
      have : reflElt f a * reflElt f b =
          reflElt f a * reflElt f c * (reflElt f c * reflElt f b) := by
        rw [mul_assoc, ← mul_assoc (reflElt f c), reflElt_mul_self, one_mul]
      rw [this]
      exact mul_mem (hnc' a c ha hc h1) (hnc' c b hc hb h2)
    · rw [reflElt_mul_self]
      exact one_mem _
    · rw [reflElt_neg, reflElt_mul_self]
      exact one_mem _
  · exact hnc' a b ha hb hab

end Normal

theorem linearIndependent_of_norm_one {u w : Fin n → ZMod 3} (hu : f u u = 1) (hw : f w w = 1)
    (h1 : u ≠ w) (h2 : u ≠ -w) : LinearIndependent (ZMod 3) ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, zero_add] at hst
    refine ⟨rfl, ?_⟩
    by_contra ht
    exact F3.ne_zero_of_norm_one hw ((smul_eq_zero.1 hst).resolve_left ht)
  · exfalso
    have hss := F3.mul_self_of_ne_zero hs
    have hu' : u = (-(s * t)) • w := by
      calc u = (s * s) • u := by rw [hss, one_smul]
        _ = s • (s • u + t • w) - (s * t) • w := by
          rw [smul_add, smul_smul, smul_smul]
          abel
        _ = (-(s * t)) • w := by rw [hst, smul_zero, zero_sub, neg_smul]
    have hc : (-(s * t)) * (-(s * t)) = 1 := by
      have := hu
      rw [hu', F3.norm_smul, hw, mul_one] at this
      exact this
    have : -(s * t) = 1 ∨ -(s * t) = -1 := by
      revert hc
      generalize -(s * t) = d
      revert d
      decide
    rcases this with h | h <;> rw [h] at hu'
    · exact h1 (by rw [hu', one_smul])
    · exact h2 (by rw [hu', neg_one_smul])

theorem eq_one_or_eq_neg_one_of_commute (hf : IsF3Form f) (hn : 4 ≤ n)
    {g : GL (Fin n) (ZMod 3)} (hg : F3.IsIsom f g)
    (hc : ∀ a b, f a a = 1 → f b b = 1 →
      g * (F3.refl f a * F3.refl f b) = F3.refl f a * F3.refl f b * g) :
    g = 1 ∨ g = -1 := by
  refine F3.eq_one_or_eq_neg_one hf hn hg fun a ha => ?_
  by_contra hne
  push Not at hne
  set c := F3.act g a with hcdef
  have hcc : f c c = 1 := by rw [hg.norm, ha]
  have key : ∀ b, f b b = 1 → ∃ α β : ZMod 3, b = α • a + β • c := by
    intro b hb
    have hgb : f (F3.act g b) (F3.act g b) = 1 := by rw [hg.norm, hb]
    have h1 : F3.refl f c * F3.refl f (F3.act g b) = F3.refl f a * F3.refl f b := by
      rw [hcdef, ← F3.conj_refl hg, ← F3.conj_refl hg]
      calc g * F3.refl f a * g⁻¹ * (g * F3.refl f b * g⁻¹)
          = g * (F3.refl f a * F3.refl f b) * g⁻¹ := by group
        _ = F3.refl f a * F3.refl f b := by rw [hc a b ha hb, mul_inv_cancel_right]
    have h2 : F3.refl f a * F3.refl f c = F3.refl f b * F3.refl f (F3.act g b) := by
      calc F3.refl f a * F3.refl f c
          = F3.refl f a * (F3.refl f c * F3.refl f (F3.act g b)) * F3.refl f (F3.act g b) := by
            rw [mul_assoc, mul_assoc, F3.refl_mul_self, mul_one]
        _ = F3.refl f a * (F3.refl f a * F3.refl f b) * F3.refl f (F3.act g b) := by rw [h1]
        _ = F3.refl f b * F3.refl f (F3.act g b) := by
            rw [← mul_assoc (F3.refl f a), F3.refl_mul_self, one_mul]
    have hca : ¬ F3.refl f c = F3.refl f a := fun h => by
      rcases (F3.refl_eq_refl_iff hcc ha).1 h with h3 | h3
      · exact hne.1 h3.symm
      · exact hne.2 (by rw [h3, neg_neg])
    have hfix : F3.refl f (F3.act g b) = F3.refl f b → False := fun hy => by
      rw [hy, F3.refl_mul_self] at h2
      apply hca
      calc F3.refl f c = F3.refl f a * (F3.refl f a * F3.refl f c) := by
            rw [← mul_assoc, F3.refl_mul_self, one_mul]
        _ = F3.refl f a := by rw [h2, mul_one]
    have hne' : F3.act g b ≠ b ∧ F3.act g b ≠ -b := by
      refine ⟨fun h => hfix (by rw [h]), fun h => hfix (by rw [h, F3.refl_neg])⟩
    have hli := linearIndependent_of_norm_one hgb hb hne'.1 hne'.2
    obtain ⟨x, hx⟩ := F3.exists_pairings hf hli ![0, 1]
    have hx0 : f x (F3.act g b) = 0 := by simpa using hx 0
    have hx1 : f x b = 1 := by simpa using hx 1
    have h3 := congrArg (fun h => F3.act h x) h2
    simp only [F3.act_mul] at h3
    rw [F3.act_refl hgb, hx0, zero_smul, add_zero, F3.act_refl hb, hx1, one_smul,
      F3.act_refl hcc, F3.act_refl ha, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left] at h3
    exact ⟨f x a + f x c * f c a, f x c, by
      linear_combination (norm := module) (-1 : ZMod 3) • h3⟩
  obtain ⟨y, hy0, hy⟩ := F3.exists_ne_zero_perp (f := f) (k := 2) (by omega) ![a, c]
  have hya : f y a = 0 := by simpa using hy 0
  have hyc : f y c = 0 := by simpa using hy 1
  apply hy0
  refine F3.eq_zero_of_forall_norm_one hf (by omega) fun b hb => ?_
  obtain ⟨α, β, rfl⟩ := key b hb
  rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.smul_right, hya, hyc]
  ring

theorem card_reflGroup_eq (hf : IsF3Form f) (hn : 4 ≤ n) {K : Subgroup (F3.reflGroup f)}
    (hKn : K.Normal) (hK : CFSG.Open.IsQuasisimple K) :
    ∃ i z : ℕ, (i = 1 ∨ i = 2) ∧ (z = 1 ∨ z = 2) ∧
      Nat.card (F3.reflGroup f) = i * z * Nat.card (K ⧸ Subgroup.center K) := by
  have hprod : ∀ a b, f a a = 1 → f b b = 1 → reflElt f a * reflElt f b ∈ K :=
    fun a b ha hb => reflElt_mul_mem hf hn hKn hK ha hb
  obtain ⟨a₀, ha₀⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  set t := reflElt f a₀
  have htt : t * t = 1 := reflElt_mul_self a₀
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hdich : ∀ g : F3.reflGroup f, g ∈ K ∨ g * t ∈ K := by
    rintro ⟨g, hg⟩
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := F3.mem_reflSet_iff.1 hx
      exact Or.inr (hprod a a₀ ha ha₀)
    | one => exact Or.inl (one_mem _)
    | mul x y hx hy ihx ihy =>
      have hxy : (⟨x * y, mul_mem hx hy⟩ : F3.reflGroup f) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [hxy]
      set X : F3.reflGroup f := ⟨x, hx⟩
      set Y : F3.reflGroup f := ⟨y, hy⟩
      rcases ihx with hX | hX <;> rcases ihy with hY | hY
      · exact Or.inl (mul_mem hX hY)
      · exact Or.inr (by rw [mul_assoc]; exact mul_mem hX hY)
      · refine Or.inr ?_
        have : X * Y * t = X * t * (t⁻¹ * Y * t⁻¹⁻¹) := by group
        rw [this]
        exact mul_mem hX (hKn.conj_mem _ hY _)
      · refine Or.inl ?_
        have : X * Y = X * t * (t⁻¹ * (Y * t) * t⁻¹⁻¹) := by
          rw [inv_inv, htinv]
          calc X * Y = X * (t * t) * Y * (t * t) := by rw [htt, mul_one, mul_one]
            _ = X * t * (t * (Y * t) * t) := by group
        rw [this]
        exact mul_mem hX (hKn.conj_mem _ hY _)
    | inv x hx ih =>
      have hxi : (⟨x⁻¹, inv_mem hx⟩ : F3.reflGroup f) = (⟨x, hx⟩ : F3.reflGroup f)⁻¹ := rfl
      rw [hxi]
      rcases ih with hX | hX
      · exact Or.inl (inv_mem hX)
      · refine Or.inr ?_
        have : (⟨x, hx⟩ : F3.reflGroup f)⁻¹ * t = t * (⟨x, hx⟩ * t)⁻¹ * t⁻¹ := by
          rw [htinv]
          group
        rw [this]
        exact hKn.conj_mem _ (inv_mem hX) _
  have hidx : K.index = 1 ∨ K.index = 2 := by
    have hle : Nat.card (F3.reflGroup f ⧸ K) ≤ 2 := by
      have hsurj : Function.Surjective
          (![1, QuotientGroup.mk t] : Fin 2 → F3.reflGroup f ⧸ K) := by
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        rcases hdich g with hg | hg
        · exact ⟨0, by simpa using ((QuotientGroup.eq_one_iff g).2 hg).symm⟩
        · refine ⟨1, ?_⟩
          have h1 : (QuotientGroup.mk (g * t) : F3.reflGroup f ⧸ K) = 1 :=
            (QuotientGroup.eq_one_iff _).2 hg
          rw [QuotientGroup.mk_mul] at h1
          have h2 : (QuotientGroup.mk g : F3.reflGroup f ⧸ K) = (QuotientGroup.mk t)⁻¹ :=
            eq_inv_of_mul_eq_one_left h1
          rw [h2, ← QuotientGroup.mk_inv, htinv]
          rfl
      have := Nat.card_le_card_of_surjective _ hsurj
      rwa [Nat.card_fin] at this
    have hpos : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [Subgroup.index] at hpos ⊢
    omega
  have hcen : Nat.card (Subgroup.center K) = 1 ∨ Nat.card (Subgroup.center K) = 2 := by
    have hpm : ∀ x : Subgroup.center K,
        (((x : K) : F3.reflGroup f) : GL (Fin n) (ZMod 3)) ∈
          ({1, -1} : Set (GL (Fin n) (ZMod 3))) := by
      intro x
      have := eq_one_or_eq_neg_one_of_commute hf hn (F3.isIsom_of_mem hf x.1.1.2)
        fun a b ha hb => by
          have h := Subgroup.mem_center_iff.1 x.2 ⟨_, hprod a b ha hb⟩
          have h' := congrArg (fun y : K => ((y : F3.reflGroup f) : GL (Fin n) (ZMod 3))) h
          simp only [Subgroup.coe_mul, coe_reflElt] at h'
          exact h'.symm
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hinj : Function.Injective fun x : Subgroup.center K =>
        (⟨_, hpm x⟩ : ({1, -1} : Set (GL (Fin n) (ZMod 3)))) := by
      intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_coe_set_eq] at hle
    have h2 : ({1, -1} : Set (GL (Fin n) (ZMod 3))).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have hpos : 0 < Nat.card (Subgroup.center K) := Nat.card_pos
    omega
  refine ⟨K.index, Nat.card (Subgroup.center K), hidx, hcen, ?_⟩
  rw [← K.index_mul_card, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)]
  ring

end CFSG.Fischer.Classification.Recognition.R3
