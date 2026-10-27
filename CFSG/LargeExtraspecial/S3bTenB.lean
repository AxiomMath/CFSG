module

public import CFSG.LargeExtraspecial.S3bTenA
public import CFSG.LargeExtraspecial.S3bTenGeom
public import CFSG.LargeExtraspecial.S3bThirteen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul)

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

instance instFiniteO : Finite S.O :=
  Finite.of_injective (fun s : S.O => ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

theorem mul_self_eq_one_of_mem_Abar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {s : S.O} (hs : s ∈ S.Abar g) : s * s = 1 := by
  rw [← pow_two]
  exact S.sq_eq_one_of_mem_Lbar haQ (S.Abar_le_Lbar haQ hne hs)

theorem card_Abar_le_four {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) : Nat.card (S.Abar g) ≤ 4 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Abar g) {1}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨s₂, hs₂, hs₂'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Abar g) {1, s₁}
    (Finset.card_le_two.trans_lt (by omega))
  obtain ⟨s₃, hs₃, hs₃'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Abar g)
    {1, s₁, s₂, s₁ * s₂} (Finset.card_le_four.trans_lt h)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs₁' hs₂' hs₃'
  have hsq := fun s (hs : s ∈ S.Abar g) => S.mul_self_eq_one_of_mem_Abar haQ hne hs
  have hcomm := fun s (hs : s ∈ S.Abar g) t (ht : t ∈ S.Abar g) =>
    S.Lbar_comm haQ (S.Abar_le_Lbar haQ hne hs) (S.Abar_le_Lbar haQ hne ht)
  have hinv : ∀ s ∈ S.Abar g, ∀ t, s * t = 1 → t = s := fun s hs t hst => by
    calc t = s * s * t := by rw [hsq s hs, one_mul]
      _ = s := by rw [mul_assoc, hst, mul_one]
  have h12 : s₁ * s₂ ≠ 1 := fun h' => hs₂'.2 (hinv s₁ hs₁ s₂ h')
  have h13 : s₁ * s₃ ≠ 1 := fun h' => hs₃'.2.1 (hinv s₁ hs₁ s₃ h')
  have h23 : s₂ * s₃ ≠ 1 := fun h' => hs₃'.2.2.1 (hinv s₂ hs₂ s₃ h')
  have h123 : s₁ * s₂ * s₃ ≠ 1 := fun h' =>
    hs₃'.2.2.2 (hinv (s₁ * s₂) (mul_mem hs₁ hs₂) s₃ h')
  obtain ⟨u₁, hu₁, he₁⟩ := S.exists_eichler_of_mem_Abar haQ hne hs₁
  obtain ⟨u₂, hu₂, he₂⟩ := S.exists_eichler_of_mem_Abar haQ hne hs₂
  obtain ⟨u₃, hu₃, he₃⟩ := S.exists_eichler_of_mem_Abar haQ hne hs₃
  have key := fun s (hs : s ∈ S.Abar g) (hs1 : s ≠ 1) u hu he =>
    (S.eichler_data_of_mem_Abar haQ hne hno (s := s) hs hs1 (u := u) hu he).2.1
  have hu₁₂ : polar S.q (S.cl (g * S.z * g⁻¹)) (u₁ + u₂) = 0 := by
    rw [polar_add_right, hu₁, hu₂, add_zero]
  refine false_of_three_anisotropic (q := S.q) (key s₁ hs₁ hs₁' u₁ hu₁ he₁)
    (key s₂ hs₂ hs₂'.1 u₂ hu₂ he₂) (key s₃ hs₃ hs₃'.1 u₃ hu₃ he₃)
    (key _ (mul_mem hs₁ hs₂) h12 (u₁ + u₂) hu₁₂ ?_)
    (key _ (mul_mem hs₁ hs₃) h13 (u₁ + u₃) (by rw [polar_add_right, hu₁, hu₃, add_zero]) ?_)
    (key _ (mul_mem hs₂ hs₃) h23 (u₂ + u₃) (by rw [polar_add_right, hu₂, hu₃, add_zero]) ?_)
    (key _ (mul_mem (mul_mem hs₁ hs₂) hs₃) h123 (u₁ + u₂ + u₃)
      (by rw [polar_add_right, hu₁₂, hu₃, add_zero]) ?_)
  · rw [Subgroup.coe_mul, he₁, he₂, eichler_mul hu₁ hu₂]
  · rw [Subgroup.coe_mul, he₁, he₃, eichler_mul hu₁ hu₃]
  · rw [Subgroup.coe_mul, he₂, he₃, eichler_mul hu₂ hu₃]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, he₁, he₂, he₃, eichler_mul hu₁ hu₂,
      eichler_mul hu₁₂ hu₃]

theorem card_Abar_eq_four {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hle : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ S.width) :
    Nat.card (S.Abar g) = 4 ∧ Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ S.width := by
  have h4 : Nat.card (S.Abar g) = 4 :=
    le_antisymm (S.card_Abar_le_four haQ hne hno) (S.four_le_card_Abar haQ hne hle)
  refine ⟨h4, ?_⟩
  have h1 := S.card_CQa_mul haQ
  rw [← S.card_Abar_mul haQ hne, h4] at h1
  have h2 : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ^ 2 = (2 ^ S.width) ^ 2 := by
    rw [← pow_mul, show S.width * 2 = 2 * S.width by ring]
    have e : 2 ^ (2 * S.width + 2) = 4 * 2 ^ (2 * S.width) := by
      rw [pow_add]
      ring
    rw [e] at h1
    have : 4 * (Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ^ 2) = 4 * 2 ^ (2 * S.width) := by
      rw [← h1]
      ring
    omega
  exact Nat.pow_left_injective (by norm_num) h2

omit [Finite G] in
theorem QG_inf_Qa_mul_eq_map {g h : G} (hh : h ∈ S.M) :
    S.QG ⊓ S.Qa (h * g) = (S.QG ⊓ S.Qa g).map (MulAut.conj h).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective, S.QG_map_conj hh, S.Qa_mul]

omit [Finite G] in
theorem card_QG_inf_Qa_mul {g h : G} (hh : h ∈ S.M) :
    Nat.card (S.QG ⊓ S.Qa (h * g) : Subgroup G) = Nat.card (S.QG ⊓ S.Qa g : Subgroup G) := by
  rw [S.QG_inf_Qa_mul_eq_map hh]
  exact card_map_of_injective (MulAut.conj h).injective

theorem card_QG_inf_Qa_eq {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.QG ⊓ S.Qa g : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) := by
  rw [← S.card_submodule, ← S.card_clPre,
    S.clPre_clSub inf_le_left ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩]

theorem q_eq_zero_of_mem_clSub_QG_inf_Qa {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) : S.q v = 0 := by
  obtain ⟨w, hw, hwQ, rfl⟩ := S.mem_clSub_iff.mp hv
  exact (S.q_cl_eq_zero_iff hwQ).mpr (S.QG_inf_Qa_sq hne hw)

theorem finrank_clSub_QG_inf_Qa {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {k : ℕ} (hk : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ k) :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) + 1 = k := by
  rw [S.card_QG_inf_Qa_eq haQ hne, ← pow_succ'] at hk
  exact Nat.pow_right_injective le_rfl hk

theorem ρ_mem_clSub_of_fix {g' y : G} (hbQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hbz : g' * S.z * g'⁻¹ ≠ S.z) (hy : y ∈ S.M)
    (hyb : y * (g' * S.z * g'⁻¹) * y⁻¹ = g' * S.z * g'⁻¹ ∨
      y * (g' * S.z * g'⁻¹) * y⁻¹ = g' * S.z * g'⁻¹ * S.z) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g')) :
    (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa g') := by
  obtain ⟨w, hw, hwQ, rfl⟩ := S.mem_clSub_iff.mp hv
  have hX : S.QG ⊓ S.Qa (y * g') = S.QG ⊓ S.Qa g' := by
    rcases hyb with h | h
    · rw [S.Qa_eq_of_conj_eq (show (y * g') * S.z * (y * g')⁻¹ = g' * S.z * g'⁻¹ by
        rw [← h]; group)]
    · exact S.QG_inf_Qa_eq_of_conj_eq_mul_z hbQ hbz (by rw [← h]; group)
  have hw' : y * w * y⁻¹ ∈ S.QG ⊓ S.Qa (y * g') :=
    ⟨S.conj_mem_QG hy hwQ, S.conj_mem_Qa_mul hw.2⟩
  rw [hX] at hw'
  rw [S.ρ_cl _ hwQ]
  exact S.cl_mem_clSub hw' hw'.1

theorem cl_not_mem_clSub_of_not_mem_Qa {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hh : h ∈ S.M) (hbQa : (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g) :
    S.cl (g * S.z * g⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa (h * g)) := by
  intro hmem
  obtain ⟨w, hw, hwQ, hwa⟩ := S.mem_clSub_iff.mp hmem
  have hab : g * S.z * g⁻¹ ≠ (h * g) * S.z * (h * g)⁻¹ := fun e => hbQa (by
    rw [← e]
    exact S.conj_z_mem_Qa g)
  rcases (S.cl_eq_cl_iff haQ hwQ).mp hwa.symm with rfl | rfl
  · exact hbQa (S.mem_Qa_symm hab hw.2)
  · obtain ⟨q, hq, hqa⟩ := S.exists_mul_conj_eq_mul_z haQ hne
    have hazb : (q * g) * S.z * (q * g)⁻¹ ≠ (h * g) * S.z * (h * g)⁻¹ := fun e => hbQa (by
      rw [← e, hqa]
      exact (S.Qa g).mul_mem (S.conj_z_mem_Qa g) (S.z_mem_Qa haQ hne))
    have h1 := S.mem_Qa_symm hazb (by rw [hqa]; exact hw.2)
    have h2 : (h * g) * S.z * (h * g)⁻¹ ∈ S.QG ⊓ S.Qa (q * g) := ⟨S.conj_mul_mem_QG hh haQ, h1⟩
    rw [S.QG_inf_Qa_mul_of_mem_QG haQ hne hq] at h2
    exact hbQa h2.2

theorem polar_eq_zero_of_eichler_fix {a u w : S.Qt} (ha0 : a ≠ 0) (haq : S.q a = 0)
    (hau : polar S.q a u = 0) (hwa : polar S.q w a = 0) (hfix : eichler S.q a u w = w) :
    polar S.q w u = 0 := by
  rw [eichler_apply_zmod2 haq hau, hwa, zero_smul, add_zero, mul_zero, add_zero,
    add_eq_left] at hfix
  rcases zmod2_eq_zero_or_eq_one (polar S.q w u) with h | h
  · exact h
  · rw [h, one_smul] at hfix
    exact absurd hfix ha0

theorem q_eq_one_of_isTypeC_eichler {a u : S.Qt} (haq : S.q a = 0) (hau : polar S.q a u = 0)
    (hC : IsTypeC S.q (eichler S.q a u) 2) : S.q u = 1 := by
  obtain ⟨-, -, -, -, -, x, hx, hqx⟩ := hC
  obtain ⟨c, c', rfl⟩ := Submodule.mem_span_pair.mp (commSpace_eichler_le a u hx)
  rcases zmod2_eq_zero_or_eq_one (S.q u) with h | h
  · exfalso
    apply hqx
    rw [map_add_eq, map_smul_zmod2, map_smul_zmod2, haq, h, polar_smul_left, polar_smul_right,
      hau]
    simp
  · exact h

theorem lemma_3_10_iii {g h y : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hh : h ∈ S.M) (hbQa : (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g) (hy : y ∈ S.M)
    (hyC : S.IsTypeCOn ⟨y, hy⟩ 2)
    (hya : S.cl (g * S.z * g⁻¹) ∈ commSpace (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hyb : (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹)) :
    S.cl (g * S.z * g⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa (h * g)) ∧
      S.clSub (S.QG ⊓ S.Qa (h * g)) ≤ fixSpace (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∧
      fixSpace (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
        LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) ∧
      (∀ x ∈ ((ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) ⊔ S.clSub (S.QG ⊓ S.Qa (h * g)), S.q x = 0) ∧
      finrank (ZMod 2) (((ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) ⊔ S.clSub (S.QG ⊓ S.Qa (h * g)) :
        Submodule (ZMod 2) S.Qt) = finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa (h * g))) + 1 := by
  have hbQ := S.conj_mul_mem_QG hh haQ
  have hbz := S.conj_mul_ne_z hh hne
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  have haW := S.cl_not_mem_clSub_of_not_mem_Qa haQ hne hh hbQa
  have hyb' : y * ((h * g) * S.z * (h * g)⁻¹) * y⁻¹ = (h * g) * S.z * (h * g)⁻¹ ∨
      y * ((h * g) * S.z * (h * g)⁻¹) * y⁻¹ = (h * g) * S.z * (h * g)⁻¹ * S.z := by
    rw [S.ρ_cl _ hbQ] at hyb
    exact (S.cl_eq_cl_iff hbQ (S.conj_mem_QG hy hbQ)).mp hyb.symm
  have hW' : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa (h * g)), S.q w = 0 := fun w hw =>
    S.q_eq_zero_of_mem_clSub_QG_inf_Qa hbz hw
  obtain ⟨h1, h2⟩ := le_fixSpace_of_isTypeC S.q_nondegenerate hyC ha0 haq hya hW'
    (fun w hw => S.ρ_mem_clSub_of_fix hbQ hbz hy hyb' hw) haW
  obtain ⟨h3, h4⟩ := span_sup_isTotallySingular ha0 haq hW' (h1.trans h2) haW
  exact ⟨haW, h1, h2, h3, h4⟩

theorem lemma_3_10_iii_plusType {g h y : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hh : h ∈ S.M) (hbQa : (h * g) * S.z * (h * g)⁻¹ ∉ S.Qa g)
    (hy : y ∈ S.M) (hyC : S.IsTypeCOn ⟨y, hy⟩ 2)
    (hya : S.cl (g * S.z * g⁻¹) ∈ commSpace (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hyb : (S.ρ ⟨y, hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹))
    (hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ S.width) :
    ∃ X : Submodule (ZMod 2) S.Qt, (∀ x ∈ X, S.q x = 0) ∧ finrank (ZMod 2) X = S.width := by
  obtain ⟨-, -, -, hX, hXdim⟩ := S.lemma_3_10_iii haQ hne hh hbQa hy hyC hya hyb
  have hWb := S.finrank_clSub_QG_inf_Qa (S.conj_mul_mem_QG hh haQ) (S.conj_mul_ne_z hh hne)
    (by rw [S.card_QG_inf_Qa_mul hh]; exact hcard)
  exact ⟨_, hX, by rw [hXdim]; exact hWb⟩

theorem lemma_3_10_iv {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hplus : ∃ X : Submodule (ZMod 2) S.Qt, (∀ x ∈ X, S.q x = 0) ∧
      finrank (ZMod 2) X = S.width)
    (hcard : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ S.width)
    {s s' : S.Qt ≃ₗ[ZMod 2] S.Qt} (hs : s ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hs' : s' ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hsW : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g), s w = w)
    (hs'W : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g), s' w = w)
    (hsC : IsTypeC S.q s 2) (hs'C : IsTypeC S.q s' 2) : ¬ IsTypeC S.q (s * s') 2 := by
  intro hC
  obtain ⟨X, hX, hXn⟩ := hplus
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff S.q_nondegenerate ha0 haq).mp hs
  obtain ⟨v, hv, rfl⟩ := (mem_pointRadical_iff S.q_nondegenerate ha0 haq).mp hs'
  rw [eichler_mul hu hv] at hC
  have hperp : ∀ (u' : S.Qt), polar S.q (S.cl (g * S.z * g⁻¹)) u' = 0 →
      (∀ w ∈ S.clSub (S.QG ⊓ S.Qa g), eichler S.q (S.cl (g * S.z * g⁻¹)) u' w = w) →
      u' ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) := by
    intro u' hu' hfix
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [polarBilin_apply_apply]
    obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hw
    refine S.polar_eq_zero_of_eichler_fix ha0 haq hu' ?_ (hfix _ hw)
    exact (S.polar_cl_eq_zero_iff hxQ haQ).mpr (S.QG_inf_Qa_comm hne hx ⟨haQ, S.conj_z_mem_Qa g⟩)
  exact false_of_anisotropic_of_witt S.q_nondegenerate S.finrank_Qt_eq_two_mul_width
    (fun w hw => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hw)
    (S.finrank_clSub_QG_inf_Qa haQ hne hcard) hX hXn (hperp u hu hsW) (hperp v hv hs'W)
    (S.q_eq_one_of_isTypeC_eichler haq hu hsC) (S.q_eq_one_of_isTypeC_eichler haq hv hs'C)
    (S.q_eq_one_of_isTypeC_eichler haq (by rw [polar_add_right, hu, hv, add_zero]) hC)

theorem mem_Qa_of_commute_of_card_le {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hle : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ S.width) (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹)) :
    (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g := by
  classical
  obtain ⟨h4, hcard⟩ := S.card_Abar_eq_four haQ hne hno hle
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  obtain ⟨t, ht, ht1⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Abar g) {1}
    (by rw [Finset.card_singleton]; omega)
  obtain ⟨τ, hτ, hτ'⟩ := exists_mem_not_mem_finset_of_card_lt (H := S.Abar g) {1, t}
    (Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht1 hτ'
  obtain ⟨u, hu, he⟩ := S.exists_eichler_of_mem_Abar haQ hne ht
  obtain ⟨v, hv, he'⟩ := S.exists_eichler_of_mem_Abar haQ hne hτ
  have htτ1 : t * τ ≠ 1 := fun h' => hτ'.2 (by
    calc τ = t * t * τ := by rw [S.mul_self_eq_one_of_mem_Abar haQ hne ht, one_mul]
      _ = t := by rw [mul_assoc, h', mul_one])
  have huv : polar S.q (S.cl (g * S.z * g⁻¹)) (u + v) = 0 := by
    rw [polar_add_right, hu, hv, add_zero]
  have heuv : ((t * τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      eichler S.q (S.cl (g * S.z * g⁻¹)) (u + v) := by
    rw [Subgroup.coe_mul, he, he', eichler_mul hu hv]
  obtain ⟨-, hqu, huW⟩ := S.eichler_data_of_mem_Abar haQ hne hno ht ht1 hu he
  obtain ⟨-, hqv, hvW⟩ := S.eichler_data_of_mem_Abar haQ hne hno hτ hτ'.1 hv he'
  obtain ⟨-, hquv, -⟩ := S.eichler_data_of_mem_Abar haQ hne hno (mul_mem ht hτ) htτ1 huv heuv
  by_contra hbQa
  have hbQ := S.conj_mul_mem_QG hh haQ
  have hbz := S.conj_mul_ne_z hh hne
  have hbperp : polar S.q (S.cl ((h * g) * S.z * (h * g)⁻¹)) (S.cl (g * S.z * g⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff hbQ haQ).mpr hab.symm
  obtain ⟨s, hs, hs1, w, hw, hsw, hqw, hbw⟩ : ∃ s ∈ S.Abar g, s ≠ 1 ∧ ∃ w : S.Qt,
      polar S.q (S.cl (g * S.z * g⁻¹)) w = 0 ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = eichler S.q (S.cl (g * S.z * g⁻¹)) w ∧ S.q w = 1 ∧
      polar S.q (S.cl ((h * g) * S.z * (h * g)⁻¹)) w = 0 := by
    by_cases h1 : polar S.q (S.cl ((h * g) * S.z * (h * g)⁻¹)) u = 0
    · exact ⟨t, ht, ht1, u, hu, he, hqu, h1⟩
    by_cases h2 : polar S.q (S.cl ((h * g) * S.z * (h * g)⁻¹)) v = 0
    · exact ⟨τ, hτ, hτ'.1, v, hv, he', hqv, h2⟩
    refine ⟨t * τ, mul_mem ht hτ, htτ1, u + v, huv, heuv, hquv, ?_⟩
    rw [polar_add_right, zmod2_eq_one_of_ne_zero h1, zmod2_eq_one_of_ne_zero h2]
    decide
  obtain ⟨y, hy, rfl⟩ := S.mem_Abar_iff.mp hs
  have hsb : (S.ρ y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) := by
    rw [hsw, eichler_apply_zmod2 haq hw, hbperp, hbw, zero_smul, add_zero, mul_zero, add_zero,
      zero_smul, add_zero]
  have hC := eichler_isTypeC S.q_nondegenerate ha0 haq hw hqw
  have hyC : S.IsTypeCOn ⟨y, y.2⟩ 2 := by
    change IsTypeC S.q (S.ρ y : S.Qt ≃ₗ[ZMod 2] S.Qt) 2
    rw [hsw]
    exact hC.1
  have hya : S.cl (g * S.z * g⁻¹) ∈ commSpace (S.ρ ⟨y, y.2⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    change S.cl (g * S.z * g⁻¹) ∈ commSpace (S.ρ y : S.Qt ≃ₗ[ZMod 2] S.Qt)
    rw [hsw, hC.2]
    exact Submodule.subset_span (by simp)
  obtain ⟨-, -, -, hXts, hXdim⟩ := S.lemma_3_10_iii haQ hne hh hbQa y.2 hyC hya hsb
  have hWb := S.finrank_clSub_QG_inf_Qa hbQ hbz (by rw [S.card_QG_inf_Qa_mul hh]; exact hcard)
  exact false_of_anisotropic_of_witt S.q_nondegenerate S.finrank_Qt_eq_two_mul_width
    (fun w hw => S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hw)
    (S.finrank_clSub_QG_inf_Qa haQ hne hcard) hXts (by rw [hXdim]; omega) huW hvW hqu hqv hquv

end Setting

end CFSG.LargeExtraspecial
