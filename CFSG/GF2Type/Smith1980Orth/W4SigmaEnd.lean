module

public import CFSG.GF2Type.Smith1980Orth.W4SigmaElem
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL
public import CFSG.GF2Type.Smith1980Orth.W4SigmaSp
public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth.W4Sigma

open Subgroup Module CFSG.LargeExtraspecial CFSG.GroupTheory.GLnTwoSplitting

theorem card_map_mul_card_le {N X : Type*} [Group N] [Group X] [Finite N] (f : N →* X)
    {K B : Subgroup N} (hBK : B ≤ K) (hB : B ≤ f.ker) :
    Nat.card (K.map f) * Nat.card B ≤ Nat.card K := by
  have h1 := Subgroup.card_mul_index (f.domRestrict K).ker
  rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h1
  have h2 : Nat.card B ≤ Nat.card (f.ker.subgroupOf K) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv]
    exact Subgroup.card_le_of_le fun y hy =>
      Subgroup.mem_subgroupOf.mpr (hB (Subgroup.mem_subgroupOf.mp hy))
  calc Nat.card (K.map f) * Nat.card B ≤ Nat.card (K.map f) * Nat.card (f.ker.subgroupOf K) :=
        Nat.mul_le_mul_left _ h2
    _ = Nat.card K := by rw [mul_comm]; exact h1

theorem zmod2_eq_of_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · rfl
  · exact absurd (h.mp rfl) one_ne_zero
  · exact absurd (h.mpr rfl) one_ne_zero
  · rfl

theorem exists_bilin_of_symm {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (f : M → M →ₗ[ZMod 2] ZMod 2) (hf : ∀ a b, f a b = f b a) :
    ∃ β : LinearMap.BilinForm (ZMod 2) M, ∀ a b, β a b = f a b :=
  ⟨LinearMap.mk₂ (ZMod 2) (fun a b => f a b)
    (fun a a' b => by rw [hf (a + a') b, map_add, hf b a, hf b a'])
    (fun r a b => by rw [hf (r • a) b, map_smul, hf b a])
    (fun a b b' => map_add _ _ _) (fun r a b => map_smul _ _ _), fun _ _ => rfl⟩

theorem mem_Qa_iff' {G : Type*} [Group G] (S : Setting G) (k y : G) :
    y ∈ S.Qa k ↔ k⁻¹ * y * k ∈ S.QG := by
  rw [Setting.Qa_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hw
  · intro hy
    exact ⟨k⁻¹ * y * k, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

namespace ElemAb

variable {G : Type*} [Group G] {e : ElemAb G}

theorem vec_eq_vec_iff {a b : e.E} : vec a = vec b ↔ (a : G) = b :=
  ⟨fun h => congrArg Subtype.val (vec_injective h), fun h => congrArg vec (Subtype.ext h)⟩

theorem exists_vec (v : Additive e.E) : ∃ a : e.E, vec a = v := ⟨Additive.toMul v, rfl⟩

theorem vec_eq_zero_iff {a : e.E} : vec a = 0 ↔ (a : G) = 1 := by
  rw [← vec_one, vec_eq_vec_iff]
  rfl

theorem conjHom_vec_eq_vec_iff (g : normalizer (e.E : Set G)) (a b : e.E) :
    e.conjHom g (vec a) = vec b ↔ (g : G) * a * (g : G)⁻¹ = b :=
  vec_eq_vec_iff

instance [Finite G] : Finite (Additive e.E ≃ₗ[ZMod 2] Additive e.E) :=
  Finite.of_injective (fun f => (f : Additive e.E → Additive e.E)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

end ElemAb

variable {G : Type*} [Group G] [Finite G]

structure SigmaEnd (S : Setting G) (A V : ElemAb G) (x u : G) : Prop where
  V_le : V.E ≤ A.E
  card_A : Nat.card A.E = 64
  card_V : Nat.card V.E = 32
  z_mem : S.z ∈ V.E
  mem_QG_iff : ∀ b ∈ A.E, b ∈ S.QG ↔ b ∈ V.E
  x_mem : x ∈ A.E
  x_not_mem : x ∉ V.E
  u_mem : u ∈ normalizer (A.E : Set G)
  u_conj_mem : u * S.z * u⁻¹ ∈ V.E
  u_conj_ne : u * S.z * u⁻¹ ≠ S.z
  QG_le : S.QG ≤ normalizer (A.E : Set G)
  trans : ∀ v ∈ V.E, ∀ w ∈ V.E, v ≠ 1 → v ≠ S.z → w ≠ 1 → w ≠ S.z →
    ∃ g ∈ normalizer (A.E : Set G), g ∈ S.M ∧ g * v * g⁻¹ = w
  surj : ∀ v ∈ V.E, ∃ q ∈ S.QG, q * x * q⁻¹ = x * v ∨ q * x * q⁻¹ = x * v * S.z
  cent_le : ∀ q ∈ S.QG, (∀ v ∈ V.E, q * v = v * q) → q ∈ V.E
  transv : ∀ f : Module.Dual (ZMod 2) (Additive V.E),
    f (ElemAb.vec (⟨S.z, z_mem⟩ : V.E)) = 0 →
      ∃ q ∈ S.QG, ∀ v : V.E, q * (v : G) = v * q ↔ f (ElemAb.vec v) = 0
  card_M : Nat.card S.M ≤ 368640

namespace SigmaEnd

variable {S : Setting G} {A V : ElemAb G} {x u : G}

theorem z_mem_A (h : SigmaEnd S A V x u) : S.z ∈ A.E := h.V_le h.z_mem

theorem A_le_M (h : SigmaEnd S A V x u) : A.E ≤ S.M := fun b hb =>
  S.mem_M_iff.mpr (A.comm b hb S.z h.z_mem_A)

theorem conj_mem_A {g : G} (hg : g ∈ normalizer (A.E : Set G)) {b : G} (hb : b ∈ A.E) :
    g * b * g⁻¹ ∈ A.E :=
  (mem_normalizer_iff.mp hg b).mp hb

theorem conj_z_mem_A (h : SigmaEnd S A V x u) {g : G} (hg : g ∈ normalizer (A.E : Set G)) :
    g * S.z * g⁻¹ ∈ A.E :=
  conj_mem_A hg h.z_mem_A

theorem conj_z_ne_one (g : G) : g * S.z * g⁻¹ ≠ 1 := (S.conjBy g).z_ne_one

theorem index_eq_two (h : SigmaEnd S A V x u) : (V.E.subgroupOf A.E).index = 2 := by
  have h1 := (V.E.subgroupOf A.E).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le).toEquiv, h.card_V, h.card_A] at h1
  omega

theorem mul_mem_V (h : SigmaEnd S A V x u) {a b : G} (ha : a ∈ A.E) (haV : a ∉ V.E)
    (hb : b ∈ A.E) (hbV : b ∉ V.E) : a * b ∈ V.E := by
  have key := Subgroup.mul_mem_iff_of_index_two h.index_eq_two (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  exact key.mpr (iff_of_false haV hbV)

theorem exists_conj_eq (h : SigmaEnd S A V x u) {v : G} (hv : v ∈ V.E) (hv1 : v ≠ 1) :
    ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = v := by
  by_cases hvz : v = S.z
  · exact ⟨1, one_mem _, by rw [hvz]; group⟩
  · obtain ⟨g, hgN, -, hg⟩ :=
      h.trans _ h.u_conj_mem v hv (conj_z_ne_one u) h.u_conj_ne hv1 hvz
    exact ⟨g * u, mul_mem hgN h.u_mem, by rw [← hg]; group⟩

theorem exists_conj_eq_or (h : SigmaEnd S A V x u) {y w : G} (hy : y ∈ A.E) (hyV : y ∉ V.E)
    (hw : w ∈ A.E) (hwV : w ∉ V.E) :
    ∃ q ∈ S.QG, q * y * q⁻¹ = w ∨ q * y * q⁻¹ = w * S.z := by
  have hxi : x⁻¹ ∈ A.E := inv_mem h.x_mem
  have hxiV : x⁻¹ ∉ V.E := fun h' => h.x_not_mem (by simpa using inv_mem h')
  obtain ⟨q₁, hq₁, h₁⟩ := h.surj _ (h.mul_mem_V hxi hxiV hy hyV)
  obtain ⟨q₂, hq₂, h₂⟩ := h.surj _ (h.mul_mem_V hxi hxiV hw hwV)
  simp only [mul_inv_cancel_left] at h₁ h₂
  have hz₁ := S.z_comm (S.QG_le_M hq₁)
  have hz₂ := S.z_comm (S.QG_le_M hq₂)
  have hzz := S.z_mul_z
  refine ⟨q₂ * q₁⁻¹, mul_mem hq₂ (inv_mem hq₁), ?_⟩
  have hy' : y = q₁ * x * q₁⁻¹ ∨ y = q₁ * x * q₁⁻¹ * S.z := by
    rcases h₁ with h₁ | h₁
    · exact Or.inl h₁.symm
    · right
      rw [h₁, mul_assoc, hzz, mul_one]
  rcases hy' with rfl | rfl
  · rw [show q₂ * q₁⁻¹ * (q₁ * x * q₁⁻¹) * (q₂ * q₁⁻¹)⁻¹ = q₂ * x * q₂⁻¹ by group]
    exact h₂
  · have e1 : q₁⁻¹ * S.z * q₁ = S.z := by rw [mul_assoc, ← hz₁, inv_mul_cancel_left]
    have e2 : q₂ * S.z * q₂⁻¹ = S.z := by rw [hz₂, mul_inv_cancel_right]
    have e : q₂ * q₁⁻¹ * (q₁ * x * q₁⁻¹ * S.z) * (q₂ * q₁⁻¹)⁻¹ = q₂ * x * q₂⁻¹ * S.z := by
      calc q₂ * q₁⁻¹ * (q₁ * x * q₁⁻¹ * S.z) * (q₂ * q₁⁻¹)⁻¹
          = q₂ * x * (q₁⁻¹ * S.z * q₁) * q₂⁻¹ := by group
        _ = q₂ * x * q₂⁻¹ * (q₂ * S.z * q₂⁻¹) := by rw [e1]; group
        _ = q₂ * x * q₂⁻¹ * S.z := by rw [e2]
    rw [e]
    rcases h₂ with h₂ | h₂
    · exact Or.inr (by rw [h₂])
    · left
      rw [h₂, mul_assoc, hzz, mul_one]

theorem conj_conj_mem (h : SigmaEnd S A V x u) {q : G} (hq : q ∈ S.QG) {b : G}
    (hb : ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = b) :
    ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = q * b * q⁻¹ := by
  obtain ⟨g, hg, rfl⟩ := hb
  exact ⟨q * g, mul_mem (h.QG_le hq) hg, by group⟩

theorem ncard_diff (h : SigmaEnd S A V x u) : ((A.E : Set G) \ V.E).ncard = 32 := by
  rw [Set.ncard_diff (fun b hb => h.V_le hb)]
  have hA : (A.E : Set G).ncard = 64 := by rw [← Nat.card_coe_set_eq]; exact h.card_A
  have hV : (V.E : Set G).ncard = 32 := by rw [← Nat.card_coe_set_eq]; exact h.card_V
  rw [hA, hV]

theorem ncard_diff_one (h : SigmaEnd S A V x u) : ((V.E : Set G) \ {1}).ncard = 31 := by
  rw [Set.ncard_diff_singleton_of_mem (one_mem V.E)]
  have hV : (V.E : Set G).ncard = 32 := by rw [← Nat.card_coe_set_eq]; exact h.card_V
  rw [hV]

theorem finrank_A (h : SigmaEnd S A V x u) : finrank (ZMod 2) (Additive A.E) = 6 := by
  have h1 := A.card_eq_two_pow_finrank
  rw [h.card_A] at h1
  exact (Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num : 64 = 2 ^ 6)))

theorem finrank_V (h : SigmaEnd S A V x u) : finrank (ZMod 2) (Additive V.E) = 5 := by
  have h1 := V.card_eq_two_pow_finrank
  rw [h.card_V] at h1
  exact (Nat.pow_right_injective le_rfl (h1.symm.trans (by norm_num : 32 = 2 ^ 5)))

theorem mem_orbit_iff (h : SigmaEnd S A V x u) (a : A.E) :
    ElemAb.vec a ∈ MulAction.orbit A.conjHom.range (ElemAb.vec (⟨S.z, h.z_mem_A⟩ : A.E)) ↔
      ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = a := by
  constructor
  · rintro ⟨⟨k, g, rfl⟩, hk⟩
    exact ⟨g, g.2, (ElemAb.conjHom_vec_eq_vec_iff g _ a).mp hk⟩
  · rintro ⟨g, hg, hga⟩
    exact ⟨⟨A.conjHom ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩, (ElemAb.conjHom_vec_eq_vec_iff ⟨g, hg⟩ _ a).mpr hga⟩

theorem false_of_forall_not_conj (h : SigmaEnd S A V x u)
    (hC : ∀ w ∈ A.E, w ∉ V.E → ¬ ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w) : False := by
  classical
  set N := normalizer (A.E : Set G) with hN
  have key : ∀ g ∈ N, ∀ v ∈ V.E, g * v * g⁻¹ ∈ V.E := by
    intro g hg v hv
    by_cases hv1 : v = 1
    · rw [hv1, mul_one, mul_inv_cancel]
      exact one_mem _
    obtain ⟨k, hk, hkv⟩ := h.exists_conj_eq hv hv1
    by_contra hn
    exact hC _ (conj_mem_A hg (h.V_le hv)) hn ⟨g * k, mul_mem hg hk, by rw [← hkv]; group⟩
  have hNV : N ≤ normalizer (V.E : Set G) := fun g hg => mem_normalizer_iff.mpr fun v =>
    ⟨key g hg v, fun hv' => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hv'⟩
  set φ : N →* (Additive V.E ≃ₗ[ZMod 2] Additive V.E) :=
    V.conjHom.comp (Subgroup.inclusion hNV) with hφ
  have hφv : ∀ (g : N) (a b : V.E),
      φ g (ElemAb.vec a) = ElemAb.vec b ↔ (g : G) * a * (g : G)⁻¹ = b :=
    fun g a b => ElemAb.conjHom_vec_eq_vec_iff (Subgroup.inclusion hNV g) a b
  set H5 := φ.range with hH5
  set zV : V.E := ⟨S.z, h.z_mem⟩ with hzV
  have hz0 : ElemAb.vec zV ≠ 0 := fun h0 => S.z_ne_one (ElemAb.vec_eq_zero_iff.mp h0)
  have hT : ∀ v w : Additive V.E, v ≠ 0 → w ≠ 0 → ∃ k ∈ H5, k v = w := by
    intro v w hv hw
    obtain ⟨v₁, rfl⟩ := ElemAb.exists_vec v
    obtain ⟨w₁, rfl⟩ := ElemAb.exists_vec w
    obtain ⟨g₁, hg₁, hv₁⟩ := h.exists_conj_eq v₁.2 fun h1 => hv (ElemAb.vec_eq_zero_iff.mpr h1)
    obtain ⟨g₂, hg₂, hw₁⟩ := h.exists_conj_eq w₁.2 fun h1 => hw (ElemAb.vec_eq_zero_iff.mpr h1)
    refine ⟨φ ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁)⟩, ⟨_, rfl⟩, ?_⟩
    rw [hφv]
    show (g₂ * g₁⁻¹) * (v₁ : G) * (g₂ * g₁⁻¹)⁻¹ = w₁
    rw [← hv₁, ← hw₁]
    group
  have htv : ∀ (f : Module.Dual (ZMod 2) (Additive V.E)) (hf : f (ElemAb.vec zV) = 0),
      LinearEquiv.transvection hf ∈ H5 := by
    intro f hf
    obtain ⟨q, hq, hqv⟩ := h.transv f hf
    refine ⟨⟨q, h.QG_le hq⟩, LinearEquiv.ext fun v => ?_⟩
    obtain ⟨v₁, rfl⟩ := ElemAb.exists_vec v
    rw [transvection_apply]
    rcases zmod_two_eq_zero_or_one (f (ElemAb.vec v₁)) with h0 | h1
    · rw [h0, zero_smul, add_zero, hφv]
      show q * (v₁ : G) * q⁻¹ = v₁
      rw [(hqv v₁).mpr h0, mul_inv_cancel_right]
    · rw [h1, one_smul, ← ElemAb.vec_mul, hφv]
      show q * (v₁ : G) * q⁻¹ = v₁ * S.z
      have hne : q * (v₁ : G) ≠ v₁ * q := fun he => by
        rw [(hqv v₁).mp he] at h1
        exact zero_ne_one h1
      rcases S.mul_comm_or hq ((h.mem_QG_iff _ (h.V_le v₁.2)).mpr v₁.2) with he | he
      · exact absurd he hne
      · calc q * (v₁ : G) * q⁻¹ = S.z * (v₁ * q) * q⁻¹ := by rw [he]
          _ = S.z * v₁ := by group
          _ = v₁ * S.z := (S.z_comm (h.A_le_M (h.V_le v₁.2))).symm
  have hcard : Nat.card H5 < 9999360 := by
    have horb : MulAction.orbit H5 (ElemAb.vec zV) = Set.univ \ {0} := by
      ext v
      simp only [MulAction.mem_orbit_iff, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
        true_and]
      constructor
      · rintro ⟨k, rfl⟩
        exact ((k : Additive V.E ≃ₗ[ZMod 2] Additive V.E).map_ne_zero_iff).mpr hz0
      · intro hv
        obtain ⟨k, hk, hkv⟩ := hT _ v hz0 hv
        exact ⟨⟨k, hk⟩, hkv⟩
    have h31 : (MulAction.orbit H5 (ElemAb.vec zV)).ncard = 31 := by
      rw [horb, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
        (Nat.card_congr Additive.toMul).trans h.card_V]
    have hmem : ∀ k ∈ MulAction.stabilizer H5 (ElemAb.vec zV),
        (k : Additive V.E ≃ₗ[ZMod 2] Additive V.E) ∈ (S.M.subgroupOf N).map φ := by
      rintro ⟨k, g, rfl⟩ hk
      refine ⟨g, ?_, rfl⟩
      have e : (g : G) * S.z * (g : G)⁻¹ = S.z := (hφv g zV zV).mp hk
      refine Subgroup.mem_subgroupOf.mpr (S.mem_M_iff.mpr ?_)
      calc (g : G) * S.z = ((g : G) * S.z * (g : G)⁻¹) * g := by group
        _ = S.z * g := by rw [e]
    have hstab : Nat.card (MulAction.stabilizer H5 (ElemAb.vec zV)) ≤
        Nat.card ((S.M.subgroupOf N).map φ) :=
      Nat.card_le_card_of_injective (fun k => ⟨((k : H5) : _), hmem k k.2⟩) fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun y : ((S.M.subgroupOf N).map φ : Subgroup _) =>
          (y : Additive V.E ≃ₗ[ZMod 2] Additive V.E)) hab))
    have hB : A.E.subgroupOf N ≤ S.M.subgroupOf N := fun g hg => h.A_le_M hg
    have hBker : A.E.subgroupOf N ≤ φ.ker := fun g hg =>
      (V.conjHom_eq_one_iff _).mpr fun v hv => A.comm g hg v (h.V_le hv)
    have h1 := card_map_mul_card_le φ hB hBker
    have hBc : Nat.card (A.E.subgroupOf N) = 64 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv, h.card_A]
    have hKM : Nat.card (S.M.subgroupOf N) ≤ Nat.card S.M :=
      Nat.card_le_card_of_injective (fun g => (⟨(g : N), g.2⟩ : S.M)) fun a b hab =>
        Subtype.ext (Subtype.ext (congrArg (fun y : S.M => (y : G)) hab))
    have e := (MulAction.stabilizer H5 (ElemAb.vec zV)).card_mul_index
    rw [MulAction.index_stabilizer, h31] at e
    rw [← e]
    have := h.card_M
    rw [hBc] at h1
    omega
  exact false_of_transitive_of_transvection_mem h.finrank_V H5 hT hz0 htv hcard

theorem false_of_exists_conj_of_exists_not_conj (h : SigmaEnd S A V x u)
    {w₁ : G} (hw₁A : w₁ ∈ A.E) (hw₁V : w₁ ∉ V.E)
    (hw₁ : ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w₁)
    {w₂ : G} (hw₂A : w₂ ∈ A.E) (hw₂V : w₂ ∉ V.E)
    (hw₂ : ¬ ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w₂) : False := by
  classical
  set P : G → Prop := fun b => ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = b with hP
  set T : Set G := (A.E : Set G) \ V.E with hT
  have hzz := S.z_mul_z
  have hTz : ∀ b ∈ T, b * S.z ∈ T := by
    rintro b ⟨hbA, hbV⟩
    refine ⟨mul_mem hbA h.z_mem_A, fun hbz => hbV ?_⟩
    have := mul_mem hbz h.z_mem
    rwa [mul_assoc, hzz, mul_one] at this
  have hnot : ∀ b ∈ T, P b → ¬ P (b * S.z) := by
    intro b hb hPb hPbz
    obtain ⟨q, hq, hq'⟩ := h.exists_conj_eq_or (hTz b hb).1 (hTz b hb).2 hw₂A hw₂V
    rcases hq' with hq' | hq'
    · exact hw₂ (hq' ▸ h.conj_conj_mem hq hPbz)
    · apply hw₂
      have e : q * b * q⁻¹ = w₂ := by
        have e1 : q * (b * S.z) * q⁻¹ = q * b * q⁻¹ * S.z := by
          rw [show q * (b * S.z) * q⁻¹ = q * b * q⁻¹ * (q * S.z * q⁻¹) by group,
            S.z_comm (S.QG_le_M hq), mul_inv_cancel_right]
        rw [e1] at hq'
        exact mul_right_cancel hq'
      exact e ▸ h.conj_conj_mem hq hPb
  have hor : ∀ b ∈ T, P b ∨ P (b * S.z) := by
    rintro b ⟨hbA, hbV⟩
    obtain ⟨q, hq, hq'⟩ := h.exists_conj_eq_or hw₁A hw₁V hbA hbV
    rcases hq' with hq' | hq'
    · exact Or.inl (hq' ▸ h.conj_conj_mem hq hw₁)
    · exact Or.inr (hq' ▸ h.conj_conj_mem hq hw₁)
  have himg : (fun b => b * S.z) '' (T ∩ {b | P b}) = T \ {b | P b} := by
    ext c
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨b, ⟨hbT, hPb⟩, rfl⟩
      exact ⟨hTz b hbT, hnot b hbT hPb⟩
    · rintro ⟨hcT, hPc⟩
      refine ⟨c * S.z, ⟨hTz c hcT, ?_⟩, by rw [mul_assoc, hzz, mul_one]⟩
      rcases hor (c * S.z) (hTz c hcT) with h1 | h1
      · exact h1
      · rw [mul_assoc, hzz, mul_one] at h1
        exact absurd h1 hPc
  have h16 : (T ∩ {b | P b}).ncard = 16 := by
    have e1 := Set.ncard_inter_add_ncard_diff_eq_ncard T {b | P b} (Set.toFinite T)
    rw [← himg, Set.ncard_image_of_injective _ (mul_left_injective S.z), h.ncard_diff] at e1
    omega
  have hO : {b | P b} = ((V.E : Set G) \ {1}) ∪ (T ∩ {b | P b}) := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_inter_iff, SetLike.mem_coe]
    constructor
    · intro hPb
      have hbA : b ∈ A.E := by
        obtain ⟨g, hg, rfl⟩ := hPb
        exact h.conj_z_mem_A hg
      have hb1 : b ≠ 1 := by
        obtain ⟨g, hg, rfl⟩ := hPb
        exact conj_z_ne_one g
      by_cases hbV : b ∈ V.E
      · exact Or.inl ⟨hbV, hb1⟩
      · exact Or.inr ⟨⟨hbA, hbV⟩, hPb⟩
    · rintro (⟨hbV, hb1⟩ | ⟨-, hPb⟩)
      · exact h.exists_conj_eq hbV hb1
      · exact hPb
  have hdisj : Disjoint ((V.E : Set G) \ {1}) (T ∩ {b | P b}) := by
    rw [Set.disjoint_left]
    rintro b ⟨hbV, -⟩ ⟨⟨-, hbV'⟩, -⟩
    exact hbV' hbV
  have h47 : ({b | P b} : Set G).ncard = 47 := by
    rw [hO, Set.ncard_union_eq hdisj, h.ncard_diff_one, h16]
  set zA : A.E := ⟨S.z, h.z_mem_A⟩ with hzA
  set H := A.conjHom.range with hH
  have horb : (fun a : Additive A.E => ((Additive.toMul a : A.E) : G)) ''
      MulAction.orbit H (ElemAb.vec zA) = {b | P b} := by
    ext b
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨a', rfl⟩ := ElemAb.exists_vec a
      exact (h.mem_orbit_iff a').mp ha
    · intro hPb
      have hbA : b ∈ A.E := by
        obtain ⟨g, hg, rfl⟩ := hPb
        exact h.conj_z_mem_A hg
      exact ⟨ElemAb.vec ⟨b, hbA⟩, (h.mem_orbit_iff ⟨b, hbA⟩).mpr hPb, rfl⟩
  have hinj : Function.Injective (fun a : Additive A.E => ((Additive.toMul a : A.E) : G)) :=
    fun a b hab => Additive.toMul.injective (Subtype.ext hab)
  have hcard : (MulAction.orbit H (ElemAb.vec zA)).ncard = 47 := by
    rw [← Set.ncard_image_of_injective _ hinj, horb, h47]
  have hdvd : 47 ∣ Nat.card H := by
    have e := (MulAction.stabilizer H (ElemAb.vec zA)).card_mul_index
    rw [MulAction.index_stabilizer, hcard] at e
    exact ⟨_, by rw [← e, mul_comm]⟩
  exact not_dvd_card_of_finrank_eq_six h.finrank_A H hdvd

theorem exists_ind (h : SigmaEnd S A V x u) :
    ∃ l : Additive A.E →ₗ[ZMod 2] ZMod 2, ∀ a : A.E, l (ElemAb.vec a) = 0 ↔ (a : G) ∈ V.E := by
  classical
  let f : Additive A.E →+ ZMod 2 :=
    { toFun := fun a => if ((Additive.toMul a : A.E) : G) ∈ V.E then 0 else 1
      map_zero' := by simp
      map_add' := fun a b => by
        have key := Subgroup.mul_mem_iff_of_index_two h.index_eq_two
          (a := Additive.toMul a) (b := Additive.toMul b)
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
        simp only [toMul_add, Subgroup.coe_mul, key]
        by_cases ha : ((Additive.toMul a : A.E) : G) ∈ V.E <;>
          by_cases hb : ((Additive.toMul b : A.E) : G) ∈ V.E <;>
          simp only [ha, hb, iff_self, iff_true, true_iff, iff_false, false_iff, not_true_eq_false,
            not_false_eq_true, ite_true, ite_false] <;> decide }
  refine ⟨f.toZModLinearMap 2, fun a => ?_⟩
  show (if ((a : A.E) : G) ∈ V.E then (0 : ZMod 2) else 1) = 0 ↔ _
  split_ifs with ha
  · exact iff_of_true rfl ha
  · exact iff_of_false one_ne_zero ha

theorem false_of_forall_conj (h : SigmaEnd S A V x u)
    (hC : ∀ w ∈ A.E, w ∉ V.E → ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w) : False := by
  classical
  set N := normalizer (A.E : Set G) with hN
  set ι : Additive A.E → G := fun a => ((Additive.toMul a : A.E) : G) with hι
  have hιA : ∀ a, ι a ∈ A.E := fun a => (Additive.toMul a).2
  have hιinj : Function.Injective ι := fun a b hab => Additive.toMul.injective (Subtype.ext hab)
  have hι0 : ∀ a, ι a = 1 ↔ a = 0 := fun a =>
    ⟨fun h1 => ElemAb.vec_eq_zero_iff.mpr h1, fun h0 => by rw [h0]; rfl⟩
  have hP : ∀ a : Additive A.E, ∃ g : G, g ∈ N ∧ (a ≠ 0 → g * S.z * g⁻¹ = ι a) := by
    intro a
    by_cases ha : a = 0
    · exact ⟨1, one_mem _, fun h' => absurd ha h'⟩
    · have ha1 : ι a ≠ 1 := fun h1 => ha ((hι0 a).mp h1)
      by_cases haV : ι a ∈ V.E
      · obtain ⟨g, hg, e⟩ := h.exists_conj_eq haV ha1
        exact ⟨g, hg, fun _ => e⟩
      · obtain ⟨g, hg, e⟩ := hC _ (hιA a) haV
        exact ⟨g, hg, fun _ => e⟩
  choose gs hgsN hgs using hP
  obtain ⟨l, hl⟩ := h.exists_ind
  set f : Additive A.E → Additive A.E →ₗ[ZMod 2] ZMod 2 := fun a =>
    if a = 0 then 0 else l ∘ₗ (A.conjLin ⟨(gs a)⁻¹, inv_mem (hgsN a)⟩).toLinearMap with hf
  have hf0 : ∀ a c, a ≠ 0 → (f a c = 0 ↔ ι c ∈ S.Qa (gs a)) := by
    intro a c ha
    obtain ⟨c', rfl⟩ := ElemAb.exists_vec c
    have e1 : f a (ElemAb.vec c') =
        l (ElemAb.vec (A.conjMulEquiv ⟨(gs a)⁻¹, inv_mem (hgsN a)⟩ c')) := by
      rw [hf]
      dsimp only
      rw [if_neg ha]
      rfl
    have hmem : (gs a)⁻¹ * (c' : G) * gs a ∈ A.E := by
      have := conj_mem_A (inv_mem (hgsN a)) c'.2
      rwa [inv_inv] at this
    rw [e1, hl, ElemAb.coe_conjMulEquiv, mem_Qa_iff']
    show (gs a)⁻¹ * (c' : G) * (gs a)⁻¹⁻¹ ∈ V.E ↔ (gs a)⁻¹ * (c' : G) * gs a ∈ S.QG
    rw [inv_inv]
    exact (h.mem_QG_iff _ hmem).symm
  have hfz : ∀ c, f 0 c = 0 := fun c => by simp [hf]
  have hfz' : ∀ a, f a 0 = 0 := fun a => map_zero _
  have hsym : ∀ a c, f a c = f c a := by
    intro a c
    by_cases ha : a = 0
    · rw [ha, hfz, hfz']
    by_cases hc : c = 0
    · rw [hc, hfz, hfz']
    by_cases hac : a = c
    · rw [hac]
    refine zmod2_eq_of_iff ((hf0 a c ha).trans (Iff.trans ?_ (hf0 c a hc).symm))
    have hne : gs c * S.z * (gs c)⁻¹ ≠ gs a * S.z * (gs a)⁻¹ := by
      rw [hgs c hc, hgs a ha]
      exact fun e => hac (hιinj e).symm
    rw [← hgs c hc, ← hgs a ha]
    exact ⟨fun h1 => S.mem_Qa_symm hne h1, fun h1 => S.mem_Qa_symm hne.symm h1⟩
  obtain ⟨β, hβ⟩ := exists_bilin_of_symm f hsym
  have hβ0 : ∀ a c, a ≠ 0 → (β a c = 0 ↔ ι c ∈ S.Qa (gs a)) := fun a c ha => by
    rw [hβ]
    exact hf0 a c ha
  have hβalt : β.IsAlt := by
    intro a
    by_cases ha : a = 0
    · simp only [ha, map_zero, LinearMap.zero_apply]
    · rw [hβ0 a a ha, ← hgs a ha]
      exact (S.conjBy (gs a)).z_mem_QG
  have hsep : ∀ a, (∀ c, β a c = 0) → a = 0 := by
    intro a hac
    by_contra ha
    have hc : gs a * x * (gs a)⁻¹ ∈ A.E := conj_mem_A (hgsN a) h.x_mem
    have h1 := (hβ0 a (ElemAb.vec ⟨_, hc⟩) ha).mp (hac _)
    rw [mem_Qa_iff'] at h1
    have h2 : (gs a)⁻¹ * (gs a * x * (gs a)⁻¹) * gs a = x := by group
    rw [show ι (ElemAb.vec ⟨_, hc⟩) = gs a * x * (gs a)⁻¹ from rfl, h2] at h1
    exact h.x_not_mem ((h.mem_QG_iff x h.x_mem).mp h1)
  have hnd : β.Nondegenerate := by
    refine ⟨hsep, fun c hc => hsep c fun a => ?_⟩
    rw [hβ, hsym, ← hβ]
    exact hc a
  set zA : A.E := ⟨S.z, h.z_mem_A⟩ with hzA
  set xA : A.E := ⟨x, h.x_mem⟩ with hxA
  have hz0 : ElemAb.vec zA ≠ 0 := fun h0 => S.z_ne_one (ElemAb.vec_eq_zero_iff.mp h0)
  have hQz : S.Qa (gs (ElemAb.vec zA)) = S.QG := Setting.Qa_eq_QG_of_conj_eq S (hgs _ hz0)
  have hperp : ∀ c, β (ElemAb.vec zA) c = 0 ↔ ι c ∈ V.E := fun c => by
    rw [hβ0 _ c hz0, hQz]
    exact h.mem_QG_iff _ (hιA c)
  have hx₀ : β (ElemAb.vec zA) (ElemAb.vec xA) = 1 :=
    zmod_two_eq_one_of_ne_zero fun h0 => h.x_not_mem ((hperp _).mp h0)
  have hinv : ∀ (g : N) (a c : Additive A.E), β (A.conjHom g a) (A.conjHom g c) = β a c := by
    intro g a c
    by_cases ha : a = 0
    · simp only [ha, map_zero, LinearMap.zero_apply]
    have hga : A.conjHom g a ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr ha
    refine zmod2_eq_of_iff ((hβ0 _ _ hga).trans (Iff.trans ?_ (hβ0 a c ha).symm))
    have hgs' : S.Qa (gs (A.conjHom g a)) = S.Qa ((g : G) * gs a) := by
      refine Setting.Qa_eq_of_conj_eq S ?_
      rw [hgs _ hga, show ι (A.conjHom g a) = (g : G) * ι a * (g : G)⁻¹ from rfl, ← hgs a ha]
      group
    rw [hgs', mem_Qa_iff', mem_Qa_iff',
      show ι (A.conjHom g c) = (g : G) * ι c * (g : G)⁻¹ from rfl]
    rw [show ((g : G) * gs a)⁻¹ * ((g : G) * ι c * (g : G)⁻¹) * ((g : G) * gs a) =
      (gs a)⁻¹ * ι c * gs a by group]
  set Hz := (S.M.subgroupOf N).map A.conjHom with hHz
  set Qh := (S.QG.subgroupOf N).map A.conjHom with hQh
  have hzfix : ∀ g : N, (g : G) ∈ S.M → A.conjHom g (ElemAb.vec zA) = ElemAb.vec zA := by
    intro g hg
    rw [ElemAb.conjHom_vec_eq_vec_iff]
    show (g : G) * S.z * (g : G)⁻¹ = S.z
    rw [S.z_comm hg, mul_inv_cancel_right]
  have hHβ : ∀ k ∈ Hz, ∀ a b : Additive A.E, β (k a) (k b) = β a b := by
    rintro _ ⟨g, -, rfl⟩ a b
    exact hinv g a b
  have hHzz : ∀ k ∈ Hz, k (ElemAb.vec zA) = ElemAb.vec zA := by
    rintro _ ⟨g, hg, rfl⟩
    exact hzfix g hg
  have hQH : Qh ≤ Hz := Subgroup.map_mono fun g hg => S.QG_le_M hg
  have hQn : ∀ k ∈ Hz, ∀ q ∈ Qh, k * q * k⁻¹ ∈ Qh := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨q, hq, rfl⟩
    refine ⟨g * q * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact S.conj_mem_QG hg hq
  have hQ1 : ∀ q ∈ Qh, ∀ v : Additive A.E, β (ElemAb.vec zA) v = 0 →
      q v - v ∈ (ZMod 2) ∙ ElemAb.vec zA := by
    rintro _ ⟨q, hq, rfl⟩ v hv
    have hq' : (q : G) ∈ S.QG := hq
    obtain ⟨v₁, rfl⟩ := ElemAb.exists_vec v
    have hv₁ : (v₁ : G) ∈ S.QG := (h.mem_QG_iff _ v₁.2).mpr ((hperp _).mp hv)
    rw [mem_span_singleton_iff_two]
    rcases S.mul_comm_or hq' hv₁ with he | he
    · left
      have e : A.conjHom q (ElemAb.vec v₁) = ElemAb.vec v₁ := by
        rw [ElemAb.conjHom_vec_eq_vec_iff, he, mul_inv_cancel_right]
      rw [e, sub_self]
    · right
      have e : A.conjHom q (ElemAb.vec v₁) = ElemAb.vec (zA * v₁) := by
        rw [ElemAb.conjHom_vec_eq_vec_iff, he]
        show S.z * ((v₁ : G) * q) * (q : G)⁻¹ = S.z * v₁
        rw [← mul_assoc S.z, mul_inv_cancel_right]
      rw [e, ElemAb.vec_mul, add_sub_cancel_right]
  have hQsurj : ∀ w : Additive A.E, β (ElemAb.vec zA) w = 0 →
      ∃ q ∈ Qh, q (ElemAb.vec xA) - ElemAb.vec xA - w ∈ (ZMod 2) ∙ ElemAb.vec zA := by
    intro w hw
    obtain ⟨w₁, rfl⟩ := ElemAb.exists_vec w
    obtain ⟨q, hq, hq'⟩ := h.surj _ ((hperp _).mp hw)
    refine ⟨A.conjHom ⟨q, h.QG_le hq⟩, ⟨⟨q, h.QG_le hq⟩, hq, rfl⟩, ?_⟩
    rw [mem_span_singleton_iff_two]
    rcases hq' with hq' | hq'
    · left
      have e : A.conjHom ⟨q, h.QG_le hq⟩ (ElemAb.vec xA) = ElemAb.vec (xA * w₁) := by
        rw [ElemAb.conjHom_vec_eq_vec_iff]
        exact hq'
      rw [e, ElemAb.vec_mul]
      abel
    · right
      have e : A.conjHom ⟨q, h.QG_le hq⟩ (ElemAb.vec xA) = ElemAb.vec (xA * w₁ * zA) := by
        rw [ElemAb.conjHom_vec_eq_vec_iff]
        exact hq'
      rw [e, ElemAb.vec_mul, ElemAb.vec_mul]
      abel
  have hQt : ∀ q ∈ Qh, (∀ v : Additive A.E, β (ElemAb.vec zA) v = 0 → q v = v) → q = 1 := by
    rintro _ ⟨q, hq, rfl⟩ hfix
    have hqV : (q : G) ∈ V.E := by
      refine h.cent_le _ hq fun v hv => ?_
      have hvA := h.V_le hv
      have e := hfix (ElemAb.vec ⟨v, hvA⟩) ((hperp _).mpr hv)
      rw [ElemAb.conjHom_vec_eq_vec_iff] at e
      calc (q : G) * v = (q : G) * v * (q : G)⁻¹ * q := by group
        _ = v * q := by rw [e]
    exact (A.conjHom_eq_one_iff q).mpr fun b hb => A.comm _ (h.V_le hqV) b hb
  obtain ⟨v, w, hvz, hwz, hv, hw, hvw⟩ := exists_not_transitive_of_radical β hβalt hnd
    h.finrank_A hz0 hx₀ Hz hHβ hHzz Qh hQH hQn hQ1 hQsurj hQt
  obtain ⟨v₁, rfl⟩ := ElemAb.exists_vec v
  obtain ⟨w₁, rfl⟩ := ElemAb.exists_vec w
  rw [mem_span_singleton_iff_two, not_or] at hv hw
  have hv1 : (v₁ : G) ≠ 1 := fun e => hv.1 (ElemAb.vec_eq_zero_iff.mpr e)
  have hw1 : (w₁ : G) ≠ 1 := fun e => hw.1 (ElemAb.vec_eq_zero_iff.mpr e)
  have hvzz : (v₁ : G) ≠ S.z := fun e => hv.2 (ElemAb.vec_eq_vec_iff.mpr e)
  have hwzz : (w₁ : G) ≠ S.z := fun e => hw.2 (ElemAb.vec_eq_vec_iff.mpr e)
  obtain ⟨g, hgN, hgM, hg⟩ :=
    h.trans _ ((hperp _).mp hvz) _ ((hperp _).mp hwz) hv1 hvzz hw1 hwzz
  refine hvw (A.conjHom ⟨g, hgN⟩) ⟨⟨g, hgN⟩, hgM, rfl⟩ ?_
  rw [(ElemAb.conjHom_vec_eq_vec_iff ⟨g, hgN⟩ v₁ w₁).mpr hg, sub_self]
  exact Submodule.zero_mem _

theorem false (h : SigmaEnd S A V x u) : False := by
  by_cases h1 : ∀ w ∈ A.E, w ∉ V.E → ¬ ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w
  · exact h.false_of_forall_not_conj h1
  by_cases h2 : ∀ w ∈ A.E, w ∉ V.E → ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w
  · exact h.false_of_forall_conj h2
  obtain ⟨w₁, hw₁A, hw₁V, hw₁⟩ :
      ∃ w ∈ A.E, w ∉ V.E ∧ ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w := by
    by_contra hc
    exact h1 fun w hwA hwV hPw => hc ⟨w, hwA, hwV, hPw⟩
  obtain ⟨w₂, hw₂A, hw₂V, hw₂⟩ :
      ∃ w ∈ A.E, w ∉ V.E ∧ ¬ ∃ g ∈ normalizer (A.E : Set G), g * S.z * g⁻¹ = w := by
    by_contra hc
    exact h2 fun w hwA hwV => by_contra fun hPw => hc ⟨w, hwA, hwV, hPw⟩
  exact h.false_of_exists_conj_of_exists_not_conj hw₁A hw₁V hw₁ hw₂A hw₂V hw₂

end SigmaEnd

end CFSG.GF2Type.Smith1980Orth.W4Sigma
