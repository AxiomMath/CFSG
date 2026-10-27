module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.GlueLib
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

@[expose] def SDp {G : Type} [Group G] (Y : Subgroup G) : Prop := ∃ n, IVK.IsSemidihedralTwoGroup ↥Y n

section Std

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

namespace Std4

theorem comp_rigid (h : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    IsRigidRankOneComp z K := by
  have : K ∈ {K | IsRigidRankOneComp z K} := by
    rw [h.comps]
    rcases hK with rfl | rfl <;> simp
  exact this

theorem comp_isPCompIn (h : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    IsPCompIn 2 (centralizer ({z} : Set G)) K :=
  (h.comp_rigid hK).1.1.2.2

theorem comp_pRank (h : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    pRank 2 ↥K = 1 :=
  (h.comp_rigid hK).2

theorem orderOf_z (h : Std4 G z S K₁ K₂) : orderOf z = 2 := h.classical.1

theorem swap (h : Std4 G z S K₁ K₂) : Std4 G z S K₂ K₁ :=
  ⟨h.simple, h.rank, h.rank_le, h.gen4, h.classical, h.thm2, h.sylow, by rw [h.comps]; exact Set.pair_comm _ _,
    h.ne.symm, h.kgh⟩

theorem rigidProduct_eq (h : Std4 G z S K₁ K₂) : rigidProduct z = K₁ ⊔ K₂ :=
  CFSG.GH74.GLS.Stage1.Thm3.Sec4.rigidProduct_eq h.comps

end Std4

theorem Pz_eq (h : Std4 G z S K₁ K₂) : Pz S z = M.Pm S K₁ K₂ := by
  unfold Pz M.Pm
  rw [h.rigidProduct_eq]

theorem Qz_eq (h : Std4 G z S K₁ K₂) : Qz S z = M.Qm (pPrimeCoreOf 2) S K₁ K₂ := by
  unfold Qz rigidSectionCentralizer M.Qm
  rw [h.rigidProduct_eq]
  rfl

theorem Rz_eq (h : Std4 G z S K₁ K₂) : Rz S z = M.Rm (pPrimeCoreOf 2) S K₁ K₂ := by
  unfold Rz M.Rm
  rw [Pz_eq h, Qz_eq h]

theorem hyp4A_iff (h : Std4 G z S K₁ K₂) : Hyp4A S z ↔ M.H4A (pPrimeCoreOf 2) z S K₁ K₂ := by
  unfold Hyp4A M.H4A
  rw [Rz_eq h]

omit [Finite G] in
theorem interchanges_iff (t : G) : Interchanges t K₁ K₂ ↔ M.Intch t K₁ K₂ := by
  unfold Interchanges M.Intch
  rw [← cj_eq_conjugate, ← cj_eq_conjugate]

theorem m4_of_std (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) :
    M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ := by
  have hz2 : orderOf z = 2 := h.orderOf_z
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  have hrp : rigidProduct z = K₁ ⊔ K₂ := h.rigidProduct_eq
  have hsyl : M.Syl2In S (centralizer ({z} : Set G)) := syl2In_of_isSylowOf h.sylow
  have hpc₁ := h.comp_isPCompIn (Or.inl rfl)
  have hpc₂ := h.comp_isPCompIn (Or.inr rfl)
  refine
    { z_sq := mul_self_eq_one_of_orderOf_eq_two hz2
      z_ne := ne_one_of_orderOf_eq_two hz2
      S_syl := hsyl
      S_top := sTop_of_clause_d hsyl hcl.2.2.2.1
      K₁_le := hpc₁.1
      K₂_le := hpc₂.1
      cs₁ := fun x hx => le_cSec_of_ne hpc₂ hpc₁ h.ne.symm hx
      cs₂ := fun x hx => le_cSec_of_ne hpc₁ hpc₂ h.ne hx
      perm := ?_
      core := fun K _ => isOddCore_pPrimeCoreOf K
      coreK := isOddCore_pPrimeCoreOf _
      nonab := fun K hK => nonab_of_isPCompIn (h.comp_isPCompIn hK)
      rk := fun K hK => rk1_of_pRank_one (h.comp_pRank hK)
      zs := fun K hK => hII G h.simple z hz2 S K h.sylow (h.comp_isPCompIn hK) (h.comp_pRank hK)
      hb := ?_
      hc := ?_
      he := ?_ }
  · intro c hc
    have hA : M.cj K₁ c ∈ ({K₁, K₂} : Set (Subgroup G)) := by
      rw [← h.comps]
      show IsRigidRankOneComp z (M.cj K₁ c)
      rw [cj_eq_conjugate]
      exact isRigidRankOneComp_cmap (h.comp_rigid (Or.inl rfl)) (inv_mem hc)
    have hB : M.cj K₂ c ∈ ({K₁, K₂} : Set (Subgroup G)) := by
      rw [← h.comps]
      show IsRigidRankOneComp z (M.cj K₂ c)
      rw [cj_eq_conjugate]
      exact isRigidRankOneComp_cmap (h.comp_rigid (Or.inr rfl)) (inv_mem hc)
    have hinj : M.cj K₁ c ≠ M.cj K₂ c := fun he => h.ne (by
      have := congrArg (fun H => M.cj H c⁻¹) he
      simpa [M.cj_cj_inv] using this)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (hA.trans hB.symm) hinj
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hB⟩
    · exact absurd (hA.trans hB.symm) hinj
  · have hb := hcl.2.1
    rw [hrp] at hb
    exact syl2In_of_isSylowOf hb
  · intro t htC htz htn K hK
    have hn : t ∉ zStar (rigidProduct z) := by rw [hrp]; exact htn
    exact rk1_of_pRank_one ((h.classical.2 t htC htz hn).2.2.1 K (h.comp_rigid hK))
  · intro t htC htz htn K hK
    have hn : t ∉ zStar (rigidProduct z) := by rw [hrp]; exact htn
    exact (h.classical.2 t htC htz hn).2.2.2.2.1 K (h.comp_rigid hK)

theorem m42_of_std (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted) (h : Std4 G z S K₁ K₂) :
    M.M42 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ :=
  ⟨m4_of_std hII h, h31 G z S K₁ K₂ h⟩

theorem intrinsic_of_comp (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂)
    (h : Std4 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : IsIntrinsic z K :=
  ⟨h.comp_isPCompIn hK, h.comp_pRank hK, hM.z_mem_comp hK⟩

theorem isIntrinsic_cj {t g : G} (hg : g⁻¹ * z * g = t) {K : Subgroup G} (hK : IsIntrinsic z K) :
    IsIntrinsic t (M.cj K g) := by
  have h1 := isIntrinsic_map_conj hK g⁻¹
  have e : g⁻¹ * z * g⁻¹⁻¹ = t := by rw [← hg, inv_inv]
  rw [e] at h1
  rw [cj_eq_conjugate]
  exact h1

theorem orderOf_conj_z (h : Std4 G z S K₁ K₂) {t g : G} (hg : g⁻¹ * z * g = t) : orderOf t = 2 := by
  have e : g⁻¹ * z * g⁻¹⁻¹ = t := by rw [← hg, inv_inv]
  rw [← e, orderOf_conj_eq]
  exact h.orderOf_z

theorem rec1b_of_std (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h : Std4 G z S K₁ K₂) :
    ∀ t g : G, g⁻¹ * z * g = t → t ∈ centralizer ({z} : Set G) →
      ∀ J L, (J = K₁ ∨ J = K₂) → (L = K₁ ∨ L = K₂) → t ∈ normalizer (J : Set G) →
        ∀ a ∈ J, IsPGroup 2 (zpowers a) → a ∉ zpowers z → a * t = t * a →
          a ∈ normalizer (M.cj L g : Set G) := by
  intro t g hg htC J L hJ hL htJ a haJ ha2 haz hat
  have hM := m4_of_std hII h
  exact (hrec G h.simple t z (orderOf_conj_z h hg) h.orderOf_z (M.centralizer_comm htC)
    (M.cj L g) J (isIntrinsic_cj hg (intrinsic_of_comp hM h hL)) (intrinsic_of_comp hM h hJ)).2
      htJ a haJ ha2 haz hat

theorem rec2_of_std (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h : Std4 G z S K₁ K₂) :
    ∀ t g : G, g⁻¹ * z * g = t → t ∈ centralizer ({z} : Set G) →
      ∀ J L, (J = K₁ ∨ J = K₂) → (L = K₁ ∨ L = K₂) → z ∈ normalizer (M.cj J g : Set G) →
        t ∈ normalizer (L : Set G) := by
  intro t g hg htC J L hJ hL hzJ
  have hM := m4_of_std hII h
  exact (hrec G h.simple z t h.orderOf_z (orderOf_conj_z h hg) (M.centralizer_comm htC).symm
    L (M.cj J g) (intrinsic_of_comp hM h hL) (isIntrinsic_cj hg (intrinsic_of_comp hM h hJ))).1 hzJ

theorem f19_pz (h19 : IVK_1_9_lifted) (h : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) :
    ∀ t ∈ S, orderOf t = 2 → t ∈ normalizer (K : Set G) → ¬ InducesFAut t K →
      (∃ n, IVK.IsSemidihedralTwoGroup ↥(Pz S z ⊓ K ⊔ zpowers t) n) ∨
        ∃ u ∈ K, t * u = u * t ∧ 4 ≤ orderOf u ∧ 2 * orderOf u = Nat.card ↥(Pz S z ⊓ K) := by
  rcases hK with rfl | rfl
  · exact h19 G z S _ _ h
  · exact h19 G z S _ _ h.swap

theorem m43_of_std (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h19 : IVK_1_9_lifted)
    (h12 : IVK_1_2f_lifted) (h : Std4 G z S K₁ K₂) :
    M.M43 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ :=
  ⟨m4_of_std hII h, rec1b_of_std hII hrec h,
    fun K hK t htS ho htn hFA => by
      have := f19_pz h19 h hK t htS ho htn hFA
      rwa [Pz_eq h] at this,
    fun K hK y hy hyn hy2 hFA =>
      h12 G z S K₁ K₂ h K (by rcases hK with rfl | rfl <;> simp) y hy hyn hy2 hFA⟩

theorem m44_of_std (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h19 : IVK_1_9_lifted)
    (h12 : IVK_1_2f_lifted) (hsd : SD_involution_fusion) (h : Std4 G z S K₁ K₂) :
    M.M44 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ :=
  ⟨m43_of_std hII hrec h19 h12 h, fun P t hP hzP hcz huniq ht2 htP htn hSD =>
    hsd G P z t hP hzP (mul_self_eq_one_of_orderOf_eq_two h.orderOf_z)
      (ne_one_of_orderOf_eq_two h.orderOf_z) hcz huniq ht2 htP htn hSD⟩

theorem m45_of_std (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted) (hrec : Bg.B_reciprocity)
    (hbal : L45_balance_step) (h : Std4 G z S K₁ K₂) :
    M.M45 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂ :=
  ⟨m42_of_std hII h31 h, rec2_of_std hII hrec h,
    fun hA t htS htz htne hI u₁ hu₁ hu₁S hsq =>
      hbal G z S K₁ K₂ h ((hyp4A_iff h).2 hA) t htS htz htne ((interchanges_iff t).2 hI) u₁ hu₁ hu₁S hsq⟩

end Std

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
