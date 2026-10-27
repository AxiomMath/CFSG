module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Prop66
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Quat
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec6.R2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem quat_Q (hII : II4_4_4_center) (hq : II4_4_quat) (hQN : Quat_normal_index)
    (h : Std4 G z S K₁ K₂) (hb : Cond6b S K₁) :
    (∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K₁) n) ∧ (Pof S K₂).relIndex (Qof S K₁) ≤ 2 := by
  have hM := m4_of_std hII h
  have hP₂q : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K₂) n :=
    hq G h.simple z h.orderOf_z S K₂ h.sylow (h.comp_isPCompIn (Or.inr rfl)) (h.comp_pRank (Or.inr rfl))
  have hP₂Q : Pof S K₂ ≤ Qof S K₁ := Pof_le_Qof hM (Or.inr ⟨rfl, rfl⟩)
  have hQp : IsPGroup 2 ↥(Qof S K₁) := hM.S_pgroup.to_le (show Qof S K₁ ≤ S from inf_le_left)
  have hnc : ¬ IsCyclic ↥(Qof S K₁) := by
    intro hc
    obtain ⟨n, hn⟩ := hP₂q
    obtain ⟨a, b, hab⟩ := quat_noncomm_group hn
    apply hab
    have := comm_of_isCyclic hc ⟨a, hP₂Q a.2⟩ ⟨b, hP₂Q b.2⟩
    have e : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val this
    exact Subtype.ext e
  have hquat : ∃ n, IVK.IsQuaternionTwoGroup ↥(Qof S K₁) n :=
    quat_of_unique_invol hQp (fun a ha ha2 ha1 =>
      eq_z_of_mem_Qof hM (Or.inl rfl) hb h.orderOf_z ha (orderOf_eq_two_of_mul_self_eq_one ha2 ha1)) hnc
  refine ⟨hquat, ?_⟩
  refine hQN G (Qof S K₁) (Pof S K₂) hP₂Q ?_ hquat hP₂q
  intro x hx y hy
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx.1
  have hxN₁ : x ∈ normalizer (K₁ : Set G) := hx.2.1
  have hxN₂ : x ∈ normalizer (K₂ : Set G) := (normalizer_iff hM h.ne hxC).1 hxN₁
  refine ⟨S.mul_mem (S.mul_mem hx.1 hy.1) (S.inv_mem hx.1), ?_⟩
  exact (Subgroup.mem_normalizer_iff.1 hxN₂ y).1 hy.2

theorem S1_swap (hII : II4_4_4_center) (h : Std4 G z S K₁ K₂) : S1 S K₂ = S1 S K₁ := by
  have hM := m4_of_std hII h
  ext x
  constructor
  · rintro ⟨hxS, hx⟩
    exact ⟨hxS, (normalizer_iff hM h.ne (hM.S_syl.1 hxS)).2 hx⟩
  · rintro ⟨hxS, hx⟩
    exact ⟨hxS, (normalizer_iff hM h.ne (hM.S_syl.1 hxS)).1 hx⟩

theorem Std4.toStd6' (h : Std4 G z S K₁ K₂) : Std6 G z S :=
  ⟨h.simple, h.rank, h.rank_le, h.gen4, h.classical, h.thm2, h.sylow, h.kgh⟩

theorem prop_6_6 (hII : II4_4_4_center) (hq : II4_4_quat) (hQN : Quat_normal_index)
    (h4hij : IVK_1_4hij_outer) (h41 : Prop4_1) : Prop6_6 := by
  intro G _ _ z S K₁ K₂ h ha₁ ha₂ hb₁ hb₂
  have hM := m4_of_std hII h
  have hM' := m4_of_std hII h.swap
  have hr₁ : IsRigidRankOneComp z K₁ := h.comp_rigid (Or.inl rfl)
  have hr₂ : IsRigidRankOneComp z K₂ := h.comp_rigid (Or.inr rfl)
  have h6 : Std6 G z S := Std4.toStd6' h
  obtain ⟨hQ₁, hi₁⟩ := quat_Q hII hq hQN h hb₁
  obtain ⟨hQ₂, hi₂⟩ := quat_Q hII hq hQN h.swap hb₂
  have hS1eq : S1 S K₂ = S1 S K₁ := S1_swap hII h
  obtain ⟨hidx₁, -, hdih₁⟩ := h4hij G z S h6 K₁ hr₁ (fun s hs hfa => ha₁ s hs.1 hfa)
  obtain ⟨hidx₂, -, hdih₂⟩ := h4hij G z S h6 K₂ hr₂ (fun s hs hfa => ha₂ s hs.1 hfa)
  rw [hS1eq] at hidx₂ hdih₂
  have hPX₁ : (Pz S z).relIndex (Pof S K₁ ⊔ Qof S K₁) ≤ 2 := by
    rw [Pz_eq h]; exact Pm_relIndex_X hM hi₁
  have hPX₂ : (Pz S z).relIndex (Pof S K₂ ⊔ Qof S K₂) ≤ 2 := by
    rw [Pz_eq h, show M.Pm S K₁ K₂ = M.Pm S K₂ K₁ by
      unfold M.Pm; rw [sup_comm]]
    exact Pm_relIndex_X hM' hi₂
  have hPle₁ : Pz S z ≤ Pof S K₁ ⊔ Qof S K₁ := by
    rw [Pz_eq h]; exact Pz_le_X hM
  have hPle₂ : Pz S z ≤ Pof S K₂ ⊔ Qof S K₂ := by
    rw [Pz_eq h, show M.Pm S K₁ K₂ = M.Pm S K₂ K₁ by
      unfold M.Pm; rw [sup_comm]]
    exact Pz_le_X hM'
  have hXle₁ : Pof S K₁ ⊔ Qof S K₁ ≤ S1 S K₁ := Pof_Qof_le_S1
  have hXle₂ : Pof S K₂ ⊔ Qof S K₂ ≤ S1 S K₁ := hS1eq ▸ Pof_Qof_le_S1
  have hm₁ := Subgroup.relIndex_mul_relIndex (Pz S z) (Pof S K₁ ⊔ Qof S K₁) (S1 S K₁) hPle₁ hXle₁
  have hm₂ := Subgroup.relIndex_mul_relIndex (Pz S z) (Pof S K₂ ⊔ Qof S K₂) (S1 S K₁) hPle₂ hXle₂
  refine ⟨⟨hQ₁, hQ₂, hi₁, hi₂⟩, ⟨S1_relIndex hM, ?_⟩, ?_, ?_⟩
  · rw [← hm₁]
    calc (Pz S z).relIndex (Pof S K₁ ⊔ Qof S K₁) * (Pof S K₁ ⊔ Qof S K₁).relIndex (S1 S K₁)
        ≤ 2 * 2 := Nat.mul_le_mul hPX₁ hidx₁
      _ = 4 := by norm_num
  · intro K hK
    rcases hK with rfl | hK
    · exact hdih₁
    · rw [Set.mem_singleton_iff] at hK
      subst hK
      exact hdih₂
  · intro h4
    obtain ⟨i1, i1'⟩ := eq_two_of_mul_eq_four hPX₁ hidx₁ (hm₁.trans h4)
    obtain ⟨i2, i2'⟩ := eq_two_of_mul_eq_four hPX₂ hidx₂ (hm₂.trans h4)
    have hQz : M.Qm (pPrimeCoreOf 2) S K₁ K₂ = zpowers z := by
      have := (h41 G z S K₁ K₂ h).1
      rwa [Qz_eq h] at this
    have hne : Pof S K₁ ⊔ Qof S K₁ ≠ Pof S K₂ ⊔ Qof S K₂ := by
      intro heq
      obtain ⟨q, hqQ, hqP⟩ : ∃ q ∈ Qof S K₁, q ∉ Pof S K₂ := by
        by_contra hcon
        push Not at hcon
        have hX₁P : Pof S K₁ ⊔ Qof S K₁ ≤ Pz S z := by
          rw [Pz_eq h, Pm_eq_sup hM]
          exact sup_le le_sup_left (fun x hx => mem_sup_right (hcon x hx))
        have := Subgroup.relIndex_eq_one.2 hX₁P
        omega
      have hqX₂ : q ∈ Pof S K₂ ⊔ Qof S K₂ := heq ▸ mem_sup_right hqQ
      obtain ⟨p₂, hp₂, q₂, hq₂, hq⟩ := Sec4.M.mem_sup_of_commute
        (fun a ha c hc => comm_Pof_Qof hM (Or.inr rfl) ha hc) hqX₂
      have hq₂Q₁ : q₂ ∈ Qof S K₁ := by
        have hp₂Q : p₂ ∈ Qof S K₁ := Pof_le_Qof hM (Or.inr ⟨rfl, rfl⟩) hp₂
        have e : q₂ = p₂⁻¹ * q := by rw [hq]; group
        rw [e]
        exact (Qof S K₁).mul_mem ((Qof S K₁).inv_mem hp₂Q) hqQ
      have hq₂z : q₂ ∈ zpowers z := by
        have := Qof_inf_le_Qm hM hq₂Q₁ hq₂
        rwa [hQz] at this
      have hzP₂ : zpowers z ≤ Pof S K₂ :=
        zpowers_le.2 ⟨hM.z_mem_S, hM.z_mem_comp (Or.inr rfl)⟩
      apply hqP
      rw [hq]
      exact (Pof S K₂).mul_mem hp₂ (hzP₂ hq₂z)
    have hk := B.klein_of_two_index_two hPle₁ hPle₂ hXle₁ hXle₂ i1 i1' i2 i2' hne
    refine ⟨hk.2, le_antisymm ?_ (sup_le (le_sup_right.trans hXle₁) (le_sup_right.trans hXle₂))⟩
    rw [hk.1]
    exact sup_le (sup_le ((Pof_le_Qof hM (Or.inl ⟨rfl, rfl⟩)).trans le_sup_right) le_sup_left)
      (sup_le ((Pof_le_Qof hM (Or.inr ⟨rfl, rfl⟩)).trans le_sup_left) le_sup_right)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
