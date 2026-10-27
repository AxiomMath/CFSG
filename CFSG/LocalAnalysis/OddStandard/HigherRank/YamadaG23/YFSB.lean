module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFSC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFJr2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFNorm

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private lemma s3_z_ne_one (hA : LFactsA s) : s.fr.z ≠ 1 := by
  intro h
  have h1 : orderOf s.fr.z = 1 := by rw [h, orderOf_one]
  rw [hA.z_order] at h1
  norm_num at h1

theorem s3_A_conj_RneT (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (h31 : s.Fact31) (hA : LFactsA s)
    (e : Setting3.Ext s) (hRT : s.R ≠ s.T) {x : G} (hx : x ∈ e.T₁) {y : G}
    (hy : y ∈ s.fr.A) : x * y * x⁻¹ ∈ s.fr.A := by
  have hXx : ∀ y ∈ s.fr.A, x * y * x⁻¹ ∈ s.fr.A ∨
      ∃ a ∈ s.fr.A, x * y * x⁻¹ = a * s.t := by
    intro y hy
    have hw : x * y * x⁻¹ ∈ s.fr.A ⊔ zpowers s.t :=
      s3_AT_conj s hS hOut h31 hA e hRT hx (Subgroup.mem_sup_left hy)
    obtain ⟨a, ha, h | h⟩ := s3_mem_A_sup_t s hw
    · exact Or.inl (by rwa [h])
    · exact Or.inr ⟨a, ha, h⟩
  exact s3_inv_arg s hS hZ h31 hA e (s3_A_le_L s)
    (srel_closure_invols_A (s3_srel hS hZ s) (s3_z_ne_one s hA)) hx hXx y hy

theorem fusion32_of_RneT (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (h31 : s.Fact31) (hA : LFactsA s)
    (e : Setting3.Ext s) (hRT : s.R ≠ s.T) : e.Fact32 := by
  have hz : s.fr.z ≠ 1 := s3_z_ne_one s hA
  have hAN : ∀ x ∈ e.T₁, ∀ y ∈ s.fr.A, x * y * x⁻¹ ∈ s.fr.A :=
    fun x hx y hy => s3_A_conj_RneT s hS hZ hOut h31 hA e hRT hx hy
  have hR1 := s3_R1_RneT s hS hZ hOut h31 hA e hRT hAN
  have hAT1 : s.fr.A ≤ e.T₁ := (s3_A_le_S s).trans ((s3_S_le_T s).trans e.T_le)
  have hST1 : s.fr.S ≤ e.T₁ := (s3_S_le_T s).trans e.T_le
  have hR1T1 : e.R₁ ≤ e.T₁ := by
    unfold Setting3.Ext.R₁
    split_ifs with h
    · exact le_rfl
    · exact inf_le_left
  have hAnorm : (s.fr.A.subgroupOf e.T₁).Normal :=
    (Subgroup.normal_subgroupOf_iff hAT1).mpr
      (fun n k hn hk => s3_A_conj_RneT s hS hZ hOut h31 hA e hRT hk hn)
  have hR1norm : (e.R₁.subgroupOf e.T₁).Normal :=
    Subgroup.normal_of_index_eq_two (by simpa only [Subgroup.relIndex] using hR1.2)
  have hTnorm : (s.T.subgroupOf e.T₁).Normal := s3_T_normal_T1 s hA h31 e
  have hSnorm : (s.fr.S.subgroupOf e.T₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hST1]
    intro n k hn hk
    have hXx : ∀ y ∈ s.fr.S, k * y * k⁻¹ ∈ s.fr.S ∨
        ∃ a ∈ s.fr.S, k * y * k⁻¹ = a * s.t := by
      intro y hy
      have hyT : y ∈ s.T := s3_S_le_T s hy
      have hyR : y ∈ s.R := s.S_le_R hy
      have hyR1 : y ∈ e.R₁ := (hR1.1 ▸ inf_le_left) hyR
      have hconjT : k * y * k⁻¹ ∈ s.T :=
        (Subgroup.normal_subgroupOf_iff e.T_le).mp hTnorm y k hyT hk
      have hconjR1 : k * y * k⁻¹ ∈ e.R₁ :=
        (Subgroup.normal_subgroupOf_iff hR1T1).mp hR1norm y k hyR1 hk
      have hconjR : k * y * k⁻¹ ∈ s.R := by
        rw [← hR1.1]
        exact ⟨hconjR1, hconjT⟩
      obtain ⟨w, hw, h | h⟩ := s3_R_cases s hS h31 (k * y * k⁻¹) hconjR
      · exact Or.inl (by rwa [h])
      · exact Or.inr ⟨w, hw, h⟩
    exact s3_inv_arg s hS hZ h31 hA e (s3_S_le_L s)
      (srel_closure_invols_S (s3_srel hS hZ s) hz) hk hXx n hn
  exact ⟨⟨hAT1, hAnorm⟩, ⟨hST1, hSnorm⟩, hR1.1, fun _ => hR1.2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
