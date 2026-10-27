module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeAct

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups commutatorElement

theorem isSolvable_of_three_levels {G : Type*} [Group G] (H₀ H₁ H₂ : Subgroup G)
    (h01 : ∀ x ∈ H₀, ∀ y ∈ H₀, ⁅x, y⁆ ∈ H₁) (h12 : ∀ x ∈ H₁, ∀ y ∈ H₁, ⁅x, y⁆ ∈ H₂)
    (h2 : ∀ x ∈ H₂, ∀ y ∈ H₂, x * y = y * x) : Group.IsSolvable ↥H₀ := by
  have e1 : derivedSeries ↥H₀ 1 ≤ H₁.subgroupOf H₀ := by
    rw [derivedSeries_succ, derivedSeries_zero]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    exact h01 a a.2 b b.2
  have e2 : derivedSeries ↥H₀ 2 ≤ H₂.subgroupOf H₀ := by
    rw [derivedSeries_succ]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    exact h12 a (e1 ha) b (e1 hb)
  have e3 : derivedSeries ↥H₀ 3 = ⊥ := by
    rw [derivedSeries_succ, eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact Subtype.ext (h2 a (e2 ha) b (e2 hb))
  exact ⟨⟨3, e3⟩⟩

private theorem conj_inv_twist {G : Type*} [Group G] {c a z : G} (h : c * z * c⁻¹ = a * z)
    (hc : c * a = a * c) : c⁻¹ * z * c = a⁻¹ * z := by
  have h1 : c⁻¹ * a * c = a := by
    rw [(show Commute c a from hc).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  calc c⁻¹ * z * c = a⁻¹ * (c⁻¹ * a * c) * (c⁻¹ * z * c) := by rw [h1]; group
    _ = a⁻¹ * (c⁻¹ * (a * z) * c) := by group
    _ = a⁻¹ * (c⁻¹ * (c * z * c⁻¹) * c) := by rw [h]
    _ = a⁻¹ * z := by group

theorem commutator_fix_of_twist {G : Type*} [Group G] {z a₁ a₂ c₁ c₂ : G}
    (h₁ : c₁ * z * c₁⁻¹ = a₁ * z) (h₂ : c₂ * z * c₂⁻¹ = a₂ * z)
    (ha₁c₁ : c₁ * a₁ = a₁ * c₁) (ha₁c₂ : c₂ * a₁ = a₁ * c₂) (ha₂c₁ : c₁ * a₂ = a₂ * c₁)
    (ha₂c₂ : c₂ * a₂ = a₂ * c₂) (ha : a₁ * a₂ = a₂ * a₁) :
    ⁅c₁, c₂⁆ * z * ⁅c₁, c₂⁆⁻¹ = z := by
  have i₁ := conj_inv_twist h₁ ha₁c₁
  have i₂ := conj_inv_twist h₂ ha₂c₂
  have f₁ : c₁⁻¹ * a₂⁻¹ * c₁ = a₂⁻¹ := by
    rw [(show Commute c₁ a₂ from ha₂c₁).inv_right.inv_left.eq, mul_assoc, inv_mul_cancel,
      mul_one]
  have f₂ : c₂ * a₂⁻¹ * c₂⁻¹ = a₂⁻¹ := by
    rw [(show Commute c₂ a₂ from ha₂c₂).inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have f₃ : c₂ * a₁⁻¹ * c₂⁻¹ = a₁⁻¹ := by
    rw [(show Commute c₂ a₁ from ha₁c₂).inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have f₄ : c₁ * a₁⁻¹ * c₁⁻¹ = a₁⁻¹ := by
    rw [(show Commute c₁ a₁ from ha₁c₁).inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅c₁, c₂⁆ * z * ⁅c₁, c₂⁆⁻¹
      = c₁ * (c₂ * (c₁⁻¹ * (c₂⁻¹ * z * c₂) * c₁) * c₂⁻¹) * c₁⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = c₁ * (c₂ * (c₁⁻¹ * (a₂⁻¹ * z) * c₁) * c₂⁻¹) * c₁⁻¹ := by rw [i₂]
    _ = c₁ * (c₂ * ((c₁⁻¹ * a₂⁻¹ * c₁) * (c₁⁻¹ * z * c₁)) * c₂⁻¹) * c₁⁻¹ := by group
    _ = c₁ * (c₂ * (a₂⁻¹ * (a₁⁻¹ * z)) * c₂⁻¹) * c₁⁻¹ := by rw [f₁, i₁]
    _ = c₁ * ((c₂ * a₂⁻¹ * c₂⁻¹) * (c₂ * a₁⁻¹ * c₂⁻¹) * (c₂ * z * c₂⁻¹)) * c₁⁻¹ := by group
    _ = c₁ * (a₂⁻¹ * a₁⁻¹ * (a₂ * z)) * c₁⁻¹ := by rw [f₂, f₃, h₂]
    _ = c₁ * (a₁⁻¹ * z) * c₁⁻¹ := by
        rw [show a₂⁻¹ * a₁⁻¹ * (a₂ * z) = a₁⁻¹ * z by
          rw [(show Commute a₂ a₁ from ha.symm).inv_inv.eq]; group]
    _ = (c₁ * a₁⁻¹ * c₁⁻¹) * (c₁ * z * c₁⁻¹) := by group
    _ = z := by rw [f₄, h₁]; group

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {S : CSetupW p f 2 Ω K z} {Fr : Frame p f 2 Ω K z}
  (P : LeviParams S Fr)

namespace LeviParams

theorem mem_centralizer_h {y : G} (hy : y ∈ P.T₀ ⊔ P.T₁) :
    y * (P.x₀ * P.x₁ * P.x₂) = (P.x₀ * P.x₁ * P.x₂) * y := by
  have hk₂ : ∀ m ∈ Mf Fr 0 1, m * P.x₂ = P.x₂ * m := fun m hm =>
    commutes_Mf_Kf Fr (i := 0) (j := 1) (k := 2) (by decide) (by decide) m hm P.x₂
      (Frame.Tf_le 2 P.x₂_mem)
  have hk₀ : ∀ m ∈ Mf Fr 1 2, m * P.x₀ = P.x₀ * m := fun m hm =>
    commutes_Mf_Kf Fr (i := 1) (j := 2) (k := 0) (by decide) (by decide) m hm P.x₀
      (Frame.Tf_le 0 P.x₀_mem)
  have hh : P.x₀ * P.x₁ * P.x₂ = P.x₁ * P.x₂ * P.x₀ := by
    rw [Fr.Tf_mul_comm P.x₀_mem P.x₁_mem, mul_assoc, Fr.Tf_mul_comm P.x₀_mem P.x₂_mem,
      ← mul_assoc]
  have hY : P.T₀ ⊔ P.T₁ ≤ Subgroup.centralizer ({P.x₀ * P.x₁ * P.x₂} : Set G) := by
    refine sup_le (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    · have h1 : t * (P.x₀ * P.x₁) = (P.x₀ * P.x₁) * t :=
        Subgroup.mem_centralizer_singleton_iff.mp (leviNode_le_centralizer _ _ ht)
      have h2 : t * P.x₂ = P.x₂ * t := hk₂ t (P.T₀_le ht)
      exact ((show Commute t (P.x₀ * P.x₁) from h1).mul_right
        (show Commute t P.x₂ from h2)).eq
    · rw [hh]
      have h1 : t * (P.x₁ * P.x₂) = (P.x₁ * P.x₂) * t :=
        Subgroup.mem_centralizer_singleton_iff.mp (leviNode_le_centralizer _ _ ht)
      have h2 : t * P.x₀ = P.x₀ * t := hk₀ t (P.T₁_le ht)
      exact ((show Commute t (P.x₁ * P.x₂) from h1).mul_right
        (show Commute t P.x₀ from h2)).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (hY hy)

theorem commute_of_centralizes_layer (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥)
    {c₁ c₂ : G} (h₁M : ∀ m ∈ Mf Fr 0 1, m * c₁ = c₁ * m) (h₁x : P.x₂ * c₁ = c₁ * P.x₂)
    (h₂M : ∀ m ∈ Mf Fr 0 1, m * c₂ = c₂ * m) (h₂x : P.x₂ * c₂ = c₂ * P.x₂) :
    c₁ * c₂ = c₂ * c₁ := by
  have d₁ := P.diagAct_of_centralizes_layer h₁M h₁x
  have d₂ := P.diagAct_of_centralizes_layer h₂M h₂x
  have hu12 : ∀ m ∈ Mf Fr 1 2, m * ⁅c₁, c₂⁆ = ⁅c₁, c₂⁆ * m := by
    intro m hm
    rw [← P.ψ₀_range] at hm
    obtain ⟨x, rfl⟩ := hm
    exact (DiagAct.commutator_commute d₁ d₂ x).symm
  have hu01 : ∀ m ∈ Mf Fr 0 1, m * ⁅c₁, c₂⁆ = ⁅c₁, c₂⁆ * m := by
    intro m hm
    have h1 : c₁ ∈ Subgroup.centralizer (Mf Fr 0 1 : Set G) := Subgroup.mem_centralizer_iff.mpr h₁M
    have h2 : c₂ ∈ Subgroup.centralizer (Mf Fr 0 1 : Set G) := Subgroup.mem_centralizer_iff.mpr h₂M
    have hu : ⁅c₁, c₂⁆ ∈ Subgroup.centralizer (Mf Fr 0 1 : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
    exact Subgroup.mem_centralizer_iff.mp hu m hm
  have hcen : ⁅c₁, c₂⁆ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : Mf Fr 0 1 ⊔ Mf Fr 1 2 ≤ Subgroup.centralizer ({⁅c₁, c₂⁆} : Set G) :=
      sup_le (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hu01 m hm))
        (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hu12 m hm))
    have hg : g ∈ Mf Fr 0 1 ⊔ Mf Fr 1 2 := by
      rw [Mf_sup_Mf_eq_top S hconn Fr]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  rw [hZ, Subgroup.mem_bot] at hcen
  exact (commutatorElement_eq_one_iff_commute.mp hcen).eq

theorem solvable_centralizer (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) :
    Group.IsSolvable ↥((P.T₀ ⊔ P.T₁) ⊓ Subgroup.centralizer (P.T₀ : Set G)) := by
  set W : Subgroup G := (P.T₀ ⊔ P.T₁) ⊓ Subgroup.centralizer (P.T₀ : Set G) with hW
  set W₁ : Subgroup G := W ⊓ Subgroup.centralizer ({Fr.zf 0} : Set G) with hW₁
  set B : Subgroup G := Subgroup.centralizer (Mf Fr 0 1 : Set G) ⊓
    Subgroup.centralizer ({P.x₂} : Set G) with hB
  have hcommW : ∀ c ∈ W, ∀ t ∈ P.T₀, t * c = c * t := fun c hc =>
    Subgroup.mem_centralizer_iff.mp hc.2
  have hcommutator : ∀ c₁ ∈ W, ∀ c₂ ∈ W, ⁅c₁, c₂⁆ ∈ W := fun c₁ h₁ c₂ h₂ => by
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem h₁ h₂) (W.inv_mem h₁)) (W.inv_mem h₂)
  have hz20 : Fr.zf 2 * Fr.zf 0 = Fr.zf 1 := by
    have h2 := zf_two_eq S hconn hZ Fr
    have hsq : Fr.zf 0 * Fr.zf 0 = 1 := by
      have h := pow_orderOf_eq_one (Fr.zf 0)
      rw [(Fr.clsW S 0).orderOf_eq_two, pow_two] at h
      exact h
    rw [h2, mul_assoc, Fr.zf_commW S 1 0, ← mul_assoc, hsq, one_mul]
  have hdich : ∀ c ∈ W, ∃ a : G, (a = 1 ∨ a = Fr.zf 2) ∧ c * Fr.zf 0 * c⁻¹ = a * Fr.zf 0 := by
    intro c hc
    rcases P.act_dichotomy hconn hZ (hcommW c hc) with ⟨-, h⟩ | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨Fr.zf 2, Or.inr rfl, by rw [h, hz20]⟩
  have hz2c : ∀ c ∈ W, c * Fr.zf 2 = Fr.zf 2 * c := fun c hc =>
    (hcommW c hc _ (P.zf_two_mem hconn hZ)).symm
  refine isSolvable_of_three_levels W W₁ B ?_ ?_ ?_
  · intro c₁ h₁ c₂ h₂
    obtain ⟨a₁, ha₁, e₁⟩ := hdich c₁ h₁
    obtain ⟨a₂, ha₂, e₂⟩ := hdich c₂ h₂
    have hac : ∀ {c : G}, c ∈ W → ∀ {a : G}, (a = 1 ∨ a = Fr.zf 2) → c * a = a * c := by
      intro c hc a ha
      rcases ha with rfl | rfl
      · rw [mul_one, one_mul]
      · exact hz2c c hc
    refine ⟨hcommutator c₁ h₁ c₂ h₂, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := commutator_fix_of_twist e₁ e₂ (hac h₁ ha₁) (hac h₂ ha₁) (hac h₁ ha₂) (hac h₂ ha₂)
      (by rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl <;> simp)
    exact mul_inv_eq_iff_eq_mul.mp this
  · intro c₁ h₁ c₂ h₂
    have hdiag : ∀ c ∈ W₁, DiagAct P.ψ₂ c := by
      intro c hc
      have hz : c * Fr.zf 0 = Fr.zf 0 * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rcases P.act_dichotomy hconn hZ (hcommW c hc.1) with ⟨hd, -⟩ | h
      · exact hd
      · exfalso
        have : c * Fr.zf 0 * c⁻¹ = Fr.zf 0 := mul_inv_eq_iff_eq_mul.mpr hz
        exact zf_ne_of_ne S Fr (i := 0) (j := 1) (by decide) (this.symm.trans h)
    have hu := hcommutator c₁ h₁.1 c₂ h₂.1
    have hu01 : ∀ m ∈ Mf Fr 0 1, m * ⁅c₁, c₂⁆ = ⁅c₁, c₂⁆ * m := by
      intro m hm
      rw [← P.ψ₂_range] at hm
      obtain ⟨x, rfl⟩ := hm
      exact (DiagAct.commutator_commute (hdiag c₁ h₁) (hdiag c₂ h₂) x).symm
    refine ⟨Subgroup.mem_centralizer_iff.mpr hu01, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hd₀₁ : P.x₀ * P.x₁ ∈ Mf Fr 0 1 := (Mf Fr 0 1).mul_mem
      (Tf_le_Mf Fr 0 (Or.inl rfl) P.x₀_mem) (Tf_le_Mf Fr 1 (Or.inr rfl) P.x₁_mem)
    have hh := P.mem_centralizer_h hu.1
    have h1 : (P.x₀ * P.x₁) * ⁅c₁, c₂⁆ = ⁅c₁, c₂⁆ * (P.x₀ * P.x₁) := hu01 _ hd₀₁
    have h2 : (P.x₀ * P.x₁) * (⁅c₁, c₂⁆ * P.x₂) = (P.x₀ * P.x₁) * (P.x₂ * ⁅c₁, c₂⁆) := by
      calc (P.x₀ * P.x₁) * (⁅c₁, c₂⁆ * P.x₂) = ((P.x₀ * P.x₁) * ⁅c₁, c₂⁆) * P.x₂ := by group
        _ = (⁅c₁, c₂⁆ * (P.x₀ * P.x₁)) * P.x₂ := by rw [h1]
        _ = ⁅c₁, c₂⁆ * (P.x₀ * P.x₁ * P.x₂) := by group
        _ = (P.x₀ * P.x₁ * P.x₂) * ⁅c₁, c₂⁆ := hh
        _ = (P.x₀ * P.x₁) * (P.x₂ * ⁅c₁, c₂⁆) := by group
    exact mul_left_cancel h2
  · intro c₁ h₁ c₂ h₂
    exact P.commute_of_centralizes_layer hconn hZ (Subgroup.mem_centralizer_iff.mp h₁.1)
      (Subgroup.mem_centralizer_singleton_iff.mp h₁.2).symm
      (Subgroup.mem_centralizer_iff.mp h₂.1) (Subgroup.mem_centralizer_singleton_iff.mp h₂.2).symm

end LeviParams

end Levi

end CFSG.ClassicalInvolution.RouteD
