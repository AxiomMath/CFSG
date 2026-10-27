module

public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.GLW4FusCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.GLR

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {c : Config}

theorem lev_of (h : W4Hyp S g t c) (hCE : CentralExtInput.{0}) :
    Lev h.S₀ (ι S) (Vt S g t) (Wt S g t) := by
  obtain ⟨H, C, ht, ht1, hVQ, hΩ, -⟩ := h.rnOmega
  have hNo : NoA2 S g := noA2_of (h.stage.noA2 g H.conj_mem H.conj_ne)
  obtain ⟨hcomm, hfix⟩ := commSpace_t_eq H C ht ht1 hVQ
  obtain ⟨k, hk, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  have hz : ∀ x, dm (ι S h.S₀.z) x = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := fun x => rfl
  refine ⟨fun α hα => ?_, fun x => ?_, fun v hv => ?_, fun x hx => ?_, fun w hw => ?_, ?_⟩
  · have hN : ι S α ∈ Nbar S g t := h.mem_S₀_QG.mp hα
    refine ⟨hN.2, fun w hw => S6.timmesfeld_6_1_one H C ht ht1 hVQ hk hb hCE hNo hΩ hN hw,
      fun x => ?_⟩
    rw [mem_Wt]
    intro u hu
    rw [dm_apply, polar_sub_right]
    have e : polar S.q u (((ι S α : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = polar S.q u x := by
      conv_lhs => rw [← hN.2 u hu]
      exact Config.polar_apply_apply _ _ _
    rw [e, sub_self]
  · rw [hz, ← hcomm]
    exact mem_commSpace.mpr ⟨x, rfl⟩
  · rw [← hcomm] at hv
    obtain ⟨x, hx⟩ := mem_commSpace.mp hv
    exact ⟨x, hx⟩
  · rw [hz, sub_eq_zero] at hx
    rw [← hfix]
    exact mem_fixSpace.mpr hx
  · rw [← hfix] at hw
    exact mem_fixSpace.mp hw
  · exact h.stage.ne_one

theorem three_le_of_mul_eq {A B d : ℕ} (hL : A * B = 2 ^ 8) (hA : A ≤ 2 ^ 4)
    (hd : ∀ k, B = 2 ^ k → d + 1 = k) : 3 ≤ d := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ hL)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ hL)
  have h1 := hd k hk
  subst hk hj
  rw [← pow_add] at hL
  have h2 := Nat.pow_right_injective le_rfl hL
  have h3 : j ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hA
  omega

theorem three_le_finrank_of {X : Type*} [Group X] [Finite X] {T : Setting X} (hw : T.width = 4)
    (hP : ∀ P : Subgroup T.Mbar, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ 2 = 1) →
      Nat.card P ≤ 2 ^ 4)
    {m : X} (hmQ : m * T.z * m⁻¹ ∈ T.QG) (hne : m * T.z * m⁻¹ ≠ T.z) :
    3 ≤ finrank (ZMod 2) (T.clSub (T.QG ⊓ T.Qa m)) := by
  have hL : Nat.card (T.Lbar m) * Nat.card (T.QG ⊓ T.Qa m : Subgroup X) = 2 ^ 8 := by
    rw [T.card_Lbar_mul m, T.card_L0 hmQ hne, hw]
  have hLle : Nat.card (T.Lbar m) ≤ 2 ^ 4 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (T.Lbar_le_Mbar m)).toEquiv]
    refine hP _ (fun a ha b hb => Subtype.ext ?_) (fun a ha => Subtype.ext ?_)
    · exact T.Lbar_comm hmQ (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)
    · rw [Subgroup.coe_pow, pow_two]
      exact mul_self_of_mem_Lbar T hmQ (Subgroup.mem_subgroupOf.mp ha)
  exact three_le_of_mul_eq hL hLle fun k hk => T.finrank_clSub_QG_inf_Qa hmQ hne hk

theorem three_le_finrank (h : W4Hyp S g t c) [IsSimpleGroup G]
    (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt) {m : ↥(Mbar0 S)}
    (hmQ : m * h.S₀.z * m⁻¹ ∈ h.S₀.QG) (hne : m * h.S₀.z * m⁻¹ ≠ h.S₀.z) :
    3 ≤ finrank (ZMod 2) (h.S₀.clSub (h.S₀.QG ⊓ h.S₀.Qa m)) :=
  three_le_finrank_of h.width_S₀ (h.card_le_of_elemAbelian hNQ hNQ6) hmQ hne

end CFSG.LargeExtraspecial.GLW4
