module

public import CFSG.LargeExtraspecial.S111BA5Dim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

theorem exists_orderOf_eq_five {Y : Type*} [Group Y] [Finite Y]
    {φ : Y →* alternatingGroup (Fin 5)} (hφs : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) : ∃ y : Y, orderOf y = 5 ∧ φ y ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h60 : Nat.card Y = Nat.card φ.ker * 60 := by
    rw [← nat_card_alternating_five, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top]
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5
    (show 5 ∣ Nat.card Y by rw [h60]; exact dvd_mul_of_dvd_right (by norm_num) _)
  refine ⟨y, hy, fun h1 => ?_⟩
  obtain ⟨n, hn⟩ := hker ⟨y, MonoidHom.mem_ker.mpr h1⟩
  have h := orderOf_dvd_of_pow_eq_one hn
  rw [Subgroup.orderOf_mk, hy] at h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h) (by norm_num)

theorem exists_mem_of_normal_of_ne_one {Y : Type*} [Group Y]
    {φ : Y →* alternatingGroup (Fin 5)} (hφs : Function.Surjective φ) {K : Subgroup Y}
    (hK : K.Normal) {y : Y} (hy : y ∈ K) (hφy : φ y ≠ 1) (x : Y) : ∃ c ∈ K, φ c = φ x := by
  have hN : (K.map φ).Normal := hK.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map φ) with h0 | h0
  · have hmem : φ y ∈ K.map φ := ⟨y, hy, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact absurd hmem hφy
  · have hmem : φ x ∈ K.map φ := by rw [h0]; exact Subgroup.mem_top _
    exact hmem

namespace Pair111

variable (P : Pair111 S g A h k k')
  {φ : ↥(S.Lbar k ⊔ S.Lbar k') →* alternatingGroup (Fin 5)}
include P

omit P in
theorem fix_Ut_of_pow_five {y : S.O} (hy : y ∈ S.Lbar k ⊔ S.Lbar k') (hy5 : y ^ 5 = 1)
    (hd : finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) ≤ 3) {u : S.Qt}
    (hu : u ∈ S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  set f := restrictEquiv (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k'))
    (fun v hv => S9.apply_mem_Ut hy hv) (fun v hv => S9.apply_mem_Ut (inv_mem hy) hv) with hf
  have hpow : ∀ (n : ℕ) (w : S9.Ut S k (S.Lbar k ⊔ S.Lbar k')),
      (((f ^ n) w : S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) : S.Qt) =
        ((y ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ]
      rfl
  have hf5 : f ^ 5 = 1 := by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [hpow, hy5]
    rfl
  have := congrArg Subtype.val (apply_eq_self_of_pow_five hd hf5 ⟨u, hu⟩)
  exact this

omit P in
theorem normal_ptFix_Ut :
    ((ptFix S (S9.Ut S k (S.Lbar k ⊔ S.Lbar k'))).subgroupOf (S.Lbar k ⊔ S.Lbar k')).Normal :=
  ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    refine mem_ptFix.mpr fun u hu => ?_
    have h1 : (((x⁻¹ : ↥(S.Lbar k ⊔ S.Lbar k')) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈
        S9.Ut S k (S.Lbar k ⊔ S.Lbar k') := S9.apply_mem_Ut (x⁻¹).2 hu
    change (((x : S.O) * (n : S.O) * ((x⁻¹ : ↥(S.Lbar k ⊔ S.Lbar k')) : S.O) : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt) u = u
    rw [coe_mul_apply, coe_mul_apply, mem_ptFix.mp hn _ h1, ← coe_mul_apply, Subgroup.coe_inv,
      mul_inv_cancel]
    rfl⟩

theorem four_le_finrank_Ut (hφs : Function.Surjective φ)
    (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k')) :
    4 ≤ finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hy, hφy⟩ := exists_orderOf_eq_five hφs (by rw [hφk]; exact CFSG.pCore_isPGroup)
  have hy5 : (y : S.O) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
  have hyC : y ∈ (ptFix S (S9.Ut S k (S.Lbar k ⊔ S.Lbar k'))).subgroupOf
      (S.Lbar k ⊔ S.Lbar k') :=
    mem_subgroupOf.mpr (mem_ptFix.mpr fun u hu =>
      fix_Ut_of_pow_five (S := S) y.2 hy5 (by omega) hu)
  have hUL : ∀ l ∈ S.Lbar k, ∀ u ∈ S9.Ut S k (S.Lbar k ⊔ S.Lbar k'),
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    intro l hl u hu
    have hlX : l ∈ S.Lbar k ⊔ S.Lbar k' := mem_sup_left hl
    obtain ⟨c, hc, hcl⟩ := exists_mem_of_normal_of_ne_one hφs normal_ptFix_Ut hyC hφy ⟨l, hlX⟩
    have hk : c⁻¹ * ⟨l, hlX⟩ ∈ CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k') := by
      rw [← hφk, MonoidHom.mem_ker, map_mul, map_inv, hcl, inv_mul_cancel]
    have hO : ((c⁻¹ * ⟨l, hlX⟩ : ↥(S.Lbar k ⊔ S.Lbar k')) : S.O) ∈
        O2Sub (S.Lbar k ⊔ S.Lbar k') := ⟨_, hk, rfl⟩
    have h1 := P.fix_Ut_of_mem_O2Sub hO hu
    have h2 : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
      mem_ptFix.mp (mem_subgroupOf.mp hc) u hu
    have e : (c : S.O) * ((c⁻¹ * ⟨l, hlX⟩ : ↥(S.Lbar k ⊔ S.Lbar k')) : S.O) = l := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [← e, coe_mul_apply, h1, h2]
  have hUa : S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ≤ (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) := by
    rw [← P.hy.hyp4.fixSub_eq]
    intro u hu
    exact (mem_fixSub S).mpr fun l hl => hUL l hl u hu
  obtain ⟨y', hy', hy'F⟩ := P.swap.exists_not_mem_Ebar
  apply hy'F
  refine ⟨hy', mem_normalizer_Lbar_of_fix hy' P.memQ P.ne ?_⟩
  have h1 : (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) ∈
      (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) :=
    hUa (S9.apply_mem_Ut (mem_sup_right hy') (S9.cl_mem_Ut _))
  rcases OrthoF2.mem_span_singleton_iff.mp h1 with h0 | h0
  · exact absurd ((LinearEquiv.map_eq_zero_iff _).mp h0) (cl_conj_z_ne_zero S P.memQ P.ne)
  · exact h0

theorem fixSub_Ebar_eq_Ut (hφs : Function.Surjective φ)
    (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k'))
    (hidx : 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k)) :
    fixSub S (Ebar S k k') = S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ∧
      fixSub S (Ebar S k' k) = S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ∧
      finrank (ZMod 2) (S9.Ut S k (S.Lbar k ⊔ S.Lbar k')) = 4 := by
  have hU4 := P.four_le_finrank_Ut hφs hφk
  have hUE : S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ≤ fixSub S (Ebar S k k') := by
    intro u hu
    refine (mem_fixSub S).mpr fun e he => P.fix_Ut_of_mem_O2Sub ?_ hu
    rw [← P.inf_O2Sub_eq] at he
    exact he.2
  have hUF : S9.Ut S k (S.Lbar k ⊔ S.Lbar k') ≤ fixSub S (Ebar S k' k) := by
    intro u hu
    refine (mem_fixSub S).mpr fun f hf => P.fix_Ut_of_mem_O2Sub ?_ hu
    rw [← P.inf_O2Sub_eq'] at hf
    exact hf.2
  have hE4 := finrank_fixSub_le_four_mul (S := S) (L := S.Lbar k) (E := Ebar S k k') inf_le_left
    (fun x hx y hy => Lbar_comm S P.memQ hx hy) (fun x hx => mul_self_of_mem_Lbar S P.memQ hx)
    (P.card_Lbar_eq_of_A5 hφk hidx)
  have hF4 := finrank_fixSub_le_four_mul (S := S) (L := S.Lbar k') (E := Ebar S k' k)
    inf_le_left
    (fun x hx y hy => Lbar_comm S P.memQ' hx hy) (fun x hx => mul_self_of_mem_Lbar S P.memQ' hx)
    (P.card_Lbar_eq_of_A5' hφk hidx)
  rw [P.finrank_fixSub_Lbar] at hE4
  rw [P.swap.finrank_fixSub_Lbar] at hF4
  have hE := Submodule.eq_of_le_of_finrank_le hUE (by omega)
  have hF := Submodule.eq_of_le_of_finrank_le hUF (by omega)
  refine ⟨hE.symm, hF.symm, ?_⟩
  rw [← hE] at hE4
  omega

end Pair111

end CFSG.LargeExtraspecial.S11
