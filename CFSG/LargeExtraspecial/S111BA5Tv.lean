module

public import CFSG.LargeExtraspecial.S111BA5Ut
public import CFSG.LargeExtraspecial.S111AExists

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem Lbar_apply_mem_clSub {x : S.O} (hx : x ∈ S.Lbar k) {v : S.Qt} (hv : v ∈ S.clSub A) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A := by
  have h1 := P.cfg.inc.apply_sub_mem_span P.mem hx hv
  have h2 : (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) ≤ S.clSub A :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (S.cl_mem_clSub P.mem P.memQ)
  rw [show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + v by abel]
  exact add_mem (h2 h1) hv

theorem card_eq_card_inf_ptFix_mul {Y : Subgroup S.O} (hY : Y ≤ S.Lbar k) :
    Nat.card Y = Nat.card (Y ⊓ ptFix S (S.clSub A) : Subgroup S.O) *
      2 ^ (finrank (ZMod 2) (S.clSub A) - finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S Y)) := by
  have haP : S.cl (k * S.z * k⁻¹) ∈ S.clSub A := S.cl_mem_clSub P.mem P.memQ
  have hinv : ∀ (x : Y) u, u ∈ S.clSub A →
      ((S.O.subtype.comp Y.subtype) x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ S.clSub A :=
    fun x u hu => P.Lbar_apply_mem_clSub (hY x.2) hu
  set ψ := restrictHom (S.O.subtype.comp Y.subtype) (S.clSub A) hinv with hψ
  have hψc : ∀ x (u : S.clSub A), ψ x u - u ∈ (ZMod 2) ∙ (⟨_, haP⟩ : S.clSub A) := by
    intro x u
    rw [mem_span_singleton_subtype]
    exact P.cfg.inc.apply_sub_mem_span P.mem (hY x.2) u.2
  have hY2 : IsPGroup 2 Y := (isPGroup_Lbar S P.memQ).to_le hY
  obtain ⟨h1, -⟩ := card_range_of_transvections hY2 ψ _ hψc
  have hker : ψ.ker = (ptFix S (S.clSub A)).subgroupOf Y := by
    ext x
    rw [MonoidHom.mem_ker, hψ, restrictHom_eq_one_iff, mem_subgroupOf]
    exact Iff.rfl
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = Nat.card Y := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hkc : Nat.card ψ.ker = Nat.card (Y ⊓ ptFix S (S.clSub A) : Subgroup S.O) := by
    rw [hker, ← inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : ptFix S (S.clSub A) ⊓ Y ≤ Y)).toEquiv,
      inf_comm]
  have hfix : (fixSpaceOf ψ.range).map (S.clSub A).subtype = S.clSub A ⊓ fixSub S Y := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, mem_fixSpaceOf_range] at hu
      exact ⟨u.2, (mem_fixSub S).mpr fun x hx => congrArg Subtype.val (hu ⟨x, hx⟩)⟩
    · rintro ⟨hvP, hvY⟩
      refine ⟨⟨v, hvP⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_fixSpaceOf_range]
      intro x
      exact Subtype.ext ((mem_fixSub S).mp hvY x x.2)
  have hf := Submodule.finrank_map_subtype_eq (S.clSub A) (fixSpaceOf ψ.range)
  rw [hfix] at hf
  rw [← hcard, hkc, h1, ← hf]

theorem finrank_clSub_inf_fixSub_Lbar :
    finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (S.Lbar k)) = 1 := by
  rw [P.hy.hyp4.fixSub_eq, inf_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr
    (S.cl_mem_clSub P.mem P.memQ)), finrank_span_singleton (cl_conj_z_ne_zero S P.memQ P.ne)]

theorem card_Lbar_eq_card_Kbar_mul :
    Nat.card (S.Lbar k) = Nat.card (Kbar S A k) * 2 ^ (finrank (ZMod 2) (S.clSub A) - 1) := by
  have := P.card_eq_card_inf_ptFix_mul (le_refl (S.Lbar k))
  rwa [P.finrank_clSub_inf_fixSub_Lbar] at this

theorem Ebar'_apply_mem_clSub {f : S.O} (hf : f ∈ Ebar S k' k) {v : S.Qt}
    (hv : v ∈ S.clSub A) : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (S.Lbar k ⊔ Ebar S k' k : Subgroup S.O) :=
    (isPGroup_Lbar S P.memQ).to_sup_of_normal_left'
      ((isPGroup_Lbar S P.memQ').to_le inf_le_left) inf_le_right
  obtain ⟨t, ht, ht1, htc⟩ := exists_ne_one_commute_of_le_normalizer hP2 le_sup_left
    P.Lbar_ne_bot (sup_le le_normalizer inf_le_right)
  obtain ⟨s, -, rfl⟩ := (mem_Lbar S).mp hf.1
  exact ρ_apply_mem_clSub
    (P.cfg.map_conj_eq_of_commute_Lbar P.mem P.ne ht ht1 (htc _ (mem_sup_right hf))) hv

theorem Kbar_le_or_le : Kbar S A k ≤ Ebar S k k' ∨ Ebar S k k' ≤ ptFix S (S.clSub A) := by
  by_cases hK : Kbar S A k ≤ Ebar S k k'
  · exact Or.inl hK
  right
  obtain ⟨x, hxK, hxE⟩ : ∃ x ∈ Kbar S A k, x ∉ Ebar S k k' := by
    by_contra hcon
    push Not at hcon
    exact hK hcon
  intro e he
  obtain ⟨f, hf, rfl⟩ := P.exists_comm_eq hxK.1 hxE he
  refine mem_ptFix.mpr fun v hv => ?_
  have h1 : ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A :=
    P.Ebar'_apply_mem_clSub (inv_mem hf) hv
  have h2 : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
    mem_ptFix.mp (inv_mem hxK.2) _ h1
  rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, h2, ← coe_mul_apply f f⁻¹, mul_inv_cancel]
  exact mem_ptFix.mp hxK.2 v hv

theorem finrank_W_eq (hE4 : Nat.card (S.Lbar k) = 4 * Nat.card (Ebar S k k')) :
    (finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (Ebar S k k')) = 3 ∧
        Kbar S A k ≤ Ebar S k k') ∨ Ebar S k k' ≤ ptFix S (S.clSub A) := by
  rcases P.Kbar_le_or_le with hKE | hE
  · refine Or.inl ⟨?_, hKE⟩
    have hL := P.card_Lbar_eq_card_Kbar_mul
    have hEc := P.card_eq_card_inf_ptFix_mul (inf_le_left : Ebar S k k' ≤ S.Lbar k)
    have hinf : Ebar S k k' ⊓ ptFix S (S.clSub A) = Kbar S A k :=
      le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨hKE hx, hx.2⟩)
    rw [hinf] at hEc
    have hK0 : 0 < Nat.card (Kbar S A k) := Nat.card_pos
    have hWr := Submodule.finrank_mono
      (inf_le_left : S.clSub A ⊓ fixSub S (Ebar S k k') ≤ S.clSub A)
    set r := finrank (ZMod 2) (S.clSub A) with hr
    set w := finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (Ebar S k k')) with hw
    rw [hE4, hEc] at hL
    have h3 : 2 ^ (r - 1) = 2 ^ (r - w + 2) := by
      rw [pow_add]
      apply Nat.eq_of_mul_eq_mul_left hK0
      rw [← hL]
      ring
    have h4 := Nat.pow_right_injective (le_refl 2) h3
    omega
  · exact Or.inr hE

theorem eq_zero_of_mem_clSub {v : S.Qt} (hv : v ∈ S.clSub A)
    (hv' : v ∈ S.clSub (A.map (MulAut.conj h).toMonoidHom)) : v = 0 := by
  obtain ⟨a, haA, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
  obtain ⟨b, hbA, hbQ, hab⟩ := S.mem_clSub_iff.mp hv'
  have hzh : S.z ∈ A.map (MulAut.conj h).toMonoidHom := (P.cfg.inc.map_conj P.hM).z_mem
  have haA' : a ∈ A.map (MulAut.conj h).toMonoidHom := by
    rcases (S.cl_eq_cl_iff haQ hbQ).mp hab.symm with e | e
    · rw [← e]; exact hbA
    · have ea : a = b * S.z := by rw [e, mul_assoc, S.z_mul_z, mul_one]
      rw [ea]; exact mul_mem hbA hzh
  have hmem : a ∈ A ⊓ A.map (MulAut.conj h).toMonoidHom := ⟨haA, haA'⟩
  rw [P.disj, Setting.mem_zpowers_iff_of_mul_self S.z_mul_z] at hmem
  rcases hmem with rfl | rfl
  · exact S.cl_one
  · exact S.cl_z

theorem finrank_add_finrank_le {φ : ↥(S.Lbar k ⊔ S.Lbar k') →* alternatingGroup (Fin 5)}
    (hφs : Function.Surjective φ) (hφk : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar k'))
    (hidx : 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k)) :
    finrank (ZMod 2) ↥(S.clSub A ⊓ fixSub S (Ebar S k k')) +
      finrank (ZMod 2) ↥(S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k))
      ≤ 4 := by
  obtain ⟨hE, hF, h4⟩ := P.fixSub_Ebar_eq_Ut hφs hφk hidx
  have hWU : S.clSub A ⊓ fixSub S (Ebar S k k') ≤ S9.Ut S k (S.Lbar k ⊔ S.Lbar k') :=
    hE ▸ inf_le_right
  have hW'U : S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k) ≤
      S9.Ut S k (S.Lbar k ⊔ S.Lbar k') := hF ▸ inf_le_right
  have hdisj : (S.clSub A ⊓ fixSub S (Ebar S k k')) ⊓
      (S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact P.eq_zero_of_mem_clSub (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).1).1
      (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).2).1
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub A ⊓ fixSub S (Ebar S k k'))
    (S.clSub (A.map (MulAut.conj h).toMonoidHom) ⊓ fixSub S (Ebar S k' k))
  rw [hdisj, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_mono (sup_le hWU hW'U)
  omega

theorem two_le_finrank_clSub : 2 ≤ finrank (ZMod 2) (S.clSub A) := by
  have h8 := P.cfg.eight_le_card
  rw [P.cfg.inc.card_eq, S.card_submodule] at h8
  by_contra hlt
  have : 2 ^ finrank (ZMod 2) (S.clSub A) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem finrank_clSub_map : finrank (ZMod 2) (S.clSub (A.map (MulAut.conj h).toMonoidHom)) =
    finrank (ZMod 2) (S.clSub A) := by
  have h1 := (P.cfg.inc.map_conj P.hM).card_eq
  rw [card_map_conj, P.cfg.inc.card_eq, S.card_submodule, S.card_submodule] at h1
  exact (Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_left (by norm_num) h1)).symm

end Pair111

end CFSG.LargeExtraspecial.S11
