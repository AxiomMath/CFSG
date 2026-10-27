module

public import CFSG.LargeExtraspecial.S8FiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def A1 (t : S.O) : Subgroup S.O :=
  (S.Lbar g ⊓ Nbar S g t) ⊓ centralizer (Nbar S g t : Set S.O)

theorem mem_A1 {t x : S.O} :
    x ∈ A1 S g t ↔ x ∈ S.Lbar g ∧ x ∈ Nbar S g t ∧ ∀ n ∈ Nbar S g t, n * x = x * n := by
  rw [A1, mem_inf, mem_inf, mem_centralizer_iff]
  simp only [SetLike.mem_coe, and_assoc]

theorem eq_one_of_sub_mem_clSub (H : Hyp4 S g) (C : Cons311 S g) {α : S.O} (hα : α ∈ S.Lbar g)
    (h : ∀ q, (α : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ S.clSub (S.QG ⊓ S.Qa g)) : α = 1 := by
  have hne := H.conj_ne
  have hαα : α * α = 1 := mul_self_of_mem_Lbar S H.conj_mem hα
  have hiso : ∀ u ∈ S.clSub (S.QG ⊓ S.Qa g), ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g),
      polar S.q u v = 0 := by
    intro u hu v hv
    have h1 := QuadraticMap.map_add S.q u v
    rw [S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne ((S.clSub _).add_mem hu hv),
      S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hu, S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hv,
      zero_add, zero_add] at h1
    exact h1.symm
  refine C.faithful α hα fun p hp => ?_
  rw [← sub_eq_zero]
  refine S.q_nondegenerate.1 _ fun x => ?_
  rw [polarBilin_apply_apply]
  have hαx : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) x) = x := by
    rw [← coe_mul_apply, hαα]; rfl
  have hpol : polar S.q ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) p) x =
      polar S.q p ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
    conv_lhs => rw [← hαx]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup α.2 _ _
  rw [polar_sub_left, hpol, ← polar_sub_right]
  exact hiso p hp _ (h x)

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem eq_top_of_Lbar_invariant (D : Std H C ht ht1 hVQ) {U : Submodule (ZMod 2) (Vt S g t)}
    (hU : ∀ l (hl : l ∈ S.Lbar g), ∀ u ∈ U, resV H.conj_mem t ⟨l, Lbar_le_Rbar ht hl⟩ u ∈ U)
    {u : Vt S g t} (huU : u ∈ U) (hua : polar D.Q (aV ht) u = 1) : U = ⊤ := by
  set a := aV ht with ha
  have ha0 : a ≠ 0 := aV_ne_zero H ht
  have hf : ∀ w, polar D.Q a w = 0 →
      w + (polar D.Q u w + D.Q w) • a ∈ U := by
    intro w hw
    have hE : eichler D.Q a w ∈ LmodN S g t := by
      rw [D.hE]; exact eichler_mem_pointRadical D.hQa hw
    obtain ⟨l, hl, hlv⟩ := mem_LmodN.mp hE
    have hres : resV H.conj_mem t ⟨l, Lbar_le_Rbar ht hl⟩ = eichler D.Q a w :=
      LinearEquiv.ext fun v => Subtype.ext (by rw [coe_resV_apply, hlv])
    have h1 := hU l hl u huU
    rw [hres] at h1
    have h2 := U.sub_mem h1 huU
    rw [eichler_apply_zmod2 D.hQa hw, polar_comm D.Q u a, hua, one_smul, mul_one] at h2
    convert h2 using 1
    abel
  set b := bV (mem_Lbar_of_pair H ht D.hh) with hb
  have hF : (⊥ : Submodule (ZMod 2) (Vt S g t)) ⊓ S2.perp D.Q ⊥ = ⊥ := bot_inf_eq _
  have hmem : ∀ v : Vt S g t, v ∈ S2.perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t)) := fun v => by
    rw [S2.perp_bot]; exact Submodule.mem_top
  have hK := S2.sup_span_pair_inf_perp_eq_bot hF (hmem a) (hmem b) D.polar_aV_bV
  have hKdim := S2.finrank_perp_sup_span_pair D.hQ hF (hmem a) (hmem b) D.polar_aV_bV
  rw [S2.perp_bot, finrank_top, D.hdim] at hKdim
  have hne : S2.perp D.Q (⊥ ⊔ Submodule.span (ZMod 2) {a, b}) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hKdim
    have := D.hm
    omega
  obtain ⟨w₁, hw₁K, hw₁⟩ := S2.exists_mem_perp_map_eq_one D.hQ hK hne
  have hw₁0 : w₁ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw₁
    exact zero_ne_one hw₁
  obtain ⟨w₂, hw₂K, hw₂w₁⟩ := S2.exists_mem_perp_polar_eq_one D.hQ hK hw₁K hw₁0
  have haw₁ : polar D.Q a w₁ = 0 := (S2.mem_perp_sup_span_pair.mp hw₁K).2.1
  have haw₂ : polar D.Q a w₂ = 0 := (S2.mem_perp_sup_span_pair.mp hw₂K).2.1
  have haU : a ∈ U := by
    have h1 := hf w₁ haw₁
    have h2 := hf w₂ haw₂
    have h3 := hf (w₁ + w₂) (by rw [polar_add_right, haw₁, haw₂, add_zero])
    have h4 := U.sub_mem (U.add_mem h1 h2) h3
    have e : w₁ + (polar D.Q u w₁ + D.Q w₁) • a + (w₂ + (polar D.Q u w₂ + D.Q w₂) • a) -
        (w₁ + w₂ + (polar D.Q u (w₁ + w₂) + D.Q (w₁ + w₂)) • a) = a := by
      rw [polar_add_right, QuadraticMap.map_add D.Q w₁ w₂, polar_comm D.Q w₁ w₂, hw₂w₁]
      have : (polar D.Q u w₁ + D.Q w₁) • a + (polar D.Q u w₂ + D.Q w₂) • a -
          (polar D.Q u w₁ + polar D.Q u w₂ + (D.Q w₁ + D.Q w₂ + 1)) • a = a := by
        rw [← add_smul, ← sub_smul]
        have key : ∀ p q r s : ZMod 2, p + r + (q + s) - (p + q + (r + s + 1)) = 1 := by decide
        have h5 := key (polar D.Q u w₁) (polar D.Q u w₂) (D.Q w₁) (D.Q w₂)
        rw [h5, one_smul]
      calc _ = (polar D.Q u w₁ + D.Q w₁) • a + (polar D.Q u w₂ + D.Q w₂) • a -
            (polar D.Q u w₁ + polar D.Q u w₂ + (D.Q w₁ + D.Q w₂ + 1)) • a := by abel
        _ = a := this
    rwa [e] at h4
  have hperp : ∀ w, polar D.Q a w = 0 → w ∈ U := by
    intro w hw
    have h1 := U.sub_mem (hf w hw) (U.smul_mem (polar D.Q u w + D.Q w) haU)
    rwa [add_sub_cancel_right] at h1
  rw [eq_top_iff]
  intro v _
  have hv' : polar D.Q a (v - polar D.Q a v • u) = 0 := by
    rw [polar_sub_right, polar_smul_right, hua, smul_eq_mul, mul_one, sub_self]
  have := U.add_mem (hperp _ hv') (U.smul_mem (polar D.Q a v) huU)
  rwa [sub_add_cancel] at this

theorem commSpace_eq_Vt_of_mem_A1 (D : Std H C ht ht1 hVQ) {α : S.O} (hα : α ∈ A1 S g t)
    (hα1 : α ≠ 1) : commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g t := by
  obtain ⟨hαL, hαN, hαc⟩ := mem_A1.mp hα
  have hle : commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t := by
    rintro _ ⟨q, rfl⟩
    exact sub_mem_Vt_of_mem_center H C ht ht1 hVQ D.hA D.hN hαN hαc q
  set U := (commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt)).comap (Vt S g t).subtype with hUdef
  have hUinv : ∀ l (hl : l ∈ S.Lbar g), ∀ u ∈ U,
      resV H.conj_mem t ⟨l, Lbar_le_Rbar ht hl⟩ u ∈ U := by
    intro l hl u hu
    obtain ⟨q, hq⟩ := mem_commSpace.mp hu
    refine mem_commSpace.mpr ⟨(l : S.Qt ≃ₗ[ZMod 2] S.Qt) q, ?_⟩
    change _ = ((resV H.conj_mem t ⟨l, Lbar_le_Rbar ht hl⟩ u : Vt S g t) : S.Qt)
    rw [coe_resV_apply]
    change _ = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt)
    have hcomm : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) q) =
        (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt) q) := by
      rw [← coe_mul_apply, ← coe_mul_apply, Lbar_comm S H.conj_mem hαL hl]
    have hq' : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = (u : S.Qt) := hq
    rw [← hq', map_sub, hcomm]
  have hnot : ∃ u ∈ U, polar D.Q (aV ht) u = 1 := by
    by_contra hcon
    push Not at hcon
    apply hα1
    refine eq_one_of_sub_mem_clSub H C hαL fun q => ?_
    have hqV : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t := hle (sub_mem_commSpace _ q)
    set u : Vt S g t := ⟨_, hqV⟩ with hu
    have huU : u ∈ U := sub_mem_commSpace _ q
    have h0 : beta H C ht ht1 hVQ (aV ht) u = 0 := by
      rw [← D.hpol, polarBilin_apply_apply]
      rcases zmod2_eq_zero_or_eq_one (polar D.Q (aV ht) u) with h | h
      · exact h
      · exact absurd h (hcon u huU)
    exact (beta_aV_eq_zero_iff H C ht ht1 hVQ u).mp h0
  obtain ⟨u, huU, hua⟩ := hnot
  have hUtop := eq_top_of_Lbar_invariant D hUinv huU hua
  refine le_antisymm hle fun v hv => ?_
  have : (⟨v, hv⟩ : Vt S g t) ∈ U := by rw [hUtop]; exact Submodule.mem_top
  exact this

end CFSG.LargeExtraspecial.S8
