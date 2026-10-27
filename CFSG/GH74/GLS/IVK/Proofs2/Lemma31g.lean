module

public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GH74.GLS.IVK.Lifted.Out
public import CFSG.GH74.GLS.IVK.Proofs2.ConjComponent
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.Semidihedral
open scoped commutatorElement

@[expose] def IVK_3_1g_fixed : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → 3 < Nat.card F₁ → 3 < Nat.card F₂ →
      (normalizer (K₁ : Set H)).index ≤ 2 ∧
      ∀ a ∈ normalizer (K₁ : Set H), ∀ b ∈ normalizer (K₁ : Set H), ⁅a, b⁆ ∈ K₁ ⊔ K₂

namespace Lemma31g

section Abstract

variable {H : Type} [Group H]

theorem mem_conj_iff (K : Subgroup H) (g u : H) :
    u ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  rfl

theorem mem_normalizer_iff_conj_eq (K : Subgroup H) (g : H) :
    g ∈ normalizer (K : Set H) ↔ K.map (MulAut.conj g).toMonoidHom = K := by
  constructor
  · intro hg
    ext u
    rw [mem_conj_iff]
    have hg' := Subgroup.mem_normalizer_iff.mp (inv_mem hg) u
    simpa [mul_assoc] using hg'.symm
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h1 := mem_conj_iff K g (g * u * g⁻¹)
    rw [hg] at h1
    simpa [mul_assoc] using h1.symm

theorem index_le_two_of_dichotomy {K₁ K₂ : Subgroup H}
    (hdich : ∀ g : H, K₁.map (MulAut.conj g).toMonoidHom = K₁ ∨
      K₁.map (MulAut.conj g).toMonoidHom = K₂) :
    (normalizer (K₁ : Set H)).index ≤ 2 := by
  by_cases hN : normalizer (K₁ : Set H) = ⊤
  · rw [hN, Subgroup.index_top]; norm_num
  obtain ⟨a, ha⟩ : ∃ a : H, a ∉ normalizer (K₁ : Set H) := by
    by_contra hcon
    push Not at hcon
    exact hN (eq_top_iff.mpr fun x _ => hcon x)
  have hquot : ∀ x y : H, x ∉ normalizer (K₁ : Set H) → y ∉ normalizer (K₁ : Set H) →
      y⁻¹ * x ∈ normalizer (K₁ : Set H) := by
    intro x y hx hy
    have hx2 : K₁.map (MulAut.conj x).toMonoidHom = K₂ :=
      (hdich x).resolve_left (fun h => hx ((mem_normalizer_iff_conj_eq K₁ x).mpr h))
    have hy2 : K₁.map (MulAut.conj y).toMonoidHom = K₂ :=
      (hdich y).resolve_left (fun h => hy ((mem_normalizer_iff_conj_eq K₁ y).mpr h))
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hxu : u ∈ K₁ ↔ x * u * x⁻¹ ∈ K₂ := by
      rw [← hx2, mem_conj_iff]
      simp [mul_assoc]
    have hyu : y⁻¹ * (x * u * x⁻¹) * y ∈ K₁ ↔ x * u * x⁻¹ ∈ K₂ := by
      rw [← hy2, mem_conj_iff]
    rw [hxu, ← hyu]
    simp [mul_assoc]
  have h2 : (normalizer (K₁ : Set H)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨a, fun b => ?_⟩
    by_cases hb : b ∈ normalizer (K₁ : Set H)
    · refine Or.inr ⟨hb, fun hba => ha ?_⟩
      have := mul_mem (inv_mem hb) hba
      simpa using this
    · refine Or.inl ⟨?_, hb⟩
      have hb' : b⁻¹ ∉ normalizer (K₁ : Set H) := fun h => hb (by simpa using inv_mem h)
      have := hquot b⁻¹ a hb' ha
      have h3 : (b * a)⁻¹ ∈ normalizer (K₁ : Set H) := by simpa [mul_inv_rev] using this
      simpa using inv_mem h3
  rw [h2]

theorem exists_inner_commutator {S : Type} [Group S] {K : Subgroup H} (e : ↥K ≃* S)
    (hout : ∀ α β : MulAut S, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : S →* MulAut S).range)
    {a b : H} (ha : a ∈ normalizer (K : Set H)) (hb : b ∈ normalizer (K : Set H)) :
    ∃ k ∈ K, ∀ x ∈ K, ⁅a, b⁆ * x * ⁅a, b⁆⁻¹ = k * x * k⁻¹ := by
  let ψ : normalizer (K : Set H) →* MulAut S :=
    (MulAut.congr e).toMonoidHom.comp K.normalizerMonoidHom
  obtain ⟨s, hs⟩ := hout (ψ ⟨a, ha⟩) (ψ ⟨b, hb⟩)
  obtain ⟨c, hcoe, key⟩ : ∃ c : normalizer (K : Set H), (c : H) = ⁅a, b⁆ ∧ ψ c = MulAut.conj s :=
    ⟨⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹, by
      rw [commutatorElement_def]
      simp, by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hs.symm⟩
  refine ⟨(e.symm s : K), (e.symm s).2, fun x hx => ?_⟩
  have h1 := congrArg (fun f : MulAut S => f (e ⟨x, hx⟩)) key
  have h1' : e (K.normalizerMonoidHom c ⟨x, hx⟩) = s * e ⟨x, hx⟩ * s⁻¹ := by
    simpa [ψ, MulAut.congr_apply] using h1
  have h2 : K.normalizerMonoidHom c ⟨x, hx⟩ = e.symm s * ⟨x, hx⟩ * (e.symm s)⁻¹ := by
    apply e.injective
    rw [h1', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 := congrArg (fun y : K => (y : H)) h2
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_mul,
    InvMemClass.coe_inv] at h3
  rw [← hcoe]
  exact h3

theorem commutator_eq_self {S : Type} [Group S] {K : Subgroup H} (e : ↥K ≃* S)
    (hperf : Group.IsPerfect S) : ⁅K, K⁆ = K := by
  have h1 : (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆) = ⊤ := by
    have h2 : (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆).map e.toMonoidHom =
        ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    have h3 : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
      have := hperf.commutator_eq_top
      rwa [commutator_def] at this
    rw [h3] at h2
    have h4 := congrArg (Subgroup.comap e.toMonoidHom) h2
    rw [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at h4
    exact h4
  have h5 := congrArg (Subgroup.map K.subtype) h1
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h5
  exact h5

theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  let quotient := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ quotient.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf.1] at hderived
    exact top_unique hderived

end Abstract

section Prod

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

omit [Field F₂] in
theorem sl2_normal {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [N.Normal] :
    N ≤ Subgroup.center _ ∨ N = ⊤ := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact normal_le_center_or_eq_top (CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩)
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF) N

theorem exists_nontrivial_inter (h : ProdSL2 H K₁ K₂ F₁ F₂) : ∃ z ∈ K₁ ⊓ K₂, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : K₁ ⊓ K₂ = ⊥ := eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  have h1 := h.card_inter
  rw [hbot] at h1
  simp at h1

theorem odd_card_fst (h : ProdSL2 H K₁ K₂ F₁ F₂) [Finite F₁] {z : H} (hz : z ∈ K₁ ⊓ K₂)
    (hz1 : z ≠ 1) : Odd (Nat.card F₁) := by
  have hF : ringChar F₁ ≠ 2 := by
    intro hc
    apply (h.z_data₁ hz hz1).1
    have := CharP.cast_eq_zero F₁ (ringChar F₁)
    rw [hc] at this
    exact_mod_cast this
  have : Fintype F₁ := Fintype.ofFinite F₁
  have h2 := FiniteField.odd_card_of_char_ne_two hF
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr h2

theorem normal_sub_le_z [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) (hF : 3 < Nat.card F₁) {z : H}
    (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) (N : Subgroup H) (hNK : N ≤ K₁)
    (hN : ∀ x ∈ K₁, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : N ≤ zpowers z ∨ N = K₁ := by
  have := h.finite₁
  let e := h.slEquiv₁
  have hN' : (N.subgroupOf K₁).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
  have hM : ((N.subgroupOf K₁).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hN' e.toMonoidHom e.surjective
  rcases sl2_normal (F := F₁) (by omega) ((N.subgroupOf K₁).map e.toMonoidHom) with hc | htop
  · left
    intro n hn
    have hnK : n ∈ K₁ := hNK hn
    have hmem : e ⟨n, hnK⟩ ∈ (N.subgroupOf K₁).map e.toMonoidHom :=
      ⟨⟨n, hnK⟩, by simpa [Subgroup.mem_subgroupOf] using hn, rfl⟩
    have hcen := hc hmem
    rcases (ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F₁ _).1 hcen with h1 | h1
    · have : (⟨n, hnK⟩ : ↥K₁) = 1 := e.injective (by rw [h1, map_one])
      have hn1 : n = 1 := congrArg Subtype.val this
      rw [hn1]
      exact one_mem _
    · have hm : e ⟨n, hnK⟩ = OddFieldSL2.minusIdentity F₁ := by
        rw [h1, ProjectiveSL2Cover.minusIdentity_eq_neg_one]
        rfl
      have : (⟨n, hnK⟩ : ↥K₁) = ⟨z, hz.1⟩ :=
        e.injective (by rw [hm, (h.z_data₁ hz hz1).2])
      have hnz : n = z := congrArg Subtype.val this
      rw [hnz]
      exact mem_zpowers z
  · right
    refine le_antisymm hNK (fun x hx => ?_)
    have hx' : e ⟨x, hx⟩ ∈ (N.subgroupOf K₁).map e.toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = ⟨x, hx⟩ := e.injective hyx
    rw [this] at hy
    simpa [Subgroup.mem_subgroupOf] using hy

theorem not_le_zpowers [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) (hF : 3 < Nat.card F₁) {z : H}
    (hzo : orderOf z = 2) : ¬ K₁ ≤ zpowers z := by
  intro hle
  have := h.finite₁
  have h1 : Nat.card ↥K₁ ≤ Nat.card ↥(zpowers z) :=
    Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hzo, Nat.card_congr h.slEquiv₁.toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F₁] at h1
  have h2 : 15 ≤ Nat.card F₁ ^ 2 - 1 := by
    have : 16 ≤ Nat.card F₁ ^ 2 := by nlinarith
    omega
  have h3 : 4 * 15 ≤ Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := Nat.mul_le_mul (by omega) h2
  omega

theorem commutator_eq [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) (hF : 3 < Nat.card F₁) :
    ⁅K₁, K₁⁆ = K₁ := by
  have := h.finite₁
  have : Fintype F₁ := Fintype.ofFinite F₁
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F₁)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  exact commutator_eq_self h.slEquiv₁
    (CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩)

theorem conj_dichotomy [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) (hF₁ : 3 < Nat.card F₁)
    (hF₂ : 3 < Nat.card F₂) (g : H) :
    K₁.map (MulAut.conj g).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  obtain ⟨z, hz, hz1⟩ := exists_nontrivial_inter h
  obtain ⟨hint, hzo⟩ := h.inter_eq hz hz1
  have hz' : z ∈ K₂ ⊓ K₁ := ⟨hz.2, hz.1⟩
  have hint' : K₂ ⊓ K₁ = zpowers z := by rw [inf_comm]; exact hint
  refine conj_component h.comm hzo hint h.fstar_normal (commutator_eq h hF₁)
    (commutator_eq h.symm hF₂) ?_ ?_ (not_le_zpowers h hF₁ hzo) (not_le_zpowers h.symm hF₂ hzo) g
  · exact fun N hNK hN => normal_sub_le_z h hF₁ hz hz1 N hNK hN
  · exact fun N hNK hN => normal_sub_le_z h.symm hF₂ hz' hz1 N hNK hN

theorem central_mem_snd [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) {a : H} (ha : a ∈ K₁)
    (hc : ∀ k ∈ K₁, k * a = a * k) : a ∈ K₂ := by
  obtain ⟨z, hz, hz1⟩ := exists_nontrivial_inter h
  have hcen : h.slEquiv₁ ⟨a, ha⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₁) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := h.slEquiv₁.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg h.slEquiv₁ (Subtype.ext (hc k k.2))
  rcases (ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F₁ _).1 hcen with h1 | h1
  · have : (⟨a, ha⟩ : ↥K₁) = 1 := h.slEquiv₁.injective (by rw [h1, map_one])
    have ha1 : a = 1 := congrArg Subtype.val this
    rw [ha1]
    exact one_mem _
  · have hm : h.slEquiv₁ ⟨a, ha⟩ = OddFieldSL2.minusIdentity F₁ := by
      rw [h1, ProjectiveSL2Cover.minusIdentity_eq_neg_one]
      rfl
    have : (⟨a, ha⟩ : ↥K₁) = ⟨z, hz.1⟩ :=
      h.slEquiv₁.injective (by rw [hm, (h.z_data₁ hz hz1).2])
    have haz : a = z := congrArg Subtype.val this
    rw [haz]
    exact hz.2

theorem conj_mem_snd [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) {g : H}
    (hg : g ∈ normalizer (K₁ : Set H)) {x : H} (hx : x ∈ K₂) : g * x * g⁻¹ ∈ K₂ := by
  have hK : g * x * g⁻¹ ∈ K₁ ⊔ K₂ :=
    h.fstar_normal.conj_mem x (Subgroup.mem_sup_right hx) g
  obtain ⟨a, ha, b, hb, hab⟩ := (h.mem_sup_iff _).1 hK
  have hc : ∀ k ∈ K₁, k * a = a * k := by
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).1 hk
      simpa using this
    have h1 := h.comm _ hk' x hx
    have h2 : k * (g * x * g⁻¹) = (g * x * g⁻¹) * k := by
      calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = (g * x * g⁻¹) * k := by group
    rw [hab] at h2
    have h3 : k * b = b * k := (h.comm k hk b hb)
    have h4 : (k * a) * b = (a * k) * b := by
      calc (k * a) * b = k * (a * b) := by group
        _ = (a * b) * k := h2
        _ = a * (b * k) := by group
        _ = a * (k * b) := by rw [h3]
        _ = (a * k) * b := by group
    exact mul_right_cancel h4
  have ha2 : a ∈ K₂ := central_mem_snd h ha hc
  rw [hab]
  exact K₂.mul_mem ha2 hb

theorem mem_normalizer_snd [Finite H] (h : ProdSL2 H K₁ K₂ F₁ F₂) {g : H}
    (hg : g ∈ normalizer (K₁ : Set H)) : g ∈ normalizer (K₂ : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_snd h hg hx, fun hx => ?_⟩
  have := conj_mem_snd h (inv_mem hg) hx
  simpa [mul_assoc] using this

end Prod

end Lemma31g

open Lemma31g in
theorem ivk_3_1g_fixed : IVK_3_1g_fixed := by
  intro F₁ F₂ _ _ H _ _ K₁ K₂ h hF₁ hF₂
  have := h.finite₁
  have := h.symm.finite₁
  refine ⟨index_le_two_of_dichotomy (conj_dichotomy h hF₁ hF₂), ?_⟩
  intro a ha b hb
  obtain ⟨z, hz, hz1⟩ := exists_nontrivial_inter h
  have hodd₁ := odd_card_fst h hz hz1
  have hodd₂ := odd_card_fst h.symm (z := z) ⟨hz.2, hz.1⟩ hz1
  have ha₂ := mem_normalizer_snd h ha
  have hb₂ := mem_normalizer_snd h hb
  obtain ⟨k₁, hk₁, hk₁x⟩ := exists_inner_commutator h.slEquiv₁
    (fun α β => CFSG.GH74.GLS.IVK.Lifted.out_abelian_sl hodd₁ hF₁ α β) ha hb
  obtain ⟨k₂, hk₂, hk₂x⟩ := exists_inner_commutator h.symm.slEquiv₁
    (fun α β => CFSG.GH74.GLS.IVK.Lifted.out_abelian_sl hodd₂ hF₂ α β) ha₂ hb₂
  have hk12 : k₁ * k₂ = k₂ * k₁ := h.comm k₁ hk₁ k₂ hk₂
  obtain ⟨w, hw⟩ : ∃ w : H, w = ⁅a, b⁆ := ⟨_, rfl⟩
  rw [← hw] at hk₁x hk₂x ⊢
  obtain ⟨c, hc⟩ : ∃ c : H, c = (k₁ * k₂)⁻¹ * w := ⟨_, rfl⟩
  have hc₁ : ∀ x ∈ K₁, c * x * c⁻¹ = x := by
    intro x hx
    have h2 : x * k₂ = k₂ * x := h.comm x hx k₂ hk₂
    calc c * x * c⁻¹ = (k₁ * k₂)⁻¹ * (w * x * w⁻¹) * (k₁ * k₂) := by
          rw [hc]; group
      _ = (k₁ * k₂)⁻¹ * (k₁ * x * k₁⁻¹) * (k₁ * k₂) := by rw [hk₁x x hx]
      _ = k₂⁻¹ * (x * k₂) := by group
      _ = x := by rw [h2]; group
  have hc₂ : ∀ x ∈ K₂, c * x * c⁻¹ = x := by
    intro x hx
    have h2 : k₁ * x = x * k₁ := h.comm k₁ hk₁ x hx
    have hc' : c = (k₂ * k₁)⁻¹ * w := by rw [hc, hk12]
    calc c * x * c⁻¹ = (k₂ * k₁)⁻¹ * (w * x * w⁻¹) * (k₂ * k₁) := by
          rw [hc']; group
      _ = (k₂ * k₁)⁻¹ * (k₂ * x * k₂⁻¹) * (k₂ * k₁) := by rw [hk₂x x hx]
      _ = k₁⁻¹ * (x * k₁) := by group
      _ = x := by rw [← h2]; group
  have hcK : c ∈ centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := (h.mem_sup_iff y).1 hy
    have h1 : c * u * c⁻¹ = u := hc₁ u hu
    have h2 : c * v * c⁻¹ = v := hc₂ v hv
    have h1' : c * u = u * c := by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1
    have h2' : c * v = v * c := by rw [mul_inv_eq_iff_eq_mul] at h2; exact h2
    calc u * v * c = u * (v * c) := by group
      _ = u * (c * v) := by rw [h2']
      _ = (u * c) * v := by group
      _ = (c * u) * v := by rw [h1']
      _ = c * (u * v) := by group
  have hcmem := h.fstar_centralizer hcK
  have : w = (k₁ * k₂) * c := by rw [hc]; group
  rw [this]
  exact (K₁ ⊔ K₂).mul_mem (Subgroup.mul_mem_sup hk₁ hk₂) hcmem

end CFSG.GH74.GLS.IVK.Proofs2
