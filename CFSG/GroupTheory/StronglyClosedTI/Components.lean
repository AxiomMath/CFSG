module

public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.ClassicalInvolution.Basic
import CFSG.GH74.SmallRanks.Basic

public section

namespace CFSG.GroupTheory.StronglyClosedTI

open Subgroup

variable {X : Type*} [Group X]

section Components

variable [Finite X]

theorem exists_mem_inf_ne_one (hL : CFSG.layer X = ⊤)
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) (T : Sylow 2 X)
    {A : Subgroup X} (hTA : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ A) {K : Subgroup X}
    (hK : CFSG.IsComponent K) : ∃ a ∈ A, a ∈ K ∧ a ≠ 1 := by
  have hKn : K.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hL hK
  have h2 : 2 ∣ Nat.card K := by
    by_contra h
    have hodd : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
    exact (Subgroup.nontrivial_iff_ne_bot K).mp (CFSG.LocalCores.isQuasisimple_nontrivial hK.1)
      (hO K hKn hodd)
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  have hk' : orderOf (k : X) = 2 := by rwa [Subgroup.orderOf_coe]
  obtain ⟨c, s, hs, hs2, hcs⟩ :=
    CFSG.ClassicalInvolution.exists_conj_mem_sylow_of_orderOf_eq_two T hk'
  have hsK : s ∈ K := by
    have : c⁻¹ * (k : X) * c⁻¹⁻¹ ∈ K := hKn.conj_mem _ k.2 c⁻¹
    rw [← hcs] at this
    simpa [mul_assoc] using this
  refine ⟨s, hTA s hs ?_, hsK, ?_⟩
  · rw [← pow_two, ← hs2]
    exact pow_orderOf_eq_one s
  · rintro rfl
    rw [orderOf_one] at hs2
    exact absurd hs2 (by norm_num)

theorem not_le_of_isComponent {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1) {K : Subgroup X}
    (hK : CFSG.IsComponent K) : ¬ K ≤ A := by
  intro hKA
  obtain ⟨-, -, a, b, hab⟩ := hK.1
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  have h1 : ∀ x : K, x * x = 1 := fun x => Subtype.ext (hA2 _ (hKA x.2))
  have h2 : ∀ x : K, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h1 x)
  have h3 := h2 (a * b)
  rw [mul_inv_rev, h2, h2] at h3
  exact h3.symm

theorem inf_eq_bot_of_le_normalizer (hL : CFSG.layer X = ⊤) (hZ : center X = ⊥)
    {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hKA : K ≤ normalizer (A : Set X)) : A ⊓ K = ⊥ := by
  have hN : ((A ⊓ K).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (hKA hk) x
    constructor
    · rintro ⟨hxA, hxK⟩
      exact ⟨h1.mp hxA, K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
    · rintro ⟨hxA, hxK⟩
      refine ⟨h1.mpr hxA, ?_⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      simpa [mul_assoc] using this
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hN with h | h
  · exfalso
    apply not_le_of_isComponent hA2 hK
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ (A ⊓ K).subgroupOf K := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  · rw [eq_bot_iff]
    intro x hx
    have hxc : (⟨x, hx.2⟩ : K) ∈ center K := h (Subgroup.mem_subgroupOf.mpr hx)
    have h2 := CFSG.LocalCores.center_component_le_centralizer_layer hK ⟨_, hxc, rfl⟩
    rw [hL, coe_top, centralizer_univ, hZ] at h2
    exact h2

theorem component_eq_of_TI (hL : CFSG.layer X = ⊤) (hZ : center X = ⊥)
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) (T : Sylow 2 X)
    {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1)
    (hTA : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ A)
    (hTI : ∀ a ∈ A, a ≠ 1 → ∀ x : X, x * a = a * x → x ∈ normalizer (A : Set X))
    {K₁ K₂ : Subgroup X} (h₁ : CFSG.IsComponent K₁) (h₂ : CFSG.IsComponent K₂) : K₁ = K₂ := by
  by_contra hne
  have hc : ⁅K₁, K₂⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne
  obtain ⟨a, haA, haK, ha1⟩ := exists_mem_inf_ne_one hL hO T hTA h₁
  have hK₂ : K₂ ≤ normalizer (A : Set X) := by
    intro k hk
    refine hTI a haA ha1 k ?_
    have := Subgroup.commutator_mem_commutator haK hk
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hbot := inf_eq_bot_of_le_normalizer hL hZ hA2 h₂ hK₂
  obtain ⟨b, hbA, hbK, hb1⟩ := exists_mem_inf_ne_one hL hO T hTA h₂
  have : b ∈ A ⊓ K₂ := ⟨hbA, hbK⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hb1 this

theorem isComponent_top [Nontrivial X] (hL : CFSG.layer X = ⊤) (hZ : center X = ⊥)
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) (T : Sylow 2 X)
    {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1)
    (hTA : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ A)
    (hTI : ∀ a ∈ A, a ≠ 1 → ∀ x : X, x * a = a * x → x ∈ normalizer (A : Set X)) :
    CFSG.IsComponent (⊤ : Subgroup X) := by
  have hex : ∃ K : Subgroup X, CFSG.IsComponent K := by
    by_contra h
    push_neg at h
    have := CFSG.LocalCores.layer_eq_bot_of_forall h
    rw [hL] at this
    exact top_ne_bot this
  obtain ⟨K, hK⟩ := hex
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hL, CFSG.layer.eq_sSup]
    exact sSup_le fun K' hK' => (component_eq_of_TI hL hZ hO T hA2 hTA hTI hK' hK).le
  exact hKtop ▸ hK

theorem card_le_of_forall_sylow_mem (T : Sylow 2 X) {A : Subgroup X}
    (hTA : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ A) {E : Subgroup X}
    (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card A := by
  have hE : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => by rw [pow_two]; exact hE2 x hx⟩
    have h1 : ∀ x : E, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (Subtype.ext (hE2 x x.2))
    have h2 : (a * b)⁻¹ = a * b := h1 (a * b)
    rw [mul_inv_rev, h1, h1] at h2
    exact h2.symm
  obtain ⟨g, hg⟩ := CFSG.GH74.SmallRanks.exists_conj_le_sylow T hE
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨e, he, rfl⟩
    refine hTA _ (hg ⟨e, he, rfl⟩) ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [hE2 e he]; group
  calc Nat.card E = Nat.card (E.map (MulAut.conj g).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
    _ ≤ Nat.card A := Subgroup.card_le_of_le hle

end Components

section Top

theorem nonempty_mulEquiv_quotient_center_top (hZ : center X = ⊥) :
    Nonempty (X ≃* ↥(⊤ : Subgroup X) ⧸ center ↥(⊤ : Subgroup X)) := by
  have hc : center ↥(⊤ : Subgroup X) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : (z : X) ∈ center X := by
      rw [mem_center_iff]
      intro g
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨g, mem_top g⟩)
    rw [hZ, mem_bot] at this
    exact Subtype.ext this
  exact ⟨(Subgroup.topEquiv.symm.trans QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq hc.symm)⟩

theorem isSimpleGroup_of_isComponent_top (hZ : center X = ⊥)
    (h : CFSG.IsComponent (⊤ : Subgroup X)) : IsSimpleGroup X := by
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_top hZ
  exact (MulEquiv.isSimpleGroup_congr e).mpr h.1.2.1

end Top

end CFSG.GroupTheory.StronglyClosedTI

end
