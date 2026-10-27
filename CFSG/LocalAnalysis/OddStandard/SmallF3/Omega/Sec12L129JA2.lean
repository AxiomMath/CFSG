module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JOff
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JAlt2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

variable {G : Type} [Group G]

@[expose] noncomputable def sec12J_beta (V : Subgroup G) :
    ↥(normalizer (V : Set G)) →* ↥(secNb V) :=
  V.normalizerMonoidHom.codRestrict (secNb V) (fun n => Subgroup.mem_map.mpr ⟨n, n.2, rfl⟩)

theorem sec12J_beta_apply (V : Subgroup G) (n : ↥(normalizer (V : Set G))) (v : ↥V) :
    (((sec12J_beta V n : ↥(secNb V)) : MulAut ↥V) v : G) = (n : G) * v * (n : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V n v

theorem sec12J_beta_ker (V : Subgroup G) {n : ↥(normalizer (V : Set G))}
    (h : sec12J_beta V n = 1) : (n : G) ∈ centralizer (V : Set G) := by
  have h1 : V.normalizerMonoidHom n = 1 := congrArg Subtype.val h
  have h2 : n ∈ V.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem sec12J_main_alt2 [Finite G] {V : Subgroup G}
    (hC : ∀ g ∈ centralizer (V : Set G), (∃ m : ℕ, g ^ (2 ^ m) = 1) → g ∈ V)
    (hΩ : Sec128Alt2 V) {F : Subgroup G} (hFN : F ≤ secN V) (hF : IsElemAbelian 2 F) :
    F ≤ V ∨ Nat.card F ≤ 128 := by
  obtain ⟨φ, hS, hE, hidx⟩ := sec12J_alt2_data hΩ
  have hFN' : F ≤ normalizer (V : Set G) := hFN
  set β := sec12J_beta V with hβ
  set F' : Subgroup ↥(normalizer (V : Set G)) := F.subgroupOf (normalizer (V : Set G)) with hF'
  have hF'el : IsElemAbelian 2 F' := hF.subgroupOf _
  set Fb : Subgroup ↥(secNb V) := F'.map β with hFb
  have hFbel : IsElemAbelian 2 Fb := hF'el.map β
  have hcardF : Nat.card F = Nat.card (F' ⊓ β.ker : Subgroup _) * Nat.card Fb := by
    have h1 := sec12J_card_inf_ker_mul β F'
    have h2 : Nat.card F' = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN').toEquiv
    rw [← h2, ← h1]
  have hker : ∀ n : ↥(normalizer (V : Set G)), (n : G) ∈ F → β n = 1 → (n : G) ∈ V := by
    intro n hnF hn1
    refine hC n (sec12J_beta_ker V hn1) ⟨1, ?_⟩
    simpa using hF.2 _ hnF
  by_cases hFb1 : Fb = ⊥
  · left
    intro x hx
    have hxF' : (⟨x, hFN' hx⟩ : ↥(normalizer (V : Set G))) ∈ F' := hx
    have hβ1 : β ⟨x, hFN' hx⟩ = 1 := by
      have hmem : β ⟨x, hFN' hx⟩ ∈ Fb := Subgroup.mem_map_of_mem β hxF'
      rw [hFb1] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact hker ⟨x, hFN' hx⟩ hx hβ1
  · right
    have hjmem : ∀ x : ↥(F' ⊓ β.ker : Subgroup _), ((x : ↥(normalizer (V : Set G))) : G) ∈ V := by
      intro x
      exact hker x (Subgroup.mem_inf.mp x.2).1 (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).2)
    let j : ↥(F' ⊓ β.ker : Subgroup _) → ↥V := fun x => ⟨((x : ↥(normalizer (V : Set G))) : G),
      hjmem x⟩
    have hj : Function.Injective j := by
      intro a b hab
      have h1 := congrArg (fun z : ↥V => (z : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    have hfix : ∀ b ∈ Fb, ∀ x : ↥(F' ⊓ β.ker : Subgroup _), (secNb V).subtype b (j x) = j x := by
      intro b hb x
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hb
      apply Subtype.ext
      have h1 := sec12J_beta_apply V f (j x)
      have hfF : (f : G) ∈ F := hf
      have hxF : ((x : ↥(normalizer (V : Set G))) : G) ∈ F := (Subgroup.mem_inf.mp x.2).1
      have hc := CFSG.Open.IsElemAbelian.comm hF hfF hxF
      change (((β f : ↥(secNb V)) : MulAut ↥V) (j x) : G) = ((x : ↥(normalizer (V : Set G))) : G)
      rw [h1]
      change (f : G) * ((x : ↥(normalizer (V : Set G))) : G) * (f : G)⁻¹ = _
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have hoff := sec12J_offender hS (secNb V).subtype_injective hE hidx j hj hFbel hFb1 hfix
    rw [hcardF]
    calc Nat.card (F' ⊓ β.ker : Subgroup _) * Nat.card Fb ≤ 128 := hoff

end CFSG.OddStandard.SmallF3.Omega
