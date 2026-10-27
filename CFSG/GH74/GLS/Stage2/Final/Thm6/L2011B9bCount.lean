module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG.ABGLocalTools

section Action

variable {A B : Type*} [Group A] [Group B]

@[expose, instance_reducible] def autCosetAction (φ : A →* MulAut B) (P : Subgroup B)
    (hP : ∀ a, ∀ p ∈ P, φ a p ∈ P) : MulAction A (B ⧸ P) where
  smul a := Quotient.map' (fun b => φ a b) (fun x y h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    have := hP a _ h
    rwa [map_mul, map_inv] at this)
  one_smul x := by
    induction x using Quotient.inductionOn' with
    | _ b =>
      show ((φ 1 b : B) : B ⧸ P) = (b : B ⧸ P)
      rw [map_one]
      rfl
  mul_smul a a' x := by
    induction x using Quotient.inductionOn' with
    | _ b =>
      show ((φ (a * a') b : B) : B ⧸ P) = ((φ a (φ a' b) : B) : B ⧸ P)
      rw [map_mul]
      rfl

end Action

section Count

variable {G : Type*} [Group G] [Finite G]

theorem not_dvd_index_of_fixed {r : ℕ} [Fact r.Prime] (N Z : Subgroup G) (hZ : IsPGroup r ↥Z)
    (hZN : ∀ w ∈ Z, ∀ n ∈ N, w * n * w⁻¹ ∈ N)
    (hfix : ∀ n ∈ N, (∀ w ∈ Z, n⁻¹ * w * n ∈ normalizer (Z : Set G)) → n ∈ normalizer (Z : Set G)) :
    ¬ r ∣ ((normalizer (Z : Set G)).subgroupOf N).index := by
  classical
  set P : Subgroup ↥N := (normalizer (Z : Set G)).subgroupOf N with hPdef
  have hZnorm : Z ≤ normalizer (N : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hZN w hw n hn, fun hn => ?_⟩
    have := hZN w⁻¹ (Z.inv_mem hw) _ hn
    simpa [mul_assoc] using this
  let φ : ↥Z →* MulAut ↥N := (N.normalizerMonoidHom).comp (Subgroup.inclusion hZnorm)
  have hφ : ∀ (w : ↥Z) (n : ↥N), ((φ w n : ↥N) : G) = (w : G) * (n : G) * (w : G)⁻¹ := fun w n =>
    N.normalizerMonoidHom_apply_apply_coe (Subgroup.inclusion hZnorm w) n
  have hP : ∀ (w : ↥Z) (p : ↥N), p ∈ P → φ w p ∈ P := by
    intro w p hp
    rw [hPdef, Subgroup.mem_subgroupOf] at hp ⊢
    rw [hφ]
    have hwn : (w : G) ∈ normalizer (Z : Set G) := Subgroup.le_normalizer w.2
    exact mul_mem (mul_mem hwn hp) (inv_mem hwn)
  let _inst : MulAction ↥Z (↥N ⧸ P) := autCosetAction φ P hP
  have hmod := hZ.card_modEq_card_fixedPoints (↥N ⧸ P)
  have hone : Nat.card ↥(MulAction.fixedPoints ↥Z (↥N ⧸ P)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨(1 : ↥N), fun w => ?_⟩⟩⟩
    ·
      have key : ∀ x : ↥(MulAction.fixedPoints ↥Z (↥N ⧸ P)), x.1 = ((1 : ↥N) : ↥N ⧸ P) := by
        rintro ⟨x, hx⟩
        induction x using Quotient.inductionOn' with
        | _ a =>
          have hxw : ∀ w : ↥Z, ((φ w a : ↥N) : ↥N ⧸ P) = (a : ↥N ⧸ P) := fun w => hx w
          have h1 : ∀ w ∈ Z, (a : G)⁻¹ * w * (a : G) ∈ normalizer (Z : Set G) := by
            intro w hw
            have h2 := hxw ⟨w, hw⟩
            rw [QuotientGroup.eq] at h2
            rw [hPdef, Subgroup.mem_subgroupOf] at h2
            have h3 : (((φ ⟨w, hw⟩ a)⁻¹ * a : ↥N) : G) ∈ normalizer (Z : Set G) := h2
            have e : (((φ ⟨w, hw⟩ a)⁻¹ * a : ↥N) : G) =
                (w * (a : G)⁻¹ * w⁻¹) * (a : G) := by
              rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]; group
            rw [e] at h3
            have hwn : w ∈ normalizer (Z : Set G) := Subgroup.le_normalizer hw
            have h4 := mul_mem (inv_mem h3) hwn
            have e2 : ((w * (a : G)⁻¹ * w⁻¹) * (a : G))⁻¹ * w = (a : G)⁻¹ * w * (a : G) := by group
            rwa [e2] at h4
          have h5 := hfix (a : G) a.2 h1
          have h6 : a ∈ P := by rw [hPdef, Subgroup.mem_subgroupOf]; exact h5
          show ((a : ↥N) : ↥N ⧸ P) = ((1 : ↥N) : ↥N ⧸ P)
          rw [QuotientGroup.eq]
          simpa using P.inv_mem h6
      exact Subtype.ext ((key x).trans (key y).symm)
    ·
      show ((φ w 1 : ↥N) : ↥N ⧸ P) = ((1 : ↥N) : ↥N ⧸ P)
      rw [map_one]
  rw [hone] at hmod
  intro hd
  have h2 : Nat.card (↥N ⧸ P) ≡ 0 [MOD r] := (Nat.modEq_zero_iff_dvd).2 (by simpa [Subgroup.index] using hd)
  have h3 : 0 ≡ 1 [MOD r] := h2.symm.trans hmod
  have h4 : 0 % r = 1 % r := h3
  have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at h4
  omega

theorem exists_sylow_of_not_dvd {r : ℕ} [Fact r.Prime] (N M : Subgroup G) (hMN : M ≤ N)
    (h : ¬ r ∣ (M.subgroupOf N).index) : ∃ V : Subgroup G, IsSylowOf r V N ∧ V ≤ M := by
  obtain ⟨V, hV⟩ := exists_isSylowOf (p := r) M
  refine ⟨V, ?_, hV.le⟩
  rw [isSylowOf_iff] at hV ⊢
  obtain ⟨hVM, hVp, hVidx⟩ := hV
  refine ⟨hVM.trans hMN, hVp, fun hdvd => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex V M N hVM hMN] at hdvd
  rcases (Fact.out : r.Prime).dvd_mul.1 hdvd with h1 | h1
  · exact hVidx h1
  · exact h h1

end Count

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
