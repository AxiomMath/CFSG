module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

section Transfer

variable {S : Type} [Group S]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ : MulAut S => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem conj_eq_one_of_mem_center {g : S} (hg : g ∈ Subgroup.center S) :
    (MulAut.conj : S →* MulAut S) g = 1 := by
  ext x
  have h1 := Subgroup.mem_center_iff.mp hg x
  simp only [MulAut.conj_apply, MulAut.one_apply]
  rw [← h1]
  group

theorem exists_comap_of_le_inner [Finite S] [IsSimpleGroup S] {A : Subgroup (MulAut S)}
    (hA : A ≤ inner S) (hE : IsElemAbelian 3 A) (hc : Nat.card A = 27) :
    ∃ Ab : Subgroup S, IsElemAbelian 3 Ab ∧ Nat.card Ab = 27 ∧
      Function.Injective (MulAut.conj : S →* MulAut S) ∧
      Subgroup.map (MulAut.conj : S →* MulAut S) Ab = A := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      have hA1 : A = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        obtain ⟨g, rfl⟩ := hA ha
        have hg : g ∈ Subgroup.center S := by
          rw [h]
          exact Subgroup.mem_top g
        rw [Subgroup.mem_bot]
        exact conj_eq_one_of_mem_center hg
      rw [hA1, Subgroup.card_bot] at hc
      norm_num at hc
  have hinj := conj_injective_of_center_eq_bot hZ
  have hA' : A ≤ (MulAut.conj : S →* MulAut S).range := hA
  have hmap : Subgroup.map (MulAut.conj : S →* MulAut S) (A.comap MulAut.conj) = A := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hA']
  refine ⟨A.comap MulAut.conj, ⟨?_, ?_⟩, ?_, hinj, hmap⟩
  ·
    refine ⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩
    have hcomm := hE.1.is_comm.comm
      (⟨MulAut.conj (a : S), Subgroup.mem_comap.mp a.2⟩ : ↥A)
      ⟨MulAut.conj (b : S), Subgroup.mem_comap.mp b.2⟩
    have hval := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul] at hval
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact hval
  · intro x hx
    have hxA : MulAut.conj (x : S) ∈ A := Subgroup.mem_comap.mp hx
    have h3 := hE.2 _ hxA
    apply hinj
    rw [map_pow, h3, map_one]
  · have h1 := Subgroup.card_map_of_injective (K := A.comap MulAut.conj) hinj
    rw [hmap] at h1
    rw [← h1, hc]

theorem centralizer_eq_iInf_fixSubgroup_map (Fb : Subgroup S) :
    Subgroup.centralizer (Fb : Set S) =
      ⨅ f ∈ Subgroup.map (MulAut.conj : S →* MulAut S) Fb, fixSubgroup f := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_iInf, Subgroup.mem_map, mem_fixSubgroup]
  constructor
  · rintro h f ⟨g, hg, rfl⟩
    rw [MulAut.conj_apply, h g hg]
    group
  · intro h g hg
    have hgx := h (MulAut.conj g) ⟨g, hg, rfl⟩
    rw [MulAut.conj_apply] at hgx
    exact mul_inv_eq_iff_eq_mul.mp hgx

theorem isGood_three_of_quasisimple [Finite S] {F : Subgroup (MulAut S)} {H C : Subgroup S}
    (hC : C = ⨅ f ∈ F, fixSubgroup f) (hHC : H ≤ C) (hsub : IsSubnormal H C)
    (hq : CFSG.Open.IsQuasisimple ↥H) (hdvd : 3 ∣ Nat.card (↥H ⧸ Subgroup.center ↥H)) :
    IsGood 3 F := by
  unfold IsGood
  rw [← hC]
  intro hbot
  have hcomp : GLAPComponent 3 C H :=
    CFSG.LocalAnalysis.GLTheoremA.S12.glaPComponent_of_quasisimple' Nat.prime_three hsub hq hdvd
  have hle : H ≤ GLAPLayer 3 C := le_sSup hcomp
  rw [hbot, le_bot_iff] at hle
  subst hle
  have h1 : Nat.card (↥(⊥ : Subgroup S) ⧸ Subgroup.center ↥(⊥ : Subgroup S)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩, ⟨1⟩⟩
  rw [h1] at hdvd
  norm_num at hdvd

theorem exists_good_of_kernel [Finite S] {A : Subgroup (MulAut S)} {Ab : Subgroup S}
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (hmap : Subgroup.map (MulAut.conj : S →* MulAut S) Ab = A)
    {Fb H : Subgroup S} (hF : Fb ≤ Ab) (h9 : Nat.card Fb = 9)
    (hH : H ≤ Subgroup.centralizer (Fb : Set S))
    (hsub : IsSubnormal H (Subgroup.centralizer (Fb : Set S)))
    (hq : CFSG.Open.IsQuasisimple ↥H) (hdvd : 3 ∣ Nat.card (↥H ⧸ Subgroup.center ↥H)) :
    ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F := by
  refine ⟨Subgroup.map (MulAut.conj : S →* MulAut S) Fb, ?_, ?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.map_mono hF
  · rw [Subgroup.card_map_of_injective hinj]
    exact h9
  · exact isGood_three_of_quasisimple (centralizer_eq_iInf_fixSubgroup_map Fb) hH hsub hq hdvd

theorem three_le_pRank_top [Finite S] {E : Subgroup S} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 27) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card S, ?_⟩ ⟨E, le_top, hE, ?_⟩
  · rintro k ⟨F, -, -, hk⟩
    have h1 : Nat.card F ≤ Nat.card S := Subgroup.card_le_card_group F
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    rw [hk] at h1
    omega
  · rw [hc]
    norm_num

end Transfer

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
