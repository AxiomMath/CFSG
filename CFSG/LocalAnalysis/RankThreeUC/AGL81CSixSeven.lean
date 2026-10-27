module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

@[expose] def IsIrreducibleAut {D : Type} [Group D] (W : Subgroup (MulAut D)) : Prop :=
  ∀ B : Subgroup D, (∀ w ∈ W, ∀ b ∈ B, w b ∈ B) → B = ⊥ ∨ B = ⊤

@[expose] def SixSeven : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsMulCommutative D → (∀ x : D, x ^ 3 = 1) →
    Nat.card D = 27 → ∀ W : Subgroup (MulAut D), IsIrreducibleAut W →
      (∃ Di : Fin 3 → Subgroup D, (∀ i, Nat.card (Di i) = 3) ∧ (⨆ i, Di i) = ⊤ ∧
          (∀ w ∈ W, ∀ i, ∃ j, (Di i).map (w : D ≃* D).toMonoidHom = Di j) ∧
          Nat.card W ∣ 48) ∨
        (∃ U : Subgroup (MulAut D), U ≤ W ∧ (U.subgroupOf W).Normal ∧ Nat.card U = 13) ∨
        (∃ U : Subgroup (MulAut D), U ≤ W ∧ (U.subgroupOf W).Normal ∧ IsSLType 3 (ZMod 3) ↥U)

private theorem card_mulAut_of_card_eq_27 {D : Type} [Group D] [Finite D]
    (hDc : IsMulCommutative D) (hD3 : ∀ x : D, x ^ 3 = 1) (hD : Nat.card D = 27) :
    Nat.card (MulAut D) = 11232 := by
  have hcard3 : Nat.card D = 3 ^ 3 := by rw [hD]; norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 3) (W := D) (n := 3) (fun a b => hDc.is_comm.comm a b) hD3 hcard3
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 3) e,
      CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3) 3, Fin.prod_univ_three]
  norm_num

private theorem card_SL_three_zmod_three :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
  rw [Matrix.card_SL_field (n := 3) (𝔽 := ZMod 3), ZMod.card, Fin.prod_univ_three]
  norm_num

theorem mem_of_normalizes_card_eq_thirteen {D : Type} [Group D] [Finite D]
    (hDc : IsMulCommutative D) (hD3 : ∀ x : D, x ^ 3 = 1) (hD : Nat.card D = 27)
    {U : Subgroup (MulAut D)} (hU : Nat.card U = 13) {x : MulAut D}
    (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hx : x ^ 13 = 1) : x ∈ U := by
  by_contra hxnot
  have hxne : x ≠ 1 := fun h => hxnot (h ▸ U.one_mem)
  have h13p : Nat.Prime 13 := by norm_num
  have horder : orderOf x = 13 := by
    have hdvd : orderOf x ∣ 13 := orderOf_dvd_of_pow_eq_one hx
    rcases h13p.eq_one_or_self_of_dvd (orderOf x) hdvd with h1 | h13
    · exact absurd (orderOf_eq_one_iff.mp h1) hxne
    · exact h13
  have hKcard : Nat.card (Subgroup.zpowers x) = 13 := by
    rw [Nat.card_zpowers, horder]
  have hle : U.map (MulAut.conj x) ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact hxU u hu
  have hxnorm : x ∈ Subgroup.normalizer (U : Set (MulAut D)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm)
  have hKle : Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set (MulAut D)) :=
    Subgroup.zpowers_le.mpr hxnorm
  have hdisj : U ⊓ Subgroup.zpowers x = ⊥ := by
    have hcard_inf : Nat.card ↥(U ⊓ Subgroup.zpowers x) = 1 := by
      have hdvd : Nat.card ↥(U ⊓ Subgroup.zpowers x) ∣ 13 := by
        rw [← hKcard]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases h13p.eq_one_or_self_of_dvd _ hdvd with h1 | h13
      · exact h1
      · exfalso
        have heq : U ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h13, hKcard])
        have hKU : Subgroup.zpowers x ≤ U := by
          rw [← heq]; exact inf_le_left
        exact hxnot (hKU (Subgroup.mem_zpowers x))
    exact (Subgroup.eq_bot_iff_card (U ⊓ Subgroup.zpowers x)).mpr hcard_inf
  let f : (↥U) × (↥(Subgroup.zpowers x)) → (↥(U ⊔ Subgroup.zpowers x)) :=
    fun p => ⟨(p.1 : MulAut D) * (p.2 : MulAut D),
      Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u1, k1⟩ ⟨u2, k2⟩ heq
      have h : (u1 : MulAut D) * (k1 : MulAut D) =
          (u2 : MulAut D) * (k2 : MulAut D) := congrArg Subtype.val heq
      have hmem : (u2 : MulAut D)⁻¹ * (u1 : MulAut D) ∈ U ⊓ Subgroup.zpowers x := by
        constructor
        · exact U.mul_mem (U.inv_mem u2.2) u1.2
        · have huk : (u2 : MulAut D)⁻¹ * (u1 : MulAut D) =
              (k2 : MulAut D) * (k1 : MulAut D)⁻¹ := by
            calc (u2 : MulAut D)⁻¹ * (u1 : MulAut D)
                = (u2 : MulAut D)⁻¹ * ((u1 : MulAut D) * (k1 : MulAut D)) *
                    (k1 : MulAut D)⁻¹ := by group
              _ = (u2 : MulAut D)⁻¹ * ((u2 : MulAut D) * (k2 : MulAut D)) *
                    (k1 : MulAut D)⁻¹ := by rw [h]
              _ = (k2 : MulAut D) * (k1 : MulAut D)⁻¹ := by group
          rw [huk]
          exact (Subgroup.zpowers x).mul_mem k2.2 ((Subgroup.zpowers x).inv_mem k1.2)
      rw [hdisj, Subgroup.mem_bot] at hmem
      have h1' : (u1 : MulAut D) = (u2 : MulAut D) := by
        calc (u1 : MulAut D) = (u2 : MulAut D) * ((u2 : MulAut D)⁻¹ * (u1 : MulAut D)) :=
              by group
          _ = (u2 : MulAut D) * 1 := by rw [hmem]
          _ = (u2 : MulAut D) := mul_one _
      have h2' : (k1 : MulAut D) = (k2 : MulAut D) := by
        have hh := h
        rw [h1'] at hh
        exact mul_left_cancel hh
      exact Prod.ext (Subtype.ext h1') (Subtype.ext h2')
    · intro h
      have hh : (h : MulAut D) ∈ (↑(U ⊔ Subgroup.zpowers x) : Set (MulAut D)) := h.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left U (Subgroup.zpowers x) hKle,
        Set.mem_mul] at hh
      rcases hh with ⟨u, hu, k, hk, huk⟩
      exact ⟨(⟨u, hu⟩, ⟨k, hk⟩), Subtype.ext huk⟩
  have hcardH : Nat.card (↥(U ⊔ Subgroup.zpowers x)) = 169 := by
    have h1 : Nat.card (↥(U ⊔ Subgroup.zpowers x)) =
        Nat.card ((↥U) × (↥(Subgroup.zpowers x))) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    rw [h1, Nat.card_prod, hU, hKcard]
  have hdvd : 169 ∣ Nat.card (MulAut D) := by
    rw [← hcardH]
    exact Subgroup.card_subgroup_dvd_card (U ⊔ Subgroup.zpowers x)
  rw [card_mulAut_of_card_eq_27 hDc hD3 hD] at hdvd
  exact (by norm_num : ¬ (169 ∣ 11232)) hdvd

theorem eq_of_normal_isSLType_of_pow_thirteen {D : Type} [Group D] [Finite D]
    (hDc : IsMulCommutative D) (hD3 : ∀ x : D, x ^ 3 = 1) (hD : Nat.card D = 27)
    {W U : Subgroup (MulAut D)} (hUW : U ≤ W) (hU : IsSLType 3 (ZMod 3) ↥U) {S : Set (MulAut D)}
    (hS : ∀ x ∈ S, x ^ 13 = 1) (hWS : W = Subgroup.closure S) : W = U := by
  obtain ⟨eU⟩ := hU
  have hUcard : Nat.card U = 5616 := by
    rw [Nat.card_congr eU.toEquiv, card_SL_three_zmod_three]
  have hindex : U.index = 2 := by
    rw [Subgroup.index_eq_card_div, hUcard, card_mulAut_of_card_eq_27 hDc hD3 hD]
  haveI : U.Normal := Subgroup.normal_of_index_eq_two hindex
  have hxU : ∀ x ∈ S, x ∈ U := by
    intro x hxS
    rw [← QuotientGroup.eq_one_iff (N := U) x]
    apply orderOf_eq_one_iff.mp
    change orderOf (QuotientGroup.mk' U x) = 1
    have h13 : orderOf (QuotientGroup.mk' U x) ∣ 13 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hS x hxS, map_one]
    have h2 : orderOf (QuotientGroup.mk' U x) ∣ 2 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk' U x)
      rwa [← Subgroup.index_eq_card U, hindex] at h
    have hgcd : orderOf (QuotientGroup.mk' U x) ∣ 1 := by
      have := Nat.dvd_gcd h13 h2
      rwa [show Nat.gcd 13 2 = 1 by norm_num] at this
    exact Nat.dvd_one.mp hgcd
  apply le_antisymm _ hUW
  rw [hWS]
  exact (Subgroup.closure_le U).mpr hxU

theorem sixSeven_of_pow_thirteen (h67 : SixSeven) {D : Type} [Group D] [Finite D]
    (hDc : IsMulCommutative D) (hD3 : ∀ x : D, x ^ 3 = 1) (hD : Nat.card D = 27)
    {W : Subgroup (MulAut D)} (hW : IsIrreducibleAut W) {S : Set (MulAut D)}
    (hS : ∀ x ∈ S, x ^ 13 = 1) (hWS : W = Subgroup.closure S) :
    Nat.card W = 13 ∨ IsSLType 3 (ZMod 3) ↥W := by
  rcases h67 D hDc hD3 hD W hW with ⟨_, _, _, _, hW48⟩ | hcase2 | hcase3
  · exfalso
    have hWbot : W = ⊥ := by
      have hSe : ∀ y ∈ S, y ∈ (⊥ : Subgroup (MulAut D)) := by
        intro y hy
        have hyW : y ∈ W := by rw [hWS]; exact Subgroup.subset_closure hy
        have h13 : orderOf y ∣ 13 := orderOf_dvd_of_pow_eq_one (hS y hy)
        have hW' : orderOf y ∣ Nat.card W := by
          rw [← Nat.card_zpowers y]
          exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyW)
        have h48 : orderOf y ∣ 48 := dvd_trans hW' hW48
        have hgcd : orderOf y ∣ 1 := by
          have := Nat.dvd_gcd h13 h48
          rwa [show Nat.gcd 13 48 = 1 by norm_num] at this
        rw [Subgroup.mem_bot]
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
      rw [hWS]
      exact le_bot_iff.mp ((Subgroup.closure_le ⊥).mpr hSe)
    have h3dvd : 3 ∣ Nat.card D := by rw [hD]; norm_num
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 h3dvd
    let B : Subgroup D := Subgroup.zpowers g
    have hBcard : Nat.card B = 3 := by
      change Nat.card (Subgroup.zpowers g) = 3
      rw [Nat.card_zpowers, hg]
    have hBinv : ∀ w ∈ W, ∀ b ∈ B, w b ∈ B := by
      intro w hw b hb
      have hw1 : w = 1 := by
        have := hw
        rw [hWbot, Subgroup.mem_bot] at this
        exact this
      rw [hw1]
      simpa using hb
    rcases hW B hBinv with hBbot | hBtop
    · rw [hBbot, Subgroup.card_bot] at hBcard
      exact (by norm_num : (1 : ℕ) ≠ 3) hBcard
    · rw [hBtop, Subgroup.card_top, hD] at hBcard
      exact (by norm_num : (27 : ℕ) ≠ 3) hBcard
  · obtain ⟨U, hUW, hUnorm, hU13⟩ := hcase2
    left
    have hWU : W = U := by
      apply le_antisymm _ hUW
      rw [hWS]
      apply (Subgroup.closure_le U).mpr
      intro y hy
      have hyW : y ∈ W := by rw [hWS]; exact Subgroup.subset_closure hy
      refine mem_of_normalizes_card_eq_thirteen hDc hD3 hD hU13 ?_ (hS y hy)
      intro u hu
      have huW : u ∈ W := hUW hu
      have hconj := hUnorm.conj_mem (⟨u, huW⟩ : W)
        ((Subgroup.mem_subgroupOf).mpr hu) (⟨y, hyW⟩ : W)
      simpa [Subgroup.mem_subgroupOf] using hconj
    rw [hWU, hU13]
  · obtain ⟨U, hUW, _, hU⟩ := hcase3
    right
    rw [eq_of_normal_isSLType_of_pow_thirteen hDc hD3 hD hUW hU hS hWS]
    exact hU

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
