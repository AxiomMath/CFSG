module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.FixedIndex
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Rel
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriConf.LocalData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type} [Group G] [Finite G]

namespace TriData

variable {S : Setting G} {g : G} (T : TriData S g)

theorem triLocal (H : Hyp4 S g) (i0 : Fin 3)
    (htrans : ∀ k : Fin 3, ∃ x : S.Mbar, T.perm x k ≠ k) :
    TriConf.TriLocal S g (T.l i0) (eb T.σ i0)
      (S.Mbar ⊓ normalizer (zpowers (eb T.σ i0) : Set S.O)) := by
  classical
  let k : S.O := eb T.σ i0
  let t : S.O := T.l i0
  let M1 : Subgroup S.O := S.Mbar ⊓ normalizer (zpowers k : Set S.O)
  change TriConf.TriLocal S g t k M1
  have hkM : k ∈ S.Mbar := T.e_mem_Mbar i0
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g (T.l_mem i0)
  have hk3 : k ^ 3 = 1 := T.e_pow_three i0
  have hkne : k ≠ 1 := T.e_ne_one i0
  have hksq : k * k = k⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa [pow_succ, pow_two, mul_assoc] using hk3)
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem (T.l_mem i0)
  have ht1 : t ≠ 1 := T.l_ne_one i0
  have htinv : t * k * t⁻¹ = k⁻¹ := T.l_conj_e i0
  have hconj : ∀ x ∈ M1, ∀ y ∈ zpowers k, x * y * x⁻¹ ∈ zpowers k := by
    intro x hx y hy
    exact (Subgroup.mem_normalizer_iff.mp hx.2 y).mp hy
  have hcomm : ∀ x ∈ M1, x * t * x⁻¹ * t⁻¹ ∈ zpowers k := by
    intro x hx
    have hpi : T.perm ⟨x, hx.1⟩ i0 = i0 :=
      (T.mem_normalizer_iff ⟨x, hx.1⟩ i0).mp hx.2
    exact T.comm_mem_zpowers ⟨x, hx.1⟩ hpi
  have hnc : ∃ x ∈ M1, x * t * x⁻¹ ≠ t := by
    refine ⟨k, ⟨hkM, Subgroup.le_normalizer (Subgroup.mem_zpowers k)⟩, ?_⟩
    intro hconjkt
    have hcommkt : k * t = t * k := by
      have h := congrArg (fun z => z * k) hconjkt
      simpa [mul_assoc] using h
    have hkt : t * k * t⁻¹ = k := by
      calc t * k * t⁻¹ = k * t * t⁻¹ := by rw [← hcommkt]
        _ = k := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hkeq : k = k⁻¹ := hkt.symm.trans htinv
    have hk2 : k * k = 1 := by
      nth_rewrite 1 [hkeq]
      exact inv_mul_cancel k
    have hk1 : k = 1 := by
      have h := hk3
      rwa [pow_succ, pow_two, hk2, one_mul] at h
    exact hkne hk1
  have hk_conj : ∀ x ∈ M1, x * k * x⁻¹ = k ∨ x * k * x⁻¹ = k⁻¹ := by
    intro x hx
    have hmem : x * k * x⁻¹ ∈ zpowers k :=
      (Subgroup.mem_normalizer_iff.mp hx.2 k).mp (Subgroup.mem_zpowers k)
    have hne : x * k * x⁻¹ ≠ 1 := by
      intro h1
      have h2 : k = 1 := by
        have h := congrArg (fun z => x⁻¹ * z * x) h1
        simpa [mul_assoc] using h
      exact hkne h2
    have hord : orderOf k = 3 := orderOf_eq_prime hk3 hkne
    have hmem' := (isOfFinOrder_of_finite k).mem_zpowers_iff_mem_range_orderOf.mp hmem
    rw [hord] at hmem'
    simp only [Finset.mem_image, Finset.mem_range] at hmem'
    obtain ⟨n, hn, hnk⟩ := hmem'
    interval_cases n
    · simp at hnk
      exact absurd hnk.symm hne
    · left
      simpa using hnk.symm
    · right
      calc x * k * x⁻¹ = k ^ 2 := hnk.symm
        _ = k * k := pow_two k
        _ = k⁻¹ := hksq
  have hDM : zpowers k ≤ M1 :=
    le_inf (Subgroup.zpowers_le.mpr hkM) Subgroup.le_normalizer
  have ht_norm : t ∈ normalizer (zpowers k : Set S.O) := by
    refine S4.mem_normalizer_of_conj_le (P := zpowers k) (y := t) ?_
    intro p hp
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← conj_zpow, htinv, inv_zpow]
    exact (Subgroup.zpowers k).inv_mem
      (Subgroup.zpow_mem (Subgroup.zpowers k) (Subgroup.mem_zpowers k) n)
  have hmul : ∀ {x : S.O}, x ∈ M1 →
      ∃ s ∈ zpowers k ⊔ zpowers t,
        ∃ c ∈ S.Mbar ⊓ centralizer ((zpowers k ⊔ zpowers t : Subgroup S.O) : Set S.O),
          x = s * c := by
    intro x hx
    obtain ⟨s, hs, c, hc, rfl⟩ :=
      S7.exists_sigma_mul_cent (M := M1) (D := zpowers k) (t := t)
        hDM (T.card_zpowers_e i0) hconj ⟨htM, ht_norm⟩ htt ht1
        (fun y hy => hcomm y hy) hnc hx
    exact ⟨s, hs, c, ⟨hc.1.1, hc.2⟩, rfl⟩
  exact
    { k_mem := hkM
      k_ne := hkne
      k_cube := hk3
      k_conj := hk_conj
      t_inv := htinv
      fpf := T.e_fpf i0
      mul_Cbar := hmul
      rel := T.s2Rel H i0 htrans }

theorem card_Mbar_eq (htrans : ∀ k : Fin 3, ∃ x : S.Mbar, T.perm x k ≠ k) :
    Nat.card S.Mbar = 648 ∨ Nat.card S.Mbar = 1296 := by
  have h : ∀ k : Fin 3, ∃ x ∈ T.perm.range, x k ≠ k := by
    intro k
    obtain ⟨x, hx⟩ := htrans k
    exact ⟨T.perm x, ⟨x, rfl⟩, hx⟩
  rcases perm3_card_of_forall_moved (H := T.perm.range) h with h3 | h6
  · left
    rw [T.card_Mbar, h3]
  · right
    rw [T.card_Mbar, h6]

end TriData

theorem exists_triLocal {S : Setting G} (hw : S.width = 4) (hnoAll : S11.NoA2All S)
    (hirr : ¬ S.IsReducible) {g : G} (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht)
    (hiso : ¬ ∃ q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2), timmesfeldNondegenerate q ∧
      (Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
        Nonempty (S.Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)))
    (hT : TrialityConfig S g t) :
    ∃ (k : S.O) (M1 : Subgroup S.O), TriConf.TriLocal S g t k M1 ∧
      (Nat.card S.Mbar = 648 ∨ Nat.card S.Mbar = 1296) := by
  obtain ⟨T⟩ := nonempty_triData hw hirr H C hT.1 hT.2.1
  obtain ⟨i0, rfl⟩ := T.exists_eq_l H C ht ht1 hVQ hΩ h4 hplus
  have htrans : ∀ k : Fin 3, ∃ x : S.Mbar, T.perm x k ≠ k := by
    by_contra h
    push Not at h
    obtain ⟨k0, hk0⟩ := h
    exact hiso (T.iso_of_fixed hw hnoAll H C hk0)
  exact ⟨eb T.σ i0, _, T.triLocal H i0 htrans, T.card_Mbar_eq htrans⟩

end CFSG.GF2Type.Smith1979.TriPlus

end
