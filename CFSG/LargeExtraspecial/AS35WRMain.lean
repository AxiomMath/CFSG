module

public import CFSG.LargeExtraspecial.AS35WRCore
public import CFSG.LargeExtraspecial.AS35WRL3
public import CFSG.LargeExtraspecial.AS35WRU3
public import CFSG.LargeExtraspecial.AS35WMain
public import CFSG.LocalAnalysis.RankTwoShapes.SingleInvolutionClass
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionShapes
public import CFSG.Milestones.LR_semidihedral_simple_recognition
public import CFSG.Walter.TwoRank
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.M11
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

variable {X : Type} [Group X]

theorem W2Data.false_of_comm [Finite X] [IsSimpleGroup X] {z : X} (h : W2Data X z)
    (hcomm : ∀ a b : X, a * b = b * a) : False := by
  obtain ⟨A, hA, hAz, -⟩ := h.aut
  have hz2 := h.orderOf_eq
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hN : (zpowers z).Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have htop : zpowers z = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers z)).resolve_left (by
      rw [zpowers_eq_bot]
      exact hz1)
  have hx : ∀ x : X, x = 1 ∨ x = z := by
    intro x
    have hxz : x ∈ zpowers z := htop ▸ mem_top x
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxz
    rw [← zpow_mod_orderOf, hz2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]
  have hA1 : A = ⊥ := by
    rw [eq_bot_iff_forall]
    intro a ha
    ext x
    rcases hx x with rfl | rfl
    · simp
    · simpa using hAz a ha
  rw [hA1, Subgroup.card_bot] at hA
  exact absurd hA (by norm_num)

theorem eq_three_of_pow_dvd_48 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : p ^ f ∣ 48) : p = 3 ∧ f = 1 := by
  have hp48 : p ∣ 2 ^ 4 * 3 := (dvd_pow_self p (by omega)).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hp48 with h2 | h3
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)) hp2
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    subst hp3
    refine ⟨rfl, ?_⟩
    by_contra hf1
    have h9 : 3 ^ 2 ∣ 3 ^ f := Nat.pow_dvd_pow 3 (by omega)
    have := h9.trans h
    norm_num at this

theorem eq_one_of_central [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (x : X)
    (hx : ∀ y : X, x * y = y * x) : x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hc | hc
  · have hxc : x ∈ center X := mem_center_iff.2 fun y => (hx y).symm
    rwa [hc, mem_bot] at hxc
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ center X := hc ▸ mem_top a
    exact absurd (mem_center_iff.1 ha b).symm hab

theorem false_of_psl3 [Finite X] {z : X}
    (hone : ∀ x : X, orderOf x = 2 → IsConj z x) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hm : CFSG.Open.StatedClassicalModel X .PSL 3 p f)
    (h48 : Nat.card (centralizer ({z} : Set X)) ∣ 48)
    (hAut : 4 * Nat.card X ≤ Nat.card (MulAut X)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := GaloisField p f) 3 p f
    (by omega) hF hm
  have h2F : (2 : GaloisField p f) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : GaloisField p f) = 0 := by rw [Nat.cast_ofNat]; exact h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 h2'))
  have hx₀ : orderOf (e.symm (psl3Inv (GaloisField p f))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_psl3Inv h2F
  have hC : Nat.card (centralizer ({z} : Set X)) =
      Nat.card (centralizer ({psl3Inv (GaloisField p f)} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p f)))) := by
    rw [natCard_centralizer_eq_of_isConj (hone _ hx₀), card_centralizer_map e.symm]
  have hq : p ^ f ∣ 48 := by
    have := card_dvd_card_centralizer_psl3Inv (F := GaloisField p f)
    rw [hF, ← hC] at this
    exact this.trans h48
  obtain ⟨rfl, rfl⟩ := eq_three_of_pow_dvd_48 hp hp2 hf hq
  obtain ⟨e₂⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod 3) 3 3 1 (by norm_num)
    CFSG.GH74.KGroups.L33.card_F hm
  obtain ⟨e₃⟩ := CFSG.GH74.KGroups.L33.equiv_psl_P13
  obtain ⟨e₄⟩ := CFSG.GH74.KGroups.L33.equiv_P13_P
  have hAutX := CFSG.GH74.KGroups.L33.card_mulAut (e₂.trans (e₃.trans e₄))
  have hX : Nat.card X = 5616 := by
    rw [Nat.card_congr e₂.toEquiv, CFSG.GH74.KGroups.L33.card_psl]
  omega

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial in
theorem false_of_psu3 [Finite X] {z : X}
    (hone : ∀ x : X, orderOf x = 2 → IsConj z x) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hq1 : p ^ f % 4 = 1) (hm : CFSG.Open.StatedClassicalModel X .PSU 3 p f)
    (h48 : Nat.card (centralizer ({z} : Set X)) ∣ 48) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hm
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 1) (ε := 1) hU
  let e : X ≃* hypPSU hU 1 1 := e₀.trans (hypPSUEquivStatedProj hU hR₀ (by omega)).symm
  have hx₀ : orderOf (e.symm (psu3Inv hU)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_psu3Inv hU hp2
  have hC : Nat.card (centralizer ({z} : Set X)) =
      Nat.card (centralizer ({psu3Inv hU} : Set (hypPSU hU 1 1))) := by
    rw [natCard_centralizer_eq_of_isConj (hone _ hx₀), card_centralizer_map e.symm]
  have hq : p ^ f ∣ 48 := by
    have := dvd_card_centralizer_psu3Inv hU
    rw [← hC] at this
    exact this.trans h48
  obtain ⟨rfl, rfl⟩ := eq_three_of_pow_dvd_48 hp hp2 hf hq
  norm_num at hq1

theorem false_of_m11
    (e : X ≃* CFSG.Open.StatedM11) (hAut : 4 * Nat.card X ≤ Nat.card (MulAut X)) : False := by
  have hS : Blueprint.NativeSporadic.IsSporadic X .M11 :=
    ⟨e.trans (MulEquiv.subgroupCongr CFSG.Semidihedral.GL2Recognition.statedM11_eq_nativeM11)⟩
  have hAutX := CFSG.GH74.KGroups.M11.card_mulAut hS
  have hX : Nat.card X = 7920 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.GL2Recognition.card_statedM11]
  omega

theorem W2Data.false_of_rankTwo_of_le
    [Finite X] [IsSimpleGroup X] {z : X} (h : W2Data X z)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hrank : Open.twoRank X = 2)
    (hone : ∀ x : X, orderOf x = 2 → IsConj z x) (E : Subgroup X)
    (hE : Open.IsElemAbelian 2 E) (hEz : E ≤ centralizer ({z} : Set X))
    (hEcard : Nat.card E = 4) : False := by
  have hq := h.quatLike hone
  by_cases hA : ∀ r ∈ oTwoCent z, r = 1 ∨ r = z
  · refine h.false_of_four hq (a := 1) (fun r hr => ?_) E hE hEz hEcard
    rcases hA r hr with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  push Not at hA
  obtain ⟨a, haR, ha1, haz⟩ := hA
  have ha : a ^ 2 = z := ((hq.cases a haR).resolve_left ha1).resolve_left haz
  by_cases hB : ∀ r ∈ oTwoCent z, r = 1 ∨ r = z ∨ r = a ∨ r = a * z
  · exact h.false_of_four hq hB E hE hEz hEcard
  push Not at hB
  obtain ⟨b, hbR, hb1, hbz, hba, hbaz⟩ := hB
  have hb : b ^ 2 = z := ((hq.cases b hbR).resolve_left hb1).resolve_left hbz
  have hne : b ≠ a ∧ b ≠ a * z := ⟨hba, hbaz⟩
  have h48 := h.card_centralizer_dvd hq haR hbR ha hb hne
  have hR8 : Nat.card (oTwoCent z) ≤ 8 :=
    Nat.le_of_dvd (by norm_num) (hq.card_dvd_eight (isPGroup_oTwoCent z) haR hbR ha hb hne)
  have hab : a * b ≠ b * a := fun hc => by
    rcases hq.eq_of_commute haR hbR ha hb hc with h1 | h1
    · exact hba h1
    · exact hbaz h1
  have hAut := h.four_mul_card_le (eq_one_of_central hnonab) hR8
  obtain ⟨P, hP⟩ := h.sylow_le
  have hRP := oTwoCent_le_sylow P hP
  have hP48 : Nat.card P ∣ 48 := (Subgroup.card_dvd_of_le hP).trans h48
  rcases RankTwoShapes.rank_two_sylow_shapes hnonab hrank P with
    ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨H, _, U, hH, ⟨e⟩⟩
  ·
    have hsq : ∀ {x : X} (hx : x ∈ (P : Subgroup X)), x ^ 2 = z →
        (⟨x, hx⟩ : (P : Subgroup X)) ^ 2 ≠ 1 := by
      intro x hx hx2 h1
      apply hq.z_ne_one
      rw [← hx2]
      exact congrArg Subtype.val h1
    exact hab (congrArg Subtype.val
      (commute_of_dihedral e (hsq (hRP haR) ha) (hsq (hRP hbR) hb)))
  ·
    rcases CFSG.Milestones.lr_semidihedral_simple_recognition_1 X hnonab ⟨P, n, hn, ⟨e⟩⟩ with
      ⟨p, f, hp, hp2, hf, -, hm⟩ | ⟨p, f, hp, hp2, hf, hq1, hm⟩ | hM
    · exact false_of_psl3 hone hp hp2 hf hm h48 hAut
    · exact false_of_psu3 hone hp hp2 hf hq1 hm h48
    · obtain ⟨e'⟩ := hM
      exact false_of_m11 e' hAut
  ·
    have hcard : Nat.card P = 2 ^ (2 * n + 1) := by
      rw [Nat.card_congr e.toEquiv,
        ComponentClassification.AschbacherKnownGroup.ShapeExclusion.wreath_card]
    have h32 : 2 ^ 5 ∣ 2 ^ (2 * n + 1) := Nat.pow_dvd_pow 2 (by omega)
    rw [← hcard] at h32
    have := h32.trans hP48
    norm_num at this
  ·
    obtain ⟨hK, ⟨eW⟩⟩ :=
      ComponentClassification.AschbacherKnownGroup.ShapeExclusion.unitary_sylow_equiv hH U
    have hcard : Nat.card P = 64 := by
      rw [Nat.card_congr (e.trans eW).toEquiv, RankTwoShapes.UnitaryFourW.natCard_unitaryFourW]
    rw [hcard] at hP48
    norm_num at hP48

theorem W2Data.false_of_rankTwo
    [Finite X] [IsSimpleGroup X] {z : X} (h : W2Data X z)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hrank : Open.twoRank X = 2) : False := by
  have hone : ∀ x : X, orderOf x = 2 → IsConj z x := fun x hx =>
    RankTwoShapes.involutions_isConj_of_twoRank_eq_two hnonab hrank h.orderOf_eq hx
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup X)
  have hE4 : Nat.card E = 4 := by
    rw [hEcard]
    change 2 ^ Open.twoRank X = 4
    rw [hrank]
    norm_num
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨P', hP'⟩ := hE2.exists_le_sylow
  obtain ⟨P, hP⟩ := h.sylow_le
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P'
  have h' := h.map (MulAut.conj g)
  have hone' : ∀ x : X, orderOf x = 2 → IsConj (MulAut.conj g z) x := fun x hx =>
    (isConj_iff.2 ⟨g⁻¹, by simp [MulAut.conj_apply]; group⟩).trans (hone x hx)
  have hEz : E ≤ centralizer ({MulAut.conj g z} : Set X) := by
    intro e he
    rw [mem_centralizer_map_iff]
    have he' : e ∈ ((g • P : Sylow 2 X) : Subgroup X) := hg ▸ hP' he
    rw [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at he'
    have he'' : g⁻¹ * e * g ∈ (P : Subgroup X) := by
      simpa [MulAut.inv_def, MulAut.conj_symm_apply] using he'
    simpa [MulAut.conj_symm_apply] using hP he''
  exact h'.false_of_rankTwo_of_le hnonab hrank hone' E hE hEz hE4

theorem rankTwoW2Input :
    RankTwoW2Input := by
  intro X _ _ _ hr z hz
  by_cases hcomm : ∀ a b : X, a * b = b * a
  · exact hz.false_of_comm hcomm
  push Not at hcomm
  have heven : Even (Nat.card X) := by
    have h2 := orderOf_dvd_natCard z
    rw [hz.orderOf_eq] at h2
    exact even_iff_two_dvd.2 h2
  have h2 := CFSG.Walter.two_le_twoRank X hcomm heven
  exact hz.false_of_rankTwo hcomm (le_antisymm hr h2)

end AS35W

end CFSG.LargeExtraspecial
