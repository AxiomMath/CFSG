module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.IndexTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem false_of_cube_contains_a (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) {E : Subgroup G}
    (hE : IsElemTwo 3 E) (haE : a ∈ E)
    (hAll : ∀ t ∈ E, t ^ 2 = 1 → t ≠ 1 → IsConj a t) : False := by
  have hcomm : IsMulCommutative ↥E := hE.1.1
  have hsq : ∀ x ∈ E, x ^ 2 = 1 := hE.1.2
  have hcard8 : Nat.card E = 8 := by rw [hE.2]; norm_num
  have hcommG : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hcomm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEGx : E ≤ Gx a := by
    intro x hx
    rw [mem_Gx]
    exact hcommG a haE x hx
  have hnot_le_zp : ¬ E ≤ Subgroup.zpowers a := by
    intro hle
    have hzple : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.mpr haE
    have hEq : E = Subgroup.zpowers a := le_antisymm hle hzple
    have h2 : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers, h.orderOf_a]
    rw [hEq] at hcard8
    omega
  have hb_exists : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    apply hnot_le_zp
    intro x hx
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  obtain ⟨b, hbE, hbzp⟩ := hb_exists
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hsq a haE
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hsq b hbE
  have hb1 : b ≠ 1 := by
    intro h1
    exact hbzp (by rw [h1]; exact Subgroup.one_mem _)
  have hba : b ≠ a := by
    intro h1
    exact hbzp (by rw [h1]; exact Subgroup.mem_zpowers a)
  let K : Subgroup G := Subgroup.closure ({a, b} : Set G)
  have hKle : K ≤ E := by
    show Subgroup.closure ({a, b} : Set G) ≤ E
    refine (Subgroup.closure_le E).mpr ?_
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haE
    · exact hbE
  have hKcard : Nat.card K = 4 := by
    have hcomm_ab : a * b = b * a := hcommG a haE b hbE
    have ha1 : a ≠ 1 := by
      intro h1
      have ho := h.orderOf_a
      rw [h1, orderOf_one] at ho
      exact (by decide : (1 : ℕ) ≠ 2) ho
    have hne_ab : a ≠ b := fun h1 => hba h1.symm
    simpa [K] using card_closure_pair (hsq a haE) (hsq b hbE) hcomm_ab ha1 hb1 hne_ab
  have hKne : K ≠ E := by
    intro hEq
    have hcard_eq : Nat.card K = Nat.card E := by rw [hEq]
    omega
  have hc_exists : ∃ c ∈ E, c ∉ K := by
    by_contra hcon
    apply hKne
    apply le_antisymm hKle
    intro x hx
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  obtain ⟨c, hcE, hcK⟩ := hc_exists
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hc1 : c ≠ 1 := by
    intro h1
    exact hcK (by rw [h1]; exact K.one_mem)
  have hca : c ≠ a := by
    intro h1
    exact hcK (by rw [h1]; exact haK)
  have hbc1 : b * c ≠ 1 := by
    intro h1
    have hc_eq : c = b := by
      have h2 : b * c = b * b := h1.trans hb2.symm
      exact mul_left_cancel h2
    exact hcK (by rw [hc_eq]; exact hbK)
  have hbca : b * c ≠ a := by
    intro h1
    have hc_eq : c = b * a := by
      have h2 : b * (b * c) = b * a := by rw [h1]
      rwa [← mul_assoc, hb2, one_mul] at h2
    exact hcK (by rw [hc_eq]; exact K.mul_mem hbK haK)
  have hab1 : a * b ≠ 1 := by
    intro h1
    have hb_eq : b = a := by
      have h2 : a * b = a * a := h1.trans ha2.symm
      exact mul_left_cancel h2
    exact hbzp (by rw [hb_eq]; exact Subgroup.mem_zpowers a)
  have hac1 : a * c ≠ 1 := by
    intro h1
    have hc_eq : c = a := by
      have h2 : a * c = a * a := h1.trans ha2.symm
      exact mul_left_cancel h2
    exact hca hc_eq
  have habc1 : a * (b * c) ≠ 1 := by
    intro h1
    have hbc_eq : b * c = a := by
      have h2 : a * (b * c) = a * a := h1.trans ha2.symm
      exact mul_left_cancel h2
    exact hbca hbc_eq
  have hb_conj : IsConj a b := hAll b hbE (hsq b hbE) hb1
  have hab_conj : IsConj a (a * b) :=
    hAll (a * b) (E.mul_mem haE hbE) (hsq (a * b) (E.mul_mem haE hbE)) hab1
  have hc_conj : IsConj a c := hAll c hcE (hsq c hcE) hc1
  have hac_conj : IsConj a (a * c) :=
    hAll (a * c) (E.mul_mem haE hcE) (hsq (a * c) (E.mul_mem haE hcE)) hac1
  have hbc_conj : IsConj a (b * c) :=
    hAll (b * c) (E.mul_mem hbE hcE) (hsq (b * c) (E.mul_mem hbE hcE)) hbc1
  have habc_conj : IsConj a (a * (b * c)) :=
    hAll (a * (b * c)) (E.mul_mem haE (E.mul_mem hbE hcE))
      (hsq (a * (b * c)) (E.mul_mem haE (E.mul_mem hbE hcE))) habc1
  have hbD : b ∉ derivedOf (Gx a) := not_mem_derivedOf_of_isConj hI h hF1 hb_conj hab_conj hba
  have hcD : c ∉ derivedOf (Gx a) := not_mem_derivedOf_of_isConj hI h hF1 hc_conj hac_conj hca
  have hbcD : b * c ∉ derivedOf (Gx a) :=
    not_mem_derivedOf_of_isConj hI h hF1 hbc_conj habc_conj hbca
  have hbGx : b ∈ Gx a := hEGx hbE
  have hcGx : c ∈ Gx a := hEGx hcE
  exact hbcD (mul_mem_derivedOf_of_not_mem h hbGx hcGx hbD hcD)

theorem no_cube_of_fusion1 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) :
    ¬ ∃ E : Subgroup G, IsElemTwo 3 E ∧ ∀ t ∈ E, t ^ 2 = 1 → t ≠ 1 → IsConj a t := by
  rintro ⟨E, hE, hAll⟩
  have hcomm : IsMulCommutative ↥E := hE.1.1
  have hsq : ∀ x ∈ E, x ^ 2 = 1 := hE.1.2
  have hcard8 : Nat.card E = 8 := by rw [hE.2]; norm_num
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard8
    omega
  obtain ⟨e, heE, he1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hEne
  have he_sq : e ^ 2 = 1 := hsq e heE
  have he_conj : IsConj a e := hAll e heE he_sq he1
  obtain ⟨c, hc⟩ := isConj_iff.mp he_conj
  have ha_eq : c⁻¹ * e * c = a := by
    rw [← hc]; group
  let g : G := c⁻¹
  let f : G →* G := (MulAut.conj g).toMonoidHom
  let E' : Subgroup G := E.map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact (MulAut.conj g).injective hxy
  have hE' : IsElemTwo 3 E' := isElemTwo_map f hf_inj hE
  have haE' : a ∈ E' := by
    refine Subgroup.mem_map.mpr ⟨e, heE, ?_⟩
    show f e = a
    show (MulAut.conj g) e = a
    rw [MulAut.conj_apply]
    simpa [g] using ha_eq
  have hAll' : ∀ t ∈ E', t ^ 2 = 1 → t ≠ 1 → IsConj a t := by
    intro t ht ht2 ht1
    obtain ⟨y, hyE, hyf⟩ := Subgroup.mem_map.mp ht
    have hy1 : y ≠ 1 := by
      intro h1
      apply ht1
      rw [← hyf, h1, map_one]
    have hy2 : y ^ 2 = 1 := by
      apply hf_inj
      rw [map_pow, hyf, ht2, map_one]
    have hconj_y : IsConj a y := hAll y hyE hy2 hy1
    have hconj_yt : IsConj y t := by
      refine isConj_iff.mpr ⟨g, ?_⟩
      simpa [f, MulAut.conj_apply] using hyf
    exact hconj_y.trans hconj_yt
  exact false_of_cube_contains_a hI h hF1 hE' haE' hAll'

end CFSG.EvenSporadicStandard.HNRecog.Section3
