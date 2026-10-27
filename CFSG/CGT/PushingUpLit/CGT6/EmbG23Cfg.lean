module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Bridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Blueprint

theorem eq_one_of_mem_center_sl2' {K : Type*} [Field K] [CharP K 2]
    {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h2 : r ^ 2 = 1 := by simpa using hr
  have h3 : (r + 1) ^ 2 = 0 := by
    rw [add_sq, h2, one_pow, mul_one, CharTwo.two_eq_zero, zero_mul, add_zero,
      CharTwo.add_self_eq_zero]
  have h4 : r = 1 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    rw [CharTwo.add_eq_zero] at this
    exact this
  subst h4
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem card_center_of_ySL3 {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)} (hY : YSL Y 3) :
    Nat.card Y = 504 ∧ ∀ z ∈ Subgroup.center ↥Y, z = 1 := by
  obtain ⟨e⟩ := hY
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 3 (by omega)]
    norm_num
  · intro z hz
    have hz' : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (Fq 3)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨w, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
    exact e.injective (by rw [eq_one_of_mem_center_sl2' hz', map_one])

section Main


theorem end412_generation_of_pinned (hpin : EmbG23.G23Pinned EmbG23.phi) {V : Type}
    [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y) (hY : YSL Y 3)
    (hout : OuterT G T Y) (hm : ChevalleyExceptionalModel (LayerQ G Y) .G2 3 1)
    (S : Subgroup (MulAut V)) (hSY : S ≤ Y) (hS8 : Nat.card S = 8) :
    ∃ g ∈ conjClosure Y G, g ∈ Subgroup.normalizer (S : Set (MulAut V)) ∧
      Y ⊔ Y.map (MulAut.conj g).toMonoidHom = conjClosure Y G := by
  obtain ⟨t, htT, ht2, htL⟩ := hout
  obtain ⟨hY504, hcenterY⟩ := card_center_of_ySL3 hY
  have hYC := h.adm.hYC
  have hYG : Y ≤ G := fun y hy => (Subgroup.mem_inf.1 (hYC hy)).1
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hYL : Y ≤ conjClosure Y G := le_conjClosure
  have htG : t ∈ G := h.adm.hTG htT
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2, pow_two] at this
    exact this
  have hnorm : ∀ x, x ∈ conjClosure Y G ↔ t * x * t⁻¹ ∈ conjClosure Y G :=
    Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure htG)
  have hperfL : Group.IsPerfect ↥(conjClosure Y G) := ⟨h.quasi.1⟩
  have hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.2 h.adm.hperf
  have hodd : ∀ z ∈ Subgroup.center ↥(conjClosure Y G), Odd (orderOf z) := by
    intro z hz
    have h1 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥(conjClosure Y G))) ∣
        Nat.card ↥(Subgroup.center ↥(conjClosure Y G)) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥(conjClosure Y G))) = orderOf z :=
      Subgroup.orderOf_mk z hz
    rw [h2] at h1
    exact Odd.of_dvd_nat h.oddZ h1
  have hC : ∀ c ∈ G, (∀ x ∈ conjClosure Y G, c * x = x * c) → c ∈ conjClosure Y G := by
    intro c hcG hc
    have hmem : (⟨c, hcG⟩ : ↥G) ∈ Subgroup.centralizer
        ((generalizedFitting ↥G : Subgroup ↥G) : Set ↥G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      rw [h.fstar] at hf
      have hfL : (f : MulAut V) ∈ conjClosure Y G := hf
      exact Subtype.ext (hc _ hfL).symm
    have := centralizer_generalizedFitting_le ↥G hmem
    rw [h.fstar] at this
    exact this
  have htY : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hYC hy)).2 t htT
  have hYZ : ∀ y : ↥(conjClosure Y G), (y : MulAut V) ∈ Y → y ∈ Subgroup.center ↥(conjClosure Y G) →
      y = 1 := by
    intro y hy hyc
    have hz : (⟨(y : MulAut V), hy⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h2 := Subgroup.mem_center_iff.1 hyc ⟨(w : MulAut V), hYL w.2⟩
      have h3 : (w : MulAut V) * y = y * w := congrArg Subtype.val h2
      exact Subtype.ext h3
    have h1 := hcenterY _ hz
    have h4 : (y : MulAut V) = 1 := congrArg Subtype.val h1
    exact Subtype.ext h4
  exact EmbG23.generation_of_outer_cfg hpin hodd hLG htG htt htL hC hnorm hYL hSY hY504 hS8 htY
    hYZ hm

end Main

end CFSG.CGT.PushingUpLit.CGT6
