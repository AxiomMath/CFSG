module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79Model
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec79_Y_dichotomy [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76)
    (hP : Asc82Tab6P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {x : G} (hx : x ∈ S ⊓ centralizer (B : Set G)) :
    x ∈ zpowers t ⊔ B ∨ ∃ b ∈ B, ∃ α : ℤˣ, InducesTypeSome L (x * b⁻¹) 6 1 1 α := by
  have hxC : x ∈ centralizer ({t} : Set G) := hc.ctx.sylow.1 hx.1
  have hxN : x ∈ normalizer (L : Set G) := hc.ctx.cent_le_normalizer h36 x hxC
  have hxB : ∀ b ∈ B, x * b = b * x :=
    fun b hb => (Subgroup.mem_centralizer_iff.mp hx.2 b hb).symm
  rcases hP.cent_B G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B hc.normalE16
      x hxN hxB with ⟨b, hb, hbC⟩ | ⟨b, hb, htype, _⟩
  · left
    have hbS : b ∈ S := (hc.normalE16.1 hb).1
    have hxb : x * b⁻¹ ∈ zpowers t := by
      rw [h76 G t L S z hc.ctx]
      exact ⟨S.mul_mem hx.1 (S.inv_mem hbS), hbC⟩
    have hxeq : x = (x * b⁻¹) * b := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hxb hb
  · exact Or.inr ⟨b, hb, htype⟩

theorem sec79_Y_sq [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {x : G} (hx : x ∈ S ⊓ centralizer (B : Set G))
    (hxA : x ∉ ASub S B) : x * x = t := by
  have hxnot : x ∉ zpowers t ⊔ B := by
    rw [← h78 G t L S z g B hc]
    exact hxA
  rcases sec79_Y_dichotomy h36 h76 hP hc hx with hxsup | ⟨b, hb, α, htype⟩
  · exact absurd hxsup hxnot
  · set r : G := x * b⁻¹ with hr
    have htype' : InducesTypeSome L r 6 1 1 α := by rw [hr]; exact htype
    have hrC : r * r ∈ centralizer (L : Set G) :=
      inducesTypeSome_sq_mem_centralizer (hP.center_triv G L hc.ctx.isOm6P) htype'
    have hbxb : Commute b (x * b⁻¹) := by
      have hbx : Commute b x := Subgroup.mem_centralizer_iff.mp hx.2 b hb
      exact hbx.mul_right (Commute.inv_right_self b)
    have hrb : r * b = b * r := by
      rw [hr]
      exact hbxb.eq.symm
    have hbb : b * b = 1 :=
      CFSG.Open.IsElemAbelian.mul_self_eq_one hc.normalE16.2.1.1 hb
    have hxr : x = r * b := by
      rw [hr]
      group
    have hxx : x * x = r * r := by
      rw [hxr]
      calc (r * b) * (r * b) = r * (b * r) * b := by group
        _ = r * (r * b) * b := by rw [hrb]
        _ = (r * r) * (b * b) := by group
        _ = r * r := by rw [hbb, mul_one]
    have hxxS : x * x ∈ S := S.mul_mem hx.1 hx.1
    have hxxC : x * x ∈ centralizer (L : Set G) := by rw [hxx]; exact hrC
    have hxx_z : x * x ∈ zpowers t := by
      rw [h76 G t L S z hc.ctx]
      exact ⟨hxxS, hxxC⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxx_z
    have hmod : t ^ (k % 2) = t ^ k := by
      simpa [hc.ctx.involution] using zpow_mod_orderOf t k
    have hkmod : t ^ (k % 2) = x * x := hmod.trans hk
    have hxxne : x * x ≠ 1 := by
      intro h1
      apply hxA
      rw [ASub, omega1]
      exact Subgroup.subset_closure ⟨hx, by rw [pow_two]; exact h1⟩
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exact absurd (by rw [← hkmod, h0, zpow_zero]) hxxne
    · rw [← hkmod, h1, zpow_one]

theorem sec79_sq_one_of_mem_A [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {y : G} (hy : y ∈ zpowers t ⊔ B) : y * y = 1 := by
  have ht2 : t ^ 2 = 1 := by
    rw [← hc.ctx.involution]
    exact pow_orderOf_eq_one t
  have hzt : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers t) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) ht2
  have hB : CFSG.Open.IsElemAbelian 2 B := hc.normalE16.2.1.1
  have hcomm : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbS : b ∈ S := (hc.normalE16.1 hb).1
    have htb : t * b = b * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hc.ctx.sylow.1 hbS)).symm
    exact ((show Commute t b from htb).zpow_left k).eq
  have hsup : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers t ⊔ B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hzt hB hcomm
  exact CFSG.Open.IsElemAbelian.mul_self_eq_one hsup hy

theorem sec79_sq_in [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) {y : G} (hy : y ∈ S ⊓ centralizer (B : Set G)) :
    y * y = 1 ∨ y * y = t := by
  by_cases hyA : y ∈ ASub S B
  · left
    have hy' : y ∈ zpowers t ⊔ B := by
      rw [← h78 G t L S z g B hc]
      exact hyA
    exact sec79_sq_one_of_mem_A hc hy'
  · right
    exact sec79_Y_sq h36 h76 hP h78 hc hy hyA

end CFSG.OddStandard.SmallF3.Omega
