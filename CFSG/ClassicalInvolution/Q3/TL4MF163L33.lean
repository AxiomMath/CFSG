module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallL33
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallU33

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups

theorem tightActs3_of_good {Y : Type} [Group Y] {R : Subgroup Y} {t : Y}
    (h : GoodThreeElement R t) : TightActs3 R t := by
  obtain ⟨x, k, hx, hk, hr, -⟩ := h
  exact ⟨x, k, hx, hk, hr⟩

section L33

open CFSG.GH74.KGroups.L33

theorem good_l33
    (X : Subgroup (Equiv.Perm (Fin 26)))
    (hPX : QP.originalSubgroup ≤ X) (hXA : X ≤ QA.originalSubgroup) {R : Subgroup ↥X}
    {S : Sylow 2 R} {t : ↥X} (hd : TightDatum R S t) (hc : TightCls ↥X R S t) :
    GoodThreeElement R t := by
  have hP : Nat.card QP.originalSubgroup = 5616 := by rw [card_group QP QP_ok, QP_valid.2]
  have hA : Nat.card QA.originalSubgroup = 11232 := by rw [card_group QA QA_ok, QA_valid.2]
  obtain ⟨k, hk⟩ : 5616 ∣ Nat.card X := hP ▸ Subgroup.card_dvd_of_le hPX
  have h2 : Nat.card X ∣ 11232 := hA ▸ Subgroup.card_dvd_of_le hXA
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5616) (by simpa using h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  · have hXP : QP.originalSubgroup = X := Subgroup.eq_of_le_of_card_ge hPX (by rw [hk, hP])
    subst hXP
    refine good_of_goodCheck (ι := QP.originalSubgroup.subtype) Subtype.val_injective
      (fun m => ?_) l33_check_9741 hd hc.1
    rw [mem_elemsT QP QP_ok m]
    exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  · have hXA' : X = QA.originalSubgroup := Subgroup.eq_of_le_of_card_ge hXA (by rw [hk, hA])
    subst hXA'
    set N : Subgroup QA.originalSubgroup := QP.originalSubgroup.subgroupOf QA.originalSubgroup
      with hNdef
    have hNcard : Nat.card N = 5616 := by
      rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hP]
    have hidx : N.index = 2 := by
      have h := Subgroup.card_mul_index N
      rw [hNcard, hA] at h
      omega
    have hN : N.Normal := Subgroup.normal_of_index_eq_two hidx
    have hNtop : N ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hidx
      omega
    exact good_of_goodOrInner hN hNtop hd hc (l33_goodOrInner t hd.order)

theorem l33_P_le_A : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, l33_QA_closure]
  exact Subgroup.closure_mono fun x hx => by
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem tightActs3_of_l33
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) (eK : ↥N ≃* QP.originalSubgroup)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t) :
    TightActs3 R t := by
  obtain ⟨M, hMP, hMA⟩ := autModel (MulEquiv.refl QP.originalSubgroup)
  have hPA : M.P ≤ M.A := by rw [hMP, hMA]; exact l33_P_le_A
  let E := MonoidHom.ofInjective (realize_injective N eK M hC)
  obtain ⟨S', hSS, hS₀⟩ := exists_sylow_map_equiv E S
  have h1 : QP.originalSubgroup ≤ (realize N eK M).range :=
    hMP.symm.le.trans (le_realize_range N eK M hPA)
  have h2 : (realize N eK M).range ≤ QA.originalSubgroup :=
    (realize_range_le N eK M).trans hMA.le
  exact tightActs3_of_good (GoodThreeElement.of_map_equiv E (good_l33 _ h1 h2
    (TightDatum.map_equiv E hd hSS hS₀) (TightCls.map_equiv E hc hSS)))

theorem tightActs3_of_equiv_l33
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* QP.originalSubgroup) {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t) : TightActs3 R t := by
  refine tightActs3_of_good (good_of_goodCheck (ι := QP.originalSubgroup.subtype.comp
    e.toMonoidHom) (Subtype.val_injective.comp e.injective) (fun m => ?_) l33_check_9741 hd hc.1)
  rw [mem_elemsT QP QP_ok m]
  exact ⟨fun hm => ⟨e.symm ⟨m, hm⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (e y).2⟩

end L33

section U33

open CFSG.GH74.KGroups.U33

theorem tightActs3_of_equiv_u33
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* QP.originalSubgroup) {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightCls Y R S t) : TightActs3 R t := by
  refine tightActs3_of_good (good_of_goodCheck (ι := QP.originalSubgroup.subtype.comp
    e.toMonoidHom) (Subtype.val_injective.comp e.injective) (fun m => ?_) u33_check_9743 hd hc.1)
  rw [mem_elemsT QP QP_ok m]
  exact ⟨fun hm => ⟨e.symm ⟨m, hm⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (e y).2⟩

end U33

end CFSG.ClassicalInvolution.Q3.TL4.MF163
