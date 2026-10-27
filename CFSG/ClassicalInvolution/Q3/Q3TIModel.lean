module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.Q3B1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification
open scoped commutatorElement

theorem normal_le_center_or_eq_top_qs {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  rcases (hN.map π (QuotientGroup.mk'_surjective _)).eq_bot_or_eq_top with h | h
  · left
    intro n hn
    have : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff n).mp this
  · right
    have hlift : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ Subgroup.center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      have h1 : π (n⁻¹ * q) = 1 := by rw [map_mul, map_inv, hnq, inv_mul_cancel]
      exact ⟨n, hn, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [eq_top_iff, ← hQ.1, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨n, hn, hna⟩ := hlift a
    obtain ⟨m, hm, hmb⟩ := hlift b
    have ha : a = n * (n⁻¹ * a) := by group
    have hb : b = m * (m⁻¹ * b) := by group
    have h1 := Subgroup.mem_center_iff.mp hna
    have h2 := Subgroup.mem_center_iff.mp hmb
    have hc : ⁅a, b⁆ = n * m * n⁻¹ * m⁻¹ := by
      rw [ha, hb, commutatorElement_def]
      calc n * (n⁻¹ * a) * (m * (m⁻¹ * b)) * (n * (n⁻¹ * a))⁻¹ * (m * (m⁻¹ * b))⁻¹
          = n * ((n⁻¹ * a) * (m * (m⁻¹ * b)) * (n⁻¹ * a)⁻¹) * n⁻¹ * (m * (m⁻¹ * b))⁻¹ := by
            group
        _ = n * (m * (m⁻¹ * b)) * n⁻¹ * (m * (m⁻¹ * b))⁻¹ := by
            rw [← h1 (m * (m⁻¹ * b)), mul_inv_cancel_right]
        _ = n * m * ((m⁻¹ * b) * (n⁻¹ * (m⁻¹ * b)⁻¹)) * m⁻¹ := by group
        _ = n * m * n⁻¹ * m⁻¹ := by
            rw [← h2 (n⁻¹ * (m⁻¹ * b)⁻¹)]
            group
    rw [hc]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)

section Model


@[expose] def ModelOddAutRigid : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
    ∀ Λ : Set (Subgroup X), InClass3 Λ → LieSystemMod3 Λ →
      ∀ (z : X) (K : Subgroup X), K ∈ Λ → IsClassicalMember3 K z →
        ∀ α : MulAut X, Odd (orderOf α) →
          (∀ c ∈ Subgroup.centralizer ({z} : Set X),
            c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X))) → α = 1

end Model

section Reduction


theorem le_of_almostSimple_member (hRigid : ModelOddAutRigid) {Y : Type} [Group Y] [Finite Y]
    (hBelow : CIT3Below (Nat.card Y)) {z : Y} {L : Subgroup Y} (hz : IsClassicalMember3 L z)
    {T : Subgroup Y} [T.Normal] (hT : IsComponentOf T ⊤)
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) (hK : IsClassicalMember3 (L ⊓ T) z) : L ≤ T := by
  by_cases hTY : T = ⊤
  · rw [hTY]
    exact le_top
  set zT : T := ⟨z, hK.mem.2⟩ with hzT
  have hKT := hK.subgroupOf (inf_le_right : L ⊓ T ≤ T)
  have hqs : CFSG.Open.IsQuasisimple T := hT.2.2
  have hcen : Subgroup.center T = ⊥ := by
    refine eq_bot_iff.mpr fun c hc => ?_
    have hc' : (c : Y) ∈ Subgroup.centralizer (T : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨t, ht⟩)
    rw [hC, Subgroup.mem_bot] at hc'
    exact Subgroup.mem_bot.mpr (Subtype.ext hc')
  have hgen : Subgroup.normalClosure (((L ⊓ T).subgroupOf T : Subgroup T) : Set T) = ⊤ := by
    rcases normal_le_center_or_eq_top_qs hqs (Subgroup.normalClosure_normal) with h | h
    · exfalso
      have h1 := h (Subgroup.subset_normalClosure hKT.mem)
      rw [hcen, Subgroup.mem_bot] at h1
      exact hz.ne_one (congrArg Subtype.val h1)
    · exact h
  have hΛ := Q3B.inClass3_conjClass hKT hgen
  have hcard : Nat.card T < Nat.card Y := by
    rw [← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hTY)
  have hLie := hBelow T hcard _ hΛ
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hCdef
  set OC := Balance.oddCoreIn C with hOC
  have hOT : ((OC ⊓ T).subgroupOf T) ≤
      Balance.oddCoreIn (Subgroup.centralizer ({zT} : Set T)) := by
    refine Balance.le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · intro w hw
      rw [Subgroup.mem_subgroupOf] at hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (Balance.oddCoreIn_le C hw.1)
      exact Subtype.ext this
    · intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have hdC : (d : Y) ∈ C := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hd ⊢
        exact congrArg Subtype.val hd
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Balance.conj_mem_oddCoreIn hdC h1, T.mul_mem (T.mul_mem d.2 h2) (T.inv_mem d.2)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, w.2⟩
        have := Balance.conj_mem_oddCoreIn (C.inv_mem hdC) h1
        simpa [mul_assoc] using this
    · have h1 : Nat.card ((OC ⊓ T).subgroupOf T) = Nat.card (OC ⊓ T : Subgroup Y) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [h1]
      exact (Balance.odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hOL : Balance.oddCoreIn L = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxC : x ∈ OC := Balance.oddCoreIn_le_of_isSubnormal hz.subnormal hx
    have hxodd : Odd (orderOf x) := by
      have h1 := orderOf_dvd_natCard (⟨x, hxC⟩ : OC)
      rw [Subgroup.orderOf_mk] at h1
      exact (Balance.odd_card_oddCoreIn C).of_dvd_nat h1
    set α : MulAut T := MulAut.conjNormal x with hα
    have hαodd : Odd (orderOf α) := hxodd.of_dvd_nat (orderOf_map_dvd _ x)
    have hfix : ∀ c ∈ Subgroup.centralizer ({zT} : Set T),
        c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({zT} : Set T)) := by
      intro c hc
      refine hOT (Subgroup.mem_subgroupOf.mpr ⟨?_, (c⁻¹ * α c).2⟩)
      have hcC : (c : Y) ∈ C := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        exact congrArg Subtype.val hc
      have hval : ((c⁻¹ * α c : T) : Y) = ((c : Y)⁻¹ * x * (c : Y)) * x⁻¹ := by
        simp [hα, MulAut.conjNormal_apply, mul_assoc]
      rw [hval]
      refine OC.mul_mem ?_ (OC.inv_mem hxC)
      have := Balance.conj_mem_oddCoreIn (C.inv_mem hcC) hxC
      simpa [mul_assoc] using this
    have h1 := hRigid T hqs hcen _ hΛ hLie zT _ (Q3B.mem_conjClass_self _) hKT α hαodd hfix
    have hxc : x ∈ Subgroup.centralizer (T : Set Y) := by
      refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
      have h2 := congrArg (fun β : MulAut T => ((β ⟨t, ht⟩ : T) : Y)) h1
      simp only [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc t * x = x * t * x⁻¹ * x := by rw [h2]
        _ = x * t := by group
    rw [hC] at hxc
    exact hxc
  have hOL' : classicalInvolutionOddCore L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hOL
  obtain ⟨e⟩ := hz.nonempty_equiv_sl2 hOL'
  have h24 : Nat.card L = 24 := by rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
  have heq : L ⊓ T = L := Subgroup.eq_of_le_of_card_ge inf_le_left (h24 ▸ hK.card_ge)
  rw [← heq]
  exact inf_le_right

end Reduction

end CFSG.ClassicalInvolution.Q3.Q3T
