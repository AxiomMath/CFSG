module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Pigeon
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Fig

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

private theorem fourBParity_normalizer (H : FourBHyps a z) (P : FourBPair a p q) :
    q ∈ Subgroup.normalizer (Gxy p ((p * q) ^ 2) : Set G) := by
  have hq2 : q * q = 1 := fourB_mul_self_q H P
  have hqq : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  have hb2 : (p * q) ^ 2 * (p * q) ^ 2 = 1 := by
    have h : ((p * q) ^ 2) ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one ((p * q) ^ 2)
      rwa [fourB_orderOf_b H P] at h1
    rwa [pow_two] at h
  have hpb : p * (p * q) ^ 2 = q * p * q := fourB_mul_b_p H P
  have hqb : q * (p * q) ^ 2 = (p * q) ^ 2 * q := fourB_comm_b_q H P
  have hforward : ∀ h ∈ Gxy p ((p * q) ^ 2),
      MulAut.conj q h ∈ Gxy p ((p * q) ^ 2) := by
    intro h hh
    have hp_comm : p * h = h * p := mem_Gx.mp (mem_Gxy.mp hh).1
    have hb_comm : (p * q) ^ 2 * h = h * (p * q) ^ 2 := mem_Gx.mp (mem_Gxy.mp hh).2
    have hcpp : MulAut.conj q p = p * (p * q) ^ 2 := by
      rw [MulAut.conj_apply, hqq]
      exact hpb.symm
    have hcb : MulAut.conj q ((p * q) ^ 2) = (p * q) ^ 2 := by
      rw [MulAut.conj_apply, hqq]
      calc q * (p * q) ^ 2 * q = ((p * q) ^ 2 * q) * q := by rw [hqb]
        _ = (p * q) ^ 2 * (q * q) := by group
        _ = (p * q) ^ 2 := by rw [hq2, mul_one]
    have hcomm_pb : (p * (p * q) ^ 2) * MulAut.conj q h =
        MulAut.conj q h * (p * (p * q) ^ 2) := by
      have h1 : MulAut.conj q (p * h) = MulAut.conj q (h * p) := by rw [hp_comm]
      rw [map_mul, map_mul] at h1
      rwa [hcpp] at h1
    have hcomm_b : (p * q) ^ 2 * MulAut.conj q h =
        MulAut.conj q h * (p * q) ^ 2 := by
      have h1 : MulAut.conj q ((p * q) ^ 2 * h) = MulAut.conj q (h * (p * q) ^ 2) := by
        rw [hb_comm]
      rw [map_mul, map_mul] at h1
      rwa [hcb] at h1
    have hpb_b : (p * (p * q) ^ 2) * (p * q) ^ 2 = p := by
      calc (p * (p * q) ^ 2) * (p * q) ^ 2 = p * ((p * q) ^ 2 * (p * q) ^ 2) := by group
        _ = p := by rw [hb2, mul_one]
    have hcomm_p : p * MulAut.conj q h = MulAut.conj q h * p := by
      calc p * MulAut.conj q h
          = ((p * (p * q) ^ 2) * (p * q) ^ 2) * MulAut.conj q h := by rw [hpb_b]
        _ = (p * (p * q) ^ 2) * ((p * q) ^ 2 * MulAut.conj q h) := by group
        _ = (p * (p * q) ^ 2) * (MulAut.conj q h * (p * q) ^ 2) := by rw [hcomm_b]
        _ = ((p * (p * q) ^ 2) * MulAut.conj q h) * (p * q) ^ 2 := by group
        _ = (MulAut.conj q h * (p * (p * q) ^ 2)) * (p * q) ^ 2 := by rw [hcomm_pb]
        _ = MulAut.conj q h * ((p * (p * q) ^ 2) * (p * q) ^ 2) := by group
        _ = MulAut.conj q h * p := by rw [hpb_b]
    exact mem_Gxy.mpr ⟨mem_Gx.mpr hcomm_p, mem_Gx.mpr hcomm_b⟩
  refine Subgroup.mem_normalizer_iff.mpr (fun h => ⟨?_, ?_⟩)
  · intro hh
    exact hforward h hh
  · intro hh
    have hrev : q * (q * h * q⁻¹) * q⁻¹ = h := by
      rw [hqq]
      calc q * (q * h * q) * q = (q * q) * h * (q * q) := by group
        _ = h := by rw [hq2]; group
    have hthis : q * (q * h * q⁻¹) * q⁻¹ ∈ Gxy p ((p * q) ^ 2) :=
      hforward (q * h * q⁻¹) hh
    rwa [hrev] at hthis

theorem fourB_card_two_four (H : FourBHyps a z) (hp : IsConj a p) {b' : G}
    (hb : b' ∈ orb2A p p) :
    Nat.card {s : G // s ∈ derivedOf (Gxy p b') ∧ orderOf s = 2 ∧ IsConj z s} = 105 := by
  have hF3p : Fusion3Facts p z := H.hF3 p z hp (IsConj.refl z)
  have hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b') := hF3p.shape_2A b' hb
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hX
  have hPicp : A8Pictures p z := H.hPic p z hp (IsConj.refl z)
  let toFun : {s : G // s ∈ derivedOf (Gxy p b') ∧ orderOf s = 2 ∧ IsConj z s} →
      {x : alternatingGroup (Fin 8) // (x : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}} :=
    fun s =>
      let x : alternatingGroup (Fin 8) := φ.symm ⟨s.1, s.2.1⟩
      ⟨x, by
        have hφx : (φ x : G) = s.1 := by
          have h := MulEquiv.apply_symm_apply φ ⟨s.1, s.2.1⟩
          exact congrArg Subtype.val h
        have hs2 : s.1 ^ 2 = 1 := by
          have h := pow_orderOf_eq_one s.1
          rwa [s.2.2.1] at h
        have hs1 : s.1 ≠ 1 := by
          intro h1
          have h2 := s.2.2.1
          rw [h1, orderOf_one] at h2
          exact (by decide : (1 : ℕ) ≠ 2) h2
        have hx2 : x ^ 2 = 1 := by
          apply φ.injective
          rw [map_pow, map_one]
          apply Subtype.ext
          change ((φ x : ↥(derivedOf (Gxy p b'))) : G) ^ 2 = 1
          rw [hφx, hs2]
        have hx1 : x ≠ 1 := by
          intro hx
          apply hs1
          calc s.1 = (φ x : G) := hφx.symm
            _ = (φ 1 : G) := by rw [hx]
            _ = 1 := by rw [map_one]; rfl
        rcases cycleType_eq_of_sq_eq_one hx2 hx1 with h | h
        · exfalso
          have hfig := hPicp.fig8a b' hb φ x h
          exact fourB_not_both H ((fourB_isConj_iff hp).mp (hφx ▸ hfig.1)) s.2.2.2
        · exact h⟩
  let invFun : {x : alternatingGroup (Fin 8) //
        (x : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}} →
      {s : G // s ∈ derivedOf (Gxy p b') ∧ orderOf s = 2 ∧ IsConj z s} :=
    fun x =>
      ⟨(φ x.1 : G), (φ x.1).2, by
        rw [Subgroup.orderOf_coe (φ x.1), MulEquiv.orderOf_eq φ x.1,
          ← Subgroup.orderOf_coe x.1, ← Equiv.Perm.lcm_cycleType, x.2]
        decide,
        (hPicp.fig8b b' hb φ x.1 x.2).1⟩
  refine (Nat.card_congr ⟨toFun, invFun, ?_, ?_⟩).trans ?_
  · intro s
    apply Subtype.ext
    change (φ (φ.symm ⟨s.1, s.2.1⟩) : G) = s.1
    rw [MulEquiv.apply_symm_apply]
  · intro x
    apply Subtype.ext
    change φ.symm (φ x.1) = x.1
    rw [MulEquiv.symm_apply_apply]
  · exact fourB_card_shape2222

theorem fourB_exists_two_four (H : FourBHyps a z) (P : FourBPair a p q) :
    ∃ t ∈ Gxy p q, t ∈ derivedOf (Gxy p ((p * q) ^ 2)) ∧ orderOf t = 2 ∧ IsConj z t ∧
      IsConj a (p * t) ∧ IsConj a ((p * q) ^ 2 * t) ∧ IsConj a (p * ((p * q) ^ 2 * t)) := by
  let b : G := (p * q) ^ 2
  have hb : b ∈ orb2A p p := (fourB_row H P).1
  let T : Set G := {s | s ∈ derivedOf (Gxy p b) ∧ orderOf s = 2 ∧ IsConj z s}
  have hcard : Nat.card ↥T = 105 := fourB_card_two_four H P.hp hb
  have hodd : Odd (Nat.card ↥T) := by rw [hcard]; exact ⟨52, by norm_num⟩
  have hq2 : q * q = 1 := fourB_mul_self_q H P
  have hT : ∀ t ∈ T, q * t * q⁻¹ ∈ T := by
    intro t ht
    have ht' : t ∈ derivedOf (Gxy p b) ∧ orderOf t = 2 ∧ IsConj z t := ht
    refine ⟨?_, ?_, ?_⟩
    · exact conj_mem_derivedOf_of_mem_normalizer (fourBParity_normalizer H P) ht'.1
    · change orderOf (MulAut.conj q t) = 2
      rw [MulEquiv.orderOf_eq (MulAut.conj q) t, ht'.2.1]
    · exact (ht'.2.2).trans (isConj_iff.mpr ⟨q, rfl⟩)
  obtain ⟨t, htT, hfix⟩ := fourB_exists_fixed_of_odd T q hq2 hT hodd
  have ht' : t ∈ derivedOf (Gxy p b) ∧ orderOf t = 2 ∧ IsConj z t := htT
  have htG : t ∈ Gxy p b := derivedOf_le _ ht'.1
  have htp : p * t = t * p := mem_Gx.mp (mem_Gxy.mp htG).1
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht'.2.1] at h
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 := ht'.2.1
    rw [h1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  have hfig := fourB_fig H P.hp hb ht'.1 ht2 ht1
  have hcls : IsConj a (p * t) ∧ IsConj a (b * t) ∧ IsConj a (p * (b * t)) := by
    rcases hfig with h | h
    · exact False.elim (fourB_not_both H h.1 ht'.2.2)
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  refine ⟨t, ?_, ht'.1, ht'.2.1, ht'.2.2, hcls.1, hcls.2.1, hcls.2.2⟩
  exact mem_Gxy.mpr ⟨mem_Gx.mpr htp, mem_Gx.mpr hfix⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
