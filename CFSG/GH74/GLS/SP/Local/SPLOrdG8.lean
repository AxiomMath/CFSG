module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG7

public section

open Subgroup DihedralGroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.ShultStronglyClosedTI.InvolutionCounting
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G8

variable {G : Type} [Group G] [Finite G] {D : SPLNot3 G}

theorem rt_eq (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d] {hd : 2 ∣ D.d}
    (cd : ChatData D hs hc hd) {ι : ℕ} (hι : ι = Nat.card {γ : ↥D.I // orderOf γ = 2})
    (hιd : ι * D.d = Nat.card ↥D.I) :
    thompsonPairCount D.t D.z D.t =
      Nat.card {p : (↥D.I ⋊[dihAct (sigmaAut D hc) (sigmaAut_sq D hc) hd] DihedralGroup D.d) ×
          (↥D.I ⋊[dihAct (sigmaAut D hc) (sigmaAut_sq D hc) hd] DihedralGroup D.d) //
        orderOf p.1 = 2 ∧ p.1 ∉ Z0 (sigmaAut D hc) (sigmaAut_sq D hc) hd ∧
          p.2 ∈ Z0 (sigmaAut D hc) (sigmaAut_sq D hc) hd ∧
          tSD (sigmaAut D hc) (sigmaAut_sq D hc) hd ∈ zpowers (p.1 * p.2)} := by
  have htt := t_mul_t D hs
  have hzz := z_mul_z D hs
  let σ := sigmaAut D hc
  let hσ := sigmaAut_sq D hc
  let e : (↥D.I ⋊[dihAct σ hσ hd] DihedralGroup D.d) → G := fun w => (cd.Φ w : G)
  have he_inj : Function.Injective e := fun w w' h => cd.Φ.injective (Subtype.ext h)
  have he_mul : ∀ a b, e (a * b) = e a * e b := fun a b => by
    show ((cd.Φ (a * b) : ↥D.Chat) : G) = _
    rw [map_mul]; rfl
  have he_ord : ∀ a, orderOf (e a) = orderOf a := fun a => by
    show orderOf ((cd.Φ a : ↥D.Chat) : G) = _
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have he_zpow : ∀ (a : ↥D.I ⋊[dihAct σ hσ hd] DihedralGroup D.d) (n : ℤ), e (a ^ n) = (e a) ^ n :=
    fun a n => by
      show ((cd.Φ (a ^ n) : ↥D.Chat) : G) = _
      rw [map_zpow]; rfl
  have he_t : e (tSD σ hσ hd) = D.t := by
    show ((cd.Φ ⟨1, r ((D.d / 2 : ℕ) : ZMod D.d)⟩ : ↥D.Chat) : G) = D.t
    rw [cd.hΦr]
    have hval : ((D.d / 2 : ℕ) : ZMod D.d).val = D.d / 2 :=
      ZMod.val_natCast_of_lt (by have := d_pos D hs; omega)
    rw [hval, cd.ht]
    simp
  have he_Ct : ∀ a, e a ∈ D.Ct := fun a => Chat_le_Ct D hs hc (cd.Φ a).2
  have hmem_iff : ∀ a b : ↥D.I ⋊[dihAct σ hσ hd] DihedralGroup D.d,
      tSD σ hσ hd ∈ zpowers (a * b) ↔ D.t ∈ zpowers (e a * e b) := by
    intro a b
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
      refine mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [← he_mul, ← he_zpow, hn, he_t]
    · intro h
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
      refine mem_zpowers_iff.mpr ⟨n, he_inj ?_⟩
      rw [he_zpow, he_mul, hn, he_t]
  have hconj_z : ∀ b ∈ Z0 σ hσ hd, IsConj D.z (e b) := fun b hb => conj_z_of_mem_Z0 hs hc cd hb
  have hconj_t : ∀ a : ↥D.I ⋊[dihAct σ hσ hd] DihedralGroup D.d, orderOf a = 2 →
      a ∉ Z0 σ hσ hd → IsConj D.t (e a) := by
    intro a ha2 haZ
    have hord : orderOf (e a) = 2 := by rw [he_ord]; exact ha2
    rcases inv_classes D hs hord with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw, hwa⟩ := (marks_iff hs hc cd hι hιd (e a)).mp ⟨h, he_Ct a⟩
      have : w = a := he_inj hwa
      rw [this] at hw
      exact haZ hw
  unfold thompsonPairCount
  symm
  refine Nat.card_eq_of_bijective
    (fun p => ⟨(e p.1.1, e p.1.2), ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨⟨a, b⟩, ha2, haZ, hbZ, ht⟩ := p
    exact ⟨hconj_t a ha2 haZ, hconj_z b hbZ, (hmem_iff a b).mp ht⟩
  · rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨a', b'⟩, ha'⟩ h
    have h1 := congrArg Subtype.val h
    have h2 : (e a, e b) = (e a', e b') := h1
    rw [Prod.mk.injEq] at h2
    exact Subtype.ext (Prod.ext (he_inj h2.1) (he_inj h2.2))
  · rintro ⟨⟨x, y⟩, hxy⟩
    obtain ⟨hx, hy, hxy'⟩ := hxy
    have hcen := mem_centralizer_of_mem_thompsonPairs htt hzz htt (p := (x, y)) ⟨hx, hy, hxy'⟩
    have hx2 : orderOf x = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hx]; exact hs.syl.t_ord
    have hy2 : orderOf y = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hy]; exact hs.syl.z_inv
    have hxC : x ∈ D.Chat := inv_Ct_le_Chat D hs hc hcen.1 (mul_self_of_orderOf_two hx2)
    have hyC : y ∈ D.Chat := inv_Ct_le_Chat D hs hc hcen.2 (mul_self_of_orderOf_two hy2)
    let a := cd.Φ.symm ⟨x, hxC⟩
    let b := cd.Φ.symm ⟨y, hyC⟩
    have hea : e a = x := by
      show ((cd.Φ (cd.Φ.symm ⟨x, hxC⟩) : ↥D.Chat) : G) = x
      rw [MulEquiv.apply_symm_apply]
    have heb : e b = y := by
      show ((cd.Φ (cd.Φ.symm ⟨y, hyC⟩) : ↥D.Chat) : G) = y
      rw [MulEquiv.apply_symm_apply]
    have ha2 : orderOf a = 2 := by rw [← he_ord, hea]; exact hx2
    have haZ : a ∉ Z0 σ hσ hd := by
      intro haZ
      have h1 := hconj_z a haZ
      rw [hea] at h1
      exact hs.syl.t_nconj (h1.trans hx.symm)
    have hbZ : b ∈ Z0 σ hσ hd := by
      obtain ⟨w, hw, hwb⟩ := (marks_iff hs hc cd hι hιd y).mp ⟨hy, hcen.2⟩
      have : w = b := he_inj (hwb.trans heb.symm)
      rw [← this]; exact hw
    have hab : tSD σ hσ hd ∈ zpowers (a * b) := by
      rw [hmem_iff, hea, heb]; exact hxy'
    refine ⟨⟨(a, b), ha2, haZ, hbZ, hab⟩, ?_⟩
    apply Subtype.ext
    show (e a, e b) = (x, y)
    rw [hea, heb]

end G8

end CFSG.GH74.GLS.SP.Local
