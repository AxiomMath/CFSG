module

public import CFSG.GH74.Generic.BProg.B3.S1L3PkgAbs
public import CFSG.GH74.Generic.BProg.B3.S3OuterRank
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1L3PkgPsl2

open CFSG Subgroup

theorem conj_involutions_of_psl2 {N : Type} [Group N] {k : Type} [Field k] [Finite k] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hk : Nat.card k = p ^ f)
    (e : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :
    ∀ a b : N, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → ∃ g : N, g * a * g⁻¹ = b := by
  intro a b ha ha2 hb hb2
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card k) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hk⟩
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power k hodd
    (e a) (e b)
    ⟨fun h => ha (e.injective (h.trans (map_one e).symm)), by
      rw [pow_two, ← map_mul, ha2, map_one]⟩
    ⟨fun h => hb (e.injective (h.trans (map_one e).symm)), by
      rw [pow_two, ← map_mul, hb2, map_one]⟩
  refine ⟨e.symm g, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hg

theorem exists_involution_of_psl2 {L : Type} [Group L] [Finite L] {k : Type} [Field k] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hk : Nat.card k = p ^ f) (h5 : 5 ≤ p ^ f)
    {N : Subgroup L} (hq : IsQuasisimple ↥N)
    (e : ↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)
    {β : L} (hβ : β * β = 1) (hβ1 : β ≠ 1) (hnorm : ∀ n ∈ N, β * n * β⁻¹ ∈ N) :
    ∃ δ ∈ N, δ ≠ 1 ∧ δ ≠ β ∧ δ * δ = 1 ∧ δ * β = β * δ := by
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨v, w, hv, hv2, hw, hw2, hvw, hvwc⟩ := S1L3PkgAbs.exists_two_commuting_involutions
    (S3OuterRank.two_le_pRank_of_psl2 hq (by omega) (by omega) e)
  by_cases hβN : β ∈ N
  · obtain ⟨d, hd1, hd2, hdb, hdc⟩ := S1L3PkgAbs.exists_invol_comm_of_conj
      (conj_involutions_of_psl2 hp hp2 hf hk e) hv hv2 hw hw2 hvw hvwc
      (b := ⟨β, hβN⟩) (fun h => hβ1 (congrArg Subtype.val h)) (Subtype.ext hβ)
    exact ⟨d, d.2, fun h => hd1 (Subtype.ext h), fun h => hdb (Subtype.ext h),
      congrArg Subtype.val hd2, congrArg Subtype.val hdc⟩
  · have hv2' : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv
    have h2 : 2 ∣ Nat.card ↥N := by
      rw [← hv2']
      exact orderOf_dvd_natCard v
    obtain ⟨δ, hδN, hδ1, hδ2, hδc⟩ := S1L3PkgAbs.exists_invol_comm_of_even h2 hβ hnorm
    exact ⟨δ, hδN, hδ1, fun h => hβN (h ▸ hδN), hδ2, hδc⟩

end S1L3PkgPsl2

end CFSG.GH74.Generic.BProg.B3
