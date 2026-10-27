module

public import CFSG.CGT.Timmesfeld75.SLTransvection
public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T : Subgroup G} {n : ℕ}

theorem exists_lift_transvection_n {H : Subgroup G} [(T.subgroupOf H).Normal]
    (e : ↥H ⧸ T.subgroupOf H ≃* SL(n, GaloisField 2 1)) {x₀ : G} (hx₀ : x₀ ∈ classD T)
    (hx₀H : x₀ ∈ H) (hu₀ : IsTransvection (e (QuotientGroup.mk (⟨x₀, hx₀H⟩ : ↥H))))
    {s : SL(n, GaloisField 2 1)} (hs : IsTransvection s) :
    ∃ x ∈ classD T, ∃ hxH : x ∈ H, e (QuotientGroup.mk (⟨x, hxH⟩ : ↥H)) = s := by
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection hu₀ hs
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e.symm W)
  have hwW : e (QuotientGroup.mk w) = W := by rw [hw]; exact e.apply_symm_apply W
  have hxH : (w : G) * x₀ * (w : G)⁻¹ ∈ H := H.mul_mem (H.mul_mem w.2 hx₀H) (H.inv_mem w.2)
  refine ⟨(w : G) * x₀ * (w : G)⁻¹, ?_, hxH, ?_⟩
  · have := classD_conj hx₀ (w : G)⁻¹
    simpa using this
  · have h1 : (⟨(w : G) * x₀ * (w : G)⁻¹, hxH⟩ : ↥H) = w * ⟨x₀, hx₀H⟩ * w⁻¹ := rfl
    rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
      map_inv, hwW, hW]

end CFSG.CGT.T75P
