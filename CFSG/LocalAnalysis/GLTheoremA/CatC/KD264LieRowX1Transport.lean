module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

section Conj

variable {S : Type*} [Group S]

theorem fixSubgroup_conj (s : S) :
    fixSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem iInf_fixSubgroup_conj (F : Subgroup S) :
    (⨅ f ∈ F.map (MulAut.conj : S →* MulAut S), fixSubgroup f) =
      Subgroup.centralizer (F : Set S) := by
  ext x
  simp only [Subgroup.mem_iInf, Subgroup.mem_map, mem_fixSubgroup, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    have hx := h (MulAut.conj g) ⟨g, hg, rfl⟩
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hx
    exact hx
  · intro h f hf
    obtain ⟨s, hs, rfl⟩ := hf
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact h s hs

end Conj

section Good

variable {S : Type} [Group S] [Finite S]

theorem isGood_of_subnormal_quasisimple {p : ℕ} (hp : p.Prime) {F : Subgroup (MulAut S)}
    {L : Subgroup S} (hL : IsSubnormal L (⨅ f ∈ F, fixSubgroup f))
    (hq : CFSG.Open.IsQuasisimple ↥L) (hd : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    IsGood p F := by
  unfold IsGood
  exact (S3.glaPLayer_ne_bot_iff hp).2 ⟨L, S12.glaPComponent_of_quasisimple' hp hL hq hd⟩

end Good

section Iso

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_of_map (p : ℕ) (ψ : G ≃* H) {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map (ψ : G →* H)) := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    change (a : H) * (b : H) = (b : H) * (a : H)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    have hc : (⟨x, hx⟩ : E) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := hcomm.is_comm.comm _ _
    exact congrArg Subtype.val hc
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hexp z' hz', map_one]

theorem pRank_map_mulEquiv [Finite G] [Finite H] (p : ℕ) (ψ : G ≃* H) (E : Subgroup G) :
    CFSG.Open.pRank p (E.map (ψ : G →* H)) = CFSG.Open.pRank p E := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E', hE'le, hE', hcard⟩
    refine ⟨E'.map (ψ.symm : H →* G), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 (hE'le hy)
      simpa using hz
    · exact isElemAbelian_of_map p ψ.symm hE'
    · rw [← hcard]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective E' (ψ.symm : H →* G)
        ψ.symm.injective).toEquiv).symm
  · rintro ⟨E', hE'le, hE', hcard⟩
    refine ⟨E'.map (ψ : G →* H), Subgroup.map_mono hE'le, isElemAbelian_of_map p ψ hE', ?_⟩
    rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E' (ψ : G →* H) ψ.injective).toEquiv).symm

end Iso

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
