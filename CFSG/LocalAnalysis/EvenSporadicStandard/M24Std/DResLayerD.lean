module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DSideCentral

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L B D : Subgroup G} {z : G}

@[expose] noncomputable def psiD (hs : LocalSetting G L z) (hBL : B ≤ L) (hD : NData B z D) :
    egNL L B →* egQD D :=
  (QuotientGroup.mk' (D.subgroupOf (normalizer (D : Set G)))).comp
    (inclusion (LayerD.egNL_le_normalizer_D hs hBL hD))

theorem psiD_apply (hs : LocalSetting G L z) (hBL : B ≤ L) (hD : NData B z D) (l : egNL L B) :
    psiD hs hBL hD l = QuotientGroup.mk ⟨l, LayerD.egNL_le_normalizer_D hs hBL hD l.2⟩ := rfl

theorem psiD_comm (hs : LocalSetting G L z) (hBL : B ≤ L) (hD : NData B z D) (y : egNL L B) :
    psiD hs hBL hD y * DSide.ztD hs hBL hD = DSide.ztD hs hBL hD * psiD hs hBL hD y := by
  rw [psiD_apply, DSide.ztD, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Octad.z_comm hs (mem_inf.1 y.2).2).symm

theorem ker_psiD (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hD : NData B z D) : (psiD hs hBL hD).ker = B.subgroupOf (egNL L B) := by
  ext y
  rw [MonoidHom.mem_ker, psiD_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf]
  exact ⟨fun h => LayerD.mem_B_of_mem_D_of_mem_L hs hBL hb hD h (mem_inf.1 y.2).2,
    fun h => hD.B_le h⟩

theorem psiD_range_equiv (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hD : NData B z D) (hA8 : Alt8Data L B) :
    Nonempty ((psiD hs hBL hD).range ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨φ, hφ, hker⟩ := hA8
  exact ⟨(QuotientGroup.quotientKerEquivRange (psiD hs hBL hD)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_psiD hs hBL hb hD).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩

theorem orderOf_ztD (hs : LocalSetting G L z) (hBL : B ≤ L) (hD : NData B z D) :
    orderOf (DSide.ztD hs hBL hD) = 2 := by
  apply orderOf_eq_prime
  · rw [sq]
    exact DSide.ztD_mul_self hs hBL hD
  · rw [DSide.ztD, Ne, QuotientGroup.eq_one_iff]
    exact fun h => hD.z_not_mem (mem_subgroupOf.1 h)

theorem centralizer_ztD (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B)
    (hD : NData B z D) : centralizer ({DSide.ztD hs hBL hD} : Set (egQD D)) =
      (psiD hs hBL hD).range ⊔ zpowers (DSide.ztD hs hBL hD) := by
  have hzN := LayerD.z_mem_normalizer_D hs hBL hD
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    rw [mem_centralizer_singleton_iff] at hx
    obtain ⟨⟨n, hnN⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨d, hdD, l, hlL, hdl⟩ := DSide.exists_decomp hs hBL hb hD hnN hx.symm
    have hdN : d ∈ normalizer (D : Set G) := le_normalizer hdD
    have hnd : n⁻¹ * d⁻¹ * n ∈ D := by
      have := (mem_normalizer_iff.1 (inv_mem hnN) d⁻¹).1 (inv_mem hdD)
      rwa [inv_inv] at this
    rcases hdl with hl | hl
    · have hlN : l ∈ normalizer (D : Set G) := hl ▸ mul_mem (inv_mem hdN) hnN
      have hlH := LayerD.mem_egNL_of hs hBL hb hD hlL hlN
      refine mem_sup_left ⟨⟨l, hlH⟩, ?_⟩
      rw [psiD_apply]
      refine QuotientGroup.eq.2 (mem_subgroupOf.2 ?_)
      show l⁻¹ * n ∈ D
      rw [← hl]
      have e : (d⁻¹ * n)⁻¹ * n = n⁻¹ * d⁻¹⁻¹ * n := by group
      rw [e, inv_inv]
      have := (mem_normalizer_iff.1 (inv_mem hnN) d).1 hdD
      rwa [inv_inv] at this
    · have hl' : l = d⁻¹ * n * z⁻¹ := by rw [hl]; group
      have hlN : l ∈ normalizer (D : Set G) := by
        rw [hl']
        exact mul_mem (mul_mem (inv_mem hdN) hnN) (inv_mem hzN)
      have hlH := LayerD.mem_egNL_of hs hBL hb hD hlL hlN
      have e : (QuotientGroup.mk ⟨n, hnN⟩ : egQD D) =
          psiD hs hBL hD ⟨l, hlH⟩ * DSide.ztD hs hBL hD := by
        rw [psiD_apply, DSide.ztD, ← QuotientGroup.mk_mul]
        refine QuotientGroup.eq.2 (mem_subgroupOf.2 ?_)
        show n⁻¹ * (l * z) ∈ D
        rw [← hl, show n⁻¹ * (d⁻¹ * n) = n⁻¹ * d⁻¹ * n by group]
        exact hnd
      rw [e]
      exact mul_mem (mem_sup_left ⟨⟨l, hlH⟩, rfl⟩) (mem_sup_right (mem_zpowers _))
  · rintro _ ⟨y, rfl⟩
    exact mem_centralizer_singleton_iff.2 (psiD_comm hs hBL hD y)
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl

end CFSG.EvenSporadicStandard.M24Std.DRes
