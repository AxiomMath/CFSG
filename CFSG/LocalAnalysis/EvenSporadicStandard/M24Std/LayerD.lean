module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic
open scoped MatrixGroups

variable {G : Type} [Group G]

namespace LayerD

variable [Finite G] {L B D : Subgroup G} {z : G}

omit [Finite G] in
theorem egM_le_normalizer_D (hD : NData B z D) : egM B z ≤ normalizer (D : Set G) := by
  intro n hn
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => hD.norm n hn x hx, fun hx => ?_⟩
  have := hD.norm n⁻¹ (inv_mem hn) _ hx
  simpa [mul_assoc] using this

section Local

variable (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B) (hD : NData B z D)
include hs hBL hb hD

theorem mem_B_of_mem_D_of_comm {d : G} (hd : d ∈ D) (hdz : d * z = z * d) : d ∈ B := by
  obtain ⟨b, hbB, h | h⟩ :=
    (Octad.mem_egV_iff hs hBL).1 (Octad.mem_egV_of_comm hs hBL hb (hD.D_le hd) hdz)
  · rw [h]; exact hbB
  · exfalso
    apply hD.z_not_mem
    have e : z = b⁻¹ * d := by rw [h]; group
    rw [e]
    exact mul_mem (inv_mem (hD.B_le hbB)) hd

theorem mem_B_of_mem_D_of_mem_L {d : G} (hd : d ∈ D) (hdL : d ∈ L) : d ∈ B :=
  mem_B_of_mem_D_of_comm hs hBL hb hD hd (Octad.z_comm hs hdL).symm

theorem mem_egNL_of {l : G} (hlL : l ∈ L) (hlN : l ∈ normalizer (D : Set G)) : l ∈ egNL L B := by
  refine mem_inf.2 ⟨mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hlL⟩
  · exact mem_B_of_mem_D_of_mem_L hs hBL hb hD ((mem_normalizer_iff.1 hlN x).1 (hD.B_le hx))
      (mul_mem (mul_mem hlL (hBL hx)) (inv_mem hlL))
  · have hxD : x ∈ D := (mem_normalizer_iff.1 hlN x).2 (hD.B_le hx)
    have hxL : x ∈ L := by
      have e : x = l⁻¹ * (l * x * l⁻¹) * l := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hlL) (hBL hx)) hlL
    exact mem_B_of_mem_D_of_mem_L hs hBL hb hD hxD hxL

omit hb in
theorem z_mem_normalizer_D : z ∈ normalizer (D : Set G) :=
  egM_le_normalizer_D hD (Octad.z_mem_egM hs hBL)

omit hb in
theorem egNL_le_normalizer_D : egNL L B ≤ normalizer (D : Set G) :=
  (Octad.egNL_le_egM hs hBL).trans (egM_le_normalizer_D hD)

noncomputable def zt : egQD D :=
  QuotientGroup.mk (⟨z, z_mem_normalizer_D hs hBL hD⟩ : normalizer (D : Set G))

noncomputable def psi : egNL L B →* egQD D :=
  (QuotientGroup.mk' (D.subgroupOf (normalizer (D : Set G)))).comp
    (inclusion (egNL_le_normalizer_D hs hBL hD))

omit hb in
theorem orderOf_zt : orderOf (zt hs hBL hD) = 2 := by
  apply orderOf_eq_prime
  · rw [zt, sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine mem_subgroupOf.2 ?_
    show z * z ∈ D
    rw [Octad.z_mul_self hs]
    exact one_mem _
  · rw [zt, Ne, QuotientGroup.eq_one_iff]
    exact fun h => hD.z_not_mem (mem_subgroupOf.1 h)

omit hb in
theorem psi_comm (y : egNL L B) : psi hs hBL hD y * zt hs hBL hD =
    zt hs hBL hD * psi hs hBL hD y := by
  rw [psi, zt, MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Octad.z_comm hs (mem_inf.1 y.2).2).symm

theorem ker_psi : (psi hs hBL hD).ker = B.subgroupOf (egNL L B) := by
  ext y
  rw [MonoidHom.mem_ker, psi, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf, coe_inclusion]
  exact ⟨fun h => mem_B_of_mem_D_of_mem_L hs hBL hb hD h (mem_inf.1 y.2).2, fun h => hD.B_le h⟩

theorem centralizer_quot_eq : centralizer ({zt hs hBL hD} : Set (egQD D)) =
    (psi hs hBL hD).range ⊔ zpowers (zt hs hBL hD) := by
  have hzN := z_mem_normalizer_D hs hBL hD
  have hHN := egNL_le_normalizer_D hs hBL hD
  have hzi := Octad.z_inv hs
  have hzz := Octad.z_mul_self hs
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    rw [mem_centralizer_singleton_iff] at hx
    obtain ⟨⟨n, hnN⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : ((⟨n, hnN⟩ * ⟨z, hzN⟩ : normalizer (D : Set G))⁻¹ * (⟨z, hzN⟩ * ⟨n, hnN⟩)) ∈
        D.subgroupOf (normalizer (D : Set G)) :=
      QuotientGroup.eq.1 (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hx)
    have hc : z⁻¹ * n⁻¹ * z * n ∈ D := by
      have h2 := mem_subgroupOf.1 h1
      have e : (((⟨n, hnN⟩ * ⟨z, hzN⟩ : normalizer (D : Set G))⁻¹ *
          (⟨z, hzN⟩ * ⟨n, hnN⟩) : normalizer (D : Set G)) : G) = z⁻¹ * n⁻¹ * z * n := by
        show (n * z)⁻¹ * (z * n) = z⁻¹ * n⁻¹ * z * n
        group
      rwa [e] at h2
    have hwz : n * z⁻¹ * n⁻¹ * z ∈ D := by
      have h3 := (mem_normalizer_iff.1 hnN _).1 hc
      have e : n * (z⁻¹ * n⁻¹ * z * n) * n⁻¹ = n * z⁻¹ * n⁻¹ * z := by group
      rwa [e] at h3
    have hdD : z * (n * z * n⁻¹) ∈ D := by
      have h4 := inv_mem hwz
      have e : (n * z⁻¹ * n⁻¹ * z)⁻¹ = z * (n * z * n⁻¹) := by
        simp only [mul_inv_rev, inv_inv, hzi, mul_assoc]
      rwa [e] at h4
    have hw2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
      calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
        _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
    set d := z * (n * z * n⁻¹) with hd_def
    have hzd : z * d = n * z * n⁻¹ := by rw [hd_def, ← mul_assoc, hzz, one_mul]
    have hd2 : d * d = 1 := hD.elem.2 _ hdD
    have h5 : z * d * z * d = d * d := by
      rw [hd2]
      calc z * d * z * d = (z * d) * (z * d) := by group
        _ = 1 := by rw [hzd]; exact hw2
    have h6 : z * d * z = d := mul_right_cancel h5
    have hdz : d * z = z * d := by
      calc d * z = (z * z) * d * z := by rw [hzz, one_mul]
        _ = z * (z * d * z) := by group
        _ = z * d := by rw [h6]
    have hdB : d ∈ B := mem_B_of_mem_D_of_comm hs hBL hb hD hdD hdz
    obtain ⟨d', hd'D, hd'⟩ := hD.onto d hdB
    have hconj : d' * z * d'⁻¹ = n * z * n⁻¹ := by
      rw [← hzd, ← hd', hzi]
      calc d' * z * d'⁻¹ = (z * z) * d' * z * d'⁻¹ := by rw [hzz, one_mul]
        _ = z * (z * d' * z * d'⁻¹) := by group
    have hmz : (d'⁻¹ * n) * z = z * (d'⁻¹ * n) := by
      have e1 : (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ = z := by
        calc (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ = d'⁻¹ * (n * z * n⁻¹) * d' := by group
          _ = d'⁻¹ * (d' * z * d'⁻¹) * d' := by rw [hconj]
          _ = z := by group
      calc (d'⁻¹ * n) * z = (d'⁻¹ * n) * z * (d'⁻¹ * n)⁻¹ * (d'⁻¹ * n) := by group
        _ = z * (d'⁻¹ * n) := by rw [e1]
    have hmN : d'⁻¹ * n ∈ normalizer (D : Set G) := mul_mem (inv_mem (le_normalizer hd'D)) hnN
    have hnd : n⁻¹ * d'⁻¹ * n ∈ D := by
      have := (mem_normalizer_iff.1 (inv_mem hnN) d'⁻¹).1 (inv_mem hd'D)
      rwa [inv_inv] at this
    obtain ⟨l, hlL, hm | hm⟩ := Octad.exists_of_comm hs hmz
    · have hlN : l ∈ normalizer (D : Set G) := hm ▸ hmN
      have hlH := mem_egNL_of hs hBL hb hD hlL hlN
      refine mem_sup_left ⟨⟨l, hlH⟩, ?_⟩
      show (QuotientGroup.mk ⟨l, hHN hlH⟩ : egQD D) = QuotientGroup.mk ⟨n, hnN⟩
      refine QuotientGroup.eq.2 (mem_subgroupOf.2 ?_)
      show l⁻¹ * n ∈ D
      rw [← hm]
      have e : (d'⁻¹ * n)⁻¹ * n = n⁻¹ * d'⁻¹⁻¹ * n := by group
      rw [e, inv_inv]
      have := (mem_normalizer_iff.1 (inv_mem hnN) d').1 hd'D
      rwa [inv_inv] at this
    · have hl : l = d'⁻¹ * n * z⁻¹ := by rw [hm]; group
      have hlN : l ∈ normalizer (D : Set G) := by
        rw [hl]
        exact mul_mem hmN (inv_mem hzN)
      have hlH := mem_egNL_of hs hBL hb hD hlL hlN
      have e : (QuotientGroup.mk ⟨n, hnN⟩ : egQD D) =
          psi hs hBL hD ⟨l, hlH⟩ * zt hs hBL hD := by
        show (QuotientGroup.mk ⟨n, hnN⟩ : egQD D) =
          QuotientGroup.mk ⟨l, hHN hlH⟩ * QuotientGroup.mk ⟨z, hzN⟩
        rw [← QuotientGroup.mk_mul]
        refine QuotientGroup.eq.2 (mem_subgroupOf.2 ?_)
        show n⁻¹ * (l * z) ∈ D
        rw [← hm]
        have e2 : n⁻¹ * (d'⁻¹ * n) = n⁻¹ * d'⁻¹ * n := by group
        rw [e2]
        exact hnd
      rw [e]
      exact mul_mem (mem_sup_left ⟨⟨l, hlH⟩, rfl⟩) (mem_sup_right (mem_zpowers _))
  · rintro _ ⟨y, rfl⟩
    exact mem_centralizer_singleton_iff.2 (psi_comm hs hBL hD y)
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl

theorem psi_range_equiv (hA8 : Alt8Data L B) :
    Nonempty ((psi hs hBL hD).range ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨φ, hφ, hker⟩ := hA8
  exact ⟨(QuotientGroup.quotientKerEquivRange (psi hs hBL hD)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_psi hs hBL hb hD).trans hker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩

end Local

end LayerD

theorem NData.isKGroupCat_egQD {B D : Subgroup G} {z : G} (hKS : KLocalSections G)
    (hD : NData B z D) : CFSG.SectionRank.IsKGroupCat (egQD D) := by
  refine hKS D (fun h => ?_) hD.elem.1
  have := hD.card
  rw [h, Subgroup.card_bot] at this
  omega

theorem layer_of_normalizer_D [Finite G] (hA : Ega81HypAZ2A8K) {L B D : Subgroup G} {z : G}
    (hK : CFSG.SectionRank.IsKGroupCat (egQD D))
    (hs : LocalSetting G L z) (hB : OctadType L B) (hb : OctadBasics L B) (hD : NData B z D)
    (hA8 : Alt8Data L B) :
    Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃*
        alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) ∨
      Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃* alternatingGroup (Fin 10)) ∨
      Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃* PSL(4, GaloisField 2 2)) ∨
      IsSporadic (egaLayer (egQD D ⧸ fusionOddCore (egQD D))) .HS :=
  hA (egQD D) hK _ _ (LayerD.orderOf_zt hs hB.1 hD) (LayerD.psi_range_equiv hs hB.1 hb hD hA8)
    (LayerD.centralizer_quot_eq hs hB.1 hb hD)
    (mem_centralizer_iff.2 (by
      rintro _ ⟨y, rfl⟩
      exact LayerD.psi_comm hs hB.1 hD y))

end CFSG.EvenSporadicStandard.M24Std
