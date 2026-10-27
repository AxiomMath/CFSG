module

public import CFSG.GH74.Generic.BProg.Frozen
public import CFSG.GH74.Generic.BProg.Helpers
public import CFSG.GH74.Generic.S3.NbrComp

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

@[expose] def DictS3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)),
    S3Setup G x K → IsJMax x K → ¬ GLS.HasTwoThinConfiguration G → OnlyInvX x K →
      ∀ (t : StatedLieTag) (p f : ℕ) (y : G) (Iw Iv : Subgroup G),
        NbrData G t p f x y Iw Iv → imgBar x Iw = K →
          NoAltJ2 G ∧ IsJ2Circ x Iw ∧
            ∃ A : Subgroup G, IsSource2 x Iw A ∧ IsAdmPair x Iw A y (imgBar x Iv)

theorem b_S3_nbrComp_of_program (hA : Stage2Allow) (hD : DictS3) : B_S3_nbrComp := by
  intro G _ _ x K hset hmax hthin honly t p f y Iw Iv hnd himg hbarcomp
  have hHyp : Hyp2 G := ⟨hset.simple, hset.nonab, hset.rank, hset.gen4, hset.kgh, hset.sylow,
    ⟨x, hset.inv, K, hset.comp, hset.g2⟩, hthin⟩
  obtain ⟨hNo, hcirc, A, hAsrc, hAdm⟩ := hD G x K hset hmax hthin honly t p f y Iw Iv hnd himg
  have hss : NbhdSemisimple x y (imgBar x Iv) := hA G hHyp hNo x Iw hcirc A hAsrc y _ hAdm
  have hy1 : y ≠ 1 := by
    intro h
    have := hnd.y_inv
    rw [h, orderOf_one] at this
    omega
  have hycl : y ∈ closure ({x, y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hcomm := hss y hycl hy1
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have hoddF : Odd (Nat.card F) := by
    rw [hF]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
  have hy2' : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hnd.y_inv, pow_two] at this
  have hIvc : ∀ i ∈ Iv, i * y = y * i :=
    central_of_involution_of_equiv_sl2 hoddF e hnd.y_Iv hy2' hy1
  have hIvC : Iv ≤ centralizer ({y} : Set G) := fun i hi =>
    Subgroup.mem_centralizer_singleton_iff.2 (hIvc i hi)
  have hIvq : IsQuasisimple ↥Iv :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by rw [hF]; have := hnd.prime.2.2; omega))
  have hIwC : Iw ≤ centralizer ({x} : Set G) := hnd.comp_w.1.1
  have hIvX : Iv ≤ ((imgBar x Iv).comap (proj x)).map (centralizer ({x} : Set G)).subtype ⊓
      centralizer ({y} : Set G) := by
    intro g hg
    have hgC : g ∈ centralizer ({x} : Set G) := hIwC (hnd.Iv_le hg)
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨g, hgC⟩, mem_imgBar.2 ⟨⟨g, hgC⟩, hg, rfl⟩, rfl⟩,
      hIvC hg⟩
  have hIvL : Iv ≤ liftAt x y (imgBar x Iv) :=
    le_oPrimeResidualOf_of_isQuasisimple hIvX hIvq
  have hcommIv : ∀ a ∈ Iv, ∀ w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)), a * w = w * a := by
    intro a ha w hw
    have h1 : ⁅a, w⁆ ∈ ⁅liftAt x y (imgBar x Iv), pPrimeCoreOf 2 (centralizer ({y} : Set G))⁆ :=
      Subgroup.commutator_mem_commutator (hIvL ha) hw
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  exact ⟨hIvC, CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hIvC).symm hIvq,
    isSubnormal_of_barSub_of_comm hbarcomp.2 hcommIv⟩

end CFSG.GH74.Generic.BProg
