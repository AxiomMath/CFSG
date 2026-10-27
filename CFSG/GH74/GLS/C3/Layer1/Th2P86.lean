module

public import CFSG.GH74.GLS.C3.Layer1.Th2P86Abs
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar

public section

namespace CFSG.GH74.GLS.Th2.P85

open Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G]

theorem pPrimeCore_Mb_eq_bot [Finite G] (M : Subgroup G) : pPrimeCore 2 (Mb M) = ⊥ := by
  have h := oddCore_barQ (Y := ↥M)
  rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at h

theorem isSubnormal_imgM {M L : Subgroup G} (hL : IsSubnormalIn L M) :
    (imgM M L).IsSubnormal :=
  Subgroup.IsSubnormal.map barMk_surjective hL.2

theorem imgM_min {K M L : Subgroup G} (hL : IsMinSubnormalIn K M L) {J : Subgroup (Mb M)}
    (hKJ : imgM M K ≤ J) (hJL : J ≤ imgM M L) (hJ : J.IsSubnormal) : J = imgM M L := by
  have hLM : L ≤ M := hL.2.1.1
  have hKL : K ≤ L := hL.1
  have hKM : K ≤ M := hKL.trans hLM
  set J' : Subgroup G := (J.comap (barMk ↥M)).map M.subtype ⊓ L with hJ'
  have hKJ' : K ≤ J' := by
    intro k hk
    refine ⟨⟨⟨k, hKM hk⟩, ?_, rfl⟩, hKL hk⟩
    exact hKJ (mem_imgM_iff.2 ⟨⟨k, hKM hk⟩, hk, rfl⟩)
  have hJ'L : J' ≤ L := inf_le_right
  have hsub : IsSubnormalIn J' M := by
    refine ⟨hJ'L.trans hLM, ?_⟩
    have h1 : J'.subgroupOf M = J.comap (barMk ↥M) ⊓ L.subgroupOf M := by
      ext m
      simp only [hJ', Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_map,
        Subgroup.mem_comap]
      constructor
      · rintro ⟨⟨m', hm', hm'eq⟩, hmL⟩
        exact ⟨(Subtype.ext hm'eq : m' = m) ▸ hm', hmL⟩
      · rintro ⟨hmJ, hmL⟩
        exact ⟨⟨m, hmJ, rfl⟩, hmL⟩
    rw [h1]
    exact (hJ.comap (barMk ↥M)).inf hL.2.1.2
  have hJ'eq : J' = L := hL.2.2 J' hKJ' hJ'L hsub
  refine le_antisymm hJL fun w hw => ?_
  obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hw
  have hmJ' : (m : G) ∈ J' := hJ'eq ▸ hm
  obtain ⟨⟨m', hm'J, hm'eq⟩, -⟩ := hmJ'
  have : m' = m := Subtype.ext hm'eq
  rw [this] at hm'J
  exact hm'J

end CFSG.GH74.GLS.Th2.P85

namespace CFSG.GH74.GLS

open Subgroup CFSG Blueprint CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.TwoThin

variable {G : Type} [Group G] [Finite G]

theorem isSimpleSocle_imgM_of_terminal {x y : G} {K T S L M : Subgroup G}
    (hstd : Th2Std x y K T S) (hKM : K ≤ M)
    (hQ : IsSylowOf 2 (T ⊓ CxK x K) (CMbar M K))
    (hL : IsMinSubnormalIn K M L)
    (hne : imgM M K ≠ imgM M L)
    (hterm : IsTerminalSub (imgM M K))
    (hrk : 2 ≤ pRank 2 ↥(T ⊓ CxK x K)) :
    IsSimpleSocle (imgM M L) ⊤ := by
  have hQM : T ⊓ CxK x K ≤ M := hQ.le.trans inf_le_left
  have hxM : x ∈ M := hQM ⟨hstd.x_mem_T, hstd.x_mem_CxK⟩
  have hx2 : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hstd.orderOf_x
  have hxb2 : orderOf (barMk ↥M ⟨x, hxM⟩) = 2 := orderOf_barMk hx2
  have hxbc : ∀ k ∈ imgM M K, barMk ↥M ⟨x, hxM⟩ * k = k * barMk ↥M ⟨x, hxM⟩ := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := mem_imgM_iff.1 hk
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.1 (hstd.K_le_C hm)).symm
  have hKcomp := hterm _ hxb2 hxbc
  have hKq : IsQuasisimple ↥(imgM M K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKcomp.1) hKcomp.2.1
  have hQ2 : IsPGroup 2 ↥(T ⊓ CxK x K) := hstd.T_pGroup.to_le inf_le_left
  obtain ⟨eQ⟩ := equiv_imgM hQM hQ2
  have hrk' : 2 ≤ pRank 2 ↥(imgM M (T ⊓ CxK x K)) := by
    rw [← Stage1.Thm2.Recip.pRank_eq_of_mulEquiv' eQ]
    exact hrk
  obtain ⟨u, huQ, v, hvQ, hu2, hv2, hne', hcomm⟩ :=
    C3.Layer1.U1a.exists_commuting_involutions hrk'
  have hQC : imgM M (T ⊓ CxK x K) ≤ centralizer (imgM M K : Set (Mb M)) := by
    rw [← imgM_cmbar_eq hKM]
    exact imgM_mono hQ.le
  exact isSimpleSocle_of_terminal (pPrimeCore_Mb_eq_bot M) hKq hterm hu2 hv2 hcomm hne'
    (fun k hk => (mem_centralizer_iff.1 (hQC huQ) k hk).symm)
    (fun k hk => (mem_centralizer_iff.1 (hQC hvQ) k hk).symm)
    (imgM_mono hL.1) (isSubnormal_imgM hL.2.1) (fun J hKJ hJL hJ => imgM_min hL hKJ hJL hJ)
    hne

theorem b_thm2_p86_proved : B_thm2_p86 := by
  intro G _ _ x y K T S M L hsetup hrk hterm
  exact isSimpleSocle_imgM_of_terminal hsetup.choice.std hsetup.KM hsetup.hQ hsetup.hL
    hsetup.ne hterm hrk

end CFSG.GH74.GLS
