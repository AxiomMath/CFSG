module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63_pocket_of_subnormal {Y N : Subgroup G} {z : G} {K : Subgroup G}
    (hK : Sl23PocketIn Y z K) (hYN : Y ≤ N) (hsub : (Y.subgroupOf N).IsSubnormal) :
    Sl23PocketIn N z K := by
  refine ⟨hK.1, hK.2.1.trans (inf_le_inf hYN le_rfl), ?_, hK.2.2.2⟩
  have hAB : Y ⊓ centralizer ({z} : Set G) ≤ N ⊓ centralizer ({z} : Set G) :=
    inf_le_inf hYN le_rfl
  have hKle : K.subgroupOf (N ⊓ centralizer ({z} : Set G)) ≤
      (Y ⊓ centralizer ({z} : Set G)).subgroupOf (N ⊓ centralizer ({z} : Set G)) :=
    fun x hx => hK.2.1 hx
  have hHsn : ((K.subgroupOf (N ⊓ centralizer ({z} : Set G))).subgroupOf
      ((Y ⊓ centralizer ({z} : Set G)).subgroupOf
        (N ⊓ centralizer ({z} : Set G)))).IsSubnormal := by
    have h := hK.2.2.1.comap
      ((Y ⊓ centralizer ({z} : Set G)).subgroupOfEquivOfLe hAB).toMonoidHom
    convert h using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  have hAsn : ((Y ⊓ centralizer ({z} : Set G)).subgroupOf
      (N ⊓ centralizer ({z} : Set G))).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion (inf_le_left : N ⊓ centralizer ({z} : Set G) ≤ N))
    convert h using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (Subgroup.mem_inf.mp x.2).2⟩⟩
  exact Subgroup.IsSubnormal.trans hKle hHsn hAsn

theorem sec63_not_omega6Minus [Finite G] (h35 : Asc82Lemma35) (hM : Asc82Tab6M)
    (hF : Asc82AutFacts) {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) {v y : G}
    {V W Y : Subgroup G} (hv : orderOf v = 2)
    (hVc : IsComponentIn V (centralizer ({v} : Set G)))
    (hWc : IsComponentIn W (centralizer ({v} : Set G))) (hWF : InFStar W) (hne : W ≠ V)
    (hy : orderOf y = 2) (hYc : IsComponentIn Y (centralizer ({y} : Set G)))
    (hYF : InFStar Y) (hVY : V ≤ Y) (hY6 : IsOmega6Minus Y) : False := by
  obtain ⟨z, hzV, hz2⟩ := exists_involution_of_isComponentIn hVc
  have hzY : z ∈ Y := hVY hzV
  obtain ⟨-, K, hK⟩ := sec711M_pocket hM hF ⟨hYc.isQuasisimple, hY6⟩ hzY hz2
  have hKC : Sl23PocketIn (centralizer ({y} : Set G)) z K :=
    sec63_pocket_of_subnormal hK hYc.1 hYc.2.2
  have hdata : Sec3PocketData y Y z K :=
    ⟨hy, hYc, hYF, hz2, hzY, hK.2.1.trans inf_le_left, hKC⟩
  have hzv : z ∈ centralizer ({v} : Set G) := hVc.1 hzV
  have hvz : v ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hzv).symm
  have hWz : W ≤ centralizer ({z} : Set G) := by
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hVc.commute_of_ne hWc hne.symm z hzV b hb).symm)
  refine h35 G t L hS y Y z K v hdata hv hvz W ⟨?_, hWF⟩
  rw [centralizer_pair_eq_inf]
  exact hWc.mono (le_inf hWc.1 hWz) inf_le_left

end CFSG.OddStandard.SmallF3.Omega
