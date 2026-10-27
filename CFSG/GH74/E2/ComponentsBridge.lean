module

public import CFSG.GH74.E2.ComponentsBasic
public import CFSG.GH74.E2.Local
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74.Generic CFSG.GH74.GLS

section Bridge

variable {G : Type} [Group G] [Finite G]

noncomputable def cenBarEquiv {t : G} (hcore : CFSG.pPrimeCore 2 ↥(Cen t) = ⊥) :
    ↥(Cen t) ≃* CentralizerBar t :=
  MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥(Cen t)))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hcore]),
      QuotientGroup.mk'_surjective _⟩

omit [Finite G] in
theorem isCompCen_quasisimple {t : G} {K : Subgroup G} (hK : IsCompCen t K) :
    IsQuasisimple ↥K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1) hK.2.1

theorem isCompCen_inC2 (hH : Hyp G) {t : G} (ht : orderOf t = 2) {K : Subgroup G}
    (hK : IsCompCen t K) :
    InC2 ↥K ∧ ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel ↥K .PSL 2 p f →
      p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 17 := by
  have hcore := hH.pPrimeCore_cen_bot ht
  let e : ↥(Cen t) ≃* CentralizerBar t := cenBarEquiv hcore
  let Kb : Subgroup (CentralizerBar t) := (K.subgroupOf (Cen t)).map e.toMonoidHom
  have hKb : IsComponent Kb := CFSG.LocalCores.isComponent_map_mulEquiv e hK.2
  let φ : ↥K ≃* ↥Kb :=
    (Subgroup.subgroupOfEquivOfLe hK.1).symm.trans
      ((K.subgroupOf (Cen t)).equivMapOfInjective e.toMonoidHom e.injective)
  refine ⟨inC2_of_mulEquiv φ.symm (hH.restrictedEven.1.1 t ht Kb hKb), ?_⟩
  intro p f hp hp2 hL
  exact (hH.restrictedEven.2.1 t ht Kb hKb p f hp hp2 (CFSG.GH74.lieModel_of_mulEquiv φ hL)).1

theorem isCompCen_gen4 (hH : Hyp G) (K : Subgroup G) : Gen4 ↥K :=
  Gen4.subgroup K hH.gen4

theorem isCompCen_rank (hH : Hyp G) {t : G} (ht : orderOf t = 2) {K : Subgroup G}
    (hK : IsCompCen t K) : SectionalTwoRankLE ↥K 3 ∨ center ↥K ≠ ⊥ := by
  by_cases htK : t ∈ K
  · right
    intro hbot
    have hmem : (⟨t, htK⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_Cen'.1 (hK.1 g.2))
    rw [hbot, Subgroup.mem_bot] at hmem
    have : t = 1 := congrArg Subtype.val hmem
    rw [this, orderOf_one] at ht
    omega
  · left
    by_contra hcon
    have hcert : RankCertified ↥K 3 := rankCertified_of_not_sectionalTwoRankLE hcon
    set C : Subgroup G := Cen t with hC
    have hKC : K ≤ C := hK.1
    have hcert' : RankCertified ↥(K.subgroupOf C) 3 :=
      hcert.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm
    let c : ↥C := ⟨t, mem_Cen.2 rfl⟩
    have hcc : ∀ x : ↥C, x * c = c * x := fun x => Subtype.ext (mem_Cen'.1 x.2)
    have hc2 : c * c = 1 := Subtype.ext (by
      show t * t = 1
      rw [← sq]
      exact orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq ht))
    have hcK : c ∉ K.subgroupOf C := fun h => htK (Subgroup.mem_subgroupOf.1 h)
    exact not_rankCertified_three_of_gen4 (Gen4.subgroup C hH.gen4) hcc hc2 hcK hcert'

theorem isCompCen_commute {t : G} {K K' : Subgroup G} (hK : IsCompCen t K)
    (hK' : IsCompCen t K') (hne : K ≠ K') : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
  rcases CFSG.LocalCores.distinct_components_commute hK.2 hK'.2 with h | h
  · have := Subgroup.subgroupOf_inj.1 h
    rw [inf_eq_left.mpr hK.1, inf_eq_left.mpr hK'.1] at this
    exact absurd this hne
  · intro k hk k' hk'
    have h1 : (⟨k, hK.1 hk⟩ : ↥(Cen t)) ∈ K.subgroupOf (Cen t) := hk
    have h2 : (⟨k', hK'.1 hk'⟩ : ↥(Cen t)) ∈ K'.subgroupOf (Cen t) := hk'
    have h3 := Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h h1) _ h2
    exact (congrArg Subtype.val h3).symm

end Bridge

end CFSG.GH74.E2
