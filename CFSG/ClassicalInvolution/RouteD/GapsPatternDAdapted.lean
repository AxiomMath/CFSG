module

public import CFSG.ClassicalInvolution.RouteD.GapsPatternDMain
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD5
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv InClass
  IsClassicalMember LocalOddCentral ExactMembers centralizingMembers ConjInvariant LieSystemData
  centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.Balance (iSup_rankOneImage_eq_range rankOneImage)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]
  {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {m : ℕ}

theorem PartnerPatternD.of_toral_normal_of_adapted (hm : 5 ≤ m) (hMFZ : FundNoncentral p)
    (hF : OrthFacts (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f .POmegaPlus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ))
    (hadapt : ∀ (nd : DNodes p f m Ω K) {β : Subgroup G} {t : G}, β ∈ Ω →
      IsClassicalMember p f β t → (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
      ∀ {pp : Fin m}, (∀ a, a ≠ pp → Commutes β (nd.J a)) → ¬ Commutes β (nd.J pp) →
        conjSub t (nd.J pp) = nd.J pp →
        pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (nd.J pp)) :
    PartnerPatternD p f m Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht hKβ
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaPlus m p f Fact.out trivial hadm
  obtain ⟨e, he⟩ := exists_equiv_cartan_plus (p := p) (f := f) (by omega : 3 ≤ m)
  obtain ⟨j, hj, hjimg, hjK, hjc, hjp⟩ := TCtx.exists_nodes_plus' (by omega : 4 ≤ m) c e he
  have hPat : PatternLemma (modelUniv .POmegaPlus m p f Fact.out).D.cartan :=
    PatternLemma.of_equiv e (fun a b => by rw [he, cartanD_eq]) (patternLemma_D (by omega))
  obtain ⟨k₀, v, hTT⟩ := hT
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨N, hNz, hNQ, hKN, hβN⟩ :=
      exists_moved_layer_member hF c hsingle hshape hβ ht hKβ hfixM
    have hNK : N ≠ K := fun h => by
      rw [h] at hKN
      exact not_commutes_self_of_mem hΩ c.hK hKN
    obtain ⟨R, hR, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
    have hgen := iSup_rankOneImage_eq_range .POmegaPlus m p f Fact.out trivial hadm c.d.ψ k₀
    have hfixrange : ∀ x ∈ c.d.ψ.range, locAut hΩ.conjInvariant htz x = x := by
      intro x hx
      rw [← hgen] at hx
      let Fix : Subgroup (locQuot Ω z) :=
        MonoidHom.eqLocus (locAut hΩ.conjInvariant htz).toMonoidHom (MonoidHom.id _)
      have hle : (⨆ γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots,
          rankOneImage (modelUniv .POmegaPlus m p f Fact.out).D c.d.ψ k₀ γ) ≤ Fix := by
        refine iSup₂_le fun γ hγ y hy => ?_
        exact ((hTT γ hγ).2).mpr (by simp [hv0, charOf]) y hy
      exact hle hx
    have hNt : N ≤ Subgroup.centralizer ({t} : Set G) :=
      (locAut_fixed_iff hΩ c.hP1 htz hNz).mpr fun x hx => hfixrange x (by
        rw [hNR] at hx
        obtain ⟨r, -, rfl⟩ := hx
        exact ⟨r, rfl⟩)
    exact hβN (commutes_partner_of_centralizes hMFZ c hsingle hshape hβ ht hKβ hNz hNt hKN)
  obtain ⟨y, hy, p₀, hfixed⟩ := exists_adapted_y_normal hΩ.conjInvariant c.d.ψ hct hPat htz v hv k₀
    hTT hjimg
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmemy : ∀ a, conjSub y (j a) ∈ centralizingMembers Ω {z} := fun a => by
    have := centralizingMembers_conj hΩ.conjInvariant y z
    rw [hyz] at this
    rw [this]
    exact ⟨j a, (hj a).1, rfl⟩
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have := centralizingMembers_conj hΩ.conjInvariant t z
    rw [htz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  have hex : ∀ a : Fin m, ∃ w, IsClassicalMember p f (conjSub y (j (e.symm a))) w := fun a => by
    obtain ⟨w₀, hw₀⟩ := hΩ.classical (j (e.symm a)) (hj _).1.1
    exact ⟨_, hw₀.conj y⟩
  choose w hw using hex
  let nd : DNodes p f m Ω K :=
    { J := fun a => conjSub y (j (e.symm a))
      w := w
      mem := fun a => hΩ.conjInvariant y _ (hj _).1.1
      cl := hw
      commK := fun a => commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _)
      comm := fun a b hab h1 h2 =>
        (hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1)
          (by simpa using h2)).conjSub y
      pair := fun a b h => by
        obtain ⟨W, hW⟩ := hjp (e.symm a) (e.symm b) (by simpa using h)
        exact ⟨_, ModelFacts.linearBlockStandardPair_map_conj hW y⟩ }
  have hfix' : ∀ a, a ≠ e p₀ → Commutes β (nd.J a) := fun a ha => by
    have hne : e.symm a ≠ p₀ := fun h => ha (by rw [← h]; exact (e.apply_symm_apply a).symm)
    have h1 := (hfixed (e.symm a)).1.mpr hne
    have hNt := (locAut_fixed_iff hΩ c.hP1 htz (hmemy (e.symm a))).mpr h1
    exact commutes_partner_of_centralizes hMFZ c hsingle hshape hβ ht hKβ (hmemy _) hNt
      (commutes_conjSub_of_mem_normalizer (c.locLayer_le_normalizer hy) (hjK _))
  have hmov' : ¬ Commutes β (nd.J (e p₀)) := fun h => by
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ] at h
    have hNt : conjSub y (j p₀) ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h t ht.mem n hn).symm
    have := (hfixed p₀).1.mp ((locAut_fixed_iff hΩ c.hP1 htz (hmemy p₀)).mp hNt)
    exact this rfl
  have hnorm' : conjSub t (nd.J (e p₀)) = nd.J (e p₀) := by
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ]
    have h1 := (hfixed p₀).2
    rw [locAut_locImg hΩ.conjInvariant htz] at h1
    exact locImg_injOn hΩ c.hP1 (hmemt _ (hmemy p₀)) (hmemy p₀) h1
  obtain ⟨hp0, hlin⟩ := hadapt nd hβ ht hKβ hfix' hmov' hnorm'
  have hFix : ∀ a : Fin m, 1 ≤ a.val → ∀ x ∈ locImg Ω z (conjSub y (j (e.symm a))),
      locAut hΩ.conjInvariant htz x = x := fun a ha => by
    refine (hfixed (e.symm a)).1.mpr fun h => ?_
    have h1 : a = e p₀ := by rw [← h]; exact (e.apply_symm_apply a).symm
    have := congrArg Fin.val h1
    omega
  refine PartnerPatternD.of_locAut c (j := fun a : Fin m => j (e.symm a)) (fun a => (hj _).1)
    (fun a => hjK _) ?_ ?_ hy htz hFix ?_
  · intro a b hab h1 h2
    exact hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1) (by simpa using h2)
  · intro a b h
    exact hjp (e.symm a) (e.symm b) (by simpa using h)
  · intro a ha
    have h1 : a = e p₀ := Fin.ext (by omega)
    subst h1
    have hJ : nd.J (e p₀) = conjSub y (j p₀) := by
      show conjSub y (j (e.symm (e p₀))) = _
      rw [Equiv.symm_apply_apply]
    rw [hJ] at hlin
    simpa using hlin

theorem PartnerPatternD.of_toral_normal_five (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus 5 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 5 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z)
    (hT : ToralNormalD c (partner_involution_commutes c.hp2 c.hz ht hKβ)) :
    PartnerPatternD p f 5 Ω K β t :=
  PartnerPatternD.of_toral_normal_of_adapted (le_refl 5) hMFZ (orthFacts_plus c.hp2 (le_refl 5) c.hq) c
    hsingle hshape hβ ht hKβ hfixM hT fun nd {_ _} hβ' ht' hKβ' {_} hfix hmov hnorm =>
    adapted_pattern_D5 (orthFacts_plus c.hp2 (le_refl 5) c.hq) c hsingle hshape nd hβ' ht' hKβ' hfix
      hmov hnorm

end CFSG.ClassicalInvolution.RouteD.Gaps
