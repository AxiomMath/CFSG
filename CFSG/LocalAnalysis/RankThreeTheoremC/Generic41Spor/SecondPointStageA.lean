module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWAux
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC
  exists_isElemAbelian_card_sq_of_nonabelian)

variable {G : Type} [Group G] [Finite G]

theorem second_point_S_decomp (hS : Setting G) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {P : Sylow p G}
    {M : Subgroup G} {u : G} (hgen : IsGenericPoint p P M u) {J : Subgroup G}
    (hJC : J ≤ Subgroup.centralizer ({u} : Set G))
    (hCJ : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G))
    (hperf : Group.IsPerfect J) (hlt : rankThreePrimeCore p J < J)
    (hmin : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) (hnot : ¬ J ≤ M)
    {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) (hQ : SecondPointFacts p Q) :
    ∃ Z : Subgroup G, IsCyclic Z ∧ u ∈ Z ∧ Z ≤ u3S P u ∧
      (∀ z ∈ Z, ∀ t ∈ u3T P u J, z * t = t * z) ∧ u3T P u J ⊓ Z = ⊥ ∧ u3T P u J ⊔ Z = u3S P u := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  set O : Subgroup G := rankThreePrimeCore p J with hO
  have hOJ : O ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hQZ : Subgroup.center Q = ⊥ := u3main_center_bot hOJ hperf hlt hmin ψ hψ hker
  obtain ⟨ρ, hρ⟩ := spw_exists_rho (p := p) hCJ ψ hψ hker
  obtain ⟨Tsyl', hTsyl', hTinj, hcardS⟩ := spw_sylow_data hgen hJC hCJ ψ hψ hker
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ O := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := by
    have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ O) := P.isPGroup'.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hdvd : Nat.card ((P : Subgroup G) ⊓ O : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ∣ Nat.card O := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
      exact (hp.coprime_iff_not_dvd.mp hOcop) this
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  set T : Subgroup G := u3T P u J with hT
  set S : Subgroup G := u3S P u with hS'
  have hTJ : T ≤ J := inf_le_right
  have hTS : T ≤ S := inf_le_left
  have hSP : S ≤ (P : Subgroup G) := inf_le_left
  have hSC : S ≤ C := inf_le_right
  have hTP : T ≤ (P : Subgroup G) := hTS.trans hSP
  have hTC : T ≤ C := hTJ.trans hJC
  have hρt : ∀ (t : G) (ht : t ∈ T), ρ ⟨t, hTC ht⟩ = MulAut.conj (ψ ⟨t, hTJ ht⟩) := by
    intro t ht
    ext q
    obtain ⟨j, rfl⟩ := hψ q
    have hj : t * (j : G) * t⁻¹ ∈ J := J.mul_mem (J.mul_mem (hTJ ht) j.2) (J.inv_mem (hTJ ht))
    have h1 := hρ ⟨t, hTC ht⟩ j hj
    have e1 : (⟨t * (j : G) * t⁻¹, hj⟩ : J) = ⟨t, hTJ ht⟩ * j * (⟨t, hTJ ht⟩ : J)⁻¹ :=
      Subtype.ext rfl
    rw [MulAut.conj_apply, h1, e1, map_mul, map_mul, map_inv]
  have hρinj : ∀ (t : G) (ht : t ∈ T), ρ ⟨t, hTC ht⟩ = 1 → t = 1 := by
    intro t ht h1
    have hcen : ψ ⟨t, hTJ ht⟩ ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h2 := congrArg (fun φ : MulAut Q => φ q) ((hρt t ht).symm.trans h1)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc q * ψ ⟨t, hTJ ht⟩ = (ψ ⟨t, hTJ ht⟩ * q * (ψ ⟨t, hTJ ht⟩)⁻¹) * ψ ⟨t, hTJ ht⟩ := by
            rw [h2]
        _ = ψ ⟨t, hTJ ht⟩ * q := by group
    rw [hQZ, Subgroup.mem_bot] at hcen
    have h3 : t ∈ O := (hOker _).mp hcen
    have h4 : t ∈ (P : Subgroup G) ⊓ O := ⟨hTP ht, h3⟩
    rw [hPO, Subgroup.mem_bot] at h4
    exact h4
  let S' : Subgroup C := S.subgroupOf C
  let T' : Subgroup C := T.subgroupOf C
  have hT'S' : T' ≤ S' := fun t ht => hTS ht
  have hinjρ : Function.Injective (ρ.comp T'.subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => by
      have h1 := hρinj ((a : C) : G) a.2 ha
      apply Subtype.ext
      apply Subtype.ext
      exact h1
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv
  have hmapT' : Nat.card (T'.map ρ) = Nat.card T := by
    have e1 : (ρ.comp T'.subtype).range = T'.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinjρ).toEquiv, hT'card]
  have hSp : IsPGroup p S' := (P.isPGroup'.to_le hSP).comap_subtype
  have hdvdA : Nat.card (S'.map ρ) ∣ Nat.card T := by
    have := hQ.autBound Tsyl' (S'.map ρ) (hSp.map ρ)
    rwa [hcardS] at this
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hAeq : T'.map ρ = S'.map ρ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hT'S')
      (by rw [hmapT']; exact Nat.le_of_dvd hpos hdvdA)
  let Z : Subgroup G := (S' ⊓ ρ.ker).map C.subtype
  have hZmem : ∀ z : G, z ∈ Z ↔ ∃ hzC : z ∈ C, z ∈ S ∧ ρ ⟨z, hzC⟩ = 1 := by
    intro z
    constructor
    · rintro ⟨c, ⟨hcS, hcker⟩, rfl⟩
      exact ⟨c.2, hcS, hcker⟩
    · rintro ⟨hzC, hzS, hz1⟩
      exact ⟨⟨z, hzC⟩, ⟨hzS, hz1⟩, rfl⟩
  have hZS : Z ≤ S := fun z hz => by
    obtain ⟨-, hzS, -⟩ := (hZmem z).mp hz
    exact hzS
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have huS : u ∈ S := ⟨hgen.1, huC⟩
  have huZ : u ∈ Z := by
    refine (hZmem u).mpr ⟨huC, huS, ?_⟩
    ext q
    obtain ⟨j, rfl⟩ := hψ q
    have hj : u * (j : G) * u⁻¹ ∈ J := by
      have : u * (j : G) * u⁻¹ = j := by
        have h1 : (j : G) * u = u * (j : G) := Subgroup.mem_centralizer_singleton_iff.mp (hJC j.2)
        rw [← h1, mul_inv_cancel_right]
      rw [this]; exact j.2
    rw [hρ ⟨u, huC⟩ j hj, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    have h1 : (j : G) * u = u * (j : G) := Subgroup.mem_centralizer_singleton_iff.mp (hJC j.2)
    show u * (j : G) * u⁻¹ = j
    rw [← h1, mul_inv_cancel_right]
  have hZT : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z := by
    intro z hz t ht
    obtain ⟨hzC, hzS, hz1⟩ := (hZmem z).mp hz
    have htJ := hTJ ht
    have hj : z * t * z⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hCJ hzC) t).mp htJ
    have h1 := hρ ⟨z, hzC⟩ ⟨t, htJ⟩ hj
    rw [hz1, MulAut.one_apply] at h1
    have h2 : ψ (⟨z * t * z⁻¹, hj⟩ * (⟨t, htJ⟩ : J)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← h1, mul_inv_cancel]
    have h3 : z * t * z⁻¹ * t⁻¹ ∈ O := (hOker _).mp h2
    have hzP := hSP hzS
    have htP := hTP ht
    have h4 : z * t * z⁻¹ * t⁻¹ ∈ (P : Subgroup G) ⊓ O :=
      ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hzP htP)
        ((P : Subgroup G).inv_mem hzP)) ((P : Subgroup G).inv_mem htP), h3⟩
    rw [hPO, Subgroup.mem_bot] at h4
    calc z * t = (z * t * z⁻¹ * t⁻¹) * (t * z) := by group
      _ = t * z := by rw [h4, one_mul]
  have hTZ : T ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgC, hgS, hg1⟩ := (hZmem g).mp hg.2
    have h1 := hρinj g hg.1 hg1
    rw [Subgroup.mem_bot]
    exact h1
  have hsup : T ⊔ Z = S := by
    apply le_antisymm
    · exact sup_le hTS hZS
    · intro s hs
      have hsC : s ∈ C := hSC hs
      have hsS' : (⟨s, hsC⟩ : C) ∈ S' := hs
      have hmem : ρ ⟨s, hsC⟩ ∈ T'.map ρ := by
        rw [hAeq]
        exact Subgroup.mem_map_of_mem ρ hsS'
      obtain ⟨t, htT', htρ⟩ := hmem
      have htT : (t : G) ∈ T := htT'
      have hz : ((t⁻¹ * ⟨s, hsC⟩ : C) : G) ∈ Z := by
        rw [hZmem]
        refine ⟨(t⁻¹ * ⟨s, hsC⟩).2, ?_, ?_⟩
        · rw [Subgroup.coe_mul, Subgroup.coe_inv]
          exact S.mul_mem (S.inv_mem (hTS htT)) hs
        · show ρ (t⁻¹ * ⟨s, hsC⟩) = 1
          rw [map_mul, map_inv, htρ, inv_mul_cancel]
      have hs' : s = (t : G) * ((t⁻¹ * ⟨s, hsC⟩ : C) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [hs']
      exact Subgroup.mul_mem_sup htT hz
  have hET : ∃ ET : Subgroup G, ET ≤ T ∧ IsElemAbelian p ET ∧ Nat.card ET = p ^ 2 := by
    rcases spw_T_structure hgen hJC hCJ ψ hψ hker hQ with ⟨hc2, hel⟩ | ⟨hc3, hexp, hnab⟩
    · exact ⟨T, le_rfl, hel, hc2⟩
    · obtain ⟨ET, hETT, hETel, hETcard, -⟩ :=
        exists_isElemAbelian_card_sq_of_nonabelian hc3 hexp hnab
      exact ⟨ET, hETT, hETel, hETcard⟩
  have hZp : IsPGroup p ↥Z := P.isPGroup'.to_le (hZS.trans hSP)
  have hZcyc : IsCyclic Z := by
    by_contra hnc
    haveI : Fact (IsPGroup p ↥Z) := ⟨hZp⟩
    obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hnc
    haveI : CFSG.IsElementaryAbelian p (E.map Z.subtype) := CFSG.IsElementaryAbelian.map_subtype
    set E' : Subgroup G := E.map Z.subtype with hE'
    have hE'card : Nat.card E' = p ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective Z.subtype_injective, hEcard]
    have hE'elem : IsElemAbelian p E' :=
      ⟨inferInstance, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
    have hE'Z : E' ≤ Z := by
      rintro _ ⟨e', -, rfl⟩
      exact e'.2
    obtain ⟨ET, hETT, hETel, hETcard⟩ := hET
    have hcomm : ∀ a ∈ ET, ∀ b ∈ E', Commute a b := fun a ha b hb =>
      (hZT b (hE'Z hb) a (hETT ha)).symm
    have hdisj : ET ⊓ E' = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have : g ∈ T ⊓ Z := ⟨hETT hg.1, hE'Z hg.2⟩
      rwa [hTZ] at this
    have h4 := plane_add_le_pRank hp hETel hE'elem hETcard hE'card hcomm hdisj
      (H := S) (hETT.trans hTS) (hE'Z.trans hZS)
    have h3 : CFSG.Open.pRank p S = 3 := hgen.2.2.2
    omega
  exact ⟨Z, hZcyc, huZ, hZS, hZT, hTZ, hsup⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
