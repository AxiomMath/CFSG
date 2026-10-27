module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointStructure
import CFSG.LocalAnalysis.RankFourTheoremC.PPointInvTwo
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_rankTwoMaximal_not_le_of_reduced {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M U : Subgroup G} {x : G} (hU : IsPGroup p U) (hUC : U ≤ centralizer ({x} : Set G))
    (V : Subgroup (RedCent p x)) (hV2 : IsPGroup 2 V)
    (hUV : ∀ (u : G) (hu : u ∈ U), QuotientGroup.mk' (primeComplementCore
      (G := centralizer ({x} : Set G)) p) ⟨u, hUC hu⟩ ∈ normalizer (V : Set (RedCent p x)))
    (hVM : ¬ V ≤ redCentM p M x) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Ob : Subgroup C := primeComplementCore (G := C) p with hOb
  set ρ : C →* RedCent p x := QuotientGroup.mk' Ob with hρ
  set Ĉ : Subgroup C := V.comap ρ with hĈ
  set Ĉg : Subgroup G := Ĉ.map C.subtype with hĈg
  have hmap : ∀ u ∈ U, Ĉg.map (MulAut.conj u).toMonoidHom ≤ Ĉg := by
    intro u hu
    rintro _ ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨⟨u, hUC hu⟩ * c * ⟨u, hUC hu⟩⁻¹, ?_, rfl⟩
    show ρ (⟨u, hUC hu⟩ * c * ⟨u, hUC hu⟩⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hUV u hu) _).mp hc
  have hUĈ : U ≤ normalizer (Ĉg : Set G) := fun u hu => by
    rw [mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hmap u hu) fun y hy => ?_
    have hz : (MulAut.conj u⁻¹) y ∈ Ĉg := hmap u⁻¹ (U.inv_mem hu) ⟨y, hy, rfl⟩
    exact ⟨_, hz, show u * (u⁻¹ * y * u⁻¹⁻¹) * u⁻¹ = y by group⟩
  have hcop : p.Coprime (Nat.card Ĉg) := by
    by_contra hnc
    have hdvd : p ∣ Nat.card Ĉg := by
      by_contra hnd
      exact hnc (hp.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Ĉg) p hdvd
    obtain ⟨c, hc, hcg⟩ := g.2
    have hgp : (g : G) ^ p = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg Subtype.val this
    have hcp : c ^ p = 1 := by
      apply C.subtype_injective
      rw [map_pow, hcg, map_one]
      exact hgp
    have hρc : ρ c = 1 := by
      obtain ⟨k, hk⟩ := hV2 ⟨ρ c, hc⟩
      have h1 : orderOf (ρ c) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hcp, map_one])
      have h2 : orderOf (ρ c) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hcop' : Nat.Coprime p (2 ^ k) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' h1 h2)
    have hcOb : c ∈ Ob := (QuotientGroup.eq_one_iff c).mp hρc
    have hordc : orderOf c = p := by
      rw [← Subgroup.orderOf_coe c]
      have hcg' : (c : G) = (g : G) := hcg
      rw [hcg', Subgroup.orderOf_coe, hg]
    have hdvdOb : p ∣ Nat.card Ob := by
      have := orderOf_dvd_natCard (⟨c, hcOb⟩ : Ob)
      rwa [Subgroup.orderOf_mk, hordc] at this
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (primeComplementCore_coprime (G := C) p) hdvdOb)
  have hUbot : U ≤ normalizer (((⊥ : Subgroup G)) : Set G) := fun u _ => by
    rw [mem_normalizer_iff]
    intro h
    simp
  obtain ⟨W, -, hW⟩ := exists_invariantTwoMaximalWithin_containing U Ĉg ⊥ bot_le
    (IsPGroup.of_card (n := 0) (by simp)) hUbot
  have hWs : CFSG.ABGLocalTools.IsSylowOf 2 W Ĉg :=
    isSylowOf_two_of_invariantTwoMaximalWithin hp hU hUĈ hcop hW
  have hĈC : Ĉg ≤ C := Subgroup.map_subtype_le _
  have hWC : W ≤ C := hW.1.trans hĈC
  set W' : Subgroup C := W.subgroupOf C with hW'
  have hW'W : W'.map C.subtype = W := by
    rw [hW', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWC]
  have hW'Ĉ : CFSG.ABGLocalTools.IsSylowOf 2 W' Ĉ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, hW'W]
    exact hWs
  obtain ⟨Q, hQ⟩ := hW'Ĉ
  set φ : Ĉ →* V := (ρ.comp Ĉ.subtype).codRestrict V (fun c => c.2) with hφdef
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective Ob (v : RedCent p x)
    exact ⟨⟨c, show ρ c ∈ V from by rw [hρ, hc]; exact v.2⟩, Subtype.ext hc⟩
  have hVtop : IsPGroup 2 ↥(⊤ : Subgroup V) := hV2.of_equiv Subgroup.topEquiv.symm
  have hQtop : (⊤ : Subgroup V) = (Q.mapSurjective hφ : Subgroup V) :=
    (Q.mapSurjective hφ).3 hVtop le_top
  have hVW : ∀ v ∈ V, ∃ c ∈ W', ρ c = v := by
    intro v hv
    have hv' : (⟨v, hv⟩ : V) ∈ (Q.mapSurjective hφ : Subgroup V) := by
      rw [← hQtop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hv'
    obtain ⟨q, hq, hqv⟩ := hv'
    refine ⟨(q : C), ?_, congrArg Subtype.val hqv⟩
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  have hWM : ¬ W ≤ M := by
    intro hWM
    refine hVM fun v hv => ?_
    obtain ⟨c, hcW, hcv⟩ := hVW v hv
    exact ⟨c, mem_subgroupOf.mpr ⟨c.2, hWM (by rw [← hW'W]; exact ⟨c, hcW, rfl⟩)⟩, hcv⟩
  obtain ⟨S₁, hWS, hS₁⟩ := exists_maximal_invariant_two_subgroup_containing U W hW.2.1 hW.2.2.1
  exact ⟨S₁, hS₁, fun h => hWM (hWS.trans h)⟩

end CFSG.LocalAnalysis.RankFourTheoremC
