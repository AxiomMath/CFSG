module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Four
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Tools
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.GSThmB
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem exists_congr_oddBarConj_eq {a b : G} {K : Subgroup G} (hK : IsTwoComponentAt a K)
    (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel K)
    (hKb : IsTwoComponentAt b (footeFixed K b)) :
    ∃ φ : K ⧸ pPrimeCore 2 K ≃* footeFixed K b ⧸ pPrimeCore 2 (footeFixed K b),
      ∀ (d : G) (hdN : d ∈ normalizer (K : Set G)) (hdNb : d ∈ normalizer (footeFixed K b : Set G)),
        d ∈ centralizer ({b} : Set G) →
          MulAut.congr φ (oddBarConj K ⟨d, hdN⟩) = oddBarConj (footeFixed K b) ⟨d, hdNb⟩ := by
  obtain ⟨φ, -, hφc⟩ := exists_quotient_mulEquiv_footeFixed hK hb hbK hKb
  refine ⟨φ, fun d hdN hdNb hdb => ?_⟩
  ext y
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm (y₀ : footeFixed K b ⧸ _))
  have hφx : φ (x : K ⧸ pPrimeCore 2 K) = (y₀ : footeFixed K b ⧸ _) := by
    rw [hx, MulEquiv.apply_symm_apply]
  have hx' : d * (x : G) * d⁻¹ ∈ K := (mem_normalizer_iff.mp hdN x).mp x.2
  have hy' : d * (y₀ : G) * d⁻¹ ∈ footeFixed K b := (mem_normalizer_iff.mp hdNb y₀).mp y₀.2
  have hc := hφc d (mem_inf.mpr ⟨hdN, hdb⟩) x ⟨_, hx'⟩ y₀ ⟨_, hy'⟩ rfl rfl hφx
  change φ (oddBarConj K ⟨d, hdN⟩ (φ.symm (y₀ : footeFixed K b ⧸ _))) = _
  rw [← hx, oddBarConj_apply_mk, hc, oddBarConj_apply_mk]

theorem mem_coreActionKernel_iff_of_footeFixed {a b : G} {K : Subgroup G}
    (hK : IsTwoComponentAt a K) (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel K)
    (hKb : IsTwoComponentAt b (footeFixed K b)) {d : G} (hdN : d ∈ normalizer (K : Set G))
    (hdNb : d ∈ normalizer (footeFixed K b : Set G)) (hdb : d ∈ centralizer ({b} : Set G)) :
    d ∈ coreActionKernel K ↔ d ∈ coreActionKernel (footeFixed K b) := by
  obtain ⟨φ, hφ⟩ := exists_congr_oddBarConj_eq hK hb hbK hKb
  have h1 := hφ d hdN hdNb hdb
  constructor
  · intro hd
    apply mem_coreActionKernel_of_oddBarConj_eq_one (g := ⟨d, hdNb⟩)
    rw [← h1, oddBarConj_eq_one_of_mem_coreActionKernel (g := ⟨d, hdN⟩) hd, map_one]
  · intro hd
    apply mem_coreActionKernel_of_oddBarConj_eq_one (g := ⟨d, hdN⟩)
    have h2 := oddBarConj_eq_one_of_mem_coreActionKernel (g := ⟨d, hdNb⟩) hd
    rw [← h1] at h2
    exact (map_eq_one_iff _ (MulAut.congr φ).injective).mp h2

theorem oddBarConj_mem_range_conj_of_footeFixed {a b : G} {K : Subgroup G}
    (hK : IsTwoComponentAt a K) (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel K)
    (hKb : IsTwoComponentAt b (footeFixed K b)) {d : G} (hdN : d ∈ normalizer (K : Set G))
    (hdNb : d ∈ normalizer (footeFixed K b : Set G)) (hdb : d ∈ centralizer ({b} : Set G))
    (hin : oddBarConj K ⟨d, hdN⟩ ∈ (MulAut.conj : K ⧸ pPrimeCore 2 K →* _).range) :
    oddBarConj (footeFixed K b) ⟨d, hdNb⟩ ∈
      (MulAut.conj : footeFixed K b ⧸ pPrimeCore 2 (footeFixed K b) →* _).range := by
  obtain ⟨φ, hφ⟩ := exists_congr_oddBarConj_eq hK hb hbK hKb
  obtain ⟨k, hk⟩ := hin
  refine ⟨φ k, ?_⟩
  rw [← hφ d hdN hdNb hdb, ← hk, FooteLit.MulAut.congr_conj]

@[expose] noncomputable def oddCoreRestriction {D K : Subgroup G} (hDK : D ≤ K) :
    D →* K ⧸ pPrimeCore 2 K :=
  (QuotientGroup.mk' (pPrimeCore 2 K)).comp (Subgroup.inclusion hDK)

theorem oddCoreRestriction_apply {D K : Subgroup G} (hDK : D ≤ K) (d : D) :
    oddCoreRestriction hDK d =
      ((Subgroup.inclusion hDK d : K) : K ⧸ pPrimeCore 2 K) := rfl

theorem oddCoreRestriction_surjective {D K : Subgroup G} (hDK : D ≤ K)
    (hsup : D ⊔ FooteLit.oddCoreIn K = K) :
    Function.Surjective (oddCoreRestriction hDK) := by
  obtain ⟨-, e, he⟩ := restriction_quotient_mulEquiv hDK hsup
  intro q
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (e.symm q)
  refine ⟨d, ?_⟩
  have h1 : e (QuotientGroup.mk d) = q := by
    rw [hd, MulEquiv.apply_symm_apply]
  rw [oddCoreRestriction_apply]
  exact (he d (hDK d.2)).symm.trans h1

end CFSG.ComponentClassification.Foote47
