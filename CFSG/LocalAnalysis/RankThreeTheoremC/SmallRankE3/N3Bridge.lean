module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

variable {X : Type} [Group X] [Finite X] {p : ℕ} {P : Sylow p X} {x z : X}

theorem plane_basic_E3 (hpl : Plane63E3 p X P x z) :
    x ^ p = 1 ∧ z ^ p = 1 ∧ x * z = z * x ∧ z ≠ 1 := by
  have hp := hpl.prime
  have hxB : x ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_left (mem_zpowers x)
  have hzB : z ∈ (zpowers x ⊔ zpowers z : Subgroup X) := Subgroup.mem_sup_right (mem_zpowers z)
  have hxp : x ^ p = 1 := hpl.plane.isElemAbelian.2 x hxB
  have hzp : z ^ p = 1 := hpl.plane.isElemAbelian.2 z hzB
  have hxz : x * z = z * x := by
    have := hpl.plane.isElemAbelian.1.is_comm.comm (⟨x, hxB⟩ : ↥(zpowers x ⊔ zpowers z))
      ⟨z, hzB⟩
    exact congrArg Subtype.val this
  refine ⟨hxp, hzp, hxz, fun h => ?_⟩
  have h1 : (zpowers x ⊔ zpowers z : Subgroup X) = zpowers x := by
    rw [h, zpowers_one_eq_bot, sup_bot_eq]
  have h2 : Nat.card (zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hxp)
  have h3 := hpl.plane.card_eq
  rw [h1] at h3
  have h4 : p ^ 2 ≤ p := h3 ▸ h2
  have h5 : 1 < p := hp.one_lt
  nlinarith

theorem section_dvd_component_E3 (hpl : Plane63E3 p X P x z) (hβ : BetaStructure p X P x z)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {S : Type} [Group S] [IsSimpleGroup S]
    (hnab : ¬ ∀ a b : S, a * b = b * a) (hpS : p ∣ Nat.card S)
    (hS : IsSecOf (centralizer ({x} : Set X)) S)
    (C : ComponentIndex (X ⧸ primeComplementCore (G := X) p)) :
    Nat.card S ∣ Nat.card ↥C.1 := by
  have hp := hpl.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  have hD3 : ¬ p ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (primeComplementCore_coprime p)
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  obtain ⟨hxp, hzp, hxz, hz1⟩ := plane_basic_E3 hpl
  have hker : ¬ p ∣ Nat.card (π.ker ⊓ centralizer ({x} : Set X) : Subgroup X) := fun h =>
    hD3 (h.trans (by
      rw [hπ, QuotientGroup.ker_mk']
      exact Subgroup.card_dvd_of_le inf_le_left))
  have hS' := hS.map_hom π hpS hker hnab
  have hrank : Open.pRank p ((centralizer ({x} : Set X)).map π) ≤ 2 :=
    (pRank_map_le_of_coprime_ker hp π hker).trans hpl.rank_centralizer
  have hzb1 : (z : X ⧸ D) ≠ 1 := by
    intro h
    have hzD : z ∈ D := (QuotientGroup.eq_one_iff z).mp h
    have hord : orderOf z = p := orderOf_eq_prime hzp hz1
    apply hD3
    rw [← hord, ← Subgroup.orderOf_mk z hzD]
    exact orderOf_dvd_natCard _
  have hzbp : (z : X ⧸ D) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hzp, QuotientGroup.mk_one]
  have hxbp : (x : X ⧸ D) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]
  have hxzb : (x : X ⧸ D) * (z : X ⧸ D) = (z : X ⧸ D) * (x : X ⧸ D) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxz]
  have hxU : (x : X ⧸ D) ∈ (centralizer ({x} : Set X)).map π :=
    ⟨x, mem_centralizer_singleton_iff.mpr rfl, rfl⟩
  have hzU : (z : X ⧸ D) ∈ (centralizer ({x} : Set X)).map π :=
    ⟨z, mem_centralizer_singleton_iff.mpr hxz.symm, rfl⟩
  have hUc : ∀ g ∈ (centralizer ({x} : Set X)).map π, g * (x : X ⧸ D) = (x : X ⧸ D) * g := by
    rintro _ ⟨u, hu, rfl⟩
    show π u * π x = π x * π u
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hu]
  have hKX : CFSG.Open.IsKGroup X :=
    (CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup).mp hpl.catalog
  have hKY : CFSG.Open.IsKGroup (X ⧸ D) :=
    hKX.of_surjective π (QuotientGroup.mk'_surjective D)
  haveI : IsSimpleGroup ↥C.1 := isSimpleGroup_of_component C.2 (hβ.centreless C)
  have hcat : IsCatalogGroup ↥C.1 :=
    ((isSecOf_self C.1).mono le_top).isCatalogGroup
      (exists_noncomm_of_component C.2 (hβ.centreless C)) hKY
  exact section_card_dvd_component hp hβ.centreless hβ.card_components hxbp hxzb hzb1 hzbp
    hβ.z_mem_layer hβ.transitive hxU hzU hUc hrank C hcat hSch hnab hpS hS'

theorem pRank_ge_of_beta_E3 (hβ : BetaStructure p X P x z)
    (hI : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input10_20_3)
    (C₀ : ComponentIndex (X ⧸ primeComplementCore (G := X) p)) {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) (hfC : f ∣ Nat.card ↥C₀.1) : p ≤ Open.pRank f (⊤ : Subgroup X) := by
  set D : Subgroup X := primeComplementCore (G := X) p with hD
  set π : X →* X ⧸ D := QuotientGroup.mk' D with hπ
  set X₁ : Subgroup X := (layer (X ⧸ D)).comap π with hX₁
  let ψ : ↥X₁ →* ↥(layer (X ⧸ D)) :=
    (π.comp X₁.subtype).codRestrict (layer (X ⧸ D)) (fun m => m.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨l, hl⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective D l
    exact ⟨⟨m, hl⟩, rfl⟩
  have hker : ψ.ker = D.subgroupOf X₁ := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  let e : ↥X₁ ⧸ D.subgroupOf X₁ ≃* (Fin p → ↥C₀.1) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).trans
      (layerPiEquiv hβ.centreless hβ.transitive hβ.card_components C₀)
  haveI : IsSimpleGroup ↥C₀.1 := isSimpleGroup_of_component C₀.2 (hβ.centreless C₀)
  have h2 := ((hI ↥X₁ (D.subgroupOf X₁) ↥C₀.1 p inferInstance
    (exists_noncomm_of_component C₀.2 (hβ.centreless C₀)) ⟨e⟩ f hf hf2).2
    (one_le_pRank_of_dvd hf hfC))
  rw [pRank_top_subtype hf.one_lt] at h2
  exact h2.trans (CFSG.SectionRank.pRank_mono hf.one_lt le_top)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
