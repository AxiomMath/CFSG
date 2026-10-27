module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.LocalAnalysis.SectionRank.SylowWitness
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

theorem ker_eq_bot_of_section_of_perfect {E S : Type*} [Group E] [Group.IsPerfect E] [Group S]
    (π : E →* S) (hC : π.ker ≤ Subgroup.center E) (σ : S →* E) (hσ : ∀ x, π (σ x) = x) :
    π.ker = ⊥ := by
  have htop : σ.range = ⊤ := EvenCover.eq_top_of_forall_mul_center fun x =>
    ⟨σ (π x), ⟨π x, rfl⟩, hC (by rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel])⟩
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨s, rfl⟩ : c ∈ σ.range := htop ▸ Subgroup.mem_top c
  rw [MonoidHom.mem_ker, hσ] at hc
  rw [hc, map_one]
  exact one_mem _

theorem not_two_dvd_of_odd {n : ℕ} (h : Odd n) : ¬ 2 ∣ n := fun h2 =>
  (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 h2)

theorem g2_even_central_odd_extension_splitting
    {k : Type} [Field k] [Finite k] [CharP k 2]
    {E : Type*} [Group E] [Finite E] {π : E →* adjointGroup .G2 k} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : adjointGroup .G2 k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : adjointGroup .G2 k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : ¬ 2 ∣ Nat.card π.ker := not_two_dvd_of_odd hodd
  refine exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2_lift (p := 2)
    (g2_isCTGroupDatum k) (g2_steinbergExtras k)
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := k) _ (adjDatum_roots _ k))
    (fun i => Adjoint.exists_sl2_hom_xPar (g2_exists_sl2_hom i)) hπ hker hC fun ρ => ?_)
  obtain ⟨ρ', hρ', -⟩ := EvenCover.sl2_existsUnique_lift hπ hker hC ρ
  exact ⟨ρ', fun g => DFunLike.congr_fun hρ' g⟩

theorem ker_mulEquiv_comp {E S T : Type*} [Group E] [Group S] [Group T] (π : E →* S)
    (e : S ≃* T) : (e.toMonoidHom.comp π).ker = π.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have hdvd : p ∣ 2 ^ f := by
    rw [← hK, Nat.card_eq_fintype_card]
    obtain ⟨n, hn, hcard⟩ := FiniteField.card K p
    rw [hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hdvd)] at hp
  exact hp

theorem g2_even_perfect_odd_cover_trivial
    {S : Type} [Group S] {f : ℕ}
    (hS : ChevalleyExceptionalModel S .G2 2 f) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have : CharP K 2 := charP_two_of_card hK
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let eC : AdjointQuotient .G2 K ≃* adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let ψ : E →* adjointGroup .G2 K := (e.trans eC).toMonoidHom.comp π
  have hψker : ψ.ker = π.ker := ker_mulEquiv_comp π (e.trans eC)
  have hψ : Function.Surjective ψ := (e.trans eC).surjective.comp hπ
  obtain ⟨σ, hσ, -, -⟩ := g2_even_central_odd_extension_splitting hψ (hψker ▸ hC)
    (hψker ▸ hodd)
  rw [← hψker]
  exact ker_eq_bot_of_section_of_perfect ψ (hψker ▸ hC) σ hσ

theorem catalog_g2_even
    {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L)
    (hSQT : IsStronglyQuasithin L) (hodd : Odd (Nat.card (Subgroup.center L))) {f : ℕ}
    (h : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 2 f) :
    Subgroup.center L = ⊥ ∧ CatalogStepConclusion L := by
  have : Group.IsPerfect L := hL.1
  exact catalogStepConclusion_of_perfect_odd_cover_trivial hSQT hodd (MulEquiv.refl _)
    fun π hπ hC hπodd => g2_even_perfect_odd_cover_trivial h π hπ hC hπodd

end CFSG.SectionRank
