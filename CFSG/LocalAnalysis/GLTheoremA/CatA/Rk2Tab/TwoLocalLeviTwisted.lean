module

public import CFSG.LieType.Chevalley.GraphFixedBorelOvergroups
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.BorelTits.Twisted
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLocal
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType
open scoped Pointwise


theorem twoLocal_card_le_of_graphFixedLevi {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : TwistTag} {σ : K →+* K} (hσ : Function.Surjective σ)
    (hHolds : CFSG.LieType.BorelTits.Holds ↥(graphFixedRootGroup t K σ) 2)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLev : ∀ (J : Set (Fin t.foldedTag.rank)), J ≠ Set.univ →
      ∀ E : Subgroup (ModGL t.tag K), E ≤ graphFixedParabolicLevi t K σ J →
        IsElemAbelian p E → Nat.card E ≤ p ^ k)
    {R E : Subgroup ↥(graphFixedRootGroup t K σ)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set ↥(graphFixedRootGroup t K σ)))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σe : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσ⟩ with hσedef
  have hσe : σe.toRingHom = σ := rfl
  obtain ⟨S, P, hPtop, hNR, -, -, hNS⟩ := hHolds R hR hR2
  set U : Subgroup (ModGL t.tag K) := graphFixedPosUnipotent t K σ with hUdef
  have hUp : IsPGroup 2 (U.subgroupOf (graphFixedRootGroup t K σ)) :=
    isPGroup_graphFixedPosUnipotent_subgroupOf 2
  have hUi : ¬ 2 ∣ (U.subgroupOf (graphFixedRootGroup t K σ)).index :=
    not_dvd_index_graphFixedPosUnipotent 2 hσ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(graphFixedRootGroup t K σ)
    (hUp.toSylow hUi) S
  have hSeq : (S : Subgroup ↥(graphFixedRootGroup t K σ)) =
      (U.subgroupOf (graphFixedRootGroup t K σ)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hB₀N : (graphFixedRootBorel t K σ).subgroupOf (graphFixedRootGroup t K σ) ≤
      Subgroup.normalizer (((U.subgroupOf (graphFixedRootGroup t K σ) :
        Subgroup ↥(graphFixedRootGroup t K σ)) : Set ↥(graphFixedRootGroup t K σ))) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h := Subgroup.mem_normalizer_iff.1
      (graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hb))
      (u : ModGL t.tag K)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h
  set P' : Subgroup ↥(graphFixedRootGroup t K σ) := P.map (MulAut.conj g⁻¹).toMonoidHom
    with hP'def
  have hB₀P' : (graphFixedRootBorel t K σ).subgroupOf (graphFixedRootGroup t K σ) ≤ P' := by
    intro b hb
    have h1 : (MulAut.conj g).toMonoidHom b ∈ P := by
      apply hNS
      rw [hSeq]
      exact Subgroup.le_normalizer_map _ ⟨b, hB₀N hb, rfl⟩
    refine ⟨_, h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set A : Subgroup (ModGL t.tag K) :=
    P'.map (graphFixedRootGroup t K σ).subtype with hAdef
  have hBA : graphFixedRootBorel t K σ ≤ A := fun b hb =>
    ⟨⟨b, graphFixedRootBorel_le t K σ hb⟩,
      hB₀P' (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hAC : A ≤ graphFixedRootGroup t K σ :=
    Subgroup.map_le_iff_le_comap.2 fun x _ => x.2
  obtain ⟨-, J, hAJ, -⟩ :=
    (fixed_Borel_overgroup_classification t K σe) A (by rwa [hσe]) (by rwa [hσe])
  have hJne : J ≠ Set.univ := by
    intro hJ
    apply hPtop
    have hAtop : A = graphFixedRootGroup t K σ := by
      rw [hAJ, hJ, hσe]
      exact (fixed_standard_parabolic_cells t K σe).2.2.2.2.2
    have hP'top : P' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : ModGL t.tag K) ∈ A := by rw [hAtop]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Subtype.ext hyx] at hy
      exact hy
    rw [eq_top_iff]
    intro x _
    have hx : (MulAut.conj g⁻¹).toMonoidHom x ∈ P' := by
      rw [hP'top]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g⁻¹).injective hyx
    rw [← this]
    exact hy
  set F : Subgroup (ModGL t.tag K) :=
    (E.map (MulAut.conj g⁻¹).toMonoidHom).map
      (graphFixedRootGroup t K σ).subtype with hFdef
  have hFA : F ≤ A := Subgroup.map_mono (Subgroup.map_mono (hER.trans hNR))
  have hFcard : Nat.card F = Nat.card E := by
    rw [Subgroup.card_map_of_injective (graphFixedRootGroup t K σ).subtype_injective,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hFel : IsElemAbelian p F := (hE.map _).map _
  obtain ⟨-, -, -, -, -, -, -, -, hQP, -, hMP, huniq, -, -, -, -, hQ2, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σe J
  rw [hσe] at hQP hMP huniq hQ2
  have hQ2' : IsPGroup 2 (graphFixedParabolicRadical t K σ J) := hQ2 2
  have hcard := CFSG.StandardType.F4Rest.card_eq_mul_of_existsUnique hQP hMP huniq
  have hQp : ¬ p ∣ Nat.card (graphFixedParabolicRadical t K σ J) := by
    obtain ⟨n, hn⟩ := hQ2'.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨x, -, hxM⟩ := CFSG.StandardType.F4Rest.exists_conj_le_of_card_eq_mul hMP hcard hQp
    (hAJ ▸ hFA) hFel.isPGroup
  set F' : Subgroup (ModGL t.tag K) := F.map (MulAut.conj x).toMonoidHom with hF'def
  have hF'el : IsElemAbelian p F' := hFel.map _
  calc Nat.card E = Nat.card F' := by
        rw [hF'def, Subgroup.card_map_of_injective (MulAut.conj x).injective, hFcard]
    _ ≤ p ^ k := hLev J hJne F' hxM hF'el

theorem twoLocalRank_le_of_graphFixedLevi {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : TwistTag} {σ : K →+* K} (hσ : Function.Surjective σ)
    (hHolds : CFSG.LieType.BorelTits.Holds ↥(graphFixedRootGroup t K σ) 2)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLev : ∀ (J : Set (Fin t.foldedTag.rank)), J ≠ Set.univ →
      ∀ E : Subgroup (ModGL t.tag K), E ≤ graphFixedParabolicLevi t K σ J →
        IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    CFSG.Open.twoLocalPrimeRank p ↥(graphFixedRootGroup t K σ) ≤ k := by
  show sSup {k' | ∃ H : Subgroup ↥(graphFixedRootGroup t K σ),
    CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k'} ≤ k
  refine csSup_le' ?_
  rintro k' ⟨H, hH, rfl⟩
  obtain ⟨R, hR, hR2, rfl⟩ := hH
  exact CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEel =>
    twoLocal_card_le_of_graphFixedLevi hσ hHolds hp hp2 hLev hR hR2 hE hEel

end CFSG.LocalAnalysis.GLTheoremA
