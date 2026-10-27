module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc

namespace ExitE4

@[expose] def E4DStarW (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
    (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
      ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
    T3.DStarConnected (CoreAssembly.conjClass K)

@[expose] def E4ModelDStar : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (CFSG.Blueprint.LieModel M .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) →
      E4DStarW M

section Transfer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem dStarConnected_of_quot (c : CentQuotGen Ω N)
    (h : T3.DStarConnected (quotFamily Ω N)) : T3.DStarConnected Ω := by
  intro K hK J hJ
  have key : ∀ Jb, Relation.ReflTransGen (dstarAdj (quotFamily Ω N))
      (K.map (QuotientGroup.mk' N)) Jb → Jb ∈ quotFamily Ω N ∧
        ∀ J ∈ Ω, J.map (QuotientGroup.mk' N) = Jb → Relation.ReflTransGen (dstarAdj Ω) K J := by
    intro Jb hJb
    induction hJb with
    | refl =>
      exact ⟨map_mem_quotFamily hK, fun J hJ e => by rw [c.eq_of_map J hJ K hK e]⟩
    | tail _ hstep ih =>
      obtain ⟨hmem, ih⟩ := ih
      obtain ⟨B, hB, rfl⟩ := hmem
      refine ⟨hstep.1, fun J hJ e => (ih B hB rfl).tail ⟨hJ, ?_⟩⟩
      have h2 := hstep.2
      rw [← e] at h2
      rcases h2 with h1 | h1
      · exact Or.inl (c.omegaStarNbr_of_map hB hJ h1)
      · exact Or.inr (c.omegaStarNbr_of_map hJ hB h1)
  exact (key _ (h _ (map_mem_quotFamily hK) _ (map_mem_quotFamily hJ))).2 J hJ rfl

end Transfer

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstarConnected_of_twinE4 (hmodel : E4ModelDStar) (hΩ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hq8 : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2))
    (hgen : omegaGen Φ = ⊤) (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    {K : Subgroup X} (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z) (hno : ¬ TightInO2 z)
    {W : Subgroup X} (hKW : K ≤ W) (hW : IsSubnormal W ⊤) (hE : TwinE4 ↥W) :
    T3.DStarConnected Φ := by
  have hWtop : W = ⊤ := eq_top_of_subnormal hgen htrans hK hW rfl hKW
  subst hWtop
  obtain ⟨Q, hQ, f, hfs, hker, hM⟩ := twinE4_of_top hE
  have hN2 : IsPGroup 2 ↥f.ker := hker
  have hzN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ f.ker := by
    intro J hJ u hu huN
    obtain ⟨g, rfl⟩ := htrans K hK J hJ
    have hu' : g * z * g⁻¹ = u := (hz.conj g).eq hu
    apply hno
    refine ⟨f.ker, inferInstance, hN2, ?_⟩
    have h3 := (inferInstance : f.ker.Normal).conj_mem u huN g⁻¹
    rw [← hu'] at h3
    simpa [mul_assoc] using h3
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => inf_eq_bot h2 hΩ hzN hJ
  have hNc : f.ker ≤ Subgroup.center X := center_of_meet hΩ h2 hgen hN2 hmeet
  have hc : CentQuotGen Φ f.ker := centQuotGen hΩ h2 hNc hmeet
  have hΦ : Φ = CoreAssembly.conjClass K := by
    ext J
    constructor
    · intro hJ
      exact htrans K hK J hJ
    · rintro ⟨g, rfl⟩
      exact hΩ.conjInvariant g K hK
  let e : (X ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : CFSG.Blueprint.LieModel (X ⧸ f.ker) .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel (X ⧸ f.ker) .POmegaPlus 4 2 1 :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  have hnab := exists_noncomm hΩ h2 hK
  have hinvK : IsUniqueInvolution (K.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz
  have hq8K : Nonempty (↥(K.map (QuotientGroup.mk' f.ker)) ≃* QuaternionGroup 2) := by
    obtain ⟨eK⟩ := hq8 K hK
    exact ⟨(AscQuot.quotRestrictEquiv (hmeet K hK)).symm.trans eK⟩
  have htw : ∀ c ∈ Subgroup.centralizer ({QuotientGroup.mk' f.ker z} : Set (X ⧸ f.ker)),
      conjSub c (K.map (QuotientGroup.mk' f.ker)) = K.map (QuotientGroup.mk' f.ker) ∨
        ∀ x ∈ K.map (QuotientGroup.mk' f.ker), ∀ y ∈ conjSub c (K.map (QuotientGroup.mk' f.ker)),
          x * y = y * x := by
    intro cb hcb
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective f.ker cb
    have hc' : QuotientGroup.mk' f.ker c * QuotientGroup.mk' f.ker z =
        QuotientGroup.mk' f.ker z * QuotientGroup.mk' f.ker c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcb
    have hq : z⁻¹ * (c * z * c⁻¹) ∈ f.ker := by
      have h0 : QuotientGroup.mk' f.ker (z⁻¹ * (c * z * c⁻¹)) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc', mul_inv_cancel_right, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have hcen : ∀ y : X, y * (z⁻¹ * (c * z * c⁻¹)) = (z⁻¹ * (c * z * c⁻¹)) * y :=
      Subgroup.mem_center_iff.mp (hNc hq)
    rcases twin_clause_central hΩ h2 hK hz hnab rfl hcen with h | h
    · left
      rw [← AscQuot.map_conjSub, h]
    · right
      rintro _ ⟨x, hx, rfl⟩ y hy
      rw [← AscQuot.map_conjSub] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, h x hx y' hy']
  have hD := hmodel (X ⧸ f.ker) hMq _ _ hq8K hinvK htw
  have hqf : quotFamily Φ f.ker = CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)) := by
    rw [hΦ]
    exact image_conjClass K
  exact dStarConnected_of_quot hc (hqf ▸ hD)

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
