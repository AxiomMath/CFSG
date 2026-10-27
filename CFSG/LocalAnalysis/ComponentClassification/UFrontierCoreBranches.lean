module

public import CFSG.LocalAnalysis.ComponentClassification.UFrontierBranches
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergCASimpleStrongEmbedding

public section

namespace CFSG.ComponentClassification.UFrontier

open CFSG.Assembly CFSG.Blueprint Subgroup

@[expose] def LowTwoRankCatalogInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Even (Nat.card G) → Open.twoRank G ≤ 2 → Catalog G

@[expose] def AschbacherCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G), 3 ≤ Open.pRank 2 (S : Subgroup G) →
      Open.properTwoGenCoreGamma (S : Subgroup G) 2 ≠ ⊤ →
      Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤ ∨ Nonempty (G ≃* Open.properTwoGenCoreJ1)

@[expose] def GH74ModelsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G →
    (∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel G .G2 0 p f ∨ Blueprint.LieModel G .trialityD4 0 p f)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel G .PSp 2 p f) ∨
    (∃ f : ℕ, Blueprint.LieModel G .twistedG2 0 3 f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧
      Blueprint.LieModel G .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧
      Blueprint.LieModel G .PSU 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ Blueprint.LieModel G .PSL 5 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ Blueprint.LieModel G .PSU 5 p f) ∨
    (Blueprint.LieModel G .PSL 2 2 3 ∨ Blueprint.LieModel G .PSL 2 2 4 ∨
      Blueprint.LieModel G .PSL 3 2 2 ∨ Blueprint.LieModel G .twistedB2 0 2 3) ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (Blueprint.NativeSporadic.IsSporadic G .M12 ∨ Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      Blueprint.NativeSporadic.IsSporadic G .M23 ∨ Blueprint.NativeSporadic.IsSporadic G .J1 ∨
      Blueprint.NativeSporadic.IsSporadic G .J2 ∨ Blueprint.NativeSporadic.IsSporadic G .J3 ∨
      Blueprint.NativeSporadic.IsSporadic G .McL ∨ Blueprint.NativeSporadic.IsSporadic G .Ly)

theorem uOutcome_of_catalog (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hcat : Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) :
    OutcomeLocal.UOutcome X := by
  have htop : GeneralizedFitting.subgroup X = ⊤ := by
    rcases (GeneralizedFitting.normal X).eq_bot_or_eq_top with h | h
    · obtain ⟨x, hx⟩ := exists_ne (1 : X)
      have h1 := GeneralizedFitting.centralizer_le X
      rw [h] at h1
      have hxc : x ∈ centralizer ((⊥ : Subgroup X) : Set X) := by
        rw [mem_centralizer_iff]
        intro m hm
        rw [coe_bot, Set.mem_singleton_iff] at hm
        rw [hm, one_mul, mul_one]
      exact absurd (mem_bot.mp (h1 hxc)) hx
    · exact h
  let e : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X) := e.isSimpleGroup
  have hnonabF : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact hCU X hsimple hnonabF (SectionRank.catalog_of_mulEquiv e hcat) hz

theorem catalog_of_gh74 (hGH : GH74ModelsInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ Open.twoRank G)
    (hsect : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) : Catalog G := by
  rcases hGH G hnonab hrank hsect with ⟨p, f, -, -, -, h | h⟩ | ⟨p, f, -, -, -, h⟩ | ⟨f, h⟩ |
      ⟨p, f, -, -, -, -, h⟩ | ⟨p, f, -, -, -, -, h⟩ | ⟨p, f, -, -, -, h⟩ | ⟨p, f, -, -, -, h⟩ |
      (h | h | h | h) | ⟨n, hn, -, he⟩ | (h | h | h | h | h | h | h | h)
  all_goals first
    | exact lieModel_catalog G _ _ _ _ h
    | exact .inr (.inl ⟨n, by omega, he⟩)
    | exact .inr (.inr (.inr (.inr ⟨_, h⟩)))

theorem one_le_pRank_two_of_mem' {G : Type} [Group G] [Finite G] {X : Subgroup G} {x : G}
    (hx : x ∈ X) (hord : orderOf x = 2) : 1 ≤ Open.pRank 2 X := by
  have hx2 : x ^ 2 = 1 := (orderOf_eq_prime_iff.mp hord).1
  have helem : Open.IsElemAbelian 2 (zpowers x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b.2
      rw [coe_mul, coe_mul, ← hi, ← hj]
      exact (Commute.zpow_zpow_self x i j).eq
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  exact le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove 2 one_lt_two X)
    ⟨zpowers x, zpowers_le.mpr hx, helem, by rw [Nat.card_zpowers, hord]; rfl⟩

theorem stronglyEmbeddedOrder_of_gammaOne_ne_top {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (hrank : 2 ≤ Open.twoRank G)
    (hne : Open.properTwoGenCoreGamma (S : Subgroup G) 1 ≠ ⊤) :
    BenderSuzuki.IsStronglyEmbeddedOrder (Open.properTwoGenCoreGamma (S : Subgroup G) 1) := by
  set Γ := Open.properTwoGenCoreGamma (S : Subgroup G) 1 with hΓ
  have hN : ∀ Q : Subgroup G, Q ≤ (S : Subgroup G) → 1 ≤ Open.pRank 2 Q →
      normalizer (Q : Set G) ≤ Γ := fun Q hQ hr =>
    le_iSup_of_le Q (le_iSup_of_le hQ (le_iSup_of_le hr le_rfl))
  have hSrank : 1 ≤ Open.pRank 2 (S : Subgroup G) := by
    rw [(SectionRank.pRank_sylow S).1]
    exact le_trans (by norm_num) hrank
  have hSH : (S : Subgroup G) ≤ Γ := le_trans (le_normalizer) (hN _ le_rfl hSrank)
  have hcore : Open.properTwoGenCoreGamma (S : Subgroup G) 2 ≤ Γ :=
    iSup_mono fun Q => iSup_mono fun _ => iSup_le fun h2 =>
      le_iSup_of_le (show 1 ≤ Open.pRank 2 Q by omega) le_rfl
  have hcent : ∀ t ∈ Γ, orderOf t = 2 → centralizer ({t} : Set G) ≤ Γ := by
    intro t htΓ ht
    obtain ⟨u, huΓ, huS⟩ :=
      ProperTwoGeneratedCore.involution_conjugate_into_sylow S Γ hSH t htΓ ht
    have hs : orderOf (u⁻¹ * t * u) = 2 := by
      have := (MulAut.conj u⁻¹).orderOf_eq t
      simpa [MulAut.conj_apply] using this.trans ht
    have hzS : zpowers (u⁻¹ * t * u) ≤ (S : Subgroup G) := zpowers_le.mpr huS
    have hNs := hN _ hzS (one_le_pRank_two_of_mem' (mem_zpowers _) hs)
    intro g hg
    have hcomm : u⁻¹ * g * u ∈ centralizer ((zpowers (u⁻¹ * t * u) : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      have hgt : t * g = g * t := (mem_centralizer_singleton_iff.mp hg).symm
      have hc : Commute (u⁻¹ * t * u) (u⁻¹ * g * u) := by
        show (u⁻¹ * t * u) * (u⁻¹ * g * u) = (u⁻¹ * g * u) * (u⁻¹ * t * u)
        calc (u⁻¹ * t * u) * (u⁻¹ * g * u) = u⁻¹ * (t * g) * u := by group
          _ = u⁻¹ * (g * t) * u := by rw [hgt]
          _ = (u⁻¹ * g * u) * (u⁻¹ * t * u) := by group
      exact (hc.zpow_left k).eq
    have hmem : u⁻¹ * g * u ∈ Γ := hNs (centralizer_le_normalizer _ hcomm)
    have : g = u * (u⁻¹ * g * u) * u⁻¹ := by group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem huΓ hmem) (Γ.inv_mem huΓ)
  exact ProperTwoGeneratedCore.strongly_embedded_order_of_full_core_centralizer_closure S Γ hne
    hSH hrank hcore hcent

theorem even_card_of_involution {X : Type} [Group X] [Finite X] {z : X} (hz : orderOf z = 2) :
    Even (Nat.card X) :=
  even_iff_two_dvd.mpr (hz ▸ orderOf_dvd_natCard z)

theorem catalog_of_gammaOne_or_J1 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (S : Sylow 2 X) (hrank : 2 ≤ Open.twoRank X)
    (h : Open.properTwoGenCoreGamma (S : Subgroup X) 1 ≠ ⊤ ∨
      Nonempty (X ≃* Open.properTwoGenCoreJ1)) : Catalog X := by
  rcases h with hne | hJ1
  · exact SteinbergCA.simple_strong_embedding_catalog X hnonab
      ⟨_, stronglyEmbeddedOrder_of_gammaOne_ne_top S hrank hne⟩
  · obtain ⟨e⟩ := hJ1
    exact .inr (.inr (.inr (.inr ⟨.J1, ⟨e.trans ProperTwoGeneratedCore.j1_exact_model_equiv⟩⟩)))

theorem properCoreBranch_of_inputs (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hlow : LowTwoRankCatalogInput) (hasc : AschbacherCoreInput) : ProperCoreBranch := by
  intro X _ _ _ hnonab _ hz S hcore
  obtain ⟨z, hz2, -⟩ := id hz
  refine uOutcome_of_catalog hCU hnonab ?_ hz
  by_cases hr : Open.twoRank X ≤ 2
  · exact hlow X hnonab (even_card_of_involution hz2) hr
  have hS3 : 3 ≤ Open.pRank 2 (S : Subgroup X) := by
    rw [(SectionRank.pRank_sylow S).1]
    change 3 ≤ Open.twoRank X
    omega
  have hcore' : Open.properTwoGenCoreGamma (S : Subgroup X) 2 ≠ ⊤ := by
    have h := hcore.ne
    simp only [UnbalancedCorr.pRank_two_eq_open] at h
    exact h
  exact catalog_of_gammaOne_or_J1 hnonab S (by omega) (hasc X hnonab S hS3 hcore')

theorem uOutcome_of_gen4_of_inputs
    (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hlow : LowTwoRankCatalogInput) (hGH : GH74ModelsInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hgen : CFSG.GH74.Gen4 G)
    (hunb : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) :
    OutcomeLocal.UOutcome G := by
  refine uOutcome_of_catalog hCU hnonab ?_ hunb
  by_cases hr : Open.twoRank G ≤ 2
  · obtain ⟨z, hz2, _⟩ := hunb
    exact hlow G hnonab (even_card_of_involution hz2) hr
  · exact catalog_of_gh74 hGH hnonab (by omega) hgen

theorem sectionalFourBranch_of_inputs (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hlow : LowTwoRankCatalogInput) (hGH : GH74ModelsInput) : SectionalFourBranch := by
  intro X _ _ _ hnonab _ hz h4 _
  exact uOutcome_of_gen4_of_inputs hCU hlow hGH hnonab h4 hz

theorem relativeU_of_tripleBranch (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hlow : LowTwoRankCatalogInput) (hasc : AschbacherCoreInput) (hGH : GH74ModelsInput)
    (htriple : TripleBranch) : KProperRelativeB.RelativeU Catalog :=
  relativeU_of_branches hCU htriple (properCoreBranch_of_inputs hCU hlow hasc)
    (sectionalFourBranch_of_inputs hCU hlow hGH)

end CFSG.ComponentClassification.UFrontier
