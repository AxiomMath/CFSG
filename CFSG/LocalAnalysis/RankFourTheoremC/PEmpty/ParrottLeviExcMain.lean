module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcSection
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LieType.Chevalley.ParabolicSylowSubsystem
public import CFSG.LieType.Chevalley.SubsystemComponent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup

section Transport

variable {A : Type*} [Group A]

theorem relPPrimeCore_map_subtype [Finite A] (G : Subgroup A) (K₀ : Subgroup ↥G) {p : ℕ}
    (hp : p.Prime) :
    relPPrimeCore p (K₀.map G.subtype) = (relPPrimeCore p K₀).map G.subtype := by
  open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple in
  refine le_antisymm ?_ (relPPrimeCore_map_le_of_injective G.subtype G.subtype_injective K₀ p)
  set N := relPPrimeCore p (K₀.map G.subtype) with hN
  have hNK : N ≤ K₀.map G.subtype := sSup_le fun _ hM => hM.1
  have hNG : N ≤ G := hNK.trans (Subgroup.map_subtype_le K₀)
  have hNeq : (N.comap G.subtype).map G.subtype = N := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hNG]
  have hcK : N.comap G.subtype ≤ K₀ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hNK hx
    rwa [← Subtype.ext hyx]
  rw [← hNeq]
  refine Subgroup.map_mono (le_sSup ⟨hcK, ?_, ?_⟩)
  · rw [Subgroup.normal_subgroupOf_iff hcK]
    intro n k hn hk
    have hnorm := relPPrimeCore_normal hp (K₀.map G.subtype)
    rw [Subgroup.normal_subgroupOf_iff hNK] at hnorm
    have h := hnorm (G.subtype n) (G.subtype k) hn ⟨k, hk, rfl⟩
    rw [Subgroup.mem_comap]
    simpa using h
  · have hc := coprime_card_relPPrimeCore hp (K₀.map G.subtype)
    rwa [← hN, ← hNeq, Subgroup.card_map_of_injective G.subtype_injective] at hc

theorem isSylowOf_comap_subtype [Finite A] {G : Subgroup A} {K₀ : Subgroup ↥G} {p : ℕ}
    [Fact p.Prime] {U : Subgroup A}
    (hU : CFSG.ABGLocalTools.IsSylowOf p U (K₀.map G.subtype)) :
    CFSG.ABGLocalTools.IsSylowOf p (U.comap G.subtype) K₀ ∧
      (U.comap G.subtype).map G.subtype = U := by
  obtain ⟨hUK, hUp, hUi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hU
  have hUG : U ≤ G := hUK.trans (Subgroup.map_subtype_le K₀)
  have hUeq : (U.comap G.subtype).map G.subtype = U := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_eq_right.2 hUG]
  refine ⟨CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨?_, ?_, ?_⟩, hUeq⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hUK hx
    rwa [← Subtype.ext hyx]
  · exact hUp.comap_of_injective G.subtype G.subtype_injective
  · rwa [← Subgroup.relIndex_map_map_of_injective _ _ G.subtype_injective, hUeq]

end Transport

section Assembly

variable {τ : Tag} {K : Type} [Field K]


theorem borel_subgroupOf_le_normalizer :
    (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤
      normalizer (((posUnipotent τ K).subgroupOf (adjointGroup τ K) :
        Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq posUnipotent_le_adjointGroup]
  exact fun x hx => (sup_le torusGroup_le_normalizer_posUnipotent Subgroup.le_normalizer) hx

theorem leviAt_of_normalizer_le [Finite K] [CharP K 2] {i₀ j₀ : Fin τ.rank} (hij₀ : i₀ ≠ j₀)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfSL : f ∣ Nat.card (SL2 K))
    (hfr : 2 ≤ CFSG.Open.pRank f (⊤ : Subgroup ↥(adjointGroup τ K)))
    (hQ : ∀ C : Set (Fin τ.rank), C ≠ Set.univ → C.Nonempty →
      ConnSubsys.IsDynkinConnected τ C → ∀ p : ℕ, p.Prime → 5 ≤ p →
      p ∣ Nat.card (subsystemGroup τ K C) →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup τ K)) ≤ 1 →
      CFSG.IsQuasisimple (subsystemGroup τ K C))
    {K₀ : Subgroup ↥(adjointGroup τ K)}
    (hN : normalizer (((posUnipotent τ K).subgroupOf (adjointGroup τ K) :
      Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) ≤ K₀) (p : ℕ) :
    LeviAt K₀ p := by
  intro _ hp h5 hrank _ hne hsyl
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have hBK₀ : (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤ K₀ :=
    borel_subgroupOf_le_normalizer.trans hN
  have hBP : borelGroup τ K ≤ K₀.map (adjointGroup τ K).subtype := fun x hx =>
    ⟨⟨x, borelGroup_le_adjointGroup' hx⟩, hBK₀ hx, rfl⟩
  have hPG : K₀.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ K₀.map (adjointGroup τ K).subtype}
  have hPJ : K₀.map (adjointGroup τ K).subtype = parabolicSubgroup τ K J :=
    (borel_overgroup_classification (τ := τ) (K := K)).1 _ hBP hPG
  have hJ : J ≠ Set.univ := by
    intro hJu
    apply hne
    have h1 : K₀.map (adjointGroup τ K).subtype = adjointGroup τ K := by
      rw [hPJ, hJu]
      exact (standard_parabolic_cells τ K).2.2.2.2.2.1
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL τ K) ∈ K₀.map (adjointGroup τ K).subtype := by
      rw [h1]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  have hsyl' : ∀ U : Subgroup (ModGL τ K),
      CFSG.ABGLocalTools.IsSylowOf 2 U (parabolicSubgroup τ K J) →
        ¬ U ≤ rankThreePrimeCore p (parabolicSubgroup τ K J) := by
    intro U hU hUO
    rw [← hPJ] at hU hUO
    obtain ⟨hU', -⟩ := isSylowOf_comap_subtype hU
    refine hsyl _ hU' fun x hx => ?_
    have h2 := hUO hx
    rw [rankThreePrimeCore, relPPrimeCore_map_subtype _ _ hp] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    rwa [← Subtype.ext hyx]
  have hpJ := ParSylow.dvd_card_subsystemGroup_of_sylowHyp J hp (by omega) hsyl'
  obtain ⟨C, hCJ, hCne, hCconn, hpC⟩ :=
    SubsysComp.exists_connected_dvd_card_subsystemGroup (K := K) hp hpJ
  have hCu : C ≠ Set.univ := fun h => hJ (Set.eq_univ_of_univ_subset (h ▸ hCJ))
  have hQC := hQ C hCu hCne hCconn p hp h5 hpC hrank
  have hpK : ¬ p ∣ Nat.card Kˣ := by
    intro hd
    have hprod := CFSG.LieType.RootSystem.cartan_pair_cases (isFiniteType_cartan τ) hij₀
    have hdet : ¬ (p : ℤ) ∣ 4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ := by
      intro hdvd
      have hpos : 0 < 4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ := by
        rcases hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [h1, h2] <;> norm_num
      have hle := Int.le_of_dvd hpos hdvd
      have hlt : 4 - τ.cartan i₀ j₀ * τ.cartan j₀ i₀ ≤ 4 := by
        rcases hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [h1, h2] <;> norm_num
      omega
    have := EvenTorusRank.two_le_pRank_of_dvd_card_units hp (by omega) hd hij₀ hdet
    omega
  have hQG : subsystemGroup τ K C ≤ adjointGroup τ K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, -, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup i c
    · exact yUnit_mem_adjointGroup i c
  set Y : Subgroup ↥(adjointGroup τ K) := (subsystemGroup τ K C).subgroupOf (adjointGroup τ K)
  set W : Subgroup ↥(adjointGroup τ K) := (Subgroup.center ↥Y).map Y.subtype
  let eY : ↥Y ≃* ↥(subsystemGroup τ K C) := Subgroup.subgroupOfEquivOfLe hQG
  have hYq : CFSG.IsQuasisimple ↥Y := CFSG.IsQuasisimple.of_mulEquiv eY hQC
  have hcardZ : Nat.card (Subgroup.center ↥Y) =
      Nat.card (Subgroup.center ↥(subsystemGroup τ K C)) :=
    Nat.card_congr (Subgroup.centerCongr eY).toEquiv
  have hcardY : Nat.card ↥Y = Nat.card ↥(subsystemGroup τ K C) := Nat.card_congr eY.toEquiv
  have hcardQuot : Nat.card (↥Y ⧸ Subgroup.center ↥Y) =
      Nat.card (↥(subsystemGroup τ K C) ⧸ Subgroup.center ↥(subsystemGroup τ K C)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Y)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(subsystemGroup τ K C))
    have hZpos : 0 < Nat.card (Subgroup.center ↥(subsystemGroup τ K C)) := Nat.card_pos
    rw [hcardY, hcardZ] at h1
    exact Nat.eq_of_mul_eq_mul_right hZpos (h1.symm.trans h2)
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥(subsystemGroup τ K C)) :=
    not_dvd_card_center_subsystemGroup hp hpK
  have hWcard : Nat.card W = Nat.card (Subgroup.center ↥Y) :=
    Subgroup.card_map_of_injective Y.subtype_injective
  refine ⟨f, Y, W, hf, hf2, ?_, hfr, ?_, s622IsSimpleSection_center_of_isQuasisimple hYq, ?_, ?_,
    ?_⟩
  ·
    rintro rfl
    omega
  ·
    intro y hy
    have hyQ : (y : ModGL τ K) ∈ subsystemGroup τ K C := hy
    have hCJL : subsystemGroup τ K C ≤ subsystemGroup τ K J := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, hi, c, rfl | rfl⟩
      · exact Subgroup.subset_closure ⟨i, hCJ hi, c, Or.inl rfl⟩
      · exact Subgroup.subset_closure ⟨i, hCJ hi, c, Or.inr rfl⟩
    have hyL : (y : ModGL τ K) ∈ subsystemGroup τ K J := hCJL hyQ
    have hyM : (y : ModGL τ K) ∈ parabolicLevi τ K J := by
      refine ((Subgroup.closure_le _).2 ?_) hyL
      rintro _ ⟨j, hj, c, rfl | rfl⟩
      · exact xUnit_mem_parabolicLevi hj c
      · exact yUnit_mem_parabolicLevi hj c
    have hyP : (y : ModGL τ K) ∈ K₀.map (adjointGroup τ K).subtype := by
      rw [hPJ]
      exact parabolicLevi_le_parabolicSubgroup J hyM
    obtain ⟨z, hz, hzy⟩ := hyP
    rwa [← Subtype.ext hzy]
  ·
    rw [relIndex_center_map, hcardQuot]
    obtain ⟨i, hi⟩ := hCne
    exact hfSL.trans (card_sl2_dvd_card_quotient_center hi)
  ·
    rw [relIndex_center_map, hcardQuot]
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(subsystemGroup τ K C))
    rw [h2] at hpC
    exact ((Nat.Prime.dvd_mul hp).1 hpC).resolve_right hpZ
  ·
    rw [hWcard, hcardZ]
    exact hpZ

end Assembly

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
