module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6FixedContainment
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.LieType.Chevalley.TwistedE6EvenCover

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.QuasithinUnique.Setup.X6
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem lc_aut_mem {G : Type} [Group G] {C U Q P : Subgroup G}
    (hQU : Q ≤ U) (hUC : U ≤ C) (hPN : P ≤ Subgroup.normalizer (Q : Set G))
    (hNC : ∀ x ∈ C, x ∈ Subgroup.normalizer (Q : Set G) → x ∈ P)
    (β : MulAut ↥C) (hβ : ∀ u : ↥C, (u : G) ∈ U → β u = u)
    (g : ↥C) (hg : (g : G) ∈ P) : ((β g : ↥C) : G) ∈ P := by
  have hQC : Q ≤ C := hQU.trans hUC
  have hconj : ∀ x : ↥C, (x : G) ∈ U →
      ((β (g * x * g⁻¹) : ↥C) : G) = ((β g : ↥C) : G) * (x : G) * ((β g : ↥C) : G)⁻¹ := by
    intro x hx
    rw [map_mul, map_mul, map_inv, hβ x hx]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hgn := Subgroup.mem_normalizer_iff.1 (hPN hg)
  have hN : ∀ h : G, h ∈ Q ↔ ((β g : ↥C) : G) * h * ((β g : ↥C) : G)⁻¹ ∈ Q := by
    intro h
    constructor
    · intro hh
      let x : ↥C := ⟨h, hQC hh⟩
      have hgx : ((g * x * g⁻¹ : ↥C) : G) ∈ Q := (hgn h).1 hh
      have h1 := hconj x (hQU hh)
      rw [hβ _ (hQU hgx)] at h1
      show ((β g : ↥C) : G) * (x : G) * ((β g : ↥C) : G)⁻¹ ∈ Q
      rw [← h1]
      exact hgx
    · intro hk
      have hhC : h ∈ C := by
        have e : h = ((β g : ↥C) : G)⁻¹ * (((β g : ↥C) : G) * h * ((β g : ↥C) : G)⁻¹) *
            ((β g : ↥C) : G) := by group
        rw [e]
        exact C.mul_mem (C.mul_mem (C.inv_mem (β g).2) (hQC hk)) (β g).2
      let x : ↥C := ⟨h, hhC⟩
      let k : ↥C := β g * x * (β g)⁻¹
      have hkQ : (k : G) ∈ Q := hk
      have hkβ : β k = k := hβ k (hQU hkQ)
      let W : ↥C := g⁻¹ * k * g
      have hWk : (g : G) * (W : G) * (g : G)⁻¹ = (k : G) := by
        simp only [W, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hWQ : (W : G) ∈ Q := (hgn (W : G)).2 (by rw [hWk]; exact hkQ)
      have hβW : β W = W := hβ W (hQU hWQ)
      have hcalc : β W = (β g)⁻¹ * k * β g := by
        simp only [W, map_mul, map_inv, hkβ]
      have e2 : (β g)⁻¹ * k * β g = W := hcalc.symm.trans hβW
      have e3 : ((β g : ↥C) : G)⁻¹ * (k : G) * ((β g : ↥C) : G) = h := by
        simp only [k, x, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have e4 : h = (W : G) := by
        rw [← e3]
        have e5 := congrArg (fun z : ↥C => (z : G)) e2
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using e5
      rw [e4]
      exact hWQ
  exact hNC _ (β g).2 (Subgroup.mem_normalizer_iff.2 hN)

theorem lc_map_eq {G : Type} [Group G] {C U Q P : Subgroup G}
    (hQU : Q ≤ U) (hUC : U ≤ C) (hPN : P ≤ Subgroup.normalizer (Q : Set G))
    (hNC : ∀ x ∈ C, x ∈ Subgroup.normalizer (Q : Set G) → x ∈ P)
    (β : MulAut ↥C) (hβ : ∀ u : ↥C, (u : G) ∈ U → β u = u) :
    (P.subgroupOf C).map β.toMonoidHom = P.subgroupOf C := by
  have hβ' : ∀ u : ↥C, (u : G) ∈ U → β.symm u = u := fun u hu =>
    (MulEquiv.symm_apply_eq β).2 (hβ u hu).symm
  have hsub : ∀ γ : MulAut ↥C, (∀ u : ↥C, (u : G) ∈ U → γ u = u) →
      ∀ g ∈ P.subgroupOf C, γ g ∈ P.subgroupOf C := fun γ hγ g hg =>
    Subgroup.mem_subgroupOf.2 (lc_aut_mem hQU hUC hPN hNC γ hγ g (Subgroup.mem_subgroupOf.1 hg))
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact hsub β hβ g hg
  · intro g hg
    exact ⟨β.symm g, hsub β.symm hβ' g hg, by simp⟩

theorem lc_charTwo_of {G : Type} [Group G] {C U Q P : Subgroup G}
    (hUC : U ≤ C) (hQU : Q ≤ U) (hU2 : IsPGroup 2 ↥(U.subgroupOf C))
    (hQP : Q ≤ P) (hPC : P ≤ C) (hPN : P ≤ Subgroup.normalizer (Q : Set G))
    (hsc : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    CFSG.QuasithinUnique.CharTwo (P.subgroupOf C) := by
  classical
  have hQC : Q ≤ C := hQU.trans hUC
  have hQ'P' : Q.subgroupOf C ≤ P.subgroupOf C := Subgroup.subgroupOf_mono C hQP
  have hP'N : P.subgroupOf C ≤ Subgroup.normalizer ((Q.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_normalizer_iff.1 (hPN (Subgroup.mem_subgroupOf.1 hg)) (h : G)]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hQ'2 : IsPGroup 2 ↥(Q.subgroupOf C) :=
    IsPGroup.to_le hU2 (Subgroup.subgroupOf_mono C hQU)
  have hcore := le_pCoreOf_of_le_normalizer hQ'P' hP'N hQ'2
  unfold CFSG.QuasithinUnique.CharTwo
  intro x hx
  obtain ⟨hxP, hxZ⟩ := Subgroup.mem_inf.1 hx
  have hxQ : (x : G) ∈ Q := by
    apply hsc
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hxP, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqC : (⟨q, hQC hq⟩ : ↥C) ∈ Q.subgroupOf C := Subgroup.mem_subgroupOf.2 hq
    have hq' := hcore hqC
    have hcomm := Subgroup.mem_centralizer_iff.1 hxZ _ hq'
    exact congrArg Subtype.val hcomm
  exact hcore (Subgroup.mem_subgroupOf.2 hxQ)

@[expose] noncomputable def lcMaxPar (K : Type) [Field K]
    (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank) :
    Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
  (graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a}).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)

theorem lc_ne_univ (a : Fin TwistTag.E6.foldedTag.rank) :
    ({b | b ≠ a} : Set (Fin TwistTag.E6.foldedTag.rank)) ≠ Set.univ := by
  intro h
  have := Set.ext_iff.1 h a
  simp at this

theorem lc_radical_facts
    (K : Type) [Field K] (σ : K ≃+* K) (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J ≤
        graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ∧
      graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J ≤
        graphFixedParabolic TwistTag.E6 K σ.toRingHom J ∧
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J ≤
        Subgroup.normalizer
          (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J : Set (ModGL TwistTag.E6.tag K)) ∧
      ∀ x ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        x ∈ Subgroup.normalizer
          (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J : Set (ModGL TwistTag.E6.tag K)) →
        x ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J := by
  have hN := diagram_fixed_parabolic_root_radical_normalizers TwistTag.E6 K σ J
  have hQU := graphFixedParabolicRadical_le_graphFixedPosUnipotent (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom) J
  have hUB := graphFixedPosUnipotent_le_graphFixedRootBorel (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom)
  have hBP := graphFixedRootBorel_le_graphFixedParabolic TwistTag.E6 K σ.toRingHom J
  refine ⟨hQU, hQU.trans (hUB.trans hBP), ?_, ?_⟩
  · rw [← hN]
    exact inf_le_right
  · intro x hxC hxN
    rw [← hN]
    exact Subgroup.mem_inf.2 ⟨hxC, hxN⟩

theorem lc_parabolic_ne_root
    (K : Type) [Field K] (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank) :
    graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a} ≠
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  intro h
  have hmem : canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    canonicalRep_orbitReflection_mem_graphFixedRootGroup (t := TwistTag.E6) a
  rw [← h] at hmem
  have h2 := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff (t := TwistTag.E6)
    (K := K) (σ := σ.toRingHom) σ.surjective (J := {b | b ≠ a}) (a := a)).1 hmem
  simp at h2

theorem lc_isSylow
    (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    CFSG.QuasithinUnique.IsSylowTwoOf (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
  rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]

theorem lc_charTwo
    (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) (hJ : J ≠ Set.univ) :
    CFSG.QuasithinUnique.CharTwo
      ((graphFixedParabolic TwistTag.E6 K σ.toRingHom J).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQU, hQP, hPN, -⟩ := lc_radical_facts K σ J
  have hU2 := isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := TwistTag.E6)
    (σ := σ.toRingHom)
  exact lc_charTwo_of (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    hQU hU2 hQP (graphFixedParabolic_le TwistTag.E6 K σ.toRingHom J) hPN
    (diagram_fixed_proper_parabolic_root_radical_self_centralizing TwistTag.E6 K σ hJ).2

theorem lc_cover
    (K : Type) [Field K] (σ : K ≃+* K)
    (A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hUA : (graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≤ A)
    (hA : A ≠ ⊤) : ∃ a, A ≤ lcMaxPar K σ a := by
  have hUC : graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  have hMC : A.map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hUM : graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ≤
      A.map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype := by
    have h1 := Subgroup.map_mono (f := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype)
      hUA
    rwa [Subgroup.map_subgroupOf_eq_of_le hUC] at h1
  have hMne : A.map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype ≠
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    intro h
    apply hA
    apply Subgroup.map_injective (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype_injective
    rw [h, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨J, hJ, hMJ, -⟩ :=
    (fixed_positive_root_overgroup_parabolic_containment TwistTag.E6 K σ hMC hUM).2.2 hMne
  obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
    by_contra hcon
    exact hJ (Set.eq_univ_of_forall fun a => by_contra fun ha => hcon ⟨a, ha⟩)
  refine ⟨a, fun x hx => Subgroup.mem_subgroupOf.2 ?_⟩
  have hJa : J ⊆ {b | b ≠ a} := by
    intro b hb
    simp only [Set.mem_setOf_eq]
    intro hba
    exact ha (hba ▸ hb)
  have hPJa : graphFixedParabolic TwistTag.E6 K σ.toRingHom J ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a} :=
    (graphFixedParabolic_le_iff (t := TwistTag.E6) (K := K) (σ := σ.toRingHom)
      σ.surjective).2 hJa
  have hxA := Subgroup.mem_map_of_mem (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype hx
  exact hPJa (hMJ hxA)

theorem lc_sSup_eq_top
    (K : Type) [Field K] (σ : K ≃+* K) :
    sSup (Set.range (lcMaxPar K σ)) = ⊤ := by
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  have hr0 : (0 : ℕ) < TwistTag.E6.foldedTag.rank := by decide
  have hr1 : (1 : ℕ) < TwistTag.E6.foldedTag.rank := by decide
  let i0 : Fin TwistTag.E6.foldedTag.rank := ⟨0, hr0⟩
  let i1 : Fin TwistTag.E6.foldedTag.rank := ⟨1, hr1⟩
  have hex : ∀ b : Fin TwistTag.E6.foldedTag.rank, ∃ a, a ≠ b := by
    intro b
    by_cases hb : b = i0
    · exact ⟨i1, fun h => absurd (congrArg Fin.val (h.trans hb)) (by simp [i0, i1])⟩
    · exact ⟨i0, fun h => hb h.symm⟩
  have hle : ∀ a : Fin TwistTag.E6.foldedTag.rank,
      graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a} ≤
        (sSup (Set.range (lcMaxPar K σ))).map
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype := by
    intro a
    have h1 : (graphFixedParabolic TwistTag.E6 K σ.toRingHom {b | b ≠ a}).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≤ sSup (Set.range (lcMaxPar K σ)) :=
      le_sSup ⟨a, rfl⟩
    have h2 := Subgroup.map_mono
      (f := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le
      (graphFixedParabolic_le TwistTag.E6 K σ.toRingHom {b | b ≠ a})] at h2
  have hC : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤
      (sSup (Set.range (lcMaxPar K σ))).map
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype := by
    refine (graphFixedRootGroup_eq_sup_closure (t := TwistTag.E6) hσs).le.trans
      (sup_le ?_ ((Subgroup.closure_le _).2 ?_))
    · exact (graphFixedRootBorel_le_graphFixedParabolic TwistTag.E6 K σ.toRingHom
        {b | b ≠ i0}).trans (hle i0)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, hab⟩ := hex b
      exact hle a (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨b, Ne.symm hab, rfl⟩))
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.1 (hC g.2)
  have hsg' : s = g := Subtype.ext hsg
  exact hsg' ▸ hs

theorem lc_parabolicData
    (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ParabolicData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      ((graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      (Set.range (lcMaxPar K σ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hUC : graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  refine
    { sylow := isSylowTwoOf_subgroupOf_top (lc_isSylow K σ)
      le := ?_
      cover := ?_
      charTwo := ?_
      gen := lc_sSup_eq_top K σ
      inv := ?_ }
  · rintro _ ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · exact Subgroup.subgroupOf_mono _ ((graphFixedPosUnipotent_le_graphFixedRootBorel
        (t := TwistTag.E6) (K := K) (σ := σ.toRingHom)).trans
        (graphFixedRootBorel_le_graphFixedParabolic TwistTag.E6 K σ.toRingHom
          {b | b ≠ a}))
    · intro htop
      apply lc_parabolic_ne_root K σ a
      exact le_antisymm (graphFixedParabolic_le TwistTag.E6 K σ.toRingHom {b | b ≠ a})
        (Subgroup.subgroupOf_eq_top.1 htop)
  · intro A hUA hA
    obtain ⟨a, ha⟩ := lc_cover K σ A hUA hA
    exact ⟨_, ⟨a, rfl⟩, ha⟩
  · rintro _ ⟨a, rfl⟩
    exact lc_charTwo K σ {b | b ≠ a} (lc_ne_univ a)
  · intro α hα _ P hP
    obtain ⟨a, rfl⟩ := hP
    obtain ⟨hQU, -, hPN, hNC⟩ := lc_radical_facts K σ {b | b ≠ a}
    exact lc_map_eq hQU hUC hPN hNC α (fun u hu => hα u (Subgroup.mem_subgroupOf.2 hu))

theorem lc_sylowFacts
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel S .twistedE6 2 f) {T : Subgroup S}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.QuasithinUnique.B113Lie.SylowFacts S T := by
  have h2 : CFSG.Blueprint.TwistedChevalleyModel S TwistTag.E6 (2 ^ f) := h.2
  obtain ⟨K, hF, hFin, hChar, σ₀, hσ₀, -, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.TwistedE6Cover.twisted_E6_model hf h2
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ ⟨σ₀.injective, hσ₀⟩
  have e' : S ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := e
  exact CFSG.QuasithinUnique.B113Lie.SylowFacts.of_mulEquiv_isSylow e'
    (lc_parabolicData K σ).sylowFacts hT

theorem asLieTwoAt_twistedE6 :
    AsLieTwoAt .twistedE6 := by
  intro n f X _ _ _ hadm hmod
  have hf : 1 ≤ f := hadm.2.1
  have h : CFSG.Blueprint.ChevalleyExceptionalModel X .twistedE6 2 f :=
    hmod.chevalleyExceptionalModel (by decide)
  have hsyl : ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
      CFSG.QuasithinUnique.B113Lie.SylowFacts X T :=
    fun _ hT => lc_sylowFacts hf h hT
  unfold SylowProps
  exact ⟨CFSG.QuasithinUnique.B113Lie.overgroups_of_forall_sylowFacts hsyl,
    CFSG.QuasithinUnique.B113Lie.oddAut_of_forall_sylowFacts hsyl⟩

end CFSG.Quasithin.LieOver
