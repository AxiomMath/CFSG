module

public import CFSG.Goldschmidt.Steps.G37Wrappers
public import CFSG.Goldschmidt.Steps.G37Basic

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Goldschmidt.SStarTransport
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)

section OpenComponents

variable {G : Type*} [Group G]

theorem open_isSubnormal_map_subtype {X : Subgroup G} {S : Subgroup X} (h : S.IsSubnormal) :
    CFSG.Open.IsSubnormal (S.map X.subtype) X := by
  have h1 := (CFSG.Open.IsSubnormal.of_mathlib h).map X.subtype
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h1

theorem open_isSubnormal_of_subgroupOf {K X : Subgroup G} (hKX : K ≤ X)
    (h : (K.subgroupOf X).IsSubnormal) : CFSG.Open.IsSubnormal K X :=
  (CFSG.Open.IsSubnormal.iff_subgroupOf hKX).2 h

theorem open_isComponentOf_of_isComponentOf {L K : Subgroup G} (h : IsComponentOf L K) :
    CFSG.Open.IsComponentOf L K :=
  ⟨h.1, open_isSubnormal_of_subgroupOf h.1 h.2.1, open_isQuasisimple_iff.mpr h.2.2⟩

theorem open_isSubnormal_map {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) : CFSG.Open.IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem open_isComponentOf_map {G' : Type*} [Group G'] (e : G ≃* G') {L K : Subgroup G}
    (h : CFSG.Open.IsComponentOf L K) :
    CFSG.Open.IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, open_isSubnormal_map _ h.2.1,
    open_isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ e.injective) h.2.2⟩

end OpenComponents

section Setup

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem pPrimeCore_eq_bot_of (hO : goldschmidtOddCore M = ⊥) : CFSG.pPrimeCore 2 M = ⊥ := by
  rwa [goldschmidtOddCore_eq_pPrimeCore] at hO

theorem eq_bot_of_isSubnormal_of_odd (hO : goldschmidtOddCore M = ⊥) {S : Subgroup M}
    (hS : S.IsSubnormal) (hodd : Odd (Nat.card S)) : S = ⊥ := by
  have h := le_pPrimeCore_of_isSubnormal_of_odd hS hodd
  rwa [← goldschmidtOddCore_eq_pPrimeCore, hO, le_bot_iff] at h

theorem goldschmidtOddCore_eq_bot_of_isSubnormal (hO : goldschmidtOddCore M = ⊥)
    {S : Subgroup M} (hS : S.IsSubnormal) : goldschmidtOddCore S = ⊥ := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hS
  rw [← goldschmidtOddCore_eq_pPrimeCore M, hO, le_bot_iff] at h1
  rw [goldschmidtOddCore_eq_pPrimeCore]
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).mp h1

theorem fittingSubgroupOf_top_eq :
    CFSG.fittingSubgroupOf (⊤ : Subgroup M) = CFSG.fittingSubgroup M :=
  CFSG.Adapters.fittingSubgroupOf_top_eq_foundations M

theorem isPGroup_fitting (hO : goldschmidtOddCore M = ⊥) :
    IsPGroup 2 (CFSG.fittingSubgroupOf (⊤ : Subgroup M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [fittingSubgroupOf_top_eq]
  exact CFSG.isPGroup_of_nilpotent_normal _ CFSG.fittingSubgroup_normal
    CFSG.fittingSubgroup_nilpotent (pPrimeCore_eq_bot_of hO)

theorem fstar_le_normalizer {L : Subgroup M} (hL : IsComponentOf L ⊤) :
    generalizedFittingSubgroupOf (⊤ : Subgroup M) ≤ Subgroup.normalizer (L : Set M) := by
  refine sup_le ?_ (CFSG.Walter.componentLayerOf_top_le_normalizer hL)
  intro f hf
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (component_centralizes_fittingSubgroupOf hL) hx
  exact (Subgroup.mem_centralizer_iff.mp h1 f hf).symm

omit [Finite M] in
theorem normalClosureIn_top_normal (A : Subgroup M) : (normalClosureIn ⊤ A).Normal := by
  have h1 : (Subgroup.normalClosure ((A.subgroupOf ⊤ : Subgroup (⊤ : Subgroup M)) :
      Set (⊤ : Subgroup M))).Normal := Subgroup.normalClosure_normal
  exact h1.map _ (fun x => ⟨⟨x, trivial⟩, rfl⟩)

omit [Finite M] in
theorem le_normalClosureIn_top (A : Subgroup M) : A ≤ normalClosureIn ⊤ A := by
  intro x hx
  exact ⟨⟨x, trivial⟩, Subgroup.subset_normalClosure hx, rfl⟩

theorem normalClosureIn_le_fstar (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥)
    {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    normalClosureIn ⊤ A ≤ generalizedFittingSubgroupOf (⊤ : Subgroup M) := by
  have h1 := (h31 M ⊤ A hS).2
  set K := normalClosureIn ⊤ A with hK
  have hKn : K.Normal := normalClosureIn_top_normal A
  have hFsn : (CFSG.fittingSubgroupOf K).IsSubnormal := by
    refine Subgroup.Normal.isSubnormal ⟨fun x hx g => ?_⟩
    exact CFSG.Walter.conj_mem_map_of_characteristic
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hKn]; exact Subgroup.mem_top g) hx
  have hY : oddCoreOf (CFSG.fittingSubgroupOf K) = ⊥ := by
    rw [oddCoreOf, goldschmidtOddCore_eq_bot_of_isSubnormal hO hFsn, Subgroup.map_bot]
  rw [hY] at h1
  refine le_trans ?_ h1
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
  rw [hy, one_mul, mul_one]

theorem goldschmidtOddCore_top_eq_bot (hO : goldschmidtOddCore M = ⊥) :
    goldschmidtOddCore (⊤ : Subgroup M) = ⊥ :=
  goldschmidtOddCore_eq_bot_of_isSubnormal hO Subgroup.IsSubnormal.top

@[expose] noncomputable def topQuotEquiv (hO : goldschmidtOddCore M = ⊥) :
    M ≃* (⊤ : Subgroup M) ⧸ goldschmidtOddCore (⊤ : Subgroup M) :=
  Subgroup.topEquiv.symm.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (goldschmidtOddCore_top_eq_bot hO).symm))

theorem topQuotEquiv_apply (hO : goldschmidtOddCore M = ⊥) (x : M) :
    topQuotEquiv hO x = (QuotientGroup.mk (⟨x, trivial⟩ : (⊤ : Subgroup M)) :
      (⊤ : Subgroup M) ⧸ goldschmidtOddCore (⊤ : Subgroup M)) :=
  rfl

theorem barOf_top_eq_map (hO : goldschmidtOddCore M = ⊥) (B : Subgroup M) :
    barOf ⊤ B = B.map (topQuotEquiv hO).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : M), hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

theorem preOf_top_eq_comap (hO : goldschmidtOddCore M = ⊥)
    (L : Subgroup ((⊤ : Subgroup M) ⧸ goldschmidtOddCore (⊤ : Subgroup M))) :
    preOf ⊤ L = L.comap (topQuotEquiv hO).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

theorem preOf_top_barOf (hO : goldschmidtOddCore M = ⊥) (B : Subgroup M) :
    preOf ⊤ (barOf ⊤ B) = B := by
  rw [preOf_top_eq_comap hO, barOf_top_eq_map hO]
  exact Subgroup.comap_map_eq_self_of_injective (topQuotEquiv hO).injective B

theorem preOf_top_centralizer_barOf (hO : goldschmidtOddCore M = ⊥) (B : Subgroup M) :
    preOf ⊤ (Subgroup.centralizer (barOf ⊤ B : Set _)) = Subgroup.centralizer (B : Set M) := by
  rw [preOf_top_eq_comap hO, barOf_top_eq_map hO]
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    apply (topQuotEquiv hO).injective
    have := h _ ⟨b, hb, rfl⟩
    simpa using this
  · rintro h _ ⟨b, hb, rfl⟩
    have := congrArg (topQuotEquiv hO) (h b hb)
    simpa using this

end Setup

section Components

variable {M : Type} [Group M] [Finite M]

theorem componentFacts31 (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L ⊤)
    (hLK : L ≤ normalClosureIn ⊤ A) :
    IsSStarIn L (A ⊓ L) ∧ normalClosureIn L (A ⊓ L) = L ∧
      A = A ⊓ L ⊔ A ⊓ Subgroup.centralizer (L : Set M) := by
  have hLK' : IsComponentOf L (normalClosureIn ⊤ A) := isComponentOf_of_le hL hLK le_top
  have hc : CFSG.Open.IsComponentOf (barOf ⊤ L) (barOf ⊤ (normalClosureIn ⊤ A)) := by
    rw [barOf_top_eq_map hO, barOf_top_eq_map hO]
    exact open_isComponentOf_map _ (open_isComponentOf_of_isComponentOf hLK')
  obtain ⟨h1, h2, h3⟩ := (h31 M ⊤ A hS).1 _ hc
  rw [preOf_top_barOf hO] at h1 h2 h3
  rw [preOf_top_centralizer_barOf hO] at h3
  have hLsn : L.IsSubnormal := CFSG.Walter.isSubnormal_of_isComponentOf hL
  have hOL : oddCoreOf L = ⊥ := by
    rw [oddCoreOf, goldschmidtOddCore_eq_bot_of_isSubnormal hO hLsn, Subgroup.map_bot]
  rw [hOL, sup_bot_eq] at h2
  exact ⟨h1, h2.symm, h3⟩

theorem not_inf_le_centralizer (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥)
    {A : Subgroup M} (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L ⊤)
    (hLK : L ≤ normalClosureIn ⊤ A) :
    ¬ A ⊓ L ≤ Subgroup.centralizer (L : Set M) := by
  intro h
  obtain ⟨-, hcl, -⟩ := componentFacts31 h31 hO hS hL hLK
  apply not_le_centralizer_self hL.2.2
  have h1 : ((A ⊓ L).subgroupOf L : Subgroup L) ≤ Subgroup.center L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h hx)) y y.2)
  have h2 : Subgroup.normalClosure (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) ≤
      Subgroup.center L := Subgroup.normalClosure_le_normal h1
  have h3 : normalClosureIn L (A ⊓ L) ≤ Subgroup.centralizer (L : Set M) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp (h2 hx)) ⟨y, hy⟩)
  rwa [hcl] at h3

theorem exists_mul_of_mem (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥)
    {A : Subgroup M} (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L ⊤)
    (hLK : L ≤ normalClosureIn ⊤ A) {x : M} (hx : x ∈ A) :
    ∃ y ∈ A ⊓ L, ∃ z ∈ A ⊓ Subgroup.centralizer (L : Set M), y * z = x := by
  obtain ⟨-, -, hA⟩ := componentFacts31 h31 hO hS hL hLK
  have hAc := hS.2.1
  have hN : A ⊓ L ≤ Subgroup.normalizer
      ((A ⊓ Subgroup.centralizer (L : Set M) : Subgroup M) : Set M) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have hcomm : ∀ b ∈ A, g * b * g⁻¹ = b := by
      intro b hb
      have := hAc.is_comm.comm ⟨g, (Subgroup.mem_inf.mp hg).1⟩ ⟨b, hb⟩
      have h1 : g * b = b * g := congrArg Subtype.val this
      rw [h1, mul_inv_cancel_right]
    constructor
    · intro hb
      rw [hcomm b (Subgroup.mem_inf.mp hb).1]
      exact hb
    · intro hb
      have hbA : b ∈ A := by
        have h1 := (Subgroup.mem_inf.mp hb).1
        have h2 : b = g⁻¹ * (g * b * g⁻¹) * g := by group
        rw [h2]
        exact A.mul_mem (A.mul_mem (A.inv_mem (Subgroup.mem_inf.mp hg).1) h1)
          (Subgroup.mem_inf.mp hg).1
      rw [hcomm b hbA] at hb
      exact hb
  rw [hA] at hx
  exact mem_sup_of_le_normalizer hN hx

theorem pPrimeCore_eq_bot_of_isSubnormal (hO : goldschmidtOddCore M = ⊥) {L : Subgroup M}
    (hL : L.IsSubnormal) : CFSG.pPrimeCore 2 L = ⊥ := by
  rw [← goldschmidtOddCore_eq_pPrimeCore]
  exact goldschmidtOddCore_eq_bot_of_isSubnormal hO hL

theorem isPGroup_center (hO : goldschmidtOddCore M = ⊥) {L : Subgroup M}
    (hL : IsComponentOf L ⊤) : IsPGroup 2 (Subgroup.center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.isPGroup_of_nilpotent_normal (Subgroup.center L) inferInstance inferInstance
    (pPrimeCore_eq_bot_of_isSubnormal hO (CFSG.Walter.isSubnormal_of_isComponentOf hL))

theorem isGoldType (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥)
    {A : Subgroup M} (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L ⊤)
    (hLK : L ≤ normalClosureIn ⊤ A) : IsGoldTypeI L ∨ IsGoldTypeII L := by
  obtain ⟨hSL, hcl, -⟩ := componentFacts31 h31 hO hS hL hLK
  obtain ⟨-, -, T, -, -, -, -, -, -, hK4⟩ := hSL
  set K := normalClosureIn L (A ⊓ L) with hK
  have hKsn : K.IsSubnormal := by
    rw [hcl]
    exact CFSG.Walter.isSubnormal_of_isComponentOf hL
  have hOK : goldschmidtOddCore K = ⊥ := goldschmidtOddCore_eq_bot_of_isSubnormal hO hKsn
  let eQ : K ⧸ goldschmidtOddCore K ≃* L :=
    ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot).trans
      (MulEquiv.subgroupCongr hcl)
  let e : (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) ≃* L := Subgroup.topEquiv.trans eQ
  have hc : CFSG.Open.IsComponentOf (⊤ : Subgroup (K ⧸ goldschmidtOddCore K)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _,
      open_isQuasisimple_of_mulEquiv e.symm (open_isQuasisimple_iff.mpr hL.2.2)⟩
  rcases hK4 ⊤ hc with h | h
  · exact Or.inl (isGoldTypeI_of_mulEquiv e h)
  · exact Or.inr (isGoldTypeII_of_mulEquiv e h)

omit [Finite M] in
theorem exists_mul_of_mem_fstar {x : M}
    (hx : x ∈ generalizedFittingSubgroupOf (⊤ : Subgroup M)) :
    ∃ z ∈ CFSG.fittingSubgroupOf (⊤ : Subgroup M), ∃ e ∈ componentLayerOf (⊤ : Subgroup M),
      z * e = x := by
  have : (componentLayerOf (⊤ : Subgroup M)).Normal :=
    CFSG.Walter.normal_of_isNormalIn_top' (componentLayerOf_isNormalIn ⊤)
  exact Subgroup.mem_sup_of_normal_right.mp hx

end Components

end CFSG.Goldschmidt.G37
