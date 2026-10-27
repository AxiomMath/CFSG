module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolForward

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem twoLayerIn_eq_self {X P : Subgroup G} (hP : IsTwoComponentIn P X) : twoLayerIn P = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hPres, hPq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P _ hP.1).1 hP.2
  have hsup : P ⊔ oddCoreIn P = P := le_antisymm (sup_le le_rfl (map_subtype_le _)) le_sup_left
  obtain ⟨-, hr, -, -⟩ := cover_facts hPq le_rfl hsup
  rw [hr, oddResidualIn_eq_map_primeResidual, hPres, ← MonoidHom.range_eq_map, range_subtype]

theorem not_le_coreActionKernel_of_le {V R : Subgroup G} (hRV : R ≤ V)
    (hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R)) : ¬ R ≤ coreActionKernel V := by
  intro h
  obtain ⟨-, hsimple, -⟩ := hRq
  have hcomm : ∀ x y : ↥R ⧸ pPrimeCore 2 ↥R, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨o, ho, hoe⟩ := (h a.2).2 b (hRV b.2)
    have h3 : (o : G) = (b : G)⁻¹ * (a : G)⁻¹ * b * a := hoe
    have hyR : (b : G)⁻¹ * (a : G)⁻¹ * b * a ∈ R :=
      mul_mem (mul_mem (mul_mem (inv_mem b.2) (inv_mem a.2)) b.2) a.2
    have e : (⟨(b : G)⁻¹ * (a : G)⁻¹ * b * a, hRV hyR⟩ : ↥V) = o := Subtype.ext h3.symm
    have hmem : (b : G)⁻¹ * (a : G)⁻¹ * b * a ∈ oddCoreIn R :=
      mem_oddCoreIn_of_mem_pPrimeCore hRV hyR (e ▸ ho)
    obtain ⟨o', ho', hoe'⟩ := hmem
    have h2 : (a * b)⁻¹ * (b * a) = o' := by
      apply Subtype.ext
      rw [show (o' : G) = (b : G)⁻¹ * (a : G)⁻¹ * b * a from hoe']
      simp only [coe_mul, coe_inv]
      group
    rw [h2]
    exact ho'
  have htop : center (↥R ⧸ pPrimeCore 2 ↥R) = ⊤ :=
    eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun y => hcomm y x
  have := hsimple.toNontrivial
  obtain ⟨u, v, huv⟩ := exists_pair_ne ((↥R ⧸ pPrimeCore 2 ↥R) ⧸ center (↥R ⧸ pPrimeCore 2 ↥R))
  apply huv
  induction u using QuotientGroup.induction_on with
  | H u =>
  induction v using QuotientGroup.induction_on with
  | H v =>
  rw [QuotientGroup.eq, htop]
  exact mem_top _

theorem isTwoComponentIn_of_conjClosure {L T K₁ : Subgroup G}
    (hstar : twoLayerIn (L ⊓ centralizer (T : Set G)) ≤ twoLayerIn (centralizer (T : Set G)))
    (hK₁ : IsTwoComponentIn K₁ (conjClosure (twoLayerIn (L ⊓ centralizer (T : Set G)))
      (twoLayerIn (centralizer (T : Set G))))) :
    IsTwoComponentIn K₁ (centralizer (T : Set G)) ∧
      ¬ twoLayerIn (L ⊓ centralizer (T : Set G)) ≤ coreActionKernel K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (T : Set G) with hC
  set E := twoLayerIn C with hE
  set N := conjClosure (twoLayerIn (L ⊓ C)) E with hN
  have hEC : E ≤ C := map_subtype_le _
  have hNE : N ≤ E := Sol78.conjClosure_le hstar le_normalizer
  have hNC : N ≤ C := hNE.trans hEC
  have hNsub : (N.subgroupOf C).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer hNE hEC (Sol78.le_normalizer_conjClosure _ _)
      (le_normalizer_twoLayerIn C)
  have hK₁C : IsTwoComponentIn K₁ C :=
    ⟨hK₁.1.trans hNC, GrSLit.isPComponent_subgroupOf_of_isSubnormal hK₁.1 hNC hNsub hK₁.2⟩
  refine ⟨hK₁C, fun hc => ?_⟩
  have hEN : E ≤ normalizer (K₁ : Set G) := twoLayerIn_le_normalizer hK₁C
  exact not_le_coreActionKernel_self hK₁C
    (hK₁.1.trans (conjClosure_le_coreActionKernel hc hEN))

omit [Finite G] in
theorem isTwoComponentIn_zpowers_iff {a : G} {J : Subgroup G} :
    IsTwoComponentIn J (centralizer ((zpowers a : Subgroup G) : Set G)) ↔
      IsTwoComponentIn J (centralizer ({a} : Set G)) := by
  rw [centralizer_zpowers']

theorem isSolomonMember_of_isTwoComponentAt {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJ : IsTwoComponentIn J (centralizer ({a} : Set G))) : IsSolomonMember J := by
  have hne : zpowers a ≠ ⊥ := by
    intro h
    have h1 : a = 1 := zpowers_eq_bot.mp h
    rw [h1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  exact isSolomonMember_of_isTwoComponentIn hne (isPGroup_zpowers_of_orderOf ha)
    (isTwoComponentIn_zpowers_iff.mpr hJ)

theorem mirrorGood_self {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJ : IsTwoComponentIn J (centralizer ({a} : Set G))) : MirrorGood J J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJ.1).1 hJ.2).2.2
  have hJa : J ⊓ centralizer ({a} : Set G) = J := inf_eq_left.mpr hJ.1
  refine ⟨hJq, ⟨MulEquiv.refl _⟩, a, ha, ?_, ?_, fun V hV hmv => ?_⟩
  · exact Sol78.mem_coreActionKernel_of_commute fun j hj =>
      (mem_centralizer_singleton_iff.mp (hJ.1 hj))
  · rw [hJa, twoLayerIn_eq_self hJ]
    exact le_twoLayerIn_of_isTwoComponentIn hJ
  · rw [hJa, twoLayerIn_eq_self hJ] at hmv
    have hVJ : V = J := by
      by_contra hne
      exact hmv (le_coreActionKernel_of_ne hV hJ hne)
    rw [hVJ]
    exact GSMirrorReach.refl J

end CFSG.ComponentClassification.Foote5.SolMax
