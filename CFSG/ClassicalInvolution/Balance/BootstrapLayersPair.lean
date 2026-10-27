module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamental
public import CFSG.ClassicalInvolution.Balance.BootstrapAuditFamily
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusModels
public import CFSG.ClassicalInvolution.Balance.BootstrapGeneration

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Abelian

theorem exists_pair_of_faithful {A : Type*} [CommGroup A] [Finite A] (hexp : ∀ x : A, x * x = 1)
    (hcard : Nat.card A = 8) {S : Set A} (hS : Subgroup.closure S = ⊤) {B F : Subgroup A}
    {a : A} (ha : a ∈ B) (ha1 : a ≠ 1) (hF : Nat.card F = 4) (hFB : ∀ f ∈ F, f ∈ B → f = 1) :
    ∃ x ∈ S, ∃ y ∈ S, x ∉ B ∧ y ∉ B ∧ x * y ∉ B ∧
      ∀ g ∈ ({x, y, x * y} : Set A), ∃ f ∈ F, f ≠ 1 ∧ f * g ∈ B := by
  classical
  set π : A →* A ⧸ B := QuotientGroup.mk' B with hπ
  have hker : ∀ z, π z = 1 ↔ z ∈ B := fun z => QuotientGroup.eq_one_iff z
  have hinj : Function.Injective (fun f : F => π (f : A)) := by
    intro f g h
    have h1 : (f : A)⁻¹ * g ∈ B := QuotientGroup.eq.mp h
    have h2 : (f : A)⁻¹ * g = 1 := hFB _ (F.mul_mem (F.inv_mem f.2) g.2) h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  have hFW : 4 ≤ Nat.card (A ⧸ B) := hF ▸ Nat.card_le_card_of_injective _ hinj
  have hBc : 2 ≤ Nat.card B := by
    have : Nontrivial B := ⟨⟨⟨a, ha⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup B
  have hW4 : Nat.card (A ⧸ B) = 4 := by
    rw [hcard] at hmul
    nlinarith
  have hbij : Function.Bijective (fun f : F => π (f : A)) :=
    hinj.bijective_of_nat_card_le (by rw [hF, hW4])
  obtain ⟨x, hxS, hx1⟩ : ∃ x ∈ S, π x ≠ 1 := by
    by_contra h
    push Not at h
    have hSB : Subgroup.closure S ≤ B := by
      rw [Subgroup.closure_le]
      intro z hz
      exact (hker z).mp (h z hz)
    rw [hS] at hSB
    have hF1 : Nat.card F = 1 := by
      have : F = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro f hf
        exact hFB f hf (hSB (Subgroup.mem_top f))
      rw [this, Subgroup.card_bot]
    omega
  obtain ⟨y, hyS, hy1, hyx⟩ : ∃ y ∈ S, π y ≠ 1 ∧ π y ≠ π x := by
    by_contra h
    push Not at h
    have hxx : (π x) ^ 2 = 1 := by rw [pow_two, ← map_mul, hexp, map_one]
    have hle : Subgroup.closure S ≤ (Subgroup.zpowers (π x)).comap π := by
      rw [Subgroup.closure_le]
      intro z hz
      by_cases h1 : π z = 1
      · rw [SetLike.mem_coe, Subgroup.mem_comap, h1]
        exact Subgroup.one_mem _
      · rw [SetLike.mem_coe, Subgroup.mem_comap, h z hz h1]
        exact Subgroup.mem_zpowers _
    rw [hS] at hle
    have hz : (Subgroup.zpowers (π x)) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
      exact hle (Subgroup.mem_top z)
    have hcz : Nat.card (Subgroup.zpowers (π x)) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hxx)
    rw [hz, Subgroup.card_top] at hcz
    omega
  have hxy1 : π (x * y) ≠ 1 := by
    rw [map_mul]
    intro h
    apply hyx
    have : π y = (π x)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, hexp, map_one])
  refine ⟨x, hxS, y, hyS, fun h => hx1 ((hker x).mpr h), fun h => hy1 ((hker y).mpr h),
    fun h => hxy1 ((hker _).mpr h), ?_⟩
  intro g hg
  have hg1 : π g ≠ 1 := by
    rcases hg with rfl | rfl | rfl
    · exact hx1
    · exact hy1
    · exact hxy1
  obtain ⟨f, hf⟩ := hbij.2 (π g)
  have hf' : π (f : A) = π g := hf
  refine ⟨f, f.2, fun h => hg1 ?_, ?_⟩
  · rw [← hf', h]
    exact map_one π
  · rw [← hker, map_mul, hf', ← map_mul, hexp, map_one]

variable {G : Type*} [Group G]

theorem exists_pair_in_subgroup {A : Subgroup G} (hA2 : ∀ x ∈ A, x * x = 1)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcard : Nat.card A = 8) {S : Set G} (hSA : S ⊆ A)
    (hS : Subgroup.closure S = A) {B F₀ : Subgroup G} {a : G} (haA : a ∈ A) (haB : a ∈ B)
    (ha1 : a ≠ 1) (hF₀A : F₀ ≤ A) (hF₀ : Nat.card F₀ = 4) (hFB : ∀ f ∈ F₀, f ∈ B → f = 1) :
    ∃ x ∈ S, ∃ y ∈ S, x ∉ B ∧ y ∉ B ∧ x * y ∉ B ∧
      ∀ g ∈ ({x, y, x * y} : Set G), ∃ f ∈ F₀, f ≠ 1 ∧ f * g ∈ B := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let _ : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun x y => Subtype.ext (hAc x.1 x.2 y.1 y.2) }
  set S' : Set ↥A := {z | (z : G) ∈ S} with hS'
  have himg : A.subtype '' S' = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hSA hz⟩, hz, rfl⟩
  have hclos : Subgroup.closure S' = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [MonoidHom.map_closure, himg, hS, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hF'card : Nat.card (F₀.subgroupOf A) = 4 := by
    rw [← hF₀]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₀A).toEquiv
  obtain ⟨x, hxS, y, hyS, hxB, hyB, hxyB, hrep⟩ := exists_pair_of_faithful (A := ↥A)
    (fun x => Subtype.ext (hA2 x.1 x.2)) hcard hclos (B := B.subgroupOf A)
    (F := F₀.subgroupOf A) (a := ⟨a, haA⟩) (Subgroup.mem_subgroupOf.mpr haB)
    (fun h => ha1 (congrArg Subtype.val h)) hF'card (fun f hf hfB => by
      have h1 : (f : G) ∈ F₀ := Subgroup.mem_subgroupOf.mp hf
      have h2 : (f : G) ∈ B := Subgroup.mem_subgroupOf.mp hfB
      exact Subtype.ext (hFB f h1 h2))
  refine ⟨(x : G), hxS, (y : G), hyS, fun h => hxB (Subgroup.mem_subgroupOf.mpr h),
    fun h => hyB (Subgroup.mem_subgroupOf.mpr h), fun h => hxyB (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  intro g hg
  rcases hg with rfl | rfl | rfl
  · obtain ⟨f, hfF, hf1, hfg⟩ := hrep x (Or.inl rfl)
    exact ⟨f, Subgroup.mem_subgroupOf.mp hfF, fun h => hf1 (Subtype.ext h),
      Subgroup.mem_subgroupOf.mp hfg⟩
  · obtain ⟨f, hfF, hf1, hfg⟩ := hrep y (Or.inr (Or.inl rfl))
    exact ⟨f, Subgroup.mem_subgroupOf.mp hfF, fun h => hf1 (Subtype.ext h),
      Subgroup.mem_subgroupOf.mp hfg⟩
  · obtain ⟨f, hfF, hf1, hfg⟩ := hrep (x * y) (Or.inr (Or.inr rfl))
    exact ⟨f, Subgroup.mem_subgroupOf.mp hfF, fun h => hf1 (Subtype.ext h),
      Subgroup.mem_subgroupOf.mp hfg⟩

end Abelian

section Lie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem map_layerQuotientHom_modOddIn (hΩ : ConjInvariant Ω) {a : G} {M : Subgroup G}
    (hM : M ∈ centMembers Ω a) :
    (modOddIn (centralizingLayer Ω {a}) M).map (layerQuotientHom hΩ a) = modOdd a M := by
  show ((M.subgroupOf (centLayer Ω a)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Ω a)))).map
      (layerQuotientHom hΩ a) = modOdd a M
  rw [Subgroup.map_map]
  exact map_layerToOddQuot_subgroupOf (le_centLayer hM)

theorem exists_fundamental_of_modOdd_le (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    (j : Fin D.card) {M : Subgroup G} (hM : M ∈ centMembers Ω a)
    (hMj : modOdd a M ≤ (componentHom hΩ D j).range) :
    ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      R.map (componentHom hΩ D j) = modOdd a M := by
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hMfam : modOddIn Y M ∈ localFamily Ω a := ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  have hMi : modOddIn Y M ≤ (D.hom i).range := hMR ▸ Subgroup.map_le_range _ _
  have hij : i = j := by
    refine eq_of_modOdd_le_map_range hΩ D hM hMi ?_
    have : (componentHom hΩ D j).range =
        (D.hom j).range.map (layerQuotientHom hΩ.conjInvariant a) := MonoidHom.range_comp _ _
    rwa [this] at hMj
  subst hij
  refine ⟨R, hR, ?_⟩
  have h1 : (R.map (D.hom i)).map (layerQuotientHom hΩ.conjInvariant a) =
      R.map (componentHom hΩ D i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_layerQuotientHom_modOddIn hΩ.conjInvariant hM

theorem map_componentHom_mem_memberImages (hΩ : InClass p f Ω) {a : G}
    (D : LocalLieSystemAt p f Ω a) (j : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D)
    {R : Subgroup (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) :
    R.map (componentHom hΩ D j) ∈ memberImages Ω a := by
  have hne : (centralizingMembers Ω {a}).Nonempty := by
    obtain ⟨R, -, ⟨_, ⟨K, hK, -, rfl⟩, -⟩⟩ := D.meets j
    exact ⟨K, hK⟩
  have hΦ : ConjInvariant
      (oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a}))) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {a} hne).conjInvariant
  have hmem := D.map_mem_of_single_class hΦ j hsingle hR
  have := map_layerQuotientHom_family (a := a) hΩ.conjInvariant
  rw [← this]
  refine ⟨_, hmem, ?_⟩
  exact Subgroup.map_map _ (layerQuotientHom hΩ.conjInvariant a) (D.hom j)

end Lie

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizedGeneratedAt_of_commutingFundamental (hΩ : InClass p f Ω) {A : Subgroup G}
    {𝒦 : Set (Subgroup G)} (hM : MemberFamily p f Ω A 𝒦) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (D : LocalLieSystemAt p f Ω a) (j : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D)
    (hperf : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, ⁅R, R⁆ = R)
    (hMFC : ModelFacts.CommutingFundamentalGeneration p (D.tag j) (D.rank j) (D.exp j))
    {L : Subgroup (OddQuot a)} (hL : L = (componentHom hΩ D j).range)
    (hdich : ∀ K ∈ centMembers Ω a, modOdd a K ≤ L ∨
      ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt A a L F₀) :
    CentralizedGeneratedAt Ω a F₀ L := by
  classical
  obtain ⟨hF₀A, hF₀4, -, hfaith⟩ := hF
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hM.elem.2 x hx
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hAC : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc g hg a ha)
  set B : Subgroup G := A ⊓ ((Subgroup.centralizer (L : Set (OddQuot a))).comap
    (oddQuotMk a)).map (Subgroup.centralizer ({a} : Set G)).subtype with hB
  have hBmem : ∀ (g : G) (hg : g ∈ A), g ∈ B ↔
      ∀ y ∈ L, oddQuotMk a ⟨g, hAC g hg⟩ * y = y * oddQuotMk a ⟨g, hAC g hg⟩ := by
    intro g hg
    constructor
    · rintro ⟨-, ⟨c, hc, hcg⟩⟩ y hy
      have hcg' : c = ⟨g, hAC g hg⟩ := Subtype.ext hcg
      subst hcg'
      exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
    · intro h
      exact ⟨hg, ⟨⟨g, hAC g hg⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => (h y hy).symm,
        rfl⟩⟩
  have haB : a ∈ B := (hBmem a ha).mpr fun y _ => oddQuotMk_central (hAC a ha) y
  have hne1 : ∀ (g : G) (hg : g ∈ A), g ≠ 1 → oddQuotMk a ⟨g, hAC g hg⟩ ≠ 1 :=
      fun g hg hg1 h => by
    have hsq : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (hA2 g hg)
    exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have hFB : ∀ f₀ ∈ F₀, f₀ ∈ B → f₀ = 1 := by
    intro f₀ hf₀ hfB
    by_contra hne
    have hf₀A := hF₀A hf₀
    exact hfaith _ (oddQuotMk_mem_modOdd hf₀ (hAC f₀ hf₀A)) (hne1 f₀ hf₀A hne)
      ((hBmem f₀ hf₀A).mp hfB)
  have hmem𝒦 : ∀ K ∈ 𝒦, K ∈ centMembers Ω a ∧ K ≤ Subgroup.centralizer (A : Set G) := by
    intro K hK
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    exact ⟨⟨hM.subset hK, hKA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))⟩,
      hKA⟩
  have hcomm𝒦 : ∀ K ∈ 𝒦, ∀ k ∈ K, ∀ g ∈ A, g * k = k * g := fun K hK k hk g hg =>
    Subgroup.mem_centralizer_iff.mp ((hmem𝒦 K hK).2 hk) g hg
  have hinL : ∀ K ∈ 𝒦, ∀ z : G, IsClassicalMember p f K z → z ∉ B → modOdd a K ≤ L := by
    intro K hK z hz hzB
    rcases hdich K (hmem𝒦 K hK).1 with h | h
    · exact h
    · exfalso
      apply hzB
      have hzA := hM.mem_of_isClassicalMember hK hz
      exact (hBmem z hzA).mpr fun y hy => h _ (oddQuotMk_mem_modOdd hz.mem (hAC z hzA)) y hy
  obtain ⟨x, ⟨Kx, hKx, hxcl⟩, y, ⟨Ky, hKy, hycl⟩, hxB, hyB, hxyB, hrep⟩ :=
    exists_pair_in_subgroup hA2 hAc hM.card (S := {z | ∃ K ∈ 𝒦, IsClassicalMember p f K z})
      (fun z ⟨K, hK, hz⟩ => hM.mem_of_isClassicalMember hK hz) hM.generate.symm ha haB ha1 hF₀A
      hF₀4 hFB
  have hxA : x ∈ A := hM.mem_of_isClassicalMember hKx hxcl
  have hyA : y ∈ A := hM.mem_of_isClassicalMember hKy hycl
  subst hL
  obtain ⟨Rx, hRx, hRxK⟩ := exists_fundamental_of_modOdd_le hΩ D j (hmem𝒦 Kx hKx).1
    (hinL Kx hKx x hxcl hxB)
  obtain ⟨Ry, hRy, hRyK⟩ := exists_fundamental_of_modOdd_le hΩ D j (hmem𝒦 Ky hKy).1
    (hinL Ky hKy y hycl hyB)
  have key := ModelFacts.range_le_iSup_of_commutingPair (componentHom hΩ D j)
    (componentHom_ker_le_center hΩ D j) hperf hMFC hRx hRy
    (u₁ := oddQuotMk a ⟨x, hAC x hxA⟩) (u₂ := oddQuotMk a ⟨y, hAC y hyA⟩)
    (by rw [hRxK]; exact oddQuotMk_mem_modOdd hxcl.mem _)
    (by rw [hRyK]; exact oddQuotMk_mem_modOdd hycl.mem _)
    (by
      rw [hRxK]
      intro y' hy'
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hxcl.isCentralInvolution.central _ hk)))
    (by
      rw [hRyK]
      intro y' hy'
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hycl.isCentralInvolution.central _ hk)))
    (by
      rw [hRxK]
      intro y' hy'
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hcomm𝒦 Kx hKx k hk y hyA)))
    (by
      rw [hRyK]
      intro y' hy'
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hcomm𝒦 Ky hKy k hk x hxA)))
  have hfind : ∀ g ∈ ({x, y, x * y} : Set G), ∀ (hgA : g ∈ A) (T : Subgroup (OddQuot a)),
      T ≤ (componentHom hΩ D j).range →
      (∀ t ∈ T, oddQuotMk a ⟨g, hAC g hgA⟩ * t = t * oddQuotMk a ⟨g, hAC g hgA⟩) →
      ∃ f₁ ∈ modOdd a F₀, f₁ ≠ 1 ∧ T ≤ Subgroup.centralizer ({f₁} : Set (OddQuot a)) := by
    intro g hg hgA T hTL hT
    obtain ⟨f₁, hf₁F, hf₁1, hf₁B⟩ := hrep g hg
    have hf₁A := hF₀A hf₁F
    have hf₁gA : f₁ * g ∈ A := A.mul_mem hf₁A hgA
    have hB' := (hBmem (f₁ * g) hf₁gA).mp hf₁B
    refine ⟨oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩, oddQuotMk_mem_modOdd hf₁F _, hne1 f₁ hf₁A hf₁1, ?_⟩
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hB' t (hTL ht)
    have h2 := hT t ht
    have h3 : oddQuotMk a ⟨f₁ * g, hAC _ hf₁gA⟩ =
        oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * oddQuotMk a ⟨g, hAC g hgA⟩ := by
      rw [← map_mul]
      rfl
    rw [h3] at h1
    have h4 : (oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * t) * oddQuotMk a ⟨g, hAC g hgA⟩ =
        (t * oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩) * oddQuotMk a ⟨g, hAC g hgA⟩ := by
      calc (oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * t) * oddQuotMk a ⟨g, hAC g hgA⟩
          = oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * (t * oddQuotMk a ⟨g, hAC g hgA⟩) := by
            rw [mul_assoc]
        _ = oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * (oddQuotMk a ⟨g, hAC g hgA⟩ * t) := by rw [h2]
        _ = (oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * oddQuotMk a ⟨g, hAC g hgA⟩) * t := by
            rw [mul_assoc]
        _ = t * (oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩ * oddQuotMk a ⟨g, hAC g hgA⟩) := h1
        _ = (t * oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩) * oddQuotMk a ⟨g, hAC g hgA⟩ := by
            rw [mul_assoc]
    exact (mul_right_cancel h4).symm
  refine key.trans (iSup₂_le fun R hR => iSup_le fun hcond => ?_)
  obtain ⟨M, hMmem, hMR'⟩ := map_componentHom_mem_memberImages hΩ D j hsingle hR
  have hMR : modOdd a M = R.map (componentHom hΩ D j) := hMR'
  have hRL : R.map (componentHom hΩ D j) ≤ (componentHom hΩ D j).range :=
    Subgroup.map_le_range _ _
  have hML : modOdd a M ≤ (componentHom hΩ D j).range := hMR ▸ hRL
  have hf : ∃ f₁ ∈ modOdd a F₀, f₁ ≠ 1 ∧
      modOdd a M ≤ Subgroup.centralizer ({f₁} : Set (OddQuot a)) := by
    rw [hMR]
    rcases hcond with h | h | h
    · exact hfind x (Or.inl rfl) hxA _ hRL h
    · exact hfind y (Or.inr (Or.inl rfl)) hyA _ hRL h
    · refine hfind (x * y) (Or.inr (Or.inr rfl)) (A.mul_mem hxA hyA) _ hRL fun t ht => ?_
      have h' := h t ht
      have h3 : oddQuotMk a ⟨x * y, hAC _ (A.mul_mem hxA hyA)⟩ =
          oddQuotMk a ⟨x, hAC x hxA⟩ * oddQuotMk a ⟨y, hAC y hyA⟩ := by
        rw [← map_mul]
        rfl
      rw [h3]
      exact h'
  exact le_iSup₂_of_le M hMmem.1 (le_iSup_of_le hMmem.2 (le_iSup_of_le hf
    (le_iSup_of_le hML hMR.ge)))

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
