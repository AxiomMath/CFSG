module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzy
public import CFSG.ClassicalInvolution.Balance.BootstrapLayers

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement MatrixGroups

section ComponentHom

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

@[expose] noncomputable def secComponentHom (hN : NormalizesLayer Φ a)
    (D : LocalLieSystemAt p f Φ a) (j : Fin D.card) : (compModel D j).K →* OddQuot a :=
  (sectionQuotientHom hN).comp (D.hom j)

theorem secComponentHom_ker_le_center (hN : NormalizesLayer Φ a) (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) : (secComponentHom hN D j).ker ≤ Subgroup.center (compModel D j).K := by
  intro y hy
  have h1 : D.hom j y = 1 := by
    have : sectionQuotientHom hN (D.hom j y) = 1 := hy
    exact (map_eq_one_iff _ (sectionQuotientHom_injective hN)).mp this
  exact D.ker_le_center j h1

theorem map_sectionQuotientHom_modOddIn (hN : NormalizesLayer Φ a) {M : Subgroup G}
    (hM : M ∈ centMembers Φ a) :
    (modOddIn (centralizingLayer Φ {a}) M).map (sectionQuotientHom hN) = modOdd a M := by
  show ((M.subgroupOf (centLayer Φ a)).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Φ a)))).map
      (sectionQuotientHom hN) = modOdd a M
  rw [Subgroup.map_map]
  exact map_layerToOddQuot_subgroupOf (le_centLayer hM)

theorem eq_of_modOdd_le_map_range_sec (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    {M : Subgroup G} (hM : M ∈ centMembers Φ a) {i j : Fin D.card}
    (hi : modOddIn (centralizingLayer Φ {a}) M ≤ (D.hom i).range)
    (hj : modOdd a M ≤ (D.hom j).range.map (sectionQuotientHom hs.normalizes)) : i = j := by
  by_contra hne
  have hθ := sectionQuotientHom_injective hs.normalizes
  have hmap := map_sectionQuotientHom_modOddIn hs.normalizes hM
  have hj' : modOddIn (centralizingLayer Φ {a}) M ≤ (D.hom j).range := by
    rw [← hmap] at hj
    exact (Subgroup.map_le_map_iff_of_injective hθ).mp hj
  exact hs.not_le_center hM.1 ((le_inf hi hj').trans (range_inf_range_le_center D hne))

theorem exists_fundamental_of_modOdd_le_sec (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) {M : Subgroup G} (hM : M ∈ centMembers Φ a)
    (hMj : modOdd a M ≤ (secComponentHom hs.normalizes D j).range) :
    ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      R.map (secComponentHom hs.normalizes D j) = modOdd a M := by
  set Y := centralizingLayer Φ {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hMfam : modOddIn Y M ∈ localFamily Φ a := ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  have hMi : modOddIn Y M ≤ (D.hom i).range := hMR ▸ Subgroup.map_le_range _ _
  have hij : i = j := by
    refine eq_of_modOdd_le_map_range_sec hs D hM hMi ?_
    have : (secComponentHom hs.normalizes D j).range =
        (D.hom j).range.map (sectionQuotientHom hs.normalizes) := MonoidHom.range_comp _ _
    rwa [this] at hMj
  subst hij
  refine ⟨R, hR, ?_⟩
  have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn hs.normalizes hM

theorem map_secComponentHom_mem_memberImages (hs : SecData p f a Φ)
    (D : LocalLieSystemAt p f Φ a) (j : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D)
    {R : Subgroup (compModel D j).K}
    (hR : R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) :
    R.map (secComponentHom hs.normalizes D j) ∈ memberImages Φ a := by
  have hΦ : ConjInvariant
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {a}) (centralizingLayer Φ {a}))) :=
    conjInvariant_oddQuotientFamily hs.inClass.conjInvariant
  have hmem := D.map_mem_of_single_class hΦ j hsingle hR
  rw [← map_sectionQuotientHom_family hs.normalizes]
  exact ⟨_, hmem, Subgroup.map_map _ _ _⟩

end ComponentHom


section Toral

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

structure SecToral (Φ : Set (Subgroup G)) (a : G) (A : Subgroup G) (S : Set G) : Prop where
  elem : IsElemAbelian 2 A
  card : Nat.card A = 8
  mem : a ∈ A
  subset : S ⊆ A
  generate : Subgroup.closure S = A
  member : ∀ z ∈ S, ∃ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) ∧ IsCentralInvolution K z ∧
    ∀ (g : G) (hg : g ∈ Subgroup.centralizer ({a} : Set G)), g ∈ A →
      ∀ y ∈ modOdd a K, oddQuotMk a ⟨g, hg⟩ * y = y * oddQuotMk a ⟨g, hg⟩

namespace SecToral

variable {A : Subgroup G} {S : Set G} (T : SecToral Φ a A S)
include T

omit [Finite G] in
theorem comm {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (T.elem.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

omit [Finite G] in
theorem sq {x : G} (hx : x ∈ A) : x * x = 1 := by
  rw [← pow_two]
  exact T.elem.2 x hx

omit [Finite G] in
theorem mem_centralizer {x : G} (hx : x ∈ A) : x ∈ Subgroup.centralizer ({a} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (T.comm hx T.mem)

theorem exists_mem_ne_one_centralizes {F₀ : Subgroup G} (hF₀ : F₀ ≤ A) (h4 : Nat.card F₀ = 4)
    {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Φ a L ∨ RankOneAt Φ a L) :
    ∃ g ∈ modOdd a F₀, g ≠ 1 ∧ ∀ y ∈ L, g * y = y * g := by
  obtain ⟨g, hgF, hg1⟩ := exists_ne_one_of_card_eq_two_pow (S := F₀) (n := 2) (by norm_num)
    (by rw [h4]; norm_num)
  have hgA : g ∈ A := hF₀ hgF
  have hgC : g ∈ Subgroup.centralizer ({a} : Set G) := T.mem_centralizer hgA
  let Q : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))).comap (oddQuotMk a)
  have hsub : A ≤ Q.map (Subgroup.centralizer ({a} : Set G)).subtype := by
    rw [← T.generate]
    refine (Subgroup.closure_le _).mpr ?_
    intro z hz
    obtain ⟨K, hKΦ, hKa, hzc, -⟩ := T.member z hz
    have hzA : z ∈ A := T.subset hz
    refine ⟨⟨z, T.mem_centralizer hzA⟩, ?_, rfl⟩
    show oddQuotMk a _ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot a)) : Set (OddQuot a))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (oddQuotMk_centralizes_of_isCentralInvolution hKΦ hKa hzc (T.mem_centralizer hzA) hL
      y hy).symm
  obtain ⟨q, hq, hqg⟩ := hsub hgA
  have hqe : q = ⟨g, hgC⟩ := Subtype.ext hqg
  subst hqe
  refine ⟨oddQuotMk a ⟨g, hgC⟩, oddQuotMk_mem_modOdd hgF hgC, ?_, fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hq y hy).symm⟩
  intro h
  have hsq : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hgC⟩ = 1 :=
    Subtype.ext (T.sq hgA)
  exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))

end SecToral

theorem SecToral.centralizedGeneratedAt {A : Subgroup G} {S : Set G} (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (ha1 : a ≠ 1) (D : LocalLieSystemAt p f Φ a) (j : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D)
    (hperf : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, ⁅R, R⁆ = R)
    (hMFC : ModelFacts.CommutingFundamentalGeneration p (D.tag j) (D.rank j) (D.exp j))
    {L : Subgroup (OddQuot a)} (hL : L = (secComponentHom hs.normalizes D j).range)
    (hdich : ∀ K ∈ centMembers Φ a, modOdd a K ≤ L ∨
      ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt A a L F₀) :
    CentralizedGeneratedAt Φ a F₀ L := by
  classical
  obtain ⟨hF₀A, hF₀4, -, hfaith⟩ := hF
  have hAC : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set G) := fun g hg => T.mem_centralizer hg
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
  have haB : a ∈ B := (hBmem a T.mem).mpr fun y _ => oddQuotMk_central (hAC a T.mem) y
  have hne1 : ∀ (g : G) (hg : g ∈ A), g ≠ 1 → oddQuotMk a ⟨g, hAC g hg⟩ ≠ 1 :=
      fun g hg hg1 h => by
    have hsq : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (T.sq hg)
    exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have hFB : ∀ f₀ ∈ F₀, f₀ ∈ B → f₀ = 1 := by
    intro f₀ hf₀ hfB
    by_contra hne
    have hf₀A := hF₀A hf₀
    exact hfaith _ (oddQuotMk_mem_modOdd hf₀ (hAC f₀ hf₀A)) (hne1 f₀ hf₀A hne)
      ((hBmem f₀ hf₀A).mp hfB)
  obtain ⟨x, hxS, y, hyS, hxB, hyB, hxyB, hrep⟩ :=
    exists_pair_in_subgroup (fun g hg => T.sq hg) (fun g hg h hh => T.comm hg hh) T.card T.subset
      T.generate T.mem haB ha1 hF₀A hF₀4 hFB
  have hxA : x ∈ A := T.subset hxS
  have hyA : y ∈ A := T.subset hyS
  obtain ⟨Kx, hKxΦ, hKxa, hxc, hKxcomm⟩ := T.member x hxS
  obtain ⟨Ky, hKyΦ, hKya, hyc, hKycomm⟩ := T.member y hyS
  have hinL : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) → ∀ z ∈ A,
      IsCentralInvolution K z → z ∉ B → modOdd a K ≤ L := by
    intro K hK hKa z hzA hz hzB
    rcases hdich K ⟨hK, hKa⟩ with h | h
    · exact h
    · exfalso
      apply hzB
      exact (hBmem z hzA).mpr fun y hy => h _ (oddQuotMk_mem_modOdd hz.mem (hAC z hzA)) y hy
  subst hL
  obtain ⟨Rx, hRx, hRxK⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hKxΦ, hKxa⟩
    (hinL Kx hKxΦ hKxa x hxA hxc hxB)
  obtain ⟨Ry, hRy, hRyK⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hKyΦ, hKya⟩
    (hinL Ky hKyΦ hKya y hyA hyc hyB)
  have key := ModelFacts.range_le_iSup_of_commutingPair (secComponentHom hs.normalizes D j)
    (secComponentHom_ker_le_center hs.normalizes D j) hperf hMFC hRx hRy
    (u₁ := oddQuotMk a ⟨x, hAC x hxA⟩) (u₂ := oddQuotMk a ⟨y, hAC y hyA⟩)
    (by rw [hRxK]; exact oddQuotMk_mem_modOdd hxc.mem _)
    (by rw [hRyK]; exact oddQuotMk_mem_modOdd hyc.mem _)
    (by
      rw [hRxK]
      intro y' hy'
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hxc.central _ hk)))
    (by
      rw [hRyK]
      intro y' hy'
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
      rw [← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hyc.central _ hk)))
    (by
      rw [hRxK]
      exact hKxcomm y (hAC y hyA) hyA)
    (by
      rw [hRyK]
      exact hKycomm x (hAC x hxA) hxA)
  have hfind : ∀ g ∈ ({x, y, x * y} : Set G), ∀ (hgA : g ∈ A) (T' : Subgroup (OddQuot a)),
      T' ≤ (secComponentHom hs.normalizes D j).range →
      (∀ t ∈ T', oddQuotMk a ⟨g, hAC g hgA⟩ * t = t * oddQuotMk a ⟨g, hAC g hgA⟩) →
      ∃ f₁ ∈ modOdd a F₀, f₁ ≠ 1 ∧ T' ≤ Subgroup.centralizer ({f₁} : Set (OddQuot a)) := by
    intro g hg hgA T' hTL hT
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
  obtain ⟨M, hMmem, hMR'⟩ := map_secComponentHom_mem_memberImages hs D j hsingle hR
  have hMR : modOdd a M = R.map (secComponentHom hs.normalizes D j) := hMR'
  have hRL : R.map (secComponentHom hs.normalizes D j) ≤
      (secComponentHom hs.normalizes D j).range := Subgroup.map_le_range _ _
  have hML : modOdd a M ≤ (secComponentHom hs.normalizes D j).range := hMR ▸ hRL
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

end Toral


section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem isInvolutionMember_modOdd_of_isSectionMember {a z : G} {K : Subgroup G}
    (hK : IsSectionMember p f (Subgroup.centralizer ({a} : Set G)) K z) (hq : 5 ≤ p ^ f) :
    IsInvolutionMember (modOdd a K) := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := hK.le
  have hperf : Group.IsPerfect ↥K := hK.perfect
  have hq' : CFSG.Open.IsQuasisimple (↥K ⧸ componentClassificationOddCore ↥K) := by
    obtain ⟨e'⟩ := hK.nonempty_equiv
    exact Components.quasisimple_of_equiv e' (isQuasisimple_specialLinearGroup_two h4)
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set ρ : ↥C →* OddQuot a := oddQuotMk a with hρ
  let K₀ : Subgroup ↥C := K.subgroupOf C
  let e : K₀ ≃* K := Subgroup.subgroupOfEquivOfLe hKa
  have hρodd : Odd (Nat.card ρ.ker) := by
    rw [hρ, oddQuotMk, QuotientGroup.ker_mk']
    exact OddCore.odd_card ↥C
  let r : ↥K₀ →* ↥(modOdd a K) := (ρ.domRestrict K₀).codRestrict (modOdd a K)
    fun x => Subgroup.mem_map_of_mem ρ x.2
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hkerr : r.ker = (ρ.domRestrict K₀).ker := by
    ext x
    change r x = 1 ↔ ρ x.val = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hroddker : Odd (Nat.card r.ker) := by
    rw [hkerr]
    exact OddKernel.odd_card_restriction_kernel ρ hρodd K₀
  have hperf₀ : Group.IsPerfect K₀ :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hq₀ : CFSG.Open.IsQuasisimple (↥K₀ ⧸ componentClassificationOddCore K₀) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore K₀) (componentClassificationOddCore K)
        e (OddCore.equiv_invariant e)) hq'
  have hKbarperf : Group.IsPerfect ↥(modOdd a K) := Group.IsPerfect.ofSurjective (f := r) hr
  have hKbarq : CFSG.Open.IsQuasisimple (↥(modOdd a K) ⧸
      componentClassificationOddCore (modOdd a K)) :=
    Components.quasisimple_of_equiv (OddKernel.coreQuotientEquiv r hr hroddker).symm hq₀
  have hzC : z ∈ C := hKa hK.mem
  let z' : ↥C := ⟨z, hzC⟩
  have hz2 : z' * z' = 1 := Subtype.ext hK.sq
  have hpg : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_mul_self_eq_one hK.sq
  have heq := imageModOddCore_centralizer hzC hpg
  have hsub' : IsSubnormal (modOdd a K) (Subgroup.centralizer {ρ z'}) := by
    have h2 := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hK.subnormal C
    have h3 := Components.chain_map ρ h2
    have h4 : (((Subgroup.centralizer {z} ⊓ C).subgroupOf C).map ρ) =
        Subgroup.centralizer {ρ z'} := heq
    rwa [h4] at h3
  refine ⟨hKbarperf.commutator_eq_top, hKbarq, ρ z', oddQuotMk_mem_modOdd hK.mem hzC, ?_, ?_, hsub'⟩
  · rw [← map_mul, hz2, map_one]
  · intro y hy
    obtain ⟨k, hkK, rfl⟩ := mem_modOdd_iff.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext ((hK.central hkK).symm))

end Members


section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

omit [Finite G] in
theorem oddCentralizerFreeMembers_of_centralizedGenerated_sec {F₀ : Subgroup G}
    {L : Subgroup (OddQuot a)} (h : CentralizedGeneratedAt Φ a F₀ L)
    (hΦ : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) → IsInvolutionMember (modOdd a K)) :
    OddCentralizerFreeMembers (modOdd a F₀) L := by
  refine OddCentralizerFreeMembers.of_le_iSup
    (𝒦 := {K' | ∃ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) ∧
      (∃ f ∈ modOdd a F₀, f ≠ 1 ∧ modOdd a K ≤ Subgroup.centralizer ({f} : Set (OddQuot a))) ∧
      modOdd a K ≤ L ∧ K' = modOdd a K}) ?_ ?_
  · refine h.trans (iSup₂_le fun K hK => iSup_le fun hKa => iSup_le fun hcen =>
      iSup_le fun hKL => ?_)
    exact le_iSup₂_of_le (modOdd a K) ⟨K, hK, hKa, hcen, hKL, rfl⟩ le_rfl
  · rintro _ ⟨K, hK, hKa, hcen, hKL, rfl⟩
    exact ⟨hKL, hΦ K hK hKa, hcen⟩

theorem oddCentralizerFree_of_centralizedGenerated_sec {E : Subgroup G}
    (hE2 : ∀ x ∈ E, x * x = 1)
    (hΦ : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) → IsInvolutionMember (modOdd a K))
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) (hlie : IsOddLieComponent L)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt E a L F₀)
    (hgen : CentralizedGeneratedAt Φ a F₀ L) : OddCentralizerFree (modOdd a F₀) L := by
  obtain ⟨hF₀E, h4, hFn, hfaith⟩ := hF
  have hB := involutionCentralizerB_of_isOddLieComponent
    ((CFSG.isComponent_iff_open L).mp hL).2.2 hlie
  exact OddCentralizerFree.of_members l2PrimeBalance hL
    (fun f hf hf1 => hB f hf1 (modOdd_sq_eq_one hE2 hF₀E f hf) (hFn hf))
    (oddCentralizerFreeMembers_of_centralizedGenerated_sec hgen hΦ)

theorem SecData.trichotomy (hs : SecData p f a Φ) (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hBelow : CITBelowU p f (Nat.card G))
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) :
    OmegaFreeAt Φ a L ∨ RankOneAt Φ a L ∨ (IsOddLieComponent L ∧ L ≤ memberJoin Φ a) := by
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow ha
  obtain ⟨D, -, -⟩ := hs.lieDecomposition_comp hp2 h0 hA1 hq Dsys
  have := memberJoin_normal_of_normalizes hs.normalizes
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · rcases D.rankOne_or_lie i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hlie
    · right
      left
      refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
      obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
      by_cases hji : j = i
      · subst hji
        exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
      · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
    · exact Or.inr (Or.inr ⟨hlie, D.le_join i⟩)
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Φ a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Φ a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    exact (hcomm y hy x hxY).symm

theorem layerGenerationLie_sec {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G)) (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hI : CommutingInputs p f Φ a) : LayerGenerationLie Φ A a := by
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  have hΦ : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) →
      IsInvolutionMember (modOdd a K) := fun K hK _ => by
    obtain ⟨z, hz⟩ := hs.member K hK
    exact isInvolutionMember_modOdd_of_isSectionMember hz hq
  unfold LayerGenerationLie LayerGenerationOn
  intro L hL hlie hjoin F₀ hF
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  obtain ⟨D', hD'Q, -⟩ := hs.lieDecomposition_comp hp2 h0 fundamentalWholeA1 hq Dsys
  have : (memberJoin Φ a).Normal := memberJoin_normal_of_normalizes hs.normalizes
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hD'Q i
    exact oddCentralizerFree_of_centralizedGenerated_sec (fun x hx => T.sq hx) hΦ hL hlie hF
      (T.centralizedGeneratedAt hs ha1 Dsys j (hI.single Dsys j)
        (fun R hR => commutator_self_eq_of_le (hI.perfect Dsys j R hR)) (hI.toral Dsys j) hj.symm
        (fun K hK => modOdd_le_or_commutes D' i hK) hF)
  · exfalso
    exact not_commutes_self_of_isQuasisimple hL'.2.2 fun x hx y hy => hcomm x hx y (hjoin hy)

theorem componentLayersAt_sec {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G)) (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hI : CommutingInputs p f Φ a) : ComponentLayersAt Φ A a :=
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponent L)
    (fun _ hL => hs.trichotomy hp2 h0 fundamentalWholeA1 hq hBelow hnc hL)
    (layerGenerationLie_sec hp2 hq h0 hBelow hs T hnc hI)

end Layers

end CFSG.ClassicalInvolution.Balance.Bootstrap
