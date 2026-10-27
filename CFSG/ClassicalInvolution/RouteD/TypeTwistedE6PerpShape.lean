module

public import CFSG.ClassicalInvolution.RouteD.TypeCBlock
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerMain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinModel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def PerpTableR (p f : ℕ) [Fact p.Prime] {P : Type} (rel : P → P → Prop) (p₀ : P)
    (tY : StatedLieTag) (nY : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ), e = f → IsFundTag t → t ≠ .G2 →
    t ≠ .trialityD4 → StatedLieAdmissible t n p e →
    ∀ R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∀ k ∈ R₀, (∀ r ∈ R₀, r * k = k * r) →
      ∀ φ : {R : Subgroup (modelUniv t n p e Fact.out).K //
          R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧
            R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n p e Fact.out).K)} ≃ P,
        (∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R')) → (∀ R, R.1 = R₀ → φ R = p₀) →
          t = tY ∧ n = nY

@[expose] def TE6PerpTableR (p f : ℕ) [Fact p.Prime] : Prop :=
  PerpTableR p f (TE6Layer.rel (p := p) (f := f)) none .POmegaMinus 5

section Layer

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem exists_central_model_elt {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card}
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K : Subgroup G} {R₀ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hK : Corr Ω x D i K R₀) {z : G} (hz : IsClassicalMember p f K z) :
    ∃ k ∈ R₀, D.hom i k = locMk Ω x ⟨z, le_centralizingLayer hK.1 hz.mem⟩ ∧
      ∀ r ∈ R₀, r * k = k * r := by
  obtain ⟨k, hkR, hk⟩ := exists_model_elt hK hz.mem
  refine ⟨k, hkR, hk, ?_⟩
  have hperfR : Group.IsPerfect ↥R₀ := Subgroup.isPerfect_iff.mpr (le_antisymm
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact R₀.mul_mem (R₀.mul_mem (R₀.mul_mem ha hb) (R₀.inv_mem ha)) (R₀.inv_mem hb))
    (hperf R₀ hK.2.1))
  have hcomm : Commutes (R₀.map (D.hom i)) ((Subgroup.zpowers k).map (D.hom i)) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, ⟨m, rfl⟩, rfl⟩
    have hmem : D.hom i a ∈ locImg Ω x K := hK.2.2 ▸ ⟨a, ha, rfl⟩
    obtain ⟨y, hy, hya⟩ := hmem
    have hyz : z * (y : G) = (y : G) * z :=
      Subgroup.mem_centralizer_iff.mp (le_centralizer_of_isClassicalMember hz
        (Subgroup.mem_subgroupOf.mp hy)) z (Set.mem_singleton z)
    have hc : D.hom i a * D.hom i k = D.hom i k * D.hom i a := by
      rw [hk, ← hya, ← map_mul, ← map_mul]
      exact congrArg (locMk Ω x) (Subtype.ext hyz.symm)
    rw [map_zpow]
    exact ((show Commute (D.hom i a) (D.hom i k) from hc).zpow_right m).eq
  exact fun r hr => (commutes_of_commutes_map (D.hom i) (D.ker_le_center i) hperfR hcomm)
    r hr k (Subgroup.mem_zpowers k)

theorem visible_equiv_layer' (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {K : Subgroup G} {R₀ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hK : Corr Ω x D i K R₀) {z : G} (hz : z ∈ K) {k : (modelUniv
      (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hk : D.hom i k = locMk Ω x ⟨z, le_centralizingLayer hK.1 hz⟩) :
    ∃ e : {N : compMembers Ω x D i // N.1 ∈ centralizingMembers Ω {x, z}} ≃
        {R : compFund D i // R.1 ≤ Subgroup.centralizer ({k} : Set _)},
      (∀ N N', Commutes N.1.1 N'.1.1 ↔ Commutes (e N).1.1 (e N').1.1) ∧
        ∀ N, N.1.1 = K → (e N).1.1 = R₀ := by
  obtain ⟨e₀, he₀⟩ := exists_compMembersEquiv hΩ hex hP1 D hsc hperf
  refine ⟨Equiv.subtypeEquiv e₀ (fun N => ?_), fun N N' => ?_, fun N hN => ?_⟩
  · exact visible_iff_corr hΩ hP1 hperf hK (he₀ N) hz hk
  · exact corr_commutes hΩ hP1 hperf (he₀ N.1) (he₀ N'.1)
  · have h1 : Corr Ω x D i K (e₀ N.1).1 := hN ▸ he₀ N.1
    exact corr_unique_left hperf h1 hK

end Layer

section Shape

variable [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem shape_of_perpTableR (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {K : Subgroup G} (hK : K ∈ centralizingMembers Ω {x}) {z : G}
    (hz : IsClassicalMember p f K z)
    (hlink : ∀ R ∈ centralizingMembers Ω {x, z}, Linked Ω x K R)
    {P : Type} (rel : P → P → Prop)
    (φP : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃ P)
    (hφP : ∀ N N', Commutes N.1 N'.1 ↔ rel (φP N) (φP N')) {p₀ : P}
    (hKP : ∀ h : K ∈ centralizingMembers Ω {x, z}, φP ⟨K, h⟩ = p₀)
    {tY : StatedLieTag} {nY : ℕ} (hTable : PerpTableR p f rel p₀ tY nY) :
    D.card = 1 ∧ ∃ i₁ : Fin D.card, D.tag i₁ = tY ∧ D.rank i₁ = nY ∧
      ∃ R : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K,
        Corr Ω x D i₁ K R := by
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D hp2 (by omega) hD
  have hcard : D.card = 1 := card_eq_one_of_linked hΩ hex hP1 D hK hz.mem hlink
  obtain ⟨i₁, R₀, hR₀⟩ := exists_corr_of_mem hΩ hex D hK
  refine ⟨hcard, i₁, ?_⟩
  have hKvis : K ∈ centralizingMembers Ω {x, z} :=
    mem_centralizingMembers_pair.mpr ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨k, hkR, hk, hkc⟩ := exists_central_model_elt (hperf i₁) hR₀ hz
  obtain ⟨e, he, heK⟩ := visible_equiv_layer' hΩ hex hP1 D (hsc i₁) (hperf i₁) hR₀ hz.mem hk
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hall : ∀ N ∈ centralizingMembers Ω {x}, N ∈ compMembers Ω x D i₁ := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub.elim j i₁ ▸ hj⟩
  let ι : {N : Subgroup G // N ∈ centralizingMembers Ω {x, z}} ≃
      {N : compMembers Ω x D i₁ // N.1 ∈ centralizingMembers Ω {x, z}} :=
    { toFun := fun N => ⟨⟨N.1, hall N.1 (mem_centralizingMembers_pair.mp N.2).1⟩, N.2⟩
      invFun := fun N => ⟨N.1.1, N.2⟩
      left_inv := fun N => rfl
      right_inv := fun N => rfl }
  let ι2 := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun R : Subgroup (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K =>
      R ∈ compFund D i₁) (fun R => R ≤ Subgroup.centralizer ({k} : Set _))
  let φ := ι2.symm.trans (e.symm.trans (ι.symm.trans φP))
  have hφ : ∀ R R', Commutes R.1 R'.1 ↔ rel (φ R) (φ R') := by
    intro R R'
    have h1 := he (e.symm (ι2.symm R)) (e.symm (ι2.symm R'))
    have h2 := hφP (ι.symm (e.symm (ι2.symm R))) (ι.symm (e.symm (ι2.symm R')))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    exact h1.symm.trans h2
  have h0 : ∀ R, R.1 = R₀ → φ R = p₀ := by
    intro R hR
    set N₀ : {N : compMembers Ω x D i₁ // N.1 ∈ centralizingMembers Ω {x, z}} :=
      ⟨⟨K, hall K hK⟩, hKvis⟩ with hN₀
    have h1 : e N₀ = ι2.symm R := Subtype.ext (Subtype.ext ((heK N₀ rfl).trans hR.symm))
    have h2 : e.symm (ι2.symm R) = N₀ := by rw [← h1]; exact e.symm_apply_apply N₀
    show φP (ι.symm (e.symm (ι2.symm R))) = p₀
    rw [h2]
    exact hKP hKvis
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hD i₁).2
  obtain ⟨ht, hn⟩ := hTable hp2 hq (D.tag i₁) (D.rank i₁) (D.exp i₁) hexp (D.isFundTag i₁)
    (hD i₁).1 (hD i₁).2 (D.admissible i₁) R₀ hR₀.2.1 k hkR hkc φ hφ h0
  exact ⟨ht, hn, R₀, hR₀⟩

end Shape

section Visible

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_visible_equiv' (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {z * nd.w 0, z}} ≃ TE6Layer p f,
      (∀ N N', Commutes N.1 N'.1 ↔ TE6Layer.rel (φ N) (φ N')) ∧
        ∀ h : K ∈ centralizingMembers Ω {z * nd.w 0, z}, φ ⟨K, h⟩ = none := by
  classical
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩
  have hKvis : K ∈ centralizingMembers Ω {z * nd.w 0, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hKz, le_centralizer_of_commutes (nd.commK 0 (by norm_num))
      (nd.isCl 0 (by norm_num)).mem⟩
  have hperf : ∀ ρ ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) c.hn,
      ρ ≤ ⁅ρ, ρ⁆ := by
    rintro ρ ⟨i, hi⟩
    exact (Subgroup.isPerfect_iff.mp (c.isPerfect_of_isLongRootSU2 hi)).ge
  have hmem : ∀ ρ : {R : Subgroup (Su (GaloisField p (2 * f)) p f (5 + 1)) //
      R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 5 + 1) ∧
        R ≤ Subgroup.centralizer ({te6Inv p f} : Set _)},
      ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = ρ.1.map c.d.ψ :=
    fun ρ => typeU_exists_member_of_root c.hp2 c.hq c.hm c.hΩ c.hK c.hz c.hP1 c.d ρ.2.1
  choose Lof hLz hLK hLimg using hmem
  have hvis : ∀ ρ, Lof ρ ∈ centralizingMembers Ω {z * nd.w 0, z} := by
    intro ρ
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hLz ρ, (UNodes.le_centralizer_iff_root c nd (hLz ρ) (hperf _ ρ.2.1) (hLimg ρ)).mpr
      ρ.2.2⟩
  let ι : TE6Layer p f → {N : Subgroup G // N ∈ centralizingMembers Ω {z * nd.w 0, z}} :=
    fun a => Option.elim a ⟨K, hKvis⟩ fun ρ => ⟨Lof ρ, hvis ρ⟩
  have hinj : Function.Injective ι := by
    intro a b hab
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (hLK ρ')
    · exact absurd (congrArg Subtype.val hab) (hLK ρ)
    · have h : Lof ρ = Lof ρ' := congrArg Subtype.val hab
      have himg : ρ.1.map c.d.ψ = ρ'.1.map c.d.ψ := by
        rw [← hLimg ρ, ← hLimg ρ', h]
      exact congrArg some (Subtype.ext (eq_of_map_eq_of_central c.d.ψ c.d.ker_le
        (hperf _ ρ.2.1) (hperf _ ρ'.2.1) himg))
  have hsurj : Function.Surjective ι := by
    rintro ⟨N, hN⟩
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hN
    obtain ⟨hNz, hNw⟩ := hN
    by_cases hNK : N = K
    · exact ⟨none, Subtype.ext hNK.symm⟩
    · obtain ⟨ρ, hρT, hNρ⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1
        c.d hNz hNK
      have hρc : ρ ≤ Subgroup.centralizer ({te6Inv p f} : Set _) :=
        (UNodes.le_centralizer_iff_root c nd hNz (hperf ρ hρT) hNρ).mp hNw
      refine ⟨some ⟨ρ, hρT, hρc⟩, Subtype.ext ?_⟩
      exact locImg_injOn c.hΩ c.hP1 (hLz _) hNz ((hLimg ⟨ρ, hρT, hρc⟩).trans hNρ.symm)
  have key : ∀ a b : TE6Layer p f, Commutes (ι a).1 (ι b).1 ↔ TE6Layer.rel a b := by
    intro a b
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · exact iff_false_intro (not_commutes_self_of_isClassicalMember c.hz)
    · exact iff_true_intro (typeU_commutes_K_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d
        (hLz ρ') (hLK ρ'))
    · exact iff_true_intro (commutes_symm (typeU_commutes_K_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK
        c.hz c.hP1 c.d (hLz ρ) (hLK ρ)))
    · obtain ⟨i, hi⟩ := ρ.2.1
      exact c.commutes_iff_root (hLz ρ) (hLz ρ') hi (hLimg ρ) (hLimg ρ')
  refine ⟨(Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm, fun N N' => ?_, fun h => ?_⟩
  · have h1 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N) = N :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N
    have h2 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N') = N' :=
      (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N'
    have := key ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N)
      ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N')
    rwa [h1, h2] at this
  · exact (Equiv.symm_apply_eq _).mpr (Subtype.ext rfl)

end Visible

section Consumer

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_te6Base_partner_r (hf : 1 ≤ f) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω) (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (Dz : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G}
    (hβ : IsPartnerU c nd β) (hn3 : ¬ Commutes β (nd.j 3))
    (hP1x : LocalOddCentral Ω {z * nd.w 0})
    (hexc : ∀ D : LieSystemData p f (locQuot Ω (z * nd.w 0)) (locFamily Ω (z * nd.w 0)),
      ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hTable : TE6PerpTableR p f) (hAdapt : TE6Adaptation hf nd) :
    ∃ V : Fin 3 → Subgroup G, IsTE6Base p f hf Ω K z V ∧ TE6Partner p f Ω V := by
  classical
  obtain ⟨D⟩ := exists_lieSystemData hIH (not_subset_center_mul hMFZ c nd hsingle Dz)
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D c.hp2 (by have := c.hq; omega) (hexc D)
  have hβx : β ∈ centralizingMembers Ω {z * nd.w 0} :=
    ⟨hβ.mem, UCtx.partner_le_centralizer_mul c nd (by norm_num : 0 < 5) hβ.mem hβ.pK hβ.p0⟩
  have hlink := linked_of_visible c nd hβx hβ.nK hβ.n0 hn3
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv' c nd
  have hKx := UNodes.K_mem_centralizingMembers_mul c nd (by norm_num : 0 < 5)
  obtain ⟨hcard, i₁, ht, hn, R₀, hR₀⟩ := shape_of_perpTableR c.hp2 c.hq c.hΩ c.hex hP1x D (hexc D)
    hKx c.hz hlink TE6Layer.rel φ hφ hφK hTable
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht.symm.trans h) (by decide)
  have hTwin' : TwinPartnerFactTwin p f (D.tag i₁) (D.rank i₁) (D.exp i₁) := by
    rw [ht, hn, hexp]
    exact twinPartnerFactTwin_pOmegaMinus_five c.hp2 c.hq
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hKc : K ∈ compMembers Ω (z * nd.w 0) D i₁ := ⟨hKx, hR₀.2.2 ▸ Subgroup.map_le_range _ _⟩
  have hM0 := UNodes.mem_centralizingMembers_mul c nd (by norm_num : 0 < 5) (Or.inl rfl)
  have hMc : nd.j 0 ∈ compMembers Ω (z * nd.w 0) D i₁ := by
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨nd.j 0, hM0, rfl⟩)
    exact ⟨hM0, hsub.elim j i₁ ▸ hj⟩
  obtain ⟨N, hN, pKN, pNM⟩ := exists_twin_partner_of_twin c.hq c.hΩ c.hex hP1x D (hsc i₁)
    (hperf i₁) hTwin' hKc hMc (nd.ne_K 0 (by norm_num)).symm (nd.commK 0 (by norm_num))
    c.hz.mem (nd.isCl 0 (by norm_num)).mem c.hz.orderOf_eq_two
    (nd.isCl 0 (by norm_num)).orderOf_eq_two rfl
  obtain ⟨V, hV, hV0, hc1, hc2⟩ := hAdapt N hN.1 pKN pNM
  refine ⟨V, hV, N, hN.1.1, ?_, hc1, hc2⟩
  rw [hV0]
  exact pNM

theorem routeD_typeU_five_of_nonclassical_r (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeU p f 5 Ω z)
    (hP1 : LocalOddCentral Ω {z}) (hMFZ : Gaps.FundNoncentral p)
    (hIH : LocalLieSystems p f Ω)
    (hP1x : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → LocalOddCentral Ω {z * nd.w 0})
    (hexc : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) →
      ∀ D : LieSystemData p f (locQuot Ω (z * nd.w 0)) (locFamily Ω (z * nd.w 0)),
        ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hTable : TE6PerpTableR p f)
    (hAdapt : ∀ (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
      ¬ Commutes β (nd.j 3) → TE6Adaptation hadm.2.1 nd) :
    (∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .PSU ∧ D.rank i = 8) ∨
      ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 :=
  (routeD_typeU_dichotomy hp2 hq (by norm_num) hΩ hex hK hsingle hconn hz hshape hP1).imp id
    fun hobs => by
      obtain ⟨c, nd, β, hβΩ, hβcl, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩ := hobs
      obtain ⟨Dz, -⟩ := hshape
      have hβ : IsPartnerU c nd β := ⟨hβΩ, hβcl, hnK, hpK, hn0, hp0, hlast, hmid⟩
      obtain ⟨V, hV, hpart⟩ := exists_te6Base_partner_r hadm.2.1 hMFZ hIH c nd hsingle Dz hβ
        hnot (hP1x c nd hβ hnot) (hexc c nd hβ hnot) hTable (hAdapt c nd hβ hnot)
      exact routeD_twistedE6_of_base hadm hq hΩ hK hsingle hconn hz hV hpart

end Consumer

end CFSG.ClassicalInvolution.RouteD.NonClassical
