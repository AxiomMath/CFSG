module

public import CFSG.ClassicalInvolution.Balance.BootstrapBootTriple
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Pair

theorem exists_fundamental_pair_of_inCommonComponent (hΩ : InClass p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {a : G} (D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a))
    {M K : Subgroup G} (hM : M ∈ centralizingMembers Ω {a}) (hK : K ∈ centralizingMembers Ω {a})
    (hcc : InCommonComponent a M K) :
    ∃ (i : Fin D.card)
      (R R' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K),
      R ∈ fundamentalSubgroups (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D ∧
      R' ∈ fundamentalSubgroups (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D ∧
      modOddIn (centralizingLayer Ω {a}) M = R.map (D.hom i) ∧
      modOddIn (centralizingLayer Ω {a}) K = R'.map (D.hom i) := by
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  have hMfam : modOddIn Y M ∈ localFamily Ω a := ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  have hKfam : modOddIn Y K ∈ localFamily Ω a := ⟨K.subgroupOf Y, ⟨K, hK, hKY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  obtain ⟨j, R', hR', hKR'⟩ := D.fundamental _ hKfam
  have hMi : modOddIn Y M ≤ (D.hom i).range := hMR ▸ Subgroup.map_le_range _ _
  have hKj : modOddIn Y K ≤ (D.hom j).range := hKR' ▸ Subgroup.map_le_range _ _
  have hij : i = j := by
    obtain ⟨Q, hQ, hMQ, hKQ⟩ := hcc
    have hQc : IsComponentOf Q ⊤ := (CFSG.isComponent_iff_open Q).mp hQ
    have : (memberJoin Ω a).Normal := memberJoin_normal hΩ.conjInvariant
    obtain ⟨D', hD'Q, -⟩ := lieDecomposition_localSystem_comp hp2 ModelFacts.modelClauseZero
      fundamentalWholeA1 hq hΩ D
    rcases D'.eq_or_commutes_of_isComponentOf hQc with ⟨i', hi'⟩ | hcomm
    · obtain ⟨j₀, hj₀⟩ := hD'Q i'
      have hQeq : Q = (D.hom j₀).range.map (layerQuotientHom hΩ.conjInvariant a) := by
        rw [hi', ← hj₀]
        exact MonoidHom.range_comp _ _
      have h1 := eq_of_modOdd_le_map_range hΩ D hM hMi (hQeq ▸ hMQ)
      have h2 := eq_of_modOdd_le_map_range hΩ D hK hKj (hQeq ▸ hKQ)
      exact h1.trans h2.symm
    · exfalso
      obtain ⟨z, hz⟩ := hΩ.classical M hM.1
      obtain ⟨hperf, hne⟩ := modOdd_perfect_ne_bot hz hM.2
      have hMJ : modOdd a M ≤ memberJoin Ω a :=
        le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) M hM
      apply hne
      rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm x (hMQ hx) y (hMJ hy)
  subst hij
  exact ⟨i, R, R', hR, hR', hMR, hKR'⟩

end Pair

section Involutions

@[expose] def FundInvolutionsConj (p : ℕ) [Fact p.Prime] (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n e : ℕ) : Prop :=
  ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
    ∀ R' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∀ r ∈ R, ∀ r' ∈ R', r * r = 1 → r' * r' = 1 → r ≠ 1 → r' ≠ 1 →
        (∀ y ∈ R, r * y = y * r) → (∀ y ∈ R', r' * y = y * r') →
          ∃ g : (modelUniv t n p e Fact.out).K, g * r * g⁻¹ = r'

@[expose] def TwoClassInvolutionsConj (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), p ≠ 2 → (t = .G2 ∨ t = .trialityD4) →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e → FundInvolutionsConj p t n e

theorem exists_conj_involution_of_inCommonComponent (hΩ : InClass p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hInv : TwoClassInvolutionsConj p) {a : G}
    (D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a)) {M K : Subgroup G}
    (hM : M ∈ centralizingMembers Ω {a}) (hK : K ∈ centralizingMembers Ω {a})
    (hcc : InCommonComponent a M K) {z z' : G} (hz : IsClassicalMember p f M z)
    (hz' : IsClassicalMember p f K z') :
    ∃ w ∈ centralizingLayer Ω {a}, z' * (w * z * w⁻¹) ∈ oddCoreIn (centralizingLayer Ω {a}) := by
  have hodd := odd_card_galoisField hp2 hq
  obtain ⟨i, R, R', hR, hR', hMR, hKR'⟩ :=
    exists_fundamental_pair_of_inCommonComponent hΩ hp2 hq D hM hK hcc
  set Y := centralizingLayer Ω {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hKY : K ≤ Y := le_centralizingLayer hK
  by_cases hspecial : D.tag i = .G2 ∨ D.tag i = .trialityD4
  ·
    have hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
      rintro ⟨h, -⟩
      rcases hspecial with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
    set zY : ↥Y := ⟨z, hMY hz.mem⟩ with hzY
    set zY' : ↥Y := ⟨z', hKY hz'.mem⟩ with hzY'
    have hzz : zY * zY = 1 := Subtype.ext (sq_eq_one hz)
    have hzz' : zY' * zY' = 1 := Subtype.ext (sq_eq_one hz')
    have hO : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥Y
    have hne1 : ∀ {m : G} (hm : m ∈ Y), orderOf m = 2 →
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨m, hm⟩ : ↥Y) ≠ 1 := by
      intro m hm hm2 h1
      have h2 : (⟨m, hm⟩ : ↥Y) ∈ classicalInvolutionOddCore ↥Y := (QuotientGroup.eq_one_iff _).1 h1
      have h3 := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ h2)
      have h4 : orderOf (⟨m, hm⟩ : ↥Y) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hm2
      rw [h4] at h3
      exact absurd h3 (by decide)
    have hMFZ := ModelFacts.fundNoncentral_generic p (D.tag i) (D.rank i) (D.exp i)
      (D.isFundTag i) (D.admissible i) hne
    have hinj : ∀ {R₀ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K},
        R₀ ∈ fundamentalSubgroups (D.tag i)
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D →
        ∀ c ∈ R₀, D.hom i c = 1 → c = 1 := by
      intro R₀ hR₀ c hc h1
      have hcc' : c ∈ Subgroup.center _ := D.ker_le_center i h1
      refine hMFZ R₀ hR₀ c hc fun y => ?_
      have := Subgroup.mem_center_iff.mp hcc' y
      have h2 : c * y * c⁻¹ * y⁻¹ = 1 := by
        rw [← this]
        group
      rw [h2]
      exact one_mem _
    have key : ∀ {R₀ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K},
        R₀ ∈ fundamentalSubgroups (D.tag i)
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D →
        ∀ {r₀ : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}, r₀ ∈ R₀ →
        ∀ {zb : LocalQuot Ω a}, D.hom i r₀ = zb → zb * zb = 1 → zb ≠ 1 →
        (∀ y ∈ R₀, D.hom i y * zb = zb * D.hom i y) →
          r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ ∀ y ∈ R₀, r₀ * y = y * r₀ := by
      intro R₀ hR₀ r₀ hr₀ zb hzb hzb2 hzb1 hcomm
      refine ⟨hinj hR₀ _ (R₀.mul_mem hr₀ hr₀) (by rw [map_mul, hzb, hzb2]),
        fun h => hzb1 (by rw [← hzb, h, map_one]), fun y hy => ?_⟩
      have h1 : r₀ * y * r₀⁻¹ * y⁻¹ = 1 := hinj hR₀ _
        (R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hr₀ hy) (R₀.inv_mem hr₀)) (R₀.inv_mem hy)) (by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hzb, ← hcomm y hy]
          group)
      have h2 := mul_inv_eq_one.1 h1
      calc r₀ * y = (r₀ * y * r₀⁻¹) * r₀ := by group
        _ = y * r₀ := by rw [h2]
    have hcommIm : ∀ {M₀ : Subgroup G} {w₀ : G} (hM₀ : M₀ ≤ Y) (hw₀ : IsClassicalMember p f M₀ w₀),
        ∀ x ∈ modOddIn Y M₀, x * QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
            (⟨w₀, hM₀ hw₀.mem⟩ : ↥Y) =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨w₀, hM₀ hw₀.mem⟩ : ↥Y) * x := by
      intro M₀ w₀ hM₀ hw₀ x hx
      obtain ⟨m', hm', rfl⟩ := hx
      have hcz : (m' : G) * w₀ = w₀ * (m' : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hw₀.subnormal hm')
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hcz)
    obtain ⟨r, hrR, hr⟩ : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) zY ∈
        Subgroup.map (D.hom i) R := by
      rw [← hMR]
      exact ⟨zY, Subgroup.mem_subgroupOf.2 hz.mem, rfl⟩
    obtain ⟨r', hr'R, hr'⟩ : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) zY' ∈
        Subgroup.map (D.hom i) R' := by
      rw [← hKR']
      exact ⟨zY', Subgroup.mem_subgroupOf.2 hz'.mem, rfl⟩
    obtain ⟨hrr, hr1, hrc⟩ := key hR hrR hr (by rw [← map_mul, hzz, map_one])
      (hne1 (hMY hz.mem) hz.orderOf_eq_two) (fun y hy => hcommIm hMY hz _ (by
        rw [hMR]; exact Subgroup.mem_map_of_mem _ hy))
    obtain ⟨hrr', hr1', hrc'⟩ := key hR' hr'R hr' (by rw [← map_mul, hzz', map_one])
      (hne1 (hKY hz'.mem) hz'.orderOf_eq_two) (fun y hy => hcommIm hKY hz' _ (by
        rw [hKR']; exact Subgroup.mem_map_of_mem _ hy))
    obtain ⟨g, hg⟩ := hInv _ _ _ hp2 hspecial (D.admissible i) R hR R' hR' r hrR r' hr'R hrr hrr'
      hr1 hr1' hrc hrc'
    obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
    have h5 : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (wT * zY * wT⁻¹) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) zY' := by
      rw [map_mul, map_mul, map_inv, hwT, ← hr, ← hr', ← map_mul, ← map_inv, ← map_mul, hg]
    have h6 : (wT * zY * wT⁻¹)⁻¹ * zY' ∈ classicalInvolutionOddCore ↥Y :=
      QuotientGroup.eq.mp h5
    have hu : (wT : G) * z * (wT : G)⁻¹ * ((wT : G) * z * (wT : G)⁻¹) = 1 := by
      calc (wT : G) * z * (wT : G)⁻¹ * ((wT : G) * z * (wT : G)⁻¹)
          = (wT : G) * (z * z) * (wT : G)⁻¹ := by group
        _ = 1 := by rw [sq_eq_one hz]; group
    have hU : ((wT : G) * z * (wT : G)⁻¹)⁻¹ * z' ∈ oddCoreIn Y := ⟨_, h6, rfl⟩
    refine ⟨(wT : G), wT.2, ?_⟩
    have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right (sq_eq_one hz')
    have := (oddCoreIn Y).inv_mem hU
    rwa [mul_inv_rev, inv_inv, hz'inv] at this
  ·
    rw [not_or] at hspecial
    have hD := ModelFacts.fundamentalSingleClass (D.tag i) (D.rank i) p (D.exp i) Fact.out
      (D.isFundTag i) (D.admissible i) hspecial.1 hspecial.2
    obtain ⟨g, hg⟩ := hD R hR R' hR'
    obtain ⟨wT, hwT⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) (D.hom i g)
    have hmod : modOddIn Y K = modOddIn Y (conjSub (wT : G) M) := by
      calc modOddIn Y K = R'.map (D.hom i) := hKR'
        _ = (conjSub g R).map (D.hom i) := by rw [hg]; rfl
        _ = conjSub (D.hom i g) (R.map (D.hom i)) := (conjSub_map _ _ _).symm
        _ = conjSub (D.hom i g) (modOddIn Y M) := by rw [← hMR]
        _ = conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) wT) (modOddIn Y M) := by
            rw [hwT]
        _ = (conjSub wT (M.subgroupOf Y)).map
              (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := conjSub_map _ _ _
        _ = ((conjSub (wT : G) M).subgroupOf Y).map
              (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
            rw [conjSub_subgroupOf]
        _ = modOddIn Y (conjSub (wT : G) M) := rfl
    have hwC : (wT : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      centralizingLayer_le_centralizer Ω {a} wT.2
    have hK''Y : conjSub (wT : G) M ≤ Y :=
      le_centralizingLayer (conjSub_mem_centralizingMembers hΩ.conjInvariant hwC hM)
    have hK'' : IsClassicalMember p f (conjSub (wT : G) M) ((wT : G) * z * (wT : G)⁻¹) :=
      hz.conj wT
    exact ⟨wT, wT.2, mul_mem_oddCoreIn_of_modOddIn_eq hodd hz' hK'' hKY hK''Y hmod⟩

theorem involutionLink_of_inCommonComponent' (hΩ : InClass p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hIH : LocalLieSystems p f Ω) (hInv : TwoClassInvolutionsConj p) {A : Subgroup G}
    {S : Set (Subgroup G)} {a : G} (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hS : S ⊆ Ω)
    (hinv : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hcover : ∀ M ∈ centralizingMembers Ω {a}, ∃ K ∈ S,
      K ≤ Subgroup.centralizer ({a} : Set G) ∧ InCommonComponent a M K) :
    InvolutionLink p f Ω A S a := by
  intro M hMmem z hz
  obtain ⟨K', hK'S, hK'a, hcc⟩ := hcover M hMmem
  have hK'mem : K' ∈ centralizingMembers Ω {a} := ⟨hS hK'S, hK'a⟩
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨z', hz'A, hK'z'⟩ := hinv K' hK'S
  obtain ⟨w, hwY, hU⟩ := exists_conj_involution_of_inCommonComponent hΩ hp2 hq hInv D hMmem hK'mem
    hcc hz hK'z'
  have hK'' : IsClassicalMember p f (conjSub w M) (w * z * w⁻¹) := hz.conj w
  obtain ⟨o, ho, hoz⟩ := exists_conj_of_mul_mem (sq_eq_one hK'') (sq_eq_one hK'z')
    (odd_card_oddCoreIn _) hU
  have hoY : o ∈ centralizingLayer Ω {a} := oddCoreIn_le _ ho
  refine ⟨K', hK'S, z', hz'A, hK'z', w⁻¹ * o⁻¹, mul_mem (inv_mem hwY) (inv_mem hoY), ?_⟩
  rw [hoz]
  group

end Involutions

section Assembly

variable {A : Subgroup G} {𝒦 : Set (Subgroup G)}

theorem exactMembers_and_localOddCentral_of_memberFamily_meets' [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) (hM : MemberFamily p f Ω A 𝒦)
    (hInv : TwoClassInvolutionsConj p) (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hconn : OmegaConnected Ω)
    (hgenModO : ∀ a ∈ A, IsFrameInvolution p f 𝒦 a → CentralizerGenerationModOTwo Ω A a)
    {K₀ : Subgroup G} {z₀ : G} (hK₀ : K₀ ∈ 𝒦) (hz₀ : IsClassicalMember p f K₀ z₀)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f 𝒦 a → ∀ K ∈ centMembers Ω a,
      ∃ L ∈ 𝒦, InCommonComponent a K L) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  have hlink : ∀ a ∈ A, IsFrameInvolution p f 𝒦 a → InvolutionLink p f Ω A 𝒦 a := by
    intro a ha hfa
    obtain ⟨K, hK𝒦, hK⟩ := hfa
    refine involutionLink_of_inCommonComponent' hΩ hp2 hq hIH hInv
      (not_subset_center_of_ne_one hnab hK.ne_one) hM.subset (fun K hK => ?_) ?_
    · obtain ⟨z, hzA, hz, -⟩ := hM.involution K hK
      exact ⟨z, hzA, hz⟩
    · intro M hMa
      obtain ⟨L, hL𝒦, hcc⟩ := hcover a ha ⟨K, hK𝒦, hK⟩ M hMa
      obtain ⟨-, -, -, hLA⟩ := hM.involution L hL𝒦
      exact ⟨L, hL𝒦, hLA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)), hcc⟩
  exact exactMembers_and_localOddCentral_of_memberFamily_wb hnab hp2 hq h9
    ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hsingle hIH hM hloc hconn hgenModO hlink hK₀
    hz₀ (hcover z₀ (hM.mem_of_isClassicalMember hK₀ hz₀) ⟨K₀, hK₀, hz₀⟩)

theorem exactMembers_and_localOddCentral_of_frameFamily' [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h27 : p ^ f ≠ 27) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hmodel : LayerGenerationModel) (hconn : OmegaConnected Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) (hInv : TwoClassInvolutionsConj p)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  obtain ⟨K₀, hK₀⟩ := hM.nonempty
  obtain ⟨z₀, -, hz₀, -⟩ := hM.involution K₀ hK₀
  exact exactMembers_and_localOddCentral_of_memberFamily_meets' hnab hp2 hq h9 hΩ hsingle hIH hM
    hInv
    (componentLayersAt_of_model hnab hp2 hq h27 ModelFacts.modelClauseZero hΩ hIH
      (fun x hx => by
        rw [← pow_two]
        exact hM.elem.2 x hx) hmodel)
    hconn
    (fun a ha hfa => centralizerGenerationModOTwo_of_memberFamily hp2 hq h27
      ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hmodel hM ha
      (by
        obtain ⟨K, -, hK⟩ := hfa
        exact not_subset_center_of_ne_one hnab hK.ne_one))
    hK₀ hz₀ hcover

theorem bootTriple_of_model' (h9 : p ^ f ≠ 9) (h27 : p ^ f ≠ 27) (hmodel : LayerGenerationModel)
    (hInv : TwoClassInvolutionsConj p) (hcover : p ≠ 2 → 5 ≤ p ^ f → FrameCoverage p f) :
    CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily' hnab hp2 hq h9 h27 hΩ
    (CoreAssembly.exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hmodel
    (omegaConnected_of_deltaConnected hconn) hM hInv
    (hcover hp2 hq G hnab K z hz hBelow hconn A hM)
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end Assembly

end CFSG.ClassicalInvolution.Balance.Bootstrap
