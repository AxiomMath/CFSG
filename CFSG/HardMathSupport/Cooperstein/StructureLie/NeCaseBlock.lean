module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseAux
public import CFSG.HardMathSupport.Cooperstein.StructureLie.Transvection
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortCommutator
public import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeModule
public import CFSG.Quasithin.Background.D14Normal

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM IsClassicalTwoOrG2)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Proving (mem_pCoreOf_iff)
open scoped commutatorElement

variable {G : Type} [Group G]

section BarIncl

variable {X K : Subgroup G}

@[expose] def barIncl (X : Subgroup G) {K : Subgroup G} (hK : K ≤ X) :
    ↥K →* ↥X ⧸ CFSG.pCore 2 ↥X :=
  (barHom X).comp (Subgroup.inclusion hK)

theorem range_barIncl (hK : K ≤ X) : (barIncl X hK).range = barM X K := by
  ext γ
  constructor
  · rintro ⟨l, rfl⟩
    exact barHom_mem_barM (X := X) (Y := K) (x := ⟨l, hK l.2⟩) l.2
  · intro hγ
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_ker_barIncl (hK : K ≤ X) {l : ↥K} :
    l ∈ (barIncl X hK).ker ↔ (l : G) ∈ pCoreOf 2 X := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have : (⟨l, hK l.2⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h
    exact mem_pCoreOf_iff.mpr ⟨_, this, rfl⟩
  · intro h
    obtain ⟨y, hy, hyl⟩ := mem_pCoreOf_iff.mp h
    have : y = ⟨l, hK l.2⟩ := Subtype.ext hyl
    subst this
    exact (QuotientGroup.eq_one_iff _).mpr hy

theorem barM_self (X : Subgroup G) : barM X X = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective γ
  exact barHom_mem_barM x.2

theorem barM_perfect {X K : Subgroup G} (hK : K ≤ X) (hperf : ⁅K, K⁆ = K) :
    ⁅barM X K, barM X K⁆ = barM X K := by
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have : Group.IsPerfect (barIncl X hK).range := Group.IsPerfect.range _
  have h := Subgroup.isPerfect_iff.mp this
  rwa [range_barIncl] at h

end BarIncl

variable [Finite G]

theorem yh_le_normalizer (hbot : EightNineBotCase)
    {X S L Yh : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hcent : CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralizerInRadical
      (barM X L) (barM X (S ⊓ L)))
    (hY1 : Yh ≤ neY S L) (hY3 : (Yh.subgroupOf (neY S L)).Normal)
    (hchev : CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.IsChevOver Yh (S ⊓ L)) :
    Yh ≤ Subgroup.normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q', _, ψ, hψs, hψk, hQ'qs, hQ'cl⟩ := hchev
  have hQ'perf : commutator Q' = ⊤ := hQ'qs.1.commutator_eq_top
  have hQS : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hSX : S ≤ X := hA.twoRadical.1
  have hLX : L ≤ X := hL.le
  have hX1X : neX1 S L ≤ X := (neX1_le_sup S L).trans (sup_le hLX hSX)
  have hA1 := asc81bHyp_neX1 hA hL hSL
  have hX1 := isKGroup_neX1 hX hA hL
  have hRP : S ⊓ L ≤ pCoreOf 2 (neX1 S L) := inf_le_pCoreOf_neX1 hA hSL
  have hPS : pCoreOf 2 (neX1 S L) ≤ S := hA1.twoCore_le
  have hL1Yh : perfectCore Yh ≤ Yh := perfectCore_le Yh
  have hL1X1 : perfectCore Yh ≤ neX1 S L := hL1Yh.trans (hY1.trans (neY_le_neX1 S L))
  have hL1L : perfectCore Yh ≤ L := hL1Yh.trans (hY1.trans (neY_le_left S L))
  have hL1X : perfectCore Yh ≤ X := hL1L.trans hLX
  have hcov : ∀ h ∈ Yh, ∃ l ∈ perfectCore Yh, ∃ r ∈ S ⊓ L, h = l * r := by
    intro h hh
    obtain ⟨d, hd, hdψ⟩ := exists_mem_perfectCore_of_surjective ψ hψs hQ'perf (ψ ⟨h, hh⟩)
    refine ⟨d, hd, (d : G)⁻¹ * h, ?_, by group⟩
    have h1 : d⁻¹ * (⟨h, hh⟩ : ↥Yh) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdψ, inv_mul_cancel]
    rw [hψk, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hL1N : perfectCore Yh ≤ Subgroup.normalizer (S : Set G) := by
    by_contra hnot
    let ψ₁ : ↥(perfectCore Yh) →* Q' := ψ.comp (Subgroup.inclusion hL1Yh)
    have hψ₁s : Function.Surjective ψ₁ := fun q => by
      obtain ⟨l, hl, hlq⟩ := exists_mem_perfectCore_of_surjective ψ hψs hQ'perf q
      exact ⟨⟨l, hl⟩, hlq⟩
    have hkerψ₁ : ψ₁.ker = (barIncl (neX1 S L) hL1X1).ker := by
      ext l
      rw [mem_ker_barIncl]
      constructor
      · intro h
        have h1 : Subgroup.inclusion hL1Yh l ∈ ψ.ker := h
        rw [hψk, Subgroup.mem_subgroupOf] at h1
        exact hRP h1
      · intro h
        have h2 : (l : G) ∈ S ⊓ L := ⟨hPS h, hL1L l.2⟩
        have h3 : Subgroup.inclusion hL1Yh l ∈ ψ.ker := by
          rw [hψk, Subgroup.mem_subgroupOf]; exact h2
        exact h3
    obtain ⟨e'⟩ := nonempty_mulEquiv_of_ker_eq (barIncl (neX1 S L) hL1X1).rangeRestrict ψ₁
      (MonoidHom.rangeRestrict_surjective _) hψ₁s
      (by rw [MonoidHom.ker_rangeRestrict]; exact hkerψ₁.symm)
    let e : ↥(barM (neX1 S L) (perfectCore Yh)) ≃* Q' :=
      (MulEquiv.subgroupCongr (range_barIncl hL1X1).symm).trans e'
    have hY1n : ((neY S L).subgroupOf (neX1 S L)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (neY_le_neX1 S L)).mpr
        (sup_le Subgroup.le_normalizer (le_normalizer_neY hSL))
    have hsub : IsSubnormal (perfectCore Yh) (neX1 S L) :=
      IsSubnormal.step hL1Yh (normal_perfectCore_subgroupOf Yh)
        (IsSubnormal.step hY1 hY3 (IsSubnormal.step (neY_le_neX1 S L) hY1n (IsSubnormal.refl _)))
    have hbsub : IsSubnormal (barM (neX1 S L) (perfectCore Yh)) ⊤ := by
      have := isSubnormal_barM hsub (le_refl (neX1 S L))
      rwa [barM_self] at this
    have hW : IsWeakSBlock (neX1 S L) S (perfectCore Yh) :=
      ⟨⟨hL1X1, hsub, perfectCore_perfect Yh,
        ⟨le_top, hbsub, open_isQuasisimple_of_mulEquiv e.symm
          (open_isQuasisimple_of_isQuasisimple hQ'qs)⟩⟩, hnot⟩
    have hcl : IsClassicalTwoOrG2 (↥(barM (neX1 S L) (perfectCore Yh)) ⧸
        Subgroup.center ↥(barM (neX1 S L) (perfectCore Yh))) :=
      CFSG.HardMathSupport.Cooperstein.Proving.isClassicalTwoOrG2_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center _) (Subgroup.center Q') e
          (Subgroup.map_center_eq e)).symm hQ'cl
    have hbot0 : barM (neX1 S L) (S ⊓ perfectCore Yh) = ⊥ := by
      rw [eq_bot_iff]
      intro γ hγ
      obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
      have hxP : (x : G) ∈ pCoreOf 2 (neX1 S L) := hRP ⟨hx.1, hL1L hx.2⟩
      obtain ⟨y, hy, hyx⟩ := mem_pCoreOf_iff.mp hxP
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hy)
    have hSO := hbot G (neX1 S L) S (perfectCore Yh) hX1 hA1 hW hcl hbot0
    have htr := eightEightTransvection G (neX1 S L) S (perfectCore Yh) hX1 hA1 hW hcl hSO
    have hcomm := commutator_pCore_le_blockV hX1 hA1 hW htr
    set T := pCoreOf 2 (perfectCore Yh ⊔ S) with hT
    have hLS : perfectCore Yh ⊔ S ≤ neX1 S L := sup_le hL1X1 (le_neX1 S L)
    have hQT : pCoreOf 2 X ≤ T :=
      normal_pGroup_le_pCoreOf 2 (pCoreOf 2 X) (perfectCore Yh ⊔ S) (hQS.trans le_sup_right)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hQS.trans le_sup_right)).mpr
          (fun g hg => localGroup_le_normalizer_pCoreOf 2 X (hX1X (hLS hg))))
        (pCoreOf_isPGroup 2 X)
    have hRT : S ⊓ L ≤ T :=
      normal_pGroup_le_pCoreOf 2 (S ⊓ L) (perfectCore Yh ⊔ S)
        (inf_le_left.trans le_sup_right)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans le_sup_right)).mpr
          (fun g hg => neX1_le_normalizer_inf hSL (hLS hg)))
        (hA.twoRadical.isPGroup.to_le inf_le_left)
    have hVQ : ∀ v ∈ omegaOneCenterOf T, v ∈ pCoreOf 2 X := by
      intro v hv
      have hvT : v ∈ T := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _ hv
      have hvX : v ∈ X := hX1X (hLS (pCoreOf_le 2 _ hvT))
      refine hA.charTwo ⟨hvX, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp
        (CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self T (hQT hq)) v hv
      exact this.symm
    have hcommQ : ∀ r ∈ S ⊓ L, ∀ l ∈ perfectCore Yh,
        l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 X := by
      intro r hr l hl
      have h1 := Subgroup.commutator_mem_commutator (hRT hr) hl
      rw [commutatorElement_def] at h1
      have h2 := hVQ _ (hcomm h1)
      have : l * r * l⁻¹ * r⁻¹ = (r * l * r⁻¹ * l⁻¹)⁻¹ := by group
      rw [this]
      exact (pCoreOf 2 X).inv_mem h2
    have hdec : ∀ k ∈ barM X (perfectCore Yh),
        k ∈ barM X (S ⊓ L) ⊔
          CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.centerIn (barM X L) := by
      intro k hk
      obtain ⟨x, hxL1, rfl⟩ := mem_barM_iff.mp hk
      refine hcent _ (barHom_mem_barM (hL1L hxL1)) (fun r hr => ?_)
      obtain ⟨z, hzR, rfl⟩ := mem_barM_iff.mp hr
      exact barHom_comm_iff.mpr (hcommQ (z : G) hzR (x : G) hxL1)
    have hbotL1 : barM X (perfectCore Yh) = ⊥ :=
      perfect_eq_bot_of_decomp (isPGroup_barM (hA.twoRadical.isPGroup.to_le inf_le_left))
        (barM_mono inf_le_right) (barM_perfect hL1X (perfectCore_perfect Yh)) hdec
    apply hnot
    intro l hl
    have hlX : l ∈ X := hL1X hl
    have h1 : barHom X ⟨l, hlX⟩ ∈ barM X (perfectCore Yh) := barHom_mem_barM hl
    rw [hbotL1, Subgroup.mem_bot] at h1
    have h2 : (⟨l, hlX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.le_normalizer (hQS (mem_pCoreOf_iff.mpr ⟨_, h2, rfl⟩))
  intro y hy
  obtain ⟨l, hl, r, hr, rfl⟩ := hcov y hy
  exact Subgroup.mul_mem _ (hL1N hl) (Subgroup.le_normalizer hr.1)

end CFSG.HardMathSupport.Cooperstein.StructureLie
