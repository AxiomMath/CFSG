module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBalMem
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFront
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairFinalAll
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHCl

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (LayerGenerationPairAt LayerGenerationHybrid
  LayerGenerationPairOr)
open CFSG.Open (IsSubnormal)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAtC_nt_of_hybrid {t : StatedLieTag} {k e : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hn : t = .PSL → 3 ≤ k) (hhyb : LayerGenerationHybrid p) :
    T5BaseAtC p f t k e Not := by
  intro hp2 hq hfund hadm hef H _ _ ψ hker R hR R' hR' eK eJ hne hcomm z hz hcl hzJ A hA hAKJ hzA
    hfaith
  have hef' : e = f := hef.resolve_right fun h => hD4 h.1
  subst hef'
  obtain ⟨x, x', hd⟩ := thm5IH_nt_front hG2 hD4 hp2 hq hfund hadm rfl ψ hker hR hR' eK eJ hcomm hz
    hzJ hA hAKJ
  have hA4 : Nat.card A = 4 := by simpa using hA.1
  have hf0 : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e hf0]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hopen := ModelFacts.isQuasisimple_modelUniv t k p e Fact.out hfund hadm
  have hperfK : Group.IsPerfect (modelUniv t k p e Fact.out).K := ⟨hopen.1⟩
  obtain ⟨hcen, hnorm, hcentY⟩ := FrameVertex.innerHom_spec ψ hker
  set L : Subgroup H := ψ.range with hL
  set π := FrameVertex.innerHom ψ with hπ
  have hπk : π.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K := fun g hg =>
    hcen g (MonoidHom.mem_ker.mp hg)
  have hAL : A ≤ L :=
    hAKJ.trans (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R'))
  have hLn : A ≤ Subgroup.normalizer (L : Set H) := fun a ha => Subgroup.le_normalizer (hAL ha)
  have hF : inducedImage L A = ((toInducedAutOn L).comp (Subgroup.inclusion hLn)).range :=
    thm5IH_inducedImage_eq_range hLn
  have hcardF : Nat.card (inducedImage L A) = 4 := thm5IH_card_inducedImage hLn hA4 hfaith
  set τ : ↥A →* ↥(inducedAutOn L) := (toInducedAutOn L).comp (Subgroup.inclusion hLn) with hτ
  have hFsq : ∀ g ∈ inducedImage L A, g * g = 1 := by
    intro g hg
    rw [hF] at hg
    obtain ⟨b, rfl⟩ := hg
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hA.2 b b.2)
    rw [this, map_one]
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hc := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hLn b.2) hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    exact hfaith b b.2 (fun h => hb1 (Subtype.ext h)) fun y hy => hc y hy
  have hne1 : ∀ (a : H) (ha : a ∈ A), a ≠ 1 → τ ⟨a, ha⟩ ≠ 1 := fun a ha ha1 h =>
    ha1 (congrArg Subtype.val (hτinj (h.trans (map_one τ).symm)))
  have hπτ : ∀ (a : H) (ha : a ∈ A) (y : (modelUniv t k p e Fact.out).K), ψ y = a →
      π y = τ ⟨a, ha⟩ := by
    intro a ha y h
    subst h
    rfl
  have hzz : z * z = 1 := hz.sq
  have htA : ψ x' ∈ A := by
    obtain ⟨u, huA, hu1, huz⟩ := thm5IH_exists_ne hA4 1 z
    rcases hd.elems u huA with h | h | h | h
    · exact absurd h hu1
    · exact absurd h huz
    · rw [← h]
      exact huA
    · have : ψ x' = z * u := by
        rw [h, ← mul_assoc, hzz, one_mul]
      rw [this]
      exact A.mul_mem hzA huA
  have hFelem : ∀ g ∈ inducedImage L A, g = 1 ∨ g = π x ∨ g = π x' ∨ g = π (x * x') := by
    intro g hg
    rw [hF] at hg
    obtain ⟨⟨a, ha⟩, rfl⟩ := hg
    rcases hd.elems a ha with h | h | h | h
    · left
      have : (⟨a, ha⟩ : ↥A) = 1 := Subtype.ext h
      rw [this, map_one]
    · right; left
      have : (⟨a, ha⟩ : ↥A) = ⟨z, hzA⟩ := Subtype.ext h
      rw [this]
      exact (hπτ z hzA x hd.map_x).symm
    · right; right; left
      have : (⟨a, ha⟩ : ↥A) = ⟨ψ x', htA⟩ := Subtype.ext h
      rw [this]
      exact (hπτ _ htA x' rfl).symm
    · right; right; right
      have : (⟨a, ha⟩ : ↥A) = ⟨z * ψ x', A.mul_mem hzA htA⟩ := Subtype.ext h
      rw [this]
      exact (hπτ _ (A.mul_mem hzA htA) (x * x') (by rw [map_mul, hd.map_x])).symm
  have hFR : inducedImage L A ≤ π.range := by
    intro g hg
    rcases hFelem g hg with h | h | h | h
    · rw [h]; exact π.range.one_mem
    · rw [h]; exact ⟨x, rfl⟩
    · rw [h]; exact ⟨x', rfl⟩
    · rw [h]; exact ⟨x * x', rfl⟩
  have hπx : π x ∈ inducedImage L A := by
    rw [hF]
    exact ⟨⟨z, hzA⟩, (hπτ z hzA x hd.map_x).symm⟩
  have hπx' : π x' ∈ inducedImage L A := by
    rw [hF]
    exact ⟨⟨ψ x', htA⟩, (hπτ _ htA x' rfl).symm⟩
  have hπx1 : π x ≠ 1 := by
    rw [hπτ z hzA x hd.map_x]
    exact hne1 z hzA hz.ne_one
  have hπx'1 : π x' ≠ 1 := by
    rw [hπτ _ htA x' rfl]
    exact hne1 _ htA hd.map_x'_ne_one
  have hπxx' : π x ≠ π x' := by
    rw [hπτ z hzA x hd.map_x, hπτ _ htA x' rfl]
    intro h
    exact hd.ne (congrArg Subtype.val (hτinj h))
  have hπ3 : π (x * x') ≠ 1 := by
    intro h
    apply hπxx'
    rw [map_mul] at h
    have h2 : π x' * π x' = 1 := by rw [← map_mul, hd.sq', map_one]
    calc π x = π x * (π x' * π x') := by rw [h2, mul_one]
      _ = (π x * π x') * π x' := by rw [mul_assoc]
      _ = π x' := by rw [h, one_mul]
  have hclπ : IsClassicalMember p e (R.map π) (π x) :=
    thm5IH_isClassicalMember_innerHom ψ hker hodd hcl rfl hd.map_x hπx1
  have hsingle := ModelFacts.fundamentalSingleClass t k p e Fact.out hfund hadm hG2 hD4
  have hmem : ∀ R'' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
      IsInvolutionMember (R''.map π) := by
    intro R'' hR''
    obtain ⟨g, hg⟩ := hsingle R hR R'' hR''
    have hcl'' := ModelFacts.isClassicalMember_map_conj hodd hclπ (π g)
    have h1 : R''.map π = (R.map π).map (MulAut.conj (π g)).toMonoidHom := by
      rw [hg]
      exact (conjSub_map π g R).symm
    rw [h1]
    exact hcl''.isInvolutionMember hq
  have hker_ne : π.ker ≠ ⊤ := by
    intro h
    exact hπx1 (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
  have hLq : CFSG.Open.IsQuasisimple ↥π.range :=
    CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hopen π hker_ne
  have hmodel := (ModelFacts.modelClauseZero t k p e Fact.out hfund hadm).2
  have hlie : IsOddLieComponent π.range :=
    isOddLieComponent_of_surjective hopen π.rangeRestrict π.rangeRestrict_surjective
      ⟨x, fun h => hπx1 (congrArg Subtype.val h)⟩ hp2 hn (isFundTag_mem_tags hfund) hmodel
  have hB := involutionCentralizerB_of_isOddLieComponent hLq hlie
  have : π.range.Normal := hnorm
  have hsubL : IsSubnormal π.range ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have hnormπ : ∀ g : ↥(inducedAutOn L),
      g ∈ Subgroup.normalizer (π.range : Set ↥(inducedAutOn L)) :=
    fun g => by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g
  have hlayer : ∀ R'' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
      ∀ g ∈ inducedImage L A, g ≠ 1 →
        R''.map π ≤ Subgroup.centralizer ({g} : Set ↥(inducedAutOn L)) →
          R''.map π ≤ centralizerLayer g := by
    intro R'' hR'' g hg hg1 hc
    exact (hmem R'' hR'').le_centralizerLayer l2PrimeBalance hsubL (Subgroup.map_le_range π R'')
      hc (hB g hg1 (hFsq g hg) (hnormπ g))
  have hcommR : ∀ r ∈ R, ∀ g ∈ inducedImage L A, π r * g = g * π r := by
    intro r hr g hg
    rcases hFelem g hg with h | h | h | h
    · rw [h, mul_one, one_mul]
    · rw [h, ← map_mul, ← map_mul, (hd.central r hr).symm]
    · rw [h, ← map_mul, ← map_mul, hd.comm_RR' r hr x' hd.mem']
    · rw [h, ← map_mul, ← map_mul]
      congr 1
      calc r * (x * x') = (r * x) * x' := by group
        _ = (x * r) * x' := by rw [← hd.central r hr]
        _ = x * (r * x') := by group
        _ = x * (x' * r) := by rw [hd.comm_RR' r hr x' hd.mem']
        _ = (x * x') * r := by group
  have hcommR' : ∀ r ∈ R', ∀ g ∈ inducedImage L A, π r * g = g * π r := by
    intro r hr g hg
    rcases hFelem g hg with h | h | h | h
    · rw [h, mul_one, one_mul]
    · rw [h, ← map_mul, ← map_mul, (hd.comm_RR' x hd.mem r hr).symm]
    · rw [h, ← map_mul, ← map_mul, (hd.central' r hr).symm]
    · rw [h, ← map_mul, ← map_mul]
      congr 1
      calc r * (x * x') = (r * x) * x' := by group
        _ = (x * r) * x' := by rw [hd.comm_RR' x hd.mem r hr]
        _ = x * (r * x') := by group
        _ = x * (x' * r) := by rw [← hd.central' r hr]
        _ = (x * x') * r := by group
  have hcentR : ∀ g ∈ inducedImage L A,
      R.map π ≤ Subgroup.centralizer ({g} : Set ↥(inducedAutOn L)) := by
    intro g hg
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommR r hr g hg)
  have hcentR' : ∀ g ∈ inducedImage L A,
      R'.map π ≤ Subgroup.centralizer ({g} : Set ↥(inducedAutOn L)) := by
    intro g hg
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommR' r hr g hg)
  have hπxx'F : π (x * x') ∈ inducedImage L A := by
    rw [map_mul]
    exact (inducedImage L A).mul_mem hπx hπx'
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd' b hb
    have hRa : R.map π ≤ centralizerLayer a := hlayer R hR a ha ha1 (hcentR a ha)
    have hR'a : R'.map π ≤ centralizerLayer a := hlayer R' hR' a ha ha1 (hcentR' a ha)
    have hbL : b ∈ centralizerLayer a := by
      rcases hFelem b hb with h | h | h | h
      · rw [h]
        exact (centralizerLayer a).one_mem
      · rw [h]
        exact hRa ⟨x, hd.mem, rfl⟩
      · rw [h]
        exact hR'a ⟨x', hd.mem', rfl⟩
      · rw [h, map_mul]
        exact (centralizerLayer a).mul_mem (hRa ⟨x, hd.mem, rfl⟩) (hR'a ⟨x', hd.mem', rfl⟩)
    have hcomm := commute_of_mem_involutionOddCore_of_mem_centralizerLayer hd' hbL
    rw [Subgroup.mem_bot, commutatorElement_def, hcomm]
    group
  · change deltaCore (inducedImage L A) = ⊥
    have hgen : π.range ≤ ⨆ g ∈ inducedImage L A, ⨆ (_ : g ≠ 1), centralizerLayer g := by
      rcases hhyb t k e hfund hadm hp2 hq with hPair | ⟨-, -, hCFG⟩
      · have hcomp : CFSG.IsComponent π.range :=
          ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hLq,
            hnorm.isSubnormal⟩
        exact hPair ↥(inducedAutOn L) π hπk hcomp R hR R' hR' (π x)
          (Subgroup.mem_map_of_mem π hd.mem) (π x') (Subgroup.mem_map_of_mem π hd.mem')
          (by
            rintro _ ⟨r, hr, rfl⟩
            rw [← map_mul, ← map_mul, hd.central r hr])
          (by
            rintro _ ⟨r, hr, rfl⟩
            rw [← map_mul, ← map_mul, hd.central' r hr])
          (by
            rintro _ ⟨r, hr, rfl⟩
            rw [← map_mul, ← map_mul, (hd.comm_RR' r hr x' hd.mem').symm])
          (by
            rintro _ ⟨r, hr, rfl⟩
            rw [← map_mul, ← map_mul, hd.comm_RR' x hd.mem r hr])
          (inducedImage L A) hcardF hFsq (by rw [Subgroup.normalizer_eq_top]; exact le_top)
          (fun g _ hg1 hall => hg1 (hcentY g hall)) (π x) hπx (π x') hπx' hπx1 hπx'1 hπxx'
          (fun y _ => rfl) (fun y _ => rfl)
      · have hgenS := hCFG R hR R' hR' x hd.mem x' hd.mem' hd.central hd.central'
          (fun r hr => (hd.comm_RR' r hr x' hd.mem').symm)
          (fun r hr => hd.comm_RR' x hd.mem r hr)
        have h1 : π.range ≤ ⨆ R'' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
            ⨆ (_ : R'' ≤ Subgroup.centralizer ({x} : Set (modelUniv t k p e Fact.out).K) ∨
              R'' ≤ Subgroup.centralizer ({x'} : Set (modelUniv t k p e Fact.out).K) ∨
              R'' ≤ Subgroup.centralizer ({x * x'} : Set (modelUniv t k p e Fact.out).K)),
              R''.map π := by
          have hr : π.range = (⊤ : Subgroup (modelUniv t k p e Fact.out).K).map π :=
            MonoidHom.range_eq_map π
          refine hr.le.trans ((Subgroup.map_mono hgenS).trans (le_of_eq ?_))
          simp only [Subgroup.map_iSup]
        refine h1.trans (iSup₂_le fun R'' hR'' => iSup_le fun hP => ?_)
        have hlift : ∀ c : (modelUniv t k p e Fact.out).K, π c ∈ inducedImage L A → π c ≠ 1 →
            R'' ≤ Subgroup.centralizer ({c} : Set (modelUniv t k p e Fact.out).K) →
              R''.map π ≤ ⨆ g ∈ inducedImage L A, ⨆ (_ : g ≠ 1), centralizerLayer g := by
          intro c hcF hc1 hc
          have hcen : R''.map π ≤ Subgroup.centralizer ({π c} : Set ↥(inducedAutOn L)) := by
            rintro _ ⟨r, hr, rfl⟩
            refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
            rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hc hr)]
          exact (hlayer R'' hR'' (π c) hcF hc1 hcen).trans
            (le_iSup₂_of_le (π c) hcF (le_iSup_of_le hc1 le_rfl))
        rcases hP with hP | hP | hP
        · exact hlift x hπx hπx1 hP
        · exact hlift x' hπx' hπx'1 hP
        · exact hlift (x * x') hπxx'F hπ3 hP
    rw [eq_bot_iff]
    intro d hd'
    rw [Subgroup.mem_bot]
    refine hcentY d fun r hr => ?_
    exact (Subgroup.mem_centralizer_iff.mp (deltaCore_le_centralizer_iSup_centralizerLayer _ hd')
      r (hgen hr)).symm

theorem t5BaseAtC_nt {t : StatedLieTag} {k e : ℕ} (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hn : t = .PSL → 3 ≤ k) : T5BaseAtC p f t k e Not :=
  t5BaseAtC_nt_of_hybrid hG2 hD4 hn (Balance.Bootstrap.layerGenerationHybrid p)

end CFSG.ClassicalInvolution.Asc77
