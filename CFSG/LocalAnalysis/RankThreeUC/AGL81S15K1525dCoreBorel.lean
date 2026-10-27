module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K1525dCoreProof

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Datum

variable (m : ℕ)

abbrev SLF2 : Type := Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2)

noncomputable abbrev dat : UniversalRootDatum (SLF2 m) := rootDatum m (ZMod 2)

noncomputable abbrev bor : Subgroup (SLF2 m) :=
  CFSG.LieType.Steinberg.borel (dat m) (torus m (ZMod 2))

noncomputable abbrev minPar (i : Fin m) : Subgroup (SLF2 m) :=
  parJ (dat m) (torus m (ZMod 2)) {i}

theorem eq_one_of_mem_torus {k : Fin m} {g : SLF2 m} (hg : g ∈ torus m (ZMod 2) k) : g = 1 := by
  have h := torus_pow_eq_one k hg
  have h1 : Nat.card (ZMod 2) - 1 = 1 := by rw [Nat.card_zmod]
  rwa [h1, pow_one] at h

theorem torus_eq_bot (k : Fin m) : torus m (ZMod 2) k = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_torus m hg)

theorem iSup_torus_eq_bot : (⨆ k, torus m (ZMod 2) k) = ⊥ := by
  simp [torus_eq_bot]

theorem bor_eq : bor m = posUnipotent (dat m) := by
  show (⨆ k, torus m (ZMod 2) k) ⊔ posUnipotent (dat m) = posUnipotent (dat m)
  rw [iSup_torus_eq_bot, bot_sup_eq]

theorem borelQuotient_id :
    BorelQuotient (dat m) (weylRep m (ZMod 2)) (torus m (ZMod 2))
      (MonoidHom.id (SLF2 m)) 1 where
  ct := isCTGroupDatum m (ZMod 2)
  extras := steinbergExtras m (ZMod 2)
  pGroup := fun γ hγ => isPGroup_of_isParametrization SL.isParametrization hγ
  surj := Function.surjective_id
  odd := odd_one
  torus_pow := fun k g hg => by
    rw [eq_one_of_mem_torus m hg, one_pow]
  ker_central := fun z hz => by
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
    rw [hz]
    exact Subgroup.one_mem _
  ker_pow := fun z hz => by
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
    rw [hz]
    exact one_pow 1

theorem isPGroup_posUnipotent : IsPGroup 2 (posUnipotent (dat m)) :=
  isPGroup_iSup_pos (steinbergExtras m (ZMod 2)) (borelQuotient_id m).pGroup

theorem isPGroup_bor : IsPGroup 2 (bor m) := by
  rw [bor_eq]
  exact isPGroup_posUnipotent m

theorem isSylowTwoOf_bor : CFSG.QuasithinUnique.IsSylowTwoOf (bor m) ⊤ := by
  refine ⟨le_top, isPGroup_bor m, ?_⟩
  have h1 : ((bor m).subgroupOf ⊤).index = (bor m).index := Subgroup.relIndex_top_right (bor m)
  rw [h1, bor_eq]
  exact (borelQuotient_id m).not_dvd_index

theorem normalizer_bor : Subgroup.normalizer (bor m : Set (SLF2 m)) = bor m := by
  have h : Subgroup.normalizer (posUnipotent (dat m) : Set (SLF2 m)) ≤ bor m :=
    CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel
      (isCTGroupDatum m (ZMod 2)) (steinbergExtras m (ZMod 2))
  refine le_antisymm ?_ Subgroup.le_normalizer
  rw [bor_eq] at h ⊢
  exact h

theorem isMinOverBorel_minPar (i : Fin m) : IsMinOverBorel ⊤ (bor m) (minPar m i) := by
  have hct := isCTGroupDatum m (ZMod 2)
  have hext := steinbergExtras m (ZMod 2)
  refine ⟨le_top, ?_, ?_⟩
  · rw [top_inf_eq, normalizer_bor]
    exact borel_lt_parJ hct hext (Set.singleton_nonempty i)
  · intro Q hQ1 hQ2
    rw [top_inf_eq, normalizer_bor] at hQ1 ⊢
    exact eq_borel_or_eq_parJ_singleton hct hext hQ1 hQ2

end Datum

theorem le_pElementSubgroup_of_isPGroup {G : Type*} [Group G] {X P : Subgroup G}
    (hX : IsPGroup 2 X) (hXP : X ≤ P) : X ≤ pElementSubgroup 2 P := by
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨hXP hx, ?_⟩
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
  exact ⟨j, hj⟩

variable (m : ℕ)

theorem bor_le_pElementSubgroup (i : Fin m) : bor m ≤ pElementSubgroup 2 (minPar m i) :=
  le_pElementSubgroup_of_isPGroup (isPGroup_bor m) (borel_le_parJ _)

theorem rankOne_le_pElementSubgroup (i : Fin m) :
    CFSG.LieType.CurtisTits.rankOne (dat m).rootGroup i ≤ pElementSubgroup 2 (minPar m i) := by
  have hle : CFSG.LieType.CurtisTits.rankOne (dat m).rootGroup i ≤ minPar m i :=
    rankOne_le_parJ (Set.mem_singleton i)
  have hα : (Pi.single i 1 : Fin (dat m).rank → ℤ) ∈ (dat m).roots :=
    (RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin (dat m).rank → ℤ) ∈ (dat m).roots :=
    (RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).neg_mem _ hα
  exact sup_le
    (le_pElementSubgroup_of_isPGroup ((borelQuotient_id m).pGroup _ hα) (le_sup_left.trans hle))
    (le_pElementSubgroup_of_isPGroup ((borelQuotient_id m).pGroup _ hα')
      (le_sup_right.trans hle))

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15
