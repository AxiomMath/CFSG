module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_apply_blockIdx
  blockMat_apply_of_not_mem_left blockIdx blockIdx_injective)
open scoped MatrixGroups

section Disjoint

variable {K : Type} [Field K] {m k l i j : ℕ}

theorem blockSL_disjoint (h₁ : i + k ≤ m) (h₂ : j + l ≤ m) (hij : i + k ≤ j) :
    Disjoint (blockSL K m k i h₁).range (blockSL K m l j h₂).range := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨A, rfl⟩ ⟨B, hB⟩
  have hA : A = 1 := by
    ext x y
    have := congrFun (congrFun (congrArg (fun g : SL(m, K) => (g : Matrix (Fin m) (Fin m) K)) hB)
      (blockIdx i h₁ x)) (blockIdx i h₁ y)
    rw [coe_blockSL, coe_blockSL, blockMat_apply_blockIdx,
      blockMat_apply_of_not_mem_left _ (by simp [blockIdx]; omega)] at this
    rw [Matrix.SpecialLinearGroup.coe_one]
    simp only [Matrix.one_apply, (blockIdx_injective h₁).eq_iff] at this ⊢
    exact this.symm
  rw [hA, map_one]

end Disjoint

section RankOne

variable {K : Type} [Field K] {n : ℕ}

theorem coe_blockSL2_transvection_up (i : Fin n) (c : K) :
    blockMat (n + 1) i.val (Matrix.transvection (0 : Fin 2) 1 c) =
      Matrix.transvection i.castSucc i.succ c := by
  ext a b
  rw [blockMat_apply]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem coe_blockSL2_transvection_down (i : Fin n) (c : K) :
    blockMat (n + 1) i.val (Matrix.transvection (1 : Fin 2) 0 c) =
      Matrix.transvection i.succ i.castSucc c := by
  ext a b
  rw [blockMat_apply]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

theorem blockSL2_transvection_up (i : Fin n) (c : K) :
    blockSL2 K n i (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      Matrix.SpecialLinearGroup.transvection
        (show i.castSucc ≠ i.succ from Fin.castSucc_lt_succ.ne) c :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.transvection_coe, ← Matrix.transvection]
    exact coe_blockSL2_transvection_up i c)

theorem blockSL2_transvection_down (i : Fin n) (c : K) :
    blockSL2 K n i (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      Matrix.SpecialLinearGroup.transvection
        (show i.succ ≠ i.castSucc from Fin.castSucc_lt_succ.ne') c :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.transvection_coe, ← Matrix.transvection]
    exact coe_blockSL2_transvection_down i c)

theorem rankOne_eq_range (i : Fin n) :
    rankOne (rootGroup n K) i = (blockSL2 K n i).range := by
  rw [rankOne_rootGroup]
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ g).mp hg
    exact ⟨_, blockSL2_transvection_up i c⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ g).mp hg
    exact ⟨_, blockSL2_transvection_down i c⟩
  · rw [MonoidHom.range_eq_map, ← iSup_fundamentalRootSubgroup_eq_top (m := 1) (F := K),
      Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    obtain rfl : k = 0 := Subsingleton.elim _ _
    cases s
    · refine le_sup_of_le_right ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ x).mp hx
      exact (mem_rootSubgroup _ _).mpr ⟨c, (blockSL2_transvection_down i c).symm⟩
    · refine le_sup_of_le_left ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ x).mp hx
      exact (mem_rootSubgroup _ _).mpr ⟨c, (blockSL2_transvection_up i c).symm⟩

theorem blockSL2_mem_levi {J : Finset (Fin n)} {i : Fin n} (hi : i ∈ J) (A : SL(2, K)) :
    blockSL2 K n i A ∈ levi (rootGroup n K) J :=
  rankOne_le_levi _ hi (by rw [rankOne_eq_range]; exact ⟨A, rfl⟩)

theorem levi_pair (i j : Fin n) :
    levi (rootGroup n K) {i, j} = (blockSL2 K n i).range ⊔ (blockSL2 K n j).range := by
  rw [← rankOne_eq_range, ← rankOne_eq_range, ← levi_singleton, ← levi_singleton]
  simp only [CFSG.LieType.CurtisTits.levi, Finset.iSup_insert, Finset.iSup_singleton]

end RankOne

section Hom

variable {K : Type} [Field K] {n : ℕ}

theorem exists_hom_of_le_range {S G Y : Type*} [Group S] [Group G] [Group Y] (E : S →* G)
    (hE : Function.Injective E) (Φ : S →* Y) (T : Subgroup G) (hT : T ≤ E.range) :
    ∃ φ : T →* Y, ∀ (x : T) (s : S), (x : G) = E s → φ x = Φ s := by
  refine ⟨Φ.comp ((MonoidHom.ofInjective hE).symm.toMonoidHom.comp (Subgroup.inclusion hT)),
    fun x s hxs => ?_⟩
  have : Subgroup.inclusion hT x = MonoidHom.ofInjective hE s := Subtype.ext hxs
  simp [this]

theorem levi_hom_ext {Y : Type*} [Group Y] (I : Finset (Fin n))
    (φ₁ φ₂ : levi (rootGroup n K) I →* Y)
    (h : ∀ i ∈ I, ∀ (x : levi (rootGroup n K) I) (A : SL(2, K)),
      (x : SL(n + 1, K)) = blockSL2 K n i A → φ₁ x = φ₂ x) : φ₁ = φ₂ := by
  have hle : levi (rootGroup n K) I ≤
      (MonoidHom.eqLocus φ₁ φ₂).map (levi (rootGroup n K) I).subtype := by
    refine iSup₂_le fun i hi => ?_
    rw [rankOne_eq_range]
    rintro _ ⟨A, rfl⟩
    exact ⟨⟨_, blockSL2_mem_levi hi A⟩, h i hi ⟨_, blockSL2_mem_levi hi A⟩ A rfl, rfl⟩
  ext ⟨x, hx⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = ⟨x, hx⟩ := Subtype.ext hyx
  subst this
  exact hy

variable {Y : Type} [Group Y]

theorem exists_levi_hom_far (F : CTFamily K Y n) (i j : Fin n) (hij : (i : ℕ) + 1 < j) :
    ∃ φ : levi (rootGroup n K) {i, j} →* Y,
      ∀ k ∈ ({i, j} : Finset (Fin n)), ∀ (x : levi (rootGroup n K) {i, j}) (A : SL(2, K)),
        (x : SL(n + 1, K)) = blockSL2 K n k A → φ x = F.ι k A := by
  have hcomm : ∀ (a b : SL(2, K)), Commute (blockSL2 K n i a) (blockSL2 K n j b) :=
    fun a b => blockSL2_comm n i j hij a b
  have hdisj : Disjoint (blockSL2 K n i).range (blockSL2 K n j).range :=
    blockSL_disjoint _ _ (by omega)
  have hinj : Function.Injective ((blockSL2 K n i).noncommCoprod (blockSL2 K n j) hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).2
      ⟨blockSL2_injective n i, blockSL2_injective n j, hdisj⟩
  have hcomm' : ∀ (a b : SL(2, K)), Commute (F.ι i a) (F.ι j b) :=
    fun a b => F.comm i j hij a b
  obtain ⟨φ, hφ⟩ := exists_hom_of_le_range _ hinj ((F.ι i).noncommCoprod (F.ι j) hcomm')
    (levi (rootGroup n K) {i, j})
    (by rw [levi_pair, MonoidHom.noncommCoprod_range])
  refine ⟨φ, fun k hk x A hx => ?_⟩
  rcases Finset.mem_insert.mp hk with rfl | hk
  · have := hφ x (A, 1) (by rw [hx, MonoidHom.noncommCoprod_apply]; simp)
    rw [this, MonoidHom.noncommCoprod_apply]
    simp
  · obtain rfl := Finset.mem_singleton.mp hk
    have := hφ x (1, A) (by rw [hx, MonoidHom.noncommCoprod_apply]; simp)
    rw [this, MonoidHom.noncommCoprod_apply]
    simp

theorem exists_levi_hom_adj (F : CTFamily K Y n) (i j : Fin n) (hj : (j : ℕ) = i + 1) :
    ∃ φ : levi (rootGroup n K) {i, j} →* Y,
      ∀ k ∈ ({i, j} : Finset (Fin n)), ∀ (x : levi (rootGroup n K) {i, j}) (A : SL(2, K)),
        (x : SL(n + 1, K)) = blockSL2 K n k A → φ x = F.ι k A := by
  have hi : (i : ℕ) + 1 < n := by have := j.isLt; omega
  obtain rfl : j = ⟨i + 1, hi⟩ := Fin.ext hj
  obtain ⟨φ, hφ⟩ := exists_hom_of_le_range (blockSL3 K n i hi) (blockSL3_injective n i hi) (F.θ i)
    (levi (rootGroup n K) {i, ⟨i + 1, hi⟩}) (by
      rw [levi_pair]
      refine sup_le ?_ ?_
      · rw [← blockSL3_comp_left n i hi, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _
      · rw [← blockSL3_comp_right n i hi, MonoidHom.range_comp]
        exact Subgroup.map_le_range _ _)
  refine ⟨φ, fun k hk x A hx => ?_⟩
  rcases Finset.mem_insert.mp hk with rfl | hk
  · have := hφ x (blockSL K 3 2 0 (by omega) A) (by
      rw [hx, ← blockSL3_comp_left n k hi]
      rfl)
    rw [this, ← F.left k hi]
    rfl
  · obtain rfl := Finset.mem_singleton.mp hk
    have := hφ x (blockSL K 3 2 1 (by omega) A) (by
      rw [hx, ← blockSL3_comp_right n i hi]
      rfl)
    rw [this, ← F.right i hi]
    rfl

theorem exists_levi_hom (F : CTFamily K Y n) (J : Finset (Fin n)) (hJ : J.card ≤ 2) :
    ∃ φ : levi (rootGroup n K) J →* Y,
      ∀ k ∈ J, ∀ (x : levi (rootGroup n K) J) (A : SL(2, K)),
        (x : SL(n + 1, K)) = blockSL2 K n k A → φ x = F.ι k A := by
  interval_cases hc : J.card
  · obtain rfl := Finset.card_eq_zero.mp hc
    exact ⟨1, by simp⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    obtain ⟨φ, hφ⟩ := exists_hom_of_le_range (blockSL2 K n a) (blockSL2_injective n a) (F.ι a)
      (levi (rootGroup n K) {a}) (by rw [levi_singleton, rankOne_eq_range])
    refine ⟨φ, fun k hk x A hx => ?_⟩
    obtain rfl := Finset.mem_singleton.mp hk
    exact hφ x A hx
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    rcases lt_or_gt_of_ne hab with h | h
    · by_cases hadj : (b : ℕ) = a + 1
      · exact exists_levi_hom_adj F a b hadj
      · exact exists_levi_hom_far F a b (by have := Fin.lt_def.mp h; omega)
    · rw [Finset.pair_comm]
      by_cases hadj : (a : ℕ) = b + 1
      · exact exists_levi_hom_adj F b a hadj
      · exact exists_levi_hom_far F b a (by have := Fin.lt_def.mp h; omega)

theorem exists_compatible_family (F : CTFamily K Y n) :
    ∃ φ : ∀ J : {J : Finset (Fin n) // J.card ≤ 2}, levi (rootGroup n K) J.1 →* Y,
      IsCompatible (leviAmalgam (rootGroup n K)) φ ∧
      ∀ (J : {J : Finset (Fin n) // J.card ≤ 2}), ∀ k ∈ J.1,
        ∀ (x : levi (rootGroup n K) J.1) (A : SL(2, K)),
          (x : SL(n + 1, K)) = blockSL2 K n k A → φ J x = F.ι k A := by
  choose φ hφ using fun J : {J : Finset (Fin n) // J.card ≤ 2} => exists_levi_hom F J.1 J.2
  refine ⟨φ, ?_, hφ⟩
  intro I J hIJ x y hxy
  have hIJ' : I.1 ⊆ J.1 := hIJ
  have hfun : φ I = (φ J).comp (Subgroup.inclusion (levi_mono (rootGroup n K) hIJ')) :=
    levi_hom_ext I.1 _ _ fun k hk x A hx => by
      rw [hφ I k hk x A hx, MonoidHom.comp_apply]
      exact (hφ J k (hIJ hk) _ A (by rw [Subgroup.coe_inclusion]; exact hx)).symm
  have hy : Subgroup.inclusion (levi_mono (rootGroup n K) hIJ') x = y :=
    Subtype.ext (by rw [Subgroup.coe_inclusion]; exact hxy)
  rw [DFunLike.congr_fun hfun x, MonoidHom.comp_apply, hy]

end Hom

section Recognition

variable {K : Type} [Field K] {n : ℕ} {Y : Type} [Group Y]

theorem exists_recognition [Finite K] (hn : 3 ≤ n) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (F : CTFamily K Y n) (hgen : ⨆ i, (F.ι i).range = ⊤)
    (hnt : ∃ i, ∃ A, F.ι i A ≠ 1) :
    ∃ ψ : SL(n + 1, K) →* Y, (∀ i A, ψ (blockSL2 K n i A) = F.ι i A) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center SL(n + 1, K) ∧ CFSG.IsQuasisimple Y ∧
      Nonempty (SL(n + 1, K) ⧸ ψ.ker ≃* Y) ∧
      CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible
      CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f :=
    ⟨hp, hf, by omega, fun h => by have := congrArg Prod.fst h; simp at this; omega,
      fun h => by have := congrArg Prod.fst h; simp at this; omega⟩
  have hct := curtisTitsConclusion_specialLinear.{0} hadm hK hn
  obtain ⟨φ, hφc, hφ⟩ := exists_compatible_family F
  have hmem : ∀ (i : Fin n) (A : SL(2, K)),
      blockSL2 K n i A ∈ levi (rootGroup n K) ({i} : Finset (Fin n)) :=
    fun i A => blockSL2_mem_levi (Finset.mem_singleton_self i) A
  have hφi : ∀ (i : Fin n) (A : SL(2, K)),
      φ ⟨{i}, by simp⟩ ⟨blockSL2 K n i A, hmem i A⟩ = F.ι i A :=
    fun i A => hφ ⟨{i}, by simp⟩ i (Finset.mem_singleton_self i) _ A rfl
  have hgen' : ⨆ J, (φ J).range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun i => ?_
    rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_iSup_of_mem ⟨{i}, by simp⟩ ⟨⟨blockSL2 K n i A, hmem i A⟩, hφi i A⟩
  have hnt' : ∃ J, ∃ x, φ J x ≠ 1 := by
    obtain ⟨i, A, hA⟩ := hnt
    exact ⟨⟨{i}, by simp⟩, ⟨blockSL2 K n i A, hmem i A⟩, by rw [hφi]; exact hA⟩
  obtain ⟨ψ, hψ, hsurj, hker, hq, -, hiso, hmodel⟩ := hct.2.2.1 Y φ hφc hgen' hnt'
  have hψ' : ∀ (J : {J : Finset (Fin n) // J.card ≤ 2}) (x : levi (rootGroup n K) J.1),
      ψ x = φ J x := hψ
  exact ⟨ψ, fun i A => (hψ' ⟨{i}, by simp⟩ ⟨blockSL2 K n i A, hmem i A⟩).trans (hφi i A), hsurj,
    hker, hq, hiso, hmodel⟩

end Recognition

end CFSG.ClassicalInvolution.WeakCT
