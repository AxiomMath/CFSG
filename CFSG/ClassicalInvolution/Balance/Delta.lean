module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.SignalizerFunctorTheorem.Assembly
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.SignalizerFunctorTheorem CFSG.Assembly.Dichotomy

section Definitions

variable {G : Type*} [Group G]

@[expose] def deltaCore (D : Subgroup G) : Subgroup G :=
  ⨅ d ∈ D, ⨅ (_ : d ≠ 1), involutionOddCore d

@[expose] def TwoBalancedWrt (A : Subgroup G) : Prop :=
  ∀ F ∈ signalizerFunctorEk 2 2 A, ∀ a ∈ A, a ≠ 1 →
    deltaCore F ⊓ Subgroup.centralizer {a} ≤ involutionOddCore a

theorem mem_deltaCore_iff {D : Subgroup G} {x : G} :
    x ∈ deltaCore D ↔ ∀ d ∈ D, d ≠ 1 → x ∈ involutionOddCore d := by
  simp only [deltaCore, Subgroup.mem_iInf]

theorem deltaCore_le_involutionOddCore {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    deltaCore D ≤ involutionOddCore d :=
  fun _ hx => mem_deltaCore_iff.mp hx d hd hd1

theorem le_deltaCore {D X : Subgroup G} (h : ∀ d ∈ D, d ≠ 1 → X ≤ involutionOddCore d) :
    X ≤ deltaCore D :=
  fun _ hx => mem_deltaCore_iff.mpr fun d hd hd1 => h d hd hd1 hx

theorem involutionOddCore_le_centralizer (a : G) :
    involutionOddCore a ≤ Subgroup.centralizer {a} :=
  Subgroup.map_subtype_le _

theorem deltaCore_le_centralizer (D : Subgroup G) :
    deltaCore D ≤ Subgroup.centralizer (D : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  by_cases hd1 : d = 1
  · simp [hd1]
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer d (mem_deltaCore_iff.mp hx d hd hd1))).symm

theorem odd_card_deltaCore [Finite G] {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    Odd (Nat.card (deltaCore D)) :=
  (odd_card_oddCoreIn (Subgroup.centralizer {d})).of_dvd_nat
    (Subgroup.card_dvd_of_le (deltaCore_le_involutionOddCore hd hd1))

theorem exists_ne_one_of_card_eq_two_pow [Finite G] {S : Subgroup G} {n : ℕ} (hn : n ≠ 0)
    (hS : Nat.card S = 2 ^ n) : ∃ s ∈ S, s ≠ 1 := by
  by_contra h
  have hbot : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr fun s hs => by
    by_contra hne
    exact h ⟨s, hs, hne⟩
  rw [hbot, Subgroup.card_bot] at hS
  have : 1 < 2 ^ n := Nat.one_lt_two_pow hn
  omega

theorem conj_mem_deltaCore {D : Subgroup G} {x y : G} (hx : ∀ d ∈ D, x * d = d * x)
    (hy : y ∈ deltaCore D) : x * y * x⁻¹ ∈ deltaCore D := by
  rw [mem_deltaCore_iff] at hy ⊢
  intro d hd hd1
  refine conj_mem_oddCoreIn (X := Subgroup.centralizer {d}) ?_ (hy d hd hd1)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hx d hd)

theorem normalizer_deltaCore {A D : Subgroup G} (hA : IsMulCommutative A) (hDA : D ≤ A) :
    A ≤ Subgroup.normalizer (deltaCore D : Set G) := by
  intro x hx
  have hcomm : ∀ z ∈ A, ∀ d ∈ D, z * d = d * z := fun z hz d hd =>
    congrArg Subtype.val (hA.is_comm.comm (⟨z, hz⟩ : A) ⟨d, hDA hd⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_deltaCore (hcomm x hx) hy, fun hy => ?_⟩
  have := conj_mem_deltaCore (hcomm x⁻¹ (inv_mem hx)) hy
  simpa [mul_assoc] using this

theorem deltaCore_map (g : G) (D : Subgroup G) :
    (deltaCore D).map (MulAut.conj g).toMonoidHom =
      deltaCore (D.map (MulAut.conj g).toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv (f := MulAut.conj g), mem_deltaCore_iff, mem_deltaCore_iff]
  have key : ∀ d : G, (MulAut.conj g).symm x ∈ involutionOddCore d ↔
      x ∈ involutionOddCore ((MulAut.conj g) d) := fun d => by
    rw [← involutionOddCore_map (MulAut.conj g) d, Subgroup.mem_map_equiv]
  constructor
  · intro h d' hd' hd'1
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hd'
    exact (key d).mp (h d hd fun h1 => hd'1 (by simp [h1]))
  · intro h d hd hd1
    refine (key d).mpr (h _ (Subgroup.mem_map_of_mem _ hd) fun h1 => hd1 ?_)
    exact (MulAut.conj g).injective (by simpa using h1)

end Definitions

section SignalizerFunctor

variable {G : Type*} [Group G] [Finite G]

theorem deltaCore_isSignalizerFunctor {A : Subgroup G} (hA : IsMulCommutative A)
    (hB : TwoBalancedWrt A) : IsSignalizerFunctor 2 2 A deltaCore where
  central S _ := deltaCore_le_centralizer S
  coprime S hS := by
    obtain ⟨d, hd, hd1⟩ := exists_ne_one_of_card_eq_two_pow (by norm_num) hS.2
    exact Nat.coprime_two_left.mpr (odd_card_deltaCore hd hd1)
  normalized S hS := normalizer_deltaCore hA hS.1
  balanced S hS S' hS' := by
    refine le_deltaCore fun d hd hd1 => ?_
    refine le_trans (inf_le_inf_left _ ?_) (hB S hS d (hS'.1 hd) hd1)
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hd)

end SignalizerFunctor

section Completion

variable {G : Type} [Group G] [Finite G]

theorem isComplete_deltaCore {A : Subgroup G} (hA : IsElemAbelian 2 A) (h16 : 16 ≤ Nat.card A)
    (hB : TwoBalancedWrt A) :
    IsComplete 2 2 A deltaCore ∧ Group.IsSolvable (completion 2 2 A deltaCore) := by
  have hΘ := deltaCore_isSignalizerFunctor hA.1 hB
  have hsolv : ∀ S ∈ signalizerFunctorEk 2 2 A, Group.IsSolvable (deltaCore S) := fun S hS => by
    obtain ⟨d, hd, hd1⟩ := exists_ne_one_of_card_eq_two_pow (by norm_num) hS.2
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_deltaCore hd hd1)
  exact isComplete_of_rankOneOracle Nat.prime_two hA
    (solvable_oracle
      (Solvable.solvableRankOneTheoremAt_of_le_three 2 Nat.prime_two (by norm_num)) hA)
    2 (by norm_num) (by simpa using h16) deltaCore hΘ hsolv

theorem completion_eq_iSup_of_mem_E3 {A A₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A) (hA₀ : A₀ ∈ signalizerFunctorEk 2 3 A) :
    completion 2 2 A deltaCore = ⨆ F ∈ signalizerFunctorEk 2 2 A₀, deltaCore F := by
  obtain ⟨⟨hcop, hcent⟩, -⟩ := isComplete_deltaCore hA h16 hB
  have hΘ := deltaCore_isSignalizerFunctor hA.1 hB
  have hA₀elem : IsElemAbelian 2 A₀ :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hA₀.1
  have hnorm : A₀ ≤ Subgroup.normalizer (completion 2 2 A deltaCore : Set G) :=
    hA₀.1.trans (le_normalizer_completion hΘ.normalized)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A₀ (completion 2 2 A deltaCore) hA₀elem (by rw [hA₀.2]) hnorm hcop
  apply le_antisymm
  · refine hgen.symm.le.trans (iSup₂_le fun F hF => ?_)
    rw [hcent F (mem_Ek_of_le hA₀.1 hF)]
    exact le_iSup₂_of_le F hF le_rfl
  · exact iSup₂_le fun F hF => le_completion (mem_Ek_of_le hA₀.1 hF)

theorem completion_eq_of_mem_E3 {A A' A₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A) (hA' : IsElemAbelian 2 A')
    (h16' : 16 ≤ Nat.card A') (hB' : TwoBalancedWrt A') (hA₀ : A₀ ∈ signalizerFunctorEk 2 3 A)
    (hA₀' : A₀ ∈ signalizerFunctorEk 2 3 A') :
    completion 2 2 A deltaCore = completion 2 2 A' deltaCore :=
  (completion_eq_iSup_of_mem_E3 hA h16 hB hA₀).trans
    (completion_eq_iSup_of_mem_E3 hA' h16' hB' hA₀').symm

theorem map_conj_completion_le {A A₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A) (hA₀ : A₀ ∈ signalizerFunctorEk 2 3 A)
    {g : G} (hg : A₀.map (MulAut.conj g).toMonoidHom ≤ A) :
    (completion 2 2 A deltaCore).map (MulAut.conj g).toMonoidHom ≤ completion 2 2 A deltaCore := by
  have heq := completion_eq_iSup_of_mem_E3 hA h16 hB hA₀
  refine le_trans (le_of_eq (congrArg (Subgroup.map _) heq)) ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun F => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hF => ?_
  rw [deltaCore_map]
  refine le_completion ⟨le_trans (Subgroup.map_mono hF.1) hg, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hF.2

theorem mem_normalizer_completion_of_map_le {A A₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A) (hA₀ : A₀ ∈ signalizerFunctorEk 2 3 A)
    {g : G} (hg : A₀.map (MulAut.conj g).toMonoidHom ≤ A) :
    g ∈ Subgroup.normalizer (completion 2 2 A deltaCore : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge (map_conj_completion_le hA h16 hB hA₀ hg)
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem centralizer_le_normalizer_completion {A A₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A) (hA₀ : A₀ ∈ signalizerFunctorEk 2 3 A) :
    Subgroup.centralizer (A₀ : Set G) ≤
      Subgroup.normalizer (completion 2 2 A deltaCore : Set G) := by
  intro g hg
  refine mem_normalizer_completion_of_map_le hA h16 hB hA₀ ?_
  rintro _ ⟨x, hx, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hg x hx
  have : (MulAut.conj g).toMonoidHom x = x := by
    change g * x * g⁻¹ = x
    rw [← hcomm]
    group
  rw [this]
  exact hA₀.1 hx

theorem normalizer_le_normalizer_completion {A A₀ : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A) (hA₀ : A₀ ∈ signalizerFunctorEk 2 3 A) :
    Subgroup.normalizer (A₀ : Set G) ≤
      Subgroup.normalizer (completion 2 2 A deltaCore : Set G) := by
  intro g hg
  refine mem_normalizer_completion_of_map_le hA h16 hB hA₀ ?_
  exact (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)).trans hA₀.1

end Completion

section DeltaTriviality

variable {G : Type*} [Group G]

@[expose] def FusionGenerated (A : Subgroup G) : Prop :=
  Subgroup.closure {g : G | ∃ A₀ ∈ signalizerFunctorEk 2 3 A,
    A₀.map (MulAut.conj g).toMonoidHom ≤ A} = ⊤

theorem fusionGenerated_of_centralizer_generated {A : Subgroup G}
    (h : (⨆ E₀ ∈ signalizerFunctorEk 2 3 A, Subgroup.centralizer (E₀ : Set G)) = ⊤) :
    FusionGenerated A := by
  refine top_unique ?_
  rw [← h]
  refine iSup₂_le fun E₀ hE₀ g hg => ?_
  refine Subgroup.subset_closure ⟨E₀, hE₀, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hg x hx
  have : (MulAut.conj g).toMonoidHom x = x := by
    change g * x * g⁻¹ = x
    rw [← hcomm]
    group
  rw [this]
  exact hE₀.1 hx

end DeltaTriviality

section DeltaTrivial

variable {G : Type} [Group G] [Finite G]

theorem deltaCore_eq_bot_of_fusionGenerated {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A)
    (hO : componentClassificationOddCore G = ⊥) (hGen : FusionGenerated A) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  obtain ⟨⟨hcop, -⟩, -⟩ := isComplete_deltaCore hA h16 hB
  have hnormal : (completion 2 2 A deltaCore).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hGen, Subgroup.closure_le]
    rintro g ⟨A₀, hA₀, hg⟩
    exact mem_normalizer_completion_of_map_le hA h16 hB hA₀ hg
  have hodd : Odd (Nat.card (completion 2 2 A deltaCore)) := Nat.coprime_two_left.mp hcop
  have hle : completion 2 2 A deltaCore ≤ componentClassificationOddCore G :=
    CFSG.ComponentClassification.OddCore.maximal G _ hnormal hodd
  rw [hO] at hle
  intro F hF
  exact le_bot_iff.mp ((le_completion hF).trans hle)

theorem deltaCore_eq_bot_of_centralizer_generated {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (h16 : 16 ≤ Nat.card A) (hB : TwoBalancedWrt A)
    (hO : componentClassificationOddCore G = ⊥)
    (hGen : (⨆ E₀ ∈ signalizerFunctorEk 2 3 A, Subgroup.centralizer (E₀ : Set G)) = ⊤) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ :=
  deltaCore_eq_bot_of_fusionGenerated hA h16 hB hO (fusionGenerated_of_centralizer_generated hGen)

end DeltaTrivial

section BalanceEight

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem zpowers_eq_one_or_self_delta {z g : G} (hz2 : z * z = 1)
    (h : g ∈ Subgroup.zpowers z) : g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]

theorem twoBalancedWrt_of_eight
    {S A : Subgroup G} (hAe : CFSG.Open.IsElemAbelian 2 A) (hAS : A ≤ S)
    (hbal : ∀ V : Subgroup G, V ≤ S → CFSG.Open.IsElemAbelian 2 V →
      Nat.card V = 8 → TwoBalancedWrt V) :
    TwoBalancedWrt A := by
  intro F hF a haA ha1
  obtain ⟨hFA, hFcard⟩ := hF
  by_cases haF : a ∈ F
  · exact inf_le_left.trans (deltaCore_le_involutionOddCore haF ha1)
  · have hFe : CFSG.Open.IsElemAbelian 2 F := hAe.mono hFA
    have hcomm : a ∈ centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val
        (hAe.1.is_comm.comm ⟨f, hFA hf⟩ ⟨a, haA⟩)
    have ha2 : a ^ 2 = 1 := hAe.2 a haA
    have haord : orderOf a = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using ha2) ha1
    have hdisj : Disjoint F (Subgroup.zpowers a) := by
      rw [Subgroup.disjoint_def]
      intro x hxF hxZ
      rcases zpowers_eq_one_or_self_delta (by simpa [pow_two] using ha2) hxZ with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hxF) haF
    have hPa : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers a) :=
      CFSG.Open.isElemAbelian_zpowers (p := 2) ha2
    have hzle : Subgroup.zpowers a ≤ Subgroup.centralizer (F : Set G) :=
      Subgroup.zpowers_le.mpr hcomm
    have hcardV : Nat.card (F ⊔ Subgroup.zpowers a : Subgroup G) = 8 := by
      have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (F : Set G) :=
        hzle.trans (Subgroup.centralizer_le_normalizer (F : Set G))
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (A := F) (B := Subgroup.zpowers a) hnorm hdisj
      rw [hFcard, Nat.card_zpowers, haord] at hcard
      simpa using hcard
    have hcomm' : ∀ x ∈ F, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
      intro x hx y hy
      exact Subgroup.mem_centralizer_iff.mp (hzle hy) x hx
    have hVe : CFSG.Open.IsElemAbelian 2 (F ⊔ Subgroup.zpowers a) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hFe hPa hcomm'
    have hVS : F ⊔ Subgroup.zpowers a ≤ S :=
      sup_le (hFA.trans hAS) (Subgroup.zpowers_le.mpr (hAS haA))
    have haV : a ∈ F ⊔ Subgroup.zpowers a :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    exact hbal (F ⊔ Subgroup.zpowers a) hVS hVe hcardV F ⟨le_sup_left, hFcard⟩ a haV ha1

end BalanceEight

end CFSG.ClassicalInvolution.Balance
