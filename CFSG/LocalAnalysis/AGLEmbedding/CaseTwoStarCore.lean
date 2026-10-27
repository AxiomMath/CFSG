module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {X : Type*} [Group X] [Finite X]

abbrev conjSub (g : X) (K : Subgroup X) : Subgroup X := K.map (MulAut.conj g).toMonoidHom

omit [Finite X] in
theorem conjSub_mul (g h : X) (K : Subgroup X) :
    conjSub (g * h) K = conjSub g (conjSub h K) := by
  rw [conjSub, conjSub, conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite X] in
theorem conjSub_one (K : Subgroup X) : conjSub 1 K = K := by
  ext x
  simp [conjSub]

omit [Finite X] in
theorem conjSub_injective (g : X) {K L : Subgroup X} (h : conjSub g K = conjSub g L) : K = L := by
  have := congrArg (conjSub g⁻¹) h
  simpa only [← conjSub_mul, inv_mul_cancel, conjSub_one] using this

omit [Finite X] in
theorem conjSub_eq_iff (g : X) (K : Subgroup X) :
    conjSub g K = K ↔ g ∈ Subgroup.normalizer (K : Set X) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        simpa [MulAut.conj_apply] using hyx
      rwa [← this]
  · intro hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa [mul_assoc] using this

omit [Finite X] in
theorem isComponentOf_conjSub (g : X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsComponentOf (conjSub g K) ⊤ :=
  (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK

omit [Finite X] in
theorem le_normalizer_of_perfect
    (hthree : ∀ L₁ L₂ L₃ : Subgroup X, IsComponentOf L₁ ⊤ → IsComponentOf L₂ ⊤ →
      IsComponentOf L₃ ⊤ → L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → False)
    {W : Subgroup X} (hW : ⁅W, W⁆ = W) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    W ≤ Subgroup.normalizer (K : Set X) := by
  by_contra hnot
  obtain ⟨w₀, hw₀W, hw₀N⟩ := Set.not_subset.mp hnot
  set K' := conjSub w₀ K with hK'
  have hKK' : K ≠ K' := fun h => hw₀N ((conjSub_eq_iff w₀ K).mp h.symm)
  have hK'c : IsComponentOf K' ⊤ := isComponentOf_conjSub w₀ hK
  have hdich : ∀ g ∈ W, conjSub g K = K ∨ conjSub g K = K' := by
    intro g _
    by_contra h
    push Not at h
    exact hthree K K' (conjSub g K) hK hK'c (isComponentOf_conjSub g hK) hKK' (Ne.symm h.1)
      (Ne.symm h.2)
  have hswap : ∀ g ∈ W, (conjSub g K = K ∧ conjSub g K' = K') ∨
      (conjSub g K = K' ∧ conjSub g K' = K) := by
    intro g hg
    have hK'g : conjSub g K' = K ∨ conjSub g K' = K' := by
      rw [hK', ← conjSub_mul]
      exact hdich _ (W.mul_mem hg hw₀W)
    rcases hdich g hg with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rcases hK'g with h2 | h2
      · exact absurd (conjSub_injective g (h2.trans h1.symm)) (Ne.symm hKK')
      · exact h2
    · right
      refine ⟨h1, ?_⟩
      rcases hK'g with h2 | h2
      · exact h2
      · exact absurd (conjSub_injective g (h1.trans h2.symm)) hKK'
  have hconjinv : ∀ g : X, ∀ L : Subgroup X, conjSub g⁻¹ (conjSub g L) = L := fun g L => by
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hfixinv : ∀ g ∈ W, conjSub g K = K → conjSub g⁻¹ K = K ∧ conjSub g⁻¹ K' = K' := by
    intro g hg h1
    rcases hswap g hg with ⟨-, h2⟩ | ⟨h2, -⟩
    · refine ⟨?_, ?_⟩
      · conv_lhs => rw [← h1]
        exact hconjinv g K
      · conv_lhs => rw [← h2]
        exact hconjinv g K'
    · exact absurd (h1.symm.trans h2) hKK'
  have hswapinv : ∀ g ∈ W, conjSub g K = K' → conjSub g⁻¹ K = K' ∧ conjSub g⁻¹ K' = K := by
    intro g hg h1
    rcases hswap g hg with ⟨h2, -⟩ | ⟨-, h2⟩
    · exact absurd (h2.symm.trans h1) hKK'
    · refine ⟨?_, ?_⟩
      · conv_lhs => rw [← h2]
        exact hconjinv g K'
      · conv_lhs => rw [← h1]
        exact hconjinv g K
  have hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (K : Set X) := by
    intro a ha b hb
    rw [← conjSub_eq_iff, conjSub_mul, conjSub_mul, conjSub_mul]
    rcases hswap a ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
      rcases hswap b hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · rw [(hfixinv b hb hb1).1, (hfixinv a ha ha1).1, hb1, ha1]
    · rw [(hswapinv b hb hb1).1, (hfixinv a ha ha1).2, hb2, ha1]
    · rw [(hfixinv b hb hb1).1, (hswapinv a ha ha1).1, hb2, ha2]
    · rw [(hswapinv b hb hb1).1, (hswapinv a ha ha1).2, hb1, ha2]
  have hle : ⁅W, W⁆ ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a ha b hb
  exact hnot (hW ▸ hle)

theorem commute_of_mem_centralizer_fstar {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := X) p = ⊥) {a b : X}
    (haO : a ∈ Subgroup.centralizer (CFSG.pCore p X : Set X))
    (haK : ∀ K : Subgroup X, IsComponentOf K ⊤ → a ∈ Subgroup.centralizer (K : Set X))
    (hbO : b ∈ Subgroup.centralizer (CFSG.pCore p X : Set X))
    (hbK : ∀ K : Subgroup X, IsComponentOf K ⊤ → b ∈ Subgroup.centralizer (K : Set X)) :
    Commute a b := by
  have hF : CFSG.fittingSubgroup X = CFSG.pCore p X := CFSG.Fitting_eq_pcore _ p hcore
  have hle : ∀ x : X, x ∈ Subgroup.centralizer (CFSG.pCore p X : Set X) →
      (∀ K : Subgroup X, IsComponentOf K ⊤ → x ∈ Subgroup.centralizer (K : Set X)) →
      x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    intro x hxO hxK
    have h : CFSG.generalizedFitting X ≤ Subgroup.centralizer ({x} : Set X) := by
      refine sup_le ?_ ?_
      · rw [hF]
        intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hxO y hy
      · refine sSup_le fun L hL => ?_
        intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hxK L ((CFSG.isComponent_iff_open L).mp hL))
          y hy
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h hy))
  have haF := CFSG.centralizer_generalizedFitting_le X (hle a haO haK)
  exact Subgroup.mem_centralizer_iff.mp (hle b hbO hbK) a haF

theorem exists_component_ker_le {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := X) p = ⊥) (hOcyc : IsCyclic (CFSG.pCore p X))
    (hthree : ∀ L₁ L₂ L₃ : Subgroup X, IsComponentOf L₁ ⊤ → IsComponentOf L₂ ⊤ →
      IsComponentOf L₃ ⊤ → L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → False)
    {W : Subgroup X} (hW : ⁅W, W⁆ = W) {Λ : Type*} [Group Λ] [IsSimpleGroup Λ]
    (hΛ : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊤) (θ : W →* Λ) (hθ : Function.Surjective θ) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ ∧ W ≤ Subgroup.normalizer (K : Set X) ∧
      ∀ w : W, (w : X) ∈ Subgroup.centralizer (K : Set X) → θ w = 1 := by
  have hWO : W ≤ Subgroup.centralizer (CFSG.pCore p X : Set X) :=
    le_centralizer_of_perfect_of_isCyclic hOcyc hW
  have hWN : ∀ K : Subgroup X, IsComponentOf K ⊤ → W ≤ Subgroup.normalizer (K : Set X) :=
    fun K hK => le_normalizer_of_perfect hthree hW hK
  have hnab : ¬ ∀ a b : Λ, a * b = b * a := by
    intro hab
    have hbot : ⁅(⊤ : Subgroup Λ), (⊤ : Subgroup Λ)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a b
    exact (bot_ne_top : (⊥ : Subgroup Λ) ≠ ⊤) (hbot.symm.trans hΛ)
  have habel : ∀ A : Subgroup W, (∀ a ∈ A, ∀ K : Subgroup X, IsComponentOf K ⊤ →
      (a : X) ∈ Subgroup.centralizer (K : Set X)) → A.map θ ≠ ⊤ := by
    intro A hA htop
    apply hnab
    intro x y
    obtain ⟨a, ha, rfl⟩ : x ∈ A.map θ := htop ▸ Subgroup.mem_top x
    obtain ⟨b, hb, rfl⟩ : y ∈ A.map θ := htop ▸ Subgroup.mem_top y
    have hc : Commute (a : X) (b : X) := commute_of_mem_centralizer_fstar hcore (hWO a.2)
      (hA a ha) (hWO b.2) (hA b hb)
    have hab : a * b = b * a := Subtype.ext hc.eq
    rw [← map_mul, ← map_mul, hab]
  set Kc : Subgroup X → Subgroup W := fun K =>
    (Subgroup.centralizer (K : Set X)).subgroupOf W with hKc
  have hKcn : ∀ K : Subgroup X, IsComponentOf K ⊤ → (Kc K).Normal := by
    intro K hK
    refine ⟨fun a ha g => ?_⟩
    have hg : (g : X) ∈ Subgroup.normalizer (K : Set X) := hWN K hK g.2
    change (g : X) * a * (g : X)⁻¹ ∈ Subgroup.centralizer (K : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : (g : X)⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
      simpa [mul_assoc] using this
    have h1 : ((g : X)⁻¹ * k * g) * (a : X) = (a : X) * ((g : X)⁻¹ * k * g) :=
      Subgroup.mem_centralizer_iff.mp ha _ hk'
    calc k * ((g : X) * a * (g : X)⁻¹) = g * (((g : X)⁻¹ * k * g) * a) * (g : X)⁻¹ := by group
      _ = g * (a * ((g : X)⁻¹ * k * g)) * (g : X)⁻¹ := by rw [h1]
      _ = (g : X) * a * (g : X)⁻¹ * k := by group
  have hdich : ∀ K : Subgroup X, IsComponentOf K ⊤ → (Kc K).map θ = ⊥ ∨ (Kc K).map θ = ⊤ :=
    fun K hK => have := hKcn K hK; ((this.map θ hθ).eq_bot_or_eq_top)
  by_contra hcon
  push Not at hcon
  have htop : ∀ K : Subgroup X, IsComponentOf K ⊤ → (Kc K).map θ = ⊤ := by
    intro K hK
    rcases hdich K hK with h | h
    · exfalso
      obtain ⟨w, hwC, hw⟩ := hcon K hK (hWN K hK)
      apply hw
      have : θ w ∈ (Kc K).map θ := ⟨w, hwC, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    · exact h
  by_cases hex : ∃ K₁ : Subgroup X, IsComponentOf K₁ ⊤
  · obtain ⟨K₁, hK₁⟩ := hex
    by_cases hone : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = K₁
    · refine habel (Kc K₁) (fun a ha K hK => ?_) (htop K₁ hK₁)
      rw [hone K hK]
      exact ha
    · push Not at hone
      obtain ⟨K₂, hK₂, hne⟩ := hone
      have hall : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = K₁ ∨ K = K₂ := by
        intro K hK
        by_contra h
        push Not at h
        exact hthree K₁ K₂ K hK₁ hK₂ hK (Ne.symm hne) (Ne.symm h.1) (Ne.symm h.2)
      have hmap : (Kc K₁ ⊓ Kc K₂).map θ = ⊤ := by
        have h1 : ⁅Kc K₁, Kc K₂⁆ ≤ Kc K₁ ⊓ Kc K₂ := by
          have := hKcn K₁ hK₁
          have := hKcn K₂ hK₂
          exact Subgroup.commutator_le_inf _ _
        have h2 : ⁅(Kc K₁).map θ, (Kc K₂).map θ⁆ ≤ (Kc K₁ ⊓ Kc K₂).map θ := by
          rw [← Subgroup.map_commutator]
          exact Subgroup.map_mono h1
        rw [htop K₁ hK₁, htop K₂ hK₂, hΛ] at h2
        exact top_le_iff.mp h2
      refine habel (Kc K₁ ⊓ Kc K₂) (fun a ha K hK => ?_) hmap
      rcases hall K hK with rfl | rfl
      · exact ha.1
      · exact ha.2
  · push Not at hex
    apply habel ⊤ (fun a _ K hK => absurd hK (hex K))
    rw [Subgroup.map_top_of_surjective θ hθ]

end CFSG.AGLEmbedding
