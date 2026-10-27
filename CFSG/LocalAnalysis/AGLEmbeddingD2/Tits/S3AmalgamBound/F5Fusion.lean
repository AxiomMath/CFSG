module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFPreimage
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Escape9
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFFusion

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.RankThreeCoreUniqueness.Helpers

theorem pow_three_of_mem_closure_pair {G : Type*} [Group G] {x y : G} (hxy : x * y = y * x)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    g ^ 3 = 1 := by
  have hcomm : Subgroup.closure ({x, y} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G) := by
    rw [Subgroup.centralizer_closure]
    refine (Subgroup.closure_le _).2 ?_
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    all_goals first | rfl | simp_all [eq_comm]
  induction hg using Subgroup.closure_induction with
  | mem a ha => rcases ha with rfl | ha; exact hx; simp at ha; subst ha; exact hy
  | one => simp
  | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := Subgroup.mem_centralizer_iff.1 (hcomm hb) a ha
      rw [Commute.mul_pow hab, iha, ihb, one_mul]
  | inv a ha iha => simp [inv_pow, iha]

theorem isPGroup_three_closure_pair {G : Type*} [Group G] {x y : G} (hxy : x * y = y * x)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) : IsPGroup 3 (Subgroup.closure {x, y}) := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using pow_three_of_mem_closure_pair hxy hx hy g.2)⟩

namespace S3Family

variable {V : Type*} [CommGroup V] {I : Finset (Subgroup (MulAut V))} (hI : S3Family I)
include hI

theorem eq_one_of_mem_inf {L₁ L₂ : Subgroup (MulAut V)} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I)
    (hne : L₁ ≠ L₂) {g : MulAut V} (hg₁ : g ∈ L₁) (hg₂ : g ∈ L₂) (hg3 : g ^ 3 = 1) : g = 1 := by
  by_contra hg1
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_actsAsNaturalL2 (hI.nat L₁ h₁)
  exact hu1 (eq_one_of_fixed_of_actsAsNaturalL2 (hI.nat L₁ h₁) hg₁ hg3 hg1 hu
    (hI.fixes_commV h₁ h₂ hne hg₂ hu))

end S3Family

variable {G : Type} [Group G] [Finite G]

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.false_of_same_side_pair3_of_conj
    {M N : Subgroup G} {V : Subgroup G} (hU : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂)
    {x₁ x₂ : G} (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M) (hx₁N : x₁ ∈ N) (hx₂N : x₂ ∈ N)
    (hcomm : x₁ * x₂ = x₂ * x₁) (ho₁ : x₁ ^ 3 = 1) (ho₂ : x₂ ^ 3 = 1)
    (hL₁ : actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁) (hL₂ : actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂)
    (h₁1 : actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1) (h₂1 : actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1)
    (hconj : ∀ X : Subgroup G, X = Subgroup.closure {x₁, x₂} → X ≤ N → X ≤ M → IsPGroup 3 X →
      ¬ IsCyclic X → IsElemAbelian 3 X ∧ Nat.card X = 9 ∧ ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 →
        ∃ n ∈ M ⊓ Subgroup.normalizer (X : Set G), n * x * n⁻¹ = y) : False := by
  set g₁ := actM hU hMN ⟨x₁, hx₁M⟩ with hg₁
  set g₂ := actM hU hMN ⟨x₂, hx₂M⟩ with hg₂
  have hg₁3 : g₁ ^ 3 = 1 := by
    have h' : (⟨x₁, hx₁M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using ho₁)
    rw [hg₁, ← map_pow, h', map_one]
  have hg₂3 : g₂ ^ 3 = 1 := by
    have h' : (⟨x₂, hx₂M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using ho₂)
    rw [hg₂, ← map_pow, h', map_one]
  have hx₁1 : x₁ ≠ 1 := fun h => h₁1 (by
    have h' : (⟨x₁, hx₁M⟩ : M) = 1 := Subtype.ext h
    rw [hg₁, h', map_one])
  set X : Subgroup G := Subgroup.closure {x₁, x₂} with hX
  have hXp : IsPGroup 3 X := isPGroup_three_closure_pair hcomm ho₁ ho₂
  have hx₁X : x₁ ∈ X := Subgroup.subset_closure (by simp)
  have hx₂X : x₂ ∈ X := Subgroup.subset_closure (by simp)
  have hXN : X ≤ N := (Subgroup.closure_le N).2 (by
    intro a ha; rcases ha with rfl | ha; exact hx₁N; simp at ha; subst ha; exact hx₂N)
  have hXM : X ≤ M := (Subgroup.closure_le M).2 (by
    intro a ha; rcases ha with rfl | ha; exact hx₁M; simp at ha; subst ha; exact hx₂M)
  have hnot : ∀ k : ℤ, x₂ ≠ x₁ ^ k := by
    intro k hk
    have : g₂ = g₁ ^ k := by
      rw [hg₂, hg₁, ← map_zpow]
      congr 1
      exact Subtype.ext (by simpa using hk)
    exact h₂1 (hI.eq_one_of_mem_inf h₁ h₂ hne (this ▸ L₁.zpow_mem hL₁ k) hL₂ hg₂3)
  have hXc : ¬ IsCyclic X := by
    intro hcyc
    obtain ⟨z, hz⟩ := hcyc.exists_generator
    have hz3 : z ^ 3 = 1 := Subtype.ext (by
      simpa using pow_three_of_mem_closure_pair hcomm ho₁ ho₂ z.2)
    have hcard : Nat.card X = orderOf z := orderOf_eq_card_of_forall_mem_zpowers hz |>.symm
    have hle3 : Nat.card X ≤ 3 := by
      rw [hcard]; exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
    have hord : orderOf x₁ = 3 := by
      refine orderOf_eq_prime ho₁ hx₁1
    have hzp : Nat.card (Subgroup.zpowers x₁) = 3 := by rw [Nat.card_zpowers, hord]
    have hzpX : Subgroup.zpowers x₁ ≤ X := (Subgroup.zpowers_le).2 hx₁X
    have heq : Subgroup.zpowers x₁ = X :=
      Subgroup.eq_of_le_of_card_ge hzpX (by rw [hzp]; exact hle3)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (heq ▸ hx₂X)
    exact hnot k hk.symm
  obtain ⟨-, -, hconj⟩ := hconj X rfl hXN hXM hXp hXc
  have hy1 : x₁ * x₂ ≠ 1 := by
    intro h
    exact hnot (-1) (by rw [zpow_neg_one]; exact eq_inv_of_mul_eq_one_right h)
  obtain ⟨n, hn, hnx⟩ := hconj x₁ hx₁X hx₁1 (x₁ * x₂) (X.mul_mem hx₁X hx₂X) hy1
  obtain ⟨hnM, -⟩ := Subgroup.mem_inf.1 hn
  have hm : actM hU hMN ⟨n, hnM⟩ * g₁ * (actM hU hMN ⟨n, hnM⟩)⁻¹ = g₁ * g₂ := by
    rw [hg₁, hg₂, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hnx)
  exact hI.not_conj_of_distinct_factors h₁ h₂ hne hL₁ hL₂ hg₂3 h₂1 _ hm

theorem false_of_same_side_pair {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {N : Subgroup G} (hN : IsTwoLocal N) (hNM : ¬ N ≤ M)
    {V : Subgroup G} (hU : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂)
    {x₁ x₂ : G} (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M) (hx₁N : x₁ ∈ N) (hx₂N : x₂ ∈ N)
    (hcomm : x₁ * x₂ = x₂ * x₁) (ho₁ : x₁ ^ 3 = 1) (ho₂ : x₂ ^ 3 = 1)
    (hL₁ : actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁) (hL₂ : actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂)
    (h₁1 : actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1) (h₂1 : actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1) : False :=
  CFSG.LocalAnalysis.RankThreeTheoremC.false_of_same_side_pair3_of_conj hU hMN hI h₁ h₂ hne hx₁M
    hx₂M hx₁N hx₂N hcomm ho₁ ho₂ hL₁ hL₂ h₁1 h₂1 fun _ _ hXN hXM hXp hXc =>
      D2L34BetaConf.exists_conj_eq_of_not_isCyclic hc hstr hOnly hN hNM hXN hXM hXp hXc

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
