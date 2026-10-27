module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClOrthFixed
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Open
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Group

theorem exists_elemAbelian_of_commute_disjoint {G : Type*} [Group G] {A B S : Subgroup G}
    (hAS : A ≤ S) (hBS : B ≤ S) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : Disjoint A B)
    (hA : IsElemAbelian 5 A) (hB : IsElemAbelian 5 B) :
    ∃ E : Subgroup G, A ≤ E ∧ B ≤ E ∧ E ≤ S ∧ IsElemAbelian 5 E ∧
      Nat.card E = Nat.card A * Nat.card B := by
  have hcomm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n => hc m m.2 n n.2
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, B.subtype_injective, by simpa using hd⟩
  refine ⟨φ.range, ?_, ?_, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · intro a ha
    exact ⟨(⟨a, ha⟩, 1), by simp [hφ]⟩
  · intro b hb
    exact ⟨(1, ⟨b, hb⟩), by simp [hφ]⟩
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    exact mul_mem (hAS m.2) (hBS n.2)
  · obtain ⟨_, ⟨m, n⟩, rfl⟩ := a
    obtain ⟨_, ⟨m', n'⟩, rfl⟩ := b
    apply Subtype.ext
    show φ (m, n) * φ (m', n') = φ (m', n') * φ (m, n)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (hA.1.1.comm m m') (hB.1.1.comm n n')
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    rw [← map_pow]
    have h1 : m ^ 5 = 1 := Subtype.ext (hA.2 m m.2)
    have h2 : n ^ 5 = 1 := Subtype.ext (hB.2 n n.2)
    rw [Prod.pow_mk, h1, h2]
    exact map_one φ
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

theorem isElemAbelian_zpowers_of_orderOf_five {G : Type*} [Group G] {c : G} (hc : orderOf c = 5) :
    IsElemAbelian 5 (Subgroup.zpowers c) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    apply Subtype.ext
    show (u : G) * v = v * u
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self c i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have h5 : c ^ 5 = 1 := by have := pow_orderOf_eq_one c; rwa [hc] at this
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]

theorem exists_elemAbelian_pair {G : Type*} [Group G] (a b : G) (S : Subgroup G) (haS : a ∈ S)
    (hbS : b ∈ S) (ha : orderOf a = 5) (hb : orderOf b = 5) (hab : Commute a b)
    (hind : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b)) :
    ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  have hc : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((hab.zpow_left i).zpow_right j).eq
  obtain ⟨E, -, -, hES, hE, hcard⟩ := exists_elemAbelian_of_commute_disjoint
    (Subgroup.zpowers_le.2 haS) (Subgroup.zpowers_le.2 hbS) hc hind
    (isElemAbelian_zpowers_of_orderOf_five ha) (isElemAbelian_zpowers_of_orderOf_five hb)
  refine ⟨E, hES, hE, ?_⟩
  rw [hcard, Nat.card_zpowers, Nat.card_zpowers, ha, hb]

end Group

section Blocks

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_elemAbelian_of_blocks (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (k : ↥Rep → ℕ)
    (hk : ∀ i : ↥Rep, ∃ A : Subgroup (V ≃ₗ[K] V), A ≤ supportedBlock Q x ↑i ∧
      IsElemAbelian 5 A ∧ Nat.card A = 5 ^ k i) :
    ∃ E : Subgroup (V ≃ₗ[K] V), E ≤ isometryCentralizer Q x ∧ IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ ∑ i, k i := by
  classical
  choose A hAle hAel hAcard using hk
  have hcomm : Pairwise fun i j : ↥Rep => ∀ a b : V ≃ₗ[K] V, a ∈ A i → b ∈ A j → Commute a b :=
    fun i j hij a b ha hb => hx.blocks_commute hRep hij a b (hAle i ha) (hAle j hb)
  have hind : iSupIndep A := (hx.blocks_iSupIndep hRep).mono hAle
  set φ := Subgroup.noncommPiCoprod (H := A) hcomm with hφ
  have hinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  refine ⟨φ.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · rw [hφ, Subgroup.noncommPiCoprod_range]
    exact iSup_le fun i => (hAle i).trans (supportedBlock_le_isometryCentralizer _)
  · obtain ⟨_, s, rfl⟩ := a
    obtain ⟨_, t, rfl⟩ := b
    apply Subtype.ext
    show φ s * φ t = φ t * φ s
    rw [← map_mul, ← map_mul]
    congr 1
    funext i
    exact (hAel i).1.1.comm (s i) (t i)
  · rintro _ ⟨s, rfl⟩
    rw [← map_pow]
    have : s ^ 5 = 1 := by
      funext i
      exact Subtype.ext ((hAel i).2 (s i) (s i).2)
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_pi]
    simp only [hAcard]
    exact Finset.prod_pow_eq_pow_sum _ _ _

theorem exists_elemAbelian_two_indices (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {r₁ r₂ : ↥Rep} (hne : r₁ ≠ r₂)
    {A₁ A₂ : Subgroup (V ≃ₗ[K] V)} {k₁ k₂ : ℕ}
    (h₁ : A₁ ≤ supportedBlock Q x ↑r₁ ∧ IsElemAbelian 5 A₁ ∧ Nat.card A₁ = 5 ^ k₁)
    (h₂ : A₂ ≤ supportedBlock Q x ↑r₂ ∧ IsElemAbelian 5 A₂ ∧ Nat.card A₂ = 5 ^ k₂) :
    ∃ E : Subgroup (V ≃ₗ[K] V), E ≤ isometryCentralizer Q x ∧ IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ (k₁ + k₂) := by
  classical
  obtain ⟨E, hE, hel, hcard⟩ := exists_elemAbelian_of_blocks hx hRep
    (Pi.single r₁ k₁ + Pi.single r₂ k₂) (fun i => by
      by_cases hi1 : i = r₁
      · subst hi1
        exact ⟨A₁, h₁.1, h₁.2.1, by simpa [Pi.single_apply, hne] using h₁.2.2⟩
      · by_cases hi2 : i = r₂
        · subst hi2
          exact ⟨A₂, h₂.1, h₂.2.1, by simpa [Pi.single_apply, hne.symm] using h₂.2.2⟩
        · exact ⟨⊥, bot_le, CFSG.SectionRank.isElemAbelian_bot 5,
            by simp [Pi.single_apply, hi1, hi2]⟩)
  refine ⟨E, hE, hel, ?_⟩
  rw [hcard]
  congr 1
  simp [Finset.sum_add_distrib, Finset.sum_pi_single']

theorem exists_elemAbelian_three_indices (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {r₁ r₂ r₃ : ↥Rep} (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃)
    (h23 : r₂ ≠ r₃) {A₁ A₂ A₃ : Subgroup (V ≃ₗ[K] V)} {k₁ k₂ k₃ : ℕ}
    (h₁ : A₁ ≤ supportedBlock Q x ↑r₁ ∧ IsElemAbelian 5 A₁ ∧ Nat.card A₁ = 5 ^ k₁)
    (h₂ : A₂ ≤ supportedBlock Q x ↑r₂ ∧ IsElemAbelian 5 A₂ ∧ Nat.card A₂ = 5 ^ k₂)
    (h₃ : A₃ ≤ supportedBlock Q x ↑r₃ ∧ IsElemAbelian 5 A₃ ∧ Nat.card A₃ = 5 ^ k₃) :
    ∃ E : Subgroup (V ≃ₗ[K] V), E ≤ isometryCentralizer Q x ∧ IsElemAbelian 5 E ∧
      Nat.card E = 5 ^ (k₁ + k₂ + k₃) := by
  classical
  obtain ⟨E, hE, hel, hcard⟩ := exists_elemAbelian_of_blocks hx hRep
    (Pi.single r₁ k₁ + Pi.single r₂ k₂ + Pi.single r₃ k₃) (fun i => by
      by_cases hi1 : i = r₁
      · subst hi1
        exact ⟨A₁, h₁.1, h₁.2.1, by simpa [Pi.single_apply, h12, h13] using h₁.2.2⟩
      · by_cases hi2 : i = r₂
        · subst hi2
          exact ⟨A₂, h₂.1, h₂.2.1, by simpa [Pi.single_apply, h12.symm, h23] using h₂.2.2⟩
        · by_cases hi3 : i = r₃
          · subst hi3
            exact ⟨A₃, h₃.1, h₃.2.1, by simpa [Pi.single_apply, h13.symm, h23.symm] using h₃.2.2⟩
          · exact ⟨⊥, bot_le, CFSG.SectionRank.isElemAbelian_bot 5,
              by simp [Pi.single_apply, hi1, hi2, hi3]⟩)
  refine ⟨E, hE, hel, ?_⟩
  rw [hcard]
  congr 1
  simp [Finset.sum_add_distrib, Finset.sum_pi_single']

end Blocks

section BlockElements

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem root_pow_eq_one_iff (hx : OddOrderIsometry Q 5 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (n : ℕ) :
    AdjoinRoot.root h ^ n = 1 ↔ 5 ∣ n := by
  obtain ⟨hlam0, hord⟩ := hx.orderOf_root Nat.prime_five hh hne1
  rw [← hord, orderOf_dvd_iff_pow_eq_one, ← Units.val_inj, Units.val_pow_eq_pow_val,
    Units.val_mk0, Units.val_one]

theorem orderOf_scalar_block (hx : OddOrderIsometry Q 5 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (g : ↥(supportedBlock Q x h))
    (hg5 : g ^ 5 = 1)
    (hdet : blockDet Q x h g = AdjoinRoot.root h ^ primaryMultiplicity x.toLinearMap h)
    (hm5 : ¬ 5 ∣ primaryMultiplicity x.toLinearMap h) : orderOf (g : V ≃ₗ[K] V) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime (congrArg Subtype.val hg5) fun h1 => hm5 ?_
  have : g = 1 := Subtype.ext h1
  rw [this, map_one] at hdet
  exact (root_pow_eq_one_iff hx hh hne1 _).1 hdet.symm

theorem exists_block_elemAbelian_one (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm5 : ¬ 5 ∣ primaryMultiplicity x.toLinearMap h) :
    ∃ A : Subgroup (V ≃ₗ[K] V), A ≤ supportedBlock Q x h ∧ IsElemAbelian 5 A ∧
      Nat.card A = 5 ^ 1 := by
  obtain ⟨g, hg5, hdet, -⟩ := exists_scalar_block hx hh hne1 hself
  have ho := orderOf_scalar_block hx hh hne1 g hg5 hdet hm5
  exact ⟨Subgroup.zpowers (g : V ≃ₗ[K] V), Subgroup.zpowers_le.2 g.2,
    isElemAbelian_zpowers_of_orderOf_five ho, by rw [Nat.card_zpowers, ho, pow_one]⟩

theorem exists_block_elemAbelian_two (hx : OddOrderIsometry Q 5 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : primaryMultiplicity x.toLinearMap h = 2) :
    ∃ A : Subgroup (V ≃ₗ[K] V), A ≤ supportedBlock Q x h ∧ IsElemAbelian 5 A ∧
      Nat.card A = 5 ^ 2 := by
  classical
  have hm5 : ¬ 5 ∣ primaryMultiplicity x.toLinearMap h := by rw [hm]; norm_num
  obtain ⟨g, hg5, hdet, hcomm⟩ := exists_scalar_block hx hh hne1 hself
  obtain ⟨f, hf, hfo⟩ := exists_orderOf_five_specialBlock hx hh hne1 hself (by omega)
  have ho := orderOf_scalar_block hx hh hne1 g hg5 hdet hm5
  set f' : ↥(supportedBlock Q x h) := ⟨f, specialBlock_le_supportedBlock h hf⟩ with hf'
  have hdetf : blockDet Q x h f' = 1 := blockDet_eq_one_of_mem_specialBlock hf
  have hcom : Commute (g : V ≃ₗ[K] V) f := congrArg Subtype.val (hcomm f').eq
  have hdisj : Disjoint (Subgroup.zpowers (g : V ≃ₗ[K] V)) (Subgroup.zpowers f) := by
    rw [Subgroup.disjoint_def]
    intro u hu1 hu2
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hu1)
    obtain ⟨m, hm'⟩ := Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 hu2)
    have h1 : g ^ n = f' ^ m := Subtype.ext (by
      show ((g : V ≃ₗ[K] V)) ^ n = f ^ m
      rw [hn, hm'])
    have h2 := congrArg (blockDet Q x h) h1
    rw [map_pow, map_pow, hdet, hdetf, one_pow, ← pow_mul,
      root_pow_eq_one_iff hx hh hne1] at h2
    have h5n : 5 ∣ n := by
      have : 5 ∣ 2 * n := by simpa [hm, mul_comm] using h2
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
    rw [← hn]
    obtain ⟨c, hc⟩ := h5n
    rw [hc, pow_mul, show ((g : V ≃ₗ[K] V)) ^ 5 = 1 from congrArg Subtype.val hg5, one_pow]
  obtain ⟨E, hES, hE, hcard⟩ := exists_elemAbelian_pair (g : V ≃ₗ[K] V) f (supportedBlock Q x h)
    g.2 (specialBlock_le_supportedBlock h hf) ho hfo hcom hdisj
  exact ⟨E, hES, hE, by rw [hcard]; norm_num⟩

end BlockElements

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_rep_X_sub_one (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (hW : fixedSpace x ≠ ⊥) :
    ∃ r : ↥Rep, (r : K[X]) = X - 1 := by
  have hmem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    exact hW (fixedSpace_eq_bot_of_not_mem hnot)
  obtain ⟨r, ⟨hr, hor⟩, -⟩ := hRep.2 _ hmem
  refine ⟨⟨r, hr⟩, ?_⟩
  rcases hor with h | h
  · exact h.symm
  · have h2 := hx.reciprocal_reciprocal_eq (hRep.1 hr)
    rw [← h, reciprocalPolynomial_X_sub_one] at h2
    exact h2.symm

theorem exists_fixed_elemAbelian [CharP K 2] (hx : OddOrderIsometry Q p x)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K) (hK : Nat.card K = 4) :
    ∃ A : Subgroup (V ≃ₗ[K] V), A ≤ supportedBlock Q x (X - 1) ∧ IsElemAbelian 5 A ∧
      Nat.card A = 5 ^ 2 := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_split e hK
  refine ⟨(E.map (fixedBlockEquiv hx).symm.toMonoidHom).map
    (supportedBlock Q x (X - 1)).subtype, Subgroup.map_subtype_le _,
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hE _) _, ?_⟩
  rw [Subgroup.card_map_of_injective (supportedBlock Q x (X - 1)).subtype_injective,
    Subgroup.card_map_of_injective (fixedBlockEquiv hx).symm.injective, hcard]
  norm_num

end Fixed

section Transfer

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem false_of_elemAbelian_five_pow_four [Nontrivial V]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {G : Type} [Group G]
    [Finite G] (e : G ≃* ProjOrthDerived Q) {P : Sylow 5 G}
    (hP : CFSG.Open.pRank 5 (P : Subgroup G) = 3) {E : Subgroup (V ≃ₗ[K] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : IsElemAbelian 5 E)
    (hcard : Nat.card E = 5 ^ 4) : False := by
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hEΩ : E ≤ orthDerived Q := fun g hg =>
    hodd g (hEO hg) (Odd.of_dvd_nat (by decide : Odd 5) (orderOf_dvd_of_pow_eq_one (hE.2 g hg)))
  haveI : Finite (V ≃ₗ[K] V) := inferInstance
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hinj : Function.Injective (ρ.comp (Subgroup.inclusion hEΩ)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : ρ (Subgroup.inclusion hEΩ a) = 1 := ha
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    obtain ⟨v₀, hv₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
    obtain ⟨c, hc2, hc⟩ := CFSG.RankThree.Classical.exists_sq_eq_one_of_mem_scalars
      (g := (a : V ≃ₗ[K] V)) h1 (hEO a.2) hv₀
    have ha5 : (a : V ≃ₗ[K] V) ^ 5 = 1 := hE.2 a a.2
    have hpow : ∀ n : ℕ, ((a : V ≃ₗ[K] V) ^ n) v₀ = c ^ n • v₀ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hc, map_smul, ih, smul_smul, pow_succ]
        ring_nf
    have hv0 : v₀ ≠ 0 := by
      rintro rfl
      exact hv₀ (QuadraticMap.map_zero Q)
    have hc5 : c ^ 5 = 1 := by
      have h := hpow 5
      have h1' : (1 : V ≃ₗ[K] V) v₀ = v₀ := rfl
      rw [ha5, h1'] at h
      have h' : (c ^ 5 - 1) • v₀ = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hv0)
    have hc1 : c = 1 := by
      have h' : c ^ 5 = c * (c ^ 2) ^ 2 := by ring
      rw [hc5, hc2] at h'
      simpa using h'.symm
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    show (a : V ≃ₗ[K] V) v = v
    rw [hc, hc1, one_smul]
  have hle := CFSG.SectionRank.le_pRank_of_injective (G := ProjOrthDerived Q) (p := 5)
    (by norm_num) (fun a b => hE.1.1.comm a b) (fun a => Subtype.ext (hE.2 a a.2))
    hcard (ρ.comp (Subgroup.inclusion hEΩ)) hinj (H := ⊤) le_top
  exact false_of_four_le_pRank_top e hP hle

end Transfer

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
