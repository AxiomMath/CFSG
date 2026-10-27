module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem exists_surjective_range_of_ker_le {A Q Y : Type*} [Group A] [Group Q] [Group Y]
    (f : A →* Q) (ψ : A →* Y) (hψ : Function.Surjective ψ) (hker : f.ker ≤ ψ.ker) :
    ∃ ψ' : f.range →* Y, Function.Surjective ψ' := by
  have hf : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hker' : f.rangeRestrict.ker ≤ ψ.ker := by rwa [MonoidHom.ker_rangeRestrict]
  refine ⟨MonoidHom.liftOfSurjective f.rangeRestrict hf ⟨ψ, hker'⟩, fun y => ?_⟩
  obtain ⟨a, rfl⟩ := hψ y
  exact ⟨f.rangeRestrict a, MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ψ, hker'⟩ a⟩

theorem not_isPGroup_two_of_card_504 {Y : Type*} [Group Y] (hcard : Nat.card Y = 504) :
    ¬ IsPGroup 2 Y := by
  intro h
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h
  rw [hcard] at hk
  have hk9 : k < 9 := by
    by_contra hc
    have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> omega

theorem exists_surjective_range_of_isPGroup_ker {A Q Y : Type*} [Group A] [Group Q] [Group Y]
    (f : A →* Q) (hf : IsPGroup 2 f.ker) (ψ : A →* Y) (hψ : Function.Surjective ψ)
    (hY : IsSimpleGroup Y) (hcard : Nat.card Y = 504) :
    ∃ ψ' : f.range →* Y, Function.Surjective ψ' := by
  refine exists_surjective_range_of_ker_le f ψ hψ ?_
  have hN : (f.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases hY.eq_bot_or_eq_top_of_normal (f.ker.map ψ) with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h2 : IsPGroup 2 (f.ker.map ψ) := hf.map ψ
    rw [h] at h2
    have h3 : IsPGroup 2 Y := h2.of_equiv Subgroup.topEquiv
    exact not_isPGroup_two_of_card_504 hcard h3




theorem false_of_normal_perm_quotient {m : ℕ} (X : Subgroup (Equiv.Perm (Fin m))) [X.Normal]
    {Y : Type*} [Group Y] (hY : IsSimpleGroup Y) (hcard : Nat.card Y = 504)
    (ψ : X →* Y) (hψ : Function.Surjective ψ) : False := by
  have h504 : 504 ∣ Nat.card X := hcard ▸ Subgroup.card_dvd_of_surjective hψ
  have h7 : 7 ∣ Nat.card X := (by norm_num : 7 ∣ 504).trans h504
  have hX0 : 0 < Nat.card X := Nat.card_pos
  have hm7 : 7 ≤ m := by
    have h7' : 7 ∣ Nat.card (Equiv.Perm (Fin m)) := h7.trans (Subgroup.card_subgroup_dvd_card X)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h7'
    exact (Nat.Prime.dvd_factorial (by norm_num)).mp h7'
  have hfact : 5040 ≤ m.factorial := by
    have := Nat.factorial_le hm7
    simpa [Nat.factorial] using this
  have hnt : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hA : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hAcard : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  set A : Subgroup (Equiv.Perm (Fin m)) := alternatingGroup (Fin m) with hAdef
  have hDidx : (A.subgroupOf X).index ∣ 2 := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal A X
    rwa [alternatingGroup.index_eq_two] at h1
  have hY1 : Nontrivial Y := hY.toNontrivial
  rcases hA.eq_bot_or_eq_top_of_normal (X.subgroupOf A) with hb | ht
  ·
    have hD : A.subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxA : (x : Equiv.Perm (Fin m)) ∈ A := hx
      have : (⟨x, hxA⟩ : A) ∈ X.subgroupOf A := x.2
      rw [hb, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      have h2 : ((⟨x, hxA⟩ : A) : Equiv.Perm (Fin m)) = ((1 : A) : Equiv.Perm (Fin m)) := by
        rw [this]
      exact Subtype.ext h2
    rw [hD, Subgroup.index_bot] at hDidx
    have := Nat.le_of_dvd (by norm_num) hDidx
    omega
  ·
    have hAX : A ≤ X := fun a ha => by
      have : (⟨a, ha⟩ : A) ∈ X.subgroupOf A := by rw [ht]; trivial
      exact this
    set D : Subgroup X := A.subgroupOf X with hDdef
    have hDsimple : IsSimpleGroup D := by
      have := hA
      exact (Subgroup.subgroupOfEquivOfLe hAX).isSimpleGroup
    have hDcard : Nat.card D = m.factorial / 2 := by
      rw [← hAcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
    have hN : (D.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    rcases hY.eq_bot_or_eq_top_of_normal (D.map ψ) with h | h
    ·
      have hle : D ≤ ψ.ker := (Subgroup.map_eq_bot_iff _).mp h
      have h1 := Subgroup.index_dvd_of_le hle
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top,
        hcard] at h1
      have := Nat.le_of_dvd (by norm_num) (h1.trans hDidx)
      omega
    ·
      let ψD : D →* Y := ψ.comp D.subtype
      have hψD : Function.Surjective ψD := by
        intro y
        have hy : y ∈ D.map ψ := by rw [h]; trivial
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩
      rcases hDsimple.eq_bot_or_eq_top_of_normal ψD.ker with hk | hk
      · have hinj : Function.Injective ψD := (MonoidHom.ker_eq_bot_iff ψD).mp hk
        have := Nat.card_congr (Equiv.ofBijective ψD ⟨hinj, hψD⟩)
        rw [hDcard, hcard] at this
        omega
      · obtain ⟨y, hy⟩ := exists_ne (1 : Y)
        obtain ⟨d, rfl⟩ := hψD y
        have : d ∈ ψD.ker := by rw [hk]; trivial
        exact hy this

theorem false_of_normal_perm_prod_quotient {r s : ℕ}
    (X : Subgroup (Equiv.Perm (Fin r) × Equiv.Perm (Fin s))) [X.Normal]
    {Y : Type*} [Group Y] (hY : IsSimpleGroup Y) (hcard : Nat.card Y = 504)
    (ψ : X →* Y) (hψ : Function.Surjective ψ) : False := by
  let π₂ : X →* Equiv.Perm (Fin s) := (MonoidHom.snd _ _).comp X.subtype
  by_cases hk : π₂.ker ≤ ψ.ker
  · obtain ⟨ψ', hψ'⟩ := exists_surjective_range_of_ker_le π₂ ψ hψ hk
    have hnorm : π₂.range.Normal := by
      refine ⟨?_⟩
      rintro _ ⟨x, rfl⟩ g
      have hx : ((1, g) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) * (x : _ × _) *
          ((1, g) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s))⁻¹ ∈ X :=
        Subgroup.Normal.conj_mem inferInstance _ x.2 _
      exact ⟨⟨_, hx⟩, by simp [π₂]⟩
    have := hnorm
    exact false_of_normal_perm_quotient π₂.range hY hcard ψ' hψ'
  · have hN : (π₂.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have htop : π₂.ker.map ψ = ⊤ := by
      rcases hY.eq_bot_or_eq_top_of_normal (π₂.ker.map ψ) with h | h
      · exact absurd ((Subgroup.map_eq_bot_iff _).mp h) hk
      · exact h
    let π₁ : X →* Equiv.Perm (Fin r) := (MonoidHom.fst _ _).comp X.subtype
    let ι : π₂.ker →* Equiv.Perm (Fin r) := π₁.comp π₂.ker.subtype
    have hι : Function.Injective ι := by
      rw [injective_iff_map_eq_one]
      intro k hk1
      have h1' : ((k : X) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)).1 = 1 := hk1
      have h2' : ((k : X) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)).2 = 1 := k.2
      exact Subtype.ext (Subtype.ext (Prod.ext h1' h2'))
    have hnorm : ι.range.Normal := by
      refine ⟨?_⟩
      rintro _ ⟨k, rfl⟩ g
      have hx : ((g, 1) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) * ((k : X) : _ × _) *
          ((g, 1) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s))⁻¹ ∈ X :=
        Subgroup.Normal.conj_mem inferInstance _ (k : X).2 _
      have h2 : π₂ (k : X) = 1 := k.2
      have hk' : (⟨_, hx⟩ : X) ∈ π₂.ker := by
        rw [MonoidHom.mem_ker]
        have : ((k : X) : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)).2 = 1 := h2
        simp [π₂, this]
      exact ⟨⟨_, hk'⟩, by simp [ι, π₁]⟩
    let ψ₀ : π₂.ker →* Y := ψ.comp π₂.ker.subtype
    have hψ₀ : Function.Surjective ψ₀ := by
      intro y
      have hy : y ∈ π₂.ker.map ψ := by rw [htop]; trivial
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    let e : π₂.ker ≃* ι.range := MonoidHom.ofInjective hι
    have := hnorm
    exact false_of_normal_perm_quotient ι.range hY hcard (ψ₀.comp e.symm.toMonoidHom)
      (hψ₀.comp e.symm.surjective)

theorem false_of_perm_hom_normal_range {m : ℕ} {A Y : Type*} [Group A] [Group Y]
    (f : A →* Equiv.Perm (Fin m)) (hn : f.range.Normal) (hf : IsPGroup 2 f.ker)
    (ψ : A →* Y) (hψ : Function.Surjective ψ) (hY : IsSimpleGroup Y) (hcard : Nat.card Y = 504) :
    False := by
  obtain ⟨ψ', hψ'⟩ := exists_surjective_range_of_isPGroup_ker f hf ψ hψ hY hcard
  have := hn
  exact false_of_normal_perm_quotient f.range hY hcard ψ' hψ'

theorem false_of_perm_prod_hom_normal_range {r s : ℕ} {A Y : Type*} [Group A] [Group Y]
    (f : A →* Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (hn : f.range.Normal)
    (hf : IsPGroup 2 f.ker) (ψ : A →* Y) (hψ : Function.Surjective ψ) (hY : IsSimpleGroup Y)
    (hcard : Nat.card Y = 504) : False := by
  obtain ⟨ψ', hψ'⟩ := exists_surjective_range_of_isPGroup_ker f hf ψ hψ hY hcard
  have := hn
  exact false_of_normal_perm_prod_quotient f.range hY hcard ψ' hψ'

theorem isPGroup_ker_comp_subtype {J K : Type*} [Group J] [Group K] (ρ : J →* K)
    (hk : IsPGroup 2 ρ.ker) (B : Subgroup J) : IsPGroup 2 (ρ.comp B.subtype).ker := by
  refine hk.of_injective (((B.subtype.comp (ρ.comp B.subtype).ker.subtype)).codRestrict ρ.ker
    fun x => ?_) ?_
  · have := x.2
    exact this
  · intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥ρ.ker → J) hxy))

theorem false_of_perm_section {J : Type*} [Group J] {m : ℕ} (ρ : J →* Equiv.Perm (Fin m))
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker) (B : Subgroup J) [B.Normal]
    {Y : Type*} [Group Y] (ψ : B →* Y) (hψ : Function.Surjective ψ) (hY : IsSimpleGroup Y)
    (hcard : Nat.card Y = 504) : False := by
  have hn : (ρ.comp B.subtype).range.Normal := by
    have : (ρ.comp B.subtype).range = B.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact Subgroup.Normal.map inferInstance ρ hρ
  exact false_of_perm_hom_normal_range (ρ.comp B.subtype) hn (isPGroup_ker_comp_subtype ρ hk B)
    ψ hψ hY hcard

theorem false_of_perm_prod_section {J : Type*} [Group J] {r s : ℕ}
    (ρ : J →* Equiv.Perm (Fin r) × Equiv.Perm (Fin s))
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker) (B : Subgroup J) [B.Normal]
    {Y : Type*} [Group Y] (ψ : B →* Y) (hψ : Function.Surjective ψ) (hY : IsSimpleGroup Y)
    (hcard : Nat.card Y = 504) : False := by
  have hn : (ρ.comp B.subtype).range.Normal := by
    have : (ρ.comp B.subtype).range = B.map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact Subgroup.Normal.map inferInstance ρ hρ
  exact false_of_perm_prod_hom_normal_range (ρ.comp B.subtype) hn
    (isPGroup_ker_comp_subtype ρ hk B) ψ hψ hY hcard

theorem false_of_alt_seven_section {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 7))
    (B : Subgroup K) {Y : Type*} [Group Y] (hY : IsSimpleGroup Y) (hcard : Nat.card Y = 504)
    (ψ : B →* Y) (hψ : Function.Surjective ψ) : False := by
  have hA : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hK : IsSimpleGroup K := e.isSimpleGroup
  have hKcard : Nat.card K = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hFin : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have h504 : 504 ∣ Nat.card B := hcard ▸ Subgroup.card_dvd_of_surjective hψ
  obtain ⟨c, hc⟩ := h504
  have hidx : B.index * (504 * c) = 2520 := by
    rw [← hc, mul_comm, Subgroup.card_mul_index, hKcard]
  have hidx0 : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hc5' : 504 * (B.index * c) = 2520 := by rw [← hidx]; ring
  have hc5 : B.index * c = 5 := by omega
  have hdiv : B.index = 1 ∨ B.index = 5 := by
    have : B.index ∣ 5 := ⟨c, hc5.symm⟩
    exact (Nat.dvd_prime (by norm_num)).mp this
  rcases hdiv with h1 | h5
  ·
    have hB : B = ⊤ := Subgroup.index_eq_one.mp h1
    subst hB
    have hBs : IsSimpleGroup (⊤ : Subgroup K) := by
      have := hK
      exact Subgroup.topEquiv.isSimpleGroup
    have hBcard : Nat.card (⊤ : Subgroup K) = 2520 := by rw [Subgroup.card_top, hKcard]
    have hY1 : Nontrivial Y := hY.toNontrivial
    rcases hBs.eq_bot_or_eq_top_of_normal ψ.ker with hk | hk
    · have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk
      have := Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hψ⟩)
      rw [hBcard, hcard] at this
      omega
    · obtain ⟨y, hy⟩ := exists_ne (1 : Y)
      obtain ⟨d, rfl⟩ := hψ y
      have : d ∈ ψ.ker := by rw [hk]; trivial
      exact hy this
  ·
    have hker : (MulAction.toPermHom K (K ⧸ B)).ker = ⊥ := by
      rw [← Subgroup.normalCore_eq_ker]
      rcases hK.eq_bot_or_eq_top_of_normal B.normalCore with h | h
      · exact h
      · exfalso
        have hle : (⊤ : Subgroup K) ≤ B := h ▸ Subgroup.normalCore_le B
        have : B = ⊤ := top_le_iff.mp hle
        rw [this, Subgroup.index_top] at h5
        omega
    have hinj : Function.Injective (MulAction.toPermHom K (K ⧸ B)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hKcard, Nat.card_perm] at hle
    have hq : Nat.card (K ⧸ B) = 5 := by rw [← Subgroup.index_eq_card]; exact h5
    rw [hq] at hle
    norm_num [Nat.factorial] at hle

theorem false_of_central_extension_section {K : Type*} [Group K] (Z : Subgroup K) [Z.Normal]
    (hZ : Nat.card Z = 3) (P : Subgroup K)
    (hP : Nonempty (↥(P.map (QuotientGroup.mk' Z)) ≃* Equiv.Perm (Fin 4)))
    (B : Subgroup K) (hBP : B ≤ P) {Y : Type*} [Group Y] (hcard : Nat.card Y = 504)
    (ψ : B →* Y) (hψ : Function.Surjective ψ) : False := by
  obtain ⟨e⟩ := hP
  set q : K →* K ⧸ Z := QuotientGroup.mk' Z with hq
  let f : P →* K ⧸ Z := q.comp P.subtype
  have hrange : f.range = P.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hr : Nat.card f.range = 24 := by
    rw [hrange, Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hk : Nat.card f.ker ∣ 3 := by
    rw [← hZ]
    refine Subgroup.card_dvd_of_injective
      ((P.subtype.comp f.ker.subtype).codRestrict Z fun x => ?_) ?_
    · have h := x.2
      rw [MonoidHom.mem_ker] at h
      exact (QuotientGroup.eq_one_iff _).mp h
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥Z → K) hxy))
  have hP72 : Nat.card P ∣ 72 := by
    rw [← Subgroup.card_ker_mul_card_range f, hr]
    have := Nat.mul_dvd_mul hk (dvd_refl 24)
    simpa using this
  have h504 : 504 ∣ Nat.card B := hcard ▸ Subgroup.card_dvd_of_surjective hψ
  have hBP' : Nat.card B ∣ Nat.card P := Subgroup.card_dvd_of_le hBP
  have h7 : 504 ∣ 72 := h504.trans (hBP'.trans hP72)
  omega
end CFSG.LocalAnalysis.RankThreeTheoremC
