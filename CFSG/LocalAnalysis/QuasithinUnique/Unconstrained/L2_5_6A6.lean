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
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Unc25G2

open MulAction

structure Sharp4 (M : Type*) [Group M] [MulAction M (Fin 11)] : Prop where
  card_eq : Nat.card M = 7920
  fix_eq_one : ∀ (g : M) {a b c d : Fin 11}, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    g • a = a → g • b = b → g • c = c → g • d = d → g = 1
  trans : ∀ x y : Fin 11, ∃ g : M, g • x = y

section Stabilizers

variable {M : Type*} [Group M] [MulAction M (Fin 11)]

theorem Sharp4.finite (h : Sharp4 M) : Finite M :=
  Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)

theorem exists_notMem_finset (s : Finset (Fin 11)) (hs : s.card < 11) : ∃ w : Fin 11, w ∉ s := by
  by_contra hcon
  have hall : ∀ w : Fin 11, w ∈ s := fun w => by
    by_contra hw
    exact hcon ⟨w, hw⟩
  have hs' : s = Finset.univ := Finset.eq_univ_of_forall hall
  rw [hs', Finset.card_univ, Fintype.card_fin] at hs
  exact lt_irrefl _ hs

theorem Sharp4.eq_of_agree (h : Sharp4 M) {s t : M} {a b c d : Fin 11} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (ha : s • a = t • a)
    (hb : s • b = t • b) (hc : s • c = t • c) (hd : s • d = t • d) : s = t := by
  have key : t⁻¹ * s = 1 := by
    refine h.fix_eq_one _ hab hac had hbc hbd hcd ?_ ?_ ?_ ?_
    · rw [mul_smul, ha, inv_smul_smul]
    · rw [mul_smul, hb, inv_smul_smul]
    · rw [mul_smul, hc, inv_smul_smul]
    · rw [mul_smul, hd, inv_smul_smul]
  exact (inv_mul_eq_one.mp key).symm

theorem smul_ne_of_fixed {t : M} {a b : Fin 11} (ht : t • a = a) (hb : b ≠ a) : t • b ≠ a := by
  intro hc
  apply hb
  apply MulAction.injective t
  show t • b = t • a
  rw [ht]
  exact hc

theorem Sharp4.card_stabilizer (h : Sharp4 M) (x : Fin 11) :
    Nat.card ↥(stabilizer M x) = 720 := by
  have := h.finite
  have h1 := Subgroup.index_mul_card (stabilizer M x)
  have h2 : orbit M x = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := h.trans x y
    exact ⟨g, hg⟩
  rw [MulAction.index_stabilizer, h2, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin, h.card_eq] at h1
  omega

theorem Sharp4.card_stab2_le (h : Sharp4 M) {x y : Fin 11} (hxy : x ≠ y) :
    Nat.card ↥(stabilizer M x ⊓ stabilizer M y) ≤ 72 := by
  classical
  have := h.finite
  obtain ⟨z, hz⟩ := exists_notMem_finset {x, y}
    (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨w, hw⟩ := exists_notMem_finset {x, y, z}
    (lt_of_le_of_lt Finset.card_le_three (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz hw
  obtain ⟨hzx, hzy⟩ := hz
  obtain ⟨hwx, hwy, hwz⟩ := hw
  set U : Finset (Fin 11) := ({x, y} : Finset (Fin 11))ᶜ with hU
  have hUc : U.card = 9 := by
    rw [hU, Finset.card_compl, Fintype.card_fin, Finset.card_pair hxy]
  have hmem : ∀ t : ↥(stabilizer M x ⊓ stabilizer M y),
      ((t : M) • z, (t : M) • w) ∈ U.offDiag := by
    intro t
    have htx : (t : M) • x = x := mem_stabilizer_iff.mp t.2.1
    have hty : (t : M) • y = y := mem_stabilizer_iff.mp t.2.2
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, ?_⟩
    · simp only [hU, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨smul_ne_of_fixed htx hzx, smul_ne_of_fixed hty hzy⟩
    · simp only [hU, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨smul_ne_of_fixed htx hwx, smul_ne_of_fixed hty hwy⟩
    · intro hc
      exact hwz (MulAction.injective (t : M) hc).symm
  let f : ↥(stabilizer M x ⊓ stabilizer M y) → ↥U.offDiag :=
    fun t => ⟨((t : M) • z, (t : M) • w), hmem t⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ hft
    have e := congrArg Subtype.val hft
    have ez : (t₁ : M) • z = (t₂ : M) • z := congrArg Prod.fst e
    have ew : (t₁ : M) • w = (t₂ : M) • w := congrArg Prod.snd e
    apply Subtype.ext
    refine h.eq_of_agree (a := x) (b := y) (c := z) (d := w) hxy (fun e => hzx e.symm)
      (fun e => hwx e.symm) (fun e => hzy e.symm) (fun e => hwy e.symm) (fun e => hwz e.symm) ?_
      ?_ ez ew
    · exact (mem_stabilizer_iff.mp t₁.2.1).trans (mem_stabilizer_iff.mp t₂.2.1).symm
    · exact (mem_stabilizer_iff.mp t₁.2.2).trans (mem_stabilizer_iff.mp t₂.2.2).symm
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card ↥U.offDiag = 72 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.offDiag_card, hUc]
  omega

theorem Sharp4.card_stab3_le (h : Sharp4 M) {x y z : Fin 11} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : Nat.card ↥(stabilizer M x ⊓ stabilizer M y ⊓ stabilizer M z) ≤ 8 := by
  classical
  have := h.finite
  obtain ⟨w, hw⟩ := exists_notMem_finset {x, y, z}
    (lt_of_le_of_lt Finset.card_le_three (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨hwx, hwy, hwz⟩ := hw
  set U : Finset (Fin 11) := ({x, y, z} : Finset (Fin 11))ᶜ with hU
  have hUc : U.card = 8 := by
    have h3 : ({x, y, z} : Finset (Fin 11)).card = 3 :=
      Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
    rw [hU, Finset.card_compl, Fintype.card_fin, h3]
  have hmem : ∀ t : ↥(stabilizer M x ⊓ stabilizer M y ⊓ stabilizer M z),
      (t : M) • w ∈ U := by
    intro t
    have htx : (t : M) • x = x := mem_stabilizer_iff.mp t.2.1.1
    have hty : (t : M) • y = y := mem_stabilizer_iff.mp t.2.1.2
    have htz : (t : M) • z = z := mem_stabilizer_iff.mp t.2.2
    simp only [hU, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨smul_ne_of_fixed htx hwx, smul_ne_of_fixed hty hwy, smul_ne_of_fixed htz hwz⟩
  let f : ↥(stabilizer M x ⊓ stabilizer M y ⊓ stabilizer M z) → ↥U :=
    fun t => ⟨(t : M) • w, hmem t⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ hft
    have ew : (t₁ : M) • w = (t₂ : M) • w := congrArg Subtype.val hft
    apply Subtype.ext
    refine h.eq_of_agree (a := x) (b := y) (c := z) (d := w) hxy hxz (fun e => hwx e.symm) hyz
      (fun e => hwy e.symm) (fun e => hwz e.symm) ?_ ?_ ?_ ew
    · exact (mem_stabilizer_iff.mp t₁.2.1.1).trans (mem_stabilizer_iff.mp t₂.2.1.1).symm
    · exact (mem_stabilizer_iff.mp t₁.2.1.2).trans (mem_stabilizer_iff.mp t₂.2.1.2).symm
    · exact (mem_stabilizer_iff.mp t₁.2.2).trans (mem_stabilizer_iff.mp t₂.2.2).symm
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card ↥U = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hUc]
  omega

end Stabilizers

section Orbits

variable {M : Type*} [Group M] [MulAction M (Fin 11)] {B : Subgroup M}

theorem six_le_index_stabilizer [IsSimpleGroup ↥B] {x : Fin 11} (hB : Nat.card ↥B = 360)
    (hx : ∃ b ∈ B, b • x ≠ x) : 6 ≤ (stabilizer ↥B x).index := by
  classical
  have : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  have hHtop : stabilizer ↥B x ≠ ⊤ := by
    intro htop
    obtain ⟨b, hb, hbx⟩ := hx
    have hmem : (⟨b, hb⟩ : ↥B) ∈ stabilizer ↥B x := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hbx (mem_stabilizer_iff.mp hmem)
  have hcore : (stabilizer ↥B x).normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (stabilizer ↥B x).normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ (stabilizer ↥B x).normalCore_le)) hHtop
  have hinj : Function.Injective (MulAction.toPermHom ↥B (↥B ⧸ stabilizer ↥B x)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    exact hcore
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  rw [hB, Nat.card_perm, ← Subgroup.index_eq_card] at hdvd
  by_contra hlt
  have hk : (stabilizer ↥B x).index < 6 := by omega
  have key : ∀ k : ℕ, k < 6 → ¬ 360 ∣ k.factorial := by decide
  exact key _ hk hdvd

theorem six_le_ncard_orbit [IsSimpleGroup ↥B] {x : Fin 11} (hB : Nat.card ↥B = 360)
    (hx : ∃ b ∈ B, b • x ≠ x) : 6 ≤ (orbit ↥B x).ncard := by
  rw [← MulAction.index_stabilizer]
  exact six_le_index_stabilizer hB hx

theorem mem_orbit_of_movable [IsSimpleGroup ↥B] (hB : Nat.card ↥B = 360) {s t : Fin 11}
    (hs : ∃ b ∈ B, b • s ≠ s) (ht : ∃ b ∈ B, b • t ≠ t) : t ∈ orbit ↥B s := by
  by_contra hts
  have h1 := six_le_ncard_orbit hB hs
  have h2 := six_le_ncard_orbit hB ht
  have hdisj : Disjoint (orbit ↥B s) (orbit ↥B t) := by
    rw [Set.disjoint_left]
    intro z hzs hzt
    apply hts
    have e1 : orbit ↥B z = orbit ↥B s := MulAction.orbit_eq_iff.mpr hzs
    have e2 : orbit ↥B z = orbit ↥B t := MulAction.orbit_eq_iff.mpr hzt
    have e3 : orbit ↥B s = orbit ↥B t := e1.symm.trans e2
    rw [e3]
    exact MulAction.mem_orbit_self t
  have hunion := Set.ncard_union_eq hdisj
  have hle : (orbit ↥B s ∪ orbit ↥B t).ncard ≤ 11 := by
    calc (orbit ↥B s ∪ orbit ↥B t).ncard ≤ (Set.univ : Set (Fin 11)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = 11 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

theorem exists_fixed [IsSimpleGroup ↥B] (hB : Nat.card ↥B = 360) :
    ∃ x : Fin 11, ∀ b ∈ B, b • x = x := by
  by_contra hcon
  have hmov : ∀ x : Fin 11, ∃ b ∈ B, b • x ≠ x := fun x => by
    by_contra hx
    exact hcon ⟨x, fun b hb => by
      by_contra hne
      exact hx ⟨b, hb, hne⟩⟩
  have horb : orbit ↥B (0 : Fin 11) = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact mem_orbit_of_movable hB (hmov 0) (hmov t)
  have h1 : (stabilizer ↥B (0 : Fin 11)).index = 11 := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have h2 := Subgroup.index_mul_card (stabilizer ↥B (0 : Fin 11))
  rw [h1, hB] at h2
  omega

end Orbits

section A6

variable {M : Type*} [Group M] [MulAction M (Fin 11)] {B : Subgroup M}

theorem Sharp4.fixed_unique (h : Sharp4 M) (hB : Nat.card ↥B = 360) {x y : Fin 11}
    (hx : ∀ b ∈ B, b • x = x) (hy : ∀ b ∈ B, b • y = y) : x = y := by
  have := h.finite
  by_contra hxy
  have hle : B ≤ stabilizer M x ⊓ stabilizer M y := fun b hb =>
    ⟨mem_stabilizer_iff.mpr (hx b hb), mem_stabilizer_iff.mpr (hy b hb)⟩
  have h1 := Subgroup.card_le_of_le hle
  have h2 := h.card_stab2_le hxy
  omega

theorem Sharp4.orbit_eq_compl (h : Sharp4 M) [IsSimpleGroup ↥B] (hB : Nat.card ↥B = 360)
    {x : Fin 11} (hx : ∀ b ∈ B, b • x = x) {o : Fin 11} (ho : o ≠ x) :
    orbit ↥B o = {t | t ≠ x} := by
  have hmov : ∀ t : Fin 11, t ≠ x → ∃ b ∈ B, b • t ≠ t := by
    intro t ht
    by_contra hcon
    have hfix : ∀ b ∈ B, b • t = t := fun b hb => by
      by_contra hne
      exact hcon ⟨b, hb, hne⟩
    exact ht (h.fixed_unique hB hfix hx)
  ext t
  constructor
  · rintro ⟨b, rfl⟩ hbx
    apply ho
    apply MulAction.injective (b : ↥B)
    rw [hbx]
    exact (hx b b.2).symm
  · intro ht
    exact mem_orbit_of_movable hB (hmov o ho) (hmov t ht)

theorem Sharp4.card_stabilizer_orbit (h : Sharp4 M) [IsSimpleGroup ↥B] (hB : Nat.card ↥B = 360)
    {x : Fin 11} (hx : ∀ b ∈ B, b • x = x) {o : Fin 11} (ho : o ≠ x) :
    Nat.card ↥(stabilizer ↥B o) = 36 := by
  have := h.finite
  have h1 := Subgroup.index_mul_card (stabilizer ↥B o)
  have hc : (orbit ↥B o).ncard = 10 := by
    rw [h.orbit_eq_compl hB hx ho]
    have : {t : Fin 11 | t ≠ x} = ↑(Finset.univ.erase x) := by
      ext t
      simp
    rw [this, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
  rw [MulAction.index_stabilizer, hc, hB] at h1
  omega

theorem Sharp4.centralizer_eq_bot (h : Sharp4 M) [IsSimpleGroup ↥B] (hB : Nat.card ↥B = 360)
    {x : Fin 11} (hx : ∀ b ∈ B, b • x = x) : Subgroup.centralizer (B : Set M) = ⊥ := by
  have := h.finite
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcomm : ∀ b ∈ B, b * c = c * b := fun b hb => Subgroup.mem_centralizer_iff.mp hc b hb
  have hcx : c • x = x := by
    refine h.fixed_unique hB (fun b hb => ?_) hx
    rw [← mul_smul, hcomm b hb, mul_smul, hx b hb]
  have hco : ∀ o : Fin 11, c • o = o := by
    intro o
    by_cases hox : o = x
    · rw [hox]
      exact hcx
    · by_contra hne
      have hcox : c • o ≠ x := by
        intro e
        apply hox
        apply MulAction.injective c
        show c • o = c • x
        rw [e, hcx]
      have hle : (stabilizer ↥B o).map B.subtype ≤
          stabilizer M x ⊓ stabilizer M o ⊓ stabilizer M (c • o) := by
        rintro _ ⟨b, hb, rfl⟩
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact mem_stabilizer_iff.mpr (hx b b.2)
        · exact mem_stabilizer_iff.mpr (mem_stabilizer_iff.mp hb)
        · refine mem_stabilizer_iff.mpr ?_
          have hbo : (b : M) • o = o := mem_stabilizer_iff.mp hb
          have hbc : (b : M) • (c • o) = c • o := by
            rw [← mul_smul, hcomm b b.2, mul_smul, hbo]
          exact hbc
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_map_of_injective B.subtype_injective, h.card_stabilizer_orbit hB hx hox]
        at h1
      have h2 := h.card_stab3_le (x := x) (y := o) (z := c • o) (fun e => hox e.symm)
        (fun e => hcox e.symm) (fun e => hne e.symm)
      omega
  exact h.fix_eq_one c (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (hco 0) (hco 1) (hco 2) (hco 3)

theorem Sharp4.normalizer_eq_stabilizer (h : Sharp4 M) [IsSimpleGroup ↥B]
    (hB : Nat.card ↥B = 360) {x : Fin 11} (hx : ∀ b ∈ B, b • x = x) :
    Subgroup.normalizer (B : Set M) = stabilizer M x := by
  have := h.finite
  apply le_antisymm
  · intro n hn
    rw [mem_stabilizer_iff]
    refine h.fixed_unique hB (fun b hb => ?_) hx
    have hb' : n⁻¹ * b * n ∈ B := by
      refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * b * n)).mpr ?_
      have e : n * (n⁻¹ * b * n) * n⁻¹ = b := by group
      rw [e]
      exact hb
    calc b • (n • x) = (b * n) • x := (mul_smul b n x).symm
      _ = (n * (n⁻¹ * b * n)) • x := by rw [mul_assoc n⁻¹, mul_inv_cancel_left]
      _ = n • ((n⁻¹ * b * n) • x) := mul_smul _ _ _
      _ = n • x := by rw [hx _ hb']
  · have hBK : B ≤ stabilizer M x := fun b hb => mem_stabilizer_iff.mpr (hx b hb)
    have hidx : (B.subgroupOf (stabilizer M x)).index = 2 := by
      have h1 := Subgroup.card_mul_index (B.subgroupOf (stabilizer M x))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hB,
        h.card_stabilizer x] at h1
      omega
    have : (B.subgroupOf (stabilizer M x)).Normal := Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mp inferInstance

theorem Sharp4.sup_eq_stabilizer (h : Sharp4 M) (hB : Nat.card ↥B = 360) {x : Fin 11}
    (hx : ∀ b ∈ B, b • x = x) {Q : Subgroup M} (hQ : Nat.card ↥Q = 16)
    (hQx : Q ≤ stabilizer M x) : B ⊔ Q = stabilizer M x := by
  have := h.finite
  have hBK : B ≤ stabilizer M x := fun b hb => mem_stabilizer_iff.mpr (hx b hb)
  have hsup : B ⊔ Q ≤ stabilizer M x := sup_le hBK hQx
  have hd1 : Nat.card ↥B ∣ Nat.card ↥(B ⊔ Q) := Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card ↥(B ⊔ Q) ∣ Nat.card ↥(stabilizer M x) := Subgroup.card_dvd_of_le hsup
  rw [hB] at hd1
  rw [h.card_stabilizer x] at hd2
  have hle : Nat.card ↥(B ⊔ Q) ≤ 720 := Nat.le_of_dvd (by norm_num) hd2
  have hpos : 0 < Nat.card ↥(B ⊔ Q) := Nat.card_pos
  have hne : Nat.card ↥(B ⊔ Q) ≠ 360 := by
    intro h360
    have hBeq : B = B ⊔ Q := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h360, hB])
    have hQB : Q ≤ B := by
      rw [hBeq]
      exact le_sup_right
    have h16 := Subgroup.card_dvd_of_le hQB
    rw [hQ, hB] at h16
    omega
  have h720 : Nat.card ↥(B ⊔ Q) = 720 := by omega
  exact Subgroup.eq_of_le_of_card_ge hsup (by rw [h720, h.card_stabilizer x])

theorem Sharp4.a6_core (h : Sharp4 M) [IsSimpleGroup ↥B] (hB : Nat.card ↥B = 360)
    {Q : Subgroup M} (hQ : Nat.card ↥Q = 16) (hQN : Q ≤ Subgroup.normalizer (B : Set M)) :
    ∃ x : Fin 11, Subgroup.normalizer (B : Set M) = stabilizer M x ∧
      Subgroup.normalizer (B : Set M) = B ⊔ Q ∧ Subgroup.centralizer (B : Set M) = ⊥ := by
  obtain ⟨x, hx⟩ := exists_fixed hB
  have hN := h.normalizer_eq_stabilizer hB hx
  refine ⟨x, hN, ?_, h.centralizer_eq_bot hB hx⟩
  rw [hN]
  exact (h.sup_eq_stabilizer hB hx hQ (hN ▸ hQN)).symm

end A6

end CFSG.QuasithinUnique.Unc25G2
