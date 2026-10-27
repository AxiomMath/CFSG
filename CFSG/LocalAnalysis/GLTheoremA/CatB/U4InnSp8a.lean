module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

open CFSG.Open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Commuting

variable {G : Type*} [Group G] {P Q : Subgroup G}

theorem le_normalizer_of_commute (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) :
    P ≤ Subgroup.normalizer (Q : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have hc : ∀ c ∈ Q, a * c * a⁻¹ = c := fun c hc => by
    rw [h a ha c hc, mul_inv_cancel_right]
  constructor
  · intro hb
    rw [hc b hb]; exact hb
  · intro hb
    have h5 : a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = a * b * a⁻¹ := by
      rw [h a⁻¹ (P.inv_mem ha) _ hb, mul_inv_cancel_right]
    rw [inv_inv] at h5
    have h2 : a⁻¹ * (a * b * a⁻¹) * a = b := by group
    rw [h2] at h5
    rw [h5]; exact hb

theorem exists_mul_of_mem_sup (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G} (hx : x ∈ P ⊔ Q) :
    ∃ a ∈ P, ∃ b ∈ Q, x = a * b := by
  have h1 := Subgroup.coe_mul_of_left_le_normalizer_right P Q (le_normalizer_of_commute h)
  have hx' : x ∈ ((P ⊔ Q : Subgroup G) : Set G) := hx
  rw [h1] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem conj_mem_of_mem_sup (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G} (hx : x ∈ P ⊔ Q)
    {k : G} (hk : k ∈ P) : x * k * x⁻¹ ∈ P := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup h hx
  have hbk : k * b = b * k := h k hk b hb
  have : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
    calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
      _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [hbk]
      _ = a * k * a⁻¹ := by group
  rw [this]
  exact P.mul_mem (P.mul_mem ha hk) (P.inv_mem ha)

theorem card_sup_le [Finite G] (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) :
    Nat.card ↥(P ⊔ Q) ≤ Nat.card ↥P * Nat.card ↥Q := by
  let f : ↥P × ↥Q → ↥(P ⊔ Q) := fun ab =>
    ⟨(ab.1 : G) * ab.2, Subgroup.mul_mem_sup ab.1.2 ab.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup h hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

end Commuting

noncomputable def q2 : (ZMod 2)[X] := X ^ 2 + X + 1

theorem natDegree_q2 : q2.natDegree = 2 := by
  unfold q2
  compute_degree!

theorem monic_q2 : q2.Monic := by
  unfold q2
  monicity!

theorem q2_irreducible : Irreducible q2 := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_q2]; decide
  · intro x hx
    have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases h01 x with rfl | rfl <;> simp [q2, IsRoot.def] at hx <;> revert hx <;> decide

theorem X_pow_three_sub_one : (X ^ 3 - 1 : (ZMod 2)[X]) = (X - 1) * q2 := by
  unfold q2; ring

theorem q2_ne_X_sub_one : q2 ≠ X - 1 := by
  intro h
  have h1 : (X - 1 : (ZMod 2)[X]).natDegree = 1 := by compute_degree!
  have := congrArg Polynomial.natDegree h
  rw [natDegree_q2, h1] at this
  omega

theorem mem_primaryFactors_pow_three {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {y : Module.End (ZMod 2) V} (hy : y ^ 3 = 1)
    {h : (ZMod 2)[X]} (hh : h ∈ primaryFactors y) : h = X - 1 ∨ h = q2 := by
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.mp hh
  have hX : minpoly (ZMod 2) y ∣ (X - 1) * q2 := by
    rw [← X_pow_three_sub_one]
    exact minpoly.dvd (ZMod 2) y (by simp [hy])
  rcases hirr.prime.dvd_or_dvd (hdvd.trans hX) with hd | hd
  · left
    exact eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one hd)
  · right
    exact eq_of_monic_of_associated hmon monic_q2 (hirr.associated_of_dvd q2_irreducible hd)

theorem proj_injective_two : Function.Injective (proj 4 (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj, ← Subgroup.card_eq_one,
    card_spScalars_eq_gcd (ZMod 2) (r := 4) (by norm_num)]
  simp [Nat.card_zmod]

theorem sp8_blocks (s : StatedSp 4 (ZMod 2)) (hs : orderOf s = 3) :
    SpPrimaryBlocks 2 1 3 s (proj 4 (ZMod 2) s) := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp [Nat.card_zmod]
  have ha : orderOf (proj 4 (ZMod 2) s) = 3 := by
    rw [orderOf_injective _ proj_injective_two s, hs]
  exact (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two le_rfl hK
    Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (proj 4 (ZMod 2) s) ha).2 s rfl hs

end CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

end
