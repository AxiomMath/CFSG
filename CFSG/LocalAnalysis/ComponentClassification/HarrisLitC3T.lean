module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3S
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3H
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUi
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3K

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut StabU DiagU OIU
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def uOne {k : Type} [Field k] : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

variable {G : Type} [Group G] {Q : Subgroup G}

theorem rowOU_x_alternative (hp2 : p ≠ 2) {x : G} (hx : x ∈ normalizer (Q : Set G))
    (e : ↥Q ⧸ center ↥Q ≃* StatedProj (StatedSU 4 (p ^ f) K))
    {θ : unitarySU p f K 4 →* ↥Q} (hθs : Function.Surjective θ)
    (hθ : ∀ s, piQ e (θ s) = thU p f K s) (hθk : θ.ker ≤ center (unitarySU p f K 4))
    (hθ1 : θ (negOneU h) = 1) (hLZ : center ↥(Lay Q x) = ⊥)
    (hrow : SelectorRowOU h (phi hx e) (Jp e x)) :
    ∀ w ∈ Lay Q x, orderOf w = 2 →
      ∃ X₁ X₂ : Subgroup G, X₁ ≠ X₂ ∧ X₁ ≤ Q ⊓ centralizer {w} ∧
        X₂ ≤ Q ⊓ centralizer {w} ∧ (X₁.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
        (X₂.subgroupOf (Q ⊓ centralizer {w})).IsSubnormal ∧
        X₁ ≤ centralizer (X₂ : Set G) ∧ X₁ ⊓ X₂ = zpowers w ∧
        IsSLTwoOver (p ^ f) ↥X₁ ∧ IsSLTwoOver (p ^ f) ↥X₂ := by
  classical
  have : Finite K := h.finite
  obtain ⟨A, -, -, δ, hδ, h2, d, P, y, -, -, -, hy, hJ⟩ := hrow
  have : Fact (¬ IsSquare (δ : h.fixedField)) := ⟨hδ⟩
  have hEcard := extension_card (δ : h.fixedField)
  have hk3 : 3 ≤ Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have h3p : 3 ≤ p := by have := h.prime.two_le; omega
    exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  have : Finite (extension (δ : h.fixedField)) := Nat.finite_of_card_ne_zero (by
    rw [hEcard]
    exact pow_ne_zero _ (by omega))
  have := Fintype.ofFinite (extension (δ : h.fixedField))
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) := by
    apply LinearGroups.special_linear_dimension_two_perfect
    have h4 : 4 ≤ Fintype.card (extension (δ : h.fixedField)) := by
      rw [← Nat.card_eq_fintype_card, hEcard]
      nlinarith
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (extension (δ : h.fixedField)))) (n := 4)
      (by rw [Finset.card_univ]; exact h4)
    exact ⟨s, hs⟩
  set lam := θ.comp y with hlam
  have hmemJ : ∀ g, piQ e (lam g) ∈ Jp e x := by
    intro g
    rw [hJ, hlam, MonoidHom.comp_apply, hθ]
    exact ⟨g, rfl⟩
  have hlamL : lam.range ≤ LQ Q x := by
    apply le_LQ_of_perfect e
    · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
        hperf.commutator_eq_top]
    · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hmemJ g
  intro w hwL hw2
  have hwQ : w ∈ Q := (Lay_le hwL).1
  set q : ↥Q := ⟨w, hwQ⟩ with hq
  have hqL : q ∈ LQ Q x := hwL
  have hqJ : piQ e q ∈ Jp e x := mem_map_of_mem _ hqL
  rw [hJ] at hqJ
  obtain ⟨g, hg⟩ := hqJ
  rw [MonoidHom.comp_apply] at hg
  have hqlam : q = lam g := by
    apply piQ_injOn e hLZ hqL (hlamL ⟨g, rfl⟩)
    rw [hlam, MonoidHom.comp_apply, hθ, hg]
  set t' := y g with ht'
  have hθt' : θ t' = q := hqlam.symm
  have hw1 : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have hw1' : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hw2
    omega
  have hq1 : q ≠ 1 := fun h1 => hw1' (congrArg Subtype.val h1)
  have hord : orderOf (thU p f K t') = 2 := by
    apply orderOf_eq_prime
    · rw [hg, pow_two, ← map_mul]
      have : q * q = 1 := Subtype.ext hw1
      rw [this, map_one]
    · intro h1
      apply hq1
      apply piQ_injOn e hLZ hqL (one_mem _)
      rw [map_one, ← hg, h1]
  have hgg := mul_self_eq_neg_one_of_involution h hp2 hδ h2 P y hy g hord
  have hy1 : y (-1) = 1 := by
    apply Subtype.ext
    rw [hy, OneMemClass.coe_one, show Umat δ h2 (-1) = 1 from rowOHom_neg_one _, map_one,
      mul_one, mul_inv_cancel]
  have htt : ((t' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (t' : GL (Fin 4) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, ht', ← map_mul, hgg, hy1, OneMemClass.coe_one,
      Units.val_one]
  have ht1 : ((t' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ 1 := by
    intro h1
    have : t' = 1 := Subtype.ext (Units.ext h1)
    rw [this, map_one] at hθt'
    exact hq1 hθt'.symm
  have htm1 : ((t' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ -1 := by
    intro h1
    have : t' = negOneU h := Subtype.ext (Units.ext (by rw [h1, coe_negOneU]))
    rw [this, hθ1] at hθt'
    exact hq1 hθt'.symm
  obtain ⟨R, s, hs0, -, hR, hXR⟩ := exists_frame_t2 h hp2 t' htt ht1 htm1
  have hk2 : (-1 : SpecialLinearGroup (Fin 2) h.fixedField) ≠ 1 := by
    intro h1
    have := congrFun (congrFun (congrArg Subtype.val h1) 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at this
    apply h2
    linear_combination -this
  have hu1 : (uOne : SpecialLinearGroup (Fin 2) h.fixedField) ≠ 1 := by
    intro h1
    have := congrFun (congrFun (congrArg Subtype.val h1) 0) 1
    simp [uOne] at this
  have hun : (uOne : SpecialLinearGroup (Fin 2) h.fixedField) ≠ -1 := by
    intro h1
    have := congrFun (congrFun (congrArg Subtype.val h1) 0) 0
    simp only [uOne, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at this
    apply h2
    linear_combination this
  have hinter : ∀ a b, θ (blU h hR a) = θ (brU h hR b) →
      (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
    intro a b hab
    apply eq_of_bl_br_scalar h hR
    rw [← hθ, ← hθ, hab]
  have hn₁ : θ (blU h hR (-1)) = θ t' ∧ θ (brU h hR (-1)) = θ t' := by
    rw [blU_neg_one h hR hXR, brU_neg_one h hR hXR, map_mul, hθ1, one_mul]
    exact ⟨rfl, rfl⟩
  obtain ⟨X₁, X₂, hne, h₁, h₂, hs₁, hs₂, hc, hi, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    x_alternative_abs hθs hθk (blU h hR) (brU h hR) (blU_comm h hR hXR) (brU_comm h hR hXR)
      (blU_mul_brU h hR) (fun n hn a => conj_mem_range_bl h hR hXR hp2 hs0 hn a)
      (fun n hn b => conj_mem_range_br h hR hXR hp2 hs0 hn b) hinter hn₁ hk2 hu1 hun
  rw [hθt'] at h₁ h₂ hs₁ hs₂ hi
  have : Fintype h.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card h.fixedField = p ^ f := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
  exact ⟨X₁, X₂, hne, h₁, h₂, hs₁, hs₂, hc, hi,
    ⟨h.fixedField, inferInstance, inferInstance, hcard, ⟨e₁⟩⟩,
    ⟨h.fixedField, inferInstance, inferInstance, hcard, ⟨e₂⟩⟩⟩

end CFSG.ComponentClassification.HarrisLit.C3
