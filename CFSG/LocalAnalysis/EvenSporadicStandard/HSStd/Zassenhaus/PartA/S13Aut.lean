module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFullness

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath
open scoped commutatorElement
variable {K : Type*} [Group K]

theorem commutator_mul_central_S13 {d d' z z' : K} (hz : z ∈ center K)
    (hz' : z' ∈ center K) : ⁅d * z, d' * z'⁆ = ⁅d, d'⁆ := by
  have h1 : Commute z (d' * z') := (mem_center_iff.1 hz _).symm
  have h2 : Commute d z' := (mem_center_iff.1 hz' _)
  rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, h2.commutator_eq]
  simp

theorem eq_of_forall_mem_center (hK : commutator K = ⊤) (φ ψ : K →* K)
    (h : ∀ g, (φ g)⁻¹ * ψ g ∈ center K) : φ = ψ := by
  have hle : commutator K ≤ MonoidHom.eqLocus φ ψ := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨g, g', rfl⟩
    have hg := h g
    have hg' := h g'
    have e1 : ψ g = φ g * ((φ g)⁻¹ * ψ g) := by group
    have e2 : ψ g' = φ g' * ((φ g')⁻¹ * ψ g') := by group
    show φ ⁅g, g'⁆ = ψ ⁅g, g'⁆
    rw [map_commutatorElement, map_commutatorElement, e1, e2, commutator_mul_central_S13 hg hg']
  rw [hK] at hle
  ext g
  exact hle (mem_top g)

@[expose] noncomputable def autQuot (K : Type*) [Group K] : MulAut K →* MulAut (K ⧸ center K) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H x => simp
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with | H x => simp

theorem autQuot_mk (φ : MulAut K) (x : K) :
    autQuot K φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ _ (Subgroup.map_center_eq φ) x

theorem autQuot_injective (hK : commutator K = ⊤) : Function.Injective (autQuot K) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have h : ∀ g, (g : K)⁻¹ * φ g ∈ center K := by
    intro g
    have := DFunLike.congr_fun hφ (QuotientGroup.mk g)
    rw [autQuot_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this.symm
  have := eq_of_forall_mem_center hK (MonoidHom.id K) φ.toMonoidHom h
  ext g
  exact (DFunLike.congr_fun this g).symm

theorem autQuot_bijective [Finite K] (hK : commutator K = ⊤)
    (h : Nat.card (MulAut (K ⧸ center K)) ≤ Nat.card (MulAut K)) :
    Function.Bijective (autQuot K) :=
  (autQuot_injective hK).bijective_of_nat_card_le h

@[expose] noncomputable def autEquiv {S : Type*} [Group S] [Finite K] (hK : commutator K = ⊤)
    (e : K ⧸ center K ≃* S) (h : Nat.card (MulAut S) ≤ Nat.card (MulAut K)) :
    MulAut K ≃* MulAut S :=
  (MulEquiv.ofBijective (autQuot K) (autQuot_bijective hK (by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]; exact h))).trans (MulAut.congr e)

theorem card_mulAut_le_of_perfect [Finite K] {S : Type*} [Group S] (hK : commutator K = ⊤)
    (e : K ⧸ center K ≃* S) : Nat.card (MulAut K) ≤ Nat.card (MulAut S) := by
  rw [← Nat.card_congr (MulAut.congr e).toEquiv]
  exact Nat.card_le_card_of_injective _ (autQuot_injective hK)

section Transfer

variable {A B : Type*} [Group A] [Group B]

theorem card_centralizer_le_of_equiv (Φ : A ≃* B) [Finite B] (m : ℕ) (a : A)
    (h : Nat.card (centralizer ({Φ a} : Set B)) ≤ m) : Nat.card (centralizer ({a} : Set A)) ≤ m := by
  refine le_trans ?_ h
  rw [← Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective]
  refine Subgroup.card_le_of_le ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x * a = a * x := mem_centralizer_singleton_iff.1 hx
  rw [mem_centralizer_singleton_iff]
  show Φ x * Φ a = Φ a * Φ x
  rw [← map_mul, ← map_mul, hx']

theorem closure_involutions_of_equiv (Φ : A ≃* B)
    (h : Subgroup.closure {b : B | b * b = 1} = ⊤) :
    Subgroup.closure {a : A | a * a = 1} = ⊤ := by
  have h1 : Subgroup.closure {b : B | b * b = 1} ≤
      (Subgroup.closure {a : A | a * a = 1}).map Φ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro b hb
    refine ⟨Φ.symm b, Subgroup.subset_closure ?_, by simp⟩
    show Φ.symm b * Φ.symm b = 1
    rw [← map_mul, show b * b = 1 from hb, map_one]
  rw [h, top_le_iff] at h1
  rw [eq_top_iff]
  intro a _
  have : Φ a ∈ (Subgroup.closure {a : A | a * a = 1}).map Φ.toMonoidHom := h1 ▸ mem_top _
  obtain ⟨c, hc, hca⟩ := this
  have : c = a := Φ.injective hca
  exact this ▸ hc

end Transfer

section Diag

variable {A : Type*} [Group A] [Finite A]

theorem diag_cover (hA : Nat.card A ≤ 1440) (R : Subgroup (Wr2 A)) (hR : Nat.card R = 1440)
    (hRc : R ≤ centralizer ({tau} : Set (Wr2 A))) (hτ : (tau : Wr2 A) ∉ R) :
    Nat.card A = 1440 ∧ ∀ d : A, base d d ∈ R ∨ base d d * tau ∈ R := by
  have hτc : (tau : Wr2 A) ∈ centralizer ({tau} : Set (Wr2 A)) :=
    mem_centralizer_singleton_iff.2 rfl
  set C : Subgroup (Wr2 A) := R ⊔ zpowers tau with hC
  have hCQ : C ≤ centralizer ({tau} : Set (Wr2 A)) :=
    sup_le hRc ((zpowers_le).2 hτc)
  have h2 : 2 * Nat.card R ≤ Nat.card C :=
    two_mul_card_le_of_exists (le_sup_left) ⟨tau, mem_sup_right (mem_zpowers _), hτ⟩
  have hQ : Nat.card (centralizer ({tau} : Set (Wr2 A))) = 2 * Nat.card A := card_centralizer_tau
  have hCQ' := Subgroup.card_le_of_le hCQ
  have hA' : Nat.card A = 1440 := by omega
  refine ⟨hA', fun d => ?_⟩
  have hEq : C = centralizer ({tau} : Set (Wr2 A)) :=
    Subgroup.eq_of_le_of_card_ge hCQ (by omega)
  have hd : base d d ∈ C := by
    rw [hEq]; exact (mem_centralizer_tau_iff d d).2 rfl
  rcases mem_or_inv_mul_mem_of_mem_sup_zpowers (A := R) (t := tau) tau_mul_tau
    (fun a ha => (mem_centralizer_singleton_iff.1 (hRc ha))) hd with h | h
  · exact Or.inl h
  · right
    rw [tau_inv] at h
    have hc : base d d * tau = tau * base d d :=
      mem_centralizer_singleton_iff.1 ((mem_centralizer_tau_iff d d).2 rfl)
    rw [hc]; exact h

end Diag

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
