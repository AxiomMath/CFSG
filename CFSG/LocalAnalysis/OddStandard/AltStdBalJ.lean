module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalAct
public import CFSG.LocalAnalysis.OddStandard.AltStdBalPermJ

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open scoped commutatorElement

@[expose] def J {G : Type*} [Group G] (x : G) : Prop :=
  x ∈ ⁅centralizer ({x} : Set G), centralizer ({x} : Set G)⁆

section J

variable {A G : Type*} [Group A] [Group G]

theorem J_map (f : A →* G) {x : A} (hx : J x) : J (f x) := by
  unfold J at *
  have h1 : f x ∈ (⁅centralizer ({x} : Set A), centralizer ({x} : Set A)⁆).map f :=
    Subgroup.mem_map_of_mem f hx
  rw [Subgroup.map_commutator] at h1
  have hle : (centralizer ({x} : Set A)).map f ≤ centralizer ({f x} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ centralizer ({x} : Set A) := ha
    rw [mem_centralizer_singleton_iff] at ha' ⊢
    rw [← map_mul, ← map_mul, ha']
  exact Subgroup.commutator_mono hle hle h1

theorem J_conj (g : G) {x : G} : J (g * x * g⁻¹) ↔ J x := by
  constructor
  · intro h
    have := J_map (MulAut.conj g⁻¹).toMonoidHom h
    simpa [MulAut.conj_apply, mul_assoc] using this
  · intro h
    have := J_map (MulAut.conj g).toMonoidHom h
    simpa [MulAut.conj_apply] using this

end J

section Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem J_of_mem_L (h : Setting G L n) {y : G} (hy : y ∈ L) (hy2 : orderOf y = 2) : J y := by
  obtain ⟨e⟩ := h.iso
  have ha2 : orderOf (e ⟨y, hy⟩ : alternatingGroup (Fin n)) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
  have hJ := mem_commutator_centralizer_of_involution (α := Fin n)
    (by simpa using h.hn) ha2
  have := J_map (L.subtype.comp e.symm.toMonoidHom) hJ
  simpa using this

theorem eq_one_or_eq_of_card_eq_two (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {q : G} (hq : q ∈ Q) :
    q = 1 ∨ q = z := by
  have hdvd : orderOf (⟨q, hq⟩ : Q) ∣ 2 := hQ2 ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.1 h1)
  · exact Or.inr (eq_of_orderOf_eq_two_of_isCyclic d.cyclic hq d.mem h2 d.order)

theorem commutator_centralizer_le (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤ L := by
  obtain ⟨e⟩ := h.iso
  rw [Subgroup.commutator_le]
  have hconj : ∀ x ∈ centralizer ({z} : Set G), ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun x hx l hl =>
    (mem_normalizer_iff.1 (centralizer_le_normalizer h d hx) l).1 hl
  have hcent : ∀ q ∈ Q, ∀ x ∈ centralizer ({z} : Set G), q * x = x * q := by
    intro q hq x hx
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
    · simp
    · exact ((mem_centralizer_singleton_iff.1 hx)).symm
  have caseA : ∀ c ∈ L ⊔ Q, ∀ c' ∈ centralizer ({z} : Set G), ⁅c, c'⁆ ∈ L := by
    intro c hc c' hc'
    obtain ⟨l, hl, q, hq, rfl⟩ := (mem_sup_iff_mul d).1 hc
    have h1 : q * c' * q⁻¹ = c' := by rw [hcent q hq c' hc']; group
    have h2 : ⁅l * q, c'⁆ = l * (c' * l⁻¹ * c'⁻¹) := by
      calc ⁅l * q, c'⁆ = l * (q * c' * q⁻¹) * l⁻¹ * c'⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = l * c' * l⁻¹ * c'⁻¹ := by rw [h1]
        _ = l * (c' * l⁻¹ * c'⁻¹) := by group
    rw [h2]
    exact mul_mem hl (hconj c' hc' l⁻¹ (inv_mem hl))
  intro c hc c' hc'
  by_cases hcq : c ∈ L ⊔ Q
  · exact caseA c hcq c' hc'
  by_cases hcq' : c' ∈ L ⊔ Q
  · have := caseA c' hcq' c hc
    rw [← commutatorElement_inv]
    exact inv_mem this
  have hs := signHom_eq_neg_one h d e hc hcq
  have hs' := signHom_eq_neg_one h d e hc' hcq'
  have hmem : c' * c⁻¹ ∈ L ⊔ Q := by
    have hC : c' * c⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hc' (inv_mem hc)
    rw [mem_sup_iff h d e hC]
    change signHom e h.hn (⟨c', centralizer_le_normalizer h d hc'⟩ *
      ⟨c, centralizer_le_normalizer h d hc⟩⁻¹) = 1
    rw [map_mul, map_inv, hs, hs']
    decide
  obtain ⟨l, hl, q, hq, hlq⟩ := (mem_sup_iff_mul d).1 hmem
  have hc'eq : c' = l * q * c := by rw [hlq]; group
  have hcq' : c * q * c⁻¹ = q := by rw [← hcent q hq c hc]; group
  have h2 : ⁅c, c'⁆ = (c * l * c⁻¹) * l⁻¹ := by
    calc ⁅c, c'⁆ = (c * l * c⁻¹) * (c * q * c⁻¹) * q⁻¹ * l⁻¹ := by
          rw [hc'eq]; simp only [commutatorElement_def]; group
      _ = (c * l * c⁻¹) * q * q⁻¹ * l⁻¹ := by rw [hcq']
      _ = (c * l * c⁻¹) * l⁻¹ := by group
  rw [h2]
  exact mul_mem (hconj c hc l hl) (inv_mem hl)

theorem not_J_z (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) : ¬ J z := by
  intro hJ
  obtain ⟨e⟩ := h.iso
  have hzL : z ∈ L := commutator_centralizer_le h d hQ2 hJ
  have hz1 : z = 1 :=
    eq_one_of_mem_of_mem_centralizer e (by have := h.hn; omega) hzL (d.le d.mem)
  have := d.order
  rw [hz1, orderOf_one] at this
  omega

theorem not_conj_mem_L (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) (g : G) :
    g * z * g⁻¹ ∉ L := by
  intro hg
  have h2 : orderOf (g * z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact d.order
  exact not_J_z h d hQ2 ((J_conj g).1 (J_of_mem_L h hg h2))

end Setup

end CFSG.OddStandard.AltStdBal
