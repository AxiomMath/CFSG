module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Nrm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Om

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G]

@[expose] def fz410Cj (n : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj n).toMonoidHom

theorem mem_fz410Cj {n x : G} {A : Subgroup G} : x ∈ fz410Cj n A ↔ n⁻¹ * x * n ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    show n⁻¹ * (n * y * n⁻¹) * n ∈ A
    rw [h]
    exact hy
  · intro hx
    refine ⟨n⁻¹ * x * n, hx, ?_⟩
    show n * (n⁻¹ * x * n) * n⁻¹ = x
    group

namespace Fz410Set

variable [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem card_Om : Nat.card (Fz410Om E P Q) = 4 :=
  fz410_card_Om D.pf.EP D.pf.PQ (fun x hx y hy => D.facts.rq x (D.str.QR hx) y hy)
    (fun x hx => D.str.ZE (D.facts.sqZ x (D.str.QR hx))) D.str.card_E D.pf.card_P D.str.card_Q

theorem W_isOm : Fz410IsOm E P Q W :=
  ⟨D.str.EW, D.str.WQ, by rw [D.str.card_W, D.str.card_E], fun h => D.t_notin_P (h D.str.t_mem)⟩

private theorem nrmQ {n : G} (hn : n ∈ fz410M R E) (x : G) : n * x * n⁻¹ ∈ Q ↔ x ∈ Q := by
  have key : ∀ m ∈ fz410M R E, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := by
    intro m hm x hxQ
    have hmR : m ∈ normalizer (R : Set G) := (Subgroup.mem_inf.mp hm).1
    have hmE : m ∈ normalizer (E : Set G) := (Subgroup.mem_inf.mp hm).2
    have hxR : x ∈ R := D.str.QR hxQ
    refine (D.facts.qc _ ((Subgroup.mem_normalizer_iff.mp hmR x).mp hxR)).mp ?_
    intro e he
    have he' : m⁻¹ * e * m ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmE) e).mp he
      simpa using this
    have hc : x * (m⁻¹ * e * m) = (m⁻¹ * e * m) * x := (D.facts.qc x hxR).mpr hxQ _ he'
    calc m * x * m⁻¹ * e = m * (x * (m⁻¹ * e * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * e * m) * x) * m⁻¹ := by rw [hc]
      _ = e * (m * x * m⁻¹) := by group
  constructor
  · intro h
    have := key n⁻¹ (Subgroup.inv_mem _ hn) _ h
    simpa [mul_assoc] using this
  · exact key n hn x

theorem isOm_conj {n : G} (hn : n ∈ fz410M R E) {A : Subgroup G} (hA : Fz410IsOm E P Q A) :
    Fz410IsOm E P Q (fz410Cj n A) := by
  have hnR : n ∈ normalizer (R : Set G) := (Subgroup.mem_inf.mp hn).1
  have hnE : n ∈ normalizer (E : Set G) := (Subgroup.mem_inf.mp hn).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_fz410Cj]
    apply hA.E_le
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnE) x).mp hx
    simpa using this
  · intro x hx
    rw [mem_fz410Cj] at hx
    have hxQ : n⁻¹ * x * n ∈ Q := hA.le_Q hx
    have := (D.nrmQ hn (n⁻¹ * x * n)).mpr hxQ
    simpa [mul_assoc] using this
  · rw [show Nat.card (fz410Cj n A) = Nat.card A from
      Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hA.card
  · intro hle
    apply hA.not_le_P
    intro x hx
    have h1 : n * x * n⁻¹ ∈ fz410Cj n A := by
      rw [mem_fz410Cj]
      simpa [mul_assoc] using hx
    exact (D.nrmP hnR x).mp (hle h1)

theorem exists_act : ∃ Φ : ↥(fz410M R E) →* Equiv.Perm (Fz410Om E P Q),
    ∀ (n : ↥(fz410M R E)) (A : Fz410Om E P Q),
      (Φ n A).1 = fz410Cj (n : G) A.1 := by
  have hcj_one : ∀ A : Subgroup G, fz410Cj 1 A = A := by
    intro A
    ext x
    rw [mem_fz410Cj]
    simp
  have hcj_mul : ∀ (n m : G) (A : Subgroup G), fz410Cj (n * m) A = fz410Cj n (fz410Cj m A) := by
    intro n m A
    ext x
    rw [mem_fz410Cj, mem_fz410Cj, mem_fz410Cj]
    have : (n * m)⁻¹ * x * (n * m) = m⁻¹ * (n⁻¹ * x * n) * m := by group
    rw [this]
  let f : ↥(fz410M R E) → Equiv.Perm (Fz410Om E P Q) := fun n =>
    { toFun := fun A => ⟨fz410Cj (n : G) A.1, D.isOm_conj n.2 A.2⟩
      invFun := fun A => ⟨fz410Cj ((n : G)⁻¹) A.1, D.isOm_conj (Subgroup.inv_mem _ n.2) A.2⟩
      left_inv := fun A => by
        apply Subtype.ext
        show fz410Cj (n : G)⁻¹ (fz410Cj (n : G) A.1) = A.1
        rw [← hcj_mul, inv_mul_cancel, hcj_one]
      right_inv := fun A => by
        apply Subtype.ext
        show fz410Cj (n : G) (fz410Cj (n : G)⁻¹ A.1) = A.1
        rw [← hcj_mul, mul_inv_cancel, hcj_one] }
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, fun n A => rfl⟩
  · exact Equiv.ext fun A => Subtype.ext (hcj_one A.1)
  · intro n m
    exact Equiv.ext fun A => Subtype.ext (hcj_mul n m A.1)

variable (Φ : ↥(fz410M R E) →* Equiv.Perm (Fz410Om E P Q))
  (hΦ : ∀ (n : ↥(fz410M R E)) (A : Fz410Om E P Q),
    (Φ n A).1 = fz410Cj (n : G) A.1)

include hΦ

theorem act_R (n : ↥(fz410M R E)) (hn : (n : G) ∈ R) : Φ n = 1 := by
  refine Equiv.ext fun A => Subtype.ext ?_
  rw [hΦ n A]
  show fz410Cj (n : G) A.1 = A.1
  have hA := A.2
  ext x
  rw [mem_fz410Cj]
  constructor
  · intro h
    have hy : (n : G)⁻¹ * x * n ∈ Q := hA.le_Q h
    have hc := D.facts.rq (n : G) hn _ hy
    have h1 : (n : G) * ((n : G)⁻¹ * x * n) * (n : G)⁻¹ * ((n : G)⁻¹ * x * n)⁻¹ =
        x * ((n : G)⁻¹ * x * n)⁻¹ := by group
    rw [h1] at hc
    have h2 := A.1.mul_mem (hA.E_le hc) h
    have h3 : x * ((n : G)⁻¹ * x * n)⁻¹ * ((n : G)⁻¹ * x * n) = x := by group
    rw [h3] at h2
    exact h2
  · intro hx
    have hxQ : x ∈ Q := hA.le_Q hx
    have hc := D.facts.rq ((n : G)⁻¹) (R.inv_mem hn) x hxQ
    have := A.1.mul_mem (hA.E_le hc) hx
    simpa [mul_assoc] using this

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
