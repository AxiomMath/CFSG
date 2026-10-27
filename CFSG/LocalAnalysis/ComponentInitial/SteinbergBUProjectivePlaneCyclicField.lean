module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldArith

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix CFSG.ClassicalGroups.UnitaryFlag LinearFlag UnitaryHigher

section Unitary

variable {r f : ℕ} {K : Type} [Field K]

theorem unitary_projective_nonabelian_plane_centralizer_cyclic_field_quotient
    (h : UnitaryFieldData r f K) {p a : ℕ} (hp : p.Prime) (hpa : p = 2 * a + 1) (ha : 1 ≤ a)
    (hpq : p ∣ r ^ f + 1) (hq : ¬(2 * a + 1 = 3 ∧ r ^ f = 2))
    (D : Subgroup (MulAut (hypPSU h a 1))) (hDI : D ≤ linearSimAutGroup h ha le_rfl)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcard : Nat.card D = p ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (linearSimAut h ha le_rfl), ∀ B ∈ D.comap (linearSimAut h ha le_rfl),
      A * B = B * A) :
    D ≤ centerOf (Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1)))) ∧
      Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))) ⊓ linearSimAutGroup h ha le_rfl =
        D ∧
      (∃ g ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
        ∀ x ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
          ∃ k : ℤ, g ^ k * x ∈ D) ∧
      (∀ x ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
        ∀ y ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))), x * y = y * x) ∧
      (∀ x : semilinearSimilitudes h a 1,
        autFieldPart h ha le_rfl (by omega) hq (semilinearAutHom h ha le_rfl x) =
          (x : SemiGL (HypIndex a 1) K).right) ∧
      (∀ x ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
        autFieldPart h ha le_rfl (by omega) hq x = 1 ↔ x ∈ D) ∧
      (∀ A B : linearSimilitudes h a 1,
        Subgroup.closure {linearSimAut h ha le_rfl A, linearSimAut h ha le_rfl B} = D →
        ∀ ζ : K, ((A : GL (HypIndex a 1) K) : Matrix (HypIndex a 1) (HypIndex a 1) K) *
            (B : GL (HypIndex a 1) K) =
          ζ • (((B : GL (HypIndex a 1) K) : Matrix (HypIndex a 1) (HypIndex a 1) K) *
            (A : GL (HypIndex a 1) K)) →
        ∀ x ∈ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))),
          autFieldPart h ha le_rfl (by omega) hq x ζ = ζ) ∧
      Even (orderOf (r : ZMod p)) ∧ Odd (2 * f / orderOf (r : ZMod p)) ∧
      D.relIndex (Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1)))) ∣
        2 * f / orderOf (r : ZMod p) ∧
      Odd (Nat.card (Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))))) ∧
      ∀ Y : Subgroup (MulAut (hypPSU h a 1)),
        Y ≤ Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))) →
          Nat.Coprime p (Nat.card Y) →
            IsCyclic Y ∧
              Function.Injective ((autFieldPart h ha le_rfl (by omega) hq).comp Y.subtype) ∧
              Odd (Nat.card Y) := by
  have := finite_mulAut_hypPSU h a 1
  have := h.finite
  have hn : 3 ≤ 2 * a + 1 := by omega
  have hp2 : p ≠ 2 := by omega
  set C := Subgroup.centralizer (D : Set (MulAut (hypPSU h a 1))) with hC
  set ψ := autFieldPart h ha le_rfl hn hq with hψ
  obtain ⟨-, -, hCI, hDZ, -, -, -⟩ :=
    unitary_projective_nonabelian_plane_coprime_centralizer_central h hp hpa ha
      (fun h3 => by
        have h2 : 2 ≤ r ^ f := h.one_lt_pow
        by_contra hle
        exact hq ⟨by omega, by omega⟩) D hDI hDab hDp hcard hna
  obtain ⟨-, -, hroot⟩ := linearSimAut_plane h ha le_rfl hn hp hpa.symm D hDI hDab hDp hcard hna
  have hDC : D ≤ C := fun d hd => Subgroup.mem_centralizer_iff.2 fun e he => hDab e he d hd
  have hfroot : ∀ A B : linearSimilitudes h a 1,
      Subgroup.closure {linearSimAut h ha le_rfl A, linearSimAut h ha le_rfl B} = D →
      ∀ ζ : K, ((A : GL (HypIndex a 1) K) : Matrix (HypIndex a 1) (HypIndex a 1) K) *
          (B : GL (HypIndex a 1) K) =
        ζ • (((B : GL (HypIndex a 1) K) : Matrix (HypIndex a 1) (HypIndex a 1) K) *
          (A : GL (HypIndex a 1) K)) →
      ∀ x ∈ C, ψ x ζ = ζ := by
    intro A B hAB ζ hζ x hx
    have hAD : linearSimAut h ha le_rfl A ∈ D := hAB ▸ Subgroup.subset_closure (by simp)
    have hBD : linearSimAut h ha le_rfl B ∈ D := hAB ▸ Subgroup.subset_closure (by simp)
    obtain ⟨y, rfl⟩ := semilinearAutHom_surjective_of_admissible h ha le_rfl hn hq x
    rw [hψ, autFieldPart_apply]
    exact unitary_field_root h ha le_rfl hn hζ y (Subgroup.mem_centralizer_iff.1 hx _ hAD)
      (Subgroup.mem_centralizer_iff.1 hx _ hBD)
  have hker : ∀ x ∈ C, ψ x = 1 ↔ x ∈ D := by
    intro x hx
    rw [← MonoidHom.mem_ker, hψ, ker_autFieldPart, ← hCI]
    exact ⟨fun hI => ⟨hx, hI⟩, fun hD => hD.2⟩
  have : IsCyclic (K ≃+* K) := unitaryFieldAut_isCyclic h
  obtain ⟨hcyc, hcomm, hindex, hY⟩ := centralizer_quotient_cyclic hDC hDZ hDp ψ hker
  obtain ⟨h2f, heven, hodd⟩ := order_parity hp hp2 hpq
  set d₀ := orderOf (r : ZMod p) with hd₀
  have hd₀0 : d₀ ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff] at h2f
    have := h.one_le
    omega
  obtain ⟨d, hd, e, he, hde⟩ :=
    CFSG.LinearAlgebra.ProjectivePrimePlane.exists_closure_pair_eq hp hDp hcard
  obtain ⟨A, rfl⟩ := hDI hd
  obtain ⟨B, rfl⟩ := hDI he
  obtain ⟨ζ, hζ, hAB⟩ := hroot A B hde
  obtain ⟨φ, hφ, hφord, hφtop, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality h.prime
      (by have := h.one_le; omega) h.card
  have hrel : D.relIndex C ∣ 2 * f / d₀ := by
    rw [hindex, ← card_zpowers_frobenius_pow hφord hd₀0 h2f]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_zpowers_of_fix hφ hφtop h.prime.one_lt.le hζ hp.one_lt.le
      (hfroot A B hde ζ hAB x hx)
  have hCodd : Odd (Nat.card C) := by
    have h1 := (D.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hcard] at h1
    rw [← h1]
    exact ((hp.odd_of_ne_two hp2).pow).mul (hodd.of_dvd_nat hrel)
  refine ⟨hDZ, hCI, hcyc, hcomm, fun x => autFieldPart_apply h ha le_rfl hn hq x, hker, hfroot,
    heven, hodd, hrel, hCodd, fun Y hYC hYp => ?_⟩
  obtain ⟨hYc, hYinj⟩ := hY Y hYC hYp
  exact ⟨hYc, hYinj, hCodd.of_dvd_nat (Subgroup.card_dvd_of_le hYC)⟩

end Unitary

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
