module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.Dichotomy
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem LayerData.commutes_of_oddCore {L B : Subgroup X} [L.Normal] {a : X} {P : Subgroup X}
    (h : LayerData L B a P) {n : X} (hn : n ∈ involutionOddCore a) {p : X} (hp : p ∈ P) :
    n * p = p * n := by
  set N : Subgroup X := involutionOddCore a with hN
  set M : Subgroup X := N ⊓ L with hM
  have hMle : M ≤ L ⊓ Subgroup.centralizer ({a} : Set X) :=
    fun x hx => ⟨hx.2, involutionOddCore_le_centralizer' a hx.1⟩
  have hMnorm : ∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set X), ∀ m ∈ M, x * m * x⁻¹ ∈ M :=
    fun x hx m hm => ⟨conj_mem_involutionOddCore a hx.2 hm.1,
      L.mul_mem (L.mul_mem hx.1 hm.2) (L.inv_mem hx.1)⟩
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat (odd_natCard_involutionOddCore a) (Subgroup.card_dvd_of_le inf_le_left)
  have hMP : ⁅M, P⁆ = ⊥ := h.commutator_eq_bot hMle hMnorm hModd
  have hNPM : ⁅N, P⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g hg q hq
    refine ⟨?_, ?_⟩
    · have e : (⁅g, q⁆ : X) = g * (q * g⁻¹ * q⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem hg
        (conj_mem_involutionOddCore a (h.le hq).2 (N.inv_mem hg))
    · have e : (⁅g, q⁆ : X) = (g * q * g⁻¹) * q⁻¹ := commutatorElement_def g q
      rw [e]
      exact L.mul_mem (Subgroup.Normal.conj_mem ‹L.Normal› q (h.le hq).1 g)
        (L.inv_mem (h.le hq).1)
  have h1 : ⁅⁅N, P⁆, P⁆ = ⊥ := eq_bot_iff.mpr ((Subgroup.commutator_mono hNPM le_rfl).trans hMP.le)
  have h2 : ⁅⁅P, N⁆, P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm P N]
    exact h1
  have h3 : ⁅⁅P, P⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  have h4 : ⁅P, N⁆ = ⊥ := eq_bot_iff.mpr ((Subgroup.commutator_mono h.perf le_rfl).trans h3.le)
  exact (comm_of_commutator_eq_bot h4 hp hn).symm

theorem alphaOf_klein_outer (L : Subgroup X) [L.Normal] {z y : X} (hz2 : z * z = 1)
    (hy2 : y * y = 1) (hzy : z * y = y * z) (hz1 : z ≠ 1) (hy1 : y ≠ 1) (hzy1 : z * y ≠ 1)
    {P₁ P₂ : Subgroup X}
    (d₁ : LayerData L (Subgroup.closure ({z, y} : Set X)) y P₁)
    (d₂ : LayerData L (Subgroup.closure ({z, y} : Set X)) (z * y) P₂)
    (hN : ∀ n ∈ involutionOddCore z, n * y = y * n)
    (hrig : ∀ x : X, Odd (orderOf x) → (∀ p ∈ P₁, x * p = p * x) →
      (∀ p ∈ P₂, x * p = p * x) → x = 1) :
    alphaOf (Subgroup.closure ({z, y} : Set X)) = ⊥ := by
  classical
  set B : Subgroup X := Subgroup.closure ({z, y} : Set X) with hB
  have hBmem := fun {b : X} (hb : b ∈ B) => klein_mem_closure hz2 hy2 hzy hb
  have hzB : z ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyB : y ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzyB : z * y ∈ B := B.mul_mem hzB hyB
  have hcommB : ∀ n : X, n * z = z * n → n * y = y * n → ∀ b ∈ B, n * b = b * n := by
    intro n hnz hny b hb
    rcases hBmem hb with rfl | rfl | rfl | rfl
    · simp
    · exact hnz
    · exact hny
    · rw [← mul_assoc, hnz, mul_assoc, hny, ← mul_assoc]
  have hcover : ∀ {a : X} {P : Subgroup X}, B ≤ Subgroup.zpowers a ⊔ P →
      ∀ n : X, n * a = a * n → (∀ p ∈ P, n * p = p * n) → ∀ b ∈ B, n * b = b * n := by
    intro a P hBP n hna hnP b hb
    have hle : Subgroup.zpowers a ⊔ P ≤ Subgroup.centralizer ({n} : Set X) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y' hy'
        rw [Set.mem_singleton_iff] at hy'
        subst hy'
        exact hna
      · intro p hp
        rw [Subgroup.mem_centralizer_iff]
        intro y' hy'
        rw [Set.mem_singleton_iff] at hy'
        subst hy'
        exact hnP p hp
    have := hle (hBP hb)
    rw [Subgroup.mem_centralizer_iff] at this
    exact this n rfl
  have hcent_y : ∀ n ∈ involutionOddCore y, ∀ b ∈ B, n * b = b * n := fun n hn =>
    hcover d₁.cover n (Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer' y hn))
      (fun p hp => d₁.commutes_of_oddCore hn hp)
  have hcent_zy : ∀ n ∈ involutionOddCore (z * y), ∀ b ∈ B, n * b = b * n := fun n hn =>
    hcover d₂.cover n (Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer' (z * y) hn))
      (fun p hp => d₂.commutes_of_oddCore hn hp)
  have hcent_z : ∀ n ∈ involutionOddCore z, ∀ b ∈ B, n * b = b * n := fun n hn =>
    hcommB n (Subgroup.mem_centralizer_singleton_iff.mp
      (involutionOddCore_le_centralizer' z hn)) (hN n hn)
  refine (alphaOf_eq_bot_iff B).mpr ⟨?_, ?_⟩
  · intro a ha ha1
    rcases hBmem ha with rfl | rfl | rfl | rfl
    · exact absurd rfl ha1
    · exact commutator_eq_bot_of_comm fun g hg b hb => hcent_z g hg b hb
    · exact commutator_eq_bot_of_comm fun g hg b hb => hcent_y g hg b hb
    · exact commutator_eq_bot_of_comm fun g hg b hb => hcent_zy g hg b hb
  · refine eq_bot_iff.mpr fun x hx => ?_
    rw [Subgroup.mem_bot]
    have hxy : x ∈ involutionOddCore y := by
      have := Subgroup.mem_iInf.mp hx y
      have := Subgroup.mem_iInf.mp this hyB
      exact (Subgroup.mem_iInf.mp this hy1)
    have hxzy : x ∈ involutionOddCore (z * y) := by
      have := Subgroup.mem_iInf.mp hx (z * y)
      have := Subgroup.mem_iInf.mp this hzyB
      exact (Subgroup.mem_iInf.mp this hzy1)
    exact hrig x (Odd.of_dvd_nat (odd_natCard_involutionOddCore y)
        (Subgroup.orderOf_dvd_natCard _ hxy))
      (fun p hp => d₁.commutes_of_oddCore hxy hp) (fun p hp => d₂.commutes_of_oddCore hxzy hp)

end CFSG.ClassicalInvolution.ModelFacts.Orth15
