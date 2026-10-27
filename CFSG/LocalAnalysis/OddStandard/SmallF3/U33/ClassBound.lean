module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

variable {Γ : Type*} [Group Γ]

theorem card_inf_centralizer_mul_le (P : Subgroup Γ) [Finite P] (z : Γ) (ws : List Γ)
    (hws : ∀ w ∈ ws, w ∈ P) (hnd : (ws.map fun w => w * z * w⁻¹).Nodup) :
    ws.length * Nat.card ↥(P ⊓ Subgroup.centralizer ({z} : Set Γ)) ≤ Nat.card P := by
  classical
  let C : Subgroup Γ := P ⊓ Subgroup.centralizer ({z} : Set Γ)
  let C' : Subgroup ↥P := C.subgroupOf P
  have hCP : C ≤ P := inf_le_left
  have hcardC : Nat.card ↥C' = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCP).toEquiv
  let g : Γ → Γ := fun w => w * z * w⁻¹
  have hndg : (ws.map g).Nodup := hnd
  let f : Fin ws.length → ↥P ⧸ C' := fun i =>
    QuotientGroup.mk (s := C') ⟨ws[i.1], hws _ (List.getElem_mem i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    let a : ↥P := ⟨ws[i.1], hws _ (List.getElem_mem i.2)⟩
    let b : ↥P := ⟨ws[j.1], hws _ (List.getElem_mem j.2)⟩
    have hmem : a⁻¹ * b ∈ C' := QuotientGroup.eq.mp hij
    have hCmem : ((a⁻¹ * b : ↥P) : Γ) ∈ C := Subgroup.mem_subgroupOf.mp hmem
    have hcent : ((a⁻¹ * b : ↥P) : Γ) ∈ Subgroup.centralizer ({z} : Set Γ) :=
      (Subgroup.mem_inf.mp hCmem).2
    have hcomm : ((a⁻¹ * b : ↥P) : Γ) * z = z * ((a⁻¹ * b : ↥P) : Γ) :=
      Subgroup.mem_centralizer_singleton_iff.mp hcent
    have hcoe : ((a⁻¹ * b : ↥P) : Γ) = (ws[i.1])⁻¹ * ws[j.1] := by
      simp [a, b]
    have heq : ws[i.1] * z * ws[i.1]⁻¹ = ws[j.1] * z * ws[j.1]⁻¹ := by
      rw [hcoe] at hcomm
      have h1 : ws[j.1] * z = ws[i.1] * z * ws[i.1]⁻¹ * ws[j.1] := by
        calc ws[j.1] * z = (ws[i.1] * ((ws[i.1])⁻¹ * ws[j.1])) * z := by
              rw [mul_inv_cancel_left]
          _ = ws[i.1] * ((ws[i.1])⁻¹ * ws[j.1] * z) := by rw [mul_assoc]
          _ = ws[i.1] * (z * ((ws[i.1])⁻¹ * ws[j.1])) := by rw [hcomm]
          _ = ws[i.1] * z * ws[i.1]⁻¹ * ws[j.1] := by rw [← mul_assoc, ← mul_assoc]
      have h2 : ws[j.1] * z * ws[j.1]⁻¹ = ws[i.1] * z * ws[i.1]⁻¹ := by
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      exact h2.symm
    have hmem_eq : ws[i.1] = ws[j.1] :=
      List.inj_on_of_nodup_map hndg (List.getElem_mem i.2) (List.getElem_mem j.2) heq
    have hwsnd : ws.Nodup := List.Nodup.of_map g hndg
    exact Fin.ext (hwsnd.getElem_inj_iff.mp hmem_eq)
  have hlen : ws.length ≤ Nat.card (↥P ⧸ C') := by
    have h := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_fin] using h
  calc ws.length * Nat.card ↥C
      = ws.length * Nat.card ↥C' := by rw [← hcardC]
    _ ≤ Nat.card (↥P ⧸ C') * Nat.card ↥C' := Nat.mul_le_mul_right _ hlen
    _ = Nat.card ↥P := (Subgroup.card_eq_card_quotient_mul_card_subgroup C').symm

theorem length_le_card_of_nodup (H : Subgroup Γ) [Finite H] (l : List Γ) (hl : ∀ g ∈ l, g ∈ H)
    (hnd : l.Nodup) : l.length ≤ Nat.card H := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  rw [← List.toFinset_card_of_nodup hnd, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.card_map (Function.Embedding.subtype (· ∈ H))]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_map]
  exact ⟨⟨x, hl x (List.mem_toFinset.mp hx)⟩, Finset.mem_univ _, rfl⟩

theorem mem_iff_of_card_le (H : Subgroup Γ) [Finite H] (l : List Γ) (hl : ∀ g ∈ l, g ∈ H)
    (hnd : l.Nodup) (hcard : Nat.card H ≤ l.length) : ∀ g, g ∈ H ↔ g ∈ l := by
  classical
  have hHncard : Nat.card H = (H : Set Γ).ncard := by
    simpa using Nat.card_coe_set_eq (H : Set Γ)
  have hlcard : (l.toFinset : Set Γ).ncard = l.length := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  have hsub : (l.toFinset : Set Γ) ⊆ (H : Set Γ) :=
    fun x hx => hl x (List.mem_toFinset.mp hx)
  have hcard' : (H : Set Γ).ncard ≤ (l.toFinset : Set Γ).ncard := by
    rw [← hHncard, hlcard]
    exact hcard
  have hset : (l.toFinset : Set Γ) = (H : Set Γ) :=
    Set.eq_of_subset_of_ncard_le hsub hcard'
  intro g
  have : g ∈ (l.toFinset : Set Γ) ↔ g ∈ (H : Set Γ) := by rw [hset]
  simpa using this.symm

@[expose] def permTab {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map fun i => (σ i).val

theorem permTab_injective {n : ℕ} : Function.Injective (permTab : Equiv.Perm (Fin n) → List ℕ) := by
  intro σ τ h
  have hF : (fun i : Fin n => (σ i).val) = fun i : Fin n => (τ i).val := by
    apply List.ofFn_injective
    simpa [permTab, List.ofFn_eq_map] using h
  exact Equiv.ext fun i => Fin.ext (congrFun hF i)

theorem nodup_of_nodup_permTab {n : ℕ} (l : List (Equiv.Perm (Fin n)))
    (h : (l.map permTab).Nodup) : l.Nodup := by
  exact List.Nodup.of_map permTab h

end CFSG.OddStandard.SmallF3.HarrisU33
