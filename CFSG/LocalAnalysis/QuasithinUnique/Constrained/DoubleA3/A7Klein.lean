module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Equiv Equiv.Perm

@[expose] def a7R : Perm (Fin 7) :=
  ⟨![1, 2, 3, 0, 5, 4, 6], ![3, 0, 1, 2, 5, 4, 6], by decide, by decide⟩

@[expose] def a7S : Perm (Fin 7) :=
  ⟨![2, 1, 0, 3, 5, 4, 6], ![2, 1, 0, 3, 5, 4, 6], by decide, by decide⟩

@[expose] def a7dl : List (Perm (Fin 7)) :=
  [1, a7R, a7R * a7R, a7R * a7R * a7R, a7S, a7S * a7R, a7S * (a7R * a7R),
    a7S * (a7R * a7R * a7R)]

@[expose] def a7mem (x : Perm (Fin 7)) : Bool := a7dl.any (fun y => decide (y = x))

theorem a7mem_iff {x : Perm (Fin 7)} : a7mem x = true ↔ x ∈ a7dl := by
  unfold a7mem
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h := of_decide_eq_true hyx
    rw [← h]
    exact hy
  · intro h
    exact ⟨x, h, decide_eq_true rfl⟩

set_option maxRecDepth 100000 in
theorem a7dl_mulB : a7dl.all (fun a => a7dl.all (fun b => a7mem (a * b))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a7dl_invB : a7dl.all (fun a => a7mem a⁻¹) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a7dl_evenB : a7dl.all (fun a => decide (Perm.sign a = 1)) = true := by
  decide +kernel

theorem a7dl_nodup : a7dl.Nodup ∧ a7dl.length = 8 := by decide +kernel

theorem a7dl_mul : ∀ a ∈ a7dl, ∀ b ∈ a7dl, a * b ∈ a7dl := by
  intro a ha b hb
  have h := a7dl_mulB
  rw [List.all_eq_true] at h
  have h2 := h a ha
  rw [List.all_eq_true] at h2
  exact a7mem_iff.mp (h2 b hb)

theorem a7dl_inv : ∀ a ∈ a7dl, a⁻¹ ∈ a7dl := by
  intro a ha
  have h := a7dl_invB
  rw [List.all_eq_true] at h
  exact a7mem_iff.mp (h a ha)

theorem a7dl_even : ∀ a ∈ a7dl, a ∈ alternatingGroup (Fin 7) := by
  intro a ha
  have h := a7dl_evenB
  rw [List.all_eq_true] at h
  rw [Equiv.Perm.mem_alternatingGroup]
  exact of_decide_eq_true (h a ha)

theorem a7dl_one : (1 : Perm (Fin 7)) ∈ a7dl := by
  unfold a7dl; exact List.mem_cons_self

@[expose] def alt7D0 : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {y | (y : Perm (Fin 7)) ∈ a7dl}
  mul_mem' := fun {a b} ha hb => by
    have := a7dl_mul _ ha _ hb
    simpa using this
  one_mem' := a7dl_one
  inv_mem' := fun {a} ha => by
    have := a7dl_inv _ ha
    simpa using this

theorem mem_alt7D0 {y : alternatingGroup (Fin 7)} : y ∈ alt7D0 ↔ (y : Perm (Fin 7)) ∈ a7dl := Iff.rfl

theorem card_alt7D0 : Nat.card alt7D0 = 8 := by
  classical
  have e : ↥alt7D0 ≃ {p : Perm (Fin 7) // p ∈ a7dl} :=
    { toFun := fun y => ⟨(y.1 : Perm (Fin 7)), y.2⟩
      invFun := fun p => ⟨⟨p.1, a7dl_even _ p.2⟩, p.2⟩
      left_inv := fun y => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  have : Fintype.card {p : Perm (Fin 7) // p ∈ a7dl} = a7dl.toFinset.card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => by simp))
  rw [this, List.toFinset_card_of_nodup a7dl_nodup.1, a7dl_nodup.2]

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem alt7_exists_conj_of_card_eight (D : Subgroup (alternatingGroup (Fin 7)))
    (hD : Nat.card D = 8) :
    ∃ g : alternatingGroup (Fin 7), ∀ x : alternatingGroup (Fin 7), x ∈ D ↔ g⁻¹ * x * g ∈ alt7D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ H : Subgroup (alternatingGroup (Fin 7)), Nat.card H = 8 → ¬ 2 ∣ H.index := by
    intro H hH h2
    have := H.card_mul_index
    rw [hH, card_alt7] at this
    omega
  have hp : ∀ H : Subgroup (alternatingGroup (Fin 7)), Nat.card H = 8 → IsPGroup 2 H := fun H hH =>
    IsPGroup.of_card (n := 3) (by rw [hH]; norm_num)
  let P : Sylow 2 (alternatingGroup (Fin 7)) := (hp D hD).toSylow (hidx D hD)
  let P₀ : Sylow 2 (alternatingGroup (Fin 7)) :=
    (hp alt7D0 card_alt7D0).toSylow (hidx alt7D0 card_alt7D0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) P₀ P
  refine ⟨g, fun x => ?_⟩
  have h1 : (g • P₀ : Sylow 2 (alternatingGroup (Fin 7))) = P := hg
  have h2 : ((g • P₀ : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup (alternatingGroup (Fin 7))) =
      (P : Subgroup (alternatingGroup (Fin 7))) := by rw [h1]
  have h3 : x ∈ (P : Subgroup (alternatingGroup (Fin 7))) ↔
      g⁻¹ * x * g ∈ (P₀ : Subgroup (alternatingGroup (Fin 7))) := by
    rw [← h2, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  exact h3

@[expose] def a7fc (a z : Perm (Fin 7)) : ℕ := Fintype.card {i : Fin 7 // a i = i ∧ z i = i}

theorem a7fc_conj (π a z : Perm (Fin 7)) : a7fc (π * a * π⁻¹) (π * z * π⁻¹) = a7fc a z := by
  unfold a7fc
  refine Fintype.card_congr (Equiv.subtypeEquiv π.symm ?_)
  intro i
  have h1 : ∀ w : Perm (Fin 7), (π * w * π⁻¹) i = i ↔ w (π.symm i) = π.symm i := by
    intro w
    simp only [Perm.mul_apply, Perm.inv_def]
    exact (Equiv.eq_symm_apply π).symm
  rw [h1, h1]

@[expose] def a7condB (a c z : Perm (Fin 7)) : Bool :=
  decide (a * a = 1) && decide (c * c = 1) && decide (z * z = 1) && decide (a * z = z * a) &&
  decide (c * z = z * c) && decide (z ≠ 1) && decide (a ≠ 1) && decide (a ≠ z) &&
  decide (c ≠ 1) && decide (c ≠ z) && decide (c ≠ a) && decide (c ≠ a * z)

set_option maxRecDepth 100000 in
theorem a7_finiteB : a7dl.all (fun a => a7dl.all (fun c => a7dl.all (fun z =>
    !(a7condB a c z) || decide (a7fc a z ≠ a7fc c z)))) = true := by
  decide +kernel

theorem alt7_no_swap (D : Subgroup (alternatingGroup (Fin 7))) (hD : Nat.card D = 8)
    (a c z : alternatingGroup (Fin 7)) (ha : a ∈ D) (hc : c ∈ D) (hz : z ∈ D)
    (ha2 : a * a = 1) (hc2 : c * c = 1) (hz2 : z * z = 1) (haz : a * z = z * a)
    (hcz : c * z = z * c) (hz1 : z ≠ 1) (ha1 : a ≠ 1) (haz' : a ≠ z) (hc1 : c ≠ 1) (hcz' : c ≠ z)
    (hca : c ≠ a) (hcaz : c ≠ a * z) (π : Perm (Fin 7))
    (hπa : π * (a : Perm (Fin 7)) * π⁻¹ = (c : Perm (Fin 7)))
    (hπz : π * (z : Perm (Fin 7)) * π⁻¹ = (z : Perm (Fin 7))) : False := by
  obtain ⟨g, hg⟩ := alt7_exists_conj_of_card_eight D hD
  set γ : Perm (Fin 7) := (g : Perm (Fin 7)) with hγ
  have mem' : ∀ y ∈ D, γ⁻¹ * (y : Perm (Fin 7)) * γ ∈ a7dl := fun y hy => by
    have := (mem_alt7D0).mp ((hg y).mp hy)
    simpa using this
  have ha2' : (a : Perm (Fin 7)) * a = 1 := by simpa using congrArg Subtype.val ha2
  have hc2' : (c : Perm (Fin 7)) * c = 1 := by simpa using congrArg Subtype.val hc2
  have hz2' : (z : Perm (Fin 7)) * z = 1 := by simpa using congrArg Subtype.val hz2
  have haz'' : (a : Perm (Fin 7)) * z = z * a := by simpa using congrArg Subtype.val haz
  have hcz'' : (c : Perm (Fin 7)) * z = z * c := by simpa using congrArg Subtype.val hcz
  have hz1' : (z : Perm (Fin 7)) ≠ 1 := fun h => hz1 (Subtype.ext (by simpa using h))
  have ha1' : (a : Perm (Fin 7)) ≠ 1 := fun h => ha1 (Subtype.ext (by simpa using h))
  have hc1' : (c : Perm (Fin 7)) ≠ 1 := fun h => hc1 (Subtype.ext (by simpa using h))
  have haz2 : (a : Perm (Fin 7)) ≠ z := fun h => haz' (Subtype.ext h)
  have hcz2 : (c : Perm (Fin 7)) ≠ z := fun h => hcz' (Subtype.ext h)
  have hca2 : (c : Perm (Fin 7)) ≠ a := fun h => hca (Subtype.ext h)
  have hcaz2 : (c : Perm (Fin 7)) ≠ (a : Perm (Fin 7)) * z := fun h =>
    hcaz (Subtype.ext (by simpa using h))
  have inj : ∀ u v : Perm (Fin 7), γ⁻¹ * u * γ = γ⁻¹ * v * γ → u = v := fun u v h => by
    have h1 : γ * (γ⁻¹ * u * γ) * γ⁻¹ = γ * (γ⁻¹ * v * γ) * γ⁻¹ := by rw [h]
    simpa [mul_assoc] using h1
  have hsp : a7fc (γ⁻¹ * (a : Perm (Fin 7)) * γ) (γ⁻¹ * (z : Perm (Fin 7)) * γ) =
      a7fc (γ⁻¹ * (c : Perm (Fin 7)) * γ) (γ⁻¹ * (z : Perm (Fin 7)) * γ) := by
    have e1 := a7fc_conj γ⁻¹ (a : Perm (Fin 7)) (z : Perm (Fin 7))
    have e2 := a7fc_conj γ⁻¹ (c : Perm (Fin 7)) (z : Perm (Fin 7))
    have e3 := a7fc_conj π (a : Perm (Fin 7)) (z : Perm (Fin 7))
    rw [inv_inv] at e1 e2
    rw [hπa, hπz] at e3
    rw [e1, e2]
    exact e3.symm
  have hall := a7_finiteB
  rw [List.all_eq_true] at hall
  have h1 := hall _ (mem' a ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 _ (mem' c hc)
  rw [List.all_eq_true] at h2
  have h3 := h2 _ (mem' z hz)
  have hcond : a7condB (γ⁻¹ * (a : Perm (Fin 7)) * γ) (γ⁻¹ * (c : Perm (Fin 7)) * γ)
      (γ⁻¹ * (z : Perm (Fin 7)) * γ) = true := by
    simp only [a7condB, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · calc γ⁻¹ * (a : Perm (Fin 7)) * γ * (γ⁻¹ * (a : Perm (Fin 7)) * γ)
          = γ⁻¹ * ((a : Perm (Fin 7)) * a) * γ := by group
        _ = 1 := by rw [ha2']; group
    · calc γ⁻¹ * (c : Perm (Fin 7)) * γ * (γ⁻¹ * (c : Perm (Fin 7)) * γ)
          = γ⁻¹ * ((c : Perm (Fin 7)) * c) * γ := by group
        _ = 1 := by rw [hc2']; group
    · calc γ⁻¹ * (z : Perm (Fin 7)) * γ * (γ⁻¹ * (z : Perm (Fin 7)) * γ)
          = γ⁻¹ * ((z : Perm (Fin 7)) * z) * γ := by group
        _ = 1 := by rw [hz2']; group
    · calc γ⁻¹ * (a : Perm (Fin 7)) * γ * (γ⁻¹ * (z : Perm (Fin 7)) * γ)
          = γ⁻¹ * ((a : Perm (Fin 7)) * z) * γ := by group
        _ = γ⁻¹ * ((z : Perm (Fin 7)) * a) * γ := by rw [haz'']
        _ = γ⁻¹ * (z : Perm (Fin 7)) * γ * (γ⁻¹ * (a : Perm (Fin 7)) * γ) := by group
    · calc γ⁻¹ * (c : Perm (Fin 7)) * γ * (γ⁻¹ * (z : Perm (Fin 7)) * γ)
          = γ⁻¹ * ((c : Perm (Fin 7)) * z) * γ := by group
        _ = γ⁻¹ * ((z : Perm (Fin 7)) * c) * γ := by rw [hcz'']
        _ = γ⁻¹ * (z : Perm (Fin 7)) * γ * (γ⁻¹ * (c : Perm (Fin 7)) * γ) := by group
    · intro h
      exact hz1' (inj _ 1 (by rw [h]; group))
    · intro h
      exact ha1' (inj _ 1 (by rw [h]; group))
    · intro h
      exact haz2 (inj _ _ h)
    · intro h
      exact hc1' (inj _ 1 (by rw [h]; group))
    · intro h
      exact hcz2 (inj _ _ h)
    · intro h
      exact hca2 (inj _ _ h)
    · intro h
      apply hcaz2
      apply inj
      rw [h]
      group
  rw [hcond] at h3
  have h4 : decide (a7fc (γ⁻¹ * (a : Perm (Fin 7)) * γ) (γ⁻¹ * (z : Perm (Fin 7)) * γ) ≠
      a7fc (γ⁻¹ * (c : Perm (Fin 7)) * γ) (γ⁻¹ * (z : Perm (Fin 7)) * γ)) = true := by
    simpa using h3
  exact (of_decide_eq_true h4) hsp

end CFSG.QuasithinUnique.DoubleA3
