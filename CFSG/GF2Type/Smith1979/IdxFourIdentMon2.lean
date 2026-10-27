module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMon
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

namespace MonAux

theorem permE_mul_diagE (π : Equiv.Perm (Fin 6)) (c : Fin 6 → ZMod 3) :
    permE π * diagE c = diagE (fun i => c (π.symm i)) * permE π := by
  rw [← permE_mul_diagE_mul_inv, inv_mul_cancel_right]

theorem frobE_mul_diagE (c : Fin 6 → ZMod 3) : frobE * diagE c = diagE (-c) * frobE := by
  rw [← frobE_mul_diagE_mul_inv, inv_mul_cancel_right]

theorem mon_mul (c c' : Fin 6 → ZMod 3) (π π' : Equiv.Perm (Fin 6)) :
    diagE c * permE π * (diagE c' * permE π') =
      diagE (c + fun i => c' (π.symm i)) * permE (π * π') := by
  rw [diagE_add, permE_mul, mul_assoc, ← mul_assoc (permE π), permE_mul_diagE]
  simp only [mul_assoc]

theorem mon_inv (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) :
    (diagE c * permE π)⁻¹ = diagE (fun i => -c (π i)) * permE π⁻¹ := by
  rw [mul_inv_rev, diagE_inv, permE_inv, permE_mul_diagE]
  rfl

theorem mon_inj0 {c c' : Fin 6 → ZMod 3} {π π' : Equiv.Perm (Fin 6)}
    (h : diagE c * permE π = diagE c' * permE π') : c = c' ∧ π = π' := by
  have h' : diagE c * permE π * frobE ^ (0 : ZMod 2).val =
      diagE c' * permE π' * frobE ^ (0 : ZMod 2).val := by
    rw [frobPow_zero, mul_one, mul_one]
    exact h
  obtain ⟨h1, h2, -⟩ := mon_inj h'
  exact ⟨h1, h2⟩

theorem sum_mon_mul {c c' : Fin 6 → ZMod 3} (π : Equiv.Perm (Fin 6)) :
    ∑ i, (c + fun i => c' (π.symm i)) i = ∑ i, c i + ∑ i, c' i := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [Equiv.sum_comp π.symm c']

theorem sum_mon_inv (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) :
    ∑ i, (fun i => -c (π i)) i = -∑ i, c i := by
  rw [Finset.sum_neg_distrib, Equiv.sum_comp π c]

theorem frobPow_mul_mon (ε : ZMod 2) (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) :
    ∃ d : Fin 6 → ZMod 3, (∑ i, c i = 0 → ∑ i, d i = 0) ∧
      frobE ^ ε.val * (diagE c * permE π) = diagE d * permE π * frobE ^ ε.val := by
  rcases zmod2_cases ε with rfl | rfl
  · exact ⟨c, id, by rw [frobPow_zero, one_mul, mul_one]⟩
  · refine ⟨-c, fun hc => by simp [Finset.sum_neg_distrib, hc], ?_⟩
    rw [frobPow_one, ← mul_assoc, frobE_mul_diagE, mul_assoc, frobE_mul_permE, ← mul_assoc]

theorem frobPow_mul_frobPow (ε ε' : ZMod 2) :
    frobE ^ ε.val * frobE ^ ε'.val = frobE ^ (ε + ε').val := by
  rcases zmod2_cases ε with rfl | rfl <;> rcases zmod2_cases ε' with rfl | rfl
  · rw [add_zero, frobPow_zero, mul_one]
  · rw [zero_add, frobPow_zero, one_mul]
  · rw [add_zero, frobPow_zero, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, frobPow_one, frobPow_zero, frobE_mul_self]

noncomputable def linC (g : monLin) : Fin 6 → ZMod 3 := (mem_monLin_iff.1 g.2).choose

noncomputable def linP (g : monLin) : Equiv.Perm (Fin 6) :=
  (mem_monLin_iff.1 g.2).choose_spec.choose

theorem linC_linP (g : monLin) : (g : G12) = diagE (linC g) * permE (linP g) :=
  (mem_monLin_iff.1 g.2).choose_spec.choose_spec

theorem linC_linP_eq {g : monLin} {c : Fin 6 → ZMod 3} {π : Equiv.Perm (Fin 6)}
    (h : (g : G12) = diagE c * permE π) : linC g = c ∧ linP g = π :=
  mon_inj0 ((linC_linP g).symm.trans h)

theorem linC_linP_mul (g g' : monLin) :
    linC (g * g') = (linC g + fun i => linC g' ((linP g).symm i)) ∧
      linP (g * g') = linP g * linP g' :=
  linC_linP_eq (by rw [Subgroup.coe_mul, linC_linP g, linC_linP g', mon_mul])

end MonAux

open MonAux

noncomputable def permHom : monLin →* Equiv.Perm (Fin 6) :=
  MonoidHom.mk' linP fun g g' => (linC_linP_mul g g').2

theorem permHom_apply {g : monLin} {c : Fin 6 → ZMod 3} {π : Equiv.Perm (Fin 6)}
    (h : (g : G12) = diagE c * permE π) : permHom g = π :=
  (linC_linP_eq h).2

noncomputable def sumHom : monLin →* Multiplicative (ZMod 3) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (∑ i, linC g i)) fun g g' => by
    rw [(linC_linP_mul g g').1, sum_mon_mul, ofAdd_add]

theorem sumHom_apply {g : monLin} {c : Fin 6 → ZMod 3} {π : Equiv.Perm (Fin 6)}
    (h : (g : G12) = diagE c * permE π) : sumHom g = Multiplicative.ofAdd (∑ i, c i) := by
  show Multiplicative.ofAdd (∑ i, linC g i) = _
  rw [(linC_linP_eq h).1]

@[expose] def R0 : Subgroup G12 where
  carrier := {g | ∃ (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)), (∑ i, c i) = 0 ∧
    π ∈ alternatingGroup (Fin 6) ∧ g = diagE c * permE π}
  mul_mem' := by
    rintro _ _ ⟨c, π, hc, hπ, rfl⟩ ⟨c', π', hc', hπ', rfl⟩
    exact ⟨_, _, by rw [sum_mon_mul, hc, hc', add_zero], mul_mem hπ hπ', mon_mul c c' π π'⟩
  one_mem' := ⟨0, 1, by simp, one_mem _, by rw [diagE_zero, permE_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨c, π, hc, hπ, rfl⟩
    exact ⟨_, _, by rw [sum_mon_inv, hc, neg_zero], inv_mem hπ, mon_inv c π⟩

@[expose] def Nsub : Subgroup G12 where
  carrier := {g | ∃ (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)) (ε : ZMod 2), (∑ i, c i) = 0 ∧
    g = diagE c * permE π * frobE ^ ε.val}
  mul_mem' := by
    rintro _ _ ⟨c, π, ε, hc, rfl⟩ ⟨c', π', ε', hc', rfl⟩
    obtain ⟨d, hd, h⟩ := frobPow_mul_mon ε c' π'
    refine ⟨c + fun i => d (π.symm i), π * π', ε + ε', by rw [sum_mon_mul, hc, hd hc', add_zero],
      ?_⟩
    rw [← frobPow_mul_frobPow, ← mon_mul]
    calc diagE c * permE π * frobE ^ ε.val * (diagE c' * permE π' * frobE ^ ε'.val)
        = diagE c * permE π * (frobE ^ ε.val * (diagE c' * permE π')) * frobE ^ ε'.val := by
          simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc]
  one_mem' := ⟨0, 1, 0, by simp, by rw [diagE_zero, permE_one, frobPow_zero, mul_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨c, π, ε, hc, rfl⟩
    obtain ⟨d, hd, h⟩ := frobPow_mul_mon ε (fun i => -c (π i)) π⁻¹
    refine ⟨d, π⁻¹, ε, hd (by rw [sum_mon_inv, hc, neg_zero]), ?_⟩
    rw [mul_inv_rev, frobPow_inv, mon_inv, h]

theorem mem_Nsub_iff {g : G12} : g ∈ Nsub ↔ ∃ (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6))
    (ε : ZMod 2), (∑ i, c i) = 0 ∧ g = diagE c * permE π * frobE ^ ε.val := Iff.rfl

theorem R0_le_Nsub : R0 ≤ Nsub := by
  rintro _ ⟨c, π, hc, -, rfl⟩
  exact ⟨c, π, 0, hc, by rw [frobPow_zero, mul_one]⟩

theorem R0_le_monLin : R0 ≤ monLin := by
  rintro _ ⟨c, π, -, -, rfl⟩
  exact mem_monLin_iff.2 ⟨c, π, rfl⟩

theorem Nsub_le_monGamma : Nsub ≤ monGamma := by
  rintro _ ⟨c, π, ε, -, rfl⟩
  exact ⟨c, π, ε, rfl⟩

theorem permE_mem_R0 {π : Equiv.Perm (Fin 6)} (hπ : π ∈ alternatingGroup (Fin 6)) :
    permE π ∈ R0 :=
  ⟨0, π, by simp, hπ, by rw [diagE_zero, one_mul]⟩

theorem permE_mem_Nsub (π : Equiv.Perm (Fin 6)) : permE π ∈ Nsub :=
  ⟨0, π, 0, by simp, by rw [diagE_zero, one_mul, frobPow_zero, mul_one]⟩

theorem frobE_mem_Nsub : frobE ∈ Nsub :=
  ⟨0, 1, 1, by simp, by rw [diagE_zero, permE_one, frobPow_one, one_mul, one_mul]⟩

namespace MonAux

theorem nat_card_sumZero : Nat.card {c : Fin 6 → ZMod 3 // ∑ i, c i = 0} = 3 ^ 5 := by
  rw [Nat.card_congr sumZeroEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem nat_card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

end MonAux

theorem card_R0 : Nat.card R0 = 87480 := by
  have hbij : Function.Bijective
      (fun a : {c : Fin 6 → ZMod 3 // ∑ i, c i = 0} × alternatingGroup (Fin 6) =>
        (⟨diagE a.1.1 * permE a.2.1, a.1.1, a.2.1, a.1.2, a.2.2, rfl⟩ : R0)) := by
    refine ⟨fun a b hab => ?_, fun ⟨g, c, π, hc, hπ, hg⟩ =>
      ⟨(⟨c, hc⟩, ⟨π, hπ⟩), Subtype.ext hg.symm⟩⟩
    obtain ⟨h1, h2⟩ := mon_inj0 (congrArg Subtype.val hab)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, nat_card_sumZero, nat_card_alt6]
  rfl

theorem card_Nsub : Nat.card Nsub = 349920 := by
  have hbij : Function.Bijective
      (fun a : {c : Fin 6 → ZMod 3 // ∑ i, c i = 0} × Equiv.Perm (Fin 6) × ZMod 2 =>
        (⟨diagE a.1.1 * permE a.2.1 * frobE ^ a.2.2.val, a.1.1, a.2.1, a.2.2, a.1.2, rfl⟩ :
          Nsub)) := by
    refine ⟨fun a b hab => ?_, fun ⟨g, c, π, ε, hc, hg⟩ =>
      ⟨(⟨c, hc⟩, π, ε), Subtype.ext hg.symm⟩⟩
    obtain ⟨h1, h2, h3⟩ := mon_inj (congrArg Subtype.val hab)
    exact Prod.ext (Subtype.ext h1) (Prod.ext h2 h3)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_prod, nat_card_sumZero,
    nat_card_perm_fin6, Nat.card_zmod]
  rfl

namespace MonAux

theorem mem_R0_of_mem_monLin {g : G12} (hg : g ∈ monLin) (hs : sumHom ⟨g, hg⟩ = 1)
    (hp : permHom ⟨g, hg⟩ ∈ alternatingGroup (Fin 6)) : g ∈ R0 := by
  obtain ⟨c, π, hgc⟩ := mem_monLin_iff.1 hg
  rw [sumHom_apply (g := ⟨g, hg⟩) hgc, ofAdd_eq_one] at hs
  rw [permHom_apply (g := ⟨g, hg⟩) hgc] at hp
  exact ⟨c, π, hs, hp, hgc⟩

theorem conj_mem_R0_of_mem_monLin {g r : G12} (hg : g ∈ monLin) (hr : r ∈ R0) :
    g * r * g⁻¹ ∈ R0 := by
  have hr' := R0_le_monLin hr
  have hx := mul_mem (mul_mem hg hr') (inv_mem hg)
  obtain ⟨c, π, hc, hπ, hrc⟩ := hr
  have e : (⟨g * r * g⁻¹, hx⟩ : monLin) = ⟨g, hg⟩ * ⟨r, hr'⟩ * (⟨g, hg⟩ : monLin)⁻¹ := rfl
  refine mem_R0_of_mem_monLin hx ?_ ?_
  · rw [e, map_mul, map_mul, map_inv, sumHom_apply (g := ⟨r, hr'⟩) hrc, hc, ofAdd_zero, mul_one,
      mul_inv_cancel]
  · rw [e, map_mul, map_mul, map_inv, permHom_apply (g := ⟨r, hr'⟩) hrc]
    exact (alternatingGroup.normal (α := Fin 6)).conj_mem _ hπ _

theorem conj_frobE_mem_R0 {r : G12} (hr : r ∈ R0) : frobE * r * frobE⁻¹ ∈ R0 := by
  obtain ⟨c, π, hc, hπ, rfl⟩ := hr
  refine ⟨-c, π, by simp [Finset.sum_neg_distrib, hc], hπ, ?_⟩
  rw [frobE_inv, ← mul_assoc, frobE_mul_diagE, mul_assoc (diagE (-c)), frobE_mul_permE,
    mul_assoc, mul_assoc, frobE_mul_self, mul_one]

end MonAux

theorem mul_mem_R0_of_mem_monGamma {g r : G12} (hg : g ∈ monGamma) (hr : r ∈ R0) :
    g * r * g⁻¹ ∈ R0 := by
  obtain ⟨c, π, ε, rfl⟩ := hg
  have hl : diagE c * permE π ∈ monLin := mem_monLin_iff.2 ⟨c, π, rfl⟩
  rcases zmod2_cases ε with rfl | rfl
  · rw [frobPow_zero, mul_one]
    exact conj_mem_R0_of_mem_monLin hl hr
  · rw [frobPow_one]
    simpa only [mul_assoc, mul_inv_rev] using
      conj_mem_R0_of_mem_monLin hl (conj_frobE_mem_R0 hr)

theorem permE_mem_of_closure {ι : Type*} {E : Subgroup G12} (hD5 : D5 ≤ E)
    (c : ι → Fin 6 → ZMod 3) (p : ι → Equiv.Perm (Fin 6))
    (hb : ∀ k, diagE (c k) * permE (p k) ∈ E)
    (hp : Subgroup.closure (Set.range p) = alternatingGroup (Fin 6))
    {γ : Equiv.Perm (Fin 6)} (hγ : γ ∈ alternatingGroup (Fin 6)) : permE γ ∈ E := by
  let b : ι → monLin := fun k => ⟨diagE (c k) * permE (p k), mem_monLin_iff.2 ⟨c k, p k, rfl⟩⟩
  have hQE : Subgroup.closure (Set.range b) ≤ E.comap monLin.subtype :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨k, rfl⟩; exact hb k)
  have hpb : ⇑permHom ∘ b = p := funext fun k => permHom_apply (g := b k) rfl
  have hmap : ⁅Subgroup.closure (Set.range b), Subgroup.closure (Set.range b)⁆.map permHom =
      alternatingGroup (Fin 6) := by
    rw [Subgroup.map_commutator, MonoidHom.map_closure, ← Set.range_comp, hpb, hp,
      commutator_alternatingGroup_eq_self (by simp)]
  rw [← hmap] at hγ
  obtain ⟨q, hq, hqγ⟩ := Subgroup.mem_map.1 hγ
  obtain ⟨c₀, π₀, hq0⟩ := mem_monLin_iff.1 q.2
  rw [permHom_apply hq0] at hqγ
  subst hqγ
  have hker : ⁅Subgroup.closure (Set.range b), Subgroup.closure (Set.range b)⁆ ≤ sumHom.ker :=
    Subgroup.commutator_le.2 fun g₁ _ g₂ _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
  have hsum := hker hq
  rw [MonoidHom.mem_ker, sumHom_apply hq0, ofAdd_eq_one] at hsum
  have hqE : (q : G12) ∈ E := hQE (Subgroup.commutator_le_self _ hq)
  rw [hq0] at hqE
  simpa using mul_mem (inv_mem (hD5 ⟨c₀, hsum, rfl⟩)) hqE

end CFSG.GF2Type.Smith1979.IdxFour
