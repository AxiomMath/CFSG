module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIBadProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenY

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv Equiv.Perm CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt CFSG.Quasithin.SteinbergCB
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem exists_hom_of_carmichael {M : Type*} [Group M] {m : ℕ} (gen : Fin m → M)
    (h3 : ∀ i, gen i ^ 3 = 1) (h2 : ∀ i j, i ≠ j → (gen i * gen j) ^ 2 = 1) :
    ∃ Φ : alternatingGroup (Fin (m + 2)) →* M, ∀ i, Φ (altThreeCycle i) = gen i := by
  have hP := CFSG.Alternating.Multipliers.isPresentation_carmichael m
  set f := FreeGroup.lift (altThreeCycle (n := m)) with hf
  have hker : f.ker ≤ (FreeGroup.lift gen).ker := by
    rw [hP.ker_lift]
    exact normalClosure_le_normal fun r hr =>
      CFSG.Alternating.Multipliers.lift_carmichaelWords_eq_one h3 h2 r hr
  refine ⟨(QuotientGroup.lift f.ker (FreeGroup.lift gen) hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hP.lift_surjective).symm.toMonoidHom,
    fun i => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hP.lift_surjective).symm
      (altThreeCycle i) = ((FreeGroup.of i : FreeGroup (Fin m)) : FreeGroup (Fin m) ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    exact (FreeGroup.lift_apply_of).symm
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk,
    FreeGroup.lift_apply_of]

theorem fin7_cases (x : Fin 7) :
    (∃ i : Fin 3, x = Fin.castAdd 4 i) ∨ ∃ j : Fin 4, x = Fin.natAdd 3 j := by
  revert x
  decide

@[expose] def piA : Perm (Fin 5) := swap 0 3 * swap 3 1 * swap 1 4 * swap 4 2

@[expose] def piA' : Perm (Fin 5) := swap 0 4 * swap 4 2 * swap 1 3

@[expose] def piD : Perm (Fin 6) := swap 0 5 * swap 5 3 * swap 3 1 * swap 1 4 * swap 4 2

@[expose] def piA6 : Perm (Fin 6) := swap 0 3 * swap 3 1 * swap 1 4 * swap 4 2

@[expose] def piA'6 : Perm (Fin 6) := swap 0 4 * swap 4 2 * swap 1 3

@[expose] def kk : Fin 4 → Perm (Fin 5) :=
  ![swap 0 3 * swap 1 2, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, 1]

@[expose] def kk6 : Fin 4 → Perm (Fin 6) :=
  ![swap 0 3 * swap 1 2, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, 1]

theorem kk_mem (j : Fin 4) : kk j ∈ alternatingGroup (Fin 5) := by
  revert j
  decide

theorem kk_mem_P0 : ∀ j : Fin 4, (⟨kk j, kk_mem j⟩ : A5) ∈ P0 := by
  decide

theorem ιP56_piA : ιP56 piA = piA6 := ιP56_eq_of (by decide) (by decide)

theorem ιP56_piA' : ιP56 piA' = piA'6 := ιP56_eq_of (by decide) (by decide)

theorem ιP56_kk (j : Fin 4) : ιP56 (kk j) = kk6 j :=
  ιP56_eq_of (by revert j; decide) (by revert j; decide)

theorem ιP56_x0 : ιP56 (x0 : Perm (Fin 5)) = swap 0 1 * swap 3 4 :=
  ιP56_eq_of (by decide) (by decide)

theorem ιP56_altThreeCyclePerm (i : Fin 3) :
    ιP56 (altThreeCyclePerm i) = altThreeCyclePerm (n := 4) i.castSucc :=
  ιP56_eq_of (by revert i; decide) (by revert i; decide)

theorem coe_ι56_conjPerm (π : Perm (Fin 5)) (i : Fin 3) :
    ((ι56 (conjPerm 5 π (altThreeCycle i)) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      ιP56 π * altThreeCyclePerm (n := 4) i.castSucc * (ιP56 π)⁻¹ := by
  rw [coe_ι56, conjPerm_apply, map_mul, map_mul, map_inv, coe_altThreeCycle,
    ιP56_altThreeCyclePerm]

theorem eps_piA : ∀ i : Fin 3, ∃ k : Fin 3,
    ((x0 * y0 ^ (k : ℕ) : A5) : Perm (Fin 5)) * (piA * altThreeCyclePerm i * piA⁻¹) *
      ((x0 * y0 ^ (k : ℕ) : A5) : Perm (Fin 5))⁻¹ = (piA * altThreeCyclePerm i * piA⁻¹)⁻¹ := by
  decide

theorem eps_piA' : ∀ i : Fin 3, ∃ k : Fin 3,
    ((x0 * y0 ^ (k : ℕ) : A5) : Perm (Fin 5)) * (piA' * altThreeCyclePerm i * piA'⁻¹) *
      ((x0 * y0 ^ (k : ℕ) : A5) : Perm (Fin 5))⁻¹ = (piA' * altThreeCyclePerm i * piA'⁻¹)⁻¹ := by
  decide

theorem cross_piA : ∀ i : Fin 3,
    (piA6 * altThreeCyclePerm (n := 4) i.castSucc * piA6⁻¹ * (a6c345 : Perm (Fin 6))) ^ 2 = 1 := by
  decide

theorem cross_piA' : ∀ i : Fin 3,
    (piA'6 * altThreeCyclePerm (n := 4) i.castSucc * piA'6⁻¹ *
      ((a6c345⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6))) ^ 2 = 1 := by
  decide

theorem d3_comm : piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹ * (a6c012 : Perm (Fin 6)) =
    (a6c012 : Perm (Fin 6)) * (piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹) := by
  decide

theorem d3_conj45 : swap 4 5 * (piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹) * (swap 4 5)⁻¹ =
    (piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹)⁻¹ := by
  decide

theorem d3_conjx0 : swap 0 1 * swap 3 4 * (piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹) *
    (swap 0 1 * swap 3 4)⁻¹ = (piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹)⁻¹ := by
  decide

theorem d3_conj_kk : ∀ j : Fin 4, kk6 j * (piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹) *
    (kk6 j)⁻¹ = piD * altThreeCyclePerm (n := 4) j * piD⁻¹ := by
  decide

theorem d3_ne_one : piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹ ≠ 1 := by
  decide

theorem card_centralizer_a6c012 :
    Nat.card (centralizer ({a6c012} : Set (alternatingGroup (Fin 6)))) = 9 := by
  have hC : Nat.card (centralizer ({(a6c012 : Perm (Fin 6))} : Set (Perm (Fin 6)))) = 18 := by
    rw [nat_card_centralizer, isThreeCycle_a6c012.cycleType]
    simp [Nat.factorial]
  set C := centralizer ({(a6c012 : Perm (Fin 6))} : Set (Perm (Fin 6))) with hCdef
  set f : C →* ℤˣ := Perm.sign.comp C.subtype with hf
  have hs : swap (3 : Fin 6) 4 ∈ C := by
    rw [hCdef, mem_centralizer_singleton_iff]
    decide
  have hsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨_, hs⟩, by simp [hf, sign_swap (show (3 : Fin 6) ≠ 4 by decide)]⟩
  have hker : Nat.card f.ker = 9 := by
    have h := f.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top,
      Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, hC] at h
    omega
  rw [← hker]
  exact Nat.card_congr
    { toFun := fun g => ⟨⟨((g : alternatingGroup (Fin 6)) : Perm (Fin 6)),
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp g.2))⟩,
        MonoidHom.mem_ker.mpr (mem_alternatingGroup.mp (g : alternatingGroup (Fin 6)).2)⟩
      invFun := fun k => ⟨⟨((k : C) : Perm (Fin 6)), mem_alternatingGroup.mpr
          (MonoidHom.mem_ker.mp k.2)⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp (k : C).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem eq_a6c345_of {β : alternatingGroup (Fin 6)} (h1 : β * a6c012 = a6c012 * β)
    (h2 : conjPerm 6 (swap 4 5) β = β⁻¹) (h3 : β ≠ 1) : β = a6c345 ∨ β = a6c345⁻¹ := by
  have hle : s9Hom.range ≤ centralizer ({a6c012} : Set (alternatingGroup (Fin 6))) := by
    rintro _ ⟨p, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show ew a6c012 a6c345 p.toAdd * a6c012 = a6c012 * ew a6c012 a6c345 p.toAdd
    exact (((Commute.refl a6c012).pow_left _).mul_left
      ((show Commute a6c345 a6c012 from a6c012_comm_a6c345.symm).pow_left _)).eq
  have heq := eq_of_le_of_card_ge hle (by rw [card_centralizer_a6c012, card_range_s9Hom])
  have hβ : β ∈ s9Hom.range := heq ▸ mem_centralizer_singleton_iff.mpr h1
  obtain ⟨p, rfl⟩ := hβ
  have h2' : swap 4 5 * ((s9Hom p : alternatingGroup (Fin 6)) : Perm (Fin 6)) * (swap 4 5)⁻¹ =
      (((s9Hom p)⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
    have := congrArg Subtype.val h2
    rwa [conjPerm_apply] at this
  revert h2' h3
  revert p
  decide

theorem viaEmbeddingHom_castLE_eq_of {m n : ℕ} (h : m ≤ n) {π : Perm (Fin m)} {σ : Perm (Fin n)}
    (hfix : ∀ i : Fin n, m ≤ (i : ℕ) → σ i = i)
    (hπ : ∀ j : Fin m, σ (Fin.castLE h j) = Fin.castLE h (π j)) :
    viaEmbeddingHom (Fin.castLEEmb h) π = σ := by
  refine Equiv.ext fun i => ?_
  by_cases hi : (i : ℕ) < m
  · have hi' : Fin.castLEEmb h ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← hi', viaEmbeddingHom_apply_image]
    exact (hπ ⟨i, hi⟩).symm
  · have hnot : i ∉ Set.range (Fin.castLEEmb h) := by
      rintro ⟨j, rfl⟩
      exact hi (by simp)
    rw [viaEmbeddingHom_apply_of_notMem _ _ hnot, hfix i (by omega)]

theorem liftNat_altThreeCycle (i : Fin 3) :
    liftNat 5 (altThreeCycle (n := 3) i) = altThreeCycle (n := 7) (Fin.castAdd 4 i) := by
  apply Subtype.ext
  rw [coe_liftNat, coe_altThreeCycle, coe_altThreeCycle]
  exact viaEmbeddingHom_castLE_eq_of _ (by revert i; decide) (by revert i; decide)

theorem range_liftNat_of {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : Nonempty (↥A ≃* A5)) {Φ : alternatingGroup (Fin 9) →* G} (hΦ : Function.Injective Φ)
    (hΦA : ∀ i : Fin 3, Φ (altThreeCycle (n := 7) (Fin.castAdd 4 i)) ∈ A) :
    (Φ.comp (liftNat 5)).range = A := by
  obtain ⟨e⟩ := hA
  have hle : (Φ.comp (liftNat 5)).range ≤ A := by
    rw [MonoidHom.range_eq_map, ← closure_altThreeCycle, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [MonoidHom.comp_apply, liftNat_altThreeCycle]
    exact hΦA i
  have hinj : Function.Injective (Φ.comp (liftNat 5)) := hΦ.comp liftNat_injective
  exact eq_of_le_of_card_ge hle
    ((Nat.card_congr e.toEquiv).trans (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)).le

@[expose] def tauB : Perm (Fin 9) :=
  swap 0 1 * swap 1 5 * swap 2 6 * swap 3 7 * swap 4 8

@[expose] def cycleB (i : Fin 3) : alternatingGroup (Fin 9) :=
  altThreeCycle (n := 7) (Fin.natAdd 3 i.succ) *
    (altThreeCycle (n := 7) (Fin.natAdd 3 (0 : Fin 4)))⁻¹ *
    (altThreeCycle (n := 7) (Fin.natAdd 3 i.succ))⁻¹

theorem conj_tauB_liftNat (i : Fin 3) :
    conjPerm 9 tauB (liftNat 5 (altThreeCycle (n := 3) i)) = cycleB i := by
  apply Subtype.ext
  rw [conjPerm_apply, liftNat_altThreeCycle]
  revert i
  decide

theorem fix5_cycleB : ∀ i : Fin 3, (piD * (altThreeCyclePerm (n := 4) i.succ *
    (altThreeCyclePerm (n := 4) 0)⁻¹ * (altThreeCyclePerm (n := 4) i.succ)⁻¹) * piD⁻¹) 5 = 5 := by
  decide

theorem range_tauB_liftNat_of {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : Nonempty (↥B ≃* A5)) {Φ : alternatingGroup (Fin 9) →* G} (hΦ : Function.Injective Φ)
    (hΦB : ∀ i : Fin 3, Φ (cycleB i) ∈ B) :
    ((Φ.comp (conjPerm 9 tauB).toMonoidHom).comp (liftNat 5)).range = B := by
  obtain ⟨e⟩ := hB
  have hle : ((Φ.comp (conjPerm 9 tauB).toMonoidHom).comp (liftNat 5)).range ≤ B := by
    rw [MonoidHom.range_eq_map, ← closure_altThreeCycle, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_tauB_liftNat]
    exact hΦB i
  have hinj : Function.Injective ((Φ.comp (conjPerm 9 tauB).toMonoidHom).comp (liftNat 5)) :=
    (hΦ.comp (conjPerm 9 tauB).injective).comp liftNat_injective
  exact eq_of_le_of_card_ge hle
    ((Nat.card_congr e.toEquiv).trans (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)).le

namespace CaseICoords

variable {G : Type} [Group G] [Finite G] {A B R T : Subgroup G} (c : CaseICoords A B R T)

theorem mul_sq_eq_one_of_mem_O {a d ε : G} (ha : a ∈ A) (hε : ε ∈ A) (hεa : ε * a * ε⁻¹ = a⁻¹)
    (hεd : ε * d * ε⁻¹ = d⁻¹) (he : (a * d) ^ 2 ∈ c.symm.O) : (a * d) ^ 2 = 1 := by
  set e := (a * d) ^ 2 with he_def
  have heC : e ∈ centralizer (A : Set G) := c.symm.O_le_centralizer he
  have hae : a * e = e * a := mem_centralizer_iff.mp heC a ha
  have hεe : ε * e * ε⁻¹ = e := by rw [mem_centralizer_iff.mp heC ε hε, mul_inv_cancel_right]
  have h1 : ε * e * ε⁻¹ = (a⁻¹ * d⁻¹) ^ 2 := by
    rw [he_def, ← MulAut.conj_apply, map_pow, map_mul, MulAut.conj_apply, MulAut.conj_apply, hεa,
      hεd]
  have h2 : (a⁻¹ * d⁻¹) ^ 2 = e⁻¹ := by
    have : (a⁻¹ * d⁻¹) ^ 2 = (a⁻¹ * e * a)⁻¹ := by
      rw [he_def, sq, sq]
      group
    rw [this, mul_assoc, ← hae, inv_mul_cancel_left]
  rw [hεe, h2] at h1
  have h3 : e ^ 2 = 1 := by
    rw [sq]
    calc e * e = e * e⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel e
  have hodd : Odd (orderOf e) := by
    have h4 : orderOf e ∣ Nat.card c.symm.O := by
      rw [← Subgroup.orderOf_mk e he]
      exact orderOf_dvd_natCard _
    exact c.symm.odd_card_O.of_dvd_nat h4
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h3) with h5 | h5
  · exact orderOf_eq_one_iff.mp h5
  · rw [h5] at hodd
    exact absurd hodd (by decide)

theorem exists_alt9
    (hw : c.w ∉ c.D) :
    ∃ Φ : alternatingGroup (Fin 9) →* G, Function.Injective Φ ∧ Φ.range = A ⊔ B ∧
      (Φ.comp (liftNat 5)).range = A ∧
      ((Φ.comp (conjPerm 9 tauB).toMonoidHom).comp (liftNat 5)).range = B := by
  obtain ⟨u, hu⟩ := c.exists_isOuter
  obtain ⟨u', hu'⟩ := c.symm.exists_isOuter
  have hA6 := hu.nonempty_equiv_alt6
  have hA6' := hu'.nonempty_equiv_alt6
  obtain ⟨θ, hθ⟩ := c.exists_label hA6
  obtain ⟨θ', hθ'⟩ := c.symm.exists_label hA6'
  have hinj := map_D_injective_of_not_mem hθ hA6 hw
  set δ : c.D ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.ofBijective (c.barOf c.D_le_H) ⟨hinj, c.map_D_surjective hA6⟩).trans θ with hδ
  have hδapp : ∀ d, δ d = θ (c.barOf c.D_le_H d) := fun d => rfl
  have hδB : ∀ σ : A5, δ ⟨(c.ψB σ : G), mem_sup_left (c.ψB σ).2⟩ = ι56 σ := fun σ => hθ σ
  have hδx : ∀ d : c.D, δ ⟨c.x * d * c.x⁻¹, (mem_normalizer_iff.mp c.x_mem_normalizer_D d).mp
      d.2⟩ = conjPerm 6 (swap 4 5) (δ d) := fun d => label_x c hθ (c.barOf c.D_le_H d)
  set FD : alternatingGroup (Fin 6) →* G :=
    c.D.subtype.comp (δ.symm.toMonoidHom.comp (conjPerm 6 piD).toMonoidHom) with hFD
  set D3 : c.D := δ.symm (conjPerm 6 piD (altThreeCycle (n := 4) 3)) with hD3
  have hD3δ : ((δ D3 : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      piD * altThreeCyclePerm (n := 4) 3 * piD⁻¹ := by
    rw [hD3, MulEquiv.apply_symm_apply, conjPerm_apply, coe_altThreeCycle]
  set d3 : G := (D3 : G) with hd3
  have hFD3 : FD (altThreeCycle 3) = d3 := rfl
  have hxd3 : c.x * d3 * c.x⁻¹ = d3⁻¹ := by
    have h := hδx D3
    have h' : δ ⟨c.x * d3 * c.x⁻¹, (mem_normalizer_iff.mp c.x_mem_normalizer_D D3).mp D3.2⟩ =
        δ D3⁻¹ := by
      rw [h, map_inv]
      apply Subtype.ext
      rw [conjPerm_apply, hD3δ, d3_conj45, Subgroup.coe_inv, hD3δ]
    exact congrArg Subtype.val (δ.injective h')
  have hyd3 : (c.ψB x0 : G) * d3 * (c.ψB x0 : G)⁻¹ = d3⁻¹ := by
    have hy : (c.ψB x0 : G) ∈ c.D := mem_sup_left (c.ψB x0).2
    have h' : δ (⟨(c.ψB x0 : G), hy⟩ * D3 * ⟨(c.ψB x0 : G), hy⟩⁻¹) = δ D3⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, hδB x0]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, coe_ι56,
        ιP56_x0, hD3δ, d3_conjx0]
    exact congrArg Subtype.val (δ.injective h')
  have hd3v : d3 * c.vB = c.vB * d3 := by
    have h' : δ (D3 * ⟨c.vB, c.vB_mem_D⟩) = δ (⟨c.vB, c.vB_mem_D⟩ * D3) := by
      rw [map_mul, map_mul, hδapp ⟨c.vB, c.vB_mem_D⟩, theta_vB hθ]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hD3δ, d3_comm]
    exact congrArg Subtype.val (δ.injective h')
  have hd3w : d3 * c.w = c.w * d3 := mem_centralizer_singleton_iff.mp (c.D_le_H D3.2)
  have hd3_3 : d3 ^ 3 = 1 := by
    rw [← hFD3, ← map_pow, altThreeCycle_pow_three, map_one]
  have hd3Hv : d3 ∈ c.symm.H := mem_centralizer_singleton_iff.mpr hd3v
  have hwHv : c.w ∈ c.symm.H := mem_centralizer_singleton_iff.mpr c.commute_vB_w.eq.symm
  set β := θ' ((⟨d3, hd3Hv⟩ : c.symm.H) : c.symm.Hbar) with hβdef
  have hθ'w : θ' ((⟨c.w, hwHv⟩ : c.symm.H) : c.symm.Hbar) = a6c012 := by
    rw [← ι56_y0, ← hθ' y0]
    rfl
  have hβ1 : β * a6c012 = a6c012 * β := by
    rw [← hθ'w, hβdef, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext hd3w
  have hβ2 : conjPerm 6 (swap 4 5) β = β⁻¹ := by
    have hyN := c.symm.x_mem_normalizer
    have h1 := label_x c.symm hθ' ((⟨d3, hd3Hv⟩ : c.symm.H) : c.symm.Hbar)
    rw [← hβdef] at h1
    rw [← h1, ← map_inv, ← QuotientGroup.mk_inv]
    congr 1
    show ((⟨(c.ψB x0 : G) * d3 * (c.ψB x0 : G)⁻¹, _⟩ : c.symm.H) : c.symm.Hbar) = _
    congr 1
    exact Subtype.ext hyd3
  have hβ3 : β ≠ 1 := by
    intro h1
    have hO : d3 ∈ c.symm.O := (c.symm.mk_eq_one_iff ⟨d3, hd3Hv⟩).mp (θ'.injective
      (by rw [← hβdef, h1, map_one]))
    have hC := c.symm.O_le_centralizer hO
    have hxd : c.x * d3 * c.x⁻¹ = d3 := by
      rw [mem_centralizer_iff.mp hC c.x c.x_mem, mul_inv_cancel_right]
    rw [hxd3] at hxd
    have h2 : d3 = 1 := by
      have h3 : d3 * d3 = 1 := by
        calc d3 * d3 = d3 * d3⁻¹ := by rw [hxd]
          _ = 1 := mul_inv_cancel d3
      calc d3 = d3 ^ 3 * (d3 * d3)⁻¹ := by group
        _ = 1 := by rw [hd3_3, h3, inv_one, one_mul]
    apply d3_ne_one
    rw [← hD3δ]
    have : D3 = 1 := Subtype.ext h2
    rw [this, map_one]
    rfl
  obtain ⟨π, hπε, hπβ⟩ : ∃ π : Perm (Fin 5), (∀ i : Fin 3, ∃ k : Fin 3,
      ((x0 * y0 ^ (k : ℕ) : A5) : Perm (Fin 5)) * (π * altThreeCyclePerm i * π⁻¹) *
        ((x0 * y0 ^ (k : ℕ) : A5) : Perm (Fin 5))⁻¹ = (π * altThreeCyclePerm i * π⁻¹)⁻¹) ∧
      ∀ i : Fin 3, (ι56 (conjPerm 5 π (altThreeCycle i)) * β) ^ 2 = 1 := by
    rcases eq_a6c345_of hβ1 hβ2 hβ3 with h | h
    · refine ⟨piA, eps_piA, fun i => Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_ι56_conjPerm, ιP56_piA, h, cross_piA]
      rfl
    · refine ⟨piA', eps_piA', fun i => Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_ι56_conjPerm, ιP56_piA', h, cross_piA']
      rfl
  set FA : A5 →* G := A.subtype.comp (c.ψA.toMonoidHom.comp (conjPerm 5 π).toMonoidHom)
    with hFA
  have hcross3 : ∀ i : Fin 3, (FA (altThreeCycle i) * d3) ^ 2 = 1 := by
    intro i
    set σ : A5 := conjPerm 5 π (altThreeCycle i) with hσ
    have haA : FA (altThreeCycle i) ∈ A := (c.ψA σ).2
    obtain ⟨k, hk⟩ := hπε i
    have hσk : (x0 * y0 ^ (k : ℕ)) * σ * (x0 * y0 ^ (k : ℕ))⁻¹ = σ⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hσ,
        conjPerm_apply, coe_altThreeCycle, hk]
    have hε : (c.ψA (x0 * y0 ^ (k : ℕ)) : G) = c.x * c.w ^ (k : ℕ) := by
      rw [map_mul, map_pow, Subgroup.coe_mul, SubgroupClass.coe_pow]
      rfl
    have hεA : c.x * c.w ^ (k : ℕ) ∈ A := mul_mem c.x_mem (pow_mem c.w_mem _)
    have hεa : c.x * c.w ^ (k : ℕ) * FA (altThreeCycle i) * (c.x * c.w ^ (k : ℕ))⁻¹ =
        (FA (altThreeCycle i))⁻¹ := by
      rw [← hε]
      show (c.ψA (x0 * y0 ^ (k : ℕ)) : G) * (c.ψA σ : G) * (c.ψA (x0 * y0 ^ (k : ℕ)) : G)⁻¹ =
        (c.ψA σ : G)⁻¹
      rw [← Subgroup.coe_inv, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
        ← map_inv, ← map_inv, ← map_mul, ← map_mul, hσk]
    have hεd : c.x * c.w ^ (k : ℕ) * d3 * (c.x * c.w ^ (k : ℕ))⁻¹ = d3⁻¹ := by
      have hwk : c.w ^ (k : ℕ) * d3 = d3 * c.w ^ (k : ℕ) := ((Commute.pow_left hd3w.symm _)).eq
      calc c.x * c.w ^ (k : ℕ) * d3 * (c.x * c.w ^ (k : ℕ))⁻¹ =
          c.x * (c.w ^ (k : ℕ) * d3) * (c.w ^ (k : ℕ))⁻¹ * c.x⁻¹ := by group
        _ = c.x * d3 * c.x⁻¹ := by rw [hwk]; group
        _ = d3⁻¹ := hxd3
    have haHv : FA (altThreeCycle i) ∈ c.symm.H :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp c.vB_mem_centralizer _ haA)
    refine c.mul_sq_eq_one_of_mem_O haA hεA hεa hεd ?_
    have hmem : (FA (altThreeCycle i) * d3) ^ 2 ∈ c.symm.H :=
      pow_mem (mul_mem haHv hd3Hv) 2
    refine (c.symm.mk_eq_one_iff ⟨_, hmem⟩).mp (θ'.injective ?_)
    have h1 : (⟨(FA (altThreeCycle i) * d3) ^ 2, hmem⟩ : c.symm.H) =
        (⟨FA (altThreeCycle i), haHv⟩ * ⟨d3, hd3Hv⟩) ^ 2 := rfl
    have h2 : θ' ((⟨FA (altThreeCycle i), haHv⟩ : c.symm.H) : c.symm.Hbar) = ι56 σ := by
      rw [← hθ' σ]
      rfl
    rw [h1, QuotientGroup.mk_pow, QuotientGroup.mk_mul, map_pow, map_mul, h2, ← hβdef, hπβ i,
      map_one]
  set FAD : Fin 7 → G := Fin.append (fun i : Fin 3 => FA (altThreeCycle i))
    (fun j : Fin 4 => FD (altThreeCycle j)) with hFAD
  have hR : ∀ j : Fin 4, ∃ r ∈ centralizer (A : Set G), r * d3 * r⁻¹ = FD (altThreeCycle j) := by
    intro j
    set ρ : A5 := ⟨kk j, kk_mem j⟩ with hρ
    have hrR : (c.ψB ρ : G) ∈ R := by
      rw [c.mem_R_iff (c.ψB ρ).2, Subtype.coe_eta, MulEquiv.symm_apply_apply]
      exact kk_mem_P0 j
    have hr : (c.ψB ρ : G) ∈ centralizer (A : Set G) := c.pair.sylowR.le hrR
    refine ⟨(c.ψB ρ : G), hr, ?_⟩
    have hy : (c.ψB ρ : G) ∈ c.D := mem_sup_left (c.ψB ρ).2
    have h' : δ (⟨(c.ψB ρ : G), hy⟩ * D3 * ⟨(c.ψB ρ : G), hy⟩⁻¹) =
        conjPerm 6 piD (altThreeCycle j) := by
      rw [map_mul, map_mul, map_inv, hδB ρ]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_ι56, hρ, ιP56_kk, hD3δ,
        d3_conj_kk, conjPerm_apply, coe_altThreeCycle]
    have h'' := congrArg (fun z => ((δ.symm z : c.D) : G)) h'
    simp only [MulEquiv.symm_apply_apply] at h''
    exact h''
  have hcross : ∀ (i : Fin 3) (j : Fin 4),
      (FA (altThreeCycle i) * FD (altThreeCycle j)) ^ 2 = 1 := by
    intro i j
    obtain ⟨r, hrC, hrd⟩ := hR j
    have hrA : FA (altThreeCycle i) * r = r * FA (altThreeCycle i) :=
      mem_centralizer_iff.mp hrC _ (c.ψA (conjPerm 5 π (altThreeCycle i))).2
    have hra : r * FA (altThreeCycle i) * r⁻¹ = FA (altThreeCycle i) := by
      rw [← hrA, mul_inv_cancel_right]
    rw [← hrd, ← hra]
    calc (r * FA (altThreeCycle i) * r⁻¹ * (r * d3 * r⁻¹)) ^ 2 =
        r * (FA (altThreeCycle i) * d3) ^ 2 * r⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hcross3 i, mul_one, mul_inv_cancel]
  have hFADl : ∀ i : Fin 3, FAD (Fin.castAdd 4 i) = FA (altThreeCycle i) := fun i =>
    Fin.append_left _ _ i
  have hFADr : ∀ j : Fin 4, FAD (Fin.natAdd 3 j) = FD (altThreeCycle j) := fun j =>
    Fin.append_right _ _ j
  have h3 : ∀ i, FAD i ^ 3 = 1 := by
    intro i
    rcases fin7_cases i with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [hFADl, ← map_pow, altThreeCycle_pow_three, map_one]
    · rw [hFADr, ← map_pow, altThreeCycle_pow_three, map_one]
  have h2 : ∀ i j, i ≠ j → (FAD i * FAD j) ^ 2 = 1 := by
    intro i j hij
    rcases fin7_cases i with ⟨i, rfl⟩ | ⟨j', rfl⟩ <;> rcases fin7_cases j with ⟨i', rfl⟩ | ⟨j, rfl⟩
    · rw [hFADl, hFADl, ← map_mul, ← map_pow,
        altThreeCycle_mul_sq (fun h => hij (by rw [h])), map_one]
    · rw [hFADl, hFADr]
      exact hcross i j
    · rw [hFADr, hFADl]
      exact sq_mul_comm_eq_one (hcross i' j')
    · rw [hFADr, hFADr, ← map_mul, ← map_pow,
        altThreeCycle_mul_sq (fun h => hij (by rw [h])), map_one]
  obtain ⟨Φ, hΦ⟩ := exists_hom_of_carmichael FAD h3 h2
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hFAinj : Function.Injective FA :=
    A.subtype_injective.comp (c.ψA.injective.comp (conjPerm 5 π).injective)
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MonoidHom.normal_ker Φ).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have h1 : Φ (altThreeCycle 0) = 1 := MonoidHom.mem_ker.mp (h ▸ mem_top _)
      rw [hΦ, show (0 : Fin 7) = Fin.castAdd 4 (0 : Fin 3) from rfl, hFADl] at h1
      have h2 : altThreeCycle (n := 3) 0 = 1 := hFAinj (by rw [h1, map_one])
      exact absurd h2 (by decide)
  have hrange : Φ.range = closure (Set.range FAD) := by
    rw [MonoidHom.range_eq_map, ← closure_altThreeCycle, MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    simp only [Set.mem_range, Function.comp_apply, hΦ]
  have hFArange : FA.range = A := by
    ext a
    constructor
    · rintro ⟨σ, rfl⟩
      exact (c.ψA _).2
    · intro ha
      exact ⟨(conjPerm 5 π).symm (c.ψA.symm ⟨a, ha⟩), by simp [hFA]⟩
  have hFDrange : FD.range = c.D := by
    ext a
    constructor
    · rintro ⟨σ, rfl⟩
      exact (δ.symm _).2
    · intro ha
      exact ⟨(conjPerm 6 piD).symm (δ ⟨a, ha⟩), by simp [hFD]⟩
  have hAle : A ≤ closure (Set.range FAD) := by
    rw [← hFArange, MonoidHom.range_eq_map, ← closure_altThreeCycle, MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨Fin.castAdd 4 i, hFADl i⟩
  have hDle : c.D ≤ closure (Set.range FAD) := by
    rw [← hFDrange, MonoidHom.range_eq_map, ← closure_altThreeCycle, MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Fin.natAdd 3 j, hFADr j⟩
  have hDAB : c.D ≤ A ⊔ B := by
    refine sup_le le_sup_right ?_
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (mul_mem (mem_sup_left c.x_mem) (mem_sup_right hb))
      (inv_mem (mem_sup_left c.x_mem))
  have hΦA : ∀ i : Fin 3, Φ (altThreeCycle (n := 7) (Fin.castAdd 4 i)) ∈ A := fun i => by
    rw [hΦ, hFADl]
    exact (c.ψA _).2
  have hFDB : ∀ σ : alternatingGroup (Fin 6),
      ((conjPerm 6 piD σ : alternatingGroup (Fin 6)) : Perm (Fin 6)) 5 = 5 → FD σ ∈ B := by
    intro σ h5
    obtain ⟨ρ, hρ⟩ := mem_range_ι56 h5
    have h1 : δ.symm (conjPerm 6 piD σ) = ⟨(c.ψB ρ : G), mem_sup_left (c.ψB ρ).2⟩ := by
      rw [MulEquiv.symm_apply_eq, hδB, hρ]
    show ((δ.symm (conjPerm 6 piD σ) : c.D) : G) ∈ B
    rw [h1]
    exact (c.ψB ρ).2
  have hΦB : ∀ i : Fin 3, Φ (cycleB i) ∈ B := fun i => by
    rw [cycleB, map_mul, map_mul, map_inv, map_inv, hΦ, hΦ, hFADr, hFADr, ← map_inv, ← map_inv,
      ← map_mul, ← map_mul]
    refine hFDB _ ?_
    rw [conjPerm_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      coe_altThreeCycle, coe_altThreeCycle]
    exact fix5_cycleB i
  refine ⟨Φ, hΦinj, le_antisymm ?_ ?_, range_liftNat_of c.pair.isoA hΦinj hΦA,
    range_tauB_liftNat_of c.pair.isoB hΦinj hΦB⟩
  · rw [hrange, closure_le]
    rintro _ ⟨i, rfl⟩
    rcases fin7_cases i with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [hFADl]
      exact mem_sup_left (c.ψA _).2
    · rw [hFADr]
      exact hDAB (δ.symm _).2
  · rw [hrange]
    exact sup_le hAle ((le_sup_left : B ≤ c.D).trans hDle)

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive
