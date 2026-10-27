module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbits

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b

variable {n : ℕ}

open Classical in
theorem mem_commV_of_sum_orbit (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    {v : ↥(coreMod n)}
    (hv : ∀ q : OrbQ F, ∑ i ∈ Finset.univ.filter (fun i => orbOf F i = q), vcoord v i = 0) :
    v ∈ commV (F.map (coreAct n)) := by
  set r : Fin n → Fin n := fun m => orbRep F (orbOf F m) with hr
  have hY : ∀ m, pairVec (r m) m ∈ commV (F.map (coreAct n)) := by
    intro m
    obtain ⟨a, ha, ham⟩ := orbOf_eq_iff.1 (orbOf_orbRep F (orbOf F m)).symm
    have h := pairVec_mem_commV hn ha (r m)
    rw [ham, pairVec_comm] at h
    exact h
  have hsum : vsum (fun m => pairVec (r m) m) v = v := by
    refine vcoord_ext fun q => ?_
    have h1 : vcoord (vsum (fun m => pairVec (r m) m) v) q =
        ∑ m, vcoord v m * vcoord (pairVec (r m) m) q :=
      vcoord_map_vsum (MonoidHom.id ↥(coreMod n)) (fun m => pairVec (r m) m) v q
    rw [h1]
    simp only [vcoord_pairVec, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
    have h2 : ∑ m, (if q = r m then vcoord v m else 0) = 0 := by
      rw [← Finset.sum_filter]
      by_cases hq : ∃ m₀, q = r m₀
      · obtain ⟨m₀, hm₀⟩ := hq
        have hqo : orbOf F q = orbOf F m₀ := by rw [hm₀, hr]; exact orbOf_orbRep F _
        have hfil : Finset.univ.filter (fun m => q = r m) =
            Finset.univ.filter (fun m => orbOf F m = orbOf F q) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            rw [h, hr]
            exact (orbOf_orbRep F _).symm
          · intro h
            rw [hm₀, hr]
            simp only
            rw [h, hqo]
        rw [hfil]
        exact hv _
      · push Not at hq
        exact Finset.sum_eq_zero fun m hm => absurd (Finset.mem_filter.1 hm).2 (hq m)
    rw [h2, zero_add, Finset.sum_ite_eq]
    simp
  rw [← hsum]
  exact Subgroup.prod_mem _ fun m _ => Subgroup.pow_mem _ (hY m) _

theorem mem_commV_iff_of_orbit (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))} {x₀ : Fin n}
    (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a) {v : ↥(coreMod n)} :
    v ∈ commV (F.map (coreAct n)) ↔ ∀ i, (∀ f ∈ F, f i = i) → vcoord v i = 0 := by
  classical
  refine ⟨fun hv i hi => vcoord_eq_zero_of_mem_commV hv hi, fun hv => ?_⟩
  have hvz : ∀ i, orbOf F i ≠ orbOf F x₀ → vcoord v i = 0 := by
    intro i hi
    apply hv i
    by_contra hne
    push Not at hne
    obtain ⟨f, hf, rfl⟩ := hsame i hne
    exact hi (orbOf_apply hf x₀)
  refine mem_commV_of_sum_orbit hn fun q => ?_
  by_cases hq : q = orbOf F x₀
  · rw [Finset.sum_filter_of_ne fun i _ hi => ?_, sum_vcoord]
    by_contra hne
    rw [hq] at hne
    exact hi (hvz i hne)
  · exact Finset.sum_eq_zero fun i hi => hvz i (by rw [(Finset.mem_filter.1 hi).2]; exact hq)

theorem card_commV_mul (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))} {x₀ : Fin n}
    (hx₀ : ∃ f ∈ F, f x₀ ≠ x₀)
    (hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a) :
    Nat.card (commV (F.map (coreAct n))) * 2 ^ Nat.card {i : Fin n // ∀ f ∈ F, f i = i} * 2 =
      2 ^ n := by
  classical
  set P : Fin n → Prop := fun i => ∀ f ∈ F, f i = i with hP
  have hPx₀ : ¬ P x₀ := by
    obtain ⟨f, hf, hfx⟩ := hx₀
    exact fun h => hfx (h f hf)
  let ρ : ↥(coreMod n) →* Multiplicative ({i // P i} → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (fun i => vcoord v i)
      map_one' := rfl
      map_mul' := fun v w => rfl }
  have hker : ∀ v, v ∈ commV (F.map (coreAct n)) ↔ v ∈ ρ.ker := by
    intro v
    rw [mem_commV_iff_of_orbit hn hsame, MonoidHom.mem_ker]
    change _ ↔ Multiplicative.ofAdd (fun i : {i // P i} => vcoord v i) = 1
    rw [ofAdd_eq_one]
    constructor
    · intro h
      funext i
      exact h i i.2
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
  have hsurj : Function.Surjective ρ := by
    intro g
    set g' := Multiplicative.toAdd g
    set s := ∑ j, g' j with hs
    have hsum : ∑ i, ((if h : P i then g' ⟨i, h⟩ else 0) + (if i = x₀ then s else 0)) = 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
        ← Fintype.sum_subtype_add_sum_subtype P]
      have h1 : ∑ i : {i // P i}, (if h : P i then g' ⟨i, h⟩ else 0) = s :=
        Finset.sum_congr rfl fun i _ => dite_eq_left i.2
      have h2 : ∑ i : {i // ¬ P i}, (if h : P i then g' ⟨i, h⟩ else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => dite_eq_right i.2
      rw [h1, h2, add_zero]
      exact CharTwo.add_self_eq_zero s
    refine ⟨mkEven _ hsum, ?_⟩
    change Multiplicative.ofAdd (fun i : {i // P i} => vcoord (mkEven _ hsum) i) = g
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_ofAdd, vcoord_mkEven, dite_eq_left i.2,
      ite_eq_right (fun h : (i : Fin n) = x₀ => hPx₀ (h ▸ i.2)), add_zero]
  have h := Subgroup.card_ker_mul_card_range ρ
  rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top] at h
  have h3 : Nat.card (Multiplicative ({i // P i} → ZMod 2)) = 2 ^ Nat.card {i // P i} := by
    change Nat.card ({i // P i} → ZMod 2) = _
    rw [Nat.card_fun, Nat.card_zmod]
  rw [h3] at h
  rw [Nat.card_congr (Equiv.subtypeEquivRight hker), h]
  exact card_coreMod_mul_two hn

@[expose] def altOn (S : Finset (Fin n)) : Subgroup (Equiv.Perm (Fin n)) :=
  (alternatingGroup S).map Equiv.Perm.ofSubtype

theorem mem_altOn {S : Finset (Fin n)} {g : Equiv.Perm (Fin n)} :
    g ∈ altOn S ↔ (∀ x ∉ S, g x = x) ∧ Equiv.Perm.sign g = 1 := by
  rw [altOn, alternatingGroup.map_ofSubtype, Subgroup.mem_inf, Equiv.Perm.mem_range_ofSubtype_iff,
    Equiv.Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, h2⟩
    by_contra hne
    exact hx (h1 (Finset.mem_coe.2 (Equiv.Perm.mem_support.2 hne)))
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, h2⟩
    by_contra hne
    exact (Equiv.Perm.mem_support.1 (Finset.mem_coe.1 hx)) (h1 x hne)

theorem card_altOn {S : Finset (Fin n)} (hS : 2 ≤ S.card) :
    Nat.card (altOn S) = S.card.factorial / 2 := by
  rw [altOn, Subgroup.card_map_of_injective Equiv.Perm.ofSubtype_injective]
  have : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.1 (by rw [Fintype.card_coe]; omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem sign_eq_one_of_opResidual {F : Subgroup (Equiv.Perm (Fin n))} (hF : opResidual 2 F = F)
    {f : Equiv.Perm (Fin n)} (hf : f ∈ F) : Equiv.Perm.sign f = 1 := by
  have hle : opResidual 2 F ≤ alternatingGroup (Fin n) := by
    rw [opResidual, Subgroup.closure_le]
    rintro σ ⟨-, hodd⟩
    exact Equiv.Perm.mem_alternatingGroup.2
      (sign_eq_one_of_odd_orderOf (Nat.coprime_two_right.1 hodd))
  rw [← hF] at hf
  exact Equiv.Perm.mem_alternatingGroup.1 (hle hf)

open Classical in
@[expose] noncomputable def movFin (F : Subgroup (Equiv.Perm (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ f ∈ F, f i ≠ i

theorem mem_movFin {F : Subgroup (Equiv.Perm (Fin n))} {i : Fin n} :
    i ∈ movFin F ↔ ∃ f ∈ F, f i ≠ i := by
  unfold movFin
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem card_movFin_add (F : Subgroup (Equiv.Perm (Fin n))) :
    (movFin F).card + Nat.card {i : Fin n // ∀ f ∈ F, f i = i} = n := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => ∃ f ∈ F, f i ≠ i)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have e1 : (movFin F).card = (Finset.univ.filter fun i => ∃ f ∈ F, f i ≠ i).card := by
    unfold movFin
    congr
  have e2 : (Finset.univ.filter fun x : Fin n => ∀ f ∈ F, f x = x).card =
      (Finset.univ.filter fun a : Fin n => ¬∃ f ∈ F, f a ≠ a).card := by
    congr 1
    ext i
    simp
  omega

theorem le_altOn_movFin {F : Subgroup (Equiv.Perm (Fin n))} (hF : opResidual 2 F = F) :
    F ≤ altOn (movFin F) := by
  intro f hf
  refine mem_altOn.2 ⟨fun x hx => ?_, sign_eq_one_of_opResidual hF hf⟩
  by_contra hne
  exact hx (mem_movFin.2 ⟨f, hf, hne⟩)

end CFSG.CGT.PushingUpLit.BHS
