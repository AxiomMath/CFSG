module

public import CFSG.Holt.Induced

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction CFSG.Holt CFSG.Open

variable {X : Type*} [Fintype X] [DecidableEq X]

section Counting

private theorem two_mul_factorial_dvd {m : ℕ} (hm : 0 < m) (c : ℕ) :
    2 * (m.factorial * m.factorial * c.factorial) ∣ (2 * m + c).factorial := by
  obtain ⟨k, hk⟩ := Nat.two_dvd_centralBinom_of_one_le hm
  have h1 : (2 * m).factorial = m.centralBinom * m.factorial * m.factorial := by
    rw [Nat.centralBinom, ← Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega),
      show 2 * m - m = m by omega]
  refine dvd_trans ?_ (Nat.factorial_mul_factorial_dvd_factorial_add (2 * m) c)
  rw [h1, hk]
  exact ⟨k, by ring⟩

private def fibreStab {ι : Type*} (f : X → ι) : Subgroup (Perm X) where
  carrier := {g | ∀ x, f (g x) = f x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by
    change f (a (b x)) = f x
    rw [ha (b x), hb x]
  inv_mem' := fun {g} hg x => by
    simpa using (hg (g⁻¹ x)).symm

private theorem card_fibreStab {ι : Type*} [Fintype ι] [DecidableEq ι] (f : X → ι) :
    Nat.card (fibreStab f) = ∏ i, (Fintype.card {a // f a = i}).factorial := by
  rw [← DomMulAct.stabilizer_card f, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    ⟨fun h => funext h, fun h x => congrFun h x⟩)

omit [Fintype X] in
private theorem swap_mem_fibreStab {ι : Type*} {f : X → ι} {p q : X} (h : f p = f q) :
    swap p q ∈ fibreStab f := fun z => by
  rcases eq_or_ne z p with rfl | hp
  · rw [swap_apply_left, h]
  rcases eq_or_ne z q with rfl | hq
  · rw [swap_apply_right, h]
  · rw [swap_apply_of_ne_of_ne hp hq]

private theorem not_pow_dvd_card_fibreStab (f : X → Fin 3)
    (h01 : Fintype.card {a // f a = 0} = Fintype.card {a // f a = 1})
    (hpos : 0 < Fintype.card {a // f a = 0}) :
    ¬ 2 ^ ((Fintype.card X).factorial.factorization 2) ∣ Nat.card (fibreStab f) := by
  intro h
  rw [card_fibreStab, Fin.prod_univ_three, ← h01] at h
  have hn : Fintype.card X = 2 * Fintype.card {a // f a = 0} + Fintype.card {a // f a = 2} := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma, Fin.sum_univ_three]
    omega
  have hd := two_mul_factorial_dvd hpos (Fintype.card {a // f a = 2})
  rw [← hn] at hd
  have h2 : 2 ^ ((Fintype.card X).factorial.factorization 2 + 1) ∣ (Fintype.card X).factorial := by
    rw [pow_succ, mul_comm]
    exact dvd_trans (Nat.mul_dvd_mul_left 2 h) hd
  exact Nat.pow_succ_factorization_not_dvd (Nat.factorial_ne_zero _) Nat.prime_two h2

private theorem two_mul_card_dvd_of_le_alternatingGroup {H K : Subgroup (Perm X)} (hHK : H ≤ K)
    (hHA : H ≤ alternatingGroup X) {τ : Perm X} (hτK : τ ∈ K) (hτ : sign τ = -1) :
    2 * Nat.card H ∣ Nat.card K := by
  set A := (alternatingGroup X).subgroupOf K
  have hidx : A.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨τ, hτK⟩, fun b => ?_⟩
    simp only [A, Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_alternatingGroup, map_mul, hτ]
    rcases Int.units_eq_one_or (sign (b : Perm X)) with h | h <;> simp [h]
  have hle : H.subgroupOf K ≤ A := fun b hb => hHA hb
  have h1 : Nat.card H = Nat.card (H.subgroupOf K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv.symm
  rw [h1, ← Subgroup.card_mul_index A, hidx, mul_comm]
  exact Nat.mul_dvd_mul_right (Subgroup.card_dvd_of_le hle) 2

omit [DecidableEq X] in
theorem card_eq_of_fusionIsSylowIn_top {P : Subgroup (Perm X)} (hP : fusionIsSylowIn 2 P ⊤) :
    Nat.card P = 2 ^ ((Fintype.card X).factorial.factorization 2) := by
  rw [card_eq_of_fusionIsSylowIn hP, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card]

theorem two_mul_card_eq_of_fusionIsSylowIn_alternatingGroup (h2 : 2 ≤ Fintype.card X)
    {U : Subgroup (Perm X)} (hU : fusionIsSylowIn 2 U (alternatingGroup X)) :
    2 * Nat.card U = 2 ^ ((Fintype.card X).factorial.factorization 2) := by
  have : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have hA : 2 * Nat.card (alternatingGroup X) = (Fintype.card X).factorial := by
    rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm]
  have hA0 : Nat.card (alternatingGroup X) ≠ 0 := Nat.card_pos.ne'
  rw [card_eq_of_fusionIsSylowIn hU, ← hA, Nat.factorization_mul two_ne_zero hA0,
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one]

end Counting

section BinaryOrbits

variable {P : Subgroup (Perm X)}

omit [Fintype X] [DecidableEq X] in
private theorem apply_mem_orbit_iff {g : Perm X} (hg : g ∈ P) (z w : X) :
    g z ∈ orbit P w ↔ z ∈ orbit P w := by
  have : g z = (⟨g, hg⟩ : P) • z := rfl
  rw [this, ← orbit_eq_iff, orbit_smul, orbit_eq_iff]

private theorem exists_odd_mem_fibreStab {ι : Type*} [DecidableEq ι] {f : X → ι} {i : ι}
    (h : 2 ≤ Fintype.card {a // f a = i}) : ∃ τ ∈ fibreStab f, sign τ = -1 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, hpq⟩ := Fintype.exists_pair_of_one_lt_card h
  exact ⟨swap p q, swap_mem_fibreStab (hp.trans hq.symm),
    sign_swap fun e => hpq (Subtype.ext e)⟩

private theorem exists_fibreStab_of_orbit_ne {x y : X} (hne : orbit P x ≠ orbit P y)
    (h : Nat.card (orbit P x) = Nat.card (orbit P y)) :
    ∃ f : X → Fin 3, P ≤ fibreStab f ∧
      Fintype.card {a // f a = 0} = Fintype.card {a // f a = 1} ∧
      0 < Fintype.card {a // f a = 0} ∧
      (4 ≤ Fintype.card X → ∃ τ ∈ fibreStab f, sign τ = -1) := by
  classical
  have hdisj := (orbit.eq_or_disjoint x y).resolve_left hne
  let f : X → Fin 3 := fun z => if z ∈ orbit P x then 0 else if z ∈ orbit P y then 1 else 2
  have hf0 : ∀ z, f z = 0 ↔ z ∈ orbit P x := fun z => by
    by_cases hx : z ∈ orbit P x <;> by_cases hy : z ∈ orbit P y <;> simp [f, hx, hy]
  have hf1 : ∀ z, f z = 1 ↔ z ∈ orbit P y := fun z => by
    by_cases hx : z ∈ orbit P x
    · have : z ∉ orbit P y := Set.disjoint_left.1 hdisj hx
      simp [f, hx, this]
    · by_cases hy : z ∈ orbit P y <;> simp [f, hx, hy]
  have hc0 : Fintype.card {a // f a = 0} = Nat.card (orbit P x) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight hf0)
  have hc1 : Fintype.card {a // f a = 1} = Nat.card (orbit P y) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight hf1)
  have hpos : 0 < Fintype.card {a // f a = 0} := by
    rw [hc0]
    have : Nonempty (orbit P x) := ⟨⟨x, mem_orbit_self x⟩⟩
    exact Nat.card_pos
  refine ⟨f, fun g hg z => ?_, by rw [hc0, hc1, h], hpos, fun h4 => ?_⟩
  · simp only [f, apply_mem_orbit_iff hg]
  · have hn : Fintype.card X = Fintype.card {a // f a = 0} + Fintype.card {a // f a = 1} +
        Fintype.card {a // f a = 2} := by
      rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma, Fin.sum_univ_three]
    by_cases h2 : 2 ≤ Fintype.card {a // f a = 0}
    · exact exists_odd_mem_fibreStab h2
    · exact exists_odd_mem_fibreStab (i := 2) (by rw [hc0, hc1, ← h] at hn; rw [hc0] at h2; omega)

theorem orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_top (hP : fusionIsSylowIn 2 P ⊤)
    {x y : X} (h : Nat.card (orbit P x) = Nat.card (orbit P y)) : orbit P x = orbit P y := by
  by_contra hne
  obtain ⟨f, hPf, h01, hpos, -⟩ := exists_fibreStab_of_orbit_ne hne h
  exact not_pow_dvd_card_fibreStab f h01 hpos
    (card_eq_of_fusionIsSylowIn_top hP ▸ Subgroup.card_dvd_of_le hPf)

theorem orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup (h4 : 4 ≤ Fintype.card X)
    (hP : fusionIsSylowIn 2 P (alternatingGroup X)) {x y : X}
    (h : Nat.card (orbit P x) = Nat.card (orbit P y)) : orbit P x = orbit P y := by
  by_contra hne
  obtain ⟨f, hPf, h01, hpos, hodd⟩ := exists_fibreStab_of_orbit_ne hne h
  obtain ⟨τ, hτK, hτ⟩ := hodd h4
  have := two_mul_card_dvd_of_le_alternatingGroup hPf hP.1 hτK hτ
  rw [two_mul_card_eq_of_fusionIsSylowIn_alternatingGroup (by omega) hP] at this
  exact not_pow_dvd_card_fibreStab f h01 hpos this

end BinaryOrbits

section BinaryDigits

variable {P : Subgroup (Perm X)}

omit [DecidableEq X] in
private theorem testBit_card_iff_of_orbit_eq (hP2 : IsPGroup 2 P)
    (hdist : ∀ x y : X, Nat.card (orbit P x) = Nat.card (orbit P y) → orbit P x = orbit P y)
    (a : ℕ) : (Fintype.card X).testBit a ↔ ∃ x : X, Nat.card (orbit P x) = 2 ^ a := by
  classical
  let e : X → ℕ := fun x => Nat.log 2 (Nat.card (orbit P x))
  have he : ∀ x, 2 ^ e x = Nat.card (orbit P x) := fun x => by
    obtain ⟨k, hk⟩ := hP2.card_orbit x
    simp only [e, hk, Nat.log_pow (by norm_num : 1 < 2)]
  have hfib : ∀ x, (Finset.univ.filter fun z => e z = e x).card = 2 ^ e x := fun x => by
    rw [he, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · exact orbit_eq_iff.1 (hdist z x (by rw [← he, ← he, hz]))
    · simp only [e, orbit_eq_iff.2 hz]
  have hsum : ∑ b ∈ Finset.univ.image e, 2 ^ b = Fintype.card X := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := e)
      (fun x _ => Finset.mem_image_of_mem e (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hb
    exact (hfib x).symm
  have hA := Finset.toFinset_bitIndices_sum_two_pow (Finset.univ.image e)
  rw [hsum] at hA
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, hA, Finset.mem_image]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, (he x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Finset.mem_univ x, by simp only [e, hx, Nat.log_pow (by norm_num : 1 < 2)]⟩

theorem testBit_card_iff_of_fusionIsSylowIn_top (hP : fusionIsSylowIn 2 P ⊤) (a : ℕ) :
    (Fintype.card X).testBit a ↔ ∃ x : X, Nat.card (orbit P x) = 2 ^ a :=
  testBit_card_iff_of_orbit_eq hP.2.1
    (fun _ _ => orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_top hP) a

theorem testBit_card_iff_of_fusionIsSylowIn_alternatingGroup (h4 : 4 ≤ Fintype.card X)
    (hP : fusionIsSylowIn 2 P (alternatingGroup X)) (a : ℕ) :
    (Fintype.card X).testBit a ↔ ∃ x : X, Nat.card (orbit P x) = 2 ^ a :=
  testBit_card_iff_of_orbit_eq hP.2.1
    (fun _ _ => orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup h4 hP) a

theorem exists_testBit_card_orbit_of_fusionIsSylowIn_top (hP : fusionIsSylowIn 2 P ⊤) (x : X) :
    ∃ a, (Fintype.card X).testBit a ∧ Nat.card (orbit P x) = 2 ^ a := by
  obtain ⟨a, ha⟩ := hP.2.1.card_orbit x
  exact ⟨a, (testBit_card_iff_of_fusionIsSylowIn_top hP a).2 ⟨x, ha⟩, ha⟩

theorem exists_testBit_card_orbit_of_fusionIsSylowIn_alternatingGroup (h4 : 4 ≤ Fintype.card X)
    (hP : fusionIsSylowIn 2 P (alternatingGroup X)) (x : X) :
    ∃ a, (Fintype.card X).testBit a ∧ Nat.card (orbit P x) = 2 ^ a := by
  obtain ⟨a, ha⟩ := hP.2.1.card_orbit x
  exact ⟨a, (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup h4 hP a).2 ⟨x, ha⟩, ha⟩

theorem orbit_eq_of_fusionIsSylowIn_alternatingGroup_of_le (h4 : 4 ≤ Fintype.card X)
    {U Q : Subgroup (Perm X)} (hU : fusionIsSylowIn 2 U (alternatingGroup X))
    (hQ : IsPGroup 2 Q) (hUQ : U ≤ Q) (x : X) : orbit Q x = orbit U x := by
  have hQU : Q ⊓ alternatingGroup X = U :=
    hU.2.2 _ inf_le_right (hQ.to_le inf_le_left) (le_inf hUQ hU.1)
  have hconj : ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ ∈ U := fun q hq u hu => by
    rw [← hQU]
    exact ⟨Q.mul_mem (Q.mul_mem hq (hUQ hu)) (Q.inv_mem hq),
      (inferInstance : (alternatingGroup X).Normal).conj_mem u (hU.1 hu) q⟩
  have himage : ∀ q ∈ Q, (⇑q) '' orbit U x = orbit U (q x) := by
    intro q hq
    ext w
    constructor
    · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
      exact ⟨⟨q * u * q⁻¹, hconj q hq u u.2⟩, by
        simp [Subgroup.smul_def, Perm.smul_def]⟩
    · rintro ⟨u, rfl⟩
      refine ⟨(⟨q⁻¹ * u * q, by simpa using hconj q⁻¹ (Q.inv_mem hq) u u.2⟩ : U) • x,
        ⟨_, rfl⟩, ?_⟩
      simp [Subgroup.smul_def, Perm.smul_def]
  have hmem : ∀ q ∈ Q, q x ∈ orbit U x := fun q hq => by
    refine orbit_eq_iff.1 (orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup h4 hU ?_)
    rw [← himage q hq, Nat.card_image_of_injective q.injective]
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    exact hmem q q.2
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u, hUQ u.2⟩, rfl⟩

end BinaryDigits

section Transport

private theorem fusionIsSylowIn_inf_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {S K N : Subgroup G} (hS : fusionIsSylowIn 2 S K) (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) : fusionIsSylowIn 2 (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNK)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    simpa using (Subgroup.mem_normalizer_iff.1 (hKN (K.inv_mem hk)) x).1 (hPN hx)⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

omit [Fintype X] [DecidableEq X] in
theorem exists_ofSubtype_eq_of_mem_fixingSubgroup {Λ : Set X} [DecidablePred (· ∈ Λᶜ)]
    {g : Perm X} (hg : g ∈ fixingSubgroup (Perm X) Λ) :
    ∃ g' : Perm ↥Λᶜ, (ofSubtype g' : Perm X) = g := by
  have hfix' : ∀ x ∈ Λ, g x = x := fun x hx => by
    simpa [Perm.smul_def] using (mem_fixingSubgroup_iff _).1 hg x hx
  have h₁ : ∀ x, g x ∈ Λᶜ ↔ x ∈ Λᶜ := fun x => by
    simp only [Set.mem_compl_iff]
    refine not_congr ⟨fun h => ?_, fun h => by rwa [hfix' x h]⟩
    have := hfix' _ h
    rwa [g.injective this] at h
  exact ⟨subtypePerm g h₁, ofSubtype_subtypePerm h₁ fun x hx hxΛ => hx (hfix' x hxΛ)⟩

theorem map_ofSubtype_alternatingGroup_compl (Λ : Set X) [DecidablePred (· ∈ Λᶜ)] :
    (alternatingGroup ↥Λᶜ).map (ofSubtype : Perm ↥Λᶜ →* Perm X) =
      alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_inf, mem_alternatingGroup, mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_alternatingGroup] at hf
    exact ⟨by rw [sign_ofSubtype, hf], fun y hy => by
      rw [Perm.smul_def, ofSubtype_apply_of_not_mem f (by simpa using hy)]⟩
  · rintro ⟨hsign, hfix⟩
    obtain ⟨g', rfl⟩ := exists_ofSubtype_eq_of_mem_fixingSubgroup
      ((mem_fixingSubgroup_iff _).2 hfix)
    exact ⟨g', by rwa [mem_alternatingGroup, ← sign_ofSubtype], rfl⟩

theorem exists_fusionIsSylowIn_alternatingGroup_compl {Λ : Set X} [DecidablePred (· ∈ Λᶜ)]
    {V : Subgroup (Perm X)}
    (hV : fusionIsSylowIn 2 V (alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ)) :
    ∃ V' : Subgroup (Perm ↥Λᶜ), fusionIsSylowIn 2 V' (alternatingGroup ↥Λᶜ) ∧
      V'.map (ofSubtype : Perm ↥Λᶜ →* Perm X) = V := by
  rw [← map_ofSubtype_alternatingGroup_compl] at hV
  exact exists_fusionIsSylowIn_map_eq _ hV

end Transport

section LemmaFourOne

theorem fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup {Λ : Set X}
    (heven : Even (Nat.card ↥Λᶜ)) (h2 : Nat.card ↥Λᶜ ≠ 2) {V : Subgroup (Perm X)}
    (hV : fusionIsSylowIn 2 V (alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ)) :
    fixSet X V = Λ := by
  classical
  obtain ⟨V', hV', rfl⟩ := exists_fusionIsSylowIn_alternatingGroup_compl hV
  ext x
  constructor
  · intro hx
    by_contra hxΛ
    set y : ↥Λᶜ := ⟨x, hxΛ⟩
    have hfix : ∀ v ∈ V', v y = y := fun v hv => Subtype.ext (by
      have := hx (ofSubtype v) ⟨v, hv, rfl⟩
      rwa [Perm.smul_def, show x = (y : X) from rfl, ofSubtype_apply_coe] at this)
    have horb : orbit V' y = {y} := by
      ext w
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro ⟨v, rfl⟩
        exact hfix v v.2
      · rintro rfl
        exact mem_orbit_self y
    have hcard : Nat.card (orbit V' y) = 2 ^ 0 := by rw [horb, Nat.card_unique, pow_zero]
    have hn : Nat.card ↥Λᶜ = Fintype.card ↥Λᶜ := Nat.card_eq_fintype_card
    have hpos : 0 < Fintype.card ↥Λᶜ := Fintype.card_pos_iff.2 ⟨y⟩
    obtain ⟨k, hk⟩ := heven
    have h4 : 4 ≤ Fintype.card ↥Λᶜ := by omega
    have hbit := (testBit_card_iff_of_fusionIsSylowIn_alternatingGroup h4 hV' 0).2 ⟨y, hcard⟩
    rw [Nat.testBit_zero] at hbit
    simp only [decide_eq_true_eq] at hbit
    omega
  · intro hxΛ v hv
    exact (mem_fixingSubgroup_iff _).1 (hV.1 hv).2 x hxΛ

variable {U : Subgroup (Perm X)}

theorem fusionIsSylowIn_inf_fixingSubgroup (hU : fusionIsSylowIn 2 U (alternatingGroup X))
    {Λ : Set X} (hΛ : ∀ u ∈ U, ∀ x ∈ Λ, u x ∈ Λ) :
    fusionIsSylowIn 2 (U ⊓ fixingSubgroup (Perm X) Λ)
      (alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ) := by
  set N := alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ
  have hUN : U ⊓ fixingSubgroup (Perm X) Λ = U ⊓ N := by
    rw [← inf_assoc, inf_eq_left.2 hU.1]
  have hfixΛ : ∀ g : Perm X, g ∈ fixingSubgroup (Perm X) Λ ↔ ∀ x ∈ Λ, g x = x := fun g => by
    simp [mem_fixingSubgroup_iff, Perm.smul_def]
  have hnorm : U ≤ Subgroup.normalizer (N : Set (Perm X)) := fun u hu => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hconj : n ∈ alternatingGroup X ↔ u * n * u⁻¹ ∈ alternatingGroup X := by
      have : sign u * sign n * (sign u)⁻¹ = sign n := by
        rw [mul_comm (sign u), mul_assoc, mul_inv_cancel, mul_one]
      simp only [mem_alternatingGroup, map_mul, map_inv, this]
    simp only [N, Subgroup.mem_inf, hfixΛ, ← hconj]
    refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · have h' : n (u.symm x) = u.symm x := h _ (hΛ _ (U.inv_mem hu) x hx)
      simp only [Perm.mul_apply, Perm.inv_def, h', Equiv.apply_symm_apply]
    · have := h (u x) (hΛ u hu x hx)
      simpa [Perm.mul_apply] using this
  have hK : fusionIsSylowIn 2 U (U ⊔ N) :=
    ⟨le_sup_left, hU.2.1, fun P hPK hP hUP =>
      hU.2.2 P (hPK.trans (sup_le hU.1 inf_le_left)) hP hUP⟩
  rw [hUN]
  exact fusionIsSylowIn_inf_of_le_normalizer hK le_sup_right
    (sup_le hnorm Subgroup.le_normalizer)

theorem fixSet_inf_fixingSubgroup_eq (hU : fusionIsSylowIn 2 U (alternatingGroup X))
    {Λ : Set X} (hΛ : ∀ u ∈ U, ∀ x ∈ Λ, u x ∈ Λ) (heven : Even (Nat.card ↥Λᶜ))
    (h2 : Nat.card ↥Λᶜ ≠ 2) : fixSet X (U ⊓ fixingSubgroup (Perm X) Λ) = Λ :=
  fixSet_eq_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup heven h2
    (fusionIsSylowIn_inf_fixingSubgroup hU hΛ)

end LemmaFourOne

section Truncation

private def truncPerm (σ : Perm X) (s : Set X) [DecidablePred (· ∈ s)]
    (h : ∀ x, σ x ∈ s ↔ x ∈ s) : Perm X :=
  ofSubtype (σ.subtypePerm h)

omit [Fintype X] [DecidableEq X] in
private theorem truncPerm_apply_of_mem {σ : Perm X} {s : Set X} [DecidablePred (· ∈ s)]
    (h : ∀ x, σ x ∈ s ↔ x ∈ s) {x : X} (hx : x ∈ s) : truncPerm σ s h x = σ x := by
  simp [truncPerm, ofSubtype_apply_of_mem _ hx]

omit [Fintype X] [DecidableEq X] in
private theorem truncPerm_apply_of_notMem {σ : Perm X} {s : Set X} [DecidablePred (· ∈ s)]
    (h : ∀ x, σ x ∈ s ↔ x ∈ s) {x : X} (hx : x ∉ s) : truncPerm σ s h x = x :=
  ofSubtype_apply_of_not_mem _ hx

omit [DecidableEq X] in
private theorem truncPerm_mem_of_fusionIsSylowIn_top {P : Subgroup (Perm X)}
    (hP : fusionIsSylowIn 2 P ⊤) {ι : Type*} [DecidableEq ι] (f : X → ι)
    (hPf : ∀ p ∈ P, ∀ x y, f x = f y → f (p x) = f (p y)) {k : Perm X} (hk : k ∈ P)
    (hkf : ∀ x, f (k x) = f x) (i : ι)
    (h : ∀ x, k x ∈ {y | f y = i} ↔ x ∈ {y | f y = i}) :
    truncPerm k {y | f y = i} h ∈ P := by
  set K := P ⊓ fibreStab f
  have hKf : ∀ a ∈ K, ∀ x, f (a x) = f x := fun a ha => ha.2
  let Q : Subgroup (Perm X) :=
    { carrier := {σ | (∀ x, f (σ x) = f x) ∧ ∀ i, ∃ a ∈ K, ∀ x, f x = i → σ x = a x}
      one_mem' := ⟨fun x => rfl, fun i => ⟨1, K.one_mem, fun x _ => rfl⟩⟩
      mul_mem' := by
        rintro σ τ ⟨hσ, hσw⟩ ⟨hτ, hτw⟩
        refine ⟨fun x => by simp only [Perm.mul_apply, hσ, hτ], fun i => ?_⟩
        obtain ⟨a, ha, hax⟩ := hσw i
        obtain ⟨b, hb, hbx⟩ := hτw i
        refine ⟨a * b, K.mul_mem ha hb, fun x hx => ?_⟩
        simp only [Perm.mul_apply, hbx x hx]
        exact hax _ (by rw [hKf b hb, hx])
      inv_mem' := by
        rintro σ ⟨hσ, hσw⟩
        have hσ' : ∀ x, f (σ⁻¹ x) = f x := fun x => by simpa using (hσ (σ⁻¹ x)).symm
        refine ⟨hσ', fun i => ?_⟩
        obtain ⟨a, ha, hax⟩ := hσw i
        refine ⟨a⁻¹, K.inv_mem ha, fun x hx => ?_⟩
        have := hax _ ((hσ' x).trans hx)
        rw [eq_comm, Perm.inv_eq_iff_eq, ← this]
        simp }
  have hKQ : K ≤ Q := fun a ha => ⟨hKf a ha, fun _ => ⟨a, ha, fun _ _ => rfl⟩⟩
  have hQ2 : IsPGroup 2 Q := by
    obtain ⟨v, hv⟩ := IsPGroup.iff_card.1 hP.2.1
    refine fun σ => ⟨v, Subtype.ext ?_⟩
    obtain ⟨hσ, hσw⟩ := σ.2
    ext x
    obtain ⟨a, ha, hax⟩ := hσw (f x)
    have hpow : ∀ j, ((σ : Perm X) ^ j) x = (a ^ j) x := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih]
        refine hax _ ?_
        clear ih
        induction j with
        | zero => rfl
        | succ j ih => rw [pow_succ', Perm.mul_apply, hKf a ha, ih]
    have ha1 : a ^ 2 ^ v = 1 := by
      have := pow_card_eq_one' (G := P) (x := ⟨a, ha.1⟩)
      rw [hv] at this
      exact congrArg Subtype.val this
    rw [Subgroup.coe_pow, Subgroup.coe_one, hpow, ha1]
  have hconj : ∀ p ∈ P, ∀ σ ∈ Q, p * σ * p⁻¹ ∈ Q := by
    rintro p hp σ ⟨hσ, hσw⟩
    have hpi : p⁻¹ ∈ P := P.inv_mem hp
    refine ⟨fun x => ?_, fun i => ?_⟩
    · have := hPf p hp _ _ (hσ (p⁻¹ x))
      simpa [Perm.mul_apply] using this
    · by_cases hne : ∃ x₀, f x₀ = i
      · obtain ⟨x₀, hx₀⟩ := hne
        obtain ⟨a, ha, hax⟩ := hσw (f (p⁻¹ x₀))
        refine ⟨p * a * p⁻¹, ⟨P.mul_mem (P.mul_mem hp ha.1) hpi, fun y => ?_⟩, fun x hx => ?_⟩
        · have := hPf p hp _ _ (hKf a ha (p⁻¹ y))
          simpa [Perm.mul_apply] using this
        · simp only [Perm.mul_apply]
          rw [hax _ (hPf _ hpi _ _ (hx.trans hx₀.symm))]
      · exact ⟨1, K.one_mem, fun x hx => (hne ⟨x, hx⟩).elim⟩
  have hnorm : P ≤ Subgroup.normalizer (Q : Set (Perm X)) := fun p hp => by
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    refine ⟨hconj p hp σ, fun hσ => ?_⟩
    simpa [mul_assoc] using hconj p⁻¹ (P.inv_mem hp) _ hσ
  have hPQ : P ⊔ Q = P :=
    hP.2.2 _ le_top (IsPGroup.to_sup_of_normal_right' hP.2.1 hQ2 hnorm) le_sup_left
  refine (le_sup_right.trans hPQ.le) ⟨fun x => ?_, fun i' => ?_⟩
  · by_cases hx : f x = i
    · rw [truncPerm_apply_of_mem h hx, hkf]
    · rw [truncPerm_apply_of_notMem h hx]
  · by_cases hii : i' = i
    · subst hii
      exact ⟨k, ⟨hk, hkf⟩, fun x hx => truncPerm_apply_of_mem h hx⟩
    · exact ⟨1, K.one_mem, fun x hx => truncPerm_apply_of_notMem h (by
        simpa using fun e => hii (hx.symm.trans e))⟩

end Truncation

section Halves

omit [Fintype X] [DecidableEq X] in
private theorem card_orbit_mul_card_inf_stabilizer (M : Subgroup (Perm X)) [Finite M] (y : X) :
    Nat.card (orbit M y) * Nat.card ↥(M ⊓ stabilizer (Perm X) y) = Nat.card M := by
  rw [Nat.card_coe_set_eq, ← index_stabilizer, ← Subgroup.card_mul_index (stabilizer M y),
    mul_comm]
  congr 1
  exact Nat.card_congr
    { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Fintype X] [DecidableEq X] in
private theorem image_orbit_of_conj {M : Subgroup (Perm X)} {p : Perm X}
    (hp : ∀ m ∈ M, p * m * p⁻¹ ∈ M) (hp' : ∀ m ∈ M, p⁻¹ * m * p ∈ M) (y : X) :
    (⇑p) '' orbit M y = orbit M (p y) := by
  ext w
  constructor
  · rintro ⟨z, ⟨m, rfl⟩, rfl⟩
    exact ⟨⟨p * m * p⁻¹, hp m m.2⟩, by simp [Subgroup.smul_def, Perm.smul_def]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(⟨p⁻¹ * m * p, hp' m m.2⟩ : M) • y, ⟨_, rfl⟩, by
      simp [Subgroup.smul_def, Perm.smul_def]⟩

omit [DecidableEq X] in
private theorem exists_half_of_fusionIsSylowIn_top {P : Subgroup (Perm X)}
    (hP : fusionIsSylowIn 2 P ⊤) {y : X} (hO : 2 ≤ Nat.card (orbit P y)) :
    ∃ H₁ : Set X, H₁ ⊆ orbit P y ∧ y ∈ H₁ ∧ 2 * Nat.card H₁ = Nat.card (orbit P y) ∧
      (∀ p ∈ P, (∀ x, p x ∈ H₁ ↔ x ∈ H₁) ∨ (∀ x ∈ orbit P y, p x ∈ H₁ ↔ x ∉ H₁)) ∧
      ∀ z ∈ H₁, ∃ m ∈ P, (∀ x, m x ∈ H₁ ↔ x ∈ H₁) ∧ m y = z := by
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.1 hP.2.1
  set S := P ⊓ stabilizer (Perm X) y
  obtain ⟨a, ha⟩ := hP.2.1.card_orbit y
  obtain ⟨s', hs'⟩ := IsPGroup.iff_card.1 (hP.2.1.to_le (inf_le_left : S ≤ P))
  have hOS := card_orbit_mul_card_inf_stabilizer P y
  rw [ha, hs', hv, ← pow_add] at hOS
  have hsv : a + s' = v := Nat.pow_right_injective le_rfl hOS
  have ha1 : 1 ≤ a := by
    by_contra h0
    rw [show a = 0 by omega, pow_zero] at ha
    omega
  obtain ⟨M, hM, hSM, hMP⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (n := v - 1)
    Nat.prime_two (by rw [hs']; exact Nat.pow_dvd_pow 2 (by omega))
    (by rw [hv]; exact Nat.pow_dvd_pow 2 (by omega)) (inf_le_left : S ≤ P)
  have hidx : (M.subgroupOf P).index = 2 := by
    have h := Subgroup.card_mul_index (M.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMP).toEquiv, hM, hv] at h
    have h2 : 2 ^ v = 2 ^ (v - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have hconj : ∀ p ∈ P, ∀ m ∈ M, p * m * p⁻¹ ∈ M := fun p hp m hm => by
    have := hnorm.conj_mem ⟨m, hMP hm⟩ (Subgroup.mem_subgroupOf.2 hm) ⟨p, hp⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hconj' : ∀ p ∈ P, ∀ m ∈ M, p⁻¹ * m * p ∈ M := fun p hp m hm => by
    simpa using hconj p⁻¹ (P.inv_mem hp) m hm
  set H₁ := orbit M y
  have hMS : M ⊓ stabilizer (Perm X) y = S :=
    le_antisymm (inf_le_inf_right _ hMP) (le_inf hSM inf_le_right)
  have hcard : 2 * Nat.card H₁ = Nat.card (orbit P y) := by
    have hM' := card_orbit_mul_card_inf_stabilizer M y
    rw [hMS, hs', hM] at hM'
    rw [ha]
    have : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]
    congr 1
    refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ s' by positivity) ?_
    rw [hM', ← pow_add]
    congr 1
    omega
  have hH₁O : H₁ ⊆ orbit P y := fun z ⟨m, hm⟩ => ⟨⟨m, hMP m.2⟩, hm⟩
  have himg : ∀ p ∈ P, (⇑p) '' H₁ = orbit M (p y) := fun p hp =>
    image_orbit_of_conj (hconj p hp) (hconj' p hp) y
  have hpres : ∀ p ∈ P, p y ∈ H₁ → ∀ x, p x ∈ H₁ ↔ x ∈ H₁ := fun p hp hpy x => by
    have h : (⇑p) '' H₁ = H₁ := by rw [himg p hp, orbit_eq_iff.2 hpy]
    constructor
    · intro hx
      have hx' : p x ∈ (⇑p) '' H₁ := by rw [h]; exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      rwa [← p.injective hzx]
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
  have hswap : ∀ p ∈ P, p y ∉ H₁ → (⇑p) '' H₁ = orbit P y \ H₁ := fun p hp hpy => by
    have hdisj : Disjoint (orbit M (p y)) H₁ :=
      (orbit.eq_or_disjoint (p y) y).resolve_left fun h => hpy (orbit_eq_iff.1 h)
    rw [himg p hp]
    have hsub : orbit M (p y) ⊆ orbit P y := fun z ⟨m, hm⟩ => by
      rw [← hm]
      exact ⟨⟨m * p, P.mul_mem (hMP m.2) hp⟩, by simp [Subgroup.smul_def, Perm.smul_def]⟩
    have hc : Nat.card (orbit M (p y)) = Nat.card H₁ := by
      rw [← himg p hp, Nat.card_image_of_injective p.injective]
    refine Set.eq_of_subset_of_ncard_le (fun z hz => ⟨hsub hz, Set.disjoint_left.1 hdisj hz⟩)
      ?_ (Set.toFinite _)
    rw [Set.ncard_sdiff hH₁O, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, hc]
    omega
  refine ⟨H₁, hH₁O, mem_orbit_self y, hcard, fun p hp => ?_, fun z hz => ?_⟩
  · by_cases hpy : p y ∈ H₁
    · exact Or.inl (hpres p hp hpy)
    · refine Or.inr fun x hx => ⟨fun hpx hxH => ?_, fun hxH => ?_⟩
      · have : p x ∈ (⇑p) '' H₁ := ⟨x, hxH, rfl⟩
        rw [hswap p hp hpy] at this
        exact this.2 hpx
      · have hpi : p⁻¹ y ∉ H₁ := fun h' => by
          have h1 := hpres p⁻¹ (P.inv_mem hp) h' (p y)
          rw [show p⁻¹ (p y) = y by simp] at h1
          exact hpy (h1.1 (mem_orbit_self y))
        have : x ∈ (⇑p⁻¹) '' H₁ := by rw [hswap _ (P.inv_mem hp) hpi]; exact ⟨hx, hxH⟩
        obtain ⟨w, hw, hwx⟩ := this
        rw [← hwx]
        simpa using hw
  · obtain ⟨m, rfl⟩ := hz
    exact ⟨m, hMP m.2, hpres m (hMP m.2) ⟨m, rfl⟩, rfl⟩

end Halves

section CentralEven

omit [Fintype X] [DecidableEq X] in
private theorem truncPerm_eq_mul_diff {σ : Perm X} {A B : Set X} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] [DecidablePred (· ∈ B \ A)] (hAB : A ⊆ B)
    (hA : ∀ x, σ x ∈ A ↔ x ∈ A) (hB : ∀ x, σ x ∈ B ↔ x ∈ B)
    (hBA : ∀ x, σ x ∈ B \ A ↔ x ∈ B \ A) :
    truncPerm σ B hB = truncPerm σ A hA * truncPerm σ (B \ A) hBA := by
  ext x
  rw [Perm.mul_apply]
  by_cases hxA : x ∈ A
  · rw [truncPerm_apply_of_mem hB (hAB hxA), truncPerm_apply_of_notMem hBA (fun h => h.2 hxA),
      truncPerm_apply_of_mem hA hxA]
  · by_cases hxB : x ∈ B
    · rw [truncPerm_apply_of_mem hB hxB, truncPerm_apply_of_mem hBA ⟨hxB, hxA⟩,
        truncPerm_apply_of_notMem hA (fun h => hxA ((hA x).1 h))]
    · rw [truncPerm_apply_of_notMem hB hxB, truncPerm_apply_of_notMem hBA (fun h => hxB h.1),
        truncPerm_apply_of_notMem hA (fun h => hxB (hAB h))]

omit [Fintype X] [DecidableEq X] in
private theorem image_orbit_of_commute {P : Subgroup (Perm X)} {c : Perm X}
    (hc : ∀ p ∈ P, Commute c p) (y : X) : (⇑c) '' orbit P y = orbit P (c y) :=
  image_orbit_of_conj (fun m hm => by rw [(hc m hm).eq, mul_inv_cancel_right]; exact hm)
    (fun m hm => by rw [mul_assoc, ← (hc m hm).eq, inv_mul_cancel_left]; exact hm) y

omit [Fintype X] [DecidableEq X] in
private theorem apply_mem_orbit_iff_of_commute {P : Subgroup (Perm X)}
    (hdist : ∀ x y : X, Nat.card (orbit P x) = Nat.card (orbit P y) → orbit P x = orbit P y)
    {c : Perm X} (hc : ∀ p ∈ P, Commute c p) (x y : X) :
    c x ∈ orbit P y ↔ x ∈ orbit P y := by
  have hcx : orbit P (c x) = orbit P x :=
    hdist _ _ (by rw [← image_orbit_of_commute hc, Nat.card_image_of_injective c.injective])
  rw [← orbit_eq_iff, hcx, orbit_eq_iff]

private structure IsHalf (P : Subgroup (Perm X)) (y : X) (H₁ : Set X) : Prop where
  subset : H₁ ⊆ orbit P y
  mem : y ∈ H₁
  card : 2 * Nat.card H₁ = Nat.card (orbit P y)
  perm : ∀ p ∈ P, (∀ x, p x ∈ H₁ ↔ x ∈ H₁) ∨ (∀ x ∈ orbit P y, p x ∈ H₁ ↔ x ∉ H₁)
  trans : ∀ z ∈ H₁, ∃ m ∈ P, (∀ x, m x ∈ H₁ ↔ x ∈ H₁) ∧ m y = z
  two_le : 2 ≤ Nat.card H₁

omit [DecidableEq X] in
private theorem exists_isHalf {P : Subgroup (Perm X)} (hP : fusionIsSylowIn 2 P ⊤) {y : X}
    (hO : 4 ≤ Nat.card (orbit P y)) : ∃ H₁, IsHalf P y H₁ := by
  obtain ⟨H₁, h1, h2, h3, h4, h5⟩ :=
    exists_half_of_fusionIsSylowIn_top hP (y := y) (by omega)
  exact ⟨H₁, h1, h2, h3, h4, h5, by omega⟩

omit [Fintype X] [DecidableEq X] in
private theorem IsHalf.exists_label {P : Subgroup (Perm X)} {y : X} {H₁ : Set X}
    (hH : IsHalf P y H₁) : ∃ f : X → Fin 3, (∀ x, f x = 0 ↔ x ∈ H₁) ∧
      (∀ x, f x = 1 ↔ x ∈ orbit P y ∧ x ∉ H₁) ∧
      ∀ p ∈ P, ∀ x x', f x = f x' → f (p x) = f (p x') := by
  classical
  let f : X → Fin 3 := fun x => if x ∈ H₁ then 0 else if x ∈ orbit P y then 1 else 2
  have hf0 : ∀ x ∈ H₁, f x = 0 := fun x hx => by simp [f, hx]
  have hf1 : ∀ x ∉ H₁, x ∈ orbit P y → f x = 1 := fun x hx hxO => by simp [f, hx, hxO]
  have hf2 : ∀ x ∉ orbit P y, f x = 2 := fun x hxO => by
    have hxH : x ∉ H₁ := fun h => hxO (hH.subset h)
    simp [f, hxH, hxO]
  have hPO : ∀ p ∈ P, ∀ x, p x ∈ orbit P y ↔ x ∈ orbit P y := fun p hp x =>
    apply_mem_orbit_iff hp x y
  refine ⟨f, fun x => ?_, fun x => ?_, fun p hp => ?_⟩
  · by_cases hx : x ∈ H₁
    · simp [hf0 x hx, hx]
    · by_cases hxO : x ∈ orbit P y
      · simp [hf1 x hx hxO, hx]
      · simp [hf2 x hxO, hx]
  · by_cases hx : x ∈ H₁
    · simp [hf0 x hx, hx]
    · by_cases hxO : x ∈ orbit P y
      · simp [hf1 x hx hxO, hx, hxO]
      · simp [hf2 x hxO, hxO]
  · suffices ∃ π : Fin 3 → Fin 3, ∀ x, f (p x) = π (f x) by
      obtain ⟨π, hπ⟩ := this
      intro x x' hxx'
      rw [hπ, hπ, hxx']
    rcases hH.perm p hp with hpres | hswap
    · refine ⟨id, fun x => ?_⟩
      by_cases hx : x ∈ H₁
      · rw [hf0 x hx, hf0 _ ((hpres x).2 hx), id]
      · by_cases hxO : x ∈ orbit P y
        · rw [hf1 x hx hxO, hf1 _ (fun h' => hx ((hpres x).1 h')) ((hPO p hp x).2 hxO), id]
        · rw [hf2 x hxO, hf2 _ (fun h' => hxO ((hPO p hp x).1 h')), id]
    · refine ⟨fun i => if i = 0 then 1 else if i = 1 then 0 else 2, fun x => ?_⟩
      by_cases hxO : x ∈ orbit P y
      · by_cases hx : x ∈ H₁
        · rw [hf0 x hx, hf1 _ (fun h' => ((hswap x hxO).1 h') hx) ((hPO p hp x).2 hxO)]
          rfl
        · rw [hf1 x hx hxO, hf0 _ ((hswap x hxO).2 hx)]
          rfl
      · rw [hf2 x hxO, hf2 _ (fun h' => hxO ((hPO p hp x).1 h'))]
        rfl

omit [DecidableEq X] in
private theorem IsHalf.exists_trunc {P : Subgroup (Perm X)} (hP : fusionIsSylowIn 2 P ⊤)
    {y : X} {H₁ : Set X} (hH : IsHalf P y H₁) {m : Perm X} (hmP : m ∈ P)
    (hmH : ∀ x, m x ∈ H₁ ↔ x ∈ H₁) (B : Set X) (hB : B = H₁ ∨ B = orbit P y \ H₁) :
    ∃ m' ∈ P, (∀ x ∈ B, m' x = m x) ∧ ∀ x ∉ B, m' x = x := by
  classical
  obtain ⟨f, hf0, hf1, hPf⟩ := hH.exists_label
  have hmO : ∀ x, m x ∈ orbit P y ↔ x ∈ orbit P y := fun x => apply_mem_orbit_iff hmP x y
  have hmf : ∀ x, f (m x) = f x := fun x => by
    by_cases hx : x ∈ H₁
    · rw [(hf0 x).2 hx, (hf0 _).2 ((hmH x).2 hx)]
    · by_cases hxO : x ∈ orbit P y
      · rw [(hf1 x).2 ⟨hxO, hx⟩, (hf1 _).2 ⟨(hmO x).2 hxO, fun h' => hx ((hmH x).1 h')⟩]
      · have h1 : f x ≠ 0 := fun h' => hxO (hH.subset ((hf0 x).1 h'))
        have h2 : f x ≠ 1 := fun h' => hxO ((hf1 x).1 h').1
        have h3 : f (m x) ≠ 0 := fun h' => hxO ((hmO x).1 (hH.subset ((hf0 _).1 h')))
        have h4 : f (m x) ≠ 1 := fun h' => hxO ((hmO x).1 ((hf1 _).1 h').1)
        omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, ∀ x, x ∈ B ↔ f x = i := by
    rcases hB with rfl | rfl
    · exact ⟨0, fun x => (hf0 x).symm⟩
    · exact ⟨1, fun x => by rw [hf1 x]; rfl⟩
  have hmi : ∀ x, m x ∈ {w | f w = i} ↔ x ∈ {w | f w = i} := fun x => by
    change f (m x) = i ↔ f x = i
    rw [hmf]
  refine ⟨_, truncPerm_mem_of_fusionIsSylowIn_top hP f hPf hmP hmf i hmi, fun x hx => ?_,
    fun x hx => ?_⟩
  · exact truncPerm_apply_of_mem hmi ((hi x).1 hx)
  · exact truncPerm_apply_of_notMem hmi (fun h' => hx ((hi x).2 h'))

omit [DecidableEq X] in
private theorem IsHalf.apply_mem_iff_of_commute {P : Subgroup (Perm X)}
    (hP : fusionIsSylowIn 2 P ⊤) {y : X} {H₁ : Set X} (hH : IsHalf P y H₁) {c : Perm X}
    (hc : ∀ p ∈ P, Commute c p) (x : X) : c x ∈ H₁ ↔ x ∈ H₁ := by
  obtain ⟨z, hzH, hzy⟩ : ∃ z ∈ H₁, z ≠ y := by
    by_contra hno
    have : H₁ = {y} := Set.eq_singleton_iff_unique_mem.2 ⟨hH.mem, fun w hw => by
      by_contra hwy; exact hno ⟨w, hw, hwy⟩⟩
    have h2 := hH.two_le
    rw [this, Nat.card_unique] at h2
    omega
  obtain ⟨m, hmP, hmH, hmy⟩ := hH.trans z hzH
  obtain ⟨m₁, hm₁P, hm₁H, hm₁H'⟩ := hH.exists_trunc hP hmP hmH H₁ (Or.inl rfl)
  have hcy : c y ∈ H₁ := by
    by_contra hcy
    have := congrArg (· y) (hc _ hm₁P).eq
    simp only [Perm.mul_apply, hm₁H y hH.mem, hmy, hm₁H' _ hcy] at this
    exact hzy (c.injective this)
  have hmaps : ∀ x ∈ H₁, c x ∈ H₁ := fun x hx => by
    obtain ⟨m', hm'P, hm'H, rfl⟩ := hH.trans x hx
    have := congrArg (· y) (hc m' hm'P).eq
    simp only [Perm.mul_apply] at this
    rw [this]
    exact (hm'H _).2 hcy
  have himgH : (⇑c) '' H₁ = H₁ :=
    Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps)
      (by rw [Set.ncard_image_of_injective _ c.injective]) (Set.toFinite _)
  refine ⟨fun hx => ?_, hmaps x⟩
  rw [← himgH] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  rwa [← c.injective hwx]

private theorem sign_truncPerm_orbit_eq_one {P : Subgroup (Perm X)} (hP : fusionIsSylowIn 2 P ⊤)
    {c : Perm X} (hc : ∀ p ∈ P, Commute c p) {y : X} (hO : 4 ≤ Nat.card (orbit P y))
    [DecidablePred (· ∈ orbit P y)] (h : ∀ x, c x ∈ orbit P y ↔ x ∈ orbit P y) :
    sign (truncPerm c (orbit P y) h) = 1 := by
  classical
  obtain ⟨H₁, hH⟩ := exists_isHalf hP hO
  have hPO : ∀ p ∈ P, ∀ x, p x ∈ orbit P y ↔ x ∈ orbit P y := fun p hp x =>
    apply_mem_orbit_iff hp x y
  have hcH := hH.apply_mem_iff_of_commute hP hc
  have hcH₂ : ∀ x, c x ∈ orbit P y \ H₁ ↔ x ∈ orbit P y \ H₁ := fun x => by
    simp only [Set.mem_sdiff, h, hcH]
  rw [truncPerm_eq_mul_diff hH.subset hcH h hcH₂]
  obtain ⟨z', hz'O, hz'H⟩ : ∃ z' ∈ orbit P y, z' ∉ H₁ := by
    by_contra hno
    have hsub : orbit P y ⊆ H₁ := fun w hw => by
      by_contra hwH; exact hno ⟨w, hw, hwH⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at this
    have := hH.card
    omega
  obtain ⟨⟨g, hgP⟩, hgy⟩ := hz'O
  change g y = z' at hgy
  have hgswap : ∀ x ∈ orbit P y, g x ∈ H₁ ↔ x ∉ H₁ := by
    rcases hH.perm g hgP with hpres | hswap
    · exact absurd ((hpres y).2 hH.mem) (hgy ▸ hz'H)
    · exact hswap
  have hconj : truncPerm c (orbit P y \ H₁) hcH₂ = g * truncPerm c H₁ hcH * g⁻¹ := by
    ext x
    simp only [Perm.mul_apply]
    have hgx : g (g⁻¹ x) = x := by simp
    by_cases hxO : x ∈ orbit P y
    · have hgO : g⁻¹ x ∈ orbit P y := (hPO _ (P.inv_mem hgP) x).2 hxO
      by_cases hxH : x ∈ H₁
      · have hgH : g⁻¹ x ∉ H₁ := fun h' => (hgswap _ hgO).1 (by rw [hgx]; exact hxH) h'
        rw [truncPerm_apply_of_notMem hcH₂ (fun h' => h'.2 hxH),
          truncPerm_apply_of_notMem hcH hgH, hgx]
      · have hgH : g⁻¹ x ∈ H₁ := by
          by_contra h'
          have := (hgswap _ hgO).2 h'
          rw [hgx] at this
          exact hxH this
        rw [truncPerm_apply_of_mem hcH₂ ⟨hxO, hxH⟩, truncPerm_apply_of_mem hcH hgH]
        have := congrArg (· (g⁻¹ x)) (hc g hgP).eq
        simp only [Perm.mul_apply, hgx] at this
        exact this
    · have hgO : g⁻¹ x ∉ orbit P y := fun h' => hxO ((hPO _ (P.inv_mem hgP) x).1 h')
      rw [truncPerm_apply_of_notMem hcH₂ (fun h' => hxO h'.1),
        truncPerm_apply_of_notMem hcH (fun h' => hgO (hH.subset h')), hgx]
  rw [map_mul, hconj, map_mul, map_mul, map_inv, mul_comm (sign g), mul_assoc,
    mul_inv_cancel, mul_one, Int.units_mul_self]

private theorem four_le_card_orbit_of_fusionIsSylowIn_top (h4 : 4 ∣ Fintype.card X)
    {P : Subgroup (Perm X)} (hP : fusionIsSylowIn 2 P ⊤) (y : X) :
    4 ≤ Nat.card (orbit P y) := by
  obtain ⟨a, ha, hcard⟩ := exists_testBit_card_orbit_of_fusionIsSylowIn_top hP y
  obtain ⟨k, hk⟩ := h4
  have ha2 : 2 ≤ a := by
    by_contra hlt
    interval_cases a
    · rw [Nat.testBit_zero] at ha
      simp only [decide_eq_true_eq] at ha
      omega
    · rw [Nat.testBit_succ, Nat.testBit_zero] at ha
      simp only [decide_eq_true_eq] at ha
      omega
  rw [hcard]
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2

private theorem sign_eq_one_of_commute_of_fusionIsSylowIn_top (h4 : 4 ∣ Fintype.card X)
    {P : Subgroup (Perm X)} (hP : fusionIsSylowIn 2 P ⊤) {c : Perm X}
    (hc : ∀ p ∈ P, Commute c p) : sign c = 1 := by
  classical
  have hdist : ∀ x y : X, Nat.card (orbit P x) = Nat.card (orbit P y) → orbit P x = orbit P y :=
    fun _ _ => orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_top hP
  have key : ∀ k, ∀ B : Set X, Nat.card B = k → (∀ p ∈ P, ∀ x, p x ∈ B ↔ x ∈ B) →
      ∀ (_ : DecidablePred (· ∈ B)) (hB : ∀ x, c x ∈ B ↔ x ∈ B),
        sign (truncPerm c B hB) = 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro B hk hPB _ hB
      by_cases hne : B.Nonempty
      · obtain ⟨y, hy⟩ := hne
        have hOB : orbit P y ⊆ B := by
          rintro w ⟨p, rfl⟩
          exact (hPB p p.2 y).2 hy
        have hcO : ∀ x, c x ∈ orbit P y ↔ x ∈ orbit P y := fun x =>
          apply_mem_orbit_iff_of_commute hdist hc x y
        have hBO : ∀ x, c x ∈ B \ orbit P y ↔ x ∈ B \ orbit P y := fun x => by
          simp only [Set.mem_sdiff, hB, hcO]
        rw [truncPerm_eq_mul_diff hOB hcO hB hBO, map_mul,
          sign_truncPerm_orbit_eq_one hP hc (four_le_card_orbit_of_fusionIsSylowIn_top h4 hP y)
            hcO, one_mul]
        refine ih _ ?_ (B \ orbit P y) rfl (fun p hp x => ?_) _ hBO
        · rw [← hk, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
          exact Set.ncard_lt_ncard ⟨Set.sdiff_subset, fun h' => (h' hy).2 (mem_orbit_self y)⟩
            (Set.toFinite B)
        · simp only [Set.mem_sdiff, hPB p hp, apply_mem_orbit_iff hp]
      · have h1 : truncPerm c B hB = 1 := by
          ext x
          exact truncPerm_apply_of_notMem hB (fun hx => hne ⟨x, hx⟩)
        rw [h1, map_one]
  have huniv : ∀ x, c x ∈ (Set.univ : Set X) ↔ x ∈ Set.univ := fun x => by simp
  have hc1 : truncPerm c Set.univ huniv = c := by
    ext x
    exact truncPerm_apply_of_mem huniv (Set.mem_univ x)
  rw [← hc1]
  exact key _ _ rfl (fun p _ x => by simp) _ huniv

end CentralEven

section FCent

omit [Fintype X] [DecidableEq X] in
private theorem truncPerm_pow_apply {σ : Perm X} {s : Set X} [DecidablePred (· ∈ s)]
    (h : ∀ x, σ x ∈ s ↔ x ∈ s) (j : ℕ) (x : X) :
    (truncPerm σ s h ^ j) x = if x ∈ s then (σ ^ j) x else x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    by_cases hx : x ∈ s
    · have hjx : (σ ^ j) x ∈ s := by
        clear ih
        induction j with
        | zero => simpa using hx
        | succ j ih' => rw [pow_succ', Perm.mul_apply]; exact (h _).2 ih'
      simp only [hx, ↓reduceIte]
      rw [truncPerm_apply_of_mem h hjx]
    · simp only [hx, ↓reduceIte]
      rw [truncPerm_apply_of_notMem h hx]

variable {U : Subgroup (Perm X)}

private theorem eq_one_of_commute_of_orderOf_prime (h4 : 4 ≤ Fintype.card X)
    (hU : fusionIsSylowIn 2 U (alternatingGroup X)) {h : Perm X} (hh : ∀ u ∈ U, Commute h u)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf h = p) : h = 1 := by
  classical
  have hdist : ∀ x y : X, Nat.card (orbit U x) = Nat.card (orbit U y) → orbit U x = orbit U y :=
    fun _ _ => orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_alternatingGroup h4 hU
  ext x
  rw [Perm.one_apply]
  by_contra hx
  have hO : ∀ w, h w ∈ orbit U x ↔ w ∈ orbit U x := fun w =>
    apply_mem_orbit_iff_of_commute hdist hh w x
  have hmove : ∀ w ∈ orbit U x, h w ≠ w := by
    rintro w ⟨u, rfl⟩ hw
    apply hx
    have := congrArg (· x) (hh u u.2).eq
    simp only [Perm.mul_apply] at this
    change h ((u : Perm X) x) = (u : Perm X) x at hw
    rw [hw] at this
    exact (u : Perm X).injective this.symm
  set t := truncPerm h (orbit U x) hO
  have ht : t ^ p = 1 := by
    ext w
    rw [truncPerm_pow_apply, ← hord, pow_orderOf_eq_one, Perm.one_apply, ite_self]
  have hpg : IsPGroup p (Subgroup.zpowers t) := by
    have hdvd := orderOf_dvd_of_pow_eq_one ht
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hfix : fixedPoints (Subgroup.zpowers t) X = (orbit U x)ᶜ := by
    ext w
    simp only [mem_fixedPoints, Set.mem_compl_iff]
    constructor
    · intro hw hwO
      have := hw ⟨t, Subgroup.mem_zpowers t⟩
      change t w = w at this
      rw [truncPerm_apply_of_mem hO hwO] at this
      exact hmove w hwO this
    · intro hwO g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
      change (g : Perm X) w = w
      rw [← hk]
      exact zpow_apply_eq_self_of_apply_eq_self (truncPerm_apply_of_notMem hO hwO) k
  have : Fact p.Prime := ⟨hp⟩
  have hmod := hpg.card_modEq_card_fixedPoints X
  rw [hfix, Nat.card_coe_set_eq, ← Set.ncard_add_ncard_compl (orbit U x)] at hmod
  have h0 : (orbit U x).ncard + (orbit U x)ᶜ.ncard ≡ 0 + (orbit U x)ᶜ.ncard [MOD p] := by
    rwa [zero_add]
  have hdvd : p ∣ (orbit U x).ncard :=
    Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_right_cancel' _ h0)
  obtain ⟨a, ha⟩ := hU.2.1.card_orbit x
  rw [← Nat.card_coe_set_eq, ha] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem mem_of_commute_of_fusionIsSylowIn_alternatingGroup (h4 : 4 ∣ Fintype.card X)
    (hU : fusionIsSylowIn 2 U (alternatingGroup X)) {g : Perm X}
    (hg : ∀ u ∈ U, Commute g u) : g ∈ U := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h0 | hpos
  · have : IsEmpty X := Fintype.card_eq_zero_iff.1 h0
    rw [Subsingleton.elim g 1]
    exact U.one_mem
  have hn4 : 4 ≤ Fintype.card X := Nat.le_of_dvd hpos h4
  have hg2 : IsPGroup 2 (Subgroup.zpowers g) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos g).ne' fun {d} hd hdg => ?_⟩
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card (G := Subgroup.zpowers g) d
      (by rwa [Fintype.card_zpowers])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 k.2
    have hkC : ∀ u ∈ U, Commute (k : Perm X) u := fun u hu => by
      rw [← hn]
      exact (hg u hu).zpow_left n
    have h1 := eq_one_of_commute_of_orderOf_prime hn4 hU hkC hd hd2
      (by rw [Subgroup.orderOf_coe, hk])
    rw [show k = 1 from Subtype.ext h1, orderOf_one] at hk
    exact hd.one_lt.ne hk
  have hgU : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set (Perm X)) :=
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun u hu => (hg u hu).eq.symm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ : IsPGroup 2 ↥(U ⊔ Subgroup.zpowers g) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hg2 hU.2.1 hgU
  by_cases hgA : g ∈ alternatingGroup X
  · have := hU.2.2 _ (sup_le hU.1 (Subgroup.zpowers_le.2 hgA)) hQ le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  · exfalso
    have hsign : sign g = -1 :=
      (Int.units_eq_one_or (sign g)).resolve_left fun h1 => hgA (mem_alternatingGroup.2 h1)
    obtain ⟨R, hQR, hR⟩ := exists_fusionIsSylowIn_ge hQ le_top
    have hdvd := two_mul_card_dvd_of_le_alternatingGroup (le_sup_left : U ≤ U ⊔ _) hU.1
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)) hsign
    rw [two_mul_card_eq_of_fusionIsSylowIn_alternatingGroup (by omega) hU] at hdvd
    have hQR' : U ⊔ Subgroup.zpowers g = R := Subgroup.eq_of_le_of_card_ge hQR
      (by rw [card_eq_of_fusionIsSylowIn_top hR]; exact Nat.le_of_dvd Nat.card_pos hdvd)
    have hcent : U ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer {g} :=
      sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hg u hu).eq.symm)
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
    have hgR : ∀ r ∈ R, Commute g r := fun r hr => by
      rw [← hQR'] at hr
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hcent hr)).symm
    exact hgA (mem_alternatingGroup.2 (sign_eq_one_of_commute_of_fusionIsSylowIn_top h4 hR hgR))

end FCent

section HalfSystems

theorem sign_eq_of_sq_eq_one_of_forall_apply_ne {σ : Perm X} (hσ : σ ^ 2 = 1)
    (hfree : ∀ x, σ x ≠ x) : sign σ = (-1) ^ (Fintype.card X / 2) := by
  have hk := cycleType_of_pow_prime_eq_one (p := 2) hσ
  have hsupp : σ.support.card = Fintype.card X := by
    rw [← Finset.card_univ]
    congr 1
    ext x
    simp [mem_support, hfree x]
  have hsum := sum_cycleType σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul, hsupp] at hsum
  rw [sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    pow_add, pow_mul', Int.units_sq, one_pow, one_mul, ← hsum, Nat.mul_div_cancel _ two_pos]

theorem mem_alternatingGroup_of_sq_eq_one_of_forall_apply_ne (h4 : 4 ∣ Fintype.card X)
    {σ : Perm X} (hσ : σ ^ 2 = 1) (hfree : ∀ x, σ x ≠ x) : σ ∈ alternatingGroup X := by
  rw [mem_alternatingGroup, sign_eq_of_sq_eq_one_of_forall_apply_ne hσ hfree]
  obtain ⟨k, hk⟩ := h4
  rw [hk, show 4 * k / 2 = 2 * k by omega, pow_mul, Int.units_sq, one_pow]

theorem exists_half_system_of_fusionIsSylowIn_top {P : Subgroup (Perm X)}
    (hP : fusionIsSylowIn 2 P ⊤) {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card X = 2 ^ n) :
    ∃ H₁ : Set X, 2 * Nat.card H₁ = 2 ^ n ∧
      (∀ p ∈ P, (∀ x, p x ∈ H₁ ↔ x ∈ H₁) ∨ (∀ x, p x ∈ H₁ ↔ x ∉ H₁)) ∧
      (∃ s ∈ P ⊓ alternatingGroup X, s ^ 2 = 1 ∧ (∀ x, s x ∈ H₁ ↔ x ∉ H₁) ∧
        ∃ r ∈ P ⊓ alternatingGroup X, r ^ 2 = 1 ∧ (∀ x, r x ∈ H₁ ↔ x ∈ H₁) ∧
          (∀ x, r x ≠ x) ∧ Commute s r) ∧
      (3 ≤ n → ∀ z ∈ H₁, ∃ w ∈ P ⊓ alternatingGroup X, (∀ x ∉ H₁, w x = x) ∧ w z ≠ z) := by
  classical
  have h4 : 4 ∣ Fintype.card X := by
    rw [hcard, show n = 2 + (n - 2) by omega, pow_add]
    exact dvd_mul_right _ _
  have hne : Nonempty X := Fintype.card_pos_iff.1 (by rw [hcard]; positivity)
  obtain ⟨y⟩ := hne
  have horb : orbit P y = Set.univ := by
    obtain ⟨a, ha, hya⟩ := exists_testBit_card_orbit_of_fusionIsSylowIn_top hP y
    rw [hcard, Nat.testBit_two_pow] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hya, Nat.card_eq_fintype_card, hcard]
  have hO : Nat.card (orbit P y) = 2 ^ n := by
    rw [horb, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
  obtain ⟨H₁, hH⟩ := exists_isHalf hP (y := y) (by
    rw [hO]; calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hcard₁ : 2 * Nat.card H₁ = 2 ^ n := hH.card.trans hO
  have hperm : ∀ p ∈ P, (∀ x, p x ∈ H₁ ↔ x ∈ H₁) ∨ (∀ x, p x ∈ H₁ ↔ x ∉ H₁) := fun p hp =>
    (hH.perm p hp).imp id fun h x => h x (by rw [horb]; trivial)
  obtain ⟨z', hz'⟩ : ∃ z', z' ∉ H₁ := by
    by_contra hno
    push Not at hno
    have : H₁ = Set.univ := Set.eq_univ_of_forall hno
    rw [this, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card, hcard] at hcard₁
    have : 0 < 2 ^ n := by positivity
    omega
  obtain ⟨⟨g, hgP⟩, hgy⟩ : z' ∈ orbit P y := by rw [horb]; trivial
  change g y = z' at hgy
  have hgswap : ∀ x, g x ∈ H₁ ↔ x ∉ H₁ := by
    rcases hperm g hgP with hpres | hswap
    · exact absurd ((hpres y).2 hH.mem) (hgy ▸ hz')
    · exact hswap
  have hgi : ∀ x, g⁻¹ x ∈ H₁ ↔ x ∉ H₁ := fun x => by
    have := hgswap (g⁻¹ x)
    rw [show g (g⁻¹ x) = x by simp] at this
    tauto
  have hg2 : ∀ x, (g⁻¹ * g⁻¹) x ∈ H₁ ↔ x ∈ H₁ := fun x => by
    simp only [Perm.mul_apply, hgi]
    tauto
  obtain ⟨m₂, hm₂P, hm₂B, hm₂B'⟩ := hH.exists_trunc hP
    (P.mul_mem (P.inv_mem hgP) (P.inv_mem hgP)) hg2 (orbit P y \ H₁) (Or.inr rfl)
  have hOH : ∀ x, x ∈ orbit P y \ H₁ ↔ x ∉ H₁ := fun x => by simp [horb]
  have hs1 : ∀ x ∈ H₁, (g * m₂) x = g x := fun x hx => by
    rw [Perm.mul_apply, hm₂B' x (fun h => ((hOH x).1 h) hx)]
  have hs2 : ∀ x, x ∉ H₁ → (g * m₂) x = g⁻¹ x := fun x hx => by
    rw [Perm.mul_apply, hm₂B x ((hOH x).2 hx), Perm.mul_apply]
    simp
  have hsswap : ∀ x, (g * m₂) x ∈ H₁ ↔ x ∉ H₁ := fun x => by
    by_cases hx : x ∈ H₁
    · rw [hs1 x hx, hgswap]
    · rw [hs2 x hx, hgi]
  have hs_sq : (g * m₂) ^ 2 = 1 := by
    ext x
    rw [sq, Perm.mul_apply, Perm.one_apply]
    by_cases hx : x ∈ H₁
    · rw [hs1 x hx, hs2 _ (fun h => (hgswap x).1 h hx)]
      simp
    · rw [hs2 x hx, hs1 _ ((hgi x).2 hx)]
      simp
  have hsfree : ∀ x, (g * m₂) x ≠ x := fun x h => by
    have := hsswap x
    rw [h] at this
    tauto
  have hsP : g * m₂ ∈ P := P.mul_mem hgP hm₂P
  have hsA := mem_alternatingGroup_of_sq_eq_one_of_forall_apply_ne h4 hs_sq hsfree
  have hgne : (⟨g, hgP⟩ : P) ≠ 1 := fun h => by
    have : g = 1 := congrArg Subtype.val h
    rw [this, Perm.one_apply] at hgy
    exact hz' (hgy ▸ hH.mem)
  have : Nontrivial P := ⟨⟨_, _, hgne⟩⟩
  have hZ2 : 2 ∣ Fintype.card (Subgroup.center P) := by
    have := hP.2.1.center_nontrivial
    rcases (hP.2.1.to_subgroup (Subgroup.center P)).card_eq_or_dvd with h1 | h1
    · exact absurd h1 Finite.one_lt_card.ne'
    · rwa [← Nat.card_eq_fintype_card]
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card (G := Subgroup.center P) 2 hZ2
  set r : Perm X := ((zc : P) : Perm X)
  have hrP : r ∈ P := (zc : P).2
  have hro : orderOf r = 2 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hzc]
  have hrc : ∀ p ∈ P, Commute r p := fun p hp => by
    have := Subgroup.mem_center_iff.1 zc.2 ⟨p, hp⟩
    exact (congrArg Subtype.val this).symm
  have hr_sq : r ^ 2 = 1 := by rw [← hro, pow_orderOf_eq_one]
  have hrfree : ∀ x, r x ≠ x := fun x hx => by
    have hr1 : r = 1 := by
      ext w
      obtain ⟨⟨p, hp⟩, hpw⟩ : w ∈ orbit P x := by
        rw [orbit_eq_iff.2 (show x ∈ orbit P y by rw [horb]; trivial), horb]; trivial
      change p x = w at hpw
      rw [Perm.one_apply, ← hpw]
      have := congrArg (· x) (hrc p hp).eq
      simp only [Perm.mul_apply, hx] at this
      exact this
    rw [hr1, orderOf_one] at hro
    exact absurd hro (by norm_num)
  have hrH := hH.apply_mem_iff_of_commute hP hrc
  have hrA := mem_alternatingGroup_of_sq_eq_one_of_forall_apply_ne h4 hr_sq hrfree
  refine ⟨H₁, hcard₁, hperm, ⟨g * m₂, ⟨hsP, hsA⟩, hs_sq, hsswap, r, ⟨hrP, hrA⟩, hr_sq, hrH,
    hrfree, (hrc _ hsP).symm⟩, fun hn3 z hz => ?_⟩
  have hsupp : ∀ z' ∈ H₁, ∃ ℓ ∈ P, (∀ x ∉ H₁, ℓ x = x) ∧ ℓ y = z' := fun z' hz' => by
    obtain ⟨m, hmP, hmH, hmy⟩ := hH.trans z' hz'
    obtain ⟨ℓ, hℓP, hℓB, hℓB'⟩ := hH.exists_trunc hP hmP hmH H₁ (Or.inl rfl)
    exact ⟨ℓ, hℓP, hℓB', by rw [hℓB y hH.mem, hmy]⟩
  have htr : ∀ z' ∈ H₁, ∃ ℓ ∈ P, (∀ x ∉ H₁, ℓ x = x) ∧ ℓ z = z' := fun z' hz' => by
    obtain ⟨ℓ₁, hℓ₁P, hℓ₁B, hℓ₁y⟩ := hsupp z' hz'
    obtain ⟨ℓ₀, hℓ₀P, hℓ₀B, hℓ₀y⟩ := hsupp z hz
    refine ⟨ℓ₁ * ℓ₀⁻¹, P.mul_mem hℓ₁P (P.inv_mem hℓ₀P), fun x hx => ?_, ?_⟩
    · rw [Perm.mul_apply, show ℓ₀⁻¹ x = x by rw [Perm.inv_eq_iff_eq, hℓ₀B x hx], hℓ₁B x hx]
    · rw [Perm.mul_apply, show ℓ₀⁻¹ z = y by rw [Perm.inv_eq_iff_eq, hℓ₀y], hℓ₁y]
  by_contra hno
  push Not at hno
  have hodd : ∀ ℓ ∈ P, (∀ x ∉ H₁, ℓ x = x) → ℓ z ≠ z → sign ℓ = -1 := fun ℓ hℓP hℓB hℓz => by
    rcases Int.units_eq_one_or (sign ℓ) with h1 | h1
    · exact absurd (hno ℓ ⟨hℓP, mem_alternatingGroup.2 h1⟩ hℓB) hℓz
    · exact h1
  have hH₁ : ∀ w ∈ H₁, ∀ w' ∈ H₁, w ≠ z → w' ≠ z → w = w' := fun w hw w' hw' hwz hw'z => by
    obtain ⟨ℓ, hℓP, hℓB, hℓz⟩ := htr w hw
    obtain ⟨ℓ', hℓ'P, hℓ'B, hℓ'z⟩ := htr w' hw'
    have h1 := hodd ℓ hℓP hℓB (fun h => hwz (hℓz.symm.trans h))
    have h2 := hodd ℓ' hℓ'P hℓ'B (fun h => hw'z (hℓ'z.symm.trans h))
    have hfix := hno (ℓ⁻¹ * ℓ') (Subgroup.mem_inf.2 ⟨P.mul_mem (P.inv_mem hℓP) hℓ'P,
        mem_alternatingGroup.2 (by rw [map_mul, map_inv, h1, h2]; decide)⟩) (fun x hx => by
        rw [Perm.mul_apply, hℓ'B x hx, Perm.inv_eq_iff_eq, hℓB x hx])
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq, hℓ'z, hℓz] at hfix
    exact hfix.symm
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hc4 : 4 ≤ H₁.ncard := by rw [← Nat.card_coe_set_eq]; omega
  obtain ⟨z', hz'H, hz'z⟩ := Set.exists_ne_of_one_lt_ncard (s := H₁) (by omega) z
  have hsub : H₁ ⊆ {z, z'} := fun w hw => by
    by_cases hwz : w = z
    · exact Or.inl hwz
    · exact Or.inr (hH₁ w hw z' hz'H hwz hz'z)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hz'z.symm] at this
  omega

end HalfSystems

section Relative

theorem mem_of_commute_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup {Λ : Set X}
    (h4 : 4 ∣ Nat.card ↥Λᶜ) {V : Subgroup (Perm X)}
    (hV : fusionIsSylowIn 2 V (alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ)) {g : Perm X}
    (hgΛ : g ∈ fixingSubgroup (Perm X) Λ) (hg : ∀ v ∈ V, Commute g v) : g ∈ V := by
  classical
  obtain ⟨V', hV', rfl⟩ := exists_fusionIsSylowIn_alternatingGroup_compl hV
  obtain ⟨g', rfl⟩ := exists_ofSubtype_eq_of_mem_fixingSubgroup hgΛ
  have hg' : ∀ v ∈ V', Commute g' v := fun v hv => by
    have := (hg _ ⟨v, hv, rfl⟩).eq
    rw [← map_mul, ← map_mul] at this
    exact ofSubtype_injective this
  exact ⟨g', mem_of_commute_of_fusionIsSylowIn_alternatingGroup
    (by rwa [← Nat.card_eq_fintype_card]) hV' hg', rfl⟩

theorem exists_half_system_of_fusionIsSylowIn_alternatingGroup_inf_fixingSubgroup
    {Λ : Set X} {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card ↥Λᶜ = 2 ^ n) {V Q : Subgroup (Perm X)}
    (hV : fusionIsSylowIn 2 V (alternatingGroup X ⊓ fixingSubgroup (Perm X) Λ))
    (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q) (hQΛ : Q ≤ fixingSubgroup (Perm X) Λ) :
    ∃ H₁ : Set X, H₁ ⊆ Λᶜ ∧ 2 * Nat.card H₁ = 2 ^ n ∧
      (∀ q ∈ Q, (∀ x, q x ∈ H₁ ↔ x ∈ H₁) ∨ (∀ x ∈ Λᶜ, q x ∈ H₁ ↔ x ∉ H₁)) ∧
      (∃ s ∈ V, s ^ 2 = 1 ∧ (∀ x ∈ Λᶜ, s x ∈ H₁ ↔ x ∉ H₁) ∧
        ∃ r ∈ V, r ^ 2 = 1 ∧ (∀ x, r x ∈ H₁ ↔ x ∈ H₁) ∧ (∀ x ∈ Λᶜ, r x ≠ x) ∧
          Commute s r) ∧
      (3 ≤ n → fixSet X (Q ⊓ fixingSubgroup (Perm X) H₁) = Λ ∪ H₁) := by
  classical
  obtain ⟨V', hV', rfl⟩ := exists_fusionIsSylowIn_alternatingGroup_compl hV
  set φ : Perm ↥Λᶜ →* Perm X := ofSubtype
  have hQrange : ∀ q ∈ Q, ∃ q' : Perm ↥Λᶜ, φ q' = q := fun q hq =>
    exists_ofSubtype_eq_of_mem_fixingSubgroup (hQΛ hq)
  set Q' := Q.comap φ
  have hQ' : IsPGroup 2 Q' := hQ.comap_of_injective φ ofSubtype_injective
  have hVQ' : V' ≤ Q' := fun v hv => hVQ ⟨v, hv, rfl⟩
  obtain ⟨P', hQP', hP'⟩ := exists_fusionIsSylowIn_ge hQ' le_top
  have hV'P : P' ⊓ alternatingGroup ↥Λᶜ = V' :=
    hV'.2.2 _ inf_le_right (hP'.2.1.to_le inf_le_left) (le_inf (hVQ'.trans hQP') hV'.1)
  have hcardY : Fintype.card ↥Λᶜ = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  obtain ⟨H, hHc, hperm, ⟨s', hs'V, hs'2, hs'sw, r', hr'V, hr'2, hr'H, hr'free, hsr⟩, hiv⟩ :=
    exists_half_system_of_fusionIsSylowIn_top hP' hn hcardY
  rw [hV'P] at hs'V hr'V
  have hφ : ∀ (g : Perm ↥Λᶜ) (y : ↥Λᶜ), φ g y = g y := fun g y => ofSubtype_apply_coe g y
  have hφΛ : ∀ (g : Perm ↥Λᶜ) {x : X}, x ∉ Λᶜ → φ g x = x := fun g x hx =>
    ofSubtype_apply_of_not_mem g hx
  set H₁ : Set X := Subtype.val '' Hᶜ
  have hmem : ∀ y : ↥Λᶜ, (y : X) ∈ H₁ ↔ y ∉ H := fun y =>
    ⟨fun ⟨y', hy', hyy'⟩ => by rwa [← Subtype.ext hyy'], fun hy => ⟨y, hy, rfl⟩⟩
  have hH₁ : H₁ ⊆ Λᶜ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hpres : ∀ g : Perm ↥Λᶜ, (∀ y, g y ∈ H ↔ y ∈ H) → ∀ x, φ g x ∈ H₁ ↔ x ∈ H₁ :=
    fun g hg x => by
      by_cases hx : x ∈ Λᶜ
      · rw [show x = ((⟨x, hx⟩ : ↥Λᶜ) : X) from rfl, hφ, hmem, hmem, hg]
      · rw [hφΛ g hx]
  have hswap : ∀ g : Perm ↥Λᶜ, (∀ y, g y ∈ H ↔ y ∉ H) → ∀ x ∈ Λᶜ, φ g x ∈ H₁ ↔ x ∉ H₁ :=
    fun g hg x hx => by
      rw [show x = ((⟨x, hx⟩ : ↥Λᶜ) : X) from rfl, hφ, hmem, hmem, hg]
  refine ⟨H₁, hH₁, ?_, fun q hq => ?_, ⟨φ s', ⟨s', hs'V, rfl⟩, by rw [← map_pow, hs'2, map_one],
    hswap s' hs'sw, φ r', ⟨r', hr'V, rfl⟩, by rw [← map_pow, hr'2, map_one], hpres r' hr'H,
    fun x hx => ?_, hsr.map φ⟩, fun hn3 => ?_⟩
  · rw [Nat.card_image_of_injective Subtype.val_injective, Nat.card_coe_set_eq]
    have h1 := Set.ncard_add_ncard_compl H
    rw [Nat.card_eq_fintype_card, hcardY, ← Nat.card_coe_set_eq] at h1
    omega
  · obtain ⟨q', rfl⟩ := hQrange q hq
    rcases hperm q' (hQP' hq) with h1 | h1
    · exact Or.inl (hpres q' h1)
    · exact Or.inr (hswap q' h1)
  · rw [show x = ((⟨x, hx⟩ : ↥Λᶜ) : X) from rfl, hφ]
    exact fun h => hr'free _ (Subtype.ext h)
  · ext x
    constructor
    · intro hx
      by_contra hxΛ
      have hxc : x ∈ Λᶜ := fun h => hxΛ (Or.inl h)
      set y : ↥Λᶜ := ⟨x, hxc⟩
      have hyH : y ∈ H := by
        by_contra h
        exact hxΛ (Or.inr ((hmem y).2 h))
      obtain ⟨w', hw'V, hw'H, hw'y⟩ := hiv hn3 y hyH
      rw [hV'P] at hw'V
      have hwfix : φ w' ∈ fixingSubgroup (Perm X) H₁ :=
        (mem_fixingSubgroup_iff _).2 fun x' hx' => by
          obtain ⟨y', hy', rfl⟩ := hx'
          rw [Perm.smul_def, hφ, hw'H y' hy']
      have := hx (φ w') ⟨hVQ ⟨w', hw'V, rfl⟩, hwfix⟩
      rw [Perm.smul_def, show x = (y : X) from rfl, hφ] at this
      exact hw'y (Subtype.ext this)
    · rintro (hxΛ | hxH) g ⟨hgQ, hgH⟩
      · exact (mem_fixingSubgroup_iff _).1 (hQΛ hgQ) x hxΛ
      · exact (mem_fixingSubgroup_iff _).1 hgH x hxH

end Relative

end CFSG.Holt.H78
