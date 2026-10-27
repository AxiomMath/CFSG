module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSymmetric
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv Subgroup

variable {Ω : Type*}

section Pairs

variable {t : Perm Ω}

theorem pair_mul (htt : ∀ ω, t (t ω) = ω) {g h : Perm Ω} (hg : ∀ ω, g ω = ω ∨ g ω = t ω)
    (hh : ∀ ω, h ω = ω ∨ h ω = t ω) : ∀ ω, (g * h) ω = ω ∨ (g * h) ω = t ω := by
  intro ω
  rw [Perm.mul_apply]
  rcases hh ω with h1 | h1 <;> rw [h1]
  · exact hg ω
  · rcases hg (t ω) with h2 | h2
    · exact Or.inr h2
    · exact Or.inl (h2.trans (htt ω))

theorem pair_mul_self (htt : ∀ ω, t (t ω) = ω) {g : Perm Ω}
    (hg : ∀ ω, g ω = ω ∨ g ω = t ω) : g * g = 1 := by
  ext ω
  rw [Perm.mul_apply, Perm.one_apply]
  rcases hg ω with h1 | h1
  · rw [h1, h1]
  · rw [h1]
    rcases hg (t ω) with h2 | h2
    · have hω : t ω = ω := g.injective (h2.trans h1.symm)
      rw [h2, hω]
    · rw [h2, htt]

theorem pair_conj {c g : Perm Ω} (hc : ∀ x, c (t x) = t (c x))
    (hg : ∀ ω, g ω = ω ∨ g ω = t ω) :
    ∀ ω, (c * g * c⁻¹) ω = ω ∨ (c * g * c⁻¹) ω = t ω := by
  intro ω
  simp only [Perm.mul_apply]
  rcases hg (c⁻¹ ω) with h1 | h1 <;> rw [h1]
  · exact Or.inl (Perm.eq_inv_iff_eq.mp rfl)
  · rw [hc, Perm.eq_inv_iff_eq.mp rfl]
    exact Or.inr rfl

theorem swap_pair (htt : ∀ ω, t (t ω) = ω) [DecidableEq Ω] (a : Ω) :
    ∀ ω, swap a (t a) ω = ω ∨ swap a (t a) ω = t ω := by
  intro ω
  by_cases hωa : ω = a
  · subst hωa
    exact Or.inr (swap_apply_left _ _)
  by_cases hωt : ω = t a
  · subst hωt
    rw [swap_apply_right, htt]
    exact Or.inr rfl
  · exact Or.inl (swap_apply_of_ne_of_ne hωa hωt)

theorem swap_pair_commute (htt : ∀ ω, t (t ω) = ω) [DecidableEq Ω] (a : Ω) :
    swap a (t a) * t = t * swap a (t a) := by
  have h : t * swap a (t a) * t⁻¹ = swap a (t a) := by
    rw [← swap_apply_apply, htt, swap_comm]
  calc swap a (t a) * t = t * swap a (t a) * t⁻¹ * t := by rw [h]
    _ = t * swap a (t a) := by group

theorem ofSubtype_fixed_commute (htt : ∀ ω, t (t ω) = ω) [DecidableEq Ω]
    (τ : Perm {ω // t ω = ω}) : Perm.ofSubtype τ * t = t * Perm.ofSubtype τ := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : t x = x
  · rw [hx, Perm.ofSubtype_apply_of_mem τ hx]
    exact ((τ ⟨x, hx⟩).2).symm
  · have htx : ¬ t (t x) = t x := by
      rw [htt]
      exact fun h => hx h.symm
    rw [Perm.ofSubtype_apply_of_not_mem τ hx, Perm.ofSubtype_apply_of_not_mem τ htx]

end Pairs

theorem apply_eq_self_of_apply_eq_pair {t δ : Perm Ω} (htt : ∀ ω, t (t ω) = ω)
    (hδ : ∀ x, δ (t x) = t (δ x)) (hodd : Odd (orderOf δ)) {x : Ω} (hx : δ x = t x) :
    δ x = x := by
  apply SmallLocal.apply_eq_self_of_sq_apply_eq hodd
  rw [hx, hδ, hx, htt]

variable [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem commute_of_mem_oddCore_of_pair {C : Subgroup (Perm Ω)} {t : Perm Ω}
    (hC : C ≤ centralizer ({t} : Set (Perm Ω))) (htt : ∀ ω, t (t ω) = ω) {d u : C}
    (hd : d ∈ oddCore C) (hu : ∀ ω, (u : Perm Ω) ω = ω ∨ (u : Perm Ω) ω = t ω) :
    d * u = u * d := by
  have hdt : ∀ x, (d : Perm Ω) (t x) = t ((d : Perm Ω) x) := fun x => by
    have h := congrArg (fun g : Perm Ω => g x) (mem_centralizer_singleton_iff.mp (hC d.2))
    simpa only [Perm.mul_apply] using h
  have hx : d * u * d⁻¹ * u⁻¹ ∈ oddCore C := by
    have h := mul_mem hd ((oddCore_normal C).conj_mem _ (inv_mem hd) u)
    rwa [← mul_assoc, ← mul_assoc] at h
  have huu : (u : Perm Ω) * u = 1 := pair_mul_self htt hu
  have huinv : (u : Perm Ω)⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hxpair : ∀ ω, ((d * u * d⁻¹ * u⁻¹ : C) : Perm Ω) ω = ω ∨
      ((d * u * d⁻¹ * u⁻¹ : C) : Perm Ω) ω = t ω := by
    have h := pair_mul htt (pair_conj hdt hu) hu
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, huinv] using h
  have hxx : (d * u * d⁻¹ * u⁻¹) ^ 2 = 1 := by
    apply Subtype.ext
    rw [sq, Subgroup.coe_mul, pair_mul_self htt hxpair, Subgroup.coe_one]
  have hodd : Odd (orderOf (d * u * d⁻¹ * u⁻¹)) :=
    SmallLocal.odd_card_oddCore.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  have hdvd : orderOf (d * u * d⁻¹ * u⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one hxx
  have hone : orderOf (d * u * d⁻¹ * u⁻¹) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have h1 := orderOf_eq_one_iff.mp hone
  calc d * u = d * u * d⁻¹ * u⁻¹ * (u * d) := by group
    _ = u * d := by rw [h1, one_mul]

theorem oddCore_apply_eq_self {C : Subgroup (Perm Ω)} {t : Perm Ω}
    (hC : C ≤ centralizer ({t} : Set (Perm Ω)))
    (hAC : alternatingGroup Ω ⊓ centralizer ({t} : Set (Perm Ω)) ≤ C)
    (htt : ∀ ω, t (t ω) = ω) {d : C} (hd : d ∈ oddCore C) {a : Ω} (ha : t a ≠ a) :
    (d : Perm Ω) a = a := by
  have hcomm : ∀ e : C, ∀ x, (e : Perm Ω) (t x) = t ((e : Perm Ω) x) := fun e x => by
    have h := congrArg (fun g : Perm Ω => g x) (mem_centralizer_singleton_iff.mp (hC e.2))
    simpa only [Perm.mul_apply] using h
  have horder : ∀ e ∈ oddCore C, Odd (orderOf (e : Perm Ω)) := fun e he => by
    rw [Subgroup.orderOf_coe]
    exact SmallLocal.odd_card_oddCore.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ he)
  have key : ∀ e ∈ oddCore C, ∀ x, (e : Perm Ω) x = t x → (e : Perm Ω) x = x :=
    fun e he x hx => apply_eq_self_of_apply_eq_pair htt (hcomm e) (horder e he) hx
  by_contra hδa
  have hba : (d : Perm Ω) a ≠ t a := fun h => hδa (key d hd a h)
  have htb : t ((d : Perm Ω) a) ≠ (d : Perm Ω) a := by
    intro h
    rw [← hcomm d a] at h
    exact ha ((d : Perm Ω).injective h)
  have hcb : (d : Perm Ω) ((d : Perm Ω) a) ≠ (d : Perm Ω) a :=
    fun h => hδa ((d : Perm Ω).injective h)
  have hctb : (d : Perm Ω) ((d : Perm Ω) a) ≠ t ((d : Perm Ω) a) :=
    fun h => hcb (key d hd _ h)
  have hca : (d : Perm Ω) ((d : Perm Ω) a) ≠ a :=
    fun h => hδa (SmallLocal.apply_eq_self_of_sq_apply_eq (horder d hd) h)
  have hcta : (d : Perm Ω) ((d : Perm Ω) a) ≠ t a := by
    intro h
    have h2 : ((d * d : C) : Perm Ω) a = a :=
      key (d * d) (mul_mem hd hd) a (by simpa only [Subgroup.coe_mul, Perm.mul_apply] using h)
    simp only [Subgroup.coe_mul, Perm.mul_apply] at h2
    exact hca h2
  generalize hb : (d : Perm Ω) a = b at hba htb hcb hctb hca hcta hδa
  generalize hc : (d : Perm Ω) b = c at hcb hctb hca hcta
  have htc : t c ≠ c := by
    intro h
    rw [← hc, ← hcomm d b] at h
    exact htb ((d : Perm Ω).injective h)
  have hatc : a ≠ t c := fun h => hcta (by rw [h, htt])
  have hbc : b ≠ c := Ne.symm hcb
  have hbtc : b ≠ t c := fun h => hctb (by rw [h, htt])
  have huA : swap a (t a) * swap c (t c) ∈ alternatingGroup Ω := by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (Ne.symm ha),
      Perm.sign_swap (Ne.symm htc)]
    decide
  have hut : swap a (t a) * swap c (t c) * t = t * (swap a (t a) * swap c (t c)) := by
    rw [mul_assoc, swap_pair_commute htt c, ← mul_assoc, swap_pair_commute htt a, mul_assoc]
  have huC : swap a (t a) * swap c (t c) ∈ C :=
    hAC ⟨huA, mem_centralizer_singleton_iff.mpr hut⟩
  have hdu := congrArg Subtype.val (commute_of_mem_oddCore_of_pair hC htt
    (u := ⟨swap a (t a) * swap c (t c), huC⟩) hd (pair_mul htt (swap_pair htt a)
      (swap_pair htt c)))
  have h := congrArg (fun g : Perm Ω => g a) hdu
  simp only [Subgroup.coe_mul, Perm.mul_apply] at h
  rw [swap_apply_of_ne_of_ne (Ne.symm hca) hatc, swap_apply_left, hcomm d a, hb,
    swap_apply_of_ne_of_ne hbc hbtc, swap_apply_of_ne_of_ne hδa hba] at h
  exact htb h

theorem involution_permutation_centralizer_odd_core {H : Subgroup (Perm Ω)}
    (hH : alternatingGroup Ω ≤ H) {t : Perm Ω} (ht : orderOf t = 2) :
    (Nat.card {ω // t ω = ω} ≠ 3 →
        oddCore ↥(H ⊓ centralizer ({t} : Set (Perm Ω))) = ⊥) ∧
      (Nat.card {ω // t ω = ω} = 3 →
        (oddCore ↥(H ⊓ centralizer ({t} : Set (Perm Ω)))).map
            (H ⊓ centralizer ({t} : Set (Perm Ω))).subtype =
          (alternatingGroup {ω // t ω = ω}).map Perm.ofSubtype ∧
        Nat.card (oddCore ↥(H ⊓ centralizer ({t} : Set (Perm Ω)))) = 3 ∧
        Nat.card ((alternatingGroup {ω // t ω = ω}).map Perm.ofSubtype) = 3) := by
  set C := H ⊓ centralizer ({t} : Set (Perm Ω)) with hCdef
  set D := oddCore C with hDdef
  have htt : ∀ ω, t (t ω) = ω := by
    have h2 : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    intro ω
    rw [← Perm.mul_apply, ← sq, h2, Perm.one_apply]
  have hcomm : ∀ e : C, ∀ x, (e : Perm Ω) (t x) = t ((e : Perm Ω) x) := fun e x => by
    have h := congrArg (fun g : Perm Ω => g x) (mem_centralizer_singleton_iff.mp e.2.2)
    simpa only [Perm.mul_apply] using h
  have hDodd : Odd (Nat.card D) := SmallLocal.odd_card_oddCore
  have hpres : ∀ e : C, ∀ ω, t ((e : Perm Ω) ω) = (e : Perm Ω) ω ↔ t ω = ω := by
    intro e ω
    rw [← hcomm e ω]
    exact (e : Perm Ω).injective.eq_iff
  let ρ : C →* Perm {ω // t ω = ω} :=
    { toFun := fun e => (e : Perm Ω).subtypePerm (hpres e)
      map_one' := Equiv.ext fun _ => rfl
      map_mul' := fun _ _ => Equiv.ext fun _ => rfl }
  have hρ : ∀ e : C, ∀ x : {ω // t ω = ω}, ((ρ e) x : Ω) = (e : Perm Ω) x := fun _ _ => rfl
  obtain ⟨a₀, ha₀⟩ : ∃ a, t a ≠ a := by
    by_contra h
    push Not at h
    have h1 : t = 1 := Equiv.ext h
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hρsurj : Function.Surjective ρ := by
    intro τ
    have hτt := ofSubtype_fixed_commute htt τ
    have hfixa : ∀ x : {ω // t ω = ω}, swap a₀ (t a₀) x = x := fun x => by
      have hxa : (x : Ω) ≠ a₀ := fun h => ha₀ (h ▸ x.2)
      have hxta : (x : Ω) ≠ t a₀ := fun h => by
        have h' := x.2
        rw [h, htt] at h'
        exact ha₀ h'.symm
      exact swap_apply_of_ne_of_ne hxa hxta
    by_cases hτ : Perm.ofSubtype τ ∈ H
    · refine ⟨⟨Perm.ofSubtype τ, hτ, mem_centralizer_singleton_iff.mpr hτt⟩, ?_⟩
      ext x
      rw [hρ]
      exact Perm.ofSubtype_apply_of_mem τ x.2
    · have hsign : Perm.sign (Perm.ofSubtype τ) = -1 :=
        (Int.units_eq_one_or _).resolve_left fun h => hτ (hH h)
      set g := Perm.ofSubtype τ * swap a₀ (t a₀) with hg
      have hgH : g ∈ H := hH (by
        rw [Perm.mem_alternatingGroup, map_mul, hsign, Perm.sign_swap (Ne.symm ha₀)]
        decide)
      have hgt : g * t = t * g := by
        rw [hg, mul_assoc, swap_pair_commute htt a₀, ← mul_assoc, hτt, mul_assoc]
      refine ⟨⟨g, hgH, mem_centralizer_singleton_iff.mpr hgt⟩, ?_⟩
      ext x
      rw [hρ]
      change Perm.ofSubtype τ (swap a₀ (t a₀) x) = (τ x : Ω)
      rw [hfixa x]
      exact Perm.ofSubtype_apply_of_mem τ x.2
  have hfix : ∀ d ∈ D, ∀ a, t a ≠ a → (d : Perm Ω) a = a :=
    fun d hd a ha => oddCore_apply_eq_self inf_le_right (inf_le_inf_right _ hH) htt hd ha
  have hmoved : ∀ d ∈ D, ∀ x, (d : Perm Ω) x ≠ x → t x = x :=
    fun d hd x hx => by_contra fun h => hx (hfix d hd x h)
  have hext : ∀ d ∈ D, Perm.ofSubtype (ρ d) = (d : Perm Ω) :=
    fun d hd => Perm.ofSubtype_subtypePerm (hpres d) (hmoved d hd)
  have hKnormal : (D.map ρ).Normal := (oddCore_normal C).map ρ hρsurj
  have hKodd : Odd (Nat.card (D.map ρ)) := hDodd.of_dvd_nat (Subgroup.card_map_dvd D ρ)
  have hKcore : D.map ρ ≤ oddCore (Perm {ω // t ω = ω}) :=
    SmallLocal.le_oddCore_of_normal_odd hKnormal hKodd
  obtain ⟨hthree, hnotthree⟩ := SmallLocal.symmetric_group_odd_core {ω // t ω = ω}
  refine ⟨fun h3 => ?_, fun h3 => ?_⟩
  · rw [hnotthree h3] at hKcore
    refine (Subgroup.eq_bot_iff_forall D).mpr fun d hd => ?_
    have hρd : ρ d = 1 := (Subgroup.mem_bot.mp (hKcore (Subgroup.mem_map_of_mem ρ hd)))
    apply Subtype.ext
    rw [← hext d hd, hρd, map_one]
    rfl
  · rw [hthree h3] at hKcore
    set A := (alternatingGroup {ω // t ω = ω}).map
      (Perm.ofSubtype : Perm {ω // t ω = ω} →* Perm Ω) with hAdef
    have : Nontrivial {ω // t ω = ω} := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    have hAlt3 : Nat.card (alternatingGroup {ω // t ω = ω}) = 3 := by
      have h := two_mul_card_alternatingGroup (α := {ω // t ω = ω})
      rw [Fintype.card_perm, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h3,
        show Nat.factorial 3 = 6 from rfl] at h
      omega
    have hA3 : Nat.card A = 3 := by
      rw [hAdef, card_map_ofSubtype_alternatingGroup, hAlt3]
    have hAC : A ≤ C := by
      rintro g ⟨τ, hτ, rfl⟩
      refine ⟨hH ?_, mem_centralizer_singleton_iff.mpr (ofSubtype_fixed_commute htt τ)⟩
      rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
      exact hτ
    have hAnormal : (A.subgroupOf C).Normal := by
      refine ⟨fun g hg e => ?_⟩
      rw [Subgroup.mem_subgroupOf, mem_map_ofSubtype_alternatingGroup_iff] at hg ⊢
      obtain ⟨hgfix, hgsign⟩ := hg
      refine ⟨fun x hx => ?_, ?_⟩
      · have hx' : ¬ t (((e⁻¹ : C) : Perm Ω) x) = ((e⁻¹ : C) : Perm Ω) x := by
          rw [hpres (e⁻¹)]
          exact hx
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply] at hx' ⊢
        rw [hgfix _ hx']
        exact Perm.eq_inv_iff_eq.mp rfl
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hgsign, mul_one,
          mul_inv_cancel]
    have hAodd : Odd (Nat.card (A.subgroupOf C)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA3]
      decide
    have hAD : A.subgroupOf C ≤ D := SmallLocal.le_oddCore_of_normal_odd hAnormal hAodd
    have heq : D.map C.subtype = A := by
      apply le_antisymm
      · rintro _ ⟨d, hd, rfl⟩
        exact ⟨ρ d, hKcore (Subgroup.mem_map_of_mem ρ hd), hext d hd⟩
      · intro g hg
        exact ⟨⟨g, hAC hg⟩, hAD hg, rfl⟩
    refine ⟨heq, ?_, hA3⟩
    rw [← Subgroup.card_map_of_injective C.subtype_injective, heq, hA3]

end CFSG.ComponentClassification.SymmetricLocal
