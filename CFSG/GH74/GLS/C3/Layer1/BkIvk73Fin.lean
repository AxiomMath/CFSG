module

public import CFSG.GH74.GLS.C3.Layer1.BkSEAbs
public import CFSG.GH74.GLS.C3.Layer1.BkL114SE

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools Equiv Perm CFSG.GH74.GLS.C3.Layer2

@[expose] def conjA {m : ℕ} (σ : Perm (Fin m)) :
    alternatingGroup (Fin m) ≃* alternatingGroup (Fin m) where
  toFun g := ⟨σ * (g : Perm (Fin m)) * σ⁻¹, by
    rw [mem_alternatingGroup, map_mul, map_mul, map_inv, mem_alternatingGroup.1 g.2]
    simp [mul_comm]⟩
  invFun g := ⟨σ⁻¹ * (g : Perm (Fin m)) * σ, by
    rw [mem_alternatingGroup, map_mul, map_mul, map_inv, mem_alternatingGroup.1 g.2]
    simp [mul_comm]⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

theorem card_subtype_lt (n : ℕ) : Nat.card {p : Fin (n + 4) // p.val < n} = n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter fun p : Fin (n + 4) => p.val < n) =
      (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb (by omega)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.coe_castLEEmb]
    constructor
    · intro h
      exact ⟨⟨p.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.2
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem card_stdAlt_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (stdAlt n) ≤ Nat.card (alternatingGroup (Fin n)) := by
  classical
  let S₀ : Type := {p : Fin (n + 4) // p.val < n}
  have hS₀ : Fintype.card S₀ = n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_subtype_lt n
  have hinv : ∀ g : ↥(stdAlt n), ∀ p : Fin (n + 4),
      (((g.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) p).val < n ↔ p.val < n := by
    intro g p
    have hfix := g.2
    constructor
    · intro hp
      by_contra hcon
      push Not at hcon
      have h1 := hfix p hcon
      rw [h1] at hp
      omega
    · intro hp
      by_contra hcon
      push Not at hcon
      have h1 : ((g.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4)))
          (((g.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) p) =
          ((g.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) p := hfix _ hcon
      have h2 := ((g.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))).injective h1
      rw [h2] at hcon
      omega
  let ι : ↥(stdAlt n) → alternatingGroup S₀ := fun g =>
    ⟨((g.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))).subtypePerm (hinv g), by
      rw [mem_alternatingGroup]
      rw [Equiv.Perm.sign_subtypePerm]
      · exact mem_alternatingGroup.1 g.1.2
      · intro p hp
        by_contra hcon
        push Not at hcon
        exact hp (g.2 p hcon)⟩
  have hinj : Function.Injective ι := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro p
    by_cases hp : p.val < n
    · have := congrArg (fun a : alternatingGroup S₀ => (a : Perm S₀) ⟨p, hp⟩) hgh
      simp only [ι] at this
      exact congrArg Subtype.val this
    · push Not at hp
      rw [g.2 p hp, h.2 p hp]
  calc Nat.card (stdAlt n) ≤ Nat.card (alternatingGroup S₀) := Nat.card_le_card_of_injective ι hinj
    _ = Nat.card (alternatingGroup (Fin n)) := by
      have hnt : Nontrivial S₀ := by
        rw [← Fintype.one_lt_card_iff_nontrivial, hS₀]
        omega
      have hnt' : Nontrivial (Fin n) := by
        rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_fin]
        omega
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
        card_alternatingGroup, hS₀, Fintype.card_fin]

theorem neg_one_pow_units_eq_one_iff {k : ℕ} : ((-1 : ℤˣ) ^ k = 1) ↔ Even k :=
  neg_one_pow_eq_one_iff_even (by decide)

theorem card_support_of_involution_alt {m : ℕ} (hm : m ≤ 11) {u : Perm (Fin m)} (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (hs : Perm.sign u = 1) :
    u.support.card = 4 ∧ u.cycleType = Multiset.replicate 2 2 ∨
      u.support.card = 8 ∧ u.cycleType = Multiset.replicate 4 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : u.cycleType = Multiset.replicate (Multiset.card u.cycleType) 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hu2
  set c := Multiset.card u.cycleType with hc
  have hsum : u.cycleType.sum = u.support.card := Equiv.Perm.sum_cycleType u
  have hsum2 : u.cycleType.sum = 2 * c := by
    rw [hcyc, Multiset.sum_replicate, smul_eq_mul]; ring
  have hsupp : u.support.card = 2 * c := by omega
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu1
    rw [← Equiv.Perm.cycleType_eq_zero]
    rw [hcyc, h0]; rfl
  have hsgn : (-1 : ℤˣ) ^ (u.cycleType.sum + Multiset.card u.cycleType) = 1 := by
    rw [← Equiv.Perm.sign_of_cycleType]; exact hs
  rw [hsum2] at hsgn
  have hev : Even (2 * c + c) := neg_one_pow_units_eq_one_iff.1 hsgn
  have hle : u.support.card ≤ m := by
    have := Finset.card_le_univ u.support
    simpa using this
  have hceven : Even c := by
    rcases hev with ⟨r, hr⟩
    exact ⟨r - c, by omega⟩
  obtain ⟨r, hr⟩ := hceven
  have hr1 : 1 ≤ r := by omega
  have hr5 : r ≤ 2 := by omega
  interval_cases r
  · left
    refine ⟨by omega, ?_⟩
    rw [hcyc]
    congr 1
  · right
    refine ⟨by omega, ?_⟩
    rw [hcyc]
    congr 1

theorem fixes_support_of_simple_alt {n : ℕ} (hn : n = 5 ∨ n = 7)
    (K' : Subgroup (alternatingGroup (Fin (n + 4)))) (eK : ↥K' ≃* alternatingGroup (Fin n))
    (u : Perm (Fin (n + 4))) (hc : u.support.card ≤ 4)
    (hKu : ∀ k ∈ K', (k : Perm (Fin (n + 4))) * u = u * (k : Perm (Fin (n + 4)))) :
    ∀ k ∈ K', ∀ p ∈ u.support, (k : Perm (Fin (n + 4))) p = p := by
  classical
  have hsimp : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
  have hKs : IsSimpleGroup ↥K' := eK.isSimpleGroup
  have hinv : ∀ k : ↥K', ∀ p : Fin (n + 4),
      ((k.1 : Perm (Fin (n + 4))) p) ∈ u.support ↔ p ∈ u.support := by
    intro k p
    have hk := hKu k.1 k.2
    have h1 : u (((k.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) p) =
        ((k.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) (u p) := by
      have := congrArg (fun f : Perm (Fin (n + 4)) => f p) hk
      simpa [Perm.mul_apply] using this.symm
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support, h1]
    exact not_congr ((k.1 : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))).injective.eq_iff
  let φ : ↥K' →* Perm {p // p ∈ u.support} :=
    { toFun := fun k => (k.1 : Perm (Fin (n + 4))).subtypePerm (hinv k)
      map_one' := Equiv.ext fun p => Subtype.ext rfl
      map_mul' := fun k l => Equiv.ext fun p => Subtype.ext rfl }
  have hker : φ.ker = ⊥ ∨ φ.ker = ⊤ := φ.normal_ker.eq_bot_or_eq_top
  rcases hker with hb | ht
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hb
    have hsolv : Group.IsSolvable (Perm {p // p ∈ u.support}) := by
      apply Equiv.Perm.isSolvable
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact hc
    have hKsolv : Group.IsSolvable ↥K' := Group.isSolvable_of_isSolvable_injective hinj
    have hA : Group.IsSolvable (alternatingGroup (Fin n)) :=
      Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective
    exact alt_not_isSolvable n hn hA
  · intro k hk p hp
    have h1 : φ ⟨k, hk⟩ = 1 := by
      have : (⟨k, hk⟩ : ↥K') ∈ φ.ker := by rw [ht]; exact Subgroup.mem_top _
      exact this
    have h2 := congrArg (fun f : Perm {p // p ∈ u.support} => (f ⟨p, hp⟩ : Fin (n + 4))) h1
    simpa [φ] using h2

theorem false_of_support_eight {n : ℕ} (hn : n = 5 ∨ n = 7)
    (K' : Subgroup (alternatingGroup (Fin (n + 4)))) (eK : ↥K' ≃* alternatingGroup (Fin n))
    (u : Perm (Fin (n + 4))) (hcyc : u.cycleType = Multiset.replicate 4 2)
    (hKu : ∀ k ∈ K', (k : Perm (Fin (n + 4))) * u = u * (k : Perm (Fin (n + 4)))) : False := by
  classical
  let ι : ↥K' →* ↥(Subgroup.centralizer ({u} : Set (Perm (Fin (n + 4))))) :=
    (((alternatingGroup (Fin (n + 4))).subtype.comp K'.subtype).codRestrict
      (Subgroup.centralizer ({u} : Set (Perm (Fin (n + 4))))) fun k => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hKu k.1 k.2)
  have hinj : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Subgroup.centralizer ({u} : Set (Perm (Fin (n + 4))))) =>
      (z : Perm (Fin (n + 4)))) hab
  have hdvd := Subgroup.card_dvd_of_injective ι hinj
  rw [Equiv.Perm.nat_card_centralizer u, hcyc, Nat.card_congr eK.toEquiv,
    Nat.card_eq_fintype_card] at hdvd
  rcases hn with rfl | rfl
  · rw [card_alternatingGroup] at hdvd
    simp [Nat.factorial] at hdvd
  · rw [card_alternatingGroup] at hdvd
    simp [Nat.factorial] at hdvd

theorem card_subtype_ge (n : ℕ) : Fintype.card {p : Fin (n + 4) // n ≤ p.val} = 4 := by
  classical
  have h1 := Fintype.card_subtype_compl (fun p : Fin (n + 4) => p.val < n)
  have h2 : Fintype.card {p : Fin (n + 4) // p.val < n} = n := by
    rw [← Nat.card_eq_fintype_card]
    exact card_subtype_lt n
  have h3 : Fintype.card {p : Fin (n + 4) // n ≤ p.val} =
      Fintype.card {p : Fin (n + 4) // ¬ p.val < n} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun p => not_lt.symm)
  rw [Fintype.card_fin] at h1
  omega

theorem exists_conj_stdAlt {n : ℕ} (hn : n = 5 ∨ n = 7)
    (K' : Subgroup (alternatingGroup (Fin (n + 4)))) (eK : ↥K' ≃* alternatingGroup (Fin n))
    {u : alternatingGroup (Fin (n + 4))} (hu : orderOf u = 2) (hKu : ∀ k ∈ K', k * u = u * k) :
    ∃ σ : Perm (Fin (n + 4)), K'.map (conjA σ).toMonoidHom = stdAlt n := by
  classical
  have hm : n + 4 ≤ 11 := by rcases hn with rfl | rfl <;> norm_num
  set u₀ : Perm (Fin (n + 4)) := (u : Perm (Fin (n + 4))) with hu₀
  have hu2 : u₀ ^ 2 = 1 := by
    have h1 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg (fun a : alternatingGroup (Fin (n + 4)) => (a : Perm (Fin (n + 4)))) h1
    simpa using this
  have hu1 : u₀ ≠ 1 := by
    intro h
    have h1 : u = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hu
    omega
  have hs : Perm.sign u₀ = 1 := mem_alternatingGroup.1 u.2
  have hKu' : ∀ k ∈ K', (k : Perm (Fin (n + 4))) * u₀ = u₀ * (k : Perm (Fin (n + 4))) := fun k hk => by
    have := congrArg (fun a : alternatingGroup (Fin (n + 4)) => (a : Perm (Fin (n + 4)))) (hKu k hk)
    simpa using this
  rcases card_support_of_involution_alt hm hu2 hu1 hs with ⟨h4, -⟩ | ⟨-, h8⟩
  · have hfix := fixes_support_of_simple_alt hn K' eK u₀ h4.le hKu'
    have hcF : Fintype.card {p // p ∈ u₀.support} = Fintype.card {p : Fin (n + 4) // n ≤ p.val} := by
      rw [Fintype.card_coe, h4, card_subtype_ge]
    let e₀ : {p // p ∈ u₀.support} ≃ {p : Fin (n + 4) // n ≤ p.val} := Fintype.equivOfCardEq hcF
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun a : {p // p ∈ u₀.support} => a.1)
      (fun a => (e₀ a).1) Subtype.val_injective (fun a b h => e₀.injective (Subtype.ext h))
    refine ⟨σ, ?_⟩
    have hle : K'.map (conjA σ).toMonoidHom ≤ stdAlt n := by
      rintro _ ⟨k, hk, rfl⟩ i hi
      have hia : (e₀ (e₀.symm ⟨i, hi⟩)).1 = i := by simp
      have hσa : σ (e₀.symm ⟨i, hi⟩).1 = i := by rw [hσ, hia]
      have hkfix := hfix k hk _ (e₀.symm ⟨i, hi⟩).2
      have h1 : σ⁻¹ i = (e₀.symm ⟨i, hi⟩).1 := by
        rw [Equiv.Perm.inv_eq_iff_eq, hσa]
      show (σ * (k : Perm (Fin (n + 4))) * σ⁻¹) i = i
      rw [Perm.mul_apply, Perm.mul_apply, h1, hkfix, hσa]
    have hcard : Nat.card (stdAlt n) ≤ Nat.card (K'.map (conjA σ).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (conjA σ).injective, Nat.card_congr eK.toEquiv]
      exact card_stdAlt_le n (by rcases hn with rfl | rfl <;> norm_num)
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  · exact (false_of_support_eight hn K' eK u₀ h8 hKu').elim

end CFSG.GH74.GLS.C3.Layer1.Bk
