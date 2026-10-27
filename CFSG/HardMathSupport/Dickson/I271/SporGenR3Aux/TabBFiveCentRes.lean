module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoBLocalBound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFive

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Blueprint CFSG.Open CFSG.Monster.Existence CFSG.Monster.B.Pinned
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance Subgroup

section Res

@[expose] def BFiveCentRes : Prop :=
  TabBFiveACard ∧ ¬ 7 ∣ Nat.card ↥(centralizer ({zFive} : Set NativeSporadic.B))

end Res

section Generic

theorem centralizer_pow_eq_of_five {Q : Type*} [Group Q] {x : Q} (hx : orderOf x = 5) {c : ℕ}
    (hc : ¬ 5 ∣ c) : centralizer ({x ^ c} : Set Q) = centralizer ({x} : Set Q) := by
  have hb : (x ^ c) ^ (c ^ 3) = x := by
    rw [← pow_mul]
    conv_rhs => rw [← pow_one x]
    rw [pow_eq_pow_iff_modEq, hx]
    have hr : c % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hr0 : c % 5 ≠ 0 := fun h0 => hc (Nat.dvd_of_mod_eq_zero h0)
    show (c * c ^ 3) % 5 = 1 % 5
    rw [Nat.mul_mod, Nat.pow_mod]
    interval_cases (c % 5) <;> simp_all
  ext g
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : Commute g ((x ^ c) ^ (c ^ 3)) := Commute.pow_right h (c ^ 3)
    rw [hb] at h'
    exact h'.eq
  · intro h
    exact (Commute.pow_right h c).eq

theorem orderOf_map_of_card_ker_two {X Q : Type*} [Group X] [Group Q] (f : X →* Q)
    (hker : Nat.card ↥f.ker = 2) {x : X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : orderOf x = p) : orderOf (f x) = p := by
  have hd : orderOf (f x) ∣ p := hx ▸ orderOf_map_dvd f x
  rcases (Nat.dvd_prime hp).1 hd with h1 | h
  · exfalso
    have hmem : x ∈ f.ker := MonoidHom.mem_ker.2 (orderOf_eq_one_iff.1 h1)
    have h2 := Subgroup.orderOf_dvd_natCard f.ker hmem
    rw [hx, hker] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  · exact h

variable {G : Type} [Group G]

theorem exists_hom_of_card_center_two [Finite G] {Q : Type*} [Group Q] {X : Subgroup G}
    (hZ : Nat.card ↥(center ↥X) = 2) (e : ↥X ⧸ center ↥X ≃* Q) :
    ∃ f : ↥X →* Q, Nat.card ↥f.ker = 2 ∧ ∀ x : ↥X,
      Nat.card ↥(X ⊓ centralizer ({(x : G)} : Set G)) ≤
        2 * Nat.card ↥(centralizer ({f x} : Set Q)) := by
  haveI : Finite Q := Finite.of_equiv _ e.toEquiv
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center ↥X)), ?_, fun x => ?_⟩
  · have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥X))).ker = center ↥X := by
      ext y
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hker, hZ]
  · have hcard := card_centralizer_le_mul (center ↥X) e x
    have hZx : Nat.card ↥(center ↥X ⊓ centralizer ({x} : Set ↥X)) ≤ 2 :=
      hZ ▸ card_le_of_le inf_le_left
    rw [card_centralizer_subtype] at hcard
    exact hcard.trans (Nat.mul_le_mul_right _ hZx)

theorem exists_hom_of_twoA (hE : MonsterExistenceStatement G) {t : G} (ht : orderOf t = 2)
    (htc : Nat.card ↥(centralizer ({t} : Set G)) = 2 * monsterBabyOrder) :
    ∃ f : ↥(centralizer ({t} : Set G)) →* NativeSporadic.B, Nat.card ↥f.ker = 2 ∧
      ∀ x : ↥(centralizer ({t} : Set G)),
        Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({(x : G)} : Set G)) ≤
          2 * Nat.card ↥(centralizer ({f x} : Set NativeSporadic.B)) := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, -, -, -, hcls, hA, hB, -⟩ := id hE
  haveI : Finite G := hfin
  have htA : IsConj a t := by
    rcases hcls t ht with h | h
    · exact h
    · exfalso
      have h2 := (hB t h).2.2.2.2.1
      rw [htc] at h2
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA t htA
  set X : Subgroup G := centralizer ({t} : Set G) with hX
  have hZcard : Nat.card ↥(center ↥X) = 2 := by
    have h1 : Nat.card ↥((center ↥X).map X.subtype) = Nat.card ↥(center ↥X) :=
      card_map_of_injective X.subtype_injective
    rw [hZ, Nat.card_zpowers, ht] at h1
    exact h1.symm
  exact exists_hom_of_card_center_two hZcard e

end Generic

section Bound

theorem card_centralizer_lt_of_seven_dvd
    (hconj : ∀ y : NativeSporadic.B, orderOf y = 5 → ∃ c : ℕ, ¬ 5 ∣ c ∧
      ∃ g : NativeSporadic.B, g * zFive ^ c * g⁻¹ = y ∨ g * sFiveA ^ c * g⁻¹ = y)
    (hR : BFiveCentRes) {y : NativeSporadic.B} (hy : orderOf y = 5)
    (h7 : 7 ∣ Nat.card ↥(centralizer ({y} : Set NativeSporadic.B))) :
    Nat.card ↥(centralizer ({y} : Set NativeSporadic.B)) < 665280000 := by
  obtain ⟨c, hc, g, h | h⟩ := hconj y hy
  · exfalso
    apply hR.2
    rw [← h, TabMSeven.card_centralizer_conj, centralizer_pow_eq_of_five orderOf_zFive hc] at h7
    exact h7
  · rw [← h, TabMSeven.card_centralizer_conj, centralizer_pow_eq_of_five orderOf_sFiveA hc]
    exact hR.1

variable {G : Type} [Group G]

theorem card_inf_centralizer_le_of_twoA_res (hE : MonsterExistenceStatement G)
    (hconj : ∀ y : NativeSporadic.B, orderOf y = 5 → ∃ c : ℕ, ¬ 5 ∣ c ∧
      ∃ g : NativeSporadic.B, g * zFive ^ c * g⁻¹ = y ∨ g * sFiveA ^ c * g⁻¹ = y)
    (hR : BFiveCentRes) {t k : G} (ht : orderOf t = 2)
    (htc : Nat.card ↥(centralizer ({t} : Set G)) = 2 * monsterBabyOrder)
    (hk : orderOf k = 5) (htk : t * k = k * t) {L : Subgroup G}
    (hL : L ≤ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G))
    (hLc : Nat.card ↥L = 887040000) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) ≤ 887040000 := by
  haveI : Finite G := hE.1.1
  obtain ⟨f, hker, hle⟩ := exists_hom_of_twoA hE ht htc
  have hkX : k ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 htk.symm
  have hy : orderOf (f ⟨k, hkX⟩) = 5 :=
    orderOf_map_of_card_ker_two f hker Nat.prime_five (by norm_num)
      (by rw [Subgroup.orderOf_mk]; exact hk)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 (by rw [hLc]; norm_num)
  have hwX : (w : G) ∈ centralizer ({t} : Set G) := (hL w.2).1
  have hwk : (w : G) * k = k * w := mem_centralizer_singleton_iff.1 (hL w.2).2
  have hw7 : orderOf (f ⟨w, hwX⟩) = 7 :=
    orderOf_map_of_card_ker_two f hker (by norm_num) (by norm_num)
      (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hw)
  have hmem : f ⟨w, hwX⟩ ∈ centralizer ({f ⟨k, hkX⟩} : Set NativeSporadic.B) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext hwk)
  have h7 : 7 ∣ Nat.card ↥(centralizer ({f ⟨k, hkX⟩} : Set NativeSporadic.B)) :=
    hw7 ▸ Subgroup.orderOf_dvd_natCard _ hmem
  have hlt := card_centralizer_lt_of_seven_dvd hconj hR hy h7
  have h2 := hle ⟨k, hkX⟩
  obtain ⟨m, hm⟩ := hLc ▸ Subgroup.card_dvd_of_le hL
  change Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) ≤ _ at h2
  omega

end Bound

end CFSG.HardMathSupport.Dickson.I271.TabMFive
