module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import Mathlib.Algebra.BigOperators.Associated
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.SylowExponentPrimePart
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {W : Type*} [Group W]

theorem finsetSup_normal (s : Finset ℕ) (Z : ℕ → Subgroup W) (hZ : ∀ p ∈ s, (Z p).Normal) :
    (s.sup Z).Normal :=
  Finset.sup_induction (p := fun K : Subgroup W => K.Normal) inferInstance
    (fun M hM N hN => @Subgroup.sup_normal _ _ M N hM hN) hZ

theorem natCard_finsetSup_dvd_prod [Finite W] (s : Finset ℕ) (Z : ℕ → Subgroup W)
    (hZ : ∀ p ∈ s, (Z p).Normal) : Nat.card ↥(s.sup Z) ∣ ∏ p ∈ s, Nat.card ↥(Z p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hnormal : (Z p).Normal := hZ p (Finset.mem_insert_self p s)
    rw [Finset.sup_insert, Finset.prod_insert hp]
    exact (natCard_sup_dvd _ _).trans
      (Nat.mul_dvd_mul_left _ (ih fun q hq => hZ q (Finset.mem_insert_of_mem hq)))

theorem map_subtype_eq_bot_iff {U : Subgroup W} {K : Subgroup U} :
    K.map U.subtype = ⊥ ↔ K = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff]

theorem mem_of_orderOf_prime_of_mem_sup [Finite W] {N L : Subgroup W} [N.Normal] {q : ℕ}
    (hq : q.Prime) (hqL : ¬ q ∣ Nat.card L) {x : W} (hx : x ∈ N ⊔ L) (hxq : orderOf x = q) :
    x ∈ N := by
  set f := QuotientGroup.mk' N with hf
  have hmap : (N ⊔ L).map f = L.map f := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff N).2 (by rw [hf, QuotientGroup.ker_mk']),
      bot_sup_eq]
  have hmem : f x ∈ L.map f := hmap ▸ ⟨x, hx, rfl⟩
  have h1 : orderOf (f x) ∣ Nat.card (L.map f) := Subgroup.orderOf_dvd_natCard _ hmem
  have h2 : orderOf (f x) ∣ q := hxq ▸ orderOf_map_dvd f x
  rcases hq.eq_one_or_self_of_dvd _ h2 with h | h
  · have hx1 : f x = 1 := orderOf_eq_one_iff.1 h
    rw [hf] at hx1
    exact (QuotientGroup.eq_one_iff x).1 hx1
  · exact absurd ((h ▸ h1).trans (Subgroup.card_map_dvd L f)) hqL

theorem factorization_natCard_eq_of_not_dvd_index [Finite W] {K : Subgroup W} {r : ℕ}
    (h : ¬ r ∣ K.index) :
    (Nat.card K).factorization r = (Nat.card W).factorization r := by
  rw [← Subgroup.card_mul_index K,
    Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h, add_zero]

theorem exponent_eq_of_forall_prime_exists_le [Finite W] {U₀ : Subgroup W}
    (h : ∀ r : ℕ, r.Prime → ∃ T : Subgroup W, T ≤ U₀ ∧
      r ^ (Monoid.exponent W).factorization r ∣ Monoid.exponent T) :
    Monoid.exponent U₀ = Monoid.exponent W := by
  refine Nat.dvd_antisymm (exponent_subgroup_dvd U₀) ?_
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r k hr hk
  obtain ⟨T, hTle, hT⟩ := h r hr
  have hexp : Monoid.exponent W ≠ 0 := Monoid.ExponentExists.exponent_ne_zero .of_finite
  have hk' : k ≤ (Monoid.exponent W).factorization r := (hr.pow_dvd_iff_le_factorization hexp).1 hk
  exact ((pow_dvd_pow r hk').trans hT).trans (exponent_dvd_exponent_of_le hTle)

theorem exists_le_exponent_eq_of_not_dvd_index [Finite W] {K : Subgroup W} {r : ℕ}
    (hr : r.Prime) (hK : ¬ r ∣ K.index) :
    ∃ T : Subgroup W, T ≤ K ∧ Monoid.exponent T = r ^ (Monoid.exponent W).factorization r := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) r
    (n := (Nat.card ↥K).factorization r) (Nat.ordProj_dvd _ _)
  refine ⟨Q.map K.subtype, Subgroup.map_subtype_le Q, exponent_eq_pow_factorization_exponent hr ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, hQ,
    factorization_natCard_eq_of_not_dvd_index hK]

theorem eq_of_le_of_natCard_eq_pow_factorization [Finite W] {A K L : Subgroup W}
    [IsMulCommutative A] {p : ℕ} (hp : p.Prime) (hKA : K ≤ A) (hLA : L ≤ A)
    (hK : Nat.card K = p ^ (Nat.card A).factorization p)
    (hL : Nat.card L = p ^ (Nat.card A).factorization p) : K = L := by
  have : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card (K.subgroupOf A) = p ^ (Nat.card A).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv, hK]
  have hL' : Nat.card (L.subgroupOf A) = p ^ (Nat.card A).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv, hL]
  have : Unique (Sylow p A) := Sylow.unique_of_normal (Sylow.ofCard _ hK') inferInstance
  have hsub : K.subgroupOf A = L.subgroupOf A :=
    congrArg (fun P : Sylow p A => (P : Subgroup A))
      (Subsingleton.elim (Sylow.ofCard _ hK') (Sylow.ofCard _ hL'))
  have h := congrArg (Subgroup.map A.subtype) hsub
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKA,
    inf_eq_left.2 hLA] at h

variable {G : Type*} [Group G] [Finite G] {π : Set ℕ} {H U : Subgroup G} {A : Subgroup U}
  {S Z : ℕ → Subgroup U}

theorem exists_ne_bot_exponent_eq_of_isHallPiSubgroup [Group.IsSolvable U] [A.Normal]
    (hU : U ≠ ⊥) (hA : IsHallPiSubgroup π A)
    (hfree : ∀ q : ℕ, q.Prime → q ∉ π → ∀ v ∈ U, orderOf v = q →
      H ⊓ Subgroup.centralizer {v} = ⊥)
    (hS : ∀ p ∈ (Nat.card A).primeFactors,
      S p ≤ A ∧ Nat.card (S p) = p ^ (Nat.card A).factorization p)
    (hZS : ∀ p ∈ (Nat.card A).primeFactors, Z p ≤ S p)
    (hZnormal : ∀ p ∈ (Nat.card A).primeFactors, (Z p).Normal)
    (hZexp : ∀ p ∈ (Nat.card A).primeFactors, Monoid.exponent (Z p) = Monoid.exponent (S p))
    (hZfree : ∀ p ∈ (Nat.card A).primeFactors, ∀ z ∈ Z p, (z : G) ≠ 1 →
      H ⊓ Subgroup.centralizer {(z : G)} = ⊥) :
    ∃ U₀ : Subgroup U, U₀ ≠ ⊥ ∧ Monoid.exponent U₀ = Monoid.exponent U ∧
      ∀ u ∈ U₀, (u : G) ≠ 1 → H ⊓ Subgroup.centralizer {(u : G)} = ⊥ := by
  classical
  set s := (Nat.card A).primeFactors with hs
  set Z' : Subgroup ↥U := s.sup Z with hZ'def
  have hZ'normal : Z'.Normal := finsetSup_normal s Z hZnormal
  have hZ'A : Z' ≤ A := Finset.sup_le fun p hp => (hZS p hp).trans (hS p hp).1
  obtain ⟨V, hV⟩ := exists_isHallSubgroup (X := ↥U) πᶜ
  set U₀ : Subgroup ↥U := Z' ⊔ V with hU₀def
  have hV1 : ∀ q : ℕ, q.Prime → q ∈ π → ¬ q ∣ Nat.card V := by
    intro q hq hqπ hdvd
    exact isPiNumber_iff.1 hV.natCard q (Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.card_pos.ne'⟩) hqπ
  have hV2 : ∀ r : ℕ, r.Prime → r ∉ π → ¬ r ∣ V.index := by
    intro r hr hrπ hdvd
    have h := isPiNumber_iff.1 hV.index r
      (Nat.mem_primeFactors.2 ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩)
    rw [compl_compl] at h
    exact hrπ h
  have hexpU₀ : Monoid.exponent ↥U₀ = Monoid.exponent ↥U := by
    refine exponent_eq_of_forall_prime_exists_le fun r hr => ?_
    by_cases hrU : r ∣ Nat.card ↥U
    · by_cases hrπ : r ∈ π
      ·
        have hrA : ¬ r ∣ A.index := fun hd => hA.notMem_of_mem_primeFactors_index r
          (Nat.mem_primeFactors.2 ⟨hr, hd, Subgroup.index_ne_zero_of_finite⟩) hrπ
        have hfac : (Nat.card ↥A).factorization r = (Nat.card ↥U).factorization r :=
          factorization_natCard_eq_of_not_dvd_index hrA
        have hrs : r ∈ s := by
          rw [hs]
          refine Nat.mem_primeFactors.2 ⟨hr, ?_, Nat.card_pos.ne'⟩
          exact (hr.dvd_iff_one_le_factorization Nat.card_pos.ne').2
            (hfac ▸ (hr.dvd_iff_one_le_factorization Nat.card_pos.ne').1 hrU)
        refine ⟨Z r, le_sup_of_le_left (Finset.le_sup (f := Z) hrs), ?_⟩
        rw [hZexp r hrs,
          exponent_eq_pow_factorization_exponent hr ((hS r hrs).2.trans (by rw [hfac]))]
      ·
        obtain ⟨T, hT, hTexp⟩ := exists_le_exponent_eq_of_not_dvd_index hr (hV2 r hr hrπ)
        exact ⟨T, hT.trans le_sup_right, by rw [hTexp]⟩
    · refine ⟨⊥, bot_le, ?_⟩
      rw [Nat.factorization_eq_zero_of_not_dvd
        (fun h => hrU (h.trans Group.exponent_dvd_nat_card))]
      simp
  refine ⟨U₀, ?_, hexpU₀, ?_⟩
  ·
    intro hbot
    have h1 : Monoid.exponent ↥U = 1 := by rw [← hexpU₀, hbot]; simp
    have : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).2 hU
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥U)
    exact hx (by simpa [h1] using Monoid.pow_exponent_eq_one x)
  intro u hu hu1
  rw [Subgroup.eq_bot_iff_forall]
  intro h hmem
  by_contra hh1
  set K : Subgroup ↥U := (Subgroup.centralizer {h}).subgroupOf U ⊓ U₀ with hK
  have huK : u ∈ K :=
    ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 hmem.2).symm), hu⟩
  have hKne : K ≠ ⊥ := fun hbot => hu1 (by
    have h' := (Subgroup.mem_bot).1 (hbot ▸ huK)
    rw [h']; rfl)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card ↥K) (fun hcard => hKne (Subgroup.card_eq_one.1 hcard))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) q hqdvd
  set v : ↥U := (w : ↥U) with hv
  have hvK : v ∈ K := w.2
  have hvord : orderOf v = q := by rw [hv, Subgroup.orderOf_coe, hw]
  have hvordG : orderOf ((v : ↥U) : G) = q := by rw [Subgroup.orderOf_coe, hvord]
  have hv1 : ((v : ↥U) : G) ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hvordG
    exact hq.one_lt.ne hvordG
  have hhv : h ∈ H ⊓ Subgroup.centralizer {((v : ↥U) : G)} :=
    ⟨hmem.1, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hvK.1)).symm⟩
  by_cases hqπ : q ∈ π
  ·
    have hvZ' : v ∈ Z' := mem_of_orderOf_prime_of_mem_sup hq (hV1 q hq hqπ) hvK.2 hvord
    have hqs : q ∈ s := Nat.mem_primeFactors.2
      ⟨hq, hvord ▸ Subgroup.orderOf_dvd_natCard A (hZ'A hvZ'), Nat.card_pos.ne'⟩
    have hsplit : Z' = Z q ⊔ (s.erase q).sup Z := by
      rw [hZ'def]
      conv_lhs => rw [← Finset.insert_erase hqs]
      rw [Finset.sup_insert]
    have hcop : ¬ q ∣ Nat.card ↥((s.erase q).sup Z) := by
      intro hdvd
      obtain ⟨p, hp, hpq⟩ := (Nat.Prime.prime hq).dvd_finsetProd_iff _
        |>.1 (hdvd.trans (natCard_finsetSup_dvd_prod (s.erase q) Z
          fun p hp => hZnormal p (Finset.mem_of_mem_erase hp)))
      have hps : p ∈ s := Finset.mem_of_mem_erase hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (hs ▸ hps)
      have hqpow : q ∣ p ^ (Nat.card ↥A).factorization p :=
        (hpq.trans (Subgroup.card_dvd_of_le (hZS p hps))).trans (dvd_of_eq (hS p hps).2)
      exact Finset.ne_of_mem_erase hp
        ((Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow hqpow)).symm
    have hZqn : (Z q).Normal := hZnormal q hqs
    have hvZq : v ∈ Z q := mem_of_orderOf_prime_of_mem_sup hq hcop (hsplit ▸ hvZ') hvord
    rw [hZfree q hqs v hvZq hv1, Subgroup.mem_bot] at hhv
    exact hh1 hhv
  ·
    rw [hfree q hq hqπ _ (v : ↥U).2 hvordG, Subgroup.mem_bot] at hhv
    exact hh1 hhv

theorem exists_le_ne_bot_exponent_eq_of_isHallPiSubgroup [Group.IsSolvable U] [A.Normal]
    (hU : U ≠ ⊥) (hA : IsHallPiSubgroup π A)
    (hfree : ∀ q : ℕ, q.Prime → q ∉ π → ∀ v ∈ U, orderOf v = q →
      H ⊓ Subgroup.centralizer {v} = ⊥)
    (hS : ∀ p ∈ (Nat.card A).primeFactors,
      S p ≤ A ∧ Nat.card (S p) = p ^ (Nat.card A).factorization p)
    (hZS : ∀ p ∈ (Nat.card A).primeFactors, Z p ≤ S p)
    (hZnormal : ∀ p ∈ (Nat.card A).primeFactors, (Z p).Normal)
    (hZexp : ∀ p ∈ (Nat.card A).primeFactors, Monoid.exponent (Z p) = Monoid.exponent (S p))
    (hZfree : ∀ p ∈ (Nat.card A).primeFactors, ∀ z ∈ Z p, (z : G) ≠ 1 →
      H ⊓ Subgroup.centralizer {(z : G)} = ⊥) :
    ∃ U₀ : Subgroup G, U₀ ≤ U ∧ U₀ ≠ ⊥ ∧ Monoid.exponent U₀ = Monoid.exponent U ∧
      ∀ u ∈ U₀, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥ := by
  obtain ⟨U₀, hne, hexp, hfr⟩ :=
    exists_ne_bot_exponent_eq_of_isHallPiSubgroup hU hA hfree hS hZS hZnormal hZexp hZfree
  refine ⟨U₀.map U.subtype, Subgroup.map_subtype_le U₀,
    fun hbot => hne (map_subtype_eq_bot_iff.1 hbot), ?_, ?_⟩
  · rw [← hexp]
    exact (Monoid.exponent_eq_of_mulEquiv
      (Subgroup.equivMapOfInjective U₀ U.subtype U.subtype_injective)).symm
  · rintro u ⟨u', hu', rfl⟩ hu1
    exact hfr u' hu' hu1

end

end CFSG.FeitThompson
