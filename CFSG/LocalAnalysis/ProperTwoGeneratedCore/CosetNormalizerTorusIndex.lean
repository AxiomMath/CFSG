module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizer

open CFSG.Semidihedral.Principal
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

@[expose] def invertedPart (A : Subgroup G) (t : G) : Set G :=
  {a | a ∈ A ∧ t⁻¹ * a * t = a⁻¹}

theorem mem_invertedPart {A : Subgroup G} {t a : G} :
    a ∈ invertedPart A t ↔ a ∈ A ∧ t⁻¹ * a * t = a⁻¹ :=
  Iff.rfl

@[expose] def invertedSubgroup (A : Subgroup G) [IsMulCommutative A] (t : G) : Subgroup G where
  carrier := invertedPart A t
  mul_mem' := by
    rintro a b ⟨ha, hat⟩ ⟨hb, hbt⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have hab : b * a = a * b :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨b, hb⟩ ⟨a, ha⟩)
    calc t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by group
      _ = (b * a)⁻¹ := by rw [hat, hbt, mul_inv_rev]
      _ = (a * b)⁻¹ := by rw [hab]
  one_mem' := ⟨A.one_mem, by group⟩
  inv_mem' := by
    rintro a ⟨ha, hat⟩
    refine ⟨A.inv_mem ha, ?_⟩
    calc t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [hat]

theorem coe_invertedSubgroup (A : Subgroup G) [IsMulCommutative A] (t : G) :
    (invertedSubgroup A t : Set G) = invertedPart A t :=
  rfl

theorem mem_invertedSubgroup {A : Subgroup G} [IsMulCommutative A] {t a : G} :
    a ∈ invertedSubgroup A t ↔ a ∈ A ∧ t⁻¹ * a * t = a⁻¹ :=
  Iff.rfl

theorem eq_one_or_eq_of_mem_zpowers {t g : G} (ht : orderOf t = 2) (hg : g ∈ Subgroup.zpowers t) :
    g = 1 ∨ g = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem inv_eq_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, ← ht, pow_orderOf_eq_one]

theorem conj_commutatorElement_eq_inv {t : G} (ht : orderOf t = 2) (x : G) :
    t⁻¹ * ⁅x, t⁆ * t = ⁅x, t⁆⁻¹ := by
  have h := inv_eq_of_orderOf_eq_two ht
  rw [commutatorElement_def]
  calc t⁻¹ * (x * t * x⁻¹ * t⁻¹) * t = t⁻¹ * x * t * x⁻¹ := by group
    _ = t * x * t⁻¹ * x⁻¹ := by rw [h]
    _ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by group

theorem exists_pow_sq_eq_of_odd {d : G} (hd : Odd (orderOf d)) : ∃ m : ℕ, (d ^ m) ^ 2 = d := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.coprime_two_left.mpr hd)
  exact ⟨m, by rw [← pow_mul, mul_comm, pow_mul, hm]⟩

theorem conj_pow_eq_inv {t d : G} (hd : t⁻¹ * d * t = d⁻¹) (m : ℕ) :
    t⁻¹ * d ^ m * t = (d ^ m)⁻¹ := by
  have h := map_pow (MulAut.conj t⁻¹) d m
  simp only [MulAut.conj_apply, inv_inv] at h
  rw [h, hd, inv_pow]

theorem exists_commutatorElement_eq_of_mem_invertedPart [Finite G] {A : Subgroup G}
    (hAodd : Odd (Nat.card A)) {t a : G} (ht : orderOf t = 2) (ha : a ∈ invertedPart A t) :
    ∃ b ∈ invertedPart A t, ⁅b, t⁆ = a := by
  obtain ⟨haA, hat⟩ := ha
  obtain ⟨m, hm⟩ := exists_pow_sq_eq_of_odd (hAodd.of_dvd_nat (A.orderOf_dvd_natCard haA))
  have hbt := conj_pow_eq_inv hat m
  refine ⟨a ^ m, ⟨A.pow_mem haA m, hbt⟩, ?_⟩
  have h := inv_eq_of_orderOf_eq_two ht
  have hbt' : t * (a ^ m)⁻¹ * t⁻¹ = a ^ m := by
    have := congrArg (·⁻¹) hbt
    simpa only [mul_inv_rev, inv_inv, h, mul_assoc] using this
  calc ⁅a ^ m, t⁆ = a ^ m * (t * (a ^ m)⁻¹ * t⁻¹) := by
        rw [commutatorElement_def]; group
    _ = (a ^ m) ^ 2 := by rw [hbt', pow_two]
    _ = a := hm

theorem exists_mul_commute_of_inverted [Finite G] {t : G} (ht : orderOf t = 2) (M : Subgroup G)
    (hModd : Odd (Nat.card M)) (hM : ∀ r ∈ M, t⁻¹ * r * t = r⁻¹) {x : G}
    (hx : x⁻¹ * t * x * t⁻¹ ∈ M) : ∃ r ∈ M, Commute (x * r) t := by
  set d := x⁻¹ * t * x * t⁻¹ with hd
  obtain ⟨m, hm⟩ := exists_pow_sq_eq_of_odd (hModd.of_dvd_nat (M.orderOf_dvd_natCard hx))
  have hr : d ^ m ∈ M := M.pow_mem hx m
  refine ⟨d ^ m, hr, ?_⟩
  have h := inv_eq_of_orderOf_eq_two ht
  have hrt : t * d ^ m * t⁻¹ = (d ^ m)⁻¹ := by
    have := hM _ hr
    rw [h] at this
    rwa [h]
  have htx : t * x * t⁻¹ = x * d := by rw [hd]; group
  have key : t * (x * d ^ m) * t⁻¹ = x * d ^ m := by
    calc t * (x * d ^ m) * t⁻¹ = (t * x * t⁻¹) * (t * d ^ m * t⁻¹) := by group
      _ = x * ((d ^ m) ^ 2 * (d ^ m)⁻¹) := by rw [htx, hrt, hm, mul_assoc]
      _ = x * d ^ m := by rw [pow_two, mul_inv_cancel_right]
  calc x * d ^ m * t = t * (x * d ^ m) * t⁻¹ * t := by rw [key]
    _ = t * (x * d ^ m) := by group

theorem relIndex_eq_card_of_coe_eq_mul [Finite G] {H K M : Subgroup G} (hHK : H ≤ K)
    (hK : (K : Set G) = (H : Set G) * (M : Set G)) (hHM : H ⊓ M = ⊥) :
    H.relIndex K = Nat.card M := by
  have hMK : M ≤ K := fun m hm => by
    rw [← SetLike.mem_coe, hK]
    exact ⟨1, H.one_mem, m, hm, one_mul m⟩
  let f : H × M → K := fun p => ⟨(p.1 : G) * p.2, K.mul_mem (hHK p.1.2) (hMK p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h₁, m₁⟩ ⟨h₂, m₂⟩ heq
      have heq' : (h₁ : G) * m₁ = h₂ * m₂ := congrArg Subtype.val heq
      have hmem : (h₂ : G)⁻¹ * h₁ = m₂ * (m₁ : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
      have hbot : (h₂ : G)⁻¹ * h₁ ∈ H ⊓ M :=
        ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, hmem ▸ M.mul_mem m₂.2 (M.inv_mem m₁.2)⟩
      rw [hHM, Subgroup.mem_bot, inv_mul_eq_one] at hbot
      have hh : h₁ = h₂ := Subtype.ext hbot.symm
      subst hh
      have hm : m₁ = m₂ := Subtype.ext (mul_left_cancel heq')
      rw [hm]
    · rintro ⟨k, hk⟩
      rw [← SetLike.mem_coe, hK] at hk
      obtain ⟨h, hh, m, hm, rfl⟩ := hk
      exact ⟨(⟨h, hh⟩, ⟨m, hm⟩), rfl⟩
  have hcard : Nat.card K = Nat.card H * Nat.card M := by
    rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]
  have h := Subgroup.relIndex_mul_card H K
  rw [inf_eq_left.mpr hHK, hcard, mul_comm (Nat.card H)] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem odd_pair_torus_controls_common_involution_centralizer_index [Finite G]
    (E : Subgroup G) {t : G} (ht : orderOf t = 2) (htE : t ∈ Subgroup.normalizer (E : Set G))
    (I : Subgroup G) (hIE : I ≤ E) (_hInormal : (I.subgroupOf E).Normal)
    (hIodd : Odd (Nat.card I)) (hEt : ⁅E, Subgroup.zpowers t⁆ ≤ I)
    {u : G} (_huE : u ∈ E) (_hu : orderOf u = 2) (_hut : Commute u t)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer {u})
    (hLnormal : (L.subgroupOf (Subgroup.centralizer {u})).Normal) (htL : t ∈ L)
    [IsMulCommutative (L ⊓ E : Subgroup G)] (hAodd : Odd (Nat.card (L ⊓ E : Subgroup G))) :
    invertedPart (L ⊓ E) t = ((⁅L ⊓ E, Subgroup.zpowers t⁆ : Subgroup G) : Set G) ∧
      ⁅L ⊓ E, Subgroup.zpowers t⁆ = ⁅I ⊓ Subgroup.centralizer {u}, Subgroup.zpowers t⁆ ∧
      ⁅I ⊓ Subgroup.centralizer {u}, Subgroup.zpowers t⁆ ≤ I ∧
      ((E ⊓ Subgroup.centralizer {u} : Subgroup G) : Set G) =
        ((E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) *
          invertedPart (L ⊓ E) t ∧
      ((E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ∩
          invertedPart (L ⊓ E) t = {1} ∧
      (E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t}).relIndex
          (E ⊓ Subgroup.centralizer {u}) = Nat.card (invertedPart (L ⊓ E) t) ∧
      Nat.card (invertedPart (L ⊓ E) t) =
        (L ⊓ E ⊓ Subgroup.centralizer {t}).relIndex (L ⊓ E) := by
  set A : Subgroup G := L ⊓ E with hA
  set C : Subgroup G := I ⊓ Subgroup.centralizer {u} with hC
  set M : Subgroup G := invertedSubgroup A t with hM
  have htinv := inv_eq_of_orderOf_eq_two ht
  have htu : t ∈ Subgroup.centralizer {u} := hLC htL
  have hAt : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha =>
    ⟨L.mul_mem (L.mul_mem htL ha.1) (L.inv_mem htL), (Subgroup.mem_normalizer_iff.mp htE a).mp ha.2⟩
  have hcomm_mem : ∀ x ∈ E, ⁅x, t⁆ ∈ I := fun x hx =>
    hEt (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t))
  have hcomm_le : ∀ (X Y : Subgroup G), (∀ x ∈ X, ⁅x, t⁆ ∈ Y) → ⁅X, Subgroup.zpowers t⁆ ≤ Y := by
    intro X Y h
    rw [Subgroup.commutator_le]
    intro x hx g hg
    rcases eq_one_or_eq_of_mem_zpowers ht hg with rfl | rfl
    · rw [commutatorElement_one_right]
      exact Y.one_mem
    · exact h x hx
  have hAM : ⁅A, Subgroup.zpowers t⁆ ≤ M := by
    refine hcomm_le A M fun a ha => ⟨?_, conj_commutatorElement_eq_inv ht a⟩
    have : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact A.mul_mem ha (hAt _ (A.inv_mem ha))
  have hCM : ⁅C, Subgroup.zpowers t⁆ ≤ M := by
    refine hcomm_le C M fun c hc => ⟨⟨?_, hIE (hcomm_mem c (hIE hc.1))⟩,
      conj_commutatorElement_eq_inv ht c⟩
    have hct : c * t * c⁻¹ ∈ L := by
      have := hLnormal.conj_mem ⟨t, htu⟩ (Subgroup.mem_subgroupOf.mpr htL) ⟨c, hc.2⟩
      exact Subgroup.mem_subgroupOf.mp this
    rw [commutatorElement_def]
    exact L.mul_mem hct (L.inv_mem htL)
  have hMcomm := fun (a : G) (ha : a ∈ invertedPart A t) =>
    exists_commutatorElement_eq_of_mem_invertedPart hAodd ht ha
  have hMA : M ≤ ⁅A, Subgroup.zpowers t⁆ := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hMcomm a ha
    exact Subgroup.commutator_mem_commutator hb.1 (Subgroup.mem_zpowers t)
  have hMI : M ≤ I := fun a ha =>
    hEt (Subgroup.commutator_mono inf_le_right le_rfl (hMA ha))
  have hMC : M ≤ C := fun a ha => ⟨hMI ha, hLC ha.1.1⟩
  have hMCt : M ≤ ⁅C, Subgroup.zpowers t⁆ := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hMcomm a ha
    exact Subgroup.commutator_mem_commutator (hMC hb) (Subgroup.mem_zpowers t)
  have hMeq : ⁅A, Subgroup.zpowers t⁆ = M := le_antisymm hAM hMA
  have hCeq : ⁅C, Subgroup.zpowers t⁆ = M := le_antisymm hCM hMCt
  have hModd : Odd (Nat.card M) := hAodd.of_dvd_nat
    (Subgroup.card_dvd_of_le fun a ha => (show a ∈ invertedPart A t from ha).1)
  have hMinv : ∀ r ∈ M, t⁻¹ * r * t = r⁻¹ := fun r hr => hr.2
  have hdisj : E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t} ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxt⟩, hxA, hxinv⟩
    have hxt' : t⁻¹ * x * t = x := by
      have hxt := Subgroup.mem_centralizer_singleton_iff.mp hxt
      rw [mul_assoc, hxt, inv_mul_cancel_left]
    have hxx : x = x⁻¹ := hxt'.symm.trans hxinv
    have hsq : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hxx]
      exact mul_inv_cancel x
    have hodd : Odd (orderOf x) := hAodd.of_dvd_nat (A.orderOf_dvd_natCard hxA)
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  have hdecomp : ((E ⊓ Subgroup.centralizer {u} : Subgroup G) : Set G) =
      ((E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) *
        (M : Set G) := by
    apply Set.Subset.antisymm
    · rintro y ⟨hyE, hyu⟩
      have hyu' := Subgroup.mem_centralizer_singleton_iff.mp hyu
      have hcop : ¬ 2 ∣ Nat.card C :=
        (hIodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)).not_two_dvd_nat
      let α : Subgroup.zpowers t →* MulAut G := MulAut.conj.comp (Subgroup.zpowers t).subtype
      have hp : IsPGroup 2 (Subgroup.zpowers t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
      have hinv : ∀ a : Subgroup.zpowers t, ∀ x : G, y⁻¹ * x ∈ C → y⁻¹ * α a x ∈ C := by
        rintro ⟨a, ha⟩ x hx
        change y⁻¹ * (a * x * a⁻¹) ∈ C
        rcases eq_one_or_eq_of_mem_zpowers ht ha with h | h
        · simpa [h] using hx
        · rw [h]
          have h1 : y⁻¹ * t * y * t⁻¹ ∈ C := by
            refine ⟨?_, ?_⟩
            · have := hcomm_mem _ (E.inv_mem hyE)
              rwa [commutatorElement_def, inv_inv] at this
            · exact (Subgroup.centralizer {u}).mul_mem ((Subgroup.centralizer {u}).mul_mem
                ((Subgroup.centralizer {u}).mul_mem ((Subgroup.centralizer {u}).inv_mem hyu) htu)
                hyu) ((Subgroup.centralizer {u}).inv_mem htu)
          have h2 : t * (y⁻¹ * x) * t⁻¹ ∈ C := by
            refine ⟨?_, ?_⟩
            · have hi : y⁻¹ * x ∈ I := hx.1
              have := hcomm_mem _ (E.inv_mem (hIE hi))
              rw [commutatorElement_def, inv_inv] at this
              have h4 : t * (y⁻¹ * x) * t⁻¹ = (y⁻¹ * x) * ((y⁻¹ * x)⁻¹ * t * (y⁻¹ * x) * t⁻¹) :=
                by group
              rw [h4]
              exact I.mul_mem hi this
            · exact (Subgroup.centralizer {u}).mul_mem
                ((Subgroup.centralizer {u}).mul_mem htu hx.2)
                ((Subgroup.centralizer {u}).inv_mem htu)
          have h5 : y⁻¹ * (t * x * t⁻¹) = (y⁻¹ * t * y * t⁻¹) * (t * (y⁻¹ * x) * t⁻¹) := by group
          rw [h5]
          exact C.mul_mem h1 h2
      obtain ⟨c₀, hc₀, hfix⟩ := (coprime_invariant_coset_fixed 2 hp α C hcop y).2 hinv
      have hc₀t : Commute c₀ t := by
        have h := hfix ⟨t, Subgroup.mem_zpowers t⟩
        change t * c₀ * t⁻¹ = c₀ at h
        exact (mul_inv_eq_iff_eq_mul.mp h).symm
      set i := c₀⁻¹ * y with hi
      have hiC : i ∈ C := by
        have := C.inv_mem hc₀
        rwa [mul_inv_rev, inv_inv] at this
      have hc₀E : c₀ ∈ E := by
        have : c₀ = y * (y⁻¹ * c₀) := by group
        rw [this]
        exact E.mul_mem hyE (hIE hc₀.1)
      have hc₀u : c₀ ∈ Subgroup.centralizer {u} := by
        have : c₀ = y * (y⁻¹ * c₀) := by group
        rw [this]
        exact (Subgroup.centralizer {u}).mul_mem hyu hc₀.2
      have hid : i⁻¹ * t * i * t⁻¹ ∈ M := by
        rw [← hCeq]
        have := Subgroup.commutator_mem_commutator (C.inv_mem hiC) (Subgroup.mem_zpowers t)
        rwa [commutatorElement_def, inv_inv] at this
      obtain ⟨r, hrM, hrt⟩ := exists_mul_commute_of_inverted ht M hModd hMinv hid
      refine ⟨c₀ * (i * r), ⟨⟨E.mul_mem hc₀E (hIE (C.mul_mem hiC (hMC hrM)).1),
          (Subgroup.centralizer {u}).mul_mem hc₀u (C.mul_mem hiC (hMC hrM)).2⟩,
          Subgroup.mem_centralizer_singleton_iff.mpr (hc₀t.mul_left hrt).eq⟩,
        r⁻¹, M.inv_mem hrM, ?_⟩
      rw [hi]
      group
    · rintro _ ⟨c, ⟨⟨hcE, hcu⟩, -⟩, a, ha, rfl⟩
      exact ⟨E.mul_mem hcE ha.1.2, (Subgroup.centralizer {u}).mul_mem hcu (hLC ha.1.1)⟩
  have hAdecomp : (A : Set G) = ((A ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) *
      (M : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxd : x⁻¹ * t * x * t⁻¹ ∈ M := by
        rw [← hMeq]
        have := Subgroup.commutator_mem_commutator (A.inv_mem hx) (Subgroup.mem_zpowers t)
        rwa [commutatorElement_def, inv_inv] at this
      obtain ⟨r, hrM, hrt⟩ := exists_mul_commute_of_inverted ht M hModd hMinv hxd
      exact ⟨x * r, ⟨A.mul_mem hx hrM.1, Subgroup.mem_centralizer_singleton_iff.mpr hrt.eq⟩,
        r⁻¹, M.inv_mem hrM, by group⟩
    · rintro _ ⟨c, ⟨hcA, -⟩, a, ha, rfl⟩
      exact A.mul_mem hcA ha.1
  have hAdisj : A ⊓ Subgroup.centralizer {t} ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxA, hxt⟩, hxM⟩
    have : x ∈ E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t} ⊓ M :=
      ⟨⟨⟨hxA.2, hLC hxA.1⟩, hxt⟩, hxM⟩
    rwa [hdisj] at this
  refine ⟨?_, hMeq.trans hCeq.symm, ?_, hdecomp, ?_, ?_, ?_⟩
  · rw [hMeq]
    rfl
  · exact hcomm_le C I fun c hc => hcomm_mem c (hIE hc.1)
  · ext x
    constructor
    · rintro ⟨hx, hxM⟩
      have : x ∈ E ⊓ Subgroup.centralizer {u} ⊓ Subgroup.centralizer {t} ⊓ M := ⟨hx, hxM⟩
      rw [hdisj] at this
      exact Subgroup.mem_bot.mp this
    · rintro rfl
      exact ⟨Subgroup.one_mem _, M.one_mem⟩
  · exact relIndex_eq_card_of_coe_eq_mul inf_le_left hdecomp hdisj
  · exact (relIndex_eq_card_of_coe_eq_mul inf_le_left hAdecomp hAdisj).symm

end CFSG.ProperTwoGeneratedCore.CosetNormalizer
