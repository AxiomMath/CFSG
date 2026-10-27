module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrimePrimaryFactorization
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrimaryUniqueness
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {H Q : Type*} [Group H] [Group Q] {p : ℕ}

theorem primeRegular_eq_of_map_eq [Fact p.Prime] (π : H →* Q)
    (hcentral : π.ker ≤ Subgroup.center H) (hker : IsPGroup p π.ker) {x y : H}
    (hx : ¬ p ∣ orderOf x) (hy : ¬ p ∣ orderOf y) (hxy : π x = π y) : x = y := by
  have hpp : p.Prime := Fact.out
  have hz : x⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hker ⟨x⁻¹ * y, hz⟩
  have hzord : orderOf (x⁻¹ * y) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hk
  have hcomm : Commute (x⁻¹ * y) x :=
    ((Subgroup.mem_center_iff.mp (hcentral hz)) x).symm
  have hxcop : Nat.Coprime p (orderOf x) := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hx
  have hycop : Nat.Coprime p (orderOf y) := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hy
  have hprod : x⁻¹ * y * x = 1 * y := by
    rw [one_mul, hcomm.eq]
    group
  obtain ⟨-, hxy'⟩ := CFSG.LyonsUnitaryFour.primary_factorization_unique (k' := 0) hzord hxcop
    hcomm (by simp) hycop (Commute.one_left y) hprod
  exact hxy'

theorem exists_primeRegular_lift [Finite H] [Fact p.Prime] (π : H →* Q)
    (hπ : Function.Surjective π) {q : Q} (hq : ¬ p ∣ orderOf q) :
    ∃ x : H, ¬ p ∣ orderOf x ∧ π x = q := by
  have hpp : p.Prime := Fact.out
  obtain ⟨h, rfl⟩ := hπ q
  obtain ⟨a, b, e, -, -, hab, habh, ha, hb⟩ := finite_prime_primary_factorization h p hpp
  have ha' : orderOf (π a) ∣ p ^ e := (orderOf_map_dvd π a).trans ha
  have hb' : Nat.Coprime p (orderOf (π b)) := hb.coprime_dvd_right (orderOf_map_dvd π b)
  have hq' : Nat.Coprime p (orderOf (π h)) := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hq
  obtain ⟨-, hbq⟩ := CFSG.LyonsUnitaryFour.primary_factorization_unique (k' := 0) ha' hb'
    (hab.map π) (by simp) hq' (Commute.one_left _) (by rw [one_mul, ← map_mul, habh])
  exact ⟨b, (Nat.Prime.coprime_iff_not_dvd hpp).mp hb, hbq⟩

theorem orderOf_conj_eq (c x : H) : orderOf (c * x * c⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem card_comap_of_surjective [Finite H] (π : H →* Q) (hπ : Function.Surjective π)
    (K : Subgroup Q) : Nat.card (K.comap π) = Nat.card π.ker * Nat.card K := by
  have : Finite Q := Finite.of_surjective π hπ
  have hH : Nat.card H = Nat.card Q * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have h1 := Subgroup.card_mul_index (K.comap π)
  have h2 := Subgroup.card_mul_index K
  rw [Subgroup.index_comap_of_surjective K hπ] at h1
  have hidx : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hidx
  rw [h1, hH, ← h2]
  ring

theorem central_p_quotient_prime_regular_elements_of_surjective [Finite H] [Fact p.Prime]
    (π : H →* Q) (hπ : Function.Surjective π) (hcentral : π.ker ≤ Subgroup.center H)
    (hker : IsPGroup p π.ker) :
    Set.BijOn π {x : H | ¬ p ∣ orderOf x} {q : Q | ¬ p ∣ orderOf q} ∧
    (∃ lift : Q → H, (∀ q, ¬ p ∣ orderOf q → ¬ p ∣ orderOf (lift q) ∧ π (lift q) = q) ∧
      (∀ x, ¬ p ∣ orderOf x → lift (π x) = x) ∧
      ∀ h q, ¬ p ∣ orderOf q → lift (π h * q * (π h)⁻¹) = h * lift q * h⁻¹) ∧
    (∀ x : H, ¬ p ∣ orderOf x →
      (Subgroup.centralizer ({π x} : Set Q)).comap π = Subgroup.centralizer ({x} : Set H) ∧
      Nat.card (Subgroup.centralizer ({x} : Set H)) =
        Nat.card π.ker * Nat.card (Subgroup.centralizer ({π x} : Set Q))) ∧
    Set.BijOn (ConjClasses.map π) (ConjClasses.mk '' {x : H | ¬ p ∣ orderOf x})
      (ConjClasses.mk '' {q : Q | ¬ p ∣ orderOf q}) ∧
    (∀ x : H, ¬ p ∣ orderOf x →
      Set.BijOn π (ConjClasses.mk x).carrier (ConjClasses.mk (π x)).carrier ∧
      Nat.card (ConjClasses.mk x).carrier = Nat.card (ConjClasses.mk (π x)).carrier) ∧
    ∀ U : Subgroup Q, (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → ¬ p ∣ Nat.card U →
      ∃ (Ũ : Subgroup H) (e : Ũ ≃* U),
        (Ũ : Set H) = {x | ¬ p ∣ orderOf x ∧ π x ∈ U} ∧
        (∀ a ∈ Ũ, ∀ b ∈ Ũ, a * b = b * a) ∧
        ∀ x : Ũ, (e x : Q) = π x := by
  have hpp : p.Prime := Fact.out
  have huniq := fun {x y : H} => primeRegular_eq_of_map_eq (x := x) (y := y) π hcentral hker
  have hmap : ∀ x : H, ¬ p ∣ orderOf x → ¬ p ∣ orderOf (π x) :=
    fun x hx hdvd => hx (hdvd.trans (orderOf_map_dvd π x))
  have hconj : ∀ (c : Q) (q : Q), ¬ p ∣ orderOf q → ¬ p ∣ orderOf (c * q * c⁻¹) := by
    intro c q hq
    rwa [orderOf_conj_eq]
  have hconjH : ∀ (c : H) (x : H), ¬ p ∣ orderOf x → ¬ p ∣ orderOf (c * x * c⁻¹) := by
    intro c x hx
    rwa [orderOf_conj_eq]
  have hbij : Set.BijOn π {x : H | ¬ p ∣ orderOf x} {q : Q | ¬ p ∣ orderOf q} := by
    refine ⟨fun x hx => hmap x hx, fun x hx y hy hxy => huniq hx hy hxy, ?_⟩
    intro q hq
    obtain ⟨x, hx, hxq⟩ := exists_primeRegular_lift π hπ hq
    exact ⟨x, hx, hxq⟩
  have hcent : ∀ x : H, ¬ p ∣ orderOf x →
      (Subgroup.centralizer ({π x} : Set Q)).comap π = Subgroup.centralizer ({x} : Set H) := by
    intro x hx
    ext h
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hcomm
      have heq : h * x * h⁻¹ = x := by
        apply huniq (hconjH h x hx) hx
        rw [map_mul, map_mul, map_inv, hcomm]
        group
      calc h * x = h * x * h⁻¹ * h := by group
        _ = x * h := by rw [heq]
    · intro hcomm
      rw [← map_mul, hcomm, map_mul]
  refine ⟨hbij, ?_, ?_, ?_, ?_, ?_⟩
  ·
    classical
    let lift : Q → H := fun q =>
      if hq : ¬ p ∣ orderOf q then (exists_primeRegular_lift π hπ hq).choose else 1
    have hlift : ∀ q, ¬ p ∣ orderOf q → ¬ p ∣ orderOf (lift q) ∧ π (lift q) = q := by
      intro q hq
      simp only [lift, hq, not_false_eq_true, dite_true]
      exact (exists_primeRegular_lift π hπ hq).choose_spec
    refine ⟨lift, hlift, ?_, ?_⟩
    · intro x hx
      exact huniq (hlift (π x) (hmap x hx)).1 hx (hlift (π x) (hmap x hx)).2
    · intro h q hq
      have hq' := hconj (π h) q hq
      apply huniq (hlift _ hq').1 (hconjH h (lift q) (hlift q hq).1)
      rw [(hlift _ hq').2, map_mul, map_mul, map_inv, (hlift q hq).2]
  · intro x hx
    refine ⟨hcent x hx, ?_⟩
    rw [← hcent x hx]
    exact card_comap_of_surjective π hπ _
  ·
    refine ⟨?_, ?_, ?_⟩
    · rintro c ⟨x, hx, rfl⟩
      exact ⟨π x, hmap x hx, rfl⟩
    · rintro c₁ ⟨x, hx, rfl⟩ c₂ ⟨y, hy, rfl⟩ hxy
      change ConjClasses.mk (π x) = ConjClasses.mk (π y) at hxy
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hxy ⊢
      obtain ⟨c, hc⟩ := hxy
      obtain ⟨h, rfl⟩ := hπ c
      refine ⟨h, huniq (hconjH h x hx) hy ?_⟩
      rw [map_mul, map_mul, map_inv, hc]
    · rintro c ⟨q, hq, rfl⟩
      obtain ⟨x, hx, rfl⟩ := exists_primeRegular_lift π hπ hq
      exact ⟨ConjClasses.mk x, ⟨x, hx, rfl⟩, rfl⟩
  ·
    intro x hx
    have hclass : Set.BijOn π (ConjClasses.mk x).carrier (ConjClasses.mk (π x)).carrier := by
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hy ⊢
        obtain ⟨c, hc⟩ := hy
        exact ⟨π c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩
      · intro y hy y' hy' hyy'
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
          isConj_iff] at hy hy'
        obtain ⟨c, hc⟩ := hy
        obtain ⟨c', hc'⟩ := hy'
        have hyreg : ¬ p ∣ orderOf y := by rw [← orderOf_conj_eq c y, hc]; exact hx
        have hy'reg : ¬ p ∣ orderOf y' := by rw [← orderOf_conj_eq c' y', hc']; exact hx
        exact huniq hyreg hy'reg hyy'
      · intro q hq
        rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hq
        obtain ⟨c, hc⟩ := hq
        obtain ⟨h, rfl⟩ := hπ c
        refine ⟨h⁻¹ * x * h, ?_, ?_⟩
        · rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
          exact ⟨h, by group⟩
        · rw [map_mul, map_mul, map_inv, ← hc]
          group
    exact ⟨hclass, Nat.card_congr hclass.equiv⟩
  ·
    intro U hUc hU
    have hcommute : ∀ a b : H, ¬ p ∣ orderOf a → π a ∈ U → ¬ p ∣ orderOf b → π b ∈ U →
        a * b = b * a := by
      intro a b ha haU hb hbU
      have heq : a * b * a⁻¹ = b := by
        apply huniq (hconjH a b hb) hb
        rw [map_mul, map_mul, map_inv, hUc _ haU _ hbU]
        group
      calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [heq]
    let S : Subgroup H :=
      { carrier := {x | ¬ p ∣ orderOf x ∧ π x ∈ U}
        mul_mem' := by
          rintro a b ⟨ha, haU⟩ ⟨hb, hbU⟩
          refine ⟨fun hdvd => ?_, by rw [map_mul]; exact U.mul_mem haU hbU⟩
          have hc : Commute a b := hcommute a b ha haU hb hbU
          rcases (Nat.Prime.dvd_mul hpp).mp (hdvd.trans hc.orderOf_mul_dvd_mul_orderOf) with
            h | h
          · exact ha h
          · exact hb h
        one_mem' := by
          refine ⟨?_, by rw [map_one]; exact U.one_mem⟩
          rw [orderOf_one]
          exact hpp.not_dvd_one
        inv_mem' := by
          rintro a ⟨ha, haU⟩
          refine ⟨by rwa [orderOf_inv], by rw [map_inv]; exact U.inv_mem haU⟩ }
    let f : S →* U := (π.comp S.subtype).codRestrict U (fun x => x.2.2)
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact huniq x.2.1 y.2.1 (congrArg Subtype.val hxy)
      · intro u
        have hu : ¬ p ∣ orderOf (u : Q) := fun hdvd =>
          hU (hdvd.trans (Subgroup.orderOf_dvd_natCard U u.2))
        obtain ⟨x, hx, hxu⟩ := exists_primeRegular_lift π hπ hu
        exact ⟨⟨x, hx, by rw [hxu]; exact u.2⟩, Subtype.ext hxu⟩
    refine ⟨S, MulEquiv.ofBijective f hf, rfl, ?_, fun x => rfl⟩
    rintro a ⟨ha, haU⟩ b ⟨hb, hbU⟩
    exact hcommute a b ha haU hb hbU

theorem central_p_quotient_prime_regular_elements [Finite H] [Fact p.Prime] (Z : Subgroup H)
    [Z.Normal] (hZ : Z ≤ Subgroup.center H) (hZp : IsPGroup p Z) :
    Set.BijOn (QuotientGroup.mk' Z) {x : H | ¬ p ∣ orderOf x}
      {q : H ⧸ Z | ¬ p ∣ orderOf q} ∧
    (∃ lift : H ⧸ Z → H,
      (∀ q, ¬ p ∣ orderOf q → ¬ p ∣ orderOf (lift q) ∧ QuotientGroup.mk' Z (lift q) = q) ∧
      (∀ x, ¬ p ∣ orderOf x → lift (QuotientGroup.mk' Z x) = x) ∧
      ∀ h q, ¬ p ∣ orderOf q →
        lift (QuotientGroup.mk' Z h * q * (QuotientGroup.mk' Z h)⁻¹) = h * lift q * h⁻¹) ∧
    (∀ x : H, ¬ p ∣ orderOf x →
      (Subgroup.centralizer ({QuotientGroup.mk' Z x} : Set (H ⧸ Z))).comap
          (QuotientGroup.mk' Z) = Subgroup.centralizer ({x} : Set H) ∧
      Nat.card (Subgroup.centralizer ({x} : Set H)) =
        Nat.card Z * Nat.card (Subgroup.centralizer ({QuotientGroup.mk' Z x} : Set (H ⧸ Z)))) ∧
    Set.BijOn (ConjClasses.map (QuotientGroup.mk' Z))
      (ConjClasses.mk '' {x : H | ¬ p ∣ orderOf x})
      (ConjClasses.mk '' {q : H ⧸ Z | ¬ p ∣ orderOf q}) ∧
    (∀ x : H, ¬ p ∣ orderOf x →
      Set.BijOn (QuotientGroup.mk' Z) (ConjClasses.mk x).carrier
        (ConjClasses.mk (QuotientGroup.mk' Z x)).carrier ∧
      Nat.card (ConjClasses.mk x).carrier =
        Nat.card (ConjClasses.mk (QuotientGroup.mk' Z x)).carrier) ∧
    ∀ U : Subgroup (H ⧸ Z), (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → ¬ p ∣ Nat.card U →
      ∃ (Ũ : Subgroup H) (e : Ũ ≃* U),
        (Ũ : Set H) = {x | ¬ p ∣ orderOf x ∧ QuotientGroup.mk' Z x ∈ U} ∧
        (∀ a ∈ Ũ, ∀ b ∈ Ũ, a * b = b * a) ∧
        ∀ x : Ũ, (e x : H ⧸ Z) = QuotientGroup.mk' Z x := by
  have hker : (QuotientGroup.mk' Z).ker = Z := QuotientGroup.ker_mk' Z
  have h := central_p_quotient_prime_regular_elements_of_surjective (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z) (by rw [hker]; exact hZ) (by rw [hker]; exact hZp)
  rw [hker] at h
  exact h

end CFSG.Semidihedral.Principal
