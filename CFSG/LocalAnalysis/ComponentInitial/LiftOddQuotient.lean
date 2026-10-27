module

public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralKernel

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.LieType.CentralExt
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section OddPart

variable {L : Type*} [Group L]

@[expose] def oddPart (K : Subgroup L) (hK : K ≤ center L) : Subgroup L where
  carrier := {c | c ∈ K ∧ Odd (orderOf c)}
  one_mem' := ⟨K.one_mem, by rw [orderOf_one]; exact odd_one⟩
  mul_mem' := by
    rintro c d ⟨hc, hco⟩ ⟨hd, hdo⟩
    refine ⟨K.mul_mem hc hd, Odd.of_dvd_nat (hco.mul hdo) ?_⟩
    have hcd : Commute c d := mem_center_iff.1 (hK hd) c
    exact hcd.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _)
  inv_mem' := by
    rintro c ⟨hc, hco⟩
    exact ⟨K.inv_mem hc, by rwa [orderOf_inv]⟩

variable {K : Subgroup L} {hK : K ≤ center L}

theorem mem_oddPart {c : L} : c ∈ oddPart K hK ↔ c ∈ K ∧ Odd (orderOf c) := Iff.rfl

theorem oddPart_le : oddPart K hK ≤ K := fun _ hc => hc.1

theorem oddPart_le_center : oddPart K hK ≤ center L := oddPart_le.trans hK

instance oddPart_normal : (oddPart K hK).Normal := normal_of_le_center oddPart_le_center

theorem not_two_dvd_card_oddPart [Finite L] : ¬ 2 ∣ Nat.card (oddPart K hK) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := oddPart K hK) 2 h
  have hodd := c.2.2
  rw [Subgroup.orderOf_coe, hc] at hodd
  exact Nat.not_even_iff_odd.2 hodd even_two

theorem isPGroup_map_mk_oddPart [Finite L] :
    IsPGroup 2 (K.map (QuotientGroup.mk' (oddPart K hK))) := by
  rintro ⟨_, c, hc, rfl⟩
  obtain ⟨m, n, hn, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨m, Subtype.ext ?_⟩
  change (QuotientGroup.mk' (oddPart K hK)) (c ^ 2 ^ m) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨K.pow_mem hc _, Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one ?_)⟩
  rw [← pow_mul, ← hcm, pow_orderOf_eq_one]

end OddPart

section Quotient

variable {L S : Type*} [Group L] [Group S] {π : L →* S} (hK : π.ker ≤ center L)

@[expose] noncomputable def quotientLift : L ⧸ oddPart π.ker hK →* S :=
  QuotientGroup.lift (oddPart π.ker hK) π oddPart_le

@[simp] theorem quotientLift_mk (x : L) : quotientLift hK (x : L ⧸ oddPart π.ker hK) = π x := rfl

theorem quotientLift_surjective (hπ : Function.Surjective π) :
    Function.Surjective (quotientLift hK) := by
  intro s
  obtain ⟨x, rfl⟩ := hπ s
  exact ⟨x, rfl⟩

theorem ker_quotientLift :
    (quotientLift hK).ker = π.ker.map (QuotientGroup.mk' (oddPart π.ker hK)) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  constructor
  · intro hy
    exact ⟨x, hy, rfl⟩
  · rintro ⟨x', hx', hxx⟩
    rw [MonoidHom.mem_ker, ← hxx]
    exact hx'

theorem ker_quotientLift_le_center : (quotientLift hK).ker ≤ center (L ⧸ oddPart π.ker hK) := by
  rw [ker_quotientLift]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_center_iff.2 fun y => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change ((y * x : L) : L ⧸ oddPart π.ker hK) = ((x * y : L) : L ⧸ oddPart π.ker hK)
  rw [mem_center_iff.1 (hK hx) y]

theorem isPGroup_ker_quotientLift [Finite L] : IsPGroup 2 (quotientLift hK).ker := by
  rw [ker_quotientLift]
  exact isPGroup_map_mk_oddPart

theorem ker_mk_oddPart_le_center :
    (QuotientGroup.mk' (oddPart π.ker hK)).ker ≤ center L := by
  rw [QuotientGroup.ker_mk']
  exact oddPart_le_center

theorem not_two_dvd_card_ker_mk_oddPart [Finite L] :
    ¬ 2 ∣ Nat.card (QuotientGroup.mk' (oddPart π.ker hK)).ker := by
  rw [QuotientGroup.ker_mk']
  exact not_two_dvd_card_oddPart

variable {a : MulAut L} {α : MulAut S}

theorem mem_ker_iff_apply (hcomm : ∀ x, π (a x) = α (π x)) {x : L} :
    a x ∈ π.ker ↔ x ∈ π.ker := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hcomm, map_eq_one_iff _ α.injective]

theorem map_oddPart_eq (hcomm : ∀ x, π (a x) = α (π x)) :
    (oddPart π.ker hK).map a.toMonoidHom = oddPart π.ker hK := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxo⟩, rfl⟩
    refine ⟨(mem_ker_iff_apply hcomm).2 hx, ?_⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  · rintro ⟨hy, hyo⟩
    refine ⟨a.symm y, ⟨?_, ?_⟩, a.apply_symm_apply y⟩
    · rw [← mem_ker_iff_apply hcomm, a.apply_symm_apply]
      exact hy
    · rwa [MulEquiv.orderOf_eq]

@[expose] noncomputable def quotientAut (hcomm : ∀ x, π (a x) = α (π x)) :
    MulAut (L ⧸ oddPart π.ker hK) :=
  QuotientGroup.congr (oddPart π.ker hK) (oddPart π.ker hK) a (map_oddPart_eq hK hcomm)

@[simp] theorem quotientAut_mk (hcomm : ∀ x, π (a x) = α (π x)) (x : L) :
    quotientAut hK hcomm (x : L ⧸ oddPart π.ker hK) = ((a x : L) : L ⧸ oddPart π.ker hK) :=
  rfl

theorem quotientLift_quotientAut (hcomm : ∀ x, π (a x) = α (π x))
    (y : L ⧸ oddPart π.ker hK) :
    quotientLift hK (quotientAut hK hcomm y) = α (quotientLift hK y) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact hcomm x

end Quotient

section Lifts

variable {L S : Type*} [Group L] [Group S] [Finite L] {π : L →* S}

theorem quotientAut_sl2Lift {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) {a : MulAut L} {α : MulAut S}
    (hcomm : ∀ x, π (a x) = α (π x)) (ρ : SpecialLinearGroup (Fin 2) k →* S)
    (hfix : ∀ h, α (ρ h) = ρ h) (h : SpecialLinearGroup (Fin 2) k) :
    quotientAut hK hcomm (sl2Lift (quotientLift hK) ρ h) = sl2Lift (quotientLift hK) ρ h := by
  have hlift : (quotientLift hK).comp
      ((quotientAut hK hcomm).toMonoidHom.comp (sl2Lift (quotientLift hK) ρ)) = ρ := by
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, quotientLift_quotientAut]
    rw [map_sl2Lift hk (quotientLift_surjective hK hπ) (ker_quotientLift_le_center hK)
      (isPGroup_ker_quotientLift hK) ρ g, hfix]
  exact DFunLike.congr_fun
    (eq_sl2Lift hk (ker_quotientLift_le_center hK) (isPGroup_ker_quotientLift hK) hlift) h

theorem exists_fixed_two_lift (hK : π.ker ≤ center L) {a : MulAut L} {α : MulAut S}
    (hcomm : ∀ x, π (a x) = α (π x)) {y : L ⧸ oddPart π.ker hK}
    (hy : ∃ n : ℕ, orderOf y = 2 ^ n) (hfix : quotientAut hK hcomm y = y) :
    ∃ x : L, (x : L ⧸ oddPart π.ker hK) = y ∧ (∃ n : ℕ, orderOf x = 2 ^ n) ∧ a x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Function.Surjective (QuotientGroup.mk' (oddPart π.ker hK)) :=
    QuotientGroup.mk'_surjective _
  have hC := not_two_dvd_card_ker_mk_oddPart hK
  have hx := map_pLift hq hC hy
  have hxo := orderOf_pLift hq hC hy
  refine ⟨pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) y, hx, hxo, ?_⟩
  refine eq_of_pElement (ker_mk_oddPart_le_center hK) hC ?_ ?_ hxo
  · change ((a _ : L) : L ⧸ oddPart π.ker hK) = _
    rw [← quotientAut_mk hK hcomm]
    change quotientAut hK hcomm (QuotientGroup.mk' _ _) = QuotientGroup.mk' _ _
    rw [hx, hfix]
  · obtain ⟨n, hn⟩ := hxo
    exact ⟨n, by rw [MulEquiv.orderOf_eq]; exact hn⟩

theorem odd_rank_one_fixed_involution_lifts_through_central_kernel {E G : Type*} [Group E]
    [Group G] [Finite E] [Finite G] {π : E →* G} (hπ : Function.Surjective π)
    (hC : π.ker ≤ center E) (a : MulAut E) (b : MulAut G) (hcomm : ∀ x, π (a x) = b (π x))
    {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (ρ : SpecialLinearGroup (Fin 2) k →* G) (hfix : ∀ s ∈ ρ.range, b s = s)
    (hρ : ρ (-1) ≠ 1) :
    ∃ x ∈ fixedSubgroup a, orderOf x = 2 ∧ π x = ρ (-1) ∧ x ∉ π.ker ∧
      (π.ker = center E → x ∉ center E) := by
  have hfix' : ∀ h, b (ρ h) = ρ h := fun h => hfix _ ⟨h, rfl⟩
  set y := sl2Lift (quotientLift hC) ρ (-1)
  have hπy : quotientLift hC y = ρ (-1) :=
    map_sl2Lift hk (quotientLift_surjective hC hπ) (ker_quotientLift_le_center hC)
      (isPGroup_ker_quotientLift hC) ρ (-1)
  have hy1 : y ≠ 1 := fun h => hρ (by rw [← hπy, h, map_one])
  have hy2 : y ^ 2 = 1 := by
    rw [← map_pow, sq, neg_one_mul, neg_neg, map_one]
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨x, hxy, hxo, hax⟩ := exists_fixed_two_lift hC hcomm ⟨1, by rw [hyo, pow_one]⟩
    (quotientAut_sl2Lift hk hπ hC hcomm ρ hfix' (-1))
  have hπx : π x = ρ (-1) := by rw [← quotientLift_mk hC, hxy, hπy]
  have hx1 : x ≠ 1 := fun h => hρ (by rw [← hπx, h, map_one])
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨n, hn⟩ := hxo
    have hk2 : x ^ 2 ∈ (QuotientGroup.mk' (oddPart π.ker hC)).ker := by
      rw [MonoidHom.mem_ker, map_pow, QuotientGroup.mk'_apply, hxy, hy2]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine eq_one_of_mem_ker (not_two_dvd_card_ker_mk_oddPart hC) hk2 (n := n) ?_
    rw [← pow_mul, mul_comm, pow_mul, ← hn, pow_orderOf_eq_one, one_pow]
  have hxK : x ∉ π.ker := fun h => hρ (by rw [← hπx]; exact h)
  exact ⟨x, hax, orderOf_eq_prime hx2 hx1, hπx, hxK, fun hZ => hZ ▸ hxK⟩

theorem fixed_odd_SL2_even_image_lifts_through_full_center [Finite S]
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) (a : MulAut L) (α : MulAut S)
    (hcomm : ∀ x, π (a x) = α (π x)) {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (ρ : SpecialLinearGroup (Fin 2) k →* S) (heven : Even (Nat.card ρ.range))
    (hfix : ∀ s ∈ ρ.range, α s = s) :
    (∃ x ∈ fixedSubgroup a, (∃ n : ℕ, orderOf x = 2 ^ n) ∧ x ∉ π.ker) ∧
      (∀ R : Sylow 2 (fixedSubgroup a),
        ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker) ∧
      (π.ker = center L → ∀ R : Sylow 2 (fixedSubgroup a),
        ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix' : ∀ h, α (ρ h) = ρ h := fun h => hfix _ ⟨h, rfl⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ρ.range) 2 (even_iff_two_dvd.1 heven)
  obtain ⟨g, hg⟩ := s.2
  have hgs : orderOf (ρ g) = 2 := by rw [hg, Subgroup.orderOf_coe, hs]
  obtain ⟨m, n, hn, hgo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set h := g ^ n
  have hh : h ^ 2 ^ m = 1 := by
    rw [← pow_mul, mul_comm, ← hgo, pow_orderOf_eq_one]
  have hρh : ρ h = ρ g := by
    obtain ⟨j, rfl⟩ := hn
    have h2 : ρ g ^ 2 = 1 := by
      have := pow_orderOf_eq_one (ρ g)
      rwa [hgs] at this
    rw [map_pow, pow_succ, pow_mul, h2, one_pow, one_mul]
  have hρh1 : ρ h ≠ 1 := by
    rw [hρh]
    intro h1
    rw [h1, orderOf_one] at hgs
    exact absurd hgs (by norm_num)
  set y := sl2Lift (quotientLift hK) ρ h
  have hπy : quotientLift hK y = ρ h :=
    map_sl2Lift hk (quotientLift_surjective hK hπ) (ker_quotientLift_le_center hK)
      (isPGroup_ker_quotientLift hK) ρ h
  have hyo : ∃ n : ℕ, orderOf y = 2 ^ n := by
    have hdvd : orderOf y ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hh, map_one])
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨i, hi⟩
  obtain ⟨x, hxy, hxo, hax⟩ := exists_fixed_two_lift hK hcomm hyo
    (quotientAut_sl2Lift hk hπ hK hcomm ρ hfix' h)
  have hπx : π x = ρ h := by rw [← quotientLift_mk hK, hxy, hπy]
  have hxK : x ∉ π.ker := fun hx => hρh1 (by rw [← hπx]; exact hx)
  refine ⟨⟨x, hax, hxo, hxK⟩, fun R => not_sylow_map_le_of_mem hK hax hxo hxK R, ?_⟩
  intro hZ R
  rw [← hZ]
  exact not_sylow_map_le_of_mem hK hax hxo hxK R

end Lifts

section FixedQuotient

variable {L S : Type*} [Group L] [Group S] [Finite L] {π : L →* S}

theorem mem_sylow_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : (P : Subgroup G).Normal) {g : G} (hg : ∃ n : ℕ, orderOf g = p ^ n) :
    g ∈ (P : Subgroup G) := by
  obtain ⟨n, hn⟩ := hg
  have hp : IsPGroup p (zpowers g) := by
    rw [IsPGroup.iff_card]
    exact ⟨n, by rw [Nat.card_zpowers, hn]⟩
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have := Sylow.unique_of_normal P hP
  rw [Subsingleton.elim Q P] at hQ
  exact hQ (mem_zpowers g)

theorem pLift_mem_ker (hK : π.ker ≤ center L) {z : L ⧸ oddPart π.ker hK}
    (hz : z ∈ (quotientLift hK).ker) (hzo : ∃ n : ℕ, orderOf z = 2 ^ n) :
    pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) z ∈ π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [MonoidHom.mem_ker, ← quotientLift_mk hK]
  change quotientLift hK (QuotientGroup.mk' _ _) = 1
  rw [map_pLift (QuotientGroup.mk'_surjective _) (not_two_dvd_card_ker_mk_oddPart hK) hzo]
  exact hz

theorem mk_pLift (hK : π.ker ≤ center L) {z : L ⧸ oddPart π.ker hK}
    (hzo : ∃ n : ℕ, orderOf z = 2 ^ n) :
    ((pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) z : L) : L ⧸ oddPart π.ker hK) = z :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  map_pLift (QuotientGroup.mk'_surjective _) (not_two_dvd_card_ker_mk_oddPart hK) hzo

theorem orderOf_pLift_mk (hK : π.ker ≤ center L) {z : L ⧸ oddPart π.ker hK}
    (hzo : ∃ n : ℕ, orderOf z = 2 ^ n) :
    ∃ n : ℕ, orderOf (pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) z) = 2 ^ n :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_pLift (QuotientGroup.mk'_surjective _) (not_two_dvd_card_ker_mk_oddPart hK) hzo

theorem pLift_mem_sylow (hK : π.ker ≤ center L) (K₂ : Sylow 2 π.ker)
    {z : L ⧸ oddPart π.ker hK} (hz : z ∈ (quotientLift hK).ker)
    (hzo : ∃ n : ℕ, orderOf z = 2 ^ n) :
    (⟨_, pLift_mem_ker hK hz hzo⟩ : π.ker) ∈ (K₂ : Subgroup π.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (K₂ : Subgroup π.ker).Normal := by
    refine ⟨fun x _ g => ?_⟩
    have hcomm : g * x = x * g := Subtype.ext (mem_center_iff.1 (hK x.2) g)
    rwa [hcomm, mul_inv_cancel_right]
  refine mem_sylow_of_normal K₂ hnorm ?_
  obtain ⟨n, hn⟩ := orderOf_pLift_mk hK hzo
  exact ⟨n, by rw [← Subgroup.orderOf_coe]; exact hn⟩

theorem fixed_quotient_two_subgroup_lifts_past_fixed_central_two_rank [Finite S]
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) (K₂ : Sylow 2 π.ker)
    (a : MulAut L) (α : MulAut S) (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    (hK₂ : ∀ z ∈ (K₂ : Subgroup π.ker), a (z : L) = z) {V : Subgroup S} (hV : IsPGroup 2 V)
    (hVfix : ∀ v ∈ V, α v = v)
    (hVT : Nat.card {z : (K₂ : Subgroup π.ker) // z ^ 2 = 1} < Nat.card V) :
    (∃ x ∈ fixedSubgroup a, (∃ n : ℕ, orderOf x = 2 ^ n) ∧ π x ∈ V ∧ π x ≠ 1) ∧
      (∀ x ∈ fixedSubgroup a, π x ∈ V → π x ≠ 1 → x ∉ π.ker) ∧
      ∀ R : Sylow 2 (fixedSubgroup a),
        ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lb := L ⧸ oddPart π.ker hK
  set πb := quotientLift hK
  set ab := quotientAut hK hcomm
  have hab : ∀ y, ab (ab y) = y := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    change ((a (a x) : L) : Lb) = x
    rw [ha]
  have hkerc : πb.ker ≤ center Lb := ker_quotientLift_le_center hK
  have hker2 : IsPGroup 2 πb.ker := isPGroup_ker_quotientLift hK
  have hkero : ∀ z ∈ πb.ker, ∃ n : ℕ, orderOf z = 2 ^ n := fun z hz => by
    obtain ⟨n, hn⟩ := hker2 ⟨z, hz⟩
    exact exists_orderOf_eq_pow_of_pow_eq_one (congrArg Subtype.val hn)
  have habK : ∀ z ∈ πb.ker, ab z = z := fun z hz => by
    rw [← mk_pLift hK (hkero z hz), quotientAut_mk]
    exact congrArg _ (hK₂ _ (pLift_mem_sylow hK K₂ hz (hkero z hz)))
  set D := V.comap πb
  have hδker : ∀ y ∈ D, y⁻¹ * ab y ∈ πb.ker := fun y hy => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, quotientLift_quotientAut, hVfix _ hy,
      inv_mul_cancel]
  let δ : D →* Lb :=
    { toFun := fun y => (y : Lb)⁻¹ * ab y
      map_one' := by simp
      map_mul' := fun y z => by
        have hc := mem_center_iff.1 (hkerc (hδker y y.2))
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        calc (z : Lb)⁻¹ * (y : Lb)⁻¹ * (ab y * ab z) = (z : Lb)⁻¹ * ((y : Lb)⁻¹ * ab y) * ab z := by
              simp only [mul_assoc]
          _ = ((y : Lb)⁻¹ * ab y) * (z : Lb)⁻¹ * ab z := by rw [← hc]
          _ = (y : Lb)⁻¹ * ab y * ((z : Lb)⁻¹ * ab z) := by simp only [mul_assoc] }
  have hδ : ∀ y : D, δ y = (y : Lb)⁻¹ * ab y := fun _ => rfl
  have hδ2 : ∀ y : D, δ y ^ 2 = 1 := fun y => by
    have hd : δ y ∈ πb.ker := hδker y y.2
    have h1 : ab y = y * δ y := by rw [hδ, mul_inv_cancel_left]
    have h2 : ab (ab y) = y * (δ y * δ y) := by
      rw [h1, map_mul, habK (δ y) hd, h1, mul_assoc]
    rw [hab] at h2
    rw [sq]
    exact mul_eq_left.1 h2.symm
  let ψ : D →* S := πb.comp D.subtype
  have hψδ : ψ.ker ≤ δ.ker := fun y hy => by
    rw [MonoidHom.mem_ker, hδ, habK (y : Lb) hy, inv_mul_cancel]
  have hexists : ∃ y ∈ D, ab y = y ∧ πb y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hδψ : δ.ker ≤ ψ.ker := fun y hy => by
      have hfix : ab y = y := by
        rw [MonoidHom.mem_ker, hδ, inv_mul_eq_one] at hy
        exact hy.symm
      exact hno y y.2 hfix
    have hkereq : δ.ker = ψ.ker := le_antisymm hδψ hψδ
    have hcardD1 := Subgroup.card_ker_mul_card_range δ
    have hcardD2 := Subgroup.card_ker_mul_card_range ψ
    have hrangeψ : Nat.card ψ.range = Nat.card V := by
      have : ψ.range = V := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
        exact Subgroup.map_comap_eq_self_of_surjective (quotientLift_surjective hK hπ) V
      rw [this]
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have hrangeδ : Nat.card δ.range = Nat.card V := by
      rw [hkereq] at hcardD1
      rw [← hrangeψ]
      exact Nat.eq_of_mul_eq_mul_left hpos (hcardD1.trans hcardD2.symm)
    have hinj : Nat.card δ.range ≤ Nat.card {z : (K₂ : Subgroup π.ker) // z ^ 2 = 1} := by
      have hw : ∀ w : δ.range, (w : Lb) ∈ πb.ker ∧ (w : Lb) ^ 2 = 1 := by
        rintro ⟨_, y, rfl⟩
        exact ⟨hδker y y.2, hδ2 y⟩
      have hwo : ∀ w : δ.range, ∃ n : ℕ, orderOf (w : Lb) = 2 ^ n := fun w =>
        exists_orderOf_eq_pow_of_pow_eq_one (n := 1) (by rw [pow_one]; exact (hw w).2)
      have hsq : ∀ w : δ.range,
          (pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) (w : Lb)) ^ 2 = 1 := fun w => by
        obtain ⟨n, hn⟩ := orderOf_pLift_mk hK (hwo w)
        refine eq_one_of_mem_ker (not_two_dvd_card_ker_mk_oddPart hK) (n := n) ?_ ?_
        · rw [MonoidHom.mem_ker, map_pow]
          change ((pLift 2 _ (w : Lb) : L) : Lb) ^ 2 = 1
          rw [mk_pLift hK (hwo w)]
          exact (hw w).2
        · rw [← pow_mul, mul_comm, pow_mul, ← hn, pow_orderOf_eq_one, one_pow]
      let g : δ.range → {z : (K₂ : Subgroup π.ker) // z ^ 2 = 1} := fun w =>
        ⟨⟨⟨_, pLift_mem_ker hK (hw w).1 (hwo w)⟩, pLift_mem_sylow hK K₂ (hw w).1 (hwo w)⟩,
          Subtype.ext (Subtype.ext (hsq w))⟩
      refine Nat.card_le_card_of_injective g fun w₁ w₂ h => ?_
      have h' : pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) (w₁ : Lb) =
          pLift 2 (QuotientGroup.mk' (oddPart π.ker hK)) (w₂ : Lb) :=
        congrArg (fun z : {z : (K₂ : Subgroup π.ker) // z ^ 2 = 1} => ((z : π.ker) : L)) h
      have h'' := congrArg (fun x : L => (x : Lb)) h'
      simp only [mk_pLift hK (hwo _)] at h''
      exact Subtype.ext h''
    omega
  obtain ⟨y, hyD, hyfix, hy1⟩ := hexists
  have hyo : ∃ n : ℕ, orderOf y = 2 ^ n := by
    obtain ⟨m, hm⟩ := hV ⟨πb y, hyD⟩
    have hm' : y ^ 2 ^ m ∈ πb.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hm
    obtain ⟨n, hn⟩ := hker2 ⟨_, hm'⟩
    refine exists_orderOf_eq_pow_of_pow_eq_one (n := m + n) ?_
    rw [pow_add, pow_mul]
    exact congrArg Subtype.val hn
  obtain ⟨x, hxy, hxo, hax⟩ := exists_fixed_two_lift hK hcomm hyo hyfix
  have hπx : π x = πb y := by rw [← quotientLift_mk hK, hxy]
  have hxK : x ∉ π.ker := fun h => hy1 (by rw [← hπx]; exact h)
  refine ⟨⟨x, hax, hxo, hπx ▸ hyD, hπx ▸ hy1⟩, fun x' _ _ hx1 hxK' => hx1 hxK', fun R => ?_⟩
  exact not_sylow_map_le_of_mem hK hax hxo hxK R

theorem fixed_quotient_two_subgroup_lifts_of_cyclic_of_four [Finite S]
    (hπ : Function.Surjective π) (hK : π.ker ≤ center L) (K₂ : Sylow 2 π.ker)
    (a : MulAut L) (α : MulAut S) (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    (hK₂ : ∀ z ∈ (K₂ : Subgroup π.ker), a (z : L) = z) (hcyc : IsCyclic (K₂ : Subgroup π.ker))
    {V : Subgroup S} (hV : CFSG.Assembly.IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hVfix : ∀ v ∈ V, α v = v) :
    (∃ x ∈ fixedSubgroup a, (∃ n : ℕ, orderOf x = 2 ^ n) ∧ π x ∈ V ∧ π x ≠ 1) ∧
      (∀ x ∈ fixedSubgroup a, π x ∈ V → π x ≠ 1 → x ∉ π.ker) ∧
      ∀ R : Sylow 2 (fixedSubgroup a),
        ¬ (R : Subgroup (fixedSubgroup a)).map (fixedSubgroup a).subtype ≤ π.ker := by
  classical
  have hVp : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact hV.2 g g.2)⟩
  have : Fintype (K₂ : Subgroup π.ker) := Fintype.ofFinite _
  have hT : Nat.card {z : (K₂ : Subgroup π.ker) // z ^ 2 = 1} ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le two_pos
  exact fixed_quotient_two_subgroup_lifts_past_fixed_central_two_rank hπ hK K₂ a α ha hcomm hK₂
    hVp hVfix (by omega)

end FixedQuotient

end CFSG.LocalAnalysis.ComponentInitial
