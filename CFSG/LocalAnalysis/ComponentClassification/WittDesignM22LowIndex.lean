module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizer
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22PointStabilizer
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import Certificates.Certificate2195
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexInputs
public import Certificates.Certificate2033
public import Certificates.Certificate3029

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction
open scoped Pointwise

theorem index_modEq_relIndex_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) :
    H.index ≡ H.relIndex (Subgroup.normalizer (P : Set G)) [MOD p] := by
  set N := Subgroup.normalizer (P : Set G)
  have hmod := P.isPGroup'.card_modEq_card_fixedPoints (G ⧸ H)
  have hfix : fixedPoints (P : Subgroup G) (G ⧸ H) = orbit N ((1 : G) : G ⧸ H) := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro hx
      have hconj : ∀ q ∈ (P : Subgroup G), g⁻¹ * q * g ∈ H := by
        intro q hq
        have := hx ⟨q⁻¹, (P : Subgroup G).inv_mem hq⟩
        rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at this
        simpa [mul_assoc] using this
      have hle : ((g⁻¹ • P : Sylow p G) : Subgroup G) ≤ H := by
        intro y hy
        have hy' : y ∈ MulAut.conj g⁻¹ • ((P : Subgroup G) : Set G) := hy
        obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.1 hy'
        simpa [MulAut.smul_def] using hconj q hq
      obtain ⟨h, hh⟩ := exists_smul_eq H ((g⁻¹ • P).subtype hle) (P.subtype hPH)
      simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
      have hn : (h : G) * g⁻¹ ∈ N :=
        Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh)
      refine ⟨⟨((h : G) * g⁻¹)⁻¹, N.inv_mem hn⟩, ?_⟩
      change (((h : G) * g⁻¹)⁻¹ : G) • ((1 : G) : G ⧸ H) = (g : G ⧸ H)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simp
    · rintro ⟨n, hn⟩ q
      have hn' : ((n : G) : G ⧸ H) = (g : G ⧸ H) := by
        rw [← hn]
        change _ = (n : G) • ((1 : G) : G ⧸ H)
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      rw [← hn']
      change (q : G) • ((n : G) : G ⧸ H) = ((n : G) : G ⧸ H)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      have hn := (Subgroup.mem_normalizer_iff.1 (N.inv_mem n.2)) (q : G)⁻¹
      have hq : (q : G)⁻¹ ∈ (P : Subgroup G) := (P : Subgroup G).inv_mem q.2
      have := hPH (hn.1 hq)
      simpa [mul_assoc] using this
  have hstab : stabilizer N ((1 : G) : G ⧸ H) = H.subgroupOf N := by
    ext n
    rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def,
      MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simp
  rw [Subgroup.index, Subgroup.relIndex, ← hstab, index_stabilizer, ← Nat.card_coe_set_eq,
    ← hfix]
  exact hmod

theorem card_modEq_card_filter_fixed {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (O : Finset α) (hO : ∀ g : G, ∀ x ∈ O, g • x ∈ O)
    [DecidablePred fun x : α => ∀ g : G, g • x = x] :
    O.card ≡ (O.filter fun x => ∀ g : G, g • x = x).card [MOD p] := by
  let S : SubMulAction G α := ⟨(O : Set α), fun g x hx => hO g x hx⟩
  have : Finite S := Finite.of_injective (fun x : S => (⟨x.1, x.2⟩ : (O : Set α)))
    (fun x y e => Subtype.ext (congrArg Subtype.val e))
  have h := hG.card_modEq_card_fixedPoints S
  have h1 : Nat.card S = O.card := by
    rw [← Nat.card_eq_finsetCard]
    rfl
  have h2 : Nat.card (fixedPoints G S) = (O.filter fun x => ∀ g : G, g • x = x).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, Finset.mem_filter.2 ⟨x.1.2, fun g => ?_⟩⟩,
      fun x => ⟨⟨x.1, (Finset.mem_filter.1 x.2).1⟩, fun g => ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · exact congrArg Subtype.val (x.2 g)
    · exact Subtype.ext ((Finset.mem_filter.1 x.2).2 g)
  rw [h1, h2] at h
  exact h

theorem mem_normalizer_zpowers_iff {G : Type*} [Group G] [Finite G] (z g : G) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) ↔ g * z * g⁻¹ ∈ Subgroup.zpowers z := by
  constructor
  · intro hg
    exact (Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_zpowers z)
  · intro h
    have hmap : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [MonoidHom.map_zpowers]
        exact (Subgroup.zpowers_le).2 h
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hmap] at hx
      obtain ⟨y, hy, e⟩ := hx
      have : y = x := (MulAut.conj g).injective e
      exact this ▸ hy

theorem factorization_prime_mul {p m : ℕ} (hp : p.Prime) (hm : ¬p ∣ m) :
    (p * m).factorization p = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm]

@[expose] def sylowOfCard {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
    (hG : Nat.card G = p * m) (hm : ¬p ∣ m) (K : Subgroup G) (hK : Nat.card K = p) : Sylow p G :=
  Sylow.ofCard K (by rw [hG, factorization_prime_mul hp.out hm, pow_one, hK])

theorem table_facts :
    (∀ x, ofTable zTab x = (CFSG.Sporadic.Mathieu.m22gA * CFSG.Sporadic.Mathieu.m22gB) x) ∧
    (∀ j : Fin 11, ∀ x, ofTable zPowTabs[j.val]! x = (ofTable zTab)^[j] x) ∧
    (∀ j : Fin 5, ∀ x, ofTable wPowTabs[j.val]! x = (ofTable wTab)^[j] x) ∧
    (∀ j : Fin 7, ∀ x, ofTable yPowTabs[j.val]! x = (ofTable yTab)^[j] x) ∧
    (∀ x, (ofTable wTab)^[5] x = x) ∧ ofTable wTab 0 ≠ 0 ∧
    (∀ x, (ofTable yTab)^[7] x = x) ∧ ofTable yTab 0 ≠ 0 ∧
    (∀ x, ofTable wTab (ofTable zTab x) = ofTable zPowTabs[9]! (ofTable wTab x)) ∧
    (∀ x, ofTable cTab (ofTable wTab x) = ofTable wPowTabs[2]! (ofTable cTab x)) :=
  Certificates.certificate2033.1

theorem count_tables : m22Count (fun g => ∀ x, g x = ofTable wTab x) = 1 ∧
    m22Count (fun g => ∀ x, g x = ofTable cTab x) = 1 ∧
    m22Count (fun g => ∀ x, g x = ofTable yTab x) = 1 :=
  Certificates.certificate2033.2.1

theorem count_normalizers :
    m22Count (fun f => ∃ j : Fin 11, ∀ x, f (ofTable zTab x) = ofTable zPowTabs[j.val]! (f x)) =
      55 ∧
    m22Count (fun f => ∃ j : Fin 5, ∀ x, f (ofTable wTab x) = ofTable wPowTabs[j.val]! (f x)) =
      20 ∧
    m22Count (fun f => ∃ j : Fin 7, ∀ x, f (ofTable yTab x) = ofTable yPowTabs[j.val]! (f x)) =
      21 :=
  Certificates.certificate2033.2.2

theorem exists_of_table {t : Array ℕ} (h : m22Count (fun g => ∀ x, g x = ofTable t x) = 1) :
    ∃ w : M22, ⇑(w : Equiv.Perm (Fin 22)) = ofTable t := by
  obtain ⟨w, hw⟩ := exists_m22_of_count _ (by rw [h]; norm_num)
  exact ⟨w, funext hw⟩

@[expose] def z₀ : M22 := CFSG.Sporadic.Mathieu.m22a * CFSG.Sporadic.Mathieu.m22b

@[expose] def w₁ : M22 := (exists_of_table count_tables.1).choose

@[expose] def c₄ : M22 := (exists_of_table count_tables.2.1).choose

@[expose] def y₀ : M22 := (exists_of_table count_tables.2.2).choose

theorem coe_z₀ : ⇑(z₀ : Equiv.Perm (Fin 22)) = ofTable zTab :=
  funext fun x => (table_facts.1 x).symm

theorem coe_w₁ : ⇑(w₁ : Equiv.Perm (Fin 22)) = ofTable wTab :=
  (exists_of_table count_tables.1).choose_spec

theorem coe_c₄ : ⇑(c₄ : Equiv.Perm (Fin 22)) = ofTable cTab :=
  (exists_of_table count_tables.2.1).choose_spec

theorem coe_y₀ : ⇑(y₀ : Equiv.Perm (Fin 22)) = ofTable yTab :=
  (exists_of_table count_tables.2.2).choose_spec

theorem coe_pow_apply (g : M22) (j : ℕ) (x : Fin 22) :
    ((g ^ j : M22) : Equiv.Perm (Fin 22)) x = (⇑(g : Equiv.Perm (Fin 22)))^[j] x := by
  rw [Subgroup.coe_pow, Equiv.Perm.coe_pow]

theorem orderOf_eq_of_table {g : M22} {t : Array ℕ} {p : ℕ} [hp : Fact p.Prime]
    (hg : ⇑(g : Equiv.Perm (Fin 22)) = ofTable t) (h1 : ∀ x, (ofTable t)^[p] x = x)
    (h2 : ofTable t 0 ≠ 0) : orderOf g = p := by
  refine orderOf_eq_prime ?_ ?_
  · refine Subtype.ext (Equiv.ext fun x => ?_)
    rw [coe_pow_apply, hg]
    exact h1 x
  · intro e
    have := congrArg (fun σ : M22 => (σ : Equiv.Perm (Fin 22)) 0) e
    simp only [hg] at this
    exact h2 this

theorem orderOf_z₀ : orderOf z₀ = 11 := CFSG.Sporadic.Schreier.at_m22_image_pair_count.2.2.1

theorem orderOf_w₁ : orderOf w₁ = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_of_table coe_w₁ table_facts.2.2.2.2.1 table_facts.2.2.2.2.2.1

theorem orderOf_y₀ : orderOf y₀ = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_eq_of_table coe_y₀ table_facts.2.2.2.2.2.2.1 table_facts.2.2.2.2.2.2.2.1

theorem mem_normalizer_iff_tables {z : M22} {n : ℕ} (hz : orderOf z = n) {zt : Array ℕ}
    (hzt : ⇑(z : Equiv.Perm (Fin 22)) = ofTable zt) {T : Array (Array ℕ)}
    (hT : ∀ j : Fin n, ∀ x, ofTable T[j.val]! x = (ofTable zt)^[j] x) (g : M22) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set M22) ↔
      ∃ j : Fin n, ∀ x, (g : Equiv.Perm (Fin 22)) (ofTable zt x) =
        ofTable T[j.val]! ((g : Equiv.Perm (Fin 22)) x) := by
  rw [mem_normalizer_zpowers_iff, mem_zpowers_iff_mem_range_orderOf, hz, Finset.mem_image]
  have key : ∀ j : ℕ, z ^ j = g * z * g⁻¹ ↔ ∀ x, (g : Equiv.Perm (Fin 22)) (ofTable zt x) =
      (ofTable zt)^[j] ((g : Equiv.Perm (Fin 22)) x) := by
    intro j
    rw [eq_mul_inv_iff_mul_eq, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, Equiv.ext_iff]
    simp only [Equiv.Perm.mul_apply, Subgroup.coe_pow, Equiv.Perm.coe_pow, hzt]
    exact ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩
  constructor
  · rintro ⟨j, hj, e⟩
    rw [Finset.mem_range] at hj
    refine ⟨⟨j, hj⟩, fun x => ?_⟩
    rw [hT, (key j).1 e x]
  · rintro ⟨j, hj⟩
    refine ⟨j, Finset.mem_range.2 j.2, (key j).2 fun x => ?_⟩
    rw [hj x, hT]

theorem card_normalizer_z₀ :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers z₀ : Set M22)) = 55 := by
  rw [← count_normalizers.1, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    mem_normalizer_iff_tables orderOf_z₀ coe_z₀ table_facts.2.1 g)

theorem card_normalizer_w₁ :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers w₁ : Set M22)) = 20 := by
  rw [← count_normalizers.2.1, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    mem_normalizer_iff_tables orderOf_w₁ coe_w₁ table_facts.2.2.1 g)

theorem card_normalizer_y₀ :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers y₀ : Set M22)) = 21 := by
  rw [← count_normalizers.2.2, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    mem_normalizer_iff_tables orderOf_y₀ coe_y₀ table_facts.2.2.2.1 g)

theorem card_normalizer_sylow {p : ℕ} [Fact p.Prime] (P Q : Sylow p M22) :
    Nat.card (Subgroup.normalizer (P : Set M22)) =
      Nat.card (Subgroup.normalizer (Q : Set M22)) := by
  have hP := Subgroup.card_mul_index (Subgroup.normalizer (P : Set M22))
  have hQ := Subgroup.card_mul_index (Subgroup.normalizer (Q : Set M22))
  rw [← P.card_eq_index_normalizer] at hP
  rw [← Q.card_eq_index_normalizer] at hQ
  have hpos : 0 < Nat.card (Sylow p M22) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (hP.trans hQ.symm)

theorem card_M22' : Nat.card M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22

@[expose] def sylowZpowers {p m : ℕ} [Fact p.Prime] (hm : 443520 = p * m) (hpm : ¬p ∣ m)
    (x : M22) (hx : orderOf x = p) : Sylow p M22 :=
  sylowOfCard (card_M22'.trans hm) hpm (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx])

theorem coe_sylowZpowers {p m : ℕ} [Fact p.Prime] (hm : 443520 = p * m) (hpm : ¬p ∣ m)
    (x : M22) (hx : orderOf x = p) :
    (sylowZpowers hm hpm x hx : Subgroup M22) = Subgroup.zpowers x := rfl

theorem exists_sylow_le_of_not_dvd {p m : ℕ} [hp : Fact p.Prime] (hm : 443520 = p * m)
    (hpm : ¬p ∣ m) (H : Subgroup M22) (hk : ¬p ∣ H.index) :
    ∃ x : M22, x ∈ H ∧ orderOf x = p ∧
      H.index ≡ H.relIndex (Subgroup.normalizer (Subgroup.zpowers x : Set M22)) [MOD p] := by
  have hcard := Subgroup.card_mul_index H
  rw [card_M22', hm] at hcard
  have hdvd : p ∣ Nat.card H := by
    have : p ∣ Nat.card H * H.index := hcard ▸ dvd_mul_right p m
    exact (hp.out.dvd_mul.1 this).resolve_right hk
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvd
  refine ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx, ?_⟩
  have hx' : orderOf (x : M22) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have := index_modEq_relIndex_normalizer (sylowZpowers hm hpm (x : M22) hx') (H := H)
    (by rw [coe_sylowZpowers]; exact (Subgroup.zpowers_le).2 x.2)
  exact this

end CFSG.ComponentClassification.WittDesign
