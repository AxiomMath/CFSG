module

public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.A5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv
open scoped Pointwise


abbrev A5 := alternatingGroup (Fin 5)

@[expose] def k1 : A5 := ⟨swap 0 1 * swap 2 3, by decide⟩
@[expose] def k2 : A5 := ⟨swap 0 2 * swap 1 3, by decide⟩
@[expose] def y0 : A5 := ⟨swap 0 2 * swap 0 1, by decide⟩
@[expose] def p0inv : List A5 := [k1, k2, k1 * k2]

theorem y0_trans : ∀ b ∈ p0inv, ∀ c ∈ p0inv, ∃ k : Fin 3,
    (y0 ^ (k : ℕ))⁻¹ * b * y0 ^ (k : ℕ) = c := by decide
theorem orderOf_y0 : orderOf y0 = 3 := orderOf_eq_prime (by decide) (by decide)
theorem norm_p0 : ∀ w : A5, (∀ p ∈ (1 :: p0inv), w * p * w⁻¹ ∈ (1 :: p0inv)) →
    ∃ s ∈ (1 :: p0inv), ∃ k : Fin 3, w = s * y0 ^ (k : ℕ) := by decide +kernel
theorem p0_mul : ∀ a ∈ (1 :: p0inv), ∀ b ∈ (1 :: p0inv), a * b ∈ (1 :: p0inv) := by decide
theorem p0_inv : ∀ a ∈ (1 :: p0inv), a⁻¹ ∈ (1 :: p0inv) := by decide
theorem y0_norm : ∀ p ∈ (1 :: p0inv), y0 * p * y0⁻¹ ∈ (1 :: p0inv) := by decide
theorem y0_norm' : ∀ p, y0 * p * y0⁻¹ ∈ (1 :: p0inv) → p ∈ (1 :: p0inv) := by decide

@[expose] def P0 : Subgroup A5 where
  carrier := {x | x ∈ (1 :: p0inv)}
  one_mem' := by decide
  mul_mem' {a b} ha hb := p0_mul a ha b hb
  inv_mem' {a} ha := p0_inv a ha

theorem mem_P0 {x : A5} : x ∈ P0 ↔ x ∈ (1 :: p0inv) := Iff.rfl

instance : DecidablePred (· ∈ P0) := fun x => inferInstanceAs (Decidable (x ∈ (1 :: p0inv)))

theorem card_P0 : Nat.card P0 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl

theorem fact_A5 : (Nat.card A5).factorization 2 = 2 := by
  rw [card_A5, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem klein_of_map {H : Type*} [Group H] (ψ : A5 ≃* H) :
    ψ y0 ∈ normalizer ((P0.map ψ.toMonoidHom : Subgroup H) : Set H) ∧ orderOf (ψ y0) = 3 ∧
      (∀ b ∈ P0.map ψ.toMonoidHom, ∀ c ∈ P0.map ψ.toMonoidHom, b ≠ 1 → c ≠ 1 →
        ∃ k : ℕ, (ψ y0 ^ k)⁻¹ * b * ψ y0 ^ k = c) ∧
      ∀ w ∈ normalizer ((P0.map ψ.toMonoidHom : Subgroup H) : Set H),
        w ∈ P0.map ψ.toMonoidHom ⊔ zpowers (ψ y0) := by
  have hmem : ∀ x : H, x ∈ P0.map ψ.toMonoidHom ↔ ψ.symm x ∈ (1 :: p0inv) := fun x =>
    Subgroup.mem_map_equiv
  refine ⟨?_, by rw [MulEquiv.orderOf_eq, orderOf_y0], ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    rw [hmem, hmem, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    constructor
    · exact y0_norm _
    · intro hx
      have h := y0_norm' _ hx
      simpa [mul_assoc] using h
  · intro b hb c hc hb1 hc1
    rw [hmem] at hb hc
    have hb' : ψ.symm b ∈ p0inv := by
      rcases List.mem_cons.mp hb with h | h
      · exact absurd (by simpa using congrArg ψ h) hb1
      · exact h
    have hc' : ψ.symm c ∈ p0inv := by
      rcases List.mem_cons.mp hc with h | h
      · exact absurd (by simpa using congrArg ψ h) hc1
      · exact h
    obtain ⟨k, hk⟩ := y0_trans _ hb' _ hc'
    refine ⟨k, ?_⟩
    apply ψ.symm.injective
    rw [map_mul, map_mul, map_inv, map_pow, MulEquiv.symm_apply_apply, hk]
  · intro w hw
    have hw' : ∀ p ∈ (1 :: p0inv), ψ.symm w * p * (ψ.symm w)⁻¹ ∈ (1 :: p0inv) := by
      intro p hp
      have h := (mem_normalizer_iff.mp hw (ψ p)).mp ((hmem _).mpr (by simpa using hp))
      rw [hmem] at h
      simpa [map_mul, map_inv] using h
    obtain ⟨s, hs, k, hk⟩ := norm_p0 _ hw'
    have hw2 : w = ψ s * ψ y0 ^ (k : ℕ) := by
      rw [← map_pow, ← map_mul, ← hk, MulEquiv.apply_symm_apply]
    rw [hw2]
    exact mul_mem (mem_sup_left ((hmem _).mpr (by simpa using hs)))
      (mem_sup_right (pow_mem (mem_zpowers _) _))

theorem exists_equiv_map_P0 {H : Type*} [Group H] (e : H ≃* A5) {P : Subgroup H}
    (hP : Nat.card P = 4) : ∃ ψ : A5 ≃* H, P0.map ψ.toMonoidHom = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPe : Nat.card (P.map e.toMonoidHom) = 4 := by
    rw [← hP]
    exact Nat.card_congr (P.equivMapOfInjective _ e.injective).toEquiv.symm
  let S : Sylow 2 A5 := Sylow.ofCard (P.map e.toMonoidHom) (by rw [hPe, fact_A5]; rfl)
  let S0 : Sylow 2 A5 := Sylow.ofCard P0 (by rw [card_P0, fact_A5]; rfl)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 S0 S
  have h1 : P.map e.toMonoidHom = P0.map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun T : Sylow 2 A5 => (T : Subgroup A5)) hg
    simp only [S, S0, Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
    rw [← h, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨(MulAut.conj g).trans e.symm, ?_⟩
  have h2 : P0.map ((MulAut.conj g).trans e.symm).toMonoidHom =
      (P0.map (MulAut.conj g).toMonoidHom).map e.symm.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h2, ← h1, Subgroup.map_map]
  convert Subgroup.map_id P
  ext x
  simp

theorem exists_klein_three {G : Type*} [Group G] {A P : Subgroup G} (e : ↥A ≃* A5)
    (hPA : P ≤ A) (hP : Nat.card P = 4) :
    ∃ y ∈ A, y ∈ normalizer (P : Set G) ∧ orderOf y = 3 ∧
      (∀ b ∈ P, ∀ c ∈ P, b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) ∧
      ∀ w ∈ A, w ∈ normalizer (P : Set G) → w ∈ P ⊔ zpowers y := by
  have hP' : Nat.card (P.subgroupOf A) = 4 := by
    rw [← hP]; exact Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv
  obtain ⟨ψ, hψ⟩ := exists_equiv_map_P0 e.symm.symm hP'
  obtain ⟨hn, ho, ht, hN⟩ := klein_of_map ψ
  rw [hψ] at hn ht hN
  have hnorm : ∀ a : ↥A, (a : G) ∈ normalizer (P : Set G) ↔
      a ∈ normalizer ((P.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
    intro a
    rw [← Subgroup.subgroupOf_normalizer_eq hPA, mem_subgroupOf]
  refine ⟨(ψ y0 : G), (ψ y0).2, (hnorm _).mpr hn, by rw [Subgroup.orderOf_coe, ho], ?_, ?_⟩
  · intro b hb c hc hb1 hc1
    obtain ⟨k, hk⟩ := ht ⟨b, hPA hb⟩ (mem_subgroupOf.mpr hb) ⟨c, hPA hc⟩
      (mem_subgroupOf.mpr hc) (fun h => hb1 (congrArg Subtype.val h))
      (fun h => hc1 (congrArg Subtype.val h))
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro w hwA hw
    have h := hN ⟨w, hwA⟩ ((hnorm ⟨w, hwA⟩).mp hw)
    have hmap := mem_map_of_mem A.subtype h
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hPA, MonoidHom.map_zpowers] at hmap
    exact hmap



theorem card_dvd_four_of_isPGroup {A : Type*} [Group A] (e : A ≃* alternatingGroup (Fin 5))
    {P : Subgroup A} (hP : IsPGroup 2 P) : Nat.card P ∣ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Nat.card A = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 2 ^ k ∣ 60 := hk ▸ hA ▸ Subgroup.card_subgroup_dvd_card P
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    omega
  rw [hk]
  exact Nat.pow_dvd_pow 2 hk2


@[expose] def c4 : Perm (Fin 5) := swap 0 3 * swap 0 2 * swap 0 1

theorem orderOf_c4 : orderOf c4 = 4 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact orderOf_eq_prime_pow (by decide) (by decide)

theorem card_perm5 : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl

theorem fact_perm5 : (Nat.card (Perm (Fin 5))).factorization 2 = 3 := by
  rw [card_perm5, show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, Nat.factorization_mul (by norm_num)
    (by norm_num), Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem card_le_four_of_elemAbelian_perm {E : Subgroup (Perm (Fin 5))}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : 2 ^ k ∣ 120 := hk ▸ card_perm5 ▸ Subgroup.card_subgroup_dvd_card E
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ∣ 120 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    omega
  rcases Nat.lt_or_ge k 3 with h | h
  · rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  · exfalso
    have hk' : k = 3 := by omega
    let SE : Sylow 2 (Perm (Fin 5)) := Sylow.ofCard E (by rw [hk, hk', fact_perm5])
    have hc4 : IsPGroup 2 (zpowers c4) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, orderOf_c4]; norm_num)
    obtain ⟨S0, hS0⟩ := hc4.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) S0 SE
    have hmem : MulAut.conj g c4 ∈ E := by
      have h1 : MulAut.conj g c4 ∈ MulAut.conj g • (S0 : Subgroup (Perm (Fin 5))) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ (hS0 (mem_zpowers c4))
      rw [← Sylow.coe_subgroup_smul, hg] at h1
      exact h1
    have h2 := hE.2 _ hmem
    rw [← map_pow] at h2
    have h3 : c4 ^ 2 = 1 := (MulAut.conj g).injective (by rw [h2, map_one])
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [orderOf_c4] at h4
    omega



theorem card_le_of_le_normalizer {G : Type} [Group G] [Finite G] {A E : Subgroup G}
    (e : ↥A ≃* A5) (hEN : E ≤ normalizer (A : Set G)) (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 4 * Nat.card (E ⊓ centralizer (A : Set G) : Subgroup G) := by
  set N := normalizer (A : Set G) with hN
  have hAN : A ≤ N := le_normalizer
  let A' : Subgroup ↥N := A.subgroupOf N
  have : A'.Normal := Subgroup.normal_in_normalizer
  let e' : ↥A' ≃* A5 := (subgroupOfEquivOfLe hAN).trans e
  let ι : MulAut ↥A' ≃* Perm (Fin 5) := (MulAut.congr e').trans (MulEquiv.ofBijective
    (CFSG.Quasithin.SteinbergCB.conjPerm 5) ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective
      (by norm_num), CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩).symm
  let φ : ↥E →* Perm (Fin 5) :=
    ((ι.toMonoidHom).comp (MulAut.conjNormal (H := A'))).comp
      (Subgroup.inclusion hEN)
  have hker : ∀ x : ↥E, φ x = 1 ↔ (x : G) ∈ centralizer (A : Set G) := by
    intro x
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ ι.injective]
    rw [mem_centralizer_iff]
    constructor
    · intro h a ha
      have h1 := congrArg (fun f : MulAut ↥A' => ((f ⟨⟨a, hAN ha⟩, mem_subgroupOf.mpr ha⟩ :
        ↥A') : G)) h
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      have h2 : (x : G) * a * (x : G)⁻¹ = a := by simpa using h1
      calc a * (x : G) = (x : G) * a * (x : G)⁻¹ * (x : G) := by rw [h2]
        _ = (x : G) * a := by group
    · intro h
      refine MulEquiv.ext fun a => Subtype.ext (Subtype.ext ?_)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      have ha : ((a : ↥N) : G) ∈ A := mem_subgroupOf.mp a.2
      have h2 := h _ ha
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (x : G) * ((a : ↥N) : G) * (x : G)⁻¹ = ((a : ↥N) : G) * (x : G) * (x : G)⁻¹ := by
            rw [h2]
        _ = ((a : ↥N) : G) := by group
  have hkcard : Nat.card φ.ker = Nat.card (E ⊓ centralizer (A : Set G) : Subgroup G) := by
    refine Nat.card_congr ⟨fun x => ⟨(x : ↥E), (x : ↥E).2, (hker _).mp x.2⟩,
      fun y => ⟨⟨y, y.2.1⟩, (hker ⟨y, y.2.1⟩).mpr y.2.2⟩, fun x => rfl, fun y => rfl⟩
  have hrange : Nat.card φ.range ≤ 4 := by
    apply card_le_four_of_elemAbelian_perm
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      exact hE.1.is_comm.comm x y
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow]
      have : u ^ 2 = 1 := Subtype.ext (by simpa using hE.2 u u.2)
      rw [this, map_one]
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hkcard] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_right _ hrange

theorem center_A5 : center A5 = ⊥ := by
  have : IsSimpleGroup A5 :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A5) with h | h
  · exact h
  · exfalso
    have h1 := mem_center_iff.mp (h ▸ mem_top k1) y0
    revert h1
    decide

theorem inf_centralizer_eq_bot {G : Type*} [Group G] {A : Subgroup G} (e : ↥A ≃* A5) :
    A ⊓ centralizer (A : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxC⟩ := mem_inf.mp hx
  have hz : (⟨x, hxA⟩ : ↥A) ∈ center ↥A := mem_center_iff.mpr fun b =>
    Subtype.ext (mem_centralizer_iff.mp hxC b b.2)
  have hz' : e ⟨x, hxA⟩ ∈ center A5 := by
    rw [mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz c]
  rw [center_A5, mem_bot] at hz'
  have : (⟨x, hxA⟩ : ↥A) = 1 := e.injective (by rw [hz', map_one])
  rw [mem_bot]
  exact congrArg Subtype.val this

end CFSG.ComponentClassification.RankTwoAltFive
