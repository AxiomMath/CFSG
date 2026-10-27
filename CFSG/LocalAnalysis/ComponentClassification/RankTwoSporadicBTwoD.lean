module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B

open Subgroup
open scoped commutatorElement
open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.CTIB CFSG.Monster.B.GSide

@[expose] def TwoDFixedPointFree
    : Prop :=
  ∀ y ∈ centralizer (T9S : Set Shat), (∀ g ∈ centralizer ({t2DS} : Set Shat),
    Odd (orderOf g) → y * g * y⁻¹ * g⁻¹ ∈ T9S) → y ∈ T9S

theorem twoDFixedPointFree
    : TwoDFixedPointFree :=
  TwoDFix.fixedPointFree

section Generic

variable {G : Type*} [Group G]

theorem exists_mem_mul_pow_eq {N : Subgroup G} (hN : N.Normal) {p : G} (hp : p ∈ N) (k : G)
    (n : ℕ) : ∃ q ∈ N, (p * k) ^ n = q * k ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
  | succ n ih =>
    obtain ⟨q, hq, hqe⟩ := ih
    refine ⟨q * (k ^ n * p * (k ^ n)⁻¹), mul_mem hq (hN.conj_mem p hp _), ?_⟩
    rw [pow_succ, hqe, pow_succ]
    group

theorem mem_of_pow_two_pow_mem {N : Subgroup G} {g : G} (hg : Odd (orderOf g)) {b : ℕ}
    (h : g ^ 2 ^ b ∈ N) : g ∈ N := by
  have hcop : Nat.Coprime (2 ^ b) (orderOf g) :=
    Nat.Coprime.pow_left b (Nat.coprime_comm.1 hg.coprime_two_right)
  rcases Nat.lt_or_ge 1 (orderOf g) with h1 | h1
  · obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    have e : g = (g ^ 2 ^ b) ^ u := by
      rw [← pow_mul, ← pow_mod_orderOf, hu, pow_one]
    rw [e]
    exact pow_mem h u
  · have hg1 : g = 1 := by
      have h0 : 0 < orderOf g := Odd.pos hg
      rw [← orderOf_eq_one_iff]
      omega
    rw [hg1]
    exact one_mem _

theorem mem_of_odd_of_mul_mem {N : Subgroup G} (hN : N.Normal) {g p : G} (hg : Odd (orderOf g))
    (hp : p ∈ N) {b : ℕ} (hb : orderOf (p⁻¹ * g) = 2 ^ b) : g ∈ N := by
  obtain ⟨q, hq, hqe⟩ := exists_mem_mul_pow_eq hN hp (p⁻¹ * g) (2 ^ b)
  rw [← hb, pow_orderOf_eq_one, mul_one, mul_inv_cancel_left] at hqe
  refine mem_of_pow_two_pow_mem hg (b := b) ?_
  rw [← hb, hqe]
  exact hq

theorem commute_conj_of_commute {g a p : G}
    (h : g⁻¹ * p * g⁻¹⁻¹ * a = a * (g⁻¹ * p * g⁻¹⁻¹)) : p * (g * a * g⁻¹) = g * a * g⁻¹ * p := by
  calc p * (g * a * g⁻¹) = g * (g⁻¹ * p * g⁻¹⁻¹ * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * p * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = g * a * g⁻¹ * p := by group

theorem conj_eq_of_commute {g a : G} (h : g * a = a * g) : g * a * g⁻¹ = a := by
  rw [h, mul_inv_cancel_right]

theorem conj_eq_of_conj_mul {g x t : G} (h1 : g * (x * t) * g⁻¹ = x * t)
    (h2 : g * t * g⁻¹ = t) : g * x * g⁻¹ = x := by
  calc g * x * g⁻¹ = g * (x * t) * g⁻¹ * (g * t * g⁻¹)⁻¹ := by group
    _ = x := by rw [h1, h2, mul_inv_cancel_right]

theorem mem_centralizer_of_le_centralizer {H : Subgroup G} {a : G} (h : H ≤ centralizer {a}) :
    a ∈ centralizer (H : Set G) :=
  mem_centralizer_iff.2 fun _ hx => mem_centralizer_singleton_iff.1 (h hx)

end Generic

theorem normal_OmegaPlus
    : (OmegaPlus).Normal := by
  unfold OmegaPlus
  infer_instance

theorem mem_OmegaPlus_of_odd
    {h : TauCeti.QuadraticMap.orthogonalGroup qPlus} (hh : Odd (orderOf h)) : h ∈ OmegaPlus := by
  have := normal_OmegaPlus
  have h2 : h ^ 2 ∈ OmegaPlus := by
    obtain ⟨c, hc⟩ := index_OmegaPlus_dvd_two
    have e2 : h ^ 2 = (h ^ OmegaPlus.index) ^ c := by rw [← pow_mul, ← hc]
    rw [e2]
    exact pow_mem (pow_index_mem _ h) c
  obtain ⟨j, hj⟩ := hh
  have e : h = (h ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf h + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [e]
  exact pow_mem h2 _

theorem commutator_OmegaPlus
    (hfin : Nat.card OmegaPlus ≠ 0) : ⁅OmegaPlus, OmegaPlus⁆ = OmegaPlus := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := isSimpleGroup_OmegaPlus
  obtain ⟨m, hm⟩ := dvd_natCard_OmegaPlus
  refine commutator_eq_self_of_isSimpleGroup_of_dvd (p := 7)
    ⟨2 ^ 12 * 3 ^ 5 * 5 ^ 2 * m, by rw [hm]; ring⟩ ?_ hfin
  intro h7
  rw [h7] at hm
  norm_num at hm
  omega

@[expose] noncomputable def twoDCore
    : Subgroup (centralizer ({t2DS} : Set Shat)) :=
  normalClosure {g | Odd (orderOf g)}

instance normal_twoDCore
    : (twoDCore).Normal :=
  normalClosure_normal

theorem natCard_centralizer_t2DS
    : Nat.card (centralizer ({t2DS} : Set Shat)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 :=
  natCard_centralizer_of_rankS_eq_2168 centralizer_t2DS_le_normalizer t2DS orderOf_t2DS
    rankS_t2DS

theorem exists_orderOf_eq_two_pow_of_rhoPlus_eq_one
    {g : centralizer ({t2DS} : Set Shat)} (hg : rhoPlus centralizer_t2DS_le_normalizer g = 1) :
    ∃ b, orderOf g = 2 ^ b := by
  have hT := (rhoPlus_eq_one_iff centralizer_t2DS_le_normalizer g).1 hg
  have hmem : (g : Shat) ∈ centralizer (T9S : Set Shat) := mem_centralizer_iff.2 fun x hx => by
    have e := hT x hx
    calc x * (g : Shat) = (g : Shat) * x * (g : Shat)⁻¹ * (g : Shat) := by rw [e]
      _ = (g : Shat) * x := by group
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.1 isPGroup_centralizer_T9S) ⟨g, hmem⟩
  refine ⟨b, ?_⟩
  have h1 : orderOf (g : Shat) = orderOf g := Subgroup.orderOf_coe g
  have h2 : orderOf (⟨(g : Shat), hmem⟩ : centralizer (T9S : Set Shat)) = orderOf (g : Shat) :=
    Subgroup.orderOf_mk _ _
  rw [← h1, ← h2, hb]

theorem exists_rhoPlus_ne_one
    : ∃ g : centralizer ({t2DS} : Set Shat), orderOf g = 3 ∧
      rhoPlus centralizer_t2DS_le_normalizer g ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite (centralizer ({t2DS} : Set Shat)) := Nat.finite_of_card_ne_zero (by
    rw [natCard_centralizer_t2DS]
    norm_num)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (by
    rw [natCard_centralizer_t2DS]
    norm_num)
  refine ⟨g, hg, fun h1 => ?_⟩
  obtain ⟨b, hb⟩ := exists_orderOf_eq_two_pow_of_rhoPlus_eq_one h1
  rw [hg] at hb
  rcases b with _ | b
  · norm_num at hb
  · rw [pow_succ] at hb
    omega

theorem map_twoDCore
    : twoDCore.map (rhoPlus centralizer_t2DS_le_normalizer) = OmegaPlus := by
  have := normal_OmegaPlus
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine normalClosure_le_normal fun g hg => ?_
    exact mem_OmegaPlus_of_odd (Odd.of_dvd_nat hg (orderOf_map_dvd _ g))
  · refine le_OmegaPlus_of_normal _
      ((normalClosure_normal).map _ (rhoPlus_surjective centralizer_t2DS_le_normalizer)) ?_
    intro h
    obtain ⟨g, hg3, hg⟩ := exists_rhoPlus_ne_one
    have hmem : rhoPlus centralizer_t2DS_le_normalizer g ∈
        twoDCore.map (rhoPlus centralizer_t2DS_le_normalizer) :=
      mem_map_of_mem _ (subset_normalClosure (by show Odd (orderOf g); rw [hg3]; decide))
    rw [h, mem_bot] at hmem
    exact hg hmem

theorem natCard_OmegaPlus_ne_zero
    : Nat.card OmegaPlus ≠ 0 := by
  have h0 : Nat.card (centralizer ({t2DS} : Set Shat)) ≠ 0 := by
    rw [natCard_centralizer_t2DS]
    norm_num
  have : Finite (centralizer ({t2DS} : Set Shat)) := Nat.finite_of_card_ne_zero h0
  have : Finite (TauCeti.QuadraticMap.orthogonalGroup qPlus) :=
    Finite.of_surjective _ (rhoPlus_surjective centralizer_t2DS_le_normalizer)
  exact Nat.card_pos.ne'

theorem commutator_twoDCore
    : ⁅twoDCore, twoDCore⁆ = twoDCore := by
  refine le_antisymm (commutator_le_left _ _) (normalClosure_le_normal fun g hg => ?_)
  have hgP : g ∈ twoDCore := subset_normalClosure hg
  have hΩ : rhoPlus centralizer_t2DS_le_normalizer g ∈
      (⁅twoDCore, twoDCore⁆).map (rhoPlus centralizer_t2DS_le_normalizer) := by
    rw [map_commutator, map_twoDCore, commutator_OmegaPlus natCard_OmegaPlus_ne_zero]
    exact mem_OmegaPlus_of_odd (Odd.of_dvd_nat hg (orderOf_map_dvd _ g))
  obtain ⟨p, hp, hpg⟩ := hΩ
  have hpP : p ∈ twoDCore := commutator_le_left _ _ hp
  have hk1 : rhoPlus centralizer_t2DS_le_normalizer (p⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hpg, inv_mul_cancel]
  obtain ⟨b, hb⟩ := exists_orderOf_eq_two_pow_of_rhoPlus_eq_one hk1
  exact mem_of_odd_of_mul_mem inferInstance hg hp hb

theorem classFact_rankS_twoD
    (hD : TwoDFixedPointFree) : ClassFact rankS t2DS := by
  have := normal_OmegaPlus
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup Shat,
      P = twoDCore.map (centralizer ({t2DS} : Set Shat)).subtype := ⟨_, rfl⟩
  have hPC : P ≤ centralizer ({t2DS} : Set Shat) := hPdef ▸ map_subtype_le _
  have hPn : ∀ g ∈ centralizer ({t2DS} : Set Shat), ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    rintro g hg _ hp
    rw [hPdef] at hp ⊢
    obtain ⟨p, hp, rfl⟩ := hp
    exact ⟨⟨g, hg⟩ * p * ⟨g, hg⟩⁻¹, (normalClosure_normal).conj_mem p hp _, rfl⟩
  have hoddP : ∀ g : centralizer ({t2DS} : Set Shat), Odd (orderOf g) → (g : Shat) ∈ P :=
    fun g hg => hPdef ▸ ⟨g, subset_normalClosure hg, rfl⟩
  obtain ⟨g₃, hg₃, hρ₃⟩ := exists_rhoPlus_ne_one
  have hodd₃ : Odd (orderOf g₃) := by
    rw [hg₃]
    decide
  refine ⟨P, ?_, hPC, fun y hy hyx hy2 hy1 hyx' => ?_⟩
  · rw [hPdef, ← map_commutator, commutator_twoDCore]
  exfalso
  have hyC : y ∈ centralizer ({t2DS} : Set Shat) := mem_centralizer_singleton_iff.2 hyx
  have hyP : ∀ p ∈ P, p * y = y * p := fun p hp => (mem_centralizer_iff.1 hy) p hp
  have hρy : rhoPlus centralizer_t2DS_le_normalizer ⟨y, hyC⟩ = 1 := by
    have hcen : rhoPlus centralizer_t2DS_le_normalizer ⟨y, hyC⟩ ∈
        centralizer (OmegaPlus : Set (TauCeti.QuadraticMap.orthogonalGroup qPlus)) := by
      rw [mem_centralizer_iff]
      intro w hw
      rw [← map_twoDCore] at hw
      obtain ⟨p, hp, rfl⟩ := hw
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hyP _ (hPdef ▸ ⟨p, hp, rfl⟩)
    by_contra hne
    have hZ : centralizer (OmegaPlus : Set (TauCeti.QuadraticMap.orthogonalGroup qPlus)) ≠ ⊥ :=
      fun h => hne (by rw [h, mem_bot] at hcen; exact hcen)
    have hle := le_OmegaPlus_of_normal _ inferInstance hZ
    have hcomm : ⁅OmegaPlus, OmegaPlus⁆ = ⊥ := (commutator_eq_bot_iff_le_centralizer).2 hle
    rw [commutator_OmegaPlus natCard_OmegaPlus_ne_zero] at hcomm
    have hm : rhoPlus centralizer_t2DS_le_normalizer g₃ ∈ OmegaPlus :=
      mem_OmegaPlus_of_odd (Odd.of_dvd_nat hodd₃ (orderOf_map_dvd _ g₃))
    exact hρ₃ ((Subgroup.eq_bot_iff_forall _).1 hcomm _ hm)
  have hyT : y ∈ centralizer (T9S : Set Shat) := by
    have hT := (rhoPlus_eq_one_iff centralizer_t2DS_le_normalizer ⟨y, hyC⟩).1 hρy
    refine mem_centralizer_iff.2 fun x hx => ?_
    have e := hT x hx
    calc x * y = y * x * y⁻¹ * y := by rw [e]
      _ = y * x := by group
  have hy9 : y ∈ T9S := hD y hyT fun g hg hodd => by
    have hc := hyP g (hoddP ⟨g, hg⟩ (by rwa [Subgroup.orderOf_mk]))
    rw [show y * g * y⁻¹ * g⁻¹ = 1 by rw [← hc]; group]
    exact one_mem _
  have hR : ∀ g ∈ centralizer ({t2DS} : Set Shat), ∀ r ∈ T9S ⊓ centralizer (P : Set Shat),
      g * r * g⁻¹ ∈ T9S ⊓ centralizer (P : Set Shat) := by
    intro g hg r hr
    rw [mem_inf] at hr ⊢
    refine ⟨?_, mem_centralizer_iff.2 fun p hp => ?_⟩
    · exact ((centralizer_t2DS_le_normalizer hg) r).1 hr.1
    · have hp' : g⁻¹ * p * g⁻¹⁻¹ ∈ P := hPn _ (inv_mem hg) p hp
      exact commute_conj_of_commute ((mem_centralizer_iff.1 hr.2) _ hp')
  have ht0R : t2DS ∈ T9S ⊓ centralizer (P : Set Shat) :=
    mem_inf.2 ⟨t2DS_mem_T9S, mem_centralizer_of_le_centralizer hPC⟩
  have hyR : y ∈ T9S ⊓ centralizer (P : Set Shat) := mem_inf.2 ⟨hy9, hy⟩
  have hfix : (∀ a ∈ A8S, a ∈ T9S ⊓ centralizer (P : Set Shat)) → False := fun hA8 => by
    apply hρ₃
    rw [rhoPlus_eq_one_iff]
    have hgP : (g₃ : Shat) ∈ P := hoddP g₃ hodd₃
    have hA : ∀ a ∈ A8S, (g₃ : Shat) * a * (g₃ : Shat)⁻¹ = a := fun a ha =>
      conj_eq_of_commute ((mem_centralizer_iff.1 (mem_inf.1 (hA8 a ha)).2) _ hgP)
    have ht : (g₃ : Shat) * t2DS * (g₃ : Shat)⁻¹ = t2DS :=
      conj_eq_of_commute (mem_centralizer_singleton_iff.1 g₃.2)
    intro x hx
    rcases mem_A8S_or_mul_t2DS_mem hx with hxa | hxa
    · exact hA x hxa
    · exact conj_eq_of_conj_mul (hA _ hxa) ht
  rcases eq_of_invariant_T9S _ inf_le_left hR with h | h | h | h
  · exact t2DS_ne_one (mem_bot.1 ((SetLike.ext_iff.1 h t2DS).1 ht0R))
  · rcases (zpowers_t2DS_eq y).1 ((SetLike.ext_iff.1 h y).1 hyR) with h' | h'
    · exact hy1 h'
    · exact hyx' h'
  · exact hfix fun a ha => (SetLike.ext_iff.1 h a).2 ha
  · exact hfix fun a ha => (SetLike.ext_iff.1 h a).2 (A8S_le_T9S ha)

theorem twoD_classFact_of
    (hD : TwoDFixedPointFree) : ClassFact rankB (classRep 3) := by
  obtain ⟨X, hXe⟩ : ∃ X : NativeSporadic.B, sEquiv (iotaEquiv X) = t2DS :=
    ⟨iotaEquiv.symm (sEquiv.symm _), by rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]⟩
  have hS : ClassFact (fun s => rankS (sEquiv s)) (iotaEquiv X) :=
    classFact_of_mulEquiv sEquiv (r₁ := fun s => rankS (sEquiv s)) (fun _ => rfl)
      (by rw [hXe]; exact classFact_rankS_twoD hD)
  have hX : ClassFact rankB X :=
    @classFact_of_mulEquiv NativeSporadic.B Sbp inferInstance inferInstance iotaEquiv rankB
      (fun s => rankS (sEquiv s)) (fun a => rankS_sEquiv_iotaEquiv a) X hS
  have hXr : rankB X = 2168 := by
    rw [← rankS_sEquiv_iotaEquiv, hXe]
    exact rankS_t2DS
  have hX2 : X ^ 2 = 1 := by
    apply iotaEquiv.injective
    apply sEquiv.injective
    rw [map_pow, map_pow, hXe, map_one, map_one, sq, t2DS_mul_self]
  have hX1 : X ≠ 1 := fun h => by
    rw [h] at hXr
    simp [rankB] at hXr
  have hc3 : IsConj X (classRep 3) := by
    obtain ⟨i, hi, hc, hr⟩ := isConj_classRep hX2 hX1
    obtain ⟨-, h1, h0, h5, -⟩ := classes_B
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · exact hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc3
  rw [← hg]
  exact @classFact_conj NativeSporadic.B inferInstance rankB rankB_conj X hX g

theorem twoD_classFact
    : ClassFact rankB (classRep 3) :=
  twoD_classFact_of twoDFixedPointFree

end CFSG.ComponentClassification.RankTwoSporadic.B
