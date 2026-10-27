module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
public import Certificates.Certificate36912
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Classes
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi24PumpProof

private theorem card_fix_conj (c g : J) :
    Nat.card {k : Fin 306936 // (c * g * c⁻¹) • k = k} = Nat.card {k : Fin 306936 // g • k = k} := by
  refine Nat.card_congr
    { toFun := fun k => ⟨c⁻¹ • k.1, ?_⟩
      invFun := fun k => ⟨c • k.1, ?_⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  · have h := k.2
    rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul] at h
    exact h
  · have h := k.2
    rw [mul_smul, mul_smul, inv_smul_smul, h]

private theorem smul_mem_fix {g t : J} (h : t * g = g * t)
    {k : Fin 306936} (hk : g • k = k) : g • (t • k) = t • k := by
  rw [smul_smul, ← h, ← smul_smul, hk]

private theorem conj_comm_iff {G : Type*} [Group G] (c a b : G) :
    (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹) ↔ a * b = b * a := by
  constructor
  · intro hh
    have h1 : c * (a * b) * c⁻¹ = c * (b * a) * c⁻¹ := by
      calc c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        _ = (c * b * c⁻¹) * (c * a * c⁻¹) := hh
        _ = c * (b * a) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  · intro hh
    calc (c * a * c⁻¹) * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [hh]
      _ = (c * b * c⁻¹) * (c * a * c⁻¹) := by group

private theorem card_modEq_fix {G X : Type*} [Group G] [MulAction G X] [Finite X] {P : X → Prop} {b : G}
    (hP : ∀ k, P k → P (b • k)) {p : ℕ} (hp : p.Prime) (hb : b ^ p = 1) :
    Nat.card {k : X // P k} ≡ Nat.card {k : X // P k ∧ b • k = k} [MOD p] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype X := Fintype.ofFinite X
  let f : Function.End {k : X // P k} := fun k => ⟨b • k.1, hP k.1 k.2⟩
  have hfn : ∀ (n : ℕ) (k : {k : X // P k}), ((f ^ n) k).1 = b ^ n • k.1 := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [pow_zero b, one_smul]
      rfl
    | succ n ih =>
      intro k
      rw [pow_succ]
      show ((f ^ n) (f k)).1 = _
      rw [ih, pow_succ, mul_smul]
  have hf : f ^ p ^ 1 = 1 := by
    funext k
    apply Subtype.ext
    rw [pow_one, hfn, hb, one_smul]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf
  let e : {k : X // P k ∧ b • k = k} ≃ ↑(Function.fixedPoints f) :=
    { toFun := fun k => ⟨⟨k.1, k.2.1⟩, Subtype.ext k.2.2⟩
      invFun := fun s => ⟨s.1.1, s.1.2, congrArg Subtype.val s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

private theorem card_option_eq (α : Type*) [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]

section Five


private theorem pump_facts : Fi24PumpFacts := Certificates.certificate36912

private theorem exists_conj_five (u : J) (hu : orderOf u = 5) :
    ∃ c g : J, c⁻¹ * u * c = g ∧ FiveFix g := by
  obtain ⟨e, f, h5e, he1, h5f, hcomm, hpow, hfive⟩ := pump_facts.1
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite J := finite_J
  have hc : Commute e f := hcomm
  have hQ := CommutingPair.card_closure_pair_eq_sq (G := J) (p := 5) hc h5e h5f he1 hpow
    (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hQfull : Nat.card (Subgroup.closure ({e, f} : Set J)) =
      5 ^ (Nat.card (⊤ : Subgroup J)).factorization 5 := by
    rw [hQ, Subgroup.card_top, CFSG.Sporadic.Fi24.card_J,
      show (1255205709190661721292800 : ℕ) = 5 ^ 2 * 50208228367626468851712 by norm_num,
      CommutingPair.factorization_pow_mul Nat.prime_five 2 _ (by norm_num)]
  obtain ⟨c, -, hcQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top u) hu
  obtain ⟨a, ha, b, hb, hw⟩ :=
    @CommutingPair.exists_pow_mul_pow_of_mem J inferInstance 5 (by norm_num) e f hc h5e h5f _ hcQ
  have hwo : orderOf (c⁻¹ * u * c) = 5 := by rw [CommutingPair.orderOf_inv_mul_mul, hu]
  have hab : a + b ≠ 0 := by
    intro h0
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    rw [ha0, hb0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact absurd hwo (by norm_num)
  exact ⟨c, e ^ a * f ^ b, hw, hfive a ha b hb hab⟩

private theorem not_five_dvd_of_fix {x : J} (hx : orderOf x = 3)
    (hfix : Nat.card {k : Fin 306936 // x • k = k} = 162) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite J := finite_J
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({x} : Set J))) 5 h5
  have hyJ : orderOf (y : J) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyc : (y : J) * x = x * (y : J) :=
    (Subgroup.mem_centralizer_singleton_iff (g := x) (k := (y : J))).1 y.2
  obtain ⟨c, g, hc, hg⟩ := exists_conj_five (y : J) hyJ
  have hg5 : g ^ 5 = 1 := by
    have := pow_orderOf_eq_one (c⁻¹ * (y : J) * c)
    rwa [CommutingPair.orderOf_inv_mul_mul, hyJ, hc] at this
  have hcomm : (c⁻¹ * x * c) * g = g * (c⁻¹ * x * c) := by
    calc (c⁻¹ * x * c) * g = (c⁻¹ * x * c) * (c⁻¹ * (y : J) * c) := by rw [hc]
      _ = c⁻¹ * (x * (y : J)) * c := by group
      _ = c⁻¹ * ((y : J) * x) * c := by rw [hyc]
      _ = (c⁻¹ * (y : J) * c) * (c⁻¹ * x * c) := by group
      _ = g * (c⁻¹ * x * c) := by rw [hc]
  have hx3 : (c⁻¹ * x * c) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (c⁻¹ * x * c)
    rwa [CommutingPair.orderOf_inv_mul_mul, hx] at this
  have hfix' : Nat.card {k : Fin 306936 // (c⁻¹ * x * c) • k = k} = 162 := by
    have := card_fix_conj c⁻¹ x
    rw [inv_inv] at this
    rw [this]
    exact hfix
  have hmod := card_modEq_fix (G := J) (X := Fin 306936) (P := fun k => (c⁻¹ * x * c) • k = k)
    (b := g) (fun k hk => by
      change (c⁻¹ * x * c) • g • k = g • k
      rw [smul_smul, hcomm, ← smul_smul, hk]) Nat.prime_five hg5
  rw [hfix'] at hmod
  have hsw : Nat.card {k : Fin 306936 // (c⁻¹ * x * c) • k = k ∧ g • k = k} =
      Nat.card {k : Fin 306936 // g • k = k ∧ (c⁻¹ * x * c) • k = k} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun k => and_comm)
  rw [hsw] at hmod
  have := hg.2.2 _ hcomm hx3
  unfold Nat.ModEq at hmod
  omega

private theorem no_commute_five {g v : J} (hg : FiveFix g) {p : ℕ} (hp : p.Prime)
    (hcomm : v * g = g * v) (hvp : v ^ p = 1)
    (hcond : (p = 7 ∧ Nat.card {k : Fin 306936 // v • k = k} = 0) ∨
      (p = 13 ∧ Nat.card {k : Fin 306936 // v • k = k} ≤ 9) ∨
      (p = 11 ∧ Nat.card {k : Fin 306936 // v • k = k} ≤ 10)) : False := by
  classical
  have hmod := card_modEq_fix (G := J) (X := Fin 306936) (P := fun k => g • k = k) (b := v)
    (fun k hk => smul_mem_fix hcomm hk) hp hvp
  rw [hg.1] at hmod
  have hle : Nat.card {k : Fin 306936 // g • k = k ∧ v • k = k} ≤
      Nat.card {k : Fin 306936 // v • k = k} :=
    Nat.card_le_card_of_injective (fun k => ⟨k.1, k.2.2⟩)
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  unfold Nat.ModEq at hmod
  rcases hcond with ⟨rfl, h0⟩ | ⟨rfl, h9⟩ | ⟨rfl, h10⟩
  · omega
  · omega
  · have hφpos : 0 < Nat.card {k : Fin 306936 // g • k = k ∧ v • k = k} := by omega
    obtain ⟨⟨d, hde, hdv⟩, -⟩ := Nat.card_pos_iff.1 hφpos
    have hPstable : ∀ k : Fin 306936, (g • k = k ∧ k ≠ d ∧ cls k * cls d = cls d * cls k) →
        (g • (v • k) = v • k ∧ v • k ≠ d ∧ cls (v • k) * cls d = cls d * cls (v • k)) := by
      rintro k ⟨hk1, hk2, hk3⟩
      refine ⟨smul_mem_fix hcomm hk1, ?_, ?_⟩
      · intro h
        apply hk2
        exact MulAction.injective v (h.trans hdv.symm)
      · have hd' := cls_smul_J v d
        rw [hdv] at hd'
        have e := (conj_comm_iff (jR v) (cls k) (cls d)).2 hk3
        rw [← hd', ← cls_smul_J v k] at e
        exact e
    have hmod2 := card_modEq_fix (G := J) (X := Fin 306936)
      (P := fun k => g • k = k ∧ k ≠ d ∧ cls k * cls d = cls d * cls k) (b := v)
      hPstable hp hvp
    rw [hg.2.1 d hde] at hmod2
    unfold Nat.ModEq at hmod2
    have hinj : Function.Injective (fun o : Option {k : Fin 306936 //
        (g • k = k ∧ k ≠ d ∧ cls k * cls d = cls d * cls k) ∧ v • k = k} =>
        (match o with
          | none => (⟨d, hdv⟩ : {k : Fin 306936 // v • k = k})
          | some a => ⟨a.1, a.2.2⟩)) := by
      intro o₁ o₂ h
      cases o₁ with
      | none =>
        cases o₂ with
        | none => rfl
        | some b =>
          exfalso
          exact b.2.1.2.1 (congrArg Subtype.val h).symm
      | some a =>
        cases o₂ with
        | none =>
          exfalso
          exact a.2.1.2.1 (congrArg Subtype.val h)
        | some b =>
          exact congrArg some (Subtype.ext (by simpa using congrArg Subtype.val h))
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [card_option_eq] at hcard
    omega

private theorem not_five_dvd_of_prime_fix {v : J} {p : ℕ} (hp : p.Prime) (hvp : orderOf v = p)
    (hcond : (p = 7 ∧ Nat.card {k : Fin 306936 // v • k = k} = 0) ∨
      (p = 13 ∧ Nat.card {k : Fin 306936 // v • k = k} ≤ 9) ∨
      (p = 11 ∧ Nat.card {k : Fin 306936 // v • k = k} ≤ 10)) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set J)) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite J := finite_J
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({v} : Set J))) 5 h5
  have hyJ : orderOf (y : J) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyc : (y : J) * v = v * (y : J) :=
    (Subgroup.mem_centralizer_singleton_iff (g := v) (k := (y : J))).1 y.2
  obtain ⟨c, g, hc, hg⟩ := exists_conj_five (y : J) hyJ
  have hcomm : (c⁻¹ * v * c) * g = g * (c⁻¹ * v * c) := by
    calc (c⁻¹ * v * c) * g = (c⁻¹ * v * c) * (c⁻¹ * (y : J) * c) := by rw [hc]
      _ = c⁻¹ * (v * (y : J)) * c := by group
      _ = c⁻¹ * ((y : J) * v) * c := by rw [hyc]
      _ = (c⁻¹ * (y : J) * c) * (c⁻¹ * v * c) := by group
      _ = g * (c⁻¹ * v * c) := by rw [hc]
  have hvp' : (c⁻¹ * v * c) ^ p = 1 := by
    have := pow_orderOf_eq_one (c⁻¹ * v * c)
    rwa [CommutingPair.orderOf_inv_mul_mul, hvp] at this
  have hfix' : Nat.card {k : Fin 306936 // (c⁻¹ * v * c) • k = k} =
      Nat.card {k : Fin 306936 // v • k = k} := by
    have := card_fix_conj c⁻¹ v
    rw [inv_inv] at this
    exact this
  exact no_commute_five hg hp hcomm hvp' (by rw [hfix']; exact hcond)

private theorem pair_kill {x₀ : J} {p n : ℕ} (hD : ThreePair x₀ p n) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hcond : (p = 7 ∧ n = 0) ∨ (p = 13 ∧ n ≤ 9) ∨ (p = 11 ∧ n ≤ 10))
    {x : J} (hconj : IsConj x x₀) :
    ∃ v : J, v ∈ Subgroup.centralizer ({x} : Set J) ∧ ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ orderOf v = p ∧
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set J)) := by
  obtain ⟨v, hvp, hcomm, hfix⟩ := hD
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hord : orderOf (c⁻¹ * v * c) = p := by
    rw [CommutingPair.orderOf_inv_mul_mul]
    exact hvp
  have hfix' : Nat.card {k : Fin 306936 // (c⁻¹ * v * c) • k = k} = n := by
    have := card_fix_conj c⁻¹ v
    rw [inv_inv, hfix] at this
    exact this
  refine ⟨c⁻¹ * v * c, ?_, p, hp, hp7, hord, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c⁻¹ * v * c) * x = c⁻¹ * v * (c * x * c⁻¹) * c := by group
      _ = c⁻¹ * (v * x₀) * c := by rw [hc]; group
      _ = c⁻¹ * (x₀ * v) * c := by rw [hcomm]
      _ = x * (c⁻¹ * v * c) := by rw [← hc]; group
  · refine not_five_dvd_of_prime_fix hp hord ?_
    rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by rw [hfix']; exact h2⟩
    · exact Or.inr (Or.inl ⟨h1, by rw [hfix']; exact h2⟩)
    · exact Or.inr (Or.inr ⟨h1, by rw [hfix']; exact h2⟩)


private theorem classes_J24 (x : J) (hx : orderOf x = 3) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) ∨
      ∃ v : J, v ∈ Subgroup.centralizer ({x} : Set J) ∧ ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧
        orderOf v = p ∧ ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set J)) := by
  obtain ⟨i, hi⟩ := Fi24Sylow.fi24ThreeClasses_holds x hx
  obtain ⟨-, h0, h1, h2, h4, h3⟩ := pump_facts
  fin_cases i
  · exact Or.inr (pair_kill h0 (by norm_num) (by norm_num) (by norm_num) hi)
  · exact Or.inr (pair_kill h1 (by norm_num) (by norm_num) (by norm_num) hi)
  · exact Or.inr (pair_kill h2 (by norm_num) (by norm_num) (by norm_num) hi)
  · refine Or.inl (not_five_dvd_of_fix hx ?_)
    obtain ⟨c, hc⟩ := isConj_iff.1 hi
    have hc' : c * x * c⁻¹ = fi24Rep3 3 := hc
    have hxc : x = c⁻¹ * fi24Rep3 3 * c⁻¹⁻¹ := by
      rw [inv_inv, ← hc']
      group
    have := card_fix_conj c⁻¹ (fi24Rep3 3)
    rw [← hxc] at this
    rw [this]
    exact h3
  · exact Or.inr (pair_kill h4 (by norm_num) (by norm_num) (by norm_num) hi)

end Five
end Fi24PumpProof

open Fi24PumpProof CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.HardMathSupport.Timmesfeld.Tables.Census

private theorem noComp_generic {S H : Type*} [Group S] [Finite S] [Group H] (φ : S ≃* H)
    (h125 : ¬ 125 ∣ Nat.card S)
    (hcls : ∀ x : H, orderOf x = 3 →
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) ∨
        ∃ v : H, v ∈ Subgroup.centralizer ({x} : Set H) ∧ ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧
          orderOf v = p ∧ ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set H)))
    {s : S} (hs : orderOf s = 3) {K : Subgroup S}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set S)))
    (h : IsHatSix ↥K ∨ Nonempty (↥K ≃* alternatingGroup (Fin 6))) : False := by
  have hs' : orderOf (φ s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  rcases hcls (φ s) hs' with h5 | ⟨v, hv, p, hp, hp7, hvp, h5v⟩
  · have hcard := CFSG.Sporadic.FischerOddCore.card_centralizer_mulEquiv φ s
    exact false_of_isHatSix_of_not_five hK.1 h (by rw [← hcard]; exact h5)
  · have hvSC : φ.symm v ∈ Subgroup.centralizer ({s} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.1 hv
    have hvSp : orderOf (φ.symm v) = p := by rw [MulEquiv.orderOf_eq]; exact hvp
    have h5p : ¬ 5 ^ p ∣ Nat.card (Subgroup.centralizer ({s} : Set S)) := by
      intro hd
      apply h125
      have h1 : 5 ^ p ∣ Nat.card S := hd.trans (Subgroup.card_subgroup_dvd_card _)
      have h2 : 5 ^ 3 ∣ 5 ^ p := pow_dvd_pow 5 (by omega)
      have h3 := h2.trans h1
      norm_num at h3
      exact h3
    have h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer ({φ.symm v} : Set S)) := by
      have hcard := CFSG.Sporadic.FischerOddCore.card_centralizer_mulEquiv φ (φ.symm v)
      rw [MulEquiv.apply_symm_apply] at hcard
      rw [← hcard]
      exact h5v
    exact false_of_component_of_prime_elem hK h hvSC hp hp7 hvSp h5p h5

theorem sporNoPumpup_Fi24
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .Fi24Prime := by
  haveI : Finite (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    Finite.of_equiv NativeSporadic.Fi24prime (hbr .Fi24Prime).some.toEquiv
  let φ : (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group ≃* J :=
    (hbr .Fi24Prime).some.symm.trans CFSG.Sporadic.Fi24.fi24EquivJ
  have h125 : ¬ 125 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Fi24.card_J]
    norm_num
  refine sporNoPumpup_of_components hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (hbr .Fi24Prime).some.toEquiv]
    exact (CFSG.Sporadic.Fi24.card_Fi24prime).trans (by norm_num [sporOrd, orderFi24Prime])
  · exact @OPrimeCoreTrivialAt.of_mulEquiv 3 _ _ J (Subgroup.toGroup J) φ
      (Fi24Three.oPrimeCoreTrivialAt_J_of_classes Fi24Sylow.fi24ThreeClasses_holds)
  · intro s hs K hK h
    rcases h with h | ⟨h, _⟩
    · exact @noComp_generic _ ↥J _ _ inferInstance φ h125 classes_J24 s hs K hK (Or.inl h)
    · exact absurd h (by decide)
  · intro _ s hs K hK h
    exact (@noComp_generic _ ↥J _ _ inferInstance φ h125 classes_J24 s hs K hK (Or.inr h)).elim

end CFSG.HardMathSupport.Solomon.Coordinator
