module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36D
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33R

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

@[expose] def oddGen (C : Subgroup X) : Subgroup X := closure {x | x ∈ C ∧ Odd (orderOf x)}

theorem oddGen_le (C : Subgroup X) : oddGen C ≤ C :=
  (closure_le _).mpr fun _ hx => hx.1

theorem mem_oddGen {C : Subgroup X} {x : X} (hx : x ∈ C) (hodd : Odd (orderOf x)) :
    x ∈ oddGen C :=
  subset_closure ⟨hx, hodd⟩

theorem oddGen_mono {C D : Subgroup X} (h : C ≤ D) : oddGen C ≤ oddGen D :=
  closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem conj_mem_oddGen_centralizer {v g x : X}
    (hx : x ∈ oddGen (centralizer ({v} : Set X))) :
    g * x * g⁻¹ ∈ oddGen (centralizer ({g * v * g⁻¹} : Set X)) := by
  change x ∈ Subgroup.closure _ at hx
  induction hx using closure_induction with
  | mem y hy =>
    refine mem_oddGen (mem_centralizer_conj_iff.mp hy.1) ?_
    rw [show g * y * g⁻¹ = MulAut.conj g y from rfl, MulEquiv.orderOf_eq]
    exact hy.2
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul y z _ _ hy hz =>
    have h : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [h]
    exact mul_mem hy hz
  | inv y _ hy =>
    have h : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem hy

theorem exists_pow_odd_of_odd_map {G P : Type*} [Group G] [Finite G] [Group P] (f : G →* P)
    (x : G) (hodd : Odd (orderOf (f x))) :
    ∃ k : ℕ, Odd (orderOf (x ^ k)) ∧ f (x ^ k) = f x := by
  obtain ⟨a, c, hc, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hy : Odd (orderOf (x ^ 2 ^ a)) := by
    have h1 : (x ^ 2 ^ a) ^ c = 1 := by rw [← pow_mul, ← hord, pow_orderOf_eq_one]
    exact hc.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (2 ^ a) (orderOf (f x)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨2 ^ a * d, ?_, ?_⟩
  · rw [pow_mul]
    exact hy.of_dvd_nat (orderOf_pow_dvd d)
  · rw [pow_mul, map_pow, map_pow, hd]

theorem sign_eq_one_of_odd_orderOf {α : Type*} [Fintype α] [DecidableEq α] {π : Perm α}
    (h : Odd (orderOf π)) : Perm.sign π = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : Perm.sign π ^ orderOf π = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
  exact h1

variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem mem_alternatingGroup_of_mem_oddGen {C : Subgroup X}
    (hCN : C ≤ normalizer (M : Set X)) {y : X} (hy : y ∈ oddGen C) :
    ∀ hyN : y ∈ normalizer (M : Set X), ρ ⟨y, hyN⟩ ∈ alternatingGroup (Fin r) := by
  change y ∈ Subgroup.closure _ at hy
  induction hy using closure_induction with
  | mem z hz =>
    intro hzN
    rw [Perm.mem_alternatingGroup]
    refine sign_eq_one_of_odd_orderOf ?_
    have h1 : Odd (orderOf (⟨z, hzN⟩ : ↥(normalizer (M : Set X)))) := by
      rw [Subgroup.orderOf_mk]
      exact hz.2
    exact h1.of_dvd_nat (orderOf_map_dvd ρ _)
  | one =>
    intro h
    have h1 : ρ ⟨1, h⟩ = 1 := map_one ρ
    rw [h1]
    exact one_mem _
  | mul z w hz hw ihz ihw =>
    intro hzwN
    have hzN : z ∈ normalizer (M : Set X) := hCN (oddGen_le C hz)
    have hwN : w ∈ normalizer (M : Set X) := hCN (oddGen_le C hw)
    have h1 : (⟨z * w, hzwN⟩ : ↥(normalizer (M : Set X))) = ⟨z, hzN⟩ * ⟨w, hwN⟩ := rfl
    rw [h1, map_mul]
    exact mul_mem (ihz hzN) (ihw hwN)
  | inv z hz ihz =>
    intro hzN'
    have hzN : z ∈ normalizer (M : Set X) := hCN (oddGen_le C hz)
    have h1 : (⟨z⁻¹, hzN'⟩ : ↥(normalizer (M : Set X))) = (⟨z, hzN⟩)⁻¹ := rfl
    rw [h1, map_inv]
    exact inv_mem (ihz hzN)

theorem IsPermAction.exists_lift_oddCentGen (hρ : IsPermAction θ ρ) [Finite X] (hr : 4 ≤ r)
    {a : X} (ha : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1) {π : Perm (Fin r)}
    (hπ : π ∈ oddCentGen (ρ ⟨a, ha⟩)) :
    ∃ (q : X) (hq : q ∈ M), q ∈ oddGen (centralizer ({a} : Set X)) ∧
      ρ ⟨q, le_normalizer hq⟩ = π := by
  change π ∈ Subgroup.closure _ at hπ
  induction hπ using closure_induction with
  | mem π hπ' =>
    obtain ⟨hπA, hπσ, hodd⟩ := hπ'
    obtain ⟨x, hxa, hx⟩ := hρ.exists_lift ha ha2 (b := ⟨π, hπA⟩) hπσ
    have hρx : ρ ⟨x, le_normalizer x.2⟩ = π := by
      rw [hρ.apply_of_mem hr x, hx]
    let f : ↥M →* Perm (Fin r) := ρ.comp (Subgroup.inclusion le_normalizer)
    have hfx : f x = π := hρx
    obtain ⟨k, hk, hfk⟩ := exists_pow_odd_of_odd_map f x (by rw [hfx]; exact hodd)
    refine ⟨((x ^ k : ↥M) : X), (x ^ k).2, mem_oddGen ?_ ?_, ?_⟩
    · rw [Subgroup.coe_pow]
      exact pow_mem hxa k
    · rw [Subgroup.orderOf_coe]
      exact hk
    · rw [← hfx, ← hfk]
      rfl
  | one => exact ⟨1, one_mem _, one_mem _, map_one ρ⟩
  | mul π₁ π₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, hq₁, hq₁o, hρ₁⟩ := h₁
    obtain ⟨q₂, hq₂, hq₂o, hρ₂⟩ := h₂
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, mul_mem hq₁o hq₂o, ?_⟩
    rw [← hρ₁, ← hρ₂, ← map_mul]
    rfl
  | inv π _ h =>
    obtain ⟨q, hq, hqo, hρq⟩ := h
    refine ⟨q⁻¹, inv_mem hq, inv_mem hqo, ?_⟩
    rw [← hρq, ← map_inv]
    rfl

theorem IsPermAction.exists_four_involution (hρ : IsPermAction θ ρ) [Finite X] (hr : 9 ≤ r)
    {s : X} (hs : s ∈ normalizer (M : Set X)) (hs2 : s * s = 1) :
    ∃ (e : X) (he : e ∈ M), e ∈ oddGen (centralizer ({s} : Set X)) ∧ e * e = 1 ∧
      (ρ ⟨e, le_normalizer he⟩).support.card = 4 := by
  classical
  have hσ2 : ρ ⟨s, hs⟩ * ρ ⟨s, hs⟩ = 1 := by
    rw [← map_mul, show (⟨s, hs⟩ : ↥(normalizer (M : Set X))) * ⟨s, hs⟩ = 1 from
      Subtype.ext hs2, map_one]
  obtain ⟨δ, hδ, hδ2, hδ4⟩ := exists_four_mem_oddCentGen hσ2 (by rw [Fintype.card_fin]; exact hr)
  obtain ⟨q, hq, hqo, hρq⟩ := hρ.exists_lift_oddCentGen (by omega) hs hs2 hδ
  obtain ⟨b, c, hc, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
  have heM : q ^ c ∈ M := pow_mem hq c
  have hρe : ρ ⟨q ^ c, le_normalizer heM⟩ = δ := by
    have h1 : (⟨q ^ c, le_normalizer heM⟩ : ↥(normalizer (M : Set X))) =
        ⟨q, le_normalizer hq⟩ ^ c := rfl
    rw [h1, map_pow, hρq]
    obtain ⟨j, rfl⟩ := hc
    rw [pow_succ, pow_mul, sq, hδ2, one_pow, one_mul]
  refine ⟨q ^ c, heM, pow_mem hqo c, ?_, by rw [hρe]; exact hδ4⟩
  have hee : ρ ⟨q ^ c * q ^ c, le_normalizer (mul_mem heM heM)⟩ = 1 := by
    have h1 : (⟨q ^ c * q ^ c, le_normalizer (mul_mem heM heM)⟩ : ↥(normalizer (M : Set X))) =
        ⟨q ^ c, le_normalizer heM⟩ * ⟨q ^ c, le_normalizer heM⟩ := rfl
    rw [h1, map_mul, hρe, hδ2]
  have hcore : (⟨q ^ c * q ^ c, mul_mem heM heM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
    have h2 : (θ ((⟨q ^ c * q ^ c, mul_mem heM heM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) :
        Perm (Fin r)) = 1 := by
      rw [← hρ.apply_of_mem (by omega) ⟨q ^ c * q ^ c, mul_mem heM heM⟩]
      exact hee
    have h3 : θ ((⟨q ^ c * q ^ c, mul_mem heM heM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 :=
      Subtype.ext h2
    rw [← QuotientGroup.eq_one_iff]
    exact θ.injective (h3.trans (map_one θ).symm)
  have hodd : Odd (orderOf (q ^ c * q ^ c)) := by
    have h1 := orderOf_dvd_natCard
      (⟨⟨q ^ c * q ^ c, mul_mem heM heM⟩, hcore⟩ : ↥(pPrimeCore 2 ↥M))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
    exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card)
  have h2pow : orderOf (q ^ c * q ^ c) ∣ 2 ^ b := by
    have h1 : (q ^ c) ^ 2 ^ b = 1 := by
      rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    rw [← sq]
    exact (orderOf_pow_dvd 2).trans (orderOf_dvd_of_pow_eq_one h1)
  have h1 : orderOf (q ^ c * q ^ c) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hodd)) h2pow
  exact orderOf_eq_one_iff.mp h1

theorem not_mem_oddGen_of_four [Finite X] {e : X}
    (he : e ∈ normalizer (M : Set X)) (he2 : e * e = 1) (h4 : (ρ ⟨e, he⟩).support.card = 4)
    (hCN : centralizer ({e} : Set X) ≤ normalizer (M : Set X)) :
    e ∉ oddGen (centralizer ({e} : Set X)) := by
  classical
  set σ := ρ ⟨e, he⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨e, he⟩ : ↥(normalizer (M : Set X))) * ⟨e, he⟩ = 1 from
      Subtype.ext he2, map_one]
  let K : Subgroup X :=
    { carrier := {y | ∃ hy : y ∈ normalizer (M : Set X), ∀ x ∈ σ.support, ρ ⟨y, hy⟩ x = x}
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
        refine ⟨mul_mem h₁ h₂, fun x hx => ?_⟩
        have h3 : (⟨y₁ * y₂, mul_mem h₁ h₂⟩ : ↥(normalizer (M : Set X))) = ⟨y₁, h₁⟩ * ⟨y₂, h₂⟩ :=
          rfl
        rw [h3, map_mul, Perm.mul_apply, k₂ x hx, k₁ x hx]
      one_mem' := ⟨one_mem _, fun x _ => by
        rw [show (⟨1, one_mem _⟩ : ↥(normalizer (M : Set X))) = 1 from rfl, map_one]
        rfl⟩
      inv_mem' := by
        rintro y ⟨h, k⟩
        refine ⟨inv_mem h, fun x hx => ?_⟩
        have h3 : (⟨y⁻¹, inv_mem h⟩ : ↥(normalizer (M : Set X))) = (⟨y, h⟩)⁻¹ := rfl
        rw [h3, map_inv, Perm.inv_eq_iff_eq]
        exact (k x hx).symm }
  have hle : oddGen (centralizer ({e} : Set X)) ≤ K := by
    refine (closure_le _).mpr ?_
    rintro y ⟨hyC, hyo⟩
    show ∃ hy : y ∈ normalizer (M : Set X), ∀ x ∈ σ.support, ρ ⟨y, hy⟩ x = x
    refine ⟨hCN hyC, fun x hx => ?_⟩
    have hyσ : ρ ⟨y, hCN hyC⟩ * σ = σ * ρ ⟨y, hCN hyC⟩ := by
      rw [hσdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hyC)
    have h1 : Odd (orderOf (⟨y, hCN hyC⟩ : ↥(normalizer (M : Set X)))) := by
      rw [Subgroup.orderOf_mk]
      exact hyo
    exact apply_eq_of_odd_commute hσ2 h4.le hyσ (h1.of_dvd_nat (orderOf_map_dvd ρ _)) hx
  intro hmem
  obtain ⟨h, k⟩ : ∃ hy : e ∈ normalizer (M : Set X), ∀ x ∈ σ.support, ρ ⟨e, hy⟩ x = x :=
    hle hmem
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
  exact (Perm.mem_support.mp hx) (k x hx)

theorem IsPermAction.mem_oddGen_of_eight (hρ : IsPermAction θ ρ) [Finite X] (hr : 4 ≤ r)
    {H : Subgroup X} (hMH : M ≤ H)
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {v : X} (hvN : v ∈ normalizer (M : Set X)) (hvH : v ∈ H) (hv2 : v * v = 1)
    (hvA : ρ ⟨v, hvN⟩ ∈ alternatingGroup (Fin r)) (h8 : 8 ≤ (ρ ⟨v, hvN⟩).support.card) :
    v ∈ oddGen (centralizer ({v} : Set X)) := by
  have hσ2 : ρ ⟨v, hvN⟩ * ρ ⟨v, hvN⟩ = 1 := by
    rw [← map_mul, show (⟨v, hvN⟩ : ↥(normalizer (M : Set X))) * ⟨v, hvN⟩ = 1 from
      Subtype.ext hv2, map_one]
  obtain ⟨q, hq, hqo, hρq⟩ :=
    hρ.exists_lift_oddCentGen hr hvN hv2 (mem_oddCentGen_self hσ2 hvA h8)
  have hqvN : q⁻¹ * v ∈ normalizer (M : Set X) := mul_mem (inv_mem (le_normalizer hq)) hvN
  have hρ1 : ρ ⟨q⁻¹ * v, hqvN⟩ = 1 := by
    have h1 : (⟨q⁻¹ * v, hqvN⟩ : ↥(normalizer (M : Set X))) =
        (⟨q, le_normalizer hq⟩)⁻¹ * ⟨v, hvN⟩ := rfl
    rw [h1, map_mul, map_inv, hρq, inv_mul_cancel]
  have hodd := hker _ (mul_mem (inv_mem (hMH hq)) hvH) (hρ.mem_coreActionKernel hqvN hρ1)
  have hqC : q ∈ centralizer ({v} : Set X) := oddGen_le _ hqo
  have hvC : v ∈ centralizer ({v} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have h1 := mul_mem hqo (mem_oddGen (mul_mem (inv_mem hqC) hvC) hodd)
  rwa [mul_inv_cancel_left] at h1

end CFSG.ComponentClassification.SolMax
