module

public import CFSG.Open.GLADefs
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open CFSG.Open

variable {G : Type*} [Group G]

abbrev centerOf (C : Subgroup G) : Subgroup G :=
  (Subgroup.center C).map C.subtype

theorem mem_center_map_subtype {C : Subgroup G} {x : G} :
    x ∈ centerOf C ↔ x ∈ C ∧ ∀ c ∈ C, c * x = x * c := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun c hc => congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨c, hc⟩)⟩
  · rintro ⟨hxC, hx⟩
    exact ⟨⟨x, hxC⟩, Subgroup.mem_center_iff.2 fun c => Subtype.ext (hx c c.2), rfl⟩

theorem coprime_card_GLAPPrimeCore {p : ℕ} (hp : p.Prime) (X : Type*) [Group X] [Finite X] :
    Nat.Coprime p (Nat.card (GLAPPrimeCore p X)) := by
  set π : Set Nat.Primes := {q | q.val ≠ p}
  have hiff : ∀ N : Subgroup X, Nat.Coprime p (Nat.card N) ↔ CFSG.IsPiSubgroup π N := by
    intro N
    rw [hp.coprime_iff_not_dvd]
    constructor
    · intro hN q hq hqp
      exact hN (hqp ▸ hq)
    · intro hN hdvd
      exact hN ⟨p, hp⟩ hdvd rfl
  have heq : GLAPPrimeCore p X = CFSG.piCore π X := by
    unfold GLAPPrimeCore CFSG.pPrimeCore CFSG.piCore
    congr 1
    ext N
    exact and_congr_right fun _ => hiff N
  rw [hiff, heq]
  exact CFSG.LocalCores.piCore_isPiSubgroup π

theorem GLAPPrimeCoreOf_le (p : ℕ) (H : Subgroup G) : GLAPPrimeCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

theorem GLADelta_le_GLAPPrimeCoreOf (p : ℕ) {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    GLADelta p D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) :=
  iInf_le_of_le d (iInf_le_of_le hd (iInf_le_of_le hd1 le_rfl))

theorem commute_of_mem_GLADelta {p : ℕ} {D : Subgroup G} {x : G} (hx : x ∈ GLADelta p D)
    {d : G} (hd : d ∈ D) : d * x = x * d := by
  by_cases hd1 : d = 1
  · rw [hd1, one_mul, mul_one]
  have hx' := GLAPPrimeCoreOf_le p _ (GLADelta_le_GLAPPrimeCoreOf p hd hd1 hx)
  exact Subgroup.mem_centralizer_iff.1 hx' d rfl

theorem coprime_card_GLADelta [Finite G] {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : D ≠ ⊥) :
    Nat.Coprime p (Nat.card (GLADelta p D)) := by
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD
  have hle := GLADelta_le_GLAPPrimeCoreOf p hd (fun h => hd1 (Subtype.ext h))
  refine (coprime_card_GLAPPrimeCore hp
    (Subgroup.centralizer ({(d : G)} : Set G))).coprime_dvd_right
      ((Subgroup.card_dvd_of_le hle).trans ?_)
  rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

abbrev localDelta (p : ℕ) (H D : Subgroup G) : Subgroup G :=
  (GLADelta p (D.subgroupOf H)).map H.subtype

theorem localDelta_le_centralizer {p : ℕ} {H D : Subgroup G} (hDH : D ≤ H) :
    localDelta p H D ≤ Subgroup.centralizer (D : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_centralizer_iff.2 fun d hd => ?_
  have h := commute_of_mem_GLADelta (d := ⟨d, hDH hd⟩) hx (Subgroup.mem_subgroupOf.2 hd)
  exact congrArg Subtype.val h

theorem coprime_card_localDelta [Finite G] {p : ℕ} (hp : p.Prime) {H D : Subgroup G}
    (hDH : D ≤ H) (hD : D ≠ ⊥) : Nat.Coprime p (Nat.card (localDelta p H D)) := by
  have hD' : D.subgroupOf H ≠ ⊥ := fun h => hD (by
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_self.1 (h.mono_right hDH))
  rw [localDelta, Subgroup.card_map_of_injective H.subtype_injective]
  exact coprime_card_GLADelta hp hD'

theorem normal_of_commutator_mem {I : Subgroup G} (hcomm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ I) :
    I.Normal :=
  ⟨fun i hi g => by simpa using I.mul_mem (hcomm g i) hi⟩

theorem coprime_centralizer_central [Finite G] {p : ℕ} (hp : p.Prime) (I D : Subgroup G)
    (hcomm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ I) (hDI : D ≤ I)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcent : ∀ x ∈ I, (∀ d ∈ D, d * x = x * d) → x ∈ D) :
    Subgroup.centralizer (D : Set G) ⊓ I = D ∧ D ≤ centerOf (Subgroup.centralizer (D : Set G)) ∧
      (∀ a ∈ Subgroup.centralizer (D : Set G), ∀ b ∈ Subgroup.centralizer (D : Set G),
        a * b * a⁻¹ * b⁻¹ ∈ D) ∧
      (∀ Y : Subgroup G, Y ≤ Subgroup.centralizer (D : Set G) → Nat.Coprime p (Nat.card Y) →
        Y ≤ centerOf (Subgroup.centralizer (D : Set G))) ∧
      (D ≠ ⊥ → ∀ H : Subgroup G, D ≤ H →
        localDelta p H D ≤ centerOf (Subgroup.centralizer (D : Set G))) := by
  set C := Subgroup.centralizer (D : Set G) with hC
  have hDC : D ≤ C := fun d hd => Subgroup.mem_centralizer_iff.2 fun e he => hDab e he d hd
  have hCI : C ⊓ I = D := le_antisymm
    (fun x hx => hcent x hx.2 fun d hd => Subgroup.mem_centralizer_iff.1 hx.1 d hd)
    (le_inf hDC hDI)
  have hDZ : D ≤ centerOf C := fun d hd =>
    mem_center_map_subtype.2 ⟨hDC hd, fun c hc => (Subgroup.mem_centralizer_iff.1 hc d hd).symm⟩
  have hCD : ∀ a ∈ C, ∀ b ∈ C, a * b * a⁻¹ * b⁻¹ ∈ D := by
    intro a ha b hb
    rw [← hCI]
    exact Subgroup.mem_inf.2
      ⟨mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb), hcomm a b⟩
  have hY : ∀ Y : Subgroup G, Y ≤ C → Nat.Coprime p (Nat.card Y) → Y ≤ centerOf C := by
    intro Y hYC hYp y hy
    refine mem_center_map_subtype.2 ⟨hYC hy, fun c hc => ?_⟩
    obtain ⟨z, hz⟩ : ∃ z, z = y * c * y⁻¹ * c⁻¹ := ⟨_, rfl⟩
    have hzD : z ∈ D := hz ▸ hCD y (hYC hy) c hc
    have hzy : Commute z y :=
      ((mem_center_map_subtype.1 (hDZ hzD)).2 y (hYC hy)).symm
    have hpow : ∀ k : ℕ, y ^ k * c * (y ^ k)⁻¹ * c⁻¹ = z ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : y ^ k * c * (y ^ k)⁻¹ = z ^ k * c := by rw [← ih]; group
        calc y ^ (k + 1) * c * (y ^ (k + 1))⁻¹ * c⁻¹ =
            y * (y ^ k * c * (y ^ k)⁻¹) * y⁻¹ * c⁻¹ := by group
          _ = (y * z ^ k) * c * y⁻¹ * c⁻¹ := by rw [h1]; group
          _ = (z ^ k * y) * c * y⁻¹ * c⁻¹ := by rw [(hzy.pow_left k).eq]
          _ = z ^ (k + 1) := by rw [pow_succ, hz]; group
    have hzn : z ^ orderOf y = 1 := by
      rw [← hpow, pow_orderOf_eq_one]
      group
    have hcop : Nat.Coprime p (orderOf y) :=
      hYp.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Y hy)
    have hz1 : z = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hzn
      have h2 := orderOf_dvd_of_pow_eq_one (hDp z hzD)
      have h3 := Nat.dvd_gcd h1 h2
      rw [Nat.gcd_comm, hcop.gcd_eq_one] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    rw [hz1] at hz
    have h := congrArg (· * c) hz.symm
    simp only [one_mul, inv_mul_cancel_right] at h
    have h' := congrArg (· * y) h
    simp only [inv_mul_cancel_right] at h'
    exact h'.symm
  refine ⟨hCI, hDZ, hCD, hY, fun hD H hDH => hY _ (localDelta_le_centralizer hDH)
    (coprime_card_localDelta hp hDH hD)⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
