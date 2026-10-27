module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem pow_card_conj_eq_of_stabilizes {P W : Subgroup G} {k : G}
    (hkW : ∀ w ∈ W, k * w * k⁻¹ = w)
    (hkP : ∀ p ∈ P, k * p * k⁻¹ * p⁻¹ ∈ W) :
    ∀ p ∈ P, k ^ Nat.card W * p * (k ^ Nat.card W)⁻¹ = p := by
  intro p hp
  set d : G := k * p * k⁻¹ * p⁻¹ with hddef
  have hdW : d ∈ W := hkP p hp
  have hkpd : k * p * k⁻¹ = d * p := by
    rw [hddef]
    group
  have hpow : ∀ j : ℕ, k ^ j * p * (k ^ j)⁻¹ = d ^ j * p := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        calc
          k ^ (j + 1) * p * (k ^ (j + 1))⁻¹
              = k * (k ^ j * p * (k ^ j)⁻¹) * k⁻¹ := by
                  rw [pow_succ]
                  group
          _ = k * (d ^ j * p) * k⁻¹ := by rw [ih]
          _ = (k * d ^ j * k⁻¹) * (k * p * k⁻¹) := by group
          _ = d ^ j * (d * p) := by
                rw [hkW _ (W.pow_mem hdW j), hkpd]
          _ = d ^ (j + 1) * p := by
                rw [pow_succ]
                group
  have hd1 : d ^ Nat.card W = 1 := by
    have h : (⟨d, hdW⟩ : W) ^ Nat.card W = 1 := pow_card_eq_one'
    have h' := congrArg Subtype.val h
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
  rw [hpow (Nat.card W), hd1, one_mul]

theorem mem_of_stabilizes_three {p : ℕ} [Fact p.Prime]
    {H Q Q₀ Z : Subgroup G} (hQp : IsPGroup p Q) (hZQ₀ : Z ≤ Q₀) (hQ₀Q : Q₀ ≤ Q)
    (hCQ : ∀ h ∈ H, (∀ q ∈ Q, h * q = q * h) → h ∈ Q)
    (hHQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hHQ₀ : ∀ h ∈ H, ∀ q ∈ Q₀, h * q * h⁻¹ ∈ Q₀)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z)
    (hO : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup p K →
      K ≤ Q)
    {k : G} (hkH : k ∈ H) (hkZ : ∀ z ∈ Z, k * z * k⁻¹ = z)
    (hkQ₀ : ∀ q ∈ Q₀, k * q * k⁻¹ * q⁻¹ ∈ Z)
    (hkQ : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ Q₀) :
    k ∈ Q := by
  let K : Subgroup G :=
    { carrier := {h | h ∈ H ∧ (∀ z ∈ Z, h * z * h⁻¹ = z) ∧
        (∀ q ∈ Q₀, h * q * h⁻¹ * q⁻¹ ∈ Z) ∧
        (∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ Q₀)}
      one_mem' := ⟨H.one_mem, fun z _ => by group,
        fun q _ => by
          rw [one_mul, inv_one, mul_one, mul_inv_cancel]
          exact Z.one_mem,
        fun q _ => by
          rw [one_mul, inv_one, mul_one, mul_inv_cancel]
          exact Q₀.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haH, haZ, haQ₀, haQ⟩ ⟨hbH, hbZ, hbQ₀, hbQ⟩
        refine ⟨H.mul_mem haH hbH, fun z hz => ?_, fun q hq => ?_, fun q hq => ?_⟩
        · calc a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
            _ = z := by rw [hbZ z hz, haZ z hz]
        · have h1 := hbQ₀ q hq
          have h2 := haQ₀ q hq
          have h3 : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ = b * q * b⁻¹ * q⁻¹ := haZ _ h1
          rw [show a * b * q * (a * b)⁻¹ * q⁻¹ =
              a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) by group, h3]
          exact Z.mul_mem h1 h2
        · have h1 := hbQ q hq
          have h2 := haQ q hq
          have h3 : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ ∈ Q₀ := hHQ₀ a haH _ h1
          rw [show a * b * q * (a * b)⁻¹ * q⁻¹ =
              a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) by group]
          exact Q₀.mul_mem h3 h2
      inv_mem' := by
        rintro a ⟨haH, haZ, haQ₀, haQ⟩
        refine ⟨H.inv_mem haH, fun z hz => ?_, fun q hq => ?_, fun q hq => ?_⟩
        · have h := haZ z hz
          calc a⁻¹ * z * (a⁻¹)⁻¹ = a⁻¹ * z * a := by group
            _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [h]
            _ = z := by group
        · have hq' : a⁻¹ * q * a ∈ Q₀ := by
            have := hHQ₀ a⁻¹ (H.inv_mem haH) q hq
            rwa [inv_inv] at this
          have h1 := haQ₀ (a⁻¹ * q * a) hq'
          have h2 : a * (a⁻¹ * q * a) * a⁻¹ * (a⁻¹ * q * a)⁻¹ =
              q * a⁻¹ * q⁻¹ * a := by group
          rw [h2] at h1
          have h3 : (q * a⁻¹ * q⁻¹ * a)⁻¹ = a⁻¹ * q * (a⁻¹)⁻¹ * q⁻¹ := by group
          have h4 := Z.inv_mem h1
          rwa [h3] at h4
        · have hq' : a⁻¹ * q * a ∈ Q := by
            have := hHQ a⁻¹ (H.inv_mem haH) q hq
            rwa [inv_inv] at this
          have h1 := haQ (a⁻¹ * q * a) hq'
          have h2 : a * (a⁻¹ * q * a) * a⁻¹ * (a⁻¹ * q * a)⁻¹ =
              q * a⁻¹ * q⁻¹ * a := by group
          rw [h2] at h1
          have h3 : (q * a⁻¹ * q⁻¹ * a)⁻¹ = a⁻¹ * q * (a⁻¹)⁻¹ * q⁻¹ := by group
          have h4 := Q₀.inv_mem h1
          rwa [h3] at h4 }
  have hKH : K ≤ H := fun h hh => hh.1
  have hKn : ∀ h ∈ H, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    rintro g hg x ⟨hxH, hxZ, hxQ₀, hxQ⟩
    refine ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), fun z hz => ?_,
      fun q hq => ?_, fun q hq => ?_⟩
    · have hzg : g⁻¹ * z * g ∈ Z := by
        have := hHZ g⁻¹ (H.inv_mem hg) z hz
        rwa [inv_inv] at this
      calc g * x * g⁻¹ * z * (g * x * g⁻¹)⁻¹
          = g * (x * (g⁻¹ * z * g) * x⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hxZ _ hzg]
        _ = z := by group
    · have hq' : g⁻¹ * q * g ∈ Q₀ := by
        have := hHQ₀ g⁻¹ (H.inv_mem hg) q hq
        rwa [inv_inv] at this
      have h1 := hxQ₀ (g⁻¹ * q * g) hq'
      have h2 : g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ ∈ Z :=
        hHZ g hg _ h1
      rw [show g * x * g⁻¹ * q * (g * x * g⁻¹)⁻¹ * q⁻¹ =
          g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ by group]
      exact h2
    · have hq' : g⁻¹ * q * g ∈ Q := by
        have := hHQ g⁻¹ (H.inv_mem hg) q hq
        rwa [inv_inv] at this
      have h1 := hxQ (g⁻¹ * q * g) hq'
      have h2 : g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ ∈ Q₀ :=
        hHQ₀ g hg _ h1
      rw [show g * x * g⁻¹ * q * (g * x * g⁻¹)⁻¹ * q⁻¹ =
          g * (x * (g⁻¹ * q * g) * x⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ by group]
      exact h2
  have hx1cent : ∀ x ∈ K, ∀ q ∈ Q₀, x ^ Nat.card Z * q * (x ^ Nat.card Z)⁻¹ = q := by
    intro x hx
    exact pow_card_conj_eq_of_stabilizes hx.2.1 hx.2.2.1
  have hx2cent : ∀ x ∈ K, ∀ q ∈ Q,
      (x ^ Nat.card Z) ^ Nat.card Q₀ * q * ((x ^ Nat.card Z) ^ Nat.card Q₀)⁻¹ = q := by
    intro x hx
    exact pow_card_conj_eq_of_stabilizes (P := Q) (W := Q₀)
      (hx1cent x hx) (K.pow_mem hx (Nat.card Z)).2.2.2
  have hKp : IsPGroup p K := by
    refine IsPGroup.iff_orderOf.mpr ?_
    intro x
    have hx1K : (x : G) ^ Nat.card Z ∈ K := K.pow_mem x.2 _
    have hx2K : ((x : G) ^ Nat.card Z) ^ Nat.card Q₀ ∈ K := K.pow_mem hx1K _
    have hx2Q : ((x : G) ^ Nat.card Z) ^ Nat.card Q₀ ∈ Q := by
      refine hCQ _ (hKH hx2K) ?_
      intro q hq
      have h := hx2cent (x : G) x.2 q hq
      calc ((x : G) ^ Nat.card Z) ^ Nat.card Q₀ * q
          = ((((x : G) ^ Nat.card Z) ^ Nat.card Q₀ * q *
              (((x : G) ^ Nat.card Z) ^ Nat.card Q₀)⁻¹) *
              ((x : G) ^ Nat.card Z) ^ Nat.card Q₀) := by group
        _ = q * ((x : G) ^ Nat.card Z) ^ Nat.card Q₀ := by rw [h]
    obtain ⟨n₀, hn₀⟩ := IsPGroup.iff_card.mp (hQp.to_le hQ₀Q)
    obtain ⟨nZ, hnZ⟩ := IsPGroup.iff_card.mp ((hQp.to_le hQ₀Q).to_le hZQ₀)
    let a : Q := ⟨((x : G) ^ Nat.card Z) ^ Nat.card Q₀, hx2Q⟩
    obtain ⟨n₂, hn₂⟩ := hQp.exists_orderOf_eq_pow a
    have hn₂' : orderOf (((x : G) ^ Nat.card Z) ^ Nat.card Q₀) = p ^ n₂ :=
      (Subgroup.orderOf_coe a).trans hn₂
    have hx2pow : (((x : G) ^ Nat.card Z) ^ Nat.card Q₀) ^ p ^ n₂ = 1 := by
      rw [← hn₂', pow_orderOf_eq_one]
    have hx2eq : ((x : G) ^ Nat.card Z) ^ Nat.card Q₀ =
        (x : G) ^ (Nat.card Z * Nat.card Q₀) := (pow_mul _ _ _).symm
    have hxpow : (x : G) ^ (Nat.card Z * Nat.card Q₀ * p ^ n₂) = 1 := by
      have h := hx2pow
      rw [hx2eq, ← pow_mul] at h
      exact h
    have hdvd : orderOf (x : G) ∣ Nat.card Z * Nat.card Q₀ * p ^ n₂ :=
      orderOf_dvd_of_pow_eq_one hxpow
    rw [hnZ, hn₀, ← pow_add, ← pow_add] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    exact ⟨j, (Subgroup.orderOf_coe x).symm.trans hj⟩
  exact hO K hKH hKn hKp ⟨hkH, hkZ, hkQ₀, hkQ⟩

theorem mem_of_stabilizes_two {p : ℕ} [Fact p.Prime]
    {H Q Z : Subgroup G} (hQp : IsPGroup p Q) (hZQ : Z ≤ Q)
    (hCQ : ∀ h ∈ H, (∀ q ∈ Q, h * q = q * h) → h ∈ Q)
    (hHQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z)
    (hO : ∀ K : Subgroup G, K ≤ H → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → IsPGroup p K →
      K ≤ Q)
    {k : G} (hkH : k ∈ H) (hkZ : ∀ z ∈ Z, k * z * k⁻¹ = z)
    (hkQ : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ Z) :
    k ∈ Q := by
  refine mem_of_stabilizes_three hQp le_rfl hZQ hCQ hHQ hHZ hHZ hO hkH hkZ ?_ hkQ
  intro q hq
  rw [hkZ q hq]
  exact Z.mul_mem hq (Z.inv_mem hq)

end CFSG.GroupTheory
