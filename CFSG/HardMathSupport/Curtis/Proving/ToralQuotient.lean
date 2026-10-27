module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Curtis.Proving

variable {G : Type*} [Group G]

theorem card_quotient_eq_relIndex (T X : Subgroup G) :
    Nat.card (T ⧸ X.subgroupOf T) = X.relIndex T := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]

theorem subgroupOf_normal_of_comm {T X : Subgroup G}
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) :
    (X.subgroupOf T).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := hcomm (g : G) g.2 (n : G) n.2
  have e : (g : G) * n * (g : G)⁻¹ = ((g : G) * n * (g : G)⁻¹ * (n : G)⁻¹) * n := by group
  have key : (g : G) * n * (g : G)⁻¹ ∈ X := by
    rw [e]
    exact X.mul_mem h hn
  exact key

theorem quotient_mul_comm {T X : Subgroup G} [(X.subgroupOf T).Normal]
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) (x y : T ⧸ X.subgroupOf T) :
    x * y = y * x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h := hcomm ((b : G))⁻¹ (T.inv_mem b.2) ((a : G))⁻¹ (T.inv_mem a.2)
      simpa [mul_assoc] using h

theorem quotient_pow_eq_one {p : ℕ} {T X : Subgroup G} [(X.subgroupOf T).Normal]
    (hpow : ∀ a ∈ T, a ^ p ∈ X) (x : T ⧸ X.subgroupOf T) : x ^ p = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hpow (a : G) a.2

theorem quotient_orderOf_eq {p : ℕ} [hp : Fact p.Prime] {T X : Subgroup G}
    [(X.subgroupOf T).Normal] (hpow : ∀ a ∈ T, a ^ p ∈ X)
    {t : G} (ht : t ∈ T) (htX : t ∉ X) :
    orderOf (QuotientGroup.mk (⟨t, ht⟩ : T) : T ⧸ X.subgroupOf T) = p := by
  have hne : (QuotientGroup.mk (⟨t, ht⟩ : T) : T ⧸ X.subgroupOf T) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact htX h
  have hdvd : orderOf (QuotientGroup.mk (⟨t, ht⟩ : T) : T ⧸ X.subgroupOf T) ∣ p :=
    orderOf_dvd_of_pow_eq_one (quotient_pow_eq_one hpow _)
  rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h1

theorem exists_proper_intermediate {p : ℕ} [hp : Fact p.Prime] {T X : Subgroup G}
    (hXT : X ≤ T)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) (hpow : ∀ a ∈ T, a ^ p ∈ X)
    (hidx : X.relIndex T = p ^ 4) {t : G} (ht : t ∈ T) (htX : t ∉ X) :
    ∃ V : Subgroup G, X ≤ V ∧ V ≤ T ∧ t ∈ V ∧ V ≠ T := by
  have := subgroupOf_normal_of_comm hcomm
  let y : T ⧸ X.subgroupOf T := QuotientGroup.mk (⟨t, ht⟩ : T)
  let VT : Subgroup T := (Subgroup.zpowers y).comap (QuotientGroup.mk' (X.subgroupOf T))
  refine ⟨VT.map T.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxT : x ∈ T := hXT hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, ?_, rfl⟩
    have h1 : (QuotientGroup.mk' (X.subgroupOf T)) ⟨x, hxT⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
    show (QuotientGroup.mk' (X.subgroupOf T)) ⟨x, hxT⟩ ∈ Subgroup.zpowers y
    rw [h1]
    exact Subgroup.one_mem _
  · intro v hv
    obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.mp hv
    exact a.2
  · refine Subgroup.mem_map.mpr ⟨⟨t, ht⟩, ?_, rfl⟩
    show y ∈ Subgroup.zpowers y
    exact Subgroup.mem_zpowers y
  · intro hVT
    have hall : ∀ a : T, (QuotientGroup.mk' (X.subgroupOf T)) a ∈ Subgroup.zpowers y := by
      intro a
      have haV : (a : G) ∈ VT.map T.subtype := by rw [hVT]; exact a.2
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp haV
      have hab : b = a := Subtype.ext hba
      have hb' : (QuotientGroup.mk' (X.subgroupOf T)) b ∈ Subgroup.zpowers y := hb
      rw [hab] at hb'
      exact hb'
    have htop : Subgroup.zpowers y = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (X.subgroupOf T) q
      exact hall a
    have hcardQ : Nat.card (T ⧸ X.subgroupOf T) = p ^ 4 := by
      rw [card_quotient_eq_relIndex, hidx]
    have hcardZ : Nat.card (Subgroup.zpowers y) = p := by
      rw [Nat.card_zpowers, quotient_orderOf_eq hpow ht htX]
    have h1 : Nat.card (Subgroup.zpowers y) = Nat.card (T ⧸ X.subgroupOf T) := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hcardZ, hcardQ] at h1
    have hp2 := hp.out.two_le
    have hlt : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp2 (by decide)
    rw [pow_one, ← h1] at hlt
    exact lt_irrefl _ hlt

theorem not_premise_of_trivial_action {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y]
    {T X : Subgroup Y} {c : Y}
    (hXT : X ≤ T)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) (hpow : ∀ a ∈ T, a ^ p ∈ X)
    (hidx : X.relIndex T = p ^ 4)
    (hact : ∀ t ∈ T, c * t * c⁻¹ * t⁻¹ ∈ X)
    {t : Y} (ht : t ∈ T) (htX : t ∉ X) :
    ¬ (∀ V : Subgroup Y, X ≤ V → V ≤ T → (∀ s ∈ T, ∀ v ∈ V, s * v * s⁻¹ ∈ V) →
        (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T) := by
  intro hprem
  obtain ⟨V, hXV, hVT, htV, hVne⟩ := exists_proper_intermediate hXT hcomm hpow hidx ht htX
  have hconj : ∀ s ∈ T, ∀ v ∈ V, s * v * s⁻¹ ∈ V := by
    intro s hs v hv
    have hvT : v ∈ T := hVT hv
    have hX : s * v * s⁻¹ * v⁻¹ ∈ X := hcomm s hs v hvT
    have : s * v * s⁻¹ = (s * v * s⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V.mul_mem (hXV hX) hv
  have hcinv : ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    intro v hv
    have hvT : v ∈ T := hVT hv
    have hX : c * v * c⁻¹ * v⁻¹ ∈ X := hact v hvT
    have : c * v * c⁻¹ = (c * v * c⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V.mul_mem (hXV hX) hv
  rcases hprem V hXV hVT hconj hcinv with h | h
  · exact htX (h ▸ htV)
  · exact hVne h

end CFSG.HardMathSupport.Curtis.Proving

end
