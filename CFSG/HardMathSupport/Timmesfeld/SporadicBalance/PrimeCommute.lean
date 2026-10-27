module

public import CFSG.RankThree.PartOne.S11c.HNCoverAbstract

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Subgroup

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  rw [← h]
  rfl

theorem not_dvd_card_centralizer_of_not_commute [Finite G] {q : ℕ} [Fact q.Prime]
    (hq : ¬ q ^ 2 ∣ Nat.card G) {u : G} (hu : orderOf u = q) {x : G}
    (hno : ∀ y : G, orderOf y = orderOf x → y * u ≠ u * y) :
    ¬ q ∣ Nat.card (centralizer ({x} : Set G)) := by
  intro hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({x} : Set G)) q hdvd
  have hw' : orderOf (w : G) = q := by rw [Subgroup.orderOf_coe]; exact hw
  obtain ⟨g, k, hgk⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_orderOf_prime hq hu hw'
  have hxw : (w : G) * x = x * w := mem_centralizer_singleton_iff.1 w.2
  have huk : orderOf (u ^ k) = q := by rw [← hgk, orderOf_conj_eq, hw']
  have hc : g * x * g⁻¹ * u ^ k = u ^ k * (g * x * g⁻¹) := by
    rw [← hgk]
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hxw]
      _ = g * w * g⁻¹ * (g * x * g⁻¹) := by group
  exact hno _ (orderOf_conj_eq g x)
    (CFSG.RankThree.PartOne.HNRed.commute_of_commute_pow hu huk hc)

theorem smul_eq_of_commute_of_ncard_lt {X : Type*} [MulAction G X] {p : ℕ} (hp : p.Prime)
    {u y : G} {x : X} (hy : orderOf y = p) (hc : y * u = u * y) (hux : u • x = x)
    (hF : {z : X | u • z = z}.Finite) (hlt : {z : X | u • z = z}.ncard < p) : y • x = x := by
  have hZ : zpowers y ≤ centralizer ({u} : Set G) :=
    zpowers_le.2 (mem_centralizer_singleton_iff.2 hc)
  have hsub : MulAction.orbit (zpowers y) x ⊆ {z : X | u • z = z} := by
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hgc : g * u = u * g := mem_centralizer_singleton_iff.1 (hZ hg)
    show u • (g • x) = g • x
    rw [← mul_smul, ← hgc, mul_smul, hux]
  have hle := Set.ncard_le_ncard hsub hF
  have hdvd : (MulAction.orbit (zpowers y) x).ncard ∣ p := by
    have h := Subgroup.card_mul_index (MulAction.stabilizer (zpowers y) x)
    rw [MulAction.index_stabilizer, Nat.card_zpowers, hy] at h
    exact Dvd.intro_left _ h
  have h1 : (MulAction.orbit (zpowers y) x).ncard = 1 := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact h
    · omega
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
  have h0 : x ∈ MulAction.orbit (zpowers y) x := MulAction.mem_orbit_self x
  have hy0 : y • x ∈ MulAction.orbit (zpowers y) x := ⟨⟨y, mem_zpowers y⟩, rfl⟩
  rw [ha, Set.mem_singleton_iff] at h0 hy0
  rw [hy0, h0]

theorem not_commute_of_card_centralizer {H : Subgroup G} {S : Type*} [Group S] (θ : H →* S)
    (hθ : Function.Injective θ) {p : ℕ} {u y : G} (hu : u ∈ H) (hy : y ∈ H) (hyp : orderOf y = p)
    (hcop : ¬ p ∣ Nat.card (centralizer ({θ ⟨u, hu⟩} : Set S))) : y * u ≠ u * y := by
  intro hc
  have hcH : (⟨y, hy⟩ : H) * ⟨u, hu⟩ = ⟨u, hu⟩ * ⟨y, hy⟩ := Subtype.ext hc
  have hmem : θ ⟨y, hy⟩ ∈ centralizer ({θ ⟨u, hu⟩} : Set S) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcH]
  have hord : orderOf (θ ⟨y, hy⟩) = p := by
    rw [orderOf_injective θ hθ, Subgroup.orderOf_mk]
    exact hyp
  have h := orderOf_dvd_natCard (⟨_, hmem⟩ : centralizer ({θ ⟨u, hu⟩} : Set S))
  rw [Subgroup.orderOf_mk, hord] at h
  exact hcop h

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
