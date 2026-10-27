module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenAb
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenRed
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

@[expose] def Small16 {V : Type} [CommGroup V] (Y : Subgroup (MulAut V)) : Prop :=
  ⁅Y, Y⁆ = Y ∧ ∃ S : Set (MulAut V), S ⊆ (Y : Set (MulAut V)) ∧ Subgroup.closure S = Y ∧
    ∀ x ∈ S, x ^ 5 = 1 ∧ Nat.card (commV (Subgroup.zpowers x)) ≤ 16

section Stable

variable {G : Type} [Group G]

theorem stable_of_index_prime [Finite G] {Y E H : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hHE : H ≤ E) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card E = p * Nat.card H) (hYE : Y ≤ Subgroup.normalizer (E : Set G))
    (hYH : Y ≤ Subgroup.normalizer (H : Set G)) :
    ∀ x ∈ E, ∀ y ∈ Y, x⁻¹ * (y * x * y⁻¹) ∈ H := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  have : Fact p.Prime := ⟨hp⟩
  set H' : Subgroup ↥E := H.subgroupOf E with hH'
  have hnorm : H'.Normal := ⟨fun n hn g => by
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
      rw [hE g g.2 n n.2, mul_inv_cancel_right]
    rw [Subgroup.mem_subgroupOf]
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ H
    rw [h1]
    exact hn⟩
  have hcardH' : Nat.card H' = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHE).toEquiv
  have hQcard : Nat.card (↥E ⧸ H') = p := by
    have h1 := Subgroup.card_mul_index H'
    rw [← Subgroup.index_eq_card, hcardH'] at *
    have hpos : 0 < Nat.card H := Nat.card_pos
    have : Nat.card H * H'.index = Nat.card H * p := by rw [h1, hc, mul_comm]
    have := Nat.eq_of_mul_eq_mul_left hpos this
    rw [Subgroup.index_eq_card] at this
    exact this
  have hQcyc : IsCyclic (↥E ⧸ H') := isCyclic_of_prime_card hQcard
  have hyE : ∀ y : ↥Y, (y : G) ∈ Subgroup.normalizer (E : Set G) := fun y => hYE y.2
  have hmap : ∀ y : ↥Y, H'.map (normConj E y (hyE y)).toMonoidHom = H' := by
    intro y
    ext k
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hYH y.2) (a : G)).mp (Subgroup.mem_subgroupOf.mp ha))
    · intro hk
      refine ⟨normConj E (y : G)⁻¹ (inv_mem (hyE y)) k, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hYH y.2)) (k : G)).mp
          (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr (by simpa [coe_normConj] using this)
      · ext
        simp [coe_normConj, mul_assoc]
  let ρ : ↥Y →* MulAut (↥E ⧸ H') :=
    { toFun := fun y => QuotientGroup.congr H' H' (normConj E y (hyE y)) (hmap y)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H x =>
          show QuotientGroup.mk (normConj E ((1 : ↥Y) : G) (hyE 1) x) = QuotientGroup.mk x
          congr 1
          ext
          simp [coe_normConj]
      map_mul' := fun y y' => by
        ext q
        induction q using QuotientGroup.induction_on with
        | H x =>
          show QuotientGroup.mk (normConj E ((y * y' : ↥Y) : G) (hyE (y * y')) x) =
            QuotientGroup.mk (normConj E (y : G) (hyE y) (normConj E (y' : G) (hyE y') x))
          congr 1
          ext
          simp [coe_normConj, mul_assoc] }
  have hρ : ∀ y : ↥Y, ρ y = 1 := by
    have key := perfect_map_eq_one (M := (ZMod (Nat.card (↥E ⧸ H')))ˣ)
      (fun y : ↥Y => IsCyclic.mulAutMulEquiv (↥E ⧸ H') (ρ y)) (fun y y' => by
        rw [map_mul, map_mul])
    intro y
    exact (MulEquiv.map_eq_one_iff _).mp (key y)
  intro x hx y hy
  have h1 := congrArg (fun f : MulAut (↥E ⧸ H') => f (QuotientGroup.mk ⟨x, hx⟩)) (hρ ⟨y, hy⟩)
  have h2 : (QuotientGroup.mk ⟨x, hx⟩ : ↥E ⧸ H') =
      QuotientGroup.mk (normConj E y (hyE ⟨y, hy⟩) ⟨x, hx⟩) := h1.symm
  exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h2)

end Stable

section Elementary

variable {G : Type} [Group G]

theorem normalizer_mem_of_conj {K : Subgroup G} {y : G}
    (h1 : ∀ z ∈ K, y * z * y⁻¹ ∈ K) (h2 : ∀ z ∈ K, y⁻¹ * z * y ∈ K) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h1 z, fun hz => ?_⟩
  have := h2 _ hz
  simpa [mul_assoc] using this

theorem pow_eq_one_of_abelian_minimal [Finite G] {Y P : Subgroup G} (hY : ⁅Y, Y⁆ = Y) {p : ℕ}
    (hp : p.Prime) (hP : IsPGroup p P) (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → Y ≤ Subgroup.normalizer (Q : Set G) →
      Q ≤ Subgroup.centralizer (Y : Set G))
    (hne : ¬ P ≤ Subgroup.centralizer (Y : Set G)) : ∀ x ∈ P, x ^ p = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hx₀p⟩ := hcon
  let E : Subgroup G :=
    { carrier := {z | z ∈ P ∧ z ^ p = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  let Pp : Subgroup G :=
    { carrier := {z | ∃ x ∈ P, z = x ^ p}
      one_mem' := ⟨1, one_mem _, (one_pow _).symm⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨x, hx, hxa⟩ := ha
        obtain ⟨x', hx', hxb⟩ := hb
        exact ⟨x * x', mul_mem hx hx', by
          rw [hxa, hxb, (show Commute x x' from hcomm x hx x' hx').mul_pow]⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨x, hx, hxa⟩ := ha
        exact ⟨x⁻¹, inv_mem hx, by rw [hxa, inv_pow]⟩ }
  have hEP : E ≤ P := fun z hz => hz.1
  have hPpP : Pp ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact pow_mem hx p
  have hYE : Y ≤ Subgroup.normalizer (E : Set G) := by
    intro y hy
    have hyP := hYP hy
    refine normalizer_mem_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · exact ⟨(Subgroup.mem_normalizer_iff.mp hyP z).mp hz.1, by rw [conj_pow, hz.2]; group⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyP) z).mp hz.1
      exact ⟨by simpa using this, by
        rw [show y⁻¹ * z * y = y⁻¹ * z * y⁻¹⁻¹ by rw [inv_inv], conj_pow, hz.2]; group⟩
  have hYPp : Y ≤ Subgroup.normalizer (Pp : Set G) := by
    intro y hy
    have hyP := hYP hy
    refine normalizer_mem_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyP x).mp hx, by rw [conj_pow]⟩
    · obtain ⟨x, hx, rfl⟩ := hz
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyP) x).mp hx
      exact ⟨y⁻¹ * x * y⁻¹⁻¹, this, by rw [conj_pow, inv_inv]⟩
  have hEC : E ≤ Subgroup.centralizer (Y : Set G) :=
    hmin E (lt_of_le_of_ne hEP fun h => hx₀p (by
      have : x₀ ∈ E := h ▸ hx₀
      exact this.2)) hYE
  have hPpC : Pp ≤ Subgroup.centralizer (Y : Set G) := by
    refine hmin Pp (lt_of_le_of_ne hPpP fun h => ?_) hYPp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have hpow : ∀ j : ℕ, ∀ x ∈ P, ∃ w ∈ P, x = w ^ (p ^ j) := by
      intro j
      induction j with
      | zero => exact fun x hx => ⟨x, hx, by rw [pow_zero, pow_one]⟩
      | succ j ih =>
        intro x hx
        obtain ⟨w, hw, rfl⟩ := ih x hx
        have : w ∈ Pp := h ▸ hw
        obtain ⟨w', hw', rfl⟩ := this
        exact ⟨w', hw', by rw [← pow_mul, pow_succ]; ring_nf⟩
    obtain ⟨w, hw, hwx⟩ := hpow n x₀ hx₀
    have h1 : w ^ (p ^ n) = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := (⟨w, hw⟩ : ↥P))
      rw [hn] at this
      exact congrArg Subtype.val this
    have : x₀ = 1 := by rw [hwx, h1]
    exact hx₀p (by rw [this, one_pow])
  refine hne (le_centralizer_of_stable hY (N := E) (X := P) ?_ hEC ?_)
  · intro x hx
    refine normalizer_mem_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · have : x * z * x⁻¹ = z := by rw [hcomm x hx z hz.1, mul_inv_cancel_right]
      rw [this]; exact hz
    · have : x⁻¹ * z * x = z := by
        calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
          _ = x⁻¹ * (x * z) := by rw [hcomm x hx z hz.1]
          _ = z := by group
      rw [this]; exact hz
  · intro x hx y hy
    have hyxP : y * x * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hYP hy) x).mp hx
    refine ⟨mul_mem (inv_mem hx) hyxP, ?_⟩
    have hxp : x ^ p ∈ Subgroup.centralizer (Y : Set G) := hPpC ⟨x, hx, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hxp y hy
    have h2 : y * x ^ p * y⁻¹ = x ^ p := by
      rw [mul_inv_eq_iff_eq_mul]; exact hc
    rw [(show Commute x⁻¹ (y * x * y⁻¹) from
      (hcomm _ (inv_mem hx) _ hyxP)).mul_pow, inv_pow, conj_pow, h2, inv_mul_cancel]

end Elementary

section Abelian

variable {V : Type} [CommGroup V]

theorem mem_normalizer_of_hypConj_eq {g : MulAut V} {H : Subgroup (MulAut V)}
    (h : hypConj g H = H) : g ∈ Subgroup.normalizer (H : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : g * z * g⁻¹ ∈ hypConj g H := mem_hypConj.mpr ⟨z, hz, rfl⟩
    rwa [h] at h1
  · intro hz
    have h1 : g * z * g⁻¹ ∈ hypConj g H := by rw [h]; exact hz
    have h2 := mem_hypConj'.mp h1
    simpa [mul_assoc] using h2

theorem false_of_abelian_minimal [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y P : Subgroup (MulAut V)}
    (hY : Small16 Y) {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hP : IsPGroup p P)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hYP : Y ≤ Subgroup.normalizer (P : Set (MulAut V)))
    (hmin : ∀ Q : Subgroup (MulAut V), Q < P → Y ≤ Subgroup.normalizer (Q : Set (MulAut V)) →
      Q ≤ Subgroup.centralizer (Y : Set (MulAut V)))
    (hne : ¬ P ≤ Subgroup.centralizer (Y : Set (MulAut V))) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperf, S, hSY, hSgen, hS⟩ := hY
  have hexp : ∀ x ∈ P, x ^ p = 1 := pow_eq_one_of_abelian_minimal hperf hp hP hcomm hYP hmin hne
  have hPbot : P ≠ ⊥ := fun h => hne (h ▸ bot_le)
  have : Fintype ↥P := Fintype.ofFinite _
  have hoddP : Odd (Fintype.card ↥P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [← Nat.card_eq_fintype_card, hn]
    exact hpodd.pow
  obtain ⟨H, hHP, hHc, hHS⟩ := exists_stable_hyperplane hV P hoddP hp hpodd hcomm hexp hPbot S
    (fun x hx => hYP (hSY hx)) hS
  have hYH : Y ≤ Subgroup.normalizer (H : Set (MulAut V)) := by
    rw [← hSgen, Subgroup.closure_le]
    exact fun x hx => mem_normalizer_of_hypConj_eq (hHS x hx)
  have hHlt : H < P := lt_of_le_of_ne hHP fun h => by
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [h] at hHc
    nlinarith [hp.two_le]
  have hHC := hmin H hHlt hYH
  have hd := stable_of_index_prime hperf hcomm hHP hp hHc hYP hYH
  refine hne (le_centralizer_of_stable hperf (N := H) (X := P) ?_ hHC hd)
  intro x hx
  refine normalizer_mem_of_conj (fun z hz => ?_) (fun z hz => ?_)
  · have : x * z * x⁻¹ = z := by rw [hcomm x hx z (hHP hz), mul_inv_cancel_right]
    rw [this]; exact hz
  · have : x⁻¹ * z * x = z := by
      calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
        _ = x⁻¹ * (x * z) := by rw [hcomm x hx z (hHP hz)]
        _ = z := by group
    rw [this]; exact hz

end Abelian

end CFSG.CGT.PushingUpLit.CGT6
