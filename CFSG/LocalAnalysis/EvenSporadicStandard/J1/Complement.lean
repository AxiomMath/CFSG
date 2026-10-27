module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Orbit

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

private theorem mem_zpowers_iff_of_mul_self_eq_one {U : Type*} [Group U] {c : U}
    (hc : c * c = 1) {x : U} : x ∈ zpowers c ↔ x = 1 ∨ x = c := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, hc, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hc, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

private theorem pow_apply_of_intertwine {X Y : Type*} [Group X] [Group Y] (θ : X → Y)
    (ψ : MulAut X) (φ : MulAut Y) (h : ∀ x, θ (ψ x) = φ (θ x)) (n : ℕ) (x : X) :
    θ ((ψ ^ n) x) = (φ ^ n) (θ x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

private theorem exists_restrict_aut {U : Type*} [Group U] (σ : MulAut U) (hσ : σ ^ 7 = 1)
    (W : Subgroup U) (hW : ∀ w ∈ W, σ w ∈ W) :
    ∃ τ : MulAut W, ∀ w : W, ((τ w : W) : U) = σ w := by
  have hpow : ∀ n : ℕ, ∀ w ∈ W, (σ ^ n) w ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; exact hw
    | succ n ih => intro w hw; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hW w hw)
  have hinv : ∀ w : U, σ.symm w = (σ ^ 6) w := by
    intro w
    rw [MulEquiv.symm_apply_eq, ← MulAut.mul_apply, ← pow_succ', hσ]
    rfl
  exact ⟨{ toFun := fun w => ⟨σ (w : U), hW w w.2⟩
           invFun := fun w => ⟨σ.symm (w : U), by rw [hinv]; exact hpow 6 w w.2⟩
           left_inv := fun w => Subtype.ext (σ.symm_apply_apply (w : U))
           right_inv := fun w => Subtype.ext (σ.apply_symm_apply (w : U))
           map_mul' := fun a b => Subtype.ext (map_mul σ (a : U) (b : U)) }, fun w => rfl⟩

theorem exists_complement_of_elementary_abelian {U : Type*} [Group U] [Finite U]
    (hU : Nat.card U = 16) (hcomm : ∀ a b : U, a * b = b * a) (hsq : ∀ a : U, a * a = 1)
    {c : U} (hc : c ≠ 1) (σ : MulAut U) (hσ : orderOf σ = 7) (hσc : σ c = c)
    (hfree : ∀ u : U, σ u * u⁻¹ ∈ zpowers c → u ∈ zpowers c) :
    ∃ W : Subgroup U, Nat.card W = 8 ∧ c ∉ W ∧ (∀ w ∈ W, σ w ∈ W) ∧
      (∀ u : U, u ∈ W ∨ u * c ∈ W) ∧
      ∀ a ∈ W, a ≠ 1 → ∀ b ∈ W, b ≠ 1 → ∃ i : ℕ, (σ ^ i) a = b := by
  classical
  have hσ7 : σ ^ 7 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hmul : ∀ a b : U, σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
    intro a b
    rw [map_mul, mul_inv_rev]
    calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * ((σ b * b⁻¹) * a⁻¹) := by group
      _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [hcomm (σ b * b⁻¹) a⁻¹]
      _ = σ a * a⁻¹ * (σ b * b⁻¹) := by group
  let δ : U →* U := MonoidHom.mk' (fun u => σ u * u⁻¹) hmul
  have hδ : ∀ u, δ u = σ u * u⁻¹ := fun u => rfl
  have hc2 : c * c = 1 := hsq c
  have hcord : orderOf c = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hc2) hc
  have hcW : c ∉ δ.range := by
    rintro ⟨u, hu⟩
    rw [hδ] at hu
    have h1 : σ u = c * u := by rw [← hu]; group
    have h2 : (σ ^ 2) u = u := by
      rw [pow_two, MulAut.mul_apply, h1, map_mul, hσc, h1, ← mul_assoc, hc2, one_mul]
    have h3 : ∀ n : ℕ, (σ ^ (2 * n)) u = u := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Nat.mul_succ, pow_add, MulAut.mul_apply, h2, ih]
    have h4 : σ u = u := by
      have h8 : σ ^ (2 * 4) = σ := by
        rw [show 2 * 4 = 7 + 1 from rfl, pow_succ, hσ7, one_mul]
      calc σ u = (σ ^ (2 * 4)) u := by rw [h8]
        _ = u := h3 4
    apply hc
    rw [← hu, h4, mul_inv_cancel]
  have hker : δ.ker = zpowers c := by
    ext u
    constructor
    · intro hu
      have hu' : σ u = u := by
        rw [MonoidHom.mem_ker, hδ, mul_inv_eq_one] at hu
        exact hu
      apply hfree
      rw [hu', mul_inv_cancel]
      exact one_mem _
    · intro hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [MonoidHom.mem_ker, hδ, map_zpow, hσc, mul_inv_cancel]
  have hkercard : Nat.card δ.ker = 2 := by rw [hker, Nat.card_zpowers, hcord]
  have hWcard : Nat.card δ.range = 8 := by
    have h := Subgroup.card_ker_mul_card_range δ
    rw [hkercard, hU] at h
    omega
  have hindex : δ.range.index = 2 := by
    have h := Subgroup.card_mul_index δ.range
    rw [hWcard, hU] at h
    omega
  have hinv : ∀ w ∈ δ.range, σ w ∈ δ.range := by
    rintro _ ⟨u, rfl⟩
    refine ⟨σ u, ?_⟩
    rw [hδ, hδ, map_mul, map_inv]
  refine ⟨δ.range, hWcard, hcW, hinv, fun u => ?_, ?_⟩
  · by_cases hu : u ∈ δ.range
    · exact Or.inl hu
    · right
      rw [mul_mem_iff_of_index_two hindex]
      exact iff_of_false hu hcW
  · intro a ha ha1 b hb hb1
    obtain ⟨τ, hτ⟩ := exists_restrict_aut σ hσ7 δ.range hinv
    have hτpow : ∀ (n : ℕ) (w : δ.range), ((τ ^ n) w : U) = (σ ^ n) w := fun n w =>
      pow_apply_of_intertwine (fun w : δ.range => (w : U)) τ σ (fun w => hτ w) n w
    have hτ7 : τ ^ 7 = 1 := by
      ext w
      rw [hτpow, hσ7]
      rfl
    have hfixW : ∀ x : δ.range, σ x = x → x = 1 := by
      intro x hx
      have hxk : (x : U) ∈ zpowers c := by
        rw [← hker, MonoidHom.mem_ker, hδ, hx, mul_inv_cancel]
      rcases (mem_zpowers_iff_of_mul_self_eq_one hc2).mp hxk with h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ x.2) hcW
    have hτ1 : τ ≠ 1 := by
      intro h
      have : Nontrivial δ.range := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨w, hw⟩ := exists_ne (1 : δ.range)
      apply hw
      apply hfixW
      have h1 := hτ w
      rw [h] at h1
      exact h1.symm
    have hτord : orderOf τ = 7 := by
      have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      exact orderOf_eq_prime hτ7 hτ1
    obtain ⟨-, htrans⟩ := orbit_of_prime_order hWcard τ hτord
    obtain ⟨i, hi⟩ := htrans ⟨a, ha⟩ ⟨b, hb⟩ (fun h => ha1 (congrArg Subtype.val h))
      (fun h => hb1 (congrArg Subtype.val h))
    have hi' := congrArg Subtype.val hi
    rw [hτpow] at hi'
    exact ⟨i, hi'⟩

theorem exists_complement_quotient {R : Type*} [Group R] [Finite R] (N : Subgroup R) [N.Normal]
    (hcard : Nat.card R = 16 * Nat.card N) {c : R} (hcN : c ∉ N) (hc2 : c * c = 1)
    (hcc : ∀ r : R, c * r * c⁻¹ * r⁻¹ ∈ N) (τ : MulAut R) (hτN : ∀ r : R, τ r ∈ N ↔ r ∈ N)
    (hτ7 : τ ^ 7 = 1) (hτc : τ c = c)
    (hfree : ∀ r : R, (τ r * r⁻¹ ∈ N ∨ τ r * r⁻¹ * c ∈ N) → (r ∈ N ∨ r * c ∈ N)) :
    (∀ a b : R, a * b * a⁻¹ * b⁻¹ ∈ N) ∧ (∀ a : R, a * a ∈ N) ∧
    ∃ W : Subgroup R, N ≤ W ∧ c ∉ W ∧ Nat.card R = 2 * Nat.card W ∧
      (∀ w ∈ W, τ w ∈ W) ∧ (∀ r : R, r ∈ W ∨ r * c ∈ W) ∧
      ∀ a ∈ W, a ∉ N → ∀ b ∈ W, b ∉ N → ∃ i : ℕ, (τ ^ i) a * b⁻¹ ∈ N := by
  classical
  have hU : Nat.card (R ⧸ N) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hpos : 0 < Nat.card N := Nat.card_pos
    rw [hcard] at h
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have hmap : N.map (τ : R →* R) = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hτN y).mpr hy
    · intro hx
      refine ⟨τ.symm x, (hτN _).mp ?_, τ.apply_symm_apply x⟩
      rw [MulEquiv.apply_symm_apply]
      exact hx
  let σ : MulAut (R ⧸ N) := QuotientGroup.congr N N τ hmap
  have hσmk : ∀ r : R, σ (r : R ⧸ N) = ((τ r : R) : R ⧸ N) := fun r => rfl
  have hσpow : ∀ (n : ℕ) (r : R), (σ ^ n) (r : R ⧸ N) = (((τ ^ n) r : R) : R ⧸ N) := fun n r =>
    (pow_apply_of_intertwine QuotientGroup.mk τ σ (fun r => rfl) n r).symm
  have hc1 : (c : R ⧸ N) ≠ 1 := fun h => hcN ((QuotientGroup.eq_one_iff c).mp h)
  have hc'2 : (c : R ⧸ N) * c = 1 := by rw [← QuotientGroup.mk_mul, hc2, QuotientGroup.mk_one]
  have hc'ord : orderOf (c : R ⧸ N) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hc'2) hc1
  have hcentral : ∀ u : R ⧸ N, u * c = c * u := by
    intro u
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective u
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    have h : r * c / (c * r) = (c * r * c⁻¹ * r⁻¹)⁻¹ := by
      rw [div_eq_mul_inv]
      group
    rw [h]
    exact N.inv_mem (hcc r)
  have hσc : σ (c : R ⧸ N) = c := by rw [hσmk, hτc]
  have hσ7 : σ ^ 7 = 1 := by
    ext q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hσpow, hτ7]
    rfl
  have hfreeU : ∀ u : R ⧸ N, σ u * u⁻¹ ∈ zpowers (c : R ⧸ N) → u ∈ zpowers (c : R ⧸ N) := by
    intro u hu
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective u
    have h1 : σ (r : R ⧸ N) * (r : R ⧸ N)⁻¹ = ((τ r * r⁻¹ : R) : R ⧸ N) := by
      rw [hσmk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h1, mem_zpowers_iff_of_mul_self_eq_one hc'2] at hu
    rw [mem_zpowers_iff_of_mul_self_eq_one hc'2]
    have hr := hfree r (by
      rcases hu with h | h
      · exact Or.inl ((QuotientGroup.eq_one_iff _).mp h)
      · right
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, h, hc'2])
    rcases hr with h | h
    · exact Or.inl ((QuotientGroup.eq_one_iff r).mpr h)
    · right
      have h' : (r : R ⧸ N) * c = 1 := by
        rw [← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq_one_iff _).mpr h
      rw [eq_inv_of_mul_eq_one_left h', inv_eq_of_mul_eq_one_right hc'2]
  have hσ1 : σ ≠ 1 := by
    intro h
    have hall : ∀ u : R ⧸ N, u ∈ zpowers (c : R ⧸ N) := by
      intro u
      apply hfreeU
      rw [h, MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    have h16 : Nat.card (zpowers (c : R ⧸ N)) = Nat.card (R ⧸ N) := by
      rw [(Subgroup.eq_top_iff' _).mpr hall, Subgroup.card_top]
    rw [Nat.card_zpowers, hc'ord, hU] at h16
    omega
  have hσord : orderOf σ = 7 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact orderOf_eq_prime hσ7 hσ1
  obtain ⟨hab, hexp⟩ := abelian_of_central_extension hU hc'ord hcentral σ hσord hσc hfreeU
  obtain ⟨W, hWcard, hcW, hWσ, hcover, htrans⟩ :=
    exists_complement_of_elementary_abelian hU hab hexp hc1 σ hσord hσc hfreeU
  refine ⟨fun a b => ?_, fun a => ?_, W.comap (QuotientGroup.mk' N), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab (a : R ⧸ N) b]
    group
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_mul]
    exact hexp _
  · intro n hn
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  · exact hcW
  · have h1 := Subgroup.card_mul_index (W.comap (QuotientGroup.mk' N))
    rw [Subgroup.index_comap_of_surjective W (QuotientGroup.mk'_surjective N)] at h1
    have h2 := Subgroup.card_mul_index W
    rw [hWcard, hU] at h2
    have hidx : W.index = 2 := by omega
    rw [hidx] at h1
    omega
  · intro w hw
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hw
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, ← hσmk]
    exact hWσ _ hw
  · intro r
    rcases hcover (r : R ⧸ N) with h | h
    · exact Or.inl h
    · right
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
      exact h
  · intro a ha haN b hb hbN
    obtain ⟨i, hi⟩ := htrans a ha (by rwa [Ne, QuotientGroup.eq_one_iff]) b hb
      (by rwa [Ne, QuotientGroup.eq_one_iff])
    rw [hσpow] at hi
    have := QuotientGroup.eq_iff_div_mem.mp hi
    rw [div_eq_mul_inv] at this
    exact ⟨i, this⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_complement {R Λ : Subgroup G} (hΛR : Λ ≤ R)
    (hΛn : ∀ r ∈ R, ∀ l ∈ Λ, r * l * r⁻¹ ∈ Λ)
    (hcard : Nat.card R = 16 * Nat.card Λ)
    {c : G} (hcR : c ∈ R) (hcΛ : c ∉ Λ) (hc2 : c * c = 1)
    (hccentral : ∀ r ∈ R, c * r * c⁻¹ * r⁻¹ ∈ Λ)
    {σ : G} (hσR : σ ∈ normalizer (R : Set G)) (hσΛ : σ ∈ normalizer (Λ : Set G))
    (hσ7 : σ ^ 7 = 1) (hσc : σ * c * σ⁻¹ = c)
    (hfree : ∀ r ∈ R, (σ * r * σ⁻¹ * r⁻¹ ∈ Λ ∨ σ * r * σ⁻¹ * r⁻¹ * c ∈ Λ) →
      (r ∈ Λ ∨ r * c ∈ Λ)) :
    (∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Λ) ∧ (∀ a ∈ R, a * a ∈ Λ) ∧
    ∃ W : Subgroup G, W ≤ R ∧ Λ ≤ W ∧ c ∉ W ∧ Nat.card R = 2 * Nat.card W ∧
      (∀ w ∈ W, σ * w * σ⁻¹ ∈ W) ∧ (∀ r ∈ R, r ∈ W ∨ r * c ∈ W) ∧
      ∀ a ∈ W, a ∉ Λ → ∀ b ∈ W, b ∉ Λ → ∃ i : ℕ, (σ ^ i * a * (σ ^ i)⁻¹) * b⁻¹ ∈ Λ := by
  classical
  have hN : (Λ.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff hΛR).mpr fun l r hl hr => hΛn r hr l hl
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut R, ∀ r : R, ((τ r : R) : G) = σ * r * σ⁻¹ :=
    ⟨Subgroup.normalizerMonoidHom R ⟨σ, hσR⟩, fun r => rfl⟩
  have hτpow : ∀ (n : ℕ) (r : R), ((τ ^ n) r : G) = σ ^ n * r * (σ ^ n)⁻¹ := by
    intro n r
    have h := pow_apply_of_intertwine (fun r : R => (r : G)) τ (MulAut.conj σ)
      (fun r => (hτ r).trans (MulAut.conj_apply σ r).symm) n r
    rw [h, ← map_pow (MulAut.conj : G →* MulAut G) σ n, MulAut.conj_apply]
  have hτ7 : τ ^ 7 = 1 := by
    ext r
    rw [hτpow, hσ7]
    simp
  have hNcard : Nat.card (Λ.subgroupOf R) = Nat.card Λ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛR).toEquiv
  have hτN : ∀ r : R, τ r ∈ Λ.subgroupOf R ↔ r ∈ Λ.subgroupOf R := by
    intro r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hτ]
    exact (Subgroup.mem_normalizer_iff.mp hσΛ r).symm
  have hτc : τ ⟨c, hcR⟩ = ⟨c, hcR⟩ := Subtype.ext (by rw [hτ]; exact hσc)
  have hfreeR : ∀ r : R, (τ r * r⁻¹ ∈ Λ.subgroupOf R ∨
      τ r * r⁻¹ * ⟨c, hcR⟩ ∈ Λ.subgroupOf R) →
      (r ∈ Λ.subgroupOf R ∨ r * ⟨c, hcR⟩ ∈ Λ.subgroupOf R) := by
    intro r hr
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hτ] at hr ⊢
    exact hfree r r.2 hr
  obtain ⟨hcomm, hsq, W, hNW, hcW, hWcard, hWτ, hcover, htrans⟩ :=
    exists_complement_quotient (Λ.subgroupOf R) (by rw [hNcard]; exact hcard)
      (c := ⟨c, hcR⟩) (fun h => hcΛ (Subgroup.mem_subgroupOf.mp h)) (Subtype.ext hc2)
      (fun r => Subgroup.mem_subgroupOf.mpr (hccentral r r.2)) τ hτN hτ7 hτc hfreeR
  refine ⟨fun a ha b hb => Subgroup.mem_subgroupOf.mp (hcomm ⟨a, ha⟩ ⟨b, hb⟩),
    fun a ha => Subgroup.mem_subgroupOf.mp (hsq ⟨a, ha⟩), W.map R.subtype, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact Subgroup.map_subtype_le W
  · intro l hl
    exact Subgroup.mem_map.mpr ⟨⟨l, hΛR hl⟩, hNW (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  · intro hcm
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp hcm
    have hxc' : x = ⟨c, hcR⟩ := Subtype.ext hxc
    rw [hxc'] at hx
    exact hcW hx
  · rw [Subgroup.card_subtype]
    exact hWcard
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    exact Subgroup.mem_map.mpr ⟨τ x, hWτ x hx, hτ x⟩
  · intro r hr
    rcases hcover ⟨r, hr⟩ with h | h
    · exact Or.inl (Subgroup.mem_map.mpr ⟨_, h, rfl⟩)
    · exact Or.inr (Subgroup.mem_map.mpr ⟨_, h, rfl⟩)
  · intro a ha haΛ b hb hbΛ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨i, hi⟩ := htrans x hx (fun h => haΛ (Subgroup.mem_subgroupOf.mp h)) y hy
      (fun h => hbΛ (Subgroup.mem_subgroupOf.mp h))
    refine ⟨i, ?_⟩
    have h := Subgroup.mem_subgroupOf.mp hi
    rwa [Subgroup.coe_mul, hτpow, Subgroup.coe_inv] at h

end CFSG.EvenSporadicStandard.J1Std
