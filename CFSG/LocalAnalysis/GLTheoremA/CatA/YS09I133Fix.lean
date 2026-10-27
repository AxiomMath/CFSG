module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Two

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LieType.BorelTits CFSG.LocalAnalysis.GLTheoremA.S10

theorem i133_fix_pCore_two {G : Type} [Group G] [Finite G] (α : MulAut G) {m : ℕ}
    (hm : Nat.Coprime m 2) (hα : α ^ m = 1) {Q : Subgroup G} (hQp : IsPGroup 2 ↥Q)
    (hQfix : ∀ x ∈ Q, α x = x) (hsize : twoPart (Nat.card G) ≤ 2 * Nat.card Q) :
    ∀ t ∈ pCoreOf 2 (Subgroup.normalizer (Q : Set G)), α t = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiter : ∀ x : G, (⇑α)^[m] x = x := by
    intro x
    have hpow : ∀ j : ℕ, (⇑α)^[j] x = (α ^ j) x := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
    rw [hpow, hα, MulAut.one_apply]
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN
  set R : Subgroup G := pCoreOf 2 N with hR
  have hQR : Q ≤ R := le_pCoreOf_normalizer 2 Q hQp
  have hRN : R ≤ N := pCoreOf_le 2 N
  have hRp : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 N
  have hNR : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R := fun n hn r hr =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 N hn) r).1 hr
  have hαQ : ∀ x, α x ∈ Q ↔ x ∈ Q := by
    intro x
    constructor
    · intro hx
      have h1 : α x = α (α x) := (hQfix _ hx).symm
      have h2 : x = α x := α.injective h1
      rw [h2]
      exact hx
    · intro hx
      rw [hQfix x hx]
      exact hx
  have hconj : ∀ n y : G, α n * α y * (α n)⁻¹ = α (n * y * n⁻¹) := by
    intro n y
    simp only [map_mul, map_inv]
  have hαN : ∀ n, α n ∈ N ↔ n ∈ N := by
    intro n
    have key : ∀ y : G, (α y ∈ Q ↔ α n * α y * (α n)⁻¹ ∈ Q) ↔ (y ∈ Q ↔ n * y * n⁻¹ ∈ Q) := by
      intro y
      rw [hconj, hαQ, hαQ]
    rw [hN, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro H y
      exact (key y).1 (H (α y))
    · intro H h
      obtain ⟨y, rfl⟩ := α.surjective h
      exact (key y).2 (H y)
  have hsubR : R.map α.toMonoidHom ≤ N := by
    rintro _ ⟨r, hr, rfl⟩
    exact (hαN r).2 (hRN hr)
  have hfwd : ∀ n ∈ N, ∀ g ∈ R.map α.toMonoidHom, n * g * n⁻¹ ∈ R.map α.toMonoidHom := by
    rintro n hn _ ⟨r, hr, rfl⟩
    obtain ⟨n', rfl⟩ := α.surjective n
    have hn' : n' ∈ N := (hαN n').1 hn
    refine Subgroup.mem_map.2 ⟨n' * r * n'⁻¹, hNR n' hn' r hr, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hnormR : N ≤ Subgroup.normalizer ((R.map α.toMonoidHom : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact hfwd n hn g hg
    · intro hg
      have h1 := hfwd n⁻¹ (N.inv_mem hn) _ hg
      have e : n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g := by group
      rw [e] at h1
      exact h1
  have hαR_sub : R.map α.toMonoidHom ≤ R :=
    le_pCoreOf_of_le_normalizer 2 hsubR hnormR (hRp.map α.toMonoidHom)
  have hαR : ∀ r ∈ R, α r ∈ R := fun r hr => hαR_sub (Subgroup.mem_map.2 ⟨r, hr, rfl⟩)
  have hRcard : Nat.card ↥R ≤ 2 * Nat.card ↥Q := by
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hRp
    have hdvd : 2 ^ b ∣ Nat.card G := hb ▸ Subgroup.card_subgroup_dvd_card R
    calc Nat.card ↥R = 2 ^ b := hb
      _ ≤ twoPart (Nat.card G) := i133_pow_two_le_twoPart Nat.card_pos.ne' hdvd
      _ ≤ 2 * Nat.card Q := hsize
  have hcoset : ∀ x ∈ R, ∀ y ∈ R, x ∉ Q → y ∉ Q → x⁻¹ * y ∈ Q := by
    intro x hx y hy hxQ hyQ
    set Q' : Subgroup ↥R := Q.subgroupOf R with hQ'
    have hcardQ' : Nat.card ↥Q' = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
    have hmul : Q'.index * Nat.card ↥Q' = Nat.card ↥R := Subgroup.index_mul_card Q'
    have hQpos : 0 < Nat.card ↥Q' := by
      rw [hcardQ']
      exact Nat.card_pos
    have hle2 : Q'.index ≤ 2 := by
      have h3 : Q'.index * Nat.card ↥Q' ≤ 2 * Nat.card ↥Q' := by
        rw [hmul, hcardQ']
        exact hRcard
      exact Nat.le_of_mul_le_mul_right h3 hQpos
    have hne1 : Q'.index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      have hxmem : (⟨x, hx⟩ : ↥R) ∈ Q' := by
        rw [h1]
        exact Subgroup.mem_top _
      exact hxQ (Subgroup.mem_subgroupOf.1 hxmem)
    have hne0 : Q'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : Q'.index = 2 := by omega
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.1 h2
    have hxnot : (⟨x, hx⟩ : ↥R) ∉ Q' := fun h => hxQ (Subgroup.mem_subgroupOf.1 h)
    have hynot : (⟨y, hy⟩ : ↥R) ∉ Q' := fun h => hyQ (Subgroup.mem_subgroupOf.1 h)
    have hxa : a * ⟨x, hx⟩ ∈ Q' := by
      rcases ha ⟨x, hx⟩ with h | h
      · exact h.1
      · exact absurd h.1 hxnot
    have hya : a * ⟨y, hy⟩ ∈ Q' := by
      rcases ha ⟨y, hy⟩ with h | h
      · exact h.1
      · exact absurd h.1 hynot
    have hprod := Q'.mul_mem (Q'.inv_mem hxa) hya
    have hmem := Subgroup.mem_subgroupOf.1 hprod
    have e : (((a * ⟨x, hx⟩)⁻¹ * (a * ⟨y, hy⟩) : ↥R) : G) = x⁻¹ * y := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at hmem
    exact hmem
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Q := by
    intro r hr
    by_cases hrQ : r ∈ Q
    · rw [hQfix r hrQ, inv_mul_cancel]
      exact Q.one_mem
    · exact hcoset r hr (α r) (hαR r hr) hrQ (fun h => hrQ ((hαQ r).1 h))
  intro t ht
  have htR : t ∈ R := ht
  set c : G := t⁻¹ * α t with hcdef
  have hcQ : c ∈ Q := hc t htR
  have hαt : α t = t * c := by
    rw [hcdef]
    group
  have hfixpow : ∀ j : ℕ, α (c ^ j) = c ^ j := fun j => hQfix _ (Q.pow_mem hcQ j)
  have hit : ∀ j : ℕ, (⇑α)^[j] t = t * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, hfixpow j, hαt, pow_succ', mul_assoc]
  have hcm : c ^ m = 1 := by
    have h1 : t * c ^ m = t := by
      rw [← hit m, hiter t]
    have h2 : t⁻¹ * (t * c ^ m) = t⁻¹ * t := by rw [h1]
    simpa using h2
  obtain ⟨k, hk⟩ := hQp ⟨c, hcQ⟩
  have hck : c ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.gcd m (2 ^ k) = 1 := Nat.Coprime.pow_right k hm
  have hgcd : c ^ (Nat.gcd m (2 ^ k)) = 1 := pow_gcd_eq_one.2 ⟨hcm, hck⟩
  rw [hcop, pow_one] at hgcd
  rw [hαt, hgcd, mul_one]

end CFSG.LocalAnalysis.GLTheoremA
