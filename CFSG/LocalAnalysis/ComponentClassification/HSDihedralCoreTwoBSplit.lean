module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoB

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

theorem exists_pow_involution {G : Type} [Group G] {g : G} (hg : ∃ m : ℕ, g ^ 2 ^ m = 1)
    (hg1 : g ≠ 1) : ∃ j : ℕ, (g ^ j) ^ 2 = 1 ∧ g ^ j ≠ 1 := by
  classical
  set m := Nat.find hg
  have hm : g ^ 2 ^ m = 1 := Nat.find_spec hg
  have hm0 : m ≠ 0 := fun h => hg1 (by rw [h, pow_zero, pow_one] at hm; exact hm)
  refine ⟨2 ^ (m - 1), ?_, Nat.find_min hg (by omega)⟩
  rw [← pow_mul, ← pow_succ, show m - 1 + 1 = m by omega, hm]

namespace LocalDatum

variable {Δ : LocalDatum X A}

theorem pow_dn_eq_one {d : X} (hd : d ∈ Δ.D) : d ^ Δ.dn = 1 := by
  obtain ⟨g, rfl⟩ := Δ.exists_dE hd
  have h2 : 2 ∣ Δ.dn := even_iff_two_dvd.mp Δ.even_dn
  have hg : g ^ Δ.dn = 1 := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (by rw [DihedralGroup.exponent]; exact Nat.lcm_dvd (dvd_refl _) h2)) g
  rw [← Δ.dE_pow, hg, Δ.dE_one]

variable {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

include h2 in
theorem TwoB_pow_R (hsplit : ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) {r : A} (hr : r ∈ Δ.R) :
    r ^ Δ.dn = 1 := by
  have hpow : ∀ y ∈ Δ.Dbar, y ^ Δ.dn = 1 := fun y hy => by
    obtain ⟨d, hd, rfl⟩ := (Δ.mem_Dbar_iff).mp hy
    rw [← Δ.ψe_pow (Δ.D_le hd), pow_dn_eq_one hd, Δ.ψe_one]
  rcases hsplit r hr with h | h
  · exact hpow r h
  · have hk2 := h2.2.2.2.1
    have hkc : Commute (r * k) k := by
      change r * k * k = k * (r * k)
      exact (h2.2.1 _ h).symm
    have hkn : k ^ Δ.dn = 1 := by
      obtain ⟨c, hc⟩ := Δ.even_dn
      rw [hc, ← two_mul, pow_mul, hk2, one_pow]
    have : r = r * k * k⁻¹ := by group
    rw [this, (hkc.inv_right).mul_pow, hpow _ h, inv_pow, hkn, inv_one, one_mul]

include h2 φ in
theorem TwoB_pow_Q (hsplit : ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) {q : X} (hq : q ∈ Δ.Q) :
    q ^ Δ.dn = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hvS : φ.x * q * φ.x⁻¹ ∈ Δ.S := φ.conj_mem q (Δ.Q_le hq)
  have hvQ : (φ.x * q * φ.x⁻¹) ^ Δ.dn ∈ Δ.Q := (Δ.mem_Q_iff).mpr ⟨pow_mem hvS _, by
    rw [Δ.ψe_pow hvS, TwoB_pow_R h2 hsplit (Δ.ψe_mem_R hvS)]⟩
  have hQ2 : IsPGroup 2 Δ.Q := Δ.sylow.isPGroup.to_le Δ.Q_le
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨_, pow_mem hq Δ.dn⟩
  rw [Subgroup.orderOf_mk] at hm
  obtain ⟨j, hj2, hj1⟩ := exists_pow_involution (g := q ^ Δ.dn)
    ⟨m, by rw [← hm, pow_orderOf_eq_one]⟩ hne
  have hjQ : (q ^ Δ.dn) ^ j ∈ Δ.Q := pow_mem (pow_mem hq _) _
  have ht := Δ.eq_t_of_mem_Q hjQ hj2 hj1
  have he : φ.x * (q ^ Δ.dn) ^ j * φ.x⁻¹ = ((φ.x * q * φ.x⁻¹) ^ Δ.dn) ^ j := by
    rw [conj_pow, conj_pow]
  have hxt := Δ.eq_t_of_mem_Q (he ▸ pow_mem hvQ j)
    (by rw [ht]; exact φ.conj_t_sq) (by rw [ht]; exact φ.conj_t_ne_one)
  rw [ht] at hxt
  exact φ.conj_t_ne hxt

omit [Finite X] in
theorem card_R_le (hsplit : ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) [Finite Δ.Dbar] :
    Nat.card Δ.R ≤ 2 * Nat.card Δ.Dbar := by
  classical
  let f : ↥Δ.R → ↥Δ.Dbar × Bool := fun r =>
    if h : (r : A) ∈ Δ.Dbar then (⟨r, h⟩, false)
    else (⟨r * k, (hsplit r r.2).resolve_left h⟩, true)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    by_cases ha : (a : A) ∈ Δ.Dbar <;> by_cases hb : (b : A) ∈ Δ.Dbar <;>
      simp only [ha, hb, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq] at hab
    · exact Subtype.ext hab.1
    · exact absurd hab.2 (by decide)
    · exact absurd hab.2 (by decide)
    · exact Subtype.ext (mul_right_cancel hab.1)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm] at this

include h2 in
theorem TwoB_decomp (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1)
    (hsplit : ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) {s : X} (hs : s ∈ Δ.S) :
    ∃ a ∈ Δ.D, ∃ b ∈ Δ.D, s = a * (φ.x * b * φ.x⁻¹) := by
  have hcardS : Nat.card Δ.S = Nat.card Δ.ψ.ker * Nat.card Δ.ψ.range := by
    rw [← Subgroup.index_ker Δ.ψ, Subgroup.card_mul_index]
  have hker : Nat.card Δ.ψ.ker ≤ Δ.dn := by
    have := Δ.isCyclic_ker
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Δ.ψ.ker)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd (by have := Δ.two_le_dn; omega) (orderOf_dvd_of_pow_eq_one ?_)
    have h := TwoB_pow_Q h2 φ hsplit (q := ((g : ↥Δ.S) : X)) ⟨g, g.2, rfl⟩
    exact Subtype.ext (Subtype.ext (by simpa using h))
  have : Finite Δ.Dbar := Nat.finite_of_card_ne_zero (by
    rw [Δ.card_Dbar, Δ.card_D]; have := Δ.two_le_dn; omega)
  have hR := card_R_le hsplit
  rw [Δ.card_Dbar, Δ.card_D] at hR
  have hle : Nat.card Δ.S ≤ Nat.card (↥Δ.D × ↥Δ.D) := by
    rw [Nat.card_prod, Δ.card_D, hcardS]
    calc Nat.card Δ.ψ.ker * Nat.card Δ.ψ.range ≤ Δ.dn * (2 * (2 * Δ.dn)) :=
          Nat.mul_le_mul hker hR
      _ = 2 * Δ.dn * (2 * Δ.dn) := by ring
  let f : ↥Δ.D × ↥Δ.D → ↥Δ.S := fun p =>
    ⟨p.1 * (φ.x * p.2 * φ.x⁻¹), mul_mem (Δ.D_le p.1.2) (φ.conj_mem _ (Δ.D_le p.2.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h := TwoB_unique φ hD1 a.2 a'.2 b.2 b'.2 (congrArg Subtype.val hab)
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  obtain ⟨⟨a, b⟩, hab⟩ := (hf.bijective_of_nat_card_le hle).2 ⟨s, hs⟩
  exact ⟨a, a.2, b, b.2, (congrArg Subtype.val hab).symm⟩

include h2 in
theorem TwoB_sq_decomp (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1)
    (hsplit : ∀ r ∈ Δ.R, r ∈ Δ.Dbar ∨ r * k ∈ Δ.Dbar) :
    ∃ d₀ ∈ Δ.D, φ.x ^ 2 = d₀ * (φ.x * d₀ * φ.x⁻¹) := by
  obtain ⟨a, ha, b, hb, hab⟩ := TwoB_decomp h2 φ hD1 hsplit φ.sq_mem
  have hc : φ.x * φ.x ^ 2 * φ.x⁻¹ = φ.x ^ 2 := by rw [pow_two]; group
  rw [hab] at hc
  have hbD : φ.x ^ 2 * b * (φ.x ^ 2)⁻¹ ∈ Δ.D := Δ.conj_mem_D _ φ.sq_mem b hb
  have he : φ.x * (a * (φ.x * b * φ.x⁻¹)) * φ.x⁻¹ =
      (φ.x ^ 2 * b * (φ.x ^ 2)⁻¹) * (φ.x * a * φ.x⁻¹) := by
    rw [TwoB_commute φ hD1 hbD ha, pow_two]
    group
  rw [he] at hc
  obtain ⟨h1, h2'⟩ := TwoB_unique φ hD1 hbD ha ha hb hc
  exact ⟨a, ha, by rw [hab, h2']⟩

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
