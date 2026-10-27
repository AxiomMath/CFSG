module

public import CFSG.GH74.GLS.LU.Local.CStruct2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

@[expose] def GoodR (p f r : ℕ) : Prop :=
  r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ ¬ r ∣ f ∧
    ∀ s : ℕ, Odd s → 1 < s → s ∣ f → ¬ r ∣ p ^ (2 * (f / s)) - 1

structure LUCtx (G : Type) [Group G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G)
    (t u : G) (ε : ℤ) : Prop where
  simple : IsKProperSimple G
  hp : p.Prime
  hp2 : p ≠ 2
  hq : 5 ≤ p ^ f
  hyp : A3Hyp G p f z S K₁ K₂ t u
  eps : LUEps G (p ^ f) ε z K₁ u

namespace LUCtx

variable {G : Type} [Group G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}
  {ε : ℤ}

theorem comps (X : LUCtx G p f z S K₁ K₂ t u ε) : LUComps G (p ^ f) z K₁ K₂ := X.hyp.1

theorem syl (X : LUCtx G p f z S K₁ K₂ t u ε) : LUSyl G z S K₁ K₂ t u := X.hyp.2.1

theorem h6A (X : LUCtx G p f z S K₁ K₂ t u ε) : MaxOverCentralizerPSp4 z p f := X.hyp.2.2.1

theorem h61 (X : LUCtx G p f z S K₁ K₂ t u ε) : LU61 G z S K₁ K₂ t u := X.hyp.2.2.2.1

theorem gen (X : LUCtx G p f z S K₁ K₂ t u ε) :
    ∀ c ∈ Cz z, ∃ a ∈ A0 z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ Fstar (S : Subgroup G) K₁ K₂ u, c = a * k * s * y := X.hyp.2.2.2.2

theorem odd_q (X : LUCtx G p f z S K₁ K₂ t u ε) : Odd (p ^ f) :=
  (X.hp.odd_of_ne_two X.hp2).pow

theorem isSimple (X : LUCtx G p f z S K₁ K₂ t u ε) : IsSimpleGroup G := X.simple.1

theorem nonab (X : LUCtx G p f z S K₁ K₂ t u ε) : ∃ a b : G, a * b ≠ b * a := X.simple.2.1

end LUCtx

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {z w : G} (hz : z * z = 1) (hw : w ∈ zpowers z) :
    w = 1 ∨ w = z := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
  by_cases hz1 : z = 1
  · left; rw [hz1, one_zpow]
  · have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    have hmod : z ^ (i % 2) = z ^ i := by
      have := zpow_mod_orderOf z i
      rwa [hord, Nat.cast_ofNat] at this
    rw [← hmod]
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · left; rw [h0]; simp
    · right; rw [h1]; simp

theorem mem_normalizer_of_forall {K : Subgroup G} {w : G} (h : ∀ k ∈ K, w * k * w⁻¹ ∈ K) :
    w ∈ normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj w).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have hcard : Nat.card ↥K ≤ Nat.card ↥(K.map (MulAut.conj w).toMonoidHom) :=
    (card_map_conj K w).ge
  have := Subgroup.eq_of_le_of_card_ge hle hcard
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this

theorem u_norm₂ (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) :
    u ∈ normalizer (K₂ : Set G) := by
  rcases hc.perm hs.u_mem_Cz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e2
  · exfalso
    have this : K₁.map (MulAut.conj u).toMonoidHom = K₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hs.u_norm
    rw [e1] at this
    exact hc.ne this.symm

omit [Finite G] in
theorem u_ne_one (hs : LUSyl G z S K₁ K₂ t u) : u ≠ 1 := by
  intro h
  have := hs.u_ord
  rw [h, orderOf_one] at this
  omega

theorem u_not_cent (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) (hq : Odd q)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : ∃ k ∈ K, u * k ≠ k * u := by
  by_contra h
  push Not at h
  have h1 := inv_cent_mem_zpowers hc hs hq hK hs.u_mem_Cz hs.u_sq h
  rcases eq_one_or_eq_of_mem_zpowers hs.z_sq h1 with h2 | h2
  · exact u_ne_one hs h2
  · exact hs.u_ne h2

omit [Finite G] in
theorem quasi_noncomm {K : Subgroup G} (h : CFSG.IsQuasisimple ↥K) : ∃ a b : ↥K, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem diag_exists {q : ℕ} {z₀ w : G} {L L' : Subgroup G} (hcu : LUComps G q z₀ L L')
    (hw2 : w * w = 1) (hsw : ∀ a ∈ L, w * a * w⁻¹ ∈ L') :
    ∃ D : Subgroup G, ⁅D, D⁆ = D ∧ D ≠ ⊥ ∧ (∀ d ∈ D, d * w = w * d) ∧
      (∀ d ∈ D, d * z₀ = z₀ * d) := by
  classical
  set φ := diagHom L L' w hcu.comm hsw with hφ
  have hwinv : ∀ x : G, w * (w * x * w⁻¹) * w⁻¹ = x := by
    intro x
    calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
      _ = x := by rw [hw2]; group
  refine ⟨φ.range, ?_, ?_, ?_, ?_⟩
  · have h1 : ⁅(⊤ : Subgroup ↥L), ⊤⁆ = ⊤ := hcu.quasi₁.1.commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
  · intro hbot
    obtain ⟨a, b, hab⟩ := quasi_noncomm hcu.quasi₁
    apply hab
    have hk : ∀ k : ↥L, (k : G) ∈ zpowers z₀ := by
      intro k
      have h1 : φ k ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
      rw [Subgroup.mem_bot] at h1
      have h2 : (k : G) * (w * (k : G) * w⁻¹) = 1 := h1
      have h3 : w * (k : G) * w⁻¹ = (k : G)⁻¹ := eq_inv_of_mul_eq_one_right h2
      have h4 : (k : G)⁻¹ ∈ L' := h3 ▸ hsw k k.2
      have h5 : (k : G) ∈ L ⊓ L' := ⟨k.2, by simpa using L'.inv_mem h4⟩
      rw [hcu.inf_eq] at h5
      exact h5
    have hc : ∀ (x y : G), x ∈ zpowers z₀ → y ∈ L → x * y = y * x := by
      intro x y hx hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      have : Commute z₀ y := (hcu.cz₁ hy).symm
      exact (this.zpow_left i).eq
    exact Subtype.ext (hc (a : G) (b : G) (hk a) b.2)
  · rintro _ ⟨k, rfl⟩
    have hk2 : w * (k : G) * w⁻¹ ∈ L' := hsw k k.2
    have hconj : w * ((k : G) * (w * (k : G) * w⁻¹)) * w⁻¹ = (k : G) * (w * (k : G) * w⁻¹) := by
      calc w * ((k : G) * (w * (k : G) * w⁻¹)) * w⁻¹
          = (w * (k : G) * w⁻¹) * (w * (w * (k : G) * w⁻¹) * w⁻¹) := by group
        _ = (w * (k : G) * w⁻¹) * (k : G) := by rw [hwinv]
        _ = (k : G) * (w * (k : G) * w⁻¹) := (hcu.comm k k.2 _ hk2).symm
    show (k : G) * (w * (k : G) * w⁻¹) * w = w * ((k : G) * (w * (k : G) * w⁻¹))
    calc (k : G) * (w * (k : G) * w⁻¹) * w
        = (w * ((k : G) * (w * (k : G) * w⁻¹)) * w⁻¹) * w := by rw [hconj]
      _ = w * ((k : G) * (w * (k : G) * w⁻¹)) := by group
  · rintro _ ⟨k, rfl⟩
    have hk2 : w * (k : G) * w⁻¹ ∈ L' := hsw k k.2
    have e1 := hcu.cz₁ k.2
    have e2 := hcu.cz₂ hk2
    show (k : G) * (w * (k : G) * w⁻¹) * z₀ = z₀ * ((k : G) * (w * (k : G) * w⁻¹))
    calc (k : G) * (w * (k : G) * w⁻¹) * z₀ = (k : G) * ((w * (k : G) * w⁻¹) * z₀) := by group
      _ = (k : G) * (z₀ * (w * (k : G) * w⁻¹)) := by rw [e2]
      _ = ((k : G) * z₀) * (w * (k : G) * w⁻¹) := by group
      _ = (z₀ * (k : G)) * (w * (k : G) * w⁻¹) := by rw [e1]
      _ = z₀ * ((k : G) * (w * (k : G) * w⁻¹)) := by group

theorem comps_u {p f : ℕ} {ε : ℤ} (X : LUCtx G p f z S K₁ K₂ t u ε) {h₀ : G}
    (hh₀ : h₀⁻¹ * z * h₀ = u) : LUComps G (p ^ f) u (cj K₁ h₀) (cj K₂ h₀) := by
  have := X.comps.cj h₀
  rwa [hh₀] at this

theorem normalizes_L {p f : ℕ} {ε : ℤ} (X : LUCtx G p f z S K₁ K₂ t u ε) {h₀ : G}
    (hh₀ : h₀⁻¹ * z * h₀ = u) {w g : G} (hwu : w * u = u * w) (hw2 : w * w = 1)
    (hgw : g⁻¹ * z * g = w) (hn₁ : ∀ k ∈ K₁, (g * u * g⁻¹) * k * (g * u * g⁻¹)⁻¹ ∈ K₁)
    (hn₂ : ∀ k ∈ K₂, (g * u * g⁻¹) * k * (g * u * g⁻¹)⁻¹ ∈ K₂) (hne : u ≠ w) :
    w ∈ normalizer ((cj K₁ h₀ : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := X.comps
  have hs := X.syl
  have hcu := comps_u X hh₀
  have hwC : w ∈ Cz u := mem_centralizer_singleton_iff.mpr hwu
  rcases hcu.perm hwC with ⟨e1, -⟩ | ⟨e1, e2⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e1
  · exfalso
    have hsw : ∀ a ∈ cj K₁ h₀, w * a * w⁻¹ ∈ cj K₂ h₀ := fun a ha => LUComps.mem_of_map e1 ha
    obtain ⟨D, hDperf, hDne, hDw, hDu⟩ := diag_exists hcu hw2 hsw
    set w' : G := g * u * g⁻¹ with hw'
    have hzw : z = g * w * g⁻¹ := by rw [← hgw]; group
    have hw'C : w' ∈ Cz z := by
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [hzw, hw']
      calc g * u * g⁻¹ * (g * w * g⁻¹) = g * (u * w) * g⁻¹ := by group
        _ = g * (w * u) * g⁻¹ := by rw [hwu]
        _ = g * w * g⁻¹ * (g * u * g⁻¹) := by group
    have hw'2 : w' * w' = 1 := by
      rw [hw']
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [hs.u_sq]; group
    have hw'ne : w' ≠ 1 := by
      intro h
      apply u_ne_one hs
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [← hw', h]
        _ = 1 := by group
    have hw'ord : ∃ n : ℕ, orderOf w' = 2 ^ n := by
      refine ⟨1, ?_⟩
      have : w' ^ 2 = 1 := by rw [pow_two]; exact hw'2
      simpa using orderOf_eq_prime this hw'ne
    have hw'n₁ : w' ∈ normalizer (K₁ : Set G) := mem_normalizer_of_forall hn₁
    have hw'n₂ : w' ∈ normalizer (K₂ : Set G) := mem_normalizer_of_forall hn₂
    have hnotz : w' ∉ zpowers z := by
      intro hmem
      rcases eq_one_or_eq_of_mem_zpowers hs.z_sq hmem with h1 | h1
      · exact hw'ne h1
      · apply hne
        calc u = g⁻¹ * w' * g := by rw [hw']; group
          _ = g⁻¹ * z * g := by rw [h1]
          _ = w := hgw
    have hnc₁ : ∃ k ∈ K₁, w' * k ≠ k * w' := by
      by_contra h
      push Not at h
      exact hnotz (inv_cent_mem_zpowers hc hs X.odd_q (Or.inl rfl) hw'C hw'2 h)
    have hnc₂ : ∃ k ∈ K₂, w' * k ≠ k * w' := by
      by_contra h
      push Not at h
      exact hnotz (inv_cent_mem_zpowers hc hs X.odd_q (Or.inr rfl) hw'C hw'2 h)
    have hab₁ := cenAb_C hc hs (Or.inl rfl) hw'C hw'ord hw'n₁ hnc₁
    have hab₂ := cenAb_C hc hs (Or.inr rfl) hw'C hw'ord hw'n₂ hnc₂
    set D' : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hD'
    have hD'C : D' ≤ Cz z := by
      rintro _ ⟨d, hd, rfl⟩
      refine mem_centralizer_singleton_iff.mpr ?_
      have := hDw d hd
      show (g * d * g⁻¹) * z = z * (g * d * g⁻¹)
      rw [hzw]
      calc g * d * g⁻¹ * (g * w * g⁻¹) = g * (d * w) * g⁻¹ := by group
        _ = g * (w * d) * g⁻¹ := by rw [this]
        _ = g * w * g⁻¹ * (g * d * g⁻¹) := by group
    have hD'perf : ⁅D', D'⁆ = D' := by rw [hD', ← Subgroup.map_commutator, hDperf]
    have hD'K : D' ≤ K₁ ⊔ K₂ := perfect_le_K hc hs X.gen hD'C hD'perf
    have hD'w : ∀ l ∈ D', l * w' = w' * l := by
      rintro _ ⟨d, hd, rfl⟩
      have := hDu d hd
      show (g * d * g⁻¹) * (g * u * g⁻¹) = (g * u * g⁻¹) * (g * d * g⁻¹)
      calc g * d * g⁻¹ * (g * u * g⁻¹) = g * (d * u) * g⁻¹ := by group
        _ = g * (u * d) * g⁻¹ := by rw [this]
        _ = g * u * g⁻¹ * (g * d * g⁻¹) := by group
    have hbot : D' = ⊥ :=
      perfect_commuting_eq_bot hc hn₁ hn₂ hab₁ hab₂ hD'K hD'w hD'perf
    apply hDne
    rw [hD'] at hbot
    rw [eq_bot_iff]
    intro d hd
    have h1 : (g * d * g⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact ⟨d, hd, rfl⟩
    rw [Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have : d = g⁻¹ * (g * d * g⁻¹) * g := by group
    rw [this, h1]; group

end CFSG.GH74.GLS.LU.Local
