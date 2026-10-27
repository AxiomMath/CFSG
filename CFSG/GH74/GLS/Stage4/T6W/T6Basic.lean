module

public import CFSG.GH74.GLS.Stage4.T6Grp
public import CFSG.GH74.GLS.Stage4.T2P53e
public import CFSG.GH74.GLS.Stage4.T2Rodd
public import CFSG.GH74.GLS.Stage4.T2LeafO

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6W

open CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

structure T6CtxW {G : Type} [Group G] [Finite G] (N : T2N3 G) (u : G) (p : ℕ) : Prop where
  sec5 : Ch6Sec5 N u
  ctx : T2Ctx N.z N.K₁ N.K₂ N.S
  coord : Ch6Coord N.toT2N2.toT2N1
  prime : p.Prime
  p_ne_two : p ≠ 2
  q₂_pow : ∃ n : ℕ, N.q₂ = p ^ n
  Cnorm : ∀ c : G, c * N.z = N.z * c →
    (∀ x ∈ N.K₁, c * x * c⁻¹ ∈ N.K₁) ∧ (∀ x ∈ N.K₂, c * x * c⁻¹ ∈ N.K₂)
  Rodd : ∀ x : G, x * N.z = N.z * x → Odd (orderOf x) → (∀ k ∈ N.K₁ ⊔ N.K₂, x * k = k * x) → x = 1
  zK : ∀ k ∈ N.K₁ ⊔ N.K₂, k * N.z = N.z * k
  oddK : ∀ g ∈ N.K₁ ⊔ N.K₂ ⊔ N.S, Odd (orderOf g) → g ∈ N.K₁ ⊔ N.K₂
  FS : ∀ f ∈ N.F, ∀ s ∈ N.S, f * s = s * f
  outer₂ : ∀ x ∈ N.K₁ ⊔ N.K₂ ⊔ N.S, x ∉ N.K₁ ⊔ N.K₂ → ¬ ∀ y ∈ N.K₂, x * y = y * x
  C_two : ∀ d : G, d * N.z = N.z * d → (∃ k : ℕ, d ^ (2 ^ k) = 1) → d ∈ N.K₁ ⊔ N.K₂ ⊔ N.S
  inv₁ : ∀ x ∈ N.K₁, x * x = 1 → x = 1 ∨ x = N.z
  sylcent₁ : ∀ P : Subgroup G, IsPGroup 2 ↥P → ¬ 2 ∣ P.relIndex N.K₁ →
    ∀ x ∈ N.K₁, (∀ q ∈ P, x * q = q * x) → x ∈ Subgroup.zpowers N.z

theorem t6_pow_cf {G : Type} [Group G] {C₁ F : Subgroup G} (hFn : ∀ f ∈ F, ∀ c ∈ C₁, f * c * f⁻¹ ∈ C₁)
    {c f : G} (hc : c ∈ C₁) (hf : f ∈ F) (n : ℕ) : ∃ c' ∈ C₁, (c * f) ^ n = c' * f ^ n := by
  induction n with
  | zero => exact ⟨1, C₁.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨c' * (f ^ n * c * (f ^ n)⁻¹), C₁.mul_mem hc' (hFn _ (F.pow_mem hf n) c hc), ?_⟩
    rw [pow_succ, h]
    group

theorem t6CtxW_of
    {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    {N : T2N3 G} {u : G} {p : ℕ} (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂)
    (hq₁ : N.q₁ = q₁) (hq₂ : N.q₂ = q₂) (hp : p.Prime) (hp2 : p ≠ 2) (hn₂ : ∃ n : ℕ, q₂ = p ^ n)
    (hCoord : Ch6Coord N.toT2N2.toT2N1) (h5 : Ch6Sec5 N u) : T6CtxW N u p := by
  have hloc := h5.loc
  have hF := h5.F5
  have ctx := t2Ctx_of hSet hRem hloc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have hFS : ∀ f ∈ N.F, ∀ s ∈ N.S, f * s = s * f := by
    intro f hf s hs
    have hfC : f ∈ centralizer (N.S : Set G) := by
      rw [hF.centS]; exact Subgroup.mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
  have hFz : ∀ f ∈ N.F, f * N.z = N.z * f := fun f hf => hFS f hf _ hloc.z_mem_S
  have hzK : ∀ k ∈ N.K₁ ⊔ N.K₂, k * N.z = N.z * k := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hSet.le_centralizer hk)).symm.symm
  have hoddK : ∀ g ∈ N.K₁ ⊔ N.K₂ ⊔ N.S, Odd (orderOf g) → g ∈ N.K₁ ⊔ N.K₂ := by
    intro g hg hgodd
    have hg' : g ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := by rw [← ctx.KS]; exact hg
    exact t2C_odd_mem_of_index_two hSet.index_two hg' hgodd
  have hFn := t2P53_F_normC₁ ctx hFz
  refine ⟨h5, ctx, hCoord, hp, hp2, hn₂, ?_, ?_,
    hzK, hoddK, hFS, ?_, ?_, ?_, ?_⟩
  · intro c hc
    exact t2P53_Cnorm hSet hRem ctx hF.C_le hF.F_odd hFz hc
  · intro x hxz hxodd hxK
    exact t2C_R_odd_trivial hSet hRem ctx x
      (Subgroup.mem_centralizer_singleton_iff.2 hxz) hxodd hxK
  · intro x hx hxK hcent
    have hx' : x ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := by rw [← ctx.KS]; exact hx
    exact t2C_not_cent_K₂ hSet hRem ctx.C hx' hxK hcent
  · intro d hdz ⟨k, hk⟩
    have hdC : d ∈ centralizer ({N.z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hdz
    obtain ⟨c, hc, f, hf, hdcf⟩ := t2P53_split hFn (hF.C_le hdC)
    obtain ⟨c', hc', hpow⟩ := t6_pow_cf (C₁ := N.K₁ ⊔ N.K₂ ⊔ N.S) (F := N.F)
      (fun f hf c hc => (Subgroup.mem_normalizer_iff.1 (hFn hf) c).1 hc) hc hf (2 ^ k)
    rw [hdcf] at hk
    rw [hpow] at hk
    have hf2 : f ^ (2 ^ k) ∈ N.K₁ ⊔ N.K₂ ⊔ N.S := by
      have : f ^ (2 ^ k) = c'⁻¹ := by
        calc f ^ (2 ^ k) = c'⁻¹ * (c' * f ^ (2 ^ k)) := by group
          _ = c'⁻¹ := by rw [hk]; group
      rw [this]; exact Subgroup.inv_mem _ hc'
    have hfodd : Odd (orderOf (f ^ (2 ^ k))) := by
      have : orderOf (f ^ (2 ^ k)) ∣ orderOf f := orderOf_pow_dvd _
      exact Odd.of_dvd_nat (hF.F_odd f hf) this
    have hfK := hoddK _ hf2 hfodd
    have hbot : f ^ (2 ^ k) ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨N.F.pow_mem hf _, hfK⟩
    rw [hF.F_inter_K, Subgroup.mem_bot] at hbot
    have hf1 : f = 1 := by
      have hdvd : orderOf f ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hbot
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hodd := hF.F_odd f hf
      rw [hi] at hodd
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0] at hi; simpa using orderOf_eq_one_iff.1 (by simpa using hi)
      · exfalso
        have : Even (2 ^ i) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
        exact (Nat.not_even_iff_odd.2 hodd) this
    rw [hdcf, hf1, mul_one]; exact hc
  · obtain ⟨⟨e₁, hze₁⟩, -⟩ := t2C_coords hSet
    have := hSet.finite₁
    have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
    exact t2P53_invK hodd₁ e₁ hSet.z_mem₁ hze₁
  · obtain ⟨⟨e₁, hze₁⟩, -⟩ := t2C_coords hSet
    have := hSet.finite₁
    have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
    intro P hP hPidx x hx hcent
    exact t2C_cent_sylow_K hodd₁ e₁ hP hPidx hSet.z_mem₁ hze₁ x hx hcent

variable {G : Type} [Group G] [Finite G]

abbrev M₂ (N : T2N3 G) : Subgroup G := Subgroup.normalizer (N.X₂ : Set G)

abbrev R₂ (N : T2N3 G) (p : ℕ) : Subgroup G := CFSG.Open.pCoreOf p (M₂ N)

omit [Finite G] in
theorem R₂_le_M₂ (N : T2N3 G) (p : ℕ) : R₂ N p ≤ M₂ N :=
  CFSG.LieType.BorelTits.pCoreOf_le p (M₂ N)

theorem R₂_pGroup (N : T2N3 G) {p : ℕ} (hp : p.Prime) : IsPGroup p ↥(R₂ N p) := by
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup p (M₂ N)

omit [Finite G] in
theorem R₂_norm (N : T2N3 G) (p : ℕ) {g : G} (hg : g ∈ M₂ N) {r : G} (hr : r ∈ R₂ N p) :
    g * r * g⁻¹ ∈ R₂ N p :=
  (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (M₂ N) hg) r).1 hr

theorem X₂_le_R₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : N.X₂ ≤ R₂ N p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hX : IsPGroup p ↥N.X₂ := by
    obtain ⟨n, hn⟩ := h.q₂_pow
    exact IsPGroup.of_card (n := n) (by rw [h.sec5.loc.card_X₂, hn])
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p Subgroup.le_normalizer le_rfl hX

theorem K₁_cent_X₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) {k : G} (hk : k ∈ N.K₁) {y : G}
    (hy : y ∈ N.X₂) : k * y * k⁻¹ = y := by
  have hyK : y ∈ N.K₂ := by rw [h.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hy
  have := h.sec5.loc.K_comm k hk y hyK
  rw [this]; group

theorem K₁_le_M₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : N.K₁ ≤ M₂ N := by
  intro k hk
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  rw [K₁_cent_X₂ h hk hx]
  exact hx

theorem H_le_M₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : N.H ≤ M₂ N := by
  intro k hk
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  exact h.sec5.loc.H_norm_X₂ k hk x hx

theorem z_mem_M₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : N.z ∈ M₂ N :=
  K₁_le_M₂ h h.sec5.loc.z_mem_K₁

theorem u_mem_M₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6CtxW N u p) : u ∈ M₂ N := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  rw [h.sec5.loc.u_inv_X₂ x hx]
  exact N.X₂.inv_mem hx

end CFSG.GH74.GLS.Stage4.Rest.T6W
