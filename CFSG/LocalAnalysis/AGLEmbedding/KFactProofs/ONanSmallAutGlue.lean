module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallLocal

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

section Simple

variable {K : Type} [Group K]

theorem center_eq_bot_of_simple (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    Subgroup.center K = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem normalizer_ne_top_of_simple (hs : IsSimpleGroup K) {T : Subgroup K} (h1 : T ≠ ⊥)
    (h2 : T ≠ ⊤) : Subgroup.normalizer (T : Set K) ≠ ⊤ := by
  intro htop
  have hnorm : T.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (T : Set K) := by rw [htop]; exact trivial
    exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  rcases hs.eq_bot_or_eq_top_of_normal T with h | h
  · exact h1 h
  · exact h2 h

theorem isCoatom_of_overgroups {N : Subgroup K} (hne : N ≠ ⊤)
    (hmax : ∀ Y : Subgroup K, N ≤ Y → Y = N ∨ Y = ⊤) : IsCoatom N := by
  refine ⟨hne, fun Y hY => ?_⟩
  rcases hmax Y hY.le with h | h
  · exact absurd h hY.ne'
  · exact h

theorem conj_pow_eq_pow_pow {R : Subgroup K} {s₀ : K} {lam : ℕ}
    (hpow : ∀ x ∈ R, s₀ * x * s₀⁻¹ = x ^ lam) (j : ℕ) :
    ∀ x ∈ R, s₀ ^ j * x * (s₀ ^ j)⁻¹ = x ^ (lam ^ j) := by
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
    intro x hx
    have h1 : s₀ ^ (j + 1) * x * (s₀ ^ (j + 1))⁻¹ =
        s₀ * (s₀ ^ j * x * (s₀ ^ j)⁻¹) * s₀⁻¹ := by group
    rw [h1, ih x hx]
    have hxl : x ^ (lam ^ j) ∈ R := R.pow_mem hx _
    rw [hpow _ hxl, ← pow_mul, ← pow_succ]

end Simple

section Torus

theorem natCast_pow_prime_pow {p : ℕ} [Fact p.Prime] (c a : ℕ) :
    ((c ^ (p ^ a) : ℕ) : ZMod p) = (c : ZMod p) := by
  rw [Nat.cast_pow, ZMod.pow_card_pow]

theorem not_dvd_sub_one {p M : ℕ} (hpos : 0 < M) (hM : (M : ZMod p) ≠ 1) : ¬ p ∣ M - 1 := by
  intro hd
  have hz : (((M - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [Nat.cast_sub hpos, Nat.cast_one, sub_eq_zero] at hz
  exact hM hz

theorem eq_one_of_pow_eq_self {K : Type} [Group K] {p k : ℕ} (hp : p.Prime) {y : K}
    (hyk : orderOf y ∣ p ^ k) {M : ℕ} (hM : (M : ZMod p) ≠ 1) (hy : y ^ M = y) : y = 1 := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · rw [h0, pow_zero] at hy
    exact hy.symm
  · have hy1 : y ^ (M - 1) = 1 := by
      have : y ^ (M - 1) * y = y := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]; exact hy
      simpa using this
    have hd1 : orderOf y ∣ M - 1 := orderOf_dvd_of_pow_eq_one hy1
    have hcop : Nat.Coprime (p ^ k) (M - 1) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_sub_one hpos hM))
    have : orderOf y ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hyk hd1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

variable {K : Type} [Group K] [Finite K]

theorem torus_of_conj_data {p : ℕ} (hp : p.Prime) {N : Subgroup K} {u : K} (hu : u ∈ N)
    {T : Subgroup K}
    (hfix : ∀ a : ℕ, ∀ y ∈ T, u ^ (p ^ a) * y = y * u ^ (p ^ a) → y = 1) :
    ∃ T₀ : Subgroup K, T₀ ≤ N ∧ p.Coprime (Nat.card T₀) ∧
      T ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥ := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' p hp.ne_one
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  refine ⟨Subgroup.zpowers (u ^ (p ^ a)), ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ hu _
  · rw [Nat.card_zpowers, orderOf_pow' _ hpa.ne', hab, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ hpa]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hb
  · rw [eq_bot_iff]
    rintro y ⟨hyT, hyC⟩
    have hcomm : u ^ (p ^ a) * y = y * u ^ (p ^ a) :=
      (Subgroup.mem_centralizer_iff.1 hyC _ (Subgroup.mem_zpowers _))
    exact Subgroup.mem_bot.2 (hfix a y hyT hcomm)

end Torus

section Aut

variable {K : Type} [Group K]

theorem conj_injective_of_center_bot (hcen : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut K => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    have h : g * x = x * g := by
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [this]
    exact h.symm
  rw [hcen] at this
  exact Subgroup.mem_bot.1 this

theorem aut_mul_conj_mul_inv (f : MulAut K) (g : K) :
    f * MulAut.conj g * f⁻¹ = MulAut.conj (f g) := by
  ext x
  simp [MulAut.conj_apply]

theorem innerRange_normal : ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨g, rfl⟩ := hn
  exact ⟨f g, (aut_mul_conj_mul_inv f g).symm⟩

theorem centralizer_innerRange (hcen : Subgroup.center K = ⊥) :
    Subgroup.centralizer (((MulAut.conj : K →* MulAut K).range : Subgroup (MulAut K)) :
      Set (MulAut K)) = ⊥ := by
  have hinj := conj_injective_of_center_bot hcen
  rw [eq_bot_iff]
  intro f hf
  rw [Subgroup.mem_bot]
  ext x
  have h1 : MulAut.conj x * f = f * MulAut.conj x :=
    Subgroup.mem_centralizer_iff.1 hf _ ⟨x, rfl⟩
  have h2 : f * MulAut.conj x * f⁻¹ = MulAut.conj x := by
    rw [← h1]; group
  rw [aut_mul_conj_mul_inv] at h2
  exact hinj h2

noncomputable def innerEquiv (hcen : Subgroup.center K = ⊥) :
    K ≃* ((MulAut.conj : K →* MulAut K).range) :=
  MonoidHom.ofInjective (conj_injective_of_center_bot hcen)

theorem autFixInner_of_centralizer {p k : ℕ} [Fact p.Prime] [Finite K]
    (hcen : Subgroup.center K = ⊥) (T : Sylow p K) (hT : Nat.card (T : Subgroup K) = p ^ k)
    (hX : ∀ R : Sylow p (MulAut K), Nat.card (R : Subgroup (MulAut K)) = p ^ k ∧
      Subgroup.centralizer (R : Set (MulAut K)) ≤ (R : Subgroup (MulAut K))) :
    AutFixInner p K T := by
  have hinj := conj_injective_of_center_bot hcen
  intro f hf
  let Tφ : Subgroup (MulAut K) := (T : Subgroup K).map (MulAut.conj : K →* MulAut K)
  have hTφcard : Nat.card Tφ = p ^ k := by
    rw [Subgroup.card_map_of_injective hinj]; exact hT
  have hTφp : IsPGroup p Tφ := IsPGroup.of_card hTφcard
  obtain ⟨R, hR⟩ := hTφp.exists_le_sylow
  have hRcard : Nat.card (R : Subgroup (MulAut K)) = p ^ k := (hX R).1
  have hRT : Tφ = (R : Subgroup (MulAut K)) :=
    Subgroup.eq_of_le_of_card_ge hR (by rw [hRcard, hTφcard])
  have hfc : f ∈ Subgroup.centralizer ((R : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    rw [← hRT] at hr
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hr
    have h1 := aut_mul_conj_mul_inv f t
    rw [hf t ht] at h1
    show MulAut.conj t * f = f * MulAut.conj t
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hfR : f ∈ (R : Subgroup (MulAut K)) := (hX R).2 hfc
  rw [← hRT] at hfR
  obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 hfR
  exact ⟨t, ht⟩

end Aut

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
