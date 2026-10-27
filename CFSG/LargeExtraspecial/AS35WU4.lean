module

public import CFSG.LargeExtraspecial.AS35WL5U5
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUb

public section

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace AS35W

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def rk1 (u w : HypIndex 2 0 → K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  LinearMap.toMatrix' ((hypForm h 2 0 w).smulRight u)

theorem rk1_mulVec (u w x : HypIndex 2 0 → K) : rk1 h u w *ᵥ x = hypForm h 2 0 w x • u := by
  rw [rk1, LinearMap.toMatrix'_mulVec, LinearMap.smulRight_apply]

theorem sq_dvd_card_centralizer_U4_of_family {A : hypSU h 2 0} {G : Type} [AddCommGroup G]
    [Finite G] (hG : Nat.card G = (p ^ f) ^ 2) (hpG : ∀ a : G, p • a = 0)
    (N : G →+ Matrix (HypIndex 2 0) (HypIndex 2 0) K)
    (hNN : ∀ a b x, N a *ᵥ (N b *ᵥ x) = 0)
    (hskew : ∀ a x y, hypForm h 2 0 (N a *ᵥ x) y + hypForm h 2 0 x (N a *ᵥ y) = 0)
    (hcomm : ∀ a x, N a *ᵥ (((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      *ᵥ x) = ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
        (N a *ᵥ x))
    (hinj : ∀ a, (∀ x, N a *ᵥ x = 0) → a = 0) :
    (p ^ f) ^ 2 ∣ Nat.card (centralizer ({hypProj h 2 0 A} : Set (hypPSU h 2 0))) := by
  classical
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  set Am : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
    ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hAm
  have hext : ∀ M₁ M₂ : Matrix (HypIndex 2 0) (HypIndex 2 0) K, (∀ x, M₁ *ᵥ x = M₂ *ᵥ x) →
      M₁ = M₂ := fun M₁ M₂ hM =>
    Matrix.toLin'.injective (LinearMap.ext fun x => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hM])
  have hNN' : ∀ a b, N a * N b = 0 := fun a b =>
    hext _ _ fun x => by rw [← Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  set M : G → Matrix (HypIndex 2 0) (HypIndex 2 0) K := fun a => 1 + N a with hM
  have hMmul : ∀ a b, M a * M b = M (a + b) := by
    intro a b
    simp only [hM, add_mul, mul_add, one_mul, mul_one, hNN', map_add, add_zero]
    abel
  have hM0 : M 0 = 1 := by simp [hM]
  have hMpow : ∀ (n : ℕ) a, M a ^ n = M (n • a) := by
    intro n a
    induction n with
    | zero => rw [pow_zero, zero_nsmul, hM0]
    | succ n ih => rw [pow_succ, ih, hMmul, succ_nsmul]
  have hdet : ∀ a, (M a).det = 1 := by
    intro a
    have h1 : (M a).det ^ p = 1 := by
      rw [← det_pow, hMpow, hpG, hM0, det_one]
    have h2 : ((M a).det - 1) ^ p = 0 := by
      rw [sub_pow_char, h1, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff hp.ne_zero).1 h2)
  have hMv : ∀ a v, M a *ᵥ v = v + N a *ᵥ v := fun a v => by
    rw [hM, add_mulVec, one_mulVec]
  have hiso : ∀ a x y, hypForm h 2 0 (M a *ᵥ x) (M a *ᵥ y) = hypForm h 2 0 x y := by
    intro a x y
    have h1 := hskew a x y
    have h2 : hypForm h 2 0 (N a *ᵥ x) (N a *ᵥ y) = 0 := by
      have := hskew a x (N a *ᵥ y)
      rwa [hNN, map_zero, add_zero] at this
    simp only [hMv, map_add, LinearMap.add_apply]
    linear_combination h1 + h2
  let Φ : Multiplicative G →* hypSU h 2 0 :=
    { toFun := fun a => ⟨⟨M (Multiplicative.toAdd a), M (-Multiplicative.toAdd a),
          by rw [hMmul, add_neg_cancel, hM0], by rw [hMmul, neg_add_cancel, hM0]⟩,
        mem_gramSU_iff_isometry.2 ⟨hiso _, hdet _⟩⟩
      map_one' := Subtype.ext (Units.ext hM0)
      map_mul' := fun a b => Subtype.ext (Units.ext (hMmul _ _).symm) }
  set ψ := (hypProj h 2 0).comp Φ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : Φ a ∈ hypScalars h 2 0 := by
      rw [← ker_hypProj]
      exact ha
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hmem
    have hMc : M (Multiplicative.toAdd a) = (c : K) • 1 := by
      have := congrArg (fun g : GL (HypIndex 2 0) K => Units.val g) hc
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply] at this
      rw [smul_one_eq_diagonal]
      exact this
    have hNa : N (Multiplicative.toAdd a) = ((c : K) - 1) • 1 := by
      rw [sub_smul, one_smul, ← hMc, hM, add_sub_cancel_left]
    have hsq := hNN' (Multiplicative.toAdd a) (Multiplicative.toAdd a)
    rw [hNa, smul_mul_smul_comm, Matrix.one_mul] at hsq
    have hc1 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
      have := congrFun (congrFun hsq (Sum.inl 0)) (Sum.inl 0)
      simpa using this
    have hc1' : (c : K) - 1 = 0 := mul_self_eq_zero.1 hc1
    have h0 := hinj (Multiplicative.toAdd a) fun x => by
      rw [hNa, hc1', zero_smul, Matrix.zero_mulVec]
    exact h0
  have hle : ψ.range ≤ centralizer ({hypProj h 2 0 A} : Set (hypPSU h 2 0)) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change hypProj h 2 0 (Φ a) * hypProj h 2 0 A = hypProj h 2 0 A * hypProj h 2 0 (Φ a)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change M (Multiplicative.toAdd a) * Am = Am * M (Multiplicative.toAdd a)
    refine hext _ _ fun x => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMv, hMv, Matrix.mulVec_add, hcomm]
  have hcard : Nat.card ψ.range = (p ^ f) ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    exact hG
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

@[expose] noncomputable def pFamily (e g : Fin 2 → HypIndex 2 0 → K) :
    K →+ Matrix (HypIndex 2 0) (HypIndex 2 0) K where
  toFun c := c • rk1 h (e 0) (g 1) - h.bar c • rk1 h (g 1) (e 0)
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, add_smul]
    abel

theorem pFamily_mulVec (e g : Fin 2 → HypIndex 2 0 → K) (c : K) (x : HypIndex 2 0 → K) :
    pFamily h e g c *ᵥ x =
      (c * hypForm h 2 0 (g 1) x) • e 0 - (h.bar c * hypForm h 2 0 (e 0) x) • g 1 := by
  simp only [pFamily, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sub_mulVec, smul_mulVec,
    rk1_mulVec, smul_smul]

theorem form_mulVec_of_eigen {A : hypSU h 2 0} {u : HypIndex 2 0 → K} {μ : K} (hμ : μ ≠ 0)
    (hu : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ u = μ • u)
    (x : HypIndex 2 0 → K) :
    hypForm h 2 0 u (((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x) =
      h.bar μ⁻¹ * hypForm h 2 0 u x := by
  have hiso := (mem_gramSU_iff_isometry.mp A.2).1 (μ⁻¹ • u) x
  rw [Matrix.mulVec_smul, hu, smul_smul, inv_mul_cancel₀ hμ, one_smul] at hiso
  change hypForm h 2 0 u _ = hypForm h 2 0 (μ⁻¹ • u) x at hiso
  rw [hiso, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

variable {h} in
theorem sq_dvd_of_paired [Finite K] {A : hypSU h 2 0} {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = -1) {e g : Fin 2 → HypIndex 2 0 → K}
    (hAe : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i =
      l • e i)
    (hAg : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i =
      (-l) • g i)
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) :
    (p ^ f) ^ 2 ∣ Nat.card (centralizer ({hypProj h 2 0 A} : Set (hypPSU h 2 0))) := by
  have hB := hypForm_isSymm (r := 2) (ε := 0) h
  have hge : ∀ i j, hypForm h 2 0 (g i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [← hB.eq (e j) (g i), heg]
    split_ifs with h1 h2 h2
    · exact map_one _
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero _
  have hbl : h.bar l = -l⁻¹ := by
    have : l * h.bar l = -1 := hN
    field_simp
    linear_combination this
  have hbg : h.bar (-l)⁻¹ = l := by
    rw [map_inv₀, map_neg, hbl, neg_neg, inv_inv]
  have hbe : h.bar l⁻¹ = -l := by
    rw [map_inv₀, hbl, inv_neg, inv_inv]
  have hl' : -l ≠ 0 := neg_ne_zero.2 hl0
  have : CharP K p := h.charP
  refine sq_dvd_card_centralizer_U4_of_family h (G := K) (N := pFamily h e g) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h.card, ← pow_mul, mul_comm]
  · intro c
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · intro a b x
    simp only [pFamily_mulVec, map_sub, map_smul, smul_eq_mul, hee, hgg, heg, hge]
    simp
  · intro c x y
    simp only [pFamily_mulVec, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul, h.bar_bar, hB.eq]
    ring
  · intro c x
    rw [pFamily_mulVec, pFamily_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hAe, hAg, form_mulVec_of_eigen h hl' (hAg 1),
      form_mulVec_of_eigen h hl0 (hAe 0), hbg, hbe, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · intro c hc
    have h1 := hc (e 1)
    rw [pFamily_mulVec, hge, hee] at h1
    simp only [ite_true, mul_one, mul_zero, zero_smul, sub_zero] at h1
    by_contra hc0
    have he0 : e 0 = 0 := by
      have := congrArg (fun v => c⁻¹ • v) h1
      simpa [smul_smul, inv_mul_cancel₀ hc0] using this
    have := heg 0 0
    rw [he0, map_zero, LinearMap.zero_apply] at this
    simp at this

@[expose] noncomputable def tFamily (w₁ w₂ : HypIndex 2 0 → K) :
    h.traceZero × h.traceZero →+ Matrix (HypIndex 2 0) (HypIndex 2 0) K where
  toFun a := (a.1 : K) • rk1 h w₁ w₁ + (a.2 : K) • rk1 h w₂ w₂
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, add_smul]
    abel

theorem tFamily_mulVec (w₁ w₂ : HypIndex 2 0 → K) (a : h.traceZero × h.traceZero)
    (x : HypIndex 2 0 → K) :
    tFamily h w₁ w₂ a *ᵥ x =
      ((a.1 : K) * hypForm h 2 0 w₁ x) • w₁ + ((a.2 : K) * hypForm h 2 0 w₂ x) • w₂ := by
  simp only [tFamily, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_mulVec, smul_mulVec,
    rk1_mulVec, smul_smul]

variable {h} in
theorem sq_dvd_of_orthogonal [Finite K] {A : hypSU h 2 0} {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = 1) {v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => l) (fun _ => -l) i • v i) :
    (p ^ f) ^ 2 ∣ Nat.card (centralizer ({hypProj h 2 0 A} : Set (hypPSU h 2 0))) := by
  have hB := hypForm_isSymm (r := 2) (ε := 0) h
  obtain ⟨c, hc⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  have hcN : c * h.bar c = -1 := hc
  set w₁ := v (Sum.inl 0) + c • v (Sum.inl 1) with hw₁
  set w₂ := v (Sum.inr 0) + c • v (Sum.inr 1) with hw₂
  have F11 : hypForm h 2 0 w₁ w₁ = 0 := by
    simp [hw₁, hv]
    linear_combination hcN
  have F22 : hypForm h 2 0 w₂ w₂ = 0 := by
    simp [hw₂, hv]
    linear_combination hcN
  have F12 : hypForm h 2 0 w₁ w₂ = 0 := by simp [hw₁, hw₂, hv]
  have F21 : hypForm h 2 0 w₂ w₁ = 0 := by simp [hw₁, hw₂, hv]
  have G1 : hypForm h 2 0 w₁ (v (Sum.inl 0)) = 1 := by simp [hw₁, hv]
  have G2 : hypForm h 2 0 w₂ (v (Sum.inr 0)) = 1 := by simp [hw₂, hv]
  have H1 : hypForm h 2 0 w₂ (v (Sum.inl 0)) = 0 := by simp [hw₂, hv]
  have H2 : hypForm h 2 0 w₁ (v (Sum.inr 0)) = 0 := by simp [hw₁, hv]
  set Am := ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) with hAm
  have hA1 : Am *ᵥ w₁ = l • w₁ := by
    rw [hw₁, Matrix.mulVec_add, Matrix.mulVec_smul, hAv, hAv, smul_add, smul_comm l c]
    rfl
  have hA2 : Am *ᵥ w₂ = (-l) • w₂ := by
    rw [hw₂, Matrix.mulVec_add, Matrix.mulVec_smul, hAv, hAv, smul_add, smul_comm (-l) c]
    rfl
  have hbl : h.bar l = l⁻¹ := by
    have : l * h.bar l = 1 := hN
    field_simp
    linear_combination this
  have hb1 : h.bar l⁻¹ = l := by rw [map_inv₀, hbl, inv_inv]
  have hb2 : h.bar (-l)⁻¹ = -l := by rw [map_inv₀, map_neg, hbl, inv_neg, inv_inv]
  have hl' : -l ≠ 0 := neg_ne_zero.2 hl0
  have hw0 : ∀ (w y : HypIndex 2 0 → K) (a : K), hypForm h 2 0 w y = 1 → a • w = 0 → a = 0 := by
    intro w y a hwy haw
    by_contra ha
    have : w = 0 := by
      have := congrArg (fun u => a⁻¹ • u) haw
      simpa [smul_smul, inv_mul_cancel₀ ha] using this
    rw [this, map_zero, LinearMap.zero_apply] at hwy
    exact zero_ne_one hwy
  have : CharP K p := h.charP
  have htr : ∀ μ : h.traceZero, (μ : K) + h.bar μ = 0 := fun μ => (h.mem_traceZero).1 μ.2
  refine sq_dvd_card_centralizer_U4_of_family h (G := h.traceZero × h.traceZero)
    (N := tFamily h w₁ w₂) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_prod, h.card_traceZero, sq]
  · intro a
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
      simp [nsmul_eq_mul, CharP.cast_eq_zero]
  · intro a b x
    simp only [tFamily_mulVec, map_add, map_smul, smul_eq_mul, F11, F12, F21, F22]
    simp
  · intro a x y
    simp only [tFamily_mulVec, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, map_smul, smul_eq_mul, map_mul, hB.eq]
    linear_combination (hypForm h 2 0 x w₁ * hypForm h 2 0 w₁ y) * htr a.1 +
      (hypForm h 2 0 x w₂ * hypForm h 2 0 w₂ y) * htr a.2
  · intro a x
    rw [tFamily_mulVec, tFamily_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hA1, hA2, form_mulVec_of_eigen h hl0 hA1,
      form_mulVec_of_eigen h hl' hA2, hb1, hb2, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · intro a ha
    have h1 := ha (v (Sum.inl 0))
    have h2 := ha (v (Sum.inr 0))
    rw [tFamily_mulVec, G1, H1, mul_one, mul_zero, zero_smul, add_zero] at h1
    rw [tFamily_mulVec, G2, H2, mul_one, mul_zero, zero_smul, zero_add] at h2
    exact Prod.ext (Subtype.ext (hw0 _ _ _ G1 h1)) (Subtype.ext (hw0 _ _ _ G2 h2))

open CFSG.ComponentClassification.CatFactsL4U4 CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
theorem sq_dvd_card_centralizer_U4 [Finite K] (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    {z : hypPSU h 2 0} (hz : orderOf z = 2) :
    (p ^ f) ^ 2 ∣ Nat.card (centralizer ({z} : Set (hypPSU h 2 0))) := by
  obtain ⟨A, rfl⟩ := hypProj_surjective h 2 0 z
  have hAU : (A : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 := A.2.1
  have hdetA : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = 1 :=
    A.2.2
  have hord : orderOf (QuotientGroup.mk ⟨A, hAU⟩ : hypUnitaryMod h 2 0) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have hpow : hypProj h 2 0 A ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hz])
      have hA2 : A ^ 2 ∈ hypScalars h 2 0 := by
        rw [← ker_hypProj, MonoidHom.mem_ker, map_pow]
        exact hpow
      obtain ⟨c, hc, -, hcA⟩ := mem_normOneScalars.1 hA2
      exact ⟨c, hc, pow_zero c, hcA⟩
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨c, hc, -, hcA⟩ := mem_normOneScalars.1 h1
      have hc4 : c ^ (2 * 2 + 0) = 1 := by
        apply Units.ext
        have := congrArg (fun g : GL (HypIndex 2 0) K => (Units.val g).det) hcA
        simp only at this
        rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
          Finset.card_univ, InvClassU.card_hypIndex_two_zero] at this
        change ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = _
          at this
        rw [hdetA] at this
        rw [Units.val_pow_eq_pow_val, Units.val_one, this]
      have hmem : A ∈ hypScalars h 2 0 := ⟨c, hc, hc4, hcA⟩
      rw [← ker_hypProj, MonoidHom.mem_ker] at hmem
      rw [hmem, orderOf_one] at hz
      exact absurd hz (by norm_num)
  obtain ⟨l, hl0, -, hcases⟩ := InvClassU.classify_inv_U4 h hp2 hAU hord
  rcases hcases with ⟨hN, ⟨v, hv, hAv⟩ | ⟨d, hd, v, hv, hAv⟩⟩ |
    ⟨hN, e, g, hAe, hAg, hee, hgg, heg⟩
  · exact sq_dvd_of_orthogonal hl0 hN hv hAv
  · exfalso
    have hdA : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det =
        -d ^ 4 := by
      rw [InvClassU.det_of_eigen h (by simp) (G := 1) (Gi := 1)
        (by ext i j; simp [hv, one_apply]) (Matrix.one_mul 1) hAv]
      simp [Fintype.prod_sum_type]
      ring
    have hd4 : d ^ 4 = -1 := by
      rw [hdetA] at hdA
      linear_combination hdA
    exact InvClassU.false_of_pow_four_eq_neg_one h hp2 hq hd4 hd
  · exact sq_dvd_of_paired hl0 hN hAe hAg hee hgg heg

open CFSG.Assembly.LowTwoRank in
theorem u4W2Input : U4W2Input := by
  intro X _ _ p f hp hp2 hf hq hL
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (X ≃* StatedProj (StatedSU 4 (p ^ f) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  have e : X ≃* hypPSU h 2 0 := e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm
  intro z hz
  exfalso
  have hz' := hz.map e
  have hq4 : p ^ f % 4 = 1 := by omega
  have hdvd := (sq_dvd_card_centralizer_U4 h hp2 hq4 hz'.orderOf_eq).trans hz'.card_dvd
  have := eq_three_of_sq_dvd hp hp2 hf hdvd
  omega

end AS35W

end CFSG.LargeExtraspecial
