module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1 Multiplicative

section Trace

variable {k : Type*} [Field k]

theorem exists_frobTrace_ne_zero [Finite k] {r : ℕ} (hr : 2 ≤ r) (hk : Nat.card k = r ^ 4) :
    ∃ a : k, a + a ^ r + a ^ (r ^ 2) + a ^ (r ^ 3) ≠ 0 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  by_contra h
  have h0 : ∀ a : k, a + a ^ r + a ^ (r ^ 2) + a ^ (r ^ 3) = 0 := fun a => by
    by_contra ha
    exact h ⟨a, ha⟩
  have h12 : r < r ^ 2 := by nlinarith
  have h23 : r ^ 2 < r ^ 3 := by
    rw [pow_succ r 2]
    nlinarith
  have h34 : r ^ 3 < r ^ 4 := by
    rw [pow_succ r 3]
    nlinarith [pow_pos (show 0 < r by omega) 3]
  set P : Polynomial k := Polynomial.X ^ (r ^ 3) + Polynomial.X ^ (r ^ 2) + Polynomial.X ^ r +
    Polynomial.X with hP
  have hcoeff : P.coeff (r ^ 3) = 1 := by
    have e1 : r ^ 3 ≠ r ^ 2 := by omega
    have e2 : r ^ 3 ≠ r := by omega
    have e3 : 1 ≠ r ^ 3 := by omega
    simp [hP, Polynomial.coeff_X_pow, Polynomial.coeff_X, e1, e2, e3]
  have hP0 : P ≠ 0 := fun h0' => by
    rw [h0', Polynomial.coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have hdeg : P.natDegree ≤ r ^ 3 := by
    have d1 := Polynomial.natDegree_X_pow_le (R := k) (r ^ 3)
    have d2 := Polynomial.natDegree_X_pow_le (R := k) (r ^ 2)
    have d3 := Polynomial.natDegree_X_pow_le (R := k) r
    have d4 := Polynomial.natDegree_X_le (R := k)
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (d4.trans (by omega)))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (d3.trans (by omega)))
    exact (Polynomial.natDegree_add_le _ _).trans (max_le d1 (d2.trans (by omega)))
  have hroots : (Finset.univ : Finset k).val ⊆ P.roots := by
    intro a _
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, hP]
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination h0 a
  have hcard := Polynomial.card_le_degree_of_subset_roots hroots
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hk] at hcard
  omega

theorem exists_frobTrace_eq_one [Finite k] {r : ℕ} (hr : 2 ≤ r) (hk : Nat.card k = r ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ r) : ∃ a : k, a + ε a + ε (ε a) + ε (ε (ε a)) = 1 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hε2 : ∀ a, ε (ε a) = a ^ (r ^ 2) := fun a => by rw [hε, hε, ← pow_mul, sq]
  have hε3 : ∀ a, ε (ε (ε a)) = a ^ (r ^ 3) := fun a => by
    rw [hε2, hε, ← pow_mul, show r * r ^ 2 = r ^ 3 by ring]
  have hε4 : ∀ a, ε (ε (ε (ε a))) = a := fun a => by
    rw [hε3, hε, ← pow_mul, show r * r ^ 3 = r ^ 4 by ring, ← hk, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  obtain ⟨a₀, ha₀⟩ := exists_frobTrace_ne_zero hr hk (k := k)
  set c := a₀ + ε a₀ + ε (ε a₀) + ε (ε (ε a₀)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, hε3, hε2, hε]
    exact ha₀
  have hcε : ε c = c := by
    rw [hc, map_add, map_add, map_add, hε4]
    ring
  have hcε' : ε c⁻¹ = c⁻¹ := by rw [map_inv₀, hcε]
  refine ⟨c⁻¹ * a₀, ?_⟩
  simp only [map_mul, hcε']
  rw [← mul_add, ← mul_add, ← mul_add, ← hc, inv_mul_cancel₀ hc0]

theorem exists_sub_twist_eq (ε : k ≃+* k) (l a γ : k)
    (h4 : l * ε (l * ε (l * ε (l * ε γ))) = γ) (ha : a + ε a + ε (ε a) + ε (ε (ε a)) = 1)
    (hγ : γ + l * ε γ + l * ε (l * ε γ) + l * ε (l * ε (l * ε γ)) = 0) :
    ∃ β : k, β - l * ε β = γ := by
  obtain ⟨s1, hs1⟩ : ∃ s, s = l * ε γ := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s, s = l * ε s1 := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ s, s = l * ε s2 := ⟨_, rfl⟩
  rw [← hs1, ← hs2, ← hs3] at hγ h4
  refine ⟨-(a * s1) - (a + ε a) * s2 - (a + ε a + ε (ε a)) * s3, ?_⟩
  simp only [map_sub, map_neg, map_mul, map_add]
  linear_combination (-ε a) * hs2 - (ε a + ε (ε a)) * hs3 +
    (ε a + ε (ε a) + ε (ε (ε a))) * h4 - a * hγ + γ * ha

end Trace

section Coset

variable {U : Type*} [Group U]

theorem exists_fixed_mul_mem_of_twist {k : Type*} [Field k] (X₂ : Subgroup U)
    (x₂ : Multiplicative k →* U) (hx₂ : Function.Injective x₂) (hr₂ : ∀ a, x₂ a ∈ X₂)
    (hs₂ : ∀ y ∈ X₂, ∃ b : k, y = x₂ (ofAdd b)) (θ : U ≃* U)
    (h4 : ∀ u : U, θ (θ (θ (θ u))) = u) (ε : k ≃+* k) (l : k)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd (l * ε b))) {a : k}
    (ha : a + ε a + ε (ε a) + ε (ε (ε a)) = 1) {x : U} (hx : x⁻¹ * θ x ∈ X₂) :
    ∃ v ∈ X₂, θ (x * v) = x * v := by
  obtain ⟨γ, hγ⟩ := hs₂ _ hx
  have hθx : θ x = x * x₂ (ofAdd γ) := by
    rw [← hγ]
    group
  have hx₂add : ∀ b c : k, x₂ (ofAdd b) * x₂ (ofAdd c) = x₂ (ofAdd (b + c)) := fun b c => by
    rw [← map_mul, ← ofAdd_add]
  have hstep : ∀ c : k, θ (x * x₂ (ofAdd c)) = x * x₂ (ofAdd (γ + l * ε c)) := fun c => by
    rw [map_mul, hθx, hθ₂, mul_assoc, hx₂add]
  have hN : γ + l * ε γ + l * ε (l * ε γ) + l * ε (l * ε (l * ε γ)) = 0 := by
    have h := h4 x
    rw [hθx, hstep, hstep, hstep] at h
    have h' : x₂ (ofAdd (γ + l * ε (γ + l * ε (γ + l * ε γ)))) = x₂ (ofAdd 0) := by
      rw [ofAdd_zero, map_one]
      exact mul_left_cancel (h.trans (mul_one x).symm)
    have h'' := Multiplicative.ofAdd.injective (hx₂ h')
    simp only [map_add, map_mul, mul_add] at h'' ⊢
    linear_combination h''
  have hnorm := UnHeisSub.norm_mid_of_inj x₂ hx₂ θ ε l hθ₂ h4 γ
  obtain ⟨β, hβ⟩ := exists_sub_twist_eq ε l a γ hnorm ha hN
  refine ⟨x₂ (ofAdd β), hr₂ _, ?_⟩
  have e : γ + l * ε β = β := by linear_combination -hβ
  rw [hstep, e]

theorem card_fixed_eq_mul_of_exists [Finite U] (θ : U ≃* U) (V : Subgroup U) [V.Normal]
    (hV : ∀ v ∈ V, θ v ∈ V) (hex : ∀ x : U, x⁻¹ * θ x ∈ V → ∃ v ∈ V, θ (x * v) = x * v) :
    Nat.card ↥(foldFix θ) = Nat.card ↥(V ⊓ foldFix θ) *
      Nat.card {x : U ⧸ V // QuotientGroup.map V V θ.toMonoidHom (fun v hv => hV v hv) x = x} := by
  classical
  have hmap : ∀ x : U, QuotientGroup.map V V θ.toMonoidHom (fun v hv => hV v hv)
      (x : U ⧸ V) = ((θ x : U) : U ⧸ V) :=
    fun x => QuotientGroup.map_mk V V θ.toMonoidHom (fun v hv => hV v hv) x
  let π : foldFix θ →* U ⧸ V := (QuotientGroup.mk' V).comp (foldFix θ).subtype
  have hrange : ∀ q : U ⧸ V, q ∈ π.range ↔
      QuotientGroup.map V V θ.toMonoidHom (fun v hv => hV v hv) q = q := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    constructor
    · rintro ⟨y, hy⟩
      have hy' : ((y : U) : U ⧸ V) = (x : U ⧸ V) := hy
      rw [← hy', hmap, mem_foldFix.1 y.2]
    · intro h
      rw [hmap] at h
      obtain ⟨v, hv, hfix⟩ := hex x (QuotientGroup.eq.1 h.symm)
      refine ⟨⟨x * v, hfix⟩, ?_⟩
      show (((x * v : U)) : U ⧸ V) = (x : U ⧸ V)
      exact (QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])).symm
  have hker : ∀ y : foldFix θ, y ∈ π.ker ↔ (y : U) ∈ V := by
    intro y
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff (y : U)
  have hcard : Nat.card π.ker = Nat.card ↥(V ⊓ foldFix θ) :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨(hker y.1).1 y.2, y.1.2⟩⟩
        invFun := fun u => ⟨⟨u.1, (Subgroup.mem_inf.1 u.2).2⟩,
          (hker ⟨u.1, (Subgroup.mem_inf.1 u.2).2⟩).2 (Subgroup.mem_inf.1 u.2).1⟩
        left_inv := fun y => rfl
        right_inv := fun u => rfl }
  have hmul : Nat.card ↥(foldFix θ) = Nat.card π.ker * Nat.card π.range := by
    rw [← Subgroup.index_ker π]
    exact (Subgroup.card_mul_index π.ker).symm
  rw [hmul, hcard]
  exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight hrange))

end Coset

theorem card_fixed_heis_all {p f : ℕ} [Fact p.Prime] (hf : 0 < f)
    {k : Type*} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    {U : Type*} [Group U] [Finite U] (X₁ X₂ X₃ : Subgroup U)
    (x₁ x₂ : Multiplicative k →* U) (hx₁ : Function.Injective x₁) (hx₂ : Function.Injective x₂)
    (hr₁ : ∀ a, x₁ a ∈ X₁) (hr₂ : ∀ a, x₂ a ∈ X₂)
    (hs₁ : ∀ y ∈ X₁, ∃ a : k, y = x₁ (ofAdd a)) (hs₂ : ∀ y ∈ X₂, ∃ b : k, y = x₂ (ofAdd b))
    (hdec : ∀ u : U, ∃! t : U × U × U,
      t.1 ∈ X₁ ∧ t.2.1 ∈ X₂ ∧ t.2.2 ∈ X₃ ∧ u = t.1 * t.2.1 * t.2.2)
    (hnorm₂ : ∀ (u : U), ∀ y ∈ X₂, u * y * u⁻¹ ∈ X₂)
    (hcomm : ∀ u v : U, u * v * u⁻¹ * v⁻¹ ∈ X₂)
    (θ : MulAut U) (hθ4 : θ ^ 4 = 1) (l₂ ν : kˣ)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd ((l₂ : k) * ε b)))
    (hθ₁ : ∀ y ∈ X₁, ∃ b ∈ X₂, ∃ z ∈ X₃, θ y = b * z)
    (hθ₃ : ∀ z ∈ X₃, ∃ b ∈ X₂, ∃ y ∈ X₁, θ z = b * y)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ X₂, θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd ((ν : k) * ε (ε a)))) :
    Nat.card ↥(foldFix (θ : U ≃* U)) = (p ^ f) ^ 3 ∧ IsPGroup p ↥(foldFix (θ : U ≃* U)) ∧
      ∃ y ∈ X₁, y ≠ 1 ∧ ∃ b ∈ X₂, ∃ z ∈ X₃, z ≠ 1 ∧
        y * b * z ∈ foldFix (θ : U ≃* U) := by
  have F : UnHeisSub X₁ X₂ X₃ := ⟨hdec, hnorm₂, hcomm⟩
  have hVn : X₂.Normal := F.normal
  have hp : p.Prime := Fact.out
  have h4 : ∀ u : U, θ (θ (θ (θ u))) = u := by
    intro u
    have := congrArg (fun φ : MulAut U => φ u) hθ4
    simpa [pow_succ, MulAut.mul_apply] using this
  have hVθ : ∀ v ∈ X₂, θ v ∈ X₂ := by
    intro v hv
    obtain ⟨b, rfl⟩ := hs₂ v hv
    rw [hθ₂]
    exact hr₂ _
  have hr2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow hf.ne' p)
  obtain ⟨a₁, ha₁⟩ := exists_frobTrace_eq_one hr2 hk ε hε
  have hex : ∀ x : U, x⁻¹ * (θ : U ≃* U) x ∈ X₂ →
      ∃ v ∈ X₂, (θ : U ≃* U) (x * v) = x * v := fun x hx =>
    exists_fixed_mul_mem_of_twist X₂ x₂ hx₂ hr₂ hs₂ (θ : U ≃* U) h4 ε (l₂ : k) hθ₂ ha₁ hx
  have hmul := card_fixed_eq_mul_of_exists (θ : U ≃* U) X₂ hVθ hex
  have hN₂ : (l₂ : k) ^ (1 + p ^ f + (p ^ f) ^ 2 + (p ^ f) ^ 3) = 1 := by
    have h := UnHeisSub.norm_mid_of_inj x₂ hx₂ (θ : U ≃* U) ε (l₂ : k) hθ₂ h4 1
    simp only [hε] at h
    rw [← h]
    ring
  have hVfix : Nat.card ↥(X₂ ⊓ foldFix (θ : U ≃* U)) = p ^ f := by
    rw [UnHeisSub.card_mid_fixed_of_inj X₂ x₂ hx₂ hr₂ hs₂ (θ : U ≃* U) ε (p ^ f) hε (l₂ : k) hθ₂]
    refine card_fixed_frob_twist (m := 4) (by norm_num) hf hk l₂ ?_
    apply Units.ext
    have hsum : ∑ i ∈ Finset.range 4, (p ^ f) ^ i = 1 + p ^ f + (p ^ f) ^ 2 + (p ^ f) ^ 3 := by
      simp [Finset.sum_range_succ]
    rw [hsum, Units.val_pow_eq_pow_val, Units.val_one]
    exact hN₂
  have hmap : ∀ x : U, QuotientGroup.map X₂ X₂ (θ : U ≃* U).toMonoidHom (fun v hv => hVθ v hv)
      (x : U ⧸ X₂) = (((θ : U ≃* U) x : U) : U ⧸ X₂) :=
    fun x => QuotientGroup.map_mk X₂ X₂ (θ : U ≃* U).toMonoidHom (fun v hv => hVθ v hv) x
  set T := QuotientGroup.map X₂ X₂ (θ : U ≃* U).toMonoidHom (fun v hv => hVθ v hv) with hTdef
  have hR : (p ^ f) ^ 2 = p ^ (2 * f) := (pow_mul' p 2 f).symm
  have hcosets := F.card_fixed_cosets (θ : U ≃* U) T hmap x₁ hx₁ hr₁ hs₁ ε (ν : k) hθ₁ hθ₃ hθ₁₁
  have hsol : ∀ a : k, (ν : k) * ε (ε a) = a ↔ (ν : k) * a ^ (p ^ (2 * f)) = a := by
    intro a
    rw [UnHeisSub.frob_sq ε (p ^ f) (p ^ (2 * f)) hε hR]
  have hν4 : (ν : k) ^ (1 + p ^ (2 * f)) = 1 := by
    have h := F.norm_cosets (θ : U ≃* U) T hmap h4 x₁ hx₁ hr₁ ε (ν : k) hθ₁₁ 1
    simp only [hε] at h
    rw [← hR, ← h]
    ring
  have hcard2 : Nat.card {a : k // (ν : k) * a ^ (p ^ (2 * f)) = a} = p ^ (2 * f) := by
    refine card_fixed_frob_twist (m := 2) (f := 2 * f) (by norm_num) (by omega) ?_ ν ?_
    · rw [hk]
      ring
    · apply Units.ext
      have hsum : ∑ i ∈ Finset.range 2, (p ^ (2 * f)) ^ i = 1 + p ^ (2 * f) := by
        simp [Finset.sum_range_succ]
      rw [hsum, Units.val_pow_eq_pow_val, Units.val_one]
      exact hν4
  have hcard : Nat.card ↥(foldFix (θ : U ≃* U)) = (p ^ f) ^ 3 := by
    rw [hmul, hVfix, hcosets, Nat.card_congr (Equiv.subtypeEquivRight hsol), hcard2]
    ring
  refine ⟨hcard, IsPGroup.of_card (n := f * 3) (by rw [hcard, pow_mul]), ?_⟩
  have hcos2 : 1 < Nat.card {a : k // (ν : k) * a ^ (p ^ (2 * f)) = a} := by
    rw [hcard2]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have := Finite.one_lt_card_iff_nontrivial.1 hcos2
  have h0 : (ν : k) * (0 : k) ^ (p ^ (2 * f)) = 0 := by
    rw [zero_pow (pow_ne_zero _ hp.ne_zero), mul_zero]
  obtain ⟨⟨a, ha⟩, hne⟩ := exists_ne (⟨0, h0⟩ : {a : k // (ν : k) * a ^ (p ^ (2 * f)) = a})
  have ha0 : a ≠ 0 := fun h => hne (Subtype.ext h)
  have ha' : (ν : k) * ε (ε a) = a := (hsol a).2 ha
  have hy : x₁ (ofAdd a) ∈ X₁ := hr₁ _
  have hy1 : x₁ (ofAdd a) ≠ 1 := by
    intro h
    have h' : x₁ (ofAdd a) = x₁ (ofAdd 0) := by rw [h, ofAdd_zero, map_one]
    exact ha0 (Multiplicative.ofAdd.injective (hx₁ h'))
  obtain ⟨z₀, hz₀, hTy⟩ := UnHeisSub.T_X₁ (θ : U ≃* U) T hmap hθ₁ hy
  have hTz : T (z₀ : U ⧸ X₂) = ((x₁ (ofAdd a) : U) : U ⧸ X₂) := by
    rw [← hTy, UnHeisSub.T_T_X₁ (θ : U ≃* U) T hmap x₁ ε (ν : k) hθ₁₁ a, ha']
  have hfixq : T ((x₁ (ofAdd a) * z₀ : U) : U ⧸ X₂) = ((x₁ (ofAdd a) * z₀ : U) : U ⧸ X₂) := by
    rw [QuotientGroup.mk_mul, map_mul, hTy, hTz]
    exact F.quot_comm _ _
  have hx : (x₁ (ofAdd a) * z₀)⁻¹ * (θ : U ≃* U) (x₁ (ofAdd a) * z₀) ∈ X₂ := by
    rw [hmap] at hfixq
    exact QuotientGroup.eq.1 hfixq.symm
  obtain ⟨v, hvV, hvfix⟩ := hex _ hx
  have hb : z₀ * v * z₀⁻¹ ∈ X₂ := hnorm₂ z₀ v hvV
  have hz1 : z₀ ≠ 1 := by
    intro h
    have h1 : ((θ (x₁ (ofAdd a)) : U) : U ⧸ X₂) = ((1 : U) : U ⧸ X₂) := by
      rw [← hmap, hTy, h]
    have h2 : θ (x₁ (ofAdd a)) ∈ X₂ := by
      have := QuotientGroup.eq.1 h1
      simpa using this
    have h3 : x₁ (ofAdd a) ∈ X₂ := by
      have := hVθ _ (hVθ _ (hVθ _ h2))
      rwa [h4] at this
    exact hy1 (F.eq_one_of_mem_inter hy h3)
  refine ⟨x₁ (ofAdd a), hy, hy1, z₀ * v * z₀⁻¹, hb, z₀, hz₀, hz1, ?_⟩
  rw [mem_foldFix]
  have e : x₁ (ofAdd a) * (z₀ * v * z₀⁻¹) * z₀ = x₁ (ofAdd a) * z₀ * v := by group
  rw [e]
  exact hvfix

theorem un_heis_fixed_all {X : Type*} [Group X] (D : RankTwoSystem X 3) {p f : ℕ}
    [Fact p.Prime] (hf : 0 < f) [Finite X]
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f)) (x₁ x₂ : Multiplicative k →* X)
    (hx₁inj : Function.Injective x₁) (hx₂inj : Function.Injective x₂)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₂ : ∀ a, x₂ a ∈ D.root 2)
    (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a) (hx₂s : ∀ y ∈ D.root 2, ∃ a, y = x₂ a)
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (θ : X ≃* X) (hθU : ∀ u ∈ D.U, θ u ∈ D.U) (hθ4 : ∀ y, θ (θ (θ (θ y))) = y) (l₂ ν : kˣ)
    (hθ₂ : ∀ b : k, θ (x₂ (ofAdd b)) = x₂ (ofAdd ((l₂ : k) * ε b)))
    (hθ₁ : ∀ y ∈ D.root 1, ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, θ y = b * z)
    (hθ₃ : ∀ z ∈ D.root 3, ∃ b ∈ D.root 2, ∃ y ∈ D.root 1, θ z = b * y)
    (hθ₁₁ : ∀ a : k, ∃ b ∈ D.root 2,
      θ (θ (x₁ (ofAdd a))) = b * x₁ (ofAdd ((ν : k) * ε (ε a)))) :
    Nat.card ↥(D.U ⊓ foldFix θ) = (p ^ f) ^ 3 ∧
      ∃ y ∈ D.root 1, y ≠ 1 ∧ ∃ b ∈ D.root 2, ∃ z ∈ D.root 3, z ≠ 1 ∧
        θ (y * b * z) = y * b * z := by
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  let θU : ↥D.U ≃* ↥D.U :=
    { toFun := fun u => ⟨θ (u : X), hθU u u.2⟩
      invFun := fun u => ⟨θ (θ (θ (u : X))), hθU _ (hθU _ (hθU _ u.2))⟩
      left_inv := fun u => Subtype.ext (hθ4 (u : X))
      right_inv := fun u => Subtype.ext (hθ4 (u : X))
      map_mul' := fun u v => Subtype.ext (map_mul θ (u : X) (v : X)) }
  have hθU4 : (θU : MulAut ↥D.U) ^ 4 = 1 := by
    ext u
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    exact hθ4 (u : X)
  let y₁ : Multiplicative k →* ↥D.U := x₁.codRestrict D.U fun a => hU1 (hx₁ a)
  let y₂ : Multiplicative k →* ↥D.U := x₂.codRestrict D.U fun a => hU2 (hx₂ a)
  have hdec : ∀ u : ↥D.U, ∃! t : ↥D.U × ↥D.U × ↥D.U,
      t.1 ∈ (D.root 1).subgroupOf D.U ∧ t.2.1 ∈ (D.root 2).subgroupOf D.U ∧
        t.2.2 ∈ (D.root 3).subgroupOf D.U ∧ u = t.1 * t.2.1 * t.2.2 := by
    intro u
    obtain ⟨y, hy, b, hb, z, hz, hu⟩ := un_decomp D u.2
    refine ⟨(⟨y, hU1 hy⟩, ⟨b, hU2 hb⟩, ⟨z, hU3 hz⟩),
      ⟨Subgroup.mem_subgroupOf.2 hy, Subgroup.mem_subgroupOf.2 hb, Subgroup.mem_subgroupOf.2 hz,
        Subtype.ext hu⟩, ?_⟩
    rintro ⟨y', b', z'⟩ ⟨hy', hb', hz', hu'⟩
    obtain ⟨h1, h2, h3⟩ := un_unique D (Subgroup.mem_subgroupOf.1 hy')
      hy (Subgroup.mem_subgroupOf.1 hb') hb (Subgroup.mem_subgroupOf.1 hz') hz
      (by rw [← hu]; exact (congrArg Subtype.val hu').symm)
    exact Prod.ext (Subtype.ext h1) (Prod.ext (Subtype.ext h2) (Subtype.ext h3))
  obtain ⟨hcard, -, y, hy, hy1, b, hb, z, hz, hz1, hfix⟩ := card_fixed_heis_all hf hk ε hε
    ((D.root 1).subgroupOf D.U) ((D.root 2).subgroupOf D.U) ((D.root 3).subgroupOf D.U) y₁ y₂
    (fun a b h => hx₁inj (congrArg Subtype.val h)) (fun a b h => hx₂inj (congrArg Subtype.val h))
    (fun a => Subgroup.mem_subgroupOf.2 (hx₁ _)) (fun a => Subgroup.mem_subgroupOf.2 (hx₂ _))
    (fun y hy => by
      obtain ⟨a, ha⟩ := hx₁s y (Subgroup.mem_subgroupOf.1 hy)
      exact ⟨toAdd a, Subtype.ext ha⟩)
    (fun y hy => by
      obtain ⟨a, ha⟩ := hx₂s y (Subgroup.mem_subgroupOf.1 hy)
      exact ⟨toAdd a, Subtype.ext ha⟩)
    hdec
    (fun u y hy => Subgroup.mem_subgroupOf.2 (D.conj_root₂_mem u.2 (Subgroup.mem_subgroupOf.1 hy)))
    (fun u v => Subgroup.mem_subgroupOf.2 (D.commutator_mem_root₂ hab₁ hab₃ u.2 v.2))
    θU hθU4 l₂ ν (fun b => Subtype.ext (hθ₂ b))
    (fun y hy => by
      obtain ⟨b, hb, z, hz, h⟩ := hθ₁ y (Subgroup.mem_subgroupOf.1 hy)
      exact ⟨⟨b, hU2 hb⟩, Subgroup.mem_subgroupOf.2 hb, ⟨z, hU3 hz⟩,
        Subgroup.mem_subgroupOf.2 hz, Subtype.ext h⟩)
    (fun z hz => by
      obtain ⟨b, hb, y, hy, h⟩ := hθ₃ z (Subgroup.mem_subgroupOf.1 hz)
      exact ⟨⟨b, hU2 hb⟩, Subgroup.mem_subgroupOf.2 hb, ⟨y, hU1 hy⟩,
        Subgroup.mem_subgroupOf.2 hy, Subtype.ext h⟩)
    (fun a => by
      obtain ⟨b, hb, h⟩ := hθ₁₁ a
      exact ⟨⟨b, hU2 hb⟩, Subgroup.mem_subgroupOf.2 hb, Subtype.ext h⟩)
  refine ⟨?_, (y : X), Subgroup.mem_subgroupOf.1 hy, fun h => hy1 (Subtype.ext h), (b : X),
    Subgroup.mem_subgroupOf.1 hb, (z : X), Subgroup.mem_subgroupOf.1 hz,
    fun h => hz1 (Subtype.ext h), congrArg Subtype.val (mem_foldFix.1 hfix)⟩
  rw [← hcard]
  exact Nat.card_congr
    { toFun := fun w => ⟨⟨(w : X), (Subgroup.mem_inf.1 w.2).1⟩,
        Subtype.ext (mem_foldFix.1 (Subgroup.mem_inf.1 w.2).2)⟩
      invFun := fun v => ⟨(v.1 : X),
        Subgroup.mem_inf.2 ⟨v.1.2, mem_foldFix.2 (congrArg Subtype.val v.2)⟩⟩
      left_inv := fun w => rfl
      right_inv := fun v => rfl }

end CFSG.HardMathSupport.Timmesfeld.CrossChar
