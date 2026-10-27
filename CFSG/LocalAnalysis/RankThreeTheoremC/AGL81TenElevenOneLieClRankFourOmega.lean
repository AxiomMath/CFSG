module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SOrthMinus
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace LieClAut

variable {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal]

theorem exists_pow_orderOf_three {α : G} (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαN : α ∉ N) :
    ∃ j : ℕ, 1 ≤ j ∧ orderOf (QuotientGroup.mk' N α) = 3 ^ j := by
  obtain ⟨k, hk⟩ := hα
  have h1 : (QuotientGroup.mk' N α) ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h1)
  refine ⟨j, Nat.one_le_iff_ne_zero.2 fun h0 => hαN ?_, hj⟩
  rw [h0, pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj
  exact hj

theorem mem_of_cyclic_quotient {τ : G} (hτ : ∀ g, ∃ k : ℕ, (τ ^ k)⁻¹ * g ∈ N) {H : Subgroup G}
    (hNH : N ≤ H) {α : G} (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαN : α ∉ N)
    {β : G} (hβ : β ^ 3 = 1) (hβN : β ∉ N) : β ∈ H := by
  classical
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set π := QuotientGroup.mk' N with hπ
  haveI : IsCyclic (G ⧸ N) := ⟨⟨π τ, fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨k, hk⟩ := hτ g
    refine ⟨k, ?_⟩
    simp only [zpow_natCast]
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hk⟩⟩
  obtain ⟨j, hj1, hj⟩ := exists_pow_orderOf_three hα hαN
  set a := π α ^ 3 ^ (j - 1) with ha
  have ha3 : orderOf a = 3 := by
    rw [ha, orderOf_pow' _ (pow_ne_zero _ three_ne_zero), hj]
    have h3 : 3 ^ j = 3 ^ (j - 1) * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel hj1]
    rw [h3, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hsub : (Subgroup.zpowers a : Set (G ⧸ N)).toFinset ⊆
      Finset.univ.filter fun x : G ⧸ N => x ^ 3 = 1 := fun x hx => by
    rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha3,
      pow_orderOf_eq_one, one_zpow]
  have hcard : (Finset.univ.filter fun x : G ⧸ N => x ^ 3 = 1).card ≤
      (Subgroup.zpowers a : Set (G ⧸ N)).toFinset.card := by
    have h3 : (Subgroup.zpowers a : Set (G ⧸ N)).toFinset.card = 3 := by
      rw [← Nat.card_eq_card_toFinset]
      exact (Nat.card_zpowers a).trans ha3
    rw [h3]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hb : π β ∈ (Subgroup.zpowers a : Set (G ⧸ N)).toFinset := by
    rw [heq, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [← map_pow, hβ, map_one]⟩
  rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hb
  obtain ⟨n, hn⟩ := hb
  rw [ha, ← map_pow, ← map_zpow, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hn
  have h1 : β = (α ^ 3 ^ (j - 1)) ^ n * (((α ^ 3 ^ (j - 1)) ^ n)⁻¹ * β) := by group
  rw [h1]
  exact H.mul_mem (H.zpow_mem (H.pow_mem hαH _) _) (hNH hn)

theorem three_dvd_of_cyclic_quotient {τ : G} (hτ : ∀ g, ∃ k : ℕ, (τ ^ k)⁻¹ * g ∈ N) {m : ℕ}
    (hm : τ ^ m ∈ N) {α : G} (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαN : α ∉ N) : 3 ∣ m := by
  obtain ⟨j, hj1, hj⟩ := exists_pow_orderOf_three hα hαN
  obtain ⟨k, hk⟩ := hτ α
  have h1 : QuotientGroup.mk' N α = QuotientGroup.mk' N τ ^ k := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (α)⁻¹ * τ ^ k = ((τ ^ k)⁻¹ * α)⁻¹ := by group
    rw [this]
    exact N.inv_mem hk
  have h2 : (QuotientGroup.mk' N α) ^ m = 1 := by
    rw [h1, ← pow_mul, mul_comm, pow_mul, ← map_pow, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff _).2 hm, one_pow]
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hj] at h3
  exact (dvd_pow_self 3 (by omega)).trans h3

end LieClAut

namespace OmegaE27

open CFSG.SectionRank.ClassicalEven.OrthRot Matrix

variable {ι ι' : Type} {K : Type} [Field K]

theorem isPolar_comp (e : ι ≃ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q' v = Q (v ∘ e)) {a : ι → K} {f : (ι → K) →ₗ[K] K} {q : K}
    (h : IsPolar Q a f q) :
    IsPolar Q' (a ∘ e.symm) (f.comp (LinearMap.funLeft K K e)) q :=
  fun v t => by
    have h2 : (v + t • (a ∘ e.symm)) ∘ e = v ∘ e + t • a := by
      funext i
      simp
    rw [hQ, hQ, h2, h (v ∘ e) t]
    rfl

@[expose] def comap (e : ι ≃ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q' v = Q (v ∘ e)) (P : Plane Q) : Plane Q' where
  a := P.a ∘ e.symm
  b := P.b ∘ e.symm
  f := P.f.comp (LinearMap.funLeft K K e)
  g := P.g.comp (LinearMap.funLeft K K e)
  isPolar_a := isPolar_comp e hQ P.isPolar_a
  isPolar_b := isPolar_comp e hQ P.isPolar_b
  f_b := by
    have : (P.b ∘ e.symm) ∘ e = P.b := by
      funext i
      simp
    show P.f ((P.b ∘ e.symm) ∘ e) = 1
    rw [this, P.f_b]

theorem orth_comap (e : ι ≃ ι') {Q : (ι → K) → K} {Q' : (ι' → K) → K}
    (hQ : ∀ v, Q' v = Q (v ∘ e)) {P P' : Plane Q} (h : P.Orth P') :
    (comap e hQ P).Orth (comap e hQ P') := by
  have ha : (P'.a ∘ e.symm) ∘ e = P'.a := by
    funext i
    simp
  have hb : (P'.b ∘ e.symm) ∘ e = P'.b := by
    funext i
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · show P.f ((P'.a ∘ e.symm) ∘ e) = 0
    rw [ha, h.f_a]
  · show P.f ((P'.b ∘ e.symm) ∘ e) = 0
    rw [hb, h.f_b]
  · show P.g ((P'.a ∘ e.symm) ∘ e) = 0
    rw [ha, h.g_a]
  · show P.g ((P'.b ∘ e.symm) ∘ e) = 0
    rw [hb, h.g_b]

structure Fixed [DecidableEq ι] (σ : K ≃+* K) {Q : (ι → K) → K} (P : Plane Q) : Prop where
  a : ∀ i, σ (P.a i) = P.a i
  b : ∀ i, σ (P.b i) = P.b i
  f : ∀ j, σ (P.f (Pi.single j 1)) = P.f (Pi.single j 1)
  g : ∀ j, σ (P.g (Pi.single j 1)) = P.g (Pi.single j 1)

theorem single_comp [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') (j : ι') :
    (Pi.single j (1 : K) : ι' → K) ∘ e = Pi.single (e.symm j) 1 := by
  funext i
  simp only [Function.comp_apply, Pi.single_apply, Equiv.eq_symm_apply]

theorem fixed_comap [DecidableEq ι] [DecidableEq ι'] (σ : K ≃+* K) (e : ι ≃ ι')
    {Q : (ι → K) → K} {Q' : (ι' → K) → K} (hQ : ∀ v, Q' v = Q (v ∘ e)) {P : Plane Q}
    (h : Fixed σ P) : Fixed σ (comap e hQ P) := by
  refine ⟨fun i => h.a _, fun i => h.b _, fun j => ?_, fun j => ?_⟩
  · show σ (P.f ((Pi.single j 1 : ι' → K) ∘ e)) = P.f ((Pi.single j 1 : ι' → K) ∘ e)
    rw [single_comp, h.f]
  · show σ (P.g ((Pi.single j 1 : ι' → K) ∘ e)) = P.g ((Pi.single j 1 : ι' → K) ∘ e)
    rw [single_comp, h.g]

theorem map_single [DecidableEq ι] (σ : K ≃+* K) (x i : ι) :
    σ ((Pi.single x (1 : K) : ι → K) i) = (Pi.single x 1 : ι → K) i := by
  by_cases h : i = x
  · subst h
    simp
  · simp [Pi.single_apply, h]

section HPlane

variable [DecidableEq ι] {Q : (ι → K) → K}

@[expose] def hplane {x y : ι} (hxy : x ≠ y)
    (hx : IsPolar Q (Pi.single x 1) (LinearMap.proj y) 0)
    (hy : IsPolar Q (Pi.single y 1) (LinearMap.proj x) 0) {u : ι → K} {φ : (ι → K) →ₗ[K] K}
    (hu : IsPolar Q u φ 1) (hux : u x = 0) (huy : u y = 0) : Plane Q where
  a := Pi.single x 1 + Pi.single y 1
  b := Pi.single x 1 + u
  f := LinearMap.proj y + LinearMap.proj x
  g := LinearMap.proj y + φ
  isPolar_a := hx.add hy (by simp)
  isPolar_b := hx.add hu (by rw [← hx.symm hu]; simp [huy])
  f_b := by simp [hxy, hxy.symm, hux, huy]

theorem hplane_fixed (σ : K ≃+* K) {x y : ι} (hxy : x ≠ y)
    (hx : IsPolar Q (Pi.single x 1) (LinearMap.proj y) 0)
    (hy : IsPolar Q (Pi.single y 1) (LinearMap.proj x) 0) {u : ι → K} {φ : (ι → K) →ₗ[K] K}
    (hu : IsPolar Q u φ 1) (hux : u x = 0) (huy : u y = 0) (hσu : ∀ i, σ (u i) = u i)
    (hσφ : ∀ j, σ (φ (Pi.single j 1)) = φ (Pi.single j 1)) :
    Fixed σ (hplane hxy hx hy hu hux huy) := by
  refine ⟨fun i => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩
  · show σ ((Pi.single x 1 : ι → K) i + (Pi.single y 1 : ι → K) i) = _ + _
    rw [map_add, map_single, map_single]
  · show σ ((Pi.single x 1 : ι → K) i + u i) = _ + _
    rw [map_add, map_single, hσu]
  · show σ ((Pi.single j 1 : ι → K) y + (Pi.single j 1 : ι → K) x) = _ + _
    rw [map_add, map_single, map_single]
    rfl
  · show σ ((Pi.single j 1 : ι → K) y + φ (Pi.single j 1)) = _ + _
    rw [map_add, map_single, hσφ]
    rfl

theorem hplane_orth {x y x' y' : ι} {hxy : x ≠ y}
    {hx : IsPolar Q (Pi.single x 1) (LinearMap.proj y) 0}
    {hy : IsPolar Q (Pi.single y 1) (LinearMap.proj x) 0} {u : ι → K} {φ : (ι → K) →ₗ[K] K}
    {hu : IsPolar Q u φ 1} {hux : u x = 0} {huy : u y = 0} {hxy' : x' ≠ y'}
    {hx' : IsPolar Q (Pi.single x' 1) (LinearMap.proj y') 0}
    {hy' : IsPolar Q (Pi.single y' 1) (LinearMap.proj x') 0} {u' : ι → K}
    {φ' : (ι → K) →ₗ[K] K} {hu' : IsPolar Q u' φ' 1} {hux' : u' x' = 0} {huy' : u' y' = 0}
    (h1 : x' ≠ x) (h2 : x' ≠ y) (h3 : y' ≠ x) (h4 : y' ≠ y)
    (h₁ : u' y + u' x = 0) (h₂ : u y' + u x' = 0) (h₃ : u' y + u y' + φ u' = 0) :
    (hplane hxy hx hy hu hux huy).Orth (hplane hxy' hx' hy' hu' hux' huy') := by
  have e1 := hx'.symm hu
  have e2 := hy'.symm hu
  simp only [LinearMap.proj_apply] at e1 e2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Pi.single x' 1 + Pi.single y' 1 : ι → K) y + (Pi.single x' 1 + Pi.single y' 1 : ι → K) x
      = 0
    simp [Pi.single_apply, h1.symm, h2.symm, h3.symm, h4.symm]
  · show (Pi.single x' 1 + u' : ι → K) y + (Pi.single x' 1 + u' : ι → K) x = 0
    simp only [Pi.add_apply, Pi.single_apply, h1.symm, h2.symm, if_false, zero_add]
    exact h₁
  · show (Pi.single x' 1 + Pi.single y' 1 : ι → K) y + φ (Pi.single x' 1 + Pi.single y' 1) = 0
    rw [map_add, ← e1, ← e2]
    simp only [Pi.add_apply, Pi.single_apply, h2.symm, h4.symm, if_false, zero_add]
    exact h₂
  · show (Pi.single x' 1 + u' : ι → K) y + φ (Pi.single x' 1 + u') = 0
    rw [map_add, ← e1]
    simp only [Pi.add_apply, Pi.single_apply, h2.symm, if_false, zero_add]
    linear_combination h₃

end HPlane

variable [Fintype ι] [DecidableEq ι] [CharP K 2]

theorem rot_apply {Q : (ι → K) → K} (P : Plane Q) (i j : ι) :
    (P.rot : Matrix ι ι K) i j = Pi.single (M := fun _ => K) j 1 i +
      (P.f (Pi.single j 1) + P.g (Pi.single j 1)) * P.a i + P.g (Pi.single j 1) * P.b i := by
  have h := congrFun (P.rot_mulVec (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h
  simpa using h

theorem map_rot {σ : K ≃+* K} {Q : (ι → K) → K} {P : Plane Q} (h : Fixed σ P) (i j : ι) :
    σ ((P.rot : Matrix ι ι K) i j) = (P.rot : Matrix ι ι K) i j := by
  rw [rot_apply]
  simp only [map_add, map_mul, h.a, h.b, h.f, h.g, map_single]

theorem rot_b {Q : (ι → K) → K} (P : Plane Q) : (P.rot : Matrix ι ι K) *ᵥ P.b = P.a + P.b := by
  rw [Plane.rot_mulVec, P.f_b, P.g_b, add_zero, one_smul, zero_smul, add_zero, add_comm]

theorem eq_zero_of_rot_pow {Q : (ι → K) → K} (P : Plane Q) (x : ZMod 3)
    (h : ((P.rot ^ x.val : GL ι K) : Matrix ι ι K) *ᵥ P.a = P.a) : x = 0 := by
  rcases SpE27.zmod3_cases x with rfl | rfl | rfl
  · rfl
  · exfalso
    rw [show (1 : ZMod 3).val = 1 from rfl, pow_one, Plane.rot_a] at h
    exact P.b_ne_smul_a 1 (by rw [one_smul, h])
  · exfalso
    rw [show (2 : ZMod 3).val = 2 from rfl, pow_two, mul_mulVec, Plane.rot_a, rot_b] at h
    exact P.b_ne_smul_a 0 (by rw [zero_smul]; simpa using h)

theorem pow_fix_of_orth {Q : (ι → K) → K} {P P' : Plane Q} (h : P.Orth P') (k m : ℕ) :
    ((P.rot ^ k : GL ι K) : Matrix ι ι K) *ᵥ (((P'.rot ^ m : GL ι K) : Matrix ι ι K) *ᵥ P'.a) =
      ((P'.rot ^ m : GL ι K) : Matrix ι ι K) *ᵥ P'.a := by
  rw [← mul_mulVec, ((Plane.rot_commute h).pow_pow k m).eq, mul_mulVec,
    pow_mulVec_of_fix (P.rot_fix h.f_a h.g_a)]

theorem eq_zero_of_rots {Q : (ι → K) → K} {P₀ P₁ P₂ : Plane Q} (h₀₁ : P₀.Orth P₁)
    (h₀₂ : P₀.Orth P₂) (h₁₂ : P₁.Orth P₂) (v : Fin 3 → ZMod 3)
    (h : P₀.rot ^ (v 0).val * P₁.rot ^ (v 1).val * P₂.rot ^ (v 2).val = 1) : v = 0 := by
  have h2 : v 2 = 0 := by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ P₂.a) h
    simp only [mul_mulVec, Units.val_one, one_mulVec] at this
    rw [pow_fix_of_orth h₁₂, pow_fix_of_orth h₀₂] at this
    exact eq_zero_of_rot_pow P₂ _ this
  rw [h2, show (0 : ZMod 3).val = 0 from rfl, pow_zero, mul_one] at h
  have h1 : v 1 = 0 := by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ P₁.a) h
    simp only [mul_mulVec, Units.val_one, one_mulVec] at this
    rw [pow_fix_of_orth h₀₁] at this
    exact eq_zero_of_rot_pow P₁ _ this
  rw [h1, show (0 : ZMod 3).val = 0 from rfl, pow_zero, mul_one] at h
  have h0 : v 0 = 0 := by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ P₀.a) h
    simp only [Units.val_one, one_mulVec] at this
    exact eq_zero_of_rot_pow P₀ _ this
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

section Triple

variable {H : Type*} [Group H]

theorem pow_val_add {x : H} (hx : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 3]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def tripleHom (z₀ z₁ z₂ : H) (h₀ : z₀ ^ 3 = 1) (h₁ : z₁ ^ 3 = 1) (h₂ : z₂ ^ 3 = 1)
    (c₀₁ : Commute z₀ z₁) (c₀₂ : Commute z₀ z₂) (c₁₂ : Commute z₁ z₂) :
    Multiplicative (Fin 3 → ZMod 3) →* H where
  toFun v := z₀ ^ (v.toAdd 0).val * z₁ ^ (v.toAdd 1).val * z₂ ^ (v.toAdd 2).val
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply, pow_val_add h₀, pow_val_add h₁, pow_val_add h₂]
    set p0 := z₀ ^ (v.toAdd 0).val
    set p1 := z₁ ^ (v.toAdd 1).val
    set p2 := z₂ ^ (v.toAdd 2).val
    set q0 := z₀ ^ (w.toAdd 0).val
    set q1 := z₁ ^ (w.toAdd 1).val
    set q2 := z₂ ^ (w.toAdd 2).val
    have h01 : q0 * p1 = p1 * q0 := (c₀₁.pow_pow _ _).eq
    have h02 : q0 * p2 = p2 * q0 := (c₀₂.pow_pow _ _).eq
    have h12 : q1 * p2 = p2 * q1 := (c₁₂.pow_pow _ _).eq
    calc p0 * q0 * (p1 * q1) * (p2 * q2) = p0 * (q0 * p1) * q1 * p2 * q2 := by group
      _ = p0 * p1 * q0 * (q1 * p2) * q2 := by rw [h01]; group
      _ = p0 * p1 * (q0 * p2) * q1 * q2 := by rw [h12]; group
      _ = p0 * p1 * p2 * (q0 * q1 * q2) := by rw [h02]; group

theorem tripleHom_apply (z₀ z₁ z₂ : H) (h₀ : z₀ ^ 3 = 1) (h₁ : z₁ ^ 3 = 1) (h₂ : z₂ ^ 3 = 1)
    (c₀₁ : Commute z₀ z₁) (c₀₂ : Commute z₀ z₂) (c₁₂ : Commute z₁ z₂)
    (v : Multiplicative (Fin 3 → ZMod 3)) :
    tripleHom z₀ z₁ z₂ h₀ h₁ h₂ c₀₁ c₀₂ c₁₂ v =
      z₀ ^ (v.toAdd 0).val * z₁ ^ (v.toAdd 1).val * z₂ ^ (v.toAdd 2).val := rfl

end Triple

section Minus

open CFSG.Open

variable {n : ℕ} (hn : 4 ≤ n) (b c : K)

@[expose] def jdx (k : ℕ) (hk : k < 3) : Fin (n - 1) := ⟨k, by omega⟩

theorem jdx_ne {k l : ℕ} {hk : k < 3} {hl : l < 3} (h : k ≠ l) :
    jdx (n := n) hn k hk ≠ jdx hn l hl := fun e => h (congrArg Fin.val e)

@[expose] def hypV (j : Fin (n - 1)) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (.inl j) 1 + Pi.single (.inr (.inl j)) 1

@[expose] def hypL (j : Fin (n - 1)) : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] K :=
  LinearMap.proj (.inr (.inl j)) + LinearMap.proj (.inl j)

theorem isPolar_hypV (j : Fin (n - 1)) :
    IsPolar (StatedQuadMinus n K b c) (hypV j) (hypL j) 1 :=
  (isPolar_minus_inl b c j).add (isPolar_minus_inr b c j) (by simp)

theorem hypV_apply_inl {j j' : Fin (n - 1)} (h : j' ≠ j) : (hypV (K := K) j) (.inl j') = 0 := by
  simp [hypV, Pi.single_apply, h]

theorem hypV_apply_inr {j j' : Fin (n - 1)} (h : j' ≠ j) :
    (hypV (K := K) j) (.inr (.inl j')) = 0 := by
  simp [hypV, Pi.single_apply, h]

@[expose] def uL : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) →ₗ[K] K :=
  (2 : K) • LinearMap.proj (.inr (.inr 0)) + b • LinearMap.proj (.inr (.inr 1))

@[expose] def mP₀ : Plane (StatedQuadMinus n K b c) :=
  hplane Sum.inl_ne_inr (isPolar_minus_inl b c (jdx hn 0 (by omega)))
    (isPolar_minus_inr b c (jdx hn 0 (by omega))) (isPolar_hypV b c (jdx hn 1 (by omega)))
    (hypV_apply_inl (jdx_ne hn (by omega))) (hypV_apply_inr (jdx_ne hn (by omega)))

@[expose] def mP₁ : Plane (StatedQuadMinus n K b c) :=
  hplane Sum.inl_ne_inr (isPolar_minus_inl b c (jdx hn 1 (by omega)))
    (isPolar_minus_inr b c (jdx hn 1 (by omega))) (isPolar_hypV b c (jdx hn 0 (by omega)))
    (hypV_apply_inl (jdx_ne hn (by omega))) (hypV_apply_inr (jdx_ne hn (by omega)))

@[expose] def mP₂ : Plane (StatedQuadMinus n K b c) :=
  hplane Sum.inl_ne_inr (isPolar_minus_inl b c (jdx hn 2 (by omega)))
    (isPolar_minus_inr b c (jdx hn 2 (by omega))) (u := Pi.single (.inr (.inr 0)) 1)
    (φ := uL b) (isPolar_minus_u b c) (by simp) (by simp)

variable [CharP K 2]

theorem mP₀_orth_mP₁ : (mP₀ hn b c).Orth (mP₁ hn b c) := by
  have h01 := jdx_ne (n := n) hn (k := 0) (l := 1) (hk := by omega) (hl := by omega) (by omega)
  refine hplane_orth (by simpa using h01.symm) (by simp) (by simp) (by simpa using h01.symm)
    ?_ ?_ ?_
  · simp [hypV, Pi.single_apply, CharTwo.add_self_eq_zero]
  · simp [hypV, Pi.single_apply, CharTwo.add_self_eq_zero]
  · simp [hypV, hypL, Pi.single_apply, h01, h01.symm, CharTwo.add_self_eq_zero]

theorem mP₀_orth_mP₂ : (mP₀ hn b c).Orth (mP₂ hn b c) := by
  have h02 := jdx_ne (n := n) hn (k := 0) (l := 2) (hk := by omega) (hl := by omega) (by omega)
  have h12 := jdx_ne (n := n) hn (k := 1) (l := 2) (hk := by omega) (hl := by omega) (by omega)
  refine hplane_orth (by simpa using h02.symm) (by simp) (by simp) (by simpa using h02.symm)
    ?_ ?_ ?_
  · simp
  · simp [hypV, Pi.single_apply, h12.symm]
  · simp [hypV, hypL, Pi.single_apply, h12.symm]

theorem mP₁_orth_mP₂ : (mP₁ hn b c).Orth (mP₂ hn b c) := by
  have h02 := jdx_ne (n := n) hn (k := 0) (l := 2) (hk := by omega) (hl := by omega) (by omega)
  have h12 := jdx_ne (n := n) hn (k := 1) (l := 2) (hk := by omega) (hl := by omega) (by omega)
  refine hplane_orth (by simpa using h12.symm) (by simp) (by simp) (by simpa using h12.symm)
    ?_ ?_ ?_
  · simp
  · simp [hypV, Pi.single_apply, h02.symm]
  · simp [hypV, hypL, Pi.single_apply, h02.symm]

variable {b} in
theorem mP_fixed (σ : K ≃+* K) (hb : σ b = b) :
    Fixed σ (mP₀ hn b c) ∧ Fixed σ (mP₁ hn b c) ∧ Fixed σ (mP₂ hn b c) := by
  have hv : ∀ (j : Fin (n - 1)) i, σ (hypV (K := K) j i) = hypV j i := fun j i => by
    simp only [hypV, Pi.add_apply, map_add, map_single]
  have hl : ∀ (j : Fin (n - 1)) i,
      σ (hypL (K := K) j (Pi.single i 1)) = hypL j (Pi.single i 1) := fun j i => by
    simp only [hypL, LinearMap.add_apply, LinearMap.proj_apply, map_add, map_single]
  refine ⟨hplane_fixed σ _ _ _ _ _ _ (hv _) (hl _), hplane_fixed σ _ _ _ _ _ _ (hv _) (hl _),
    hplane_fixed σ _ _ _ _ _ _ (map_single σ _) fun j => ?_⟩
  simp only [uL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
    map_add, map_mul, map_ofNat, hb, map_single]

end Minus


section Coord

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.RankThree.PartOne.KCOrthogonalSubfield

variable [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n) (b c : K)

theorem Qm_apply (v : Fin (2 * n) → K) :
    Qm n hn b c v = StatedQuadMinus n K b c (v ∘ minusIndexEquiv n (by omega)) := by
  show reindexQuadraticForm _ _ v = _
  rw [reindexQuadraticForm_apply, CFSG.LieType.Universal.Spin.quadMinus_apply]
  rfl

@[expose] noncomputable def cP (k : Fin 3) : Plane (⇑(Qm n hn b c)) :=
  comap (minusIndexEquiv n (by omega)) (Qm_apply hn b c)
    (![mP₀ hn b c, mP₁ hn b c, mP₂ hn b c] k)

theorem cP_orth {k l : Fin 3} (h : k < l) : (cP hn b c k).Orth (cP hn b c l) := by
  apply orth_comap
  fin_cases k <;> fin_cases l <;> simp at h
  · exact mP₀_orth_mP₁ hn b c
  · exact mP₀_orth_mP₂ hn b c
  · exact mP₁_orth_mP₂ hn b c

theorem cP_rot_mem (k : Fin 3) : (cP hn b c k).rot ∈ matrixDerived (Qm n hn b c) := by
  rw [matrixDerived_eq_statedOmega]
  exact Plane.rot_mem _

@[expose] noncomputable def cz (k : Fin 3) : matrixDerived (Qm n hn b c) :=
  ⟨(cP hn b c k).rot, cP_rot_mem hn b c k⟩

theorem cz_pow_three (k : Fin 3) : cz hn b c k ^ 3 = 1 :=
  Subtype.ext (by simp only [cz, Subgroup.coe_pow, Plane.rot_pow_three, Subgroup.coe_one])

theorem cz_commute {k l : Fin 3} (h : k < l) : Commute (cz hn b c k) (cz hn b c l) :=
  Subtype.ext (Plane.rot_commute (cP_orth hn b c h)).eq

@[expose] noncomputable def e27 : Multiplicative (Fin 3 → ZMod 3) →* matrixDerived (Qm n hn b c) :=
  tripleHom (cz hn b c 0) (cz hn b c 1) (cz hn b c 2) (cz_pow_three hn b c 0)
    (cz_pow_three hn b c 1) (cz_pow_three hn b c 2) (cz_commute hn b c (by decide))
    (cz_commute hn b c (by decide)) (cz_commute hn b c (by decide))

theorem e27_injective : Function.Injective (e27 hn b c) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h := congrArg Subtype.val hv
  simp only [e27, tripleHom_apply, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, cz] at h
  exact Multiplicative.toAdd.injective (eq_zero_of_rots (cP_orth hn b c (by decide))
    (cP_orth hn b c (by decide)) (cP_orth hn b c (by decide)) _ h)

variable {b} in
theorem cz_fixed (σ : K ≃+* K) (hb : σ b = b) (k : Fin 3) (i j : Fin (2 * n)) :
    σ (((cz hn b c k).val : Matrix _ _ K) i j) = ((cz hn b c k).val : Matrix _ _ K) i j := by
  obtain ⟨h₀, h₁, h₂⟩ := mP_fixed hn c σ hb
  refine map_rot (fixed_comap σ _ _ ?_) i j
  fin_cases k
  · exact h₀
  · exact h₁
  · exact h₂

variable {b c} in
theorem fieldPair_e27 (σ : K ≃+* K) (hb : σ b = b)
    (hQσ : ∀ v, Qm n hn b c (coordinateFieldMap (2 * n) σ v) = σ (Qm n hn b c v))
    (a : Multiplicative (Fin 3 → ZMod 3)) :
    conjAct (Qm n hn b c) (fieldPair (Qm n hn b c) σ hQσ) (e27 hn b c a) = e27 hn b c a := by
  have hz : ∀ k, conjAct (Qm n hn b c) (fieldPair (Qm n hn b c) σ hQσ) (cz hn b c k) =
      cz hn b c k := fun k => by
    apply Subtype.ext
    rw [conjAct_apply, matrixDerivedConjugation_val, fieldPair_left, fieldPair_right, one_mul,
      inv_one, mul_one]
    ext i j
    exact cz_fixed hn c σ hb k i j
  simp only [e27, tripleHom_apply, map_mul, map_pow, hz]

end Coord

section Beta

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.ComponentClassification

variable {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem right_eq_one_of_conjAct_eq_one (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : CatalogueBOrthogonalPointAction.ActionProperties Q (projectivePointAction Q))
    {g : similarityPairs Q} (hg : conjAct Q g = 1) : g.val.right = 1 := by
  have h1 : matrixProjectiveConjugationHom Q g = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
    change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q A
    rw [matrixProjectiveConjugation_mk]
    congr 1
    have := congrArg (fun α : MulAut (matrixDerived Q) => α A) hg
    exact this
  exact ((CFSG.RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff Q hnd
    hS3 hAP g).1 h1).1

variable (σ : K ≃+* K) (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))

theorem conjAct_fieldPair_pow_three (hσ3 : σ ^ 3 = 1) :
    conjAct Q (fieldPair Q σ hQσ) ^ 3 = 1 := by
  have : fieldPair Q σ hQσ ^ 3 = 1 :=
    Subtype.ext (by rw [fieldPair_pow_val, hσ3, map_one]; rfl)
  rw [← map_pow, this, map_one]

theorem conjAct_fieldPair_not_inner (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : CatalogueBOrthogonalPointAction.ActionProperties Q (projectivePointAction Q))
    (hσ1 : σ ≠ 1) :
    conjAct Q (fieldPair Q σ hQσ) ∉ OuterAutomorphisms.inner (matrixDerived Q) := by
  rintro ⟨y, hy⟩
  let B : matrixIsometries Q := ⟨y.val, matrixDerived_le_isometries Q y.2⟩
  have h1 : conjAct Q (fieldPair Q σ hQσ * (matrixIsometryInclusion Q B)⁻¹) = 1 := by
    rw [map_mul, map_inv, conjAct_inclusion_of_mem B y.2, ← hy]
    exact mul_inv_cancel _
  have h2 := right_eq_one_of_conjAct_eq_one hnd hS3 hAP h1
  apply hσ1
  rw [← h2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
    SemidirectProduct.inv_right, matrixIsometryInclusion_val, SemidirectProduct.right_inl,
    fieldPair_right, inv_one, mul_one]

end Beta

section Main

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.ComponentClassification

variable [Finite K] [CharP K 2]

theorem exists_rankFour_omega {X : Type} [Group X] [Finite X] (hc : Subgroup.center X = ⊥)
    {n : ℕ} (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hb : σ b = b)
    (hcσ : σ c = c) (e : X ≃* matrixDerived (Qm n hn b c)) {H : Subgroup (MulAut X)}
    (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X} (hαH : α ∈ H)
    (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  obtain ⟨τ, hτ, -⟩ := exists_frobenius_class n hn b c hirr hf
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n K b c hn hirr
  have hAP := coordinate_minus_point_action_properties n K b c hn hirr
  have hQσ : ∀ v, Qm n hn b c (coordinateFieldMap (2 * n) σ v) = σ (Qm n hn b c v) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S.coordinateQuadMinus_fieldAut_of_fixed n
      (by omega) hb hcσ
  set Ψ : MulAut X ≃* MulAut (matrixDerived (Qm n hn b c)) := MulAut.congr e with hΨ
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext p
    simp [hΨ]
  have hΨinv : ∀ p, Ψ.symm (MulAut.conj p) = MulAut.conj (e.symm p) := fun p => by
    rw [MulEquiv.symm_apply_eq, hΨconj, e.apply_symm_apply]
  have hinnΨ : ∀ β, β ∈ (MulAut.conj : X →* MulAut X).range →
      Ψ β ∈ OuterAutomorphisms.inner (matrixDerived (Qm n hn b c)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, (hΨconj x).symm⟩
  have hinnΨ' : ∀ γ, γ ∈ OuterAutomorphisms.inner (matrixDerived (Qm n hn b c)) →
      Ψ.symm γ ∈ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨e.symm p, (hΨinv p).symm⟩
  haveI : (MulAut.conj : X →* MulAut X).range.Normal := OuterAutomorphisms.inner_normal X
  set β := Ψ.symm (conjAct (Qm n hn b c) (fieldPair (Qm n hn b c) σ hQσ)) with hβ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow, conjAct_fieldPair_pow_three σ hQσ hσ3, map_one]
  have hβn : β ∉ (MulAut.conj : X →* MulAut X).range := fun h => by
    have := hinnΨ _ h
    rw [hβ, Ψ.apply_symm_apply] at this
    exact conjAct_fieldPair_not_inner σ hQσ hnd hT hAP hσ1 this
  have hτ' : ∀ g : MulAut X, ∃ k : ℕ, ((Ψ.symm τ) ^ k)⁻¹ * g ∈
      (MulAut.conj : X →* MulAut X).range := fun g => by
    obtain ⟨k, hk⟩ := hτ (Ψ g)
    refine ⟨k, ?_⟩
    have := hinnΨ' _ hk
    rwa [map_mul, map_inv, map_pow, Ψ.symm_apply_apply] at this
  have hβH : β ∈ H := LieClAut.mem_of_cyclic_quotient hτ' hinn hαH hα hαn hβ3 hβn
  refine LieClAut.exists_rankFour_of_fixed hc hinn hβH hβ3 hβn
    (e.symm.toMonoidHom.comp (e27 hn b c)) (e.symm.injective.comp (e27_injective hn b c))
    (fun a => ?_) (by simp [Nat.card_eq_fintype_card]) fun a => ?_
  · apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply]
    have h3 : ∀ x : ZMod 3, 3 • x = 0 := by decide
    exact h3 _
  · simp only [hβ, hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, e.apply_symm_apply, fieldPair_e27 hn σ hb]

end Main

section Stated

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.ComponentClassification CFSG.Assembly.LowTwoRank

variable [Finite K] [CharP K 2]

theorem nonempty_equiv_matrixDerived {X : Type} [Group X] {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    Nonempty (X ≃* matrixDerived (Qm n hn b c)) := by
  obtain ⟨hnd, -⟩ := regular_coordinateQuadMinus n K b c hn hirr
  have hQ : ∃ v, Qm n hn b c v ≠ 0 := exists_ne_zero_of_polar_nondegenerate (by omega) _ hnd
  exact ⟨(coordinateMinusWitnessEquiv K (by omega) b c e).trans
    (derivedProjEquiv (Qm n hn b c) hQ).symm⟩

theorem three_dvd_of_outer {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (e : X ≃* matrixDerived (Qm n hn b c)) {α : MulAut X} (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) : 3 ∣ f := by
  obtain ⟨τ, hτ, hτ2, -⟩ := exists_frobenius_class n hn b c hirr hf
  set Ψ : MulAut X ≃* MulAut (matrixDerived (Qm n hn b c)) := MulAut.congr e with hΨ
  haveI := OuterAutomorphisms.inner_normal (matrixDerived (Qm n hn b c))
  have hα' : ∃ k : ℕ, Ψ α ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hαn' : Ψ α ∉ OuterAutomorphisms.inner (matrixDerived (Qm n hn b c)) := by
    rintro ⟨p, hp⟩
    apply hαn
    refine ⟨e.symm p, ?_⟩
    rw [← Ψ.symm_apply_apply α, ← hp, MulEquiv.eq_symm_apply]
    ext x
    simp [hΨ]
  have h := LieClAut.three_dvd_of_cyclic_quotient hτ hτ2 hα' hαn'
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h)

theorem exists_rankFour_omega_stated {X : Type} [Group X] [Finite X]
    (hc : Subgroup.center X = ⊥) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (e : X ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) {H : Subgroup (MulAut X)}
    (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X} (hαH : α ∈ H)
    (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  obtain ⟨e₀⟩ := nonempty_equiv_matrixDerived hn hirr e
  have h3 := three_dvd_of_outer hn hirr hf e₀ hα hαn
  obtain ⟨hcard, -⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
    Nat.prime_two K hf
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S.finite_ringAut K
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := K ≃+* K) 3 (by rwa [← hcard] at h3)
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := fun h => by rw [h, orderOf_one] at hσ; norm_num at hσ
  obtain ⟨b', c', hfix, hirr'⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S.exists_fixed_rootFree_quadratic
      (Subgroup.zpowers σ) (by rw [Nat.card_zpowers, hσ]; decide)
  obtain ⟨e'⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    hirr hirr'
  obtain ⟨e₁⟩ := nonempty_equiv_matrixDerived hn hirr' (e.trans e')
  obtain ⟨hb, hc'⟩ := hfix σ (Subgroup.mem_zpowers σ)
  exact exists_rankFour_omega hc hn hirr' hf σ hσ3 hσ1 hb hc' e₁ hinn hαH hα hαn

end Stated

section Family

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15

theorem exists_eq_twistedD_four {d : TauCeti.LieTypeIndex} (hl : RankThreeList d)
    (hB : ∀ q : TauCeti.PrimePower, d ≠ .B 3 q) (hA5 : ∀ q : TauCeti.PrimePower, d ≠ .A 5 q)
    (hA3 : ∀ q : TauCeti.PrimePower, d ≠ .A 3 q) (hA6 : ∀ q : TauCeti.PrimePower, d ≠ .A 6 q)
    (hU3 : ∀ q : TauCeti.PrimePower, d ≠ .twistedA 3 q)
    (hU5 : ∀ q : TauCeti.PrimePower, d ≠ .twistedA 5 q)
    (hU6 : ∀ q : TauCeti.PrimePower, d ≠ .twistedA 6 q) :
    ∃ q : TauCeti.PrimePower, d = .twistedD 4 q := by
  cases d with
  | twistedD l q =>
    rcases l with _ | _ | _ | _ | _ | l
    all_goals first | exact hl.elim | exact ⟨q, rfl⟩
  | A l q =>
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    all_goals try exact hl.elim
    all_goals try exact absurd rfl (hA3 q)
    all_goals try exact absurd rfl (hA5 q)
    all_goals exact absurd rfl (hA6 q)
  | twistedA l q =>
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    all_goals try exact hl.elim
    all_goals try exact absurd rfl (hU3 q)
    all_goals try exact absurd rfl (hU5 q)
    all_goals exact absurd rfl (hU6 q)
  | B l q =>
    rcases l with _ | _ | _ | _ | l
    all_goals first | exact hl.elim | exact absurd rfl (hB q)
  | _ => exact hl.elim

end Family

end OmegaE27

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15 in
theorem kFactOuterThreeRankFourRestSU_holds : KFactOuterThreeRankFourRestSU := by
  intro X _ _ d hd hl hB hA5 hA3 hA6 hU3 hU5 hU6 _ he hc H hinn hα
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  obtain ⟨q, hq⟩ := OmegaE27.exists_eq_twistedD_four hl hB hA5 hA3 hA6 hU3 hU5 hU6
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  have hp : q.p = 2 := hd.1
  obtain ⟨e⟩ := he
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      4 q hv
  haveI : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) =
      2 ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent, hp]
  haveI : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩) 2 := by
    haveI := Fintype.ofFinite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD 4 q, hv⟩)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  exact OmegaE27.exists_rankFour_omega_stated hc le_rfl hirr hcard (e.trans eD) hinn hαH hαk hαn

theorem kFactTenElevenOneLieAutRes_of_fieldTwo
    (h2 : KFactTenElevenOneLieAutFieldTwo) : KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_rankFourSU kFactOuterThreeRankFourRestSU_holds h2

end CFSG.LocalAnalysis.RankThreeTheoremC
