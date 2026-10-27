module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveUniAlg
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvLA
public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspCover
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix CFSG.Open

section Algebra

variable {K : Type} [Field K] (fb : K →+* K)

theorem psu4_hh_eigen_zero {U : Matrix (Fin 4) (Fin 4) K} (hU : (U.map fb)ᵀ * U = 1) {ε ε' : K}
    {x y : Fin 4 → K} (hx : U *ᵥ x = ε • x) (hy : U *ᵥ y = ε' • y) (h : fb ε * ε' ≠ 1) :
    suHh fb x y = 0 := by
  have h1 := su_hh_unitary fb hU x y
  rw [hx, hy, su_hh_smul_left, su_hh_smul_right] at h1
  have : (fb ε * ε' - 1) * suHh fb x y = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h)

theorem psu4_suX_mulVec (a b : Fin 4 → K) (α : K) (x : Fin 4 → K) :
    suX fb a b α *ᵥ x = (α * suHh fb b x) • a - (fb α * suHh fb a x) • b := by
  simp only [suX, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]
  rfl

theorem psu4_suX_eq_zero {a b : Fin 4 → K} (hli : LinearIndependent K ![a, b]) {α : K}
    (h : suX fb a b α = 0) : α = 0 := by
  rw [LinearIndependent.pair_iff] at hli
  have hb : b ≠ 0 := by
    intro h0
    have := hli 0 1 (by simp [h0])
    exact one_ne_zero this.2
  obtain ⟨x, hx⟩ : ∃ x, suHh fb b x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (su_hh_eq_zero_of_forall fb hcon)
  have h1 := congrArg (fun N : Matrix (Fin 4) (Fin 4) K => N *ᵥ x) h
  simp only [psu4_suX_mulVec, Matrix.zero_mulVec] at h1
  have h2 := hli (α * suHh fb b x) (-(fb α * suHh fb a x)) (by
    rw [neg_smul, ← sub_eq_add_neg]
    exact h1)
  exact (mul_eq_zero.mp h2.1).resolve_right hx

theorem psu4_suX_conj_neg {M : Matrix (Fin 4) (Fin 4) K} (hU : (M.map fb)ᵀ * M = 1) {c ε₁ ε₂ : K}
    (hMM : M * M = c • 1) {w₁ w₂ : Fin 4 → K} (h1 : M *ᵥ w₁ = ε₁ • w₁) (h2 : M *ᵥ w₂ = ε₂ • w₂)
    (hε₁ : ε₁ = -(fb ε₂ * c)) (hε₂ : ε₂ = -(fb ε₁ * c)) (α : K) :
    M * suX fb w₁ w₂ α = -(suX fb w₁ w₂ α * M) := by
  have e1 := su_cj_vecMul_eigen fb hU hMM h1
  have e2 := su_cj_vecMul_eigen fb hU hMM h2
  simp only [suX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, h1, h2, e1, e2, smul_vecMulVec, vecMulVec_smul]
  have k1 : ε₁ • vecMulVec w₁ (suCj fb w₂) = -((fb ε₂ * c) • vecMulVec w₁ (suCj fb w₂)) := by
    rw [hε₁, neg_smul]
  have k2 : ε₂ • vecMulVec w₂ (suCj fb w₁) = -((fb ε₁ * c) • vecMulVec w₂ (suCj fb w₁)) := by
    rw [hε₂, neg_smul]
  rw [k1, k2]
  simp only [smul_neg]
  abel

theorem psu4_li_of_eigen {M : Matrix (Fin 4) (Fin 4) K} {ε₁ ε₂ : K} (hne : ε₂ - ε₁ ≠ 0)
    {a b : Fin 4 → K} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : M *ᵥ a = ε₁ • a)
    (hb : M *ᵥ b = ε₂ • b) : LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun v => M *ᵥ v) hst
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ha, hb, Matrix.mulVec_zero] at h1
  have h3 : ((ε₂ - ε₁) * s) • a = 0 := by
    have e : ((ε₂ - ε₁) * s) • a =
        ε₂ • (s • a + t • b) - (s • ε₁ • a + t • ε₂ • b) := by module
    rw [e, hst, h1]
    simp
  have hs : s = 0 := by
    have := (smul_eq_zero.mp h3).resolve_right ha0
    exact (mul_eq_zero.mp this).resolve_left hne
  rw [hs, zero_smul, zero_add] at hst
  exact ⟨hs, (smul_eq_zero.mp hst).resolve_right hb0⟩

end Algebra

section Siegel

variable {K : Type} [Field K] [Finite K] [CharP K 5] (fb : K →+* K)

omit [CharP K 5] in
theorem psu4_not_fixed (hK : Nat.card K = 25) : ∃ s : K, s ^ 5 ≠ s := by
  by_contra h
  push Not at h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 24 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have h5 : g ^ 5 = g := Units.ext (h g)
  have h4 : g ^ 4 = 1 := by
    have : g * g ^ 4 = g * 1 := by rw [← pow_succ', h5, mul_one]
    exact mul_left_cancel this
  have := orderOf_dvd_of_pow_eq_one h4
  rw [hord] at this
  omega

theorem psu4_inverted_c55 (hK : Nat.card K = 25) (hfb : ∀ x, fb (fb x) = x)
    (hfb5 : ∀ x : K, fb x = x ^ 5) (M : GL (Fin 4) K) (hMH : M ∈ StatedSU 4 5 K) {c ε₁ ε₂ : K}
    (hMM : (M : Matrix (Fin 4) (Fin 4) K) * (M : Matrix (Fin 4) (Fin 4) K) = c • 1)
    {w₁ w₂ : Fin 4 → K} (hli : LinearIndependent K ![w₁, w₂])
    (h1 : (M : Matrix (Fin 4) (Fin 4) K) *ᵥ w₁ = ε₁ • w₁)
    (h2 : (M : Matrix (Fin 4) (Fin 4) K) *ᵥ w₂ = ε₂ • w₂)
    (hε₁ : ε₁ = -(fb ε₂ * c)) (hε₂ : ε₂ = -(fb ε₁ * c))
    (i11 : suHh fb w₁ w₁ = 0) (i12 : suHh fb w₁ w₂ = 0) (i21 : suHh fb w₂ w₁ = 0)
    (i22 : suHh fb w₂ w₂ = 0) :
    ∃ Φ : C55 →* StatedProj (StatedSU 4 5 K), Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU 4 5 K) : StatedProj (StatedSU 4 5 K)) *
        Φ u * (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU 4 5 K) : StatedProj (StatedSU 4 5 K))⁻¹ =
        (Φ u)⁻¹ := by
  obtain ⟨lam, hlam⟩ := psu4_not_fixed (K := K) hK
  have hU := (su_unitary_of_mem_statedSU fb hfb5 hMH).1
  have hAA : suX fb w₁ w₂ 1 * suX fb w₁ w₂ 1 = 0 := suX_mul fb w₁ w₂ i11 i12 i21 i22 1 1
  have hAB : suX fb w₁ w₂ 1 * suX fb w₁ w₂ lam = 0 := suX_mul fb w₁ w₂ i11 i12 i21 i22 1 lam
  have hBA : suX fb w₁ w₂ lam * suX fb w₁ w₂ 1 = 0 := suX_mul fb w₁ w₂ i11 i12 i21 i22 lam 1
  have hBB : suX fb w₁ w₂ lam * suX fb w₁ w₂ lam = 0 :=
    suX_mul fb w₁ w₂ i11 i12 i21 i22 lam lam
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfz : ∀ a : ZMod 5, fb (zi K a) = zi K a := fun a => by
    rw [hfb5, ← map_pow, ZMod.pow_card]
  have hcomb : ∀ a b : ZMod 5, zi K a • suX fb w₁ w₂ 1 + zi K b • suX fb w₁ w₂ lam =
      suX fb w₁ w₂ (zi K a * 1 + zi K b * lam) := fun a b => by
    rw [suX_add, suX_mul_fixed fb w₁ w₂ (hfz a), suX_mul_fixed fb w₁ w₂ (hfz b)]
  have hH : ∀ a b : ZMod 5, Tu hAA hAB hBA hBB (zi K a) (zi K b) ∈ StatedSU 4 5 K := fun a b => by
    apply Subgroup.subset_closure
    refine ⟨det_Ehom_eq_one hAA hAB hBA hBB (Multiplicative.ofAdd (a, b)), ?_⟩
    have e : ((Tu hAA hAB hBA hBB (zi K a) (zi K b) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1 + suX fb w₁ w₂ (zi K a * 1 + zi K b * lam) := by
      rw [← hcomb a b, ← add_assoc]
      rfl
    rw [e]
    have e2 : (fun x : K => x ^ 5) = ⇑fb := funext fun x => (hfb5 x).symm
    rw [e2]
    exact suX_unitary fb hfb w₁ w₂ i11 i12 i21 i22 _
  have hind : ∀ a b : ZMod 5, zi K a • suX fb w₁ w₂ 1 + zi K b • suX fb w₁ w₂ lam = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    rw [hcomb] at hab
    have h0 := psu4_suX_eq_zero fb hli hab
    have hb : b = 0 := by
      by_contra hb
      apply hlam
      have hbz : zi K b ≠ 0 := fun h => hb ((zi K).injective (by rw [h, map_zero]))
      have hl : lam = -(zi K a) / zi K b := by
        field_simp
        linear_combination h0
      have : fb lam = lam := by
        conv_lhs => rw [hl]
        rw [map_div₀, map_neg, hfz, hfz, ← hl]
      rw [← hfb5]
      exact this
    subst hb
    refine ⟨?_, rfl⟩
    rw [map_zero, zero_mul, add_zero, mul_one] at h0
    exact (zi K).injective (by rw [h0, map_zero])
  exact inverted_c55_proj (StatedSU 4 5 K) M hMH hAA hAB hBA hBB
    (psu4_suX_conj_neg fb hU hMM h1 h2 hε₁ hε₂ 1)
    (psu4_suX_conj_neg fb hU hMM h1 h2 hε₁ hε₂ lam) hH hind

end Siegel

section Num

variable {K : Type} [Field K] [CharP K 5]

theorem psu4_five_zero : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5

theorem psu4_two_ne_zero : (2 : K) ≠ 0 := by
  intro h2
  have : (1 : K) = 0 := by linear_combination 3 * h2 - psu4_five_zero (K := K)
  exact one_ne_zero this

theorem psu4_three_ne_zero : (3 : K) ≠ 0 := by
  intro h3
  have : (1 : K) = 0 := by linear_combination 2 * h3 - psu4_five_zero (K := K)
  exact one_ne_zero this

end Num

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 5] (fb : K →+* K)

theorem psu4_neg (hK : Nat.card K = 25) (hfb : ∀ x, fb (fb x) = x) (hfb5 : ∀ x : K, fb x = x ^ 5)
    (h : ↥(StatedSU 4 5 K))
    (hM : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (-1 : K) • 1)
    (hnon : ∀ a : K, ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ a • 1) :
    ∃ Φ : C55 →* StatedProj (StatedSU 4 5 K), Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk h : StatedProj (StatedSU 4 5 K)) * Φ u *
        (QuotientGroup.mk h : StatedProj (StatedSU 4 5 K))⁻¹ = (Φ u)⁻¹ := by
  have h5 : (5 : K) = 0 := psu4_five_zero
  have h2 : (2 : K) ≠ 0 := psu4_two_ne_zero
  have h3 : (3 : K) ≠ 0 := psu4_three_ne_zero
  obtain ⟨hU, hdet⟩ := su_unitary_of_mem_statedSU fb hfb5 h.2
  have hMM : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((-2 : K) * (-2)) • 1 := by
    rw [hM]
    congr 1
    linear_combination (-1 : K) * h5
  obtain ⟨x, y, hli, hx, hy⟩ := su_exists_two_indep_eigen (μ := -2) hdet (neg_ne_zero.mpr h2)
    (by linear_combination 3 * h5) h2 hMM (hnon (-2))
  rw [neg_neg] at hx hy
  have iso : ∀ u v : Fin 4 → K, ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ u = (2 : K) • u →
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v = (2 : K) • v → suHh fb u v = 0 :=
    fun u v hu hv => psu4_hh_eigen_zero fb hU hu hv (by
      rw [map_ofNat]
      intro h4
      apply h3
      linear_combination h4)
  exact psu4_inverted_c55 fb hK hfb hfb5 (h : GL (Fin 4) K) h.2 hM hli hx hy
    (by rw [map_ofNat]; ring) (by rw [map_ofNat]; ring)
    (iso x x hx hx) (iso x y hx hy) (iso y x hy hx) (iso y y hy hy)

theorem psu4_pos (hK : Nat.card K = 25) (hfb : ∀ x, fb (fb x) = x) (hfb5 : ∀ x : K, fb x = x ^ 5)
    (h : ↥(StatedSU 4 5 K))
    (hM : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (1 : K) • 1)
    (hnon : ∀ a : K, ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ≠ a • 1) :
    ∃ Φ : C55 →* StatedProj (StatedSU 4 5 K), Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk h : StatedProj (StatedSU 4 5 K)) * Φ u *
        (QuotientGroup.mk h : StatedProj (StatedSU 4 5 K))⁻¹ = (Φ u)⁻¹ := by
  have h2 : (2 : K) ≠ 0 := psu4_two_ne_zero
  obtain ⟨hU, hdet⟩ := su_unitary_of_mem_statedSU fb hfb5 h.2
  have hMM1 : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((1 : K) * 1) • 1 := by
    rw [hM, one_mul]
  have hMM2 : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = ((-1 : K) * (-1)) • 1 := by
    rw [hM, neg_mul_neg, one_mul]
  obtain ⟨x, y, hli, hx, hy⟩ := su_exists_two_indep_eigen (μ := 1) hdet one_ne_zero
    (one_pow 4) h2 hMM1 (hnon 1)
  obtain ⟨x', y', hli', hx', hy'⟩ := su_exists_two_indep_eigen (μ := -1) hdet
    (neg_ne_zero.mpr one_ne_zero) (by norm_num) h2 hMM2 (hnon (-1))
  rw [neg_neg] at hx' hy'
  obtain ⟨s₁, s₂, hb0, hbb⟩ := su_exists_isotropic_plane fb hK hfb hfb5 hli
  obtain ⟨t₁, t₂, ha0, haa⟩ := su_exists_isotropic_plane fb hK hfb hfb5 hli'
  have hb : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (s₁ • x + s₂ • y) =
      (-1 : K) • (s₁ • x + s₂ • y) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hy]
    module
  have ha : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (t₁ • x' + t₂ • y') =
      (1 : K) • (t₁ • x' + t₂ • y') := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx', hy']
    module
  have hm1 : fb (1 : K) * (-1) ≠ 1 := by
    rw [map_one]
    intro h1
    apply h2
    linear_combination -h1
  have hm2 : fb (-1 : K) * 1 ≠ 1 := by
    rw [map_neg, map_one]
    intro h1
    apply h2
    linear_combination -h1
  have hab := psu4_hh_eigen_zero fb hU ha hb hm1
  have hba := psu4_hh_eigen_zero fb hU hb ha hm2
  have hli2 : LinearIndependent K ![t₁ • x' + t₂ • y', s₁ • x + s₂ • y] :=
    psu4_li_of_eigen (ε₁ := 1) (ε₂ := -1) (by
      intro h1
      apply h2
      linear_combination -h1) ha0 hb0 ha hb
  exact psu4_inverted_c55 fb hK hfb hfb5 (h : GL (Fin 4) K) h.2 hM hli2 ha hb
    (by rw [map_neg, map_one]; ring) (by rw [map_one]; ring) haa hab hba hbb

end Main

theorem psu4_five_inverts {K : Type} [Field K] [Finite K] (hK : Nat.card K = 25)
    (z : StatedProj (StatedSU 4 5 K)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ Φ : C55 →* StatedProj (StatedSU 4 5 K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 25 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : CharP K 5 := charP_of_card_eq_prime_pow (p := 5) (f := 2) (by rw [hcard]; norm_num)
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  let fb : K →+* K := frobenius K 5
  have hfb5 : ∀ x : K, fb x = x ^ 5 := fun x => rfl
  have hfb : ∀ x : K, fb (fb x) = x := fun x => by
    have := FiniteField.pow_card x
    rw [hcard] at this
    rw [hfb5, hfb5, ← pow_mul]
    exact this
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc0, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  obtain ⟨hU, hdet⟩ := su_unitary_of_mem_statedSU fb hfb5 h.2
  have hc4 : c ^ 4 = 1 := by
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, hdet, Matrix.det_smul, Matrix.det_one] at this
    simpa using this.symm
  have hc6 : c ^ 6 = 1 := by
    set e0 : Fin 4 → K := Pi.single 0 1 with he0
    have h2e : ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ e0) = c • e0 := by
      rw [Matrix.mulVec_mulVec, hM, Matrix.smul_mulVec, Matrix.one_mulVec]
    have k1 := su_hh_unitary fb hU (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ e0)
      (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ e0)
    have k2 := su_hh_unitary fb hU e0 e0
    rw [h2e, k2, su_hh_smul_left, su_hh_smul_right] at k1
    have k3 : suHh fb e0 e0 = 1 := by
      simp [suHh, suCj, he0, dotProduct, Pi.single_apply]
    rw [k3, hfb5] at k1
    linear_combination k1
  have hcc : c * c = 1 := by linear_combination hc6 - c ^ 2 * hc4
  rcases mul_self_eq_one_iff.mp hcc with hc1 | hc1
  · rw [hc1] at hM
    exact psu4_pos fb hK hfb hfb5 h hM hnon
  · rw [hc1] at hM
    exact psu4_neg fb hK hfb hfb5 h hM hnon

theorem five_not_dvd_center_psu4 (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 5 1) :
    ¬ 5 ∣ Nat.card (Subgroup.center L) := by
  intro h5
  have hmod' : CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 5 1 :=
    hmod
  have hd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq hmod'
  rcases CFSG.RankThree.PartOne.prime_dvd_table Nat.prime_five (by norm_num) (h5.trans hd) with
    ⟨ht, -, -⟩ | ⟨-, h, -⟩
  · exact absurd ht (by decide)
  · norm_num at h

theorem coverInv_psu4 (hGA : CFSG.Open.GriessAllModelsStatement) (Q : Type) [Group Q]
    (hQ : StatedClassicalModel Q .PSU 4 5 1) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e⟩⟩ := hQ
  have hK25 : Nat.card K = 25 := by simpa using hKc
  refine coverInv_of_data (fun w hw1 hw2 => ?_) (fun L _ _ hq hodd ⟨e'⟩ => ?_)
  · have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
    have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
    obtain ⟨Φ, hΦ, hinv⟩ := psu4_five_inverts hK25 (e w) hew1 hew2
    refine Or.inl ⟨e.symm.toMonoidHom.comp Φ, e.symm.injective.comp hΦ, fun u => ?_⟩
    have := congrArg e.symm (hinv u)
    simpa using this
  · have hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 5 1 :=
      ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e⟩⟩
    exact five_not_dvd_center_psu4 hGA (isQuasisimple_of_open hq) hmod

end CFSG.CGT.PushingUpLit.CGT6M
