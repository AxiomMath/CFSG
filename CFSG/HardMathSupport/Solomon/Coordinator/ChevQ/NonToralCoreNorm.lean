module

public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE7

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Malle.SeitzCube

section Algebra

variable {G : Type*} [Group G]

theorem norm_orbit_fixed (Φ : G →* G) {g ν z u₁ : G} (k : ℕ) (hν : Φ g = g * ν)
    (hz3 : z ^ 3 = 1) (hfix : ν * Φ z * ν⁻¹ = z)
    (hF : ν * Φ u₁ * ν⁻¹ = z ^ k * u₁ * (z ^ k)⁻¹)
    (h12 : Commute u₁ (z * u₁ * z⁻¹)) :
    Commute z (u₁ * (z * u₁ * z⁻¹) * (z ^ 2 * u₁ * (z ^ 2)⁻¹)) ∧
      Φ (g * (u₁ * (z * u₁ * z⁻¹) * (z ^ 2 * u₁ * (z ^ 2)⁻¹)) * g⁻¹) =
        g * (u₁ * (z * u₁ * z⁻¹) * (z ^ 2 * u₁ * (z ^ 2)⁻¹)) * g⁻¹ ∧
      ∀ n : ℕ, u₁ ^ n = 1 → (u₁ * (z * u₁ * z⁻¹) * (z ^ 2 * u₁ * (z ^ 2)⁻¹)) ^ n = 1 := by
  obtain ⟨u₂, hu₂⟩ : ∃ u₂, z * u₁ * z⁻¹ = u₂ := ⟨_, rfl⟩
  obtain ⟨u₃, hu₃⟩ : ∃ u₃, z ^ 2 * u₁ * (z ^ 2)⁻¹ = u₃ := ⟨_, rfl⟩
  rw [hu₂] at h12
  rw [hu₂, hu₃]
  have e23 : z * u₂ * z⁻¹ = u₃ := by
    rw [← hu₂, ← hu₃, pow_two]
    group
  have e31 : z * u₃ * z⁻¹ = u₁ := by
    rw [← hu₃]
    have h : z * (z ^ 2 * u₁ * (z ^ 2)⁻¹) * z⁻¹ = z ^ 3 * u₁ * (z ^ 3)⁻¹ := by group
    rw [h, hz3]
    group
  have h23 : Commute u₂ u₃ := by
    have h := h12.map (MulAut.conj z)
    simp only [MulAut.conj_apply] at h
    rwa [hu₂, e23] at h
  have h31 : Commute u₃ u₁ := by
    have h := h23.map (MulAut.conj z)
    simp only [MulAut.conj_apply] at h
    rwa [e23, e31] at h
  have hN : z * (u₁ * u₂ * u₃) * z⁻¹ = u₁ * u₂ * u₃ := by
    have h : z * (u₁ * u₂ * u₃) * z⁻¹ = (z * u₁ * z⁻¹) * (z * u₂ * z⁻¹) * (z * u₃ * z⁻¹) := by
      group
    rw [h, hu₂, e23, e31]
    calc u₂ * u₃ * u₁ = u₂ * (u₃ * u₁) := mul_assoc _ _ _
      _ = u₂ * (u₁ * u₃) := by rw [h31.eq]
      _ = u₂ * u₁ * u₃ := (mul_assoc _ _ _).symm
      _ = u₁ * u₂ * u₃ := by rw [h12.eq]
  have hzN : Commute z (u₁ * u₂ * u₃) := mul_inv_eq_iff_eq_mul.1 hN
  refine ⟨hzN, ?_, ?_⟩
  swap
  · intro n hn
    have h13 : Commute u₁ u₃ := h31.symm
    rw [(h13.mul_left h23).mul_pow, h12.mul_pow, hn]
    have h2 : u₂ ^ n = 1 := by
      rw [← hu₂, conj_pow, hn]
      group
    have h3 : u₃ ^ n = 1 := by
      rw [← hu₃, conj_pow, hn]
      group
    rw [h2, h3]
    group
  set F : G →* G := (MulAut.conj ν).toMonoidHom.comp Φ with hFdef
  have hFapply : ∀ x, F x = ν * Φ x * ν⁻¹ := fun x => rfl
  have hFz : F z = z := hfix
  have hFu₁ : F u₁ = z ^ k * u₁ * (z ^ k)⁻¹ := hF
  have hFu₂ : F u₂ = z ^ k * u₂ * (z ^ k)⁻¹ := by
    rw [← hu₂, map_mul, map_mul, map_inv, hFz, hFu₁]
    group
  have hFu₃ : F u₃ = z ^ k * u₃ * (z ^ k)⁻¹ := by
    rw [← hu₃, map_mul, map_mul, map_inv, map_pow, hFz, hFu₁]
    group
  have hFN : F (u₁ * u₂ * u₃) = u₁ * u₂ * u₃ := by
    rw [map_mul, map_mul, hFu₁, hFu₂, hFu₃]
    have h : z ^ k * u₁ * (z ^ k)⁻¹ * (z ^ k * u₂ * (z ^ k)⁻¹) * (z ^ k * u₃ * (z ^ k)⁻¹) =
        z ^ k * (u₁ * u₂ * u₃) * (z ^ k)⁻¹ := by group
    rw [h]
    exact mul_inv_eq_iff_eq_mul.2 (hzN.pow_left k).eq
  have hN' : ν * Φ (u₁ * u₂ * u₃) * ν⁻¹ = u₁ * u₂ * u₃ := hFN
  rw [map_mul, map_mul, map_inv, hν]
  calc g * ν * Φ (u₁ * u₂ * u₃) * (g * ν)⁻¹ = g * (ν * Φ (u₁ * u₂ * u₃) * ν⁻¹) * g⁻¹ := by
        group
    _ = g * (u₁ * u₂ * u₃) * g⁻¹ := by rw [hN']

end Algebra

section Descent


theorem frob_baseChangeGL {τ : Tag} {K : Type} [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) w) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) w := by
  have : Fintype K := Fintype.ofFinite K
  have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) :=
    RingHom.ext fun c => by
      change Fr (algebraMap K (AlgebraicClosure K) c) = algebraMap K (AlgebraicClosure K) c
      rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have e : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) w) =
      baseChangeGL Fr (baseChangeGL (algebraMap K (AlgebraicClosure K)) w) := Units.ext rfl
  rw [e, baseChangeGL_baseChangeGL, hcomp]

theorem exists_rational_of_frame_orbit {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    {K : Type} [Field K] [Finite K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g : ModGL τ (AlgebraicClosure K))
    (hg : g ∈ adjointGroup τ (AlgebraicClosure K)) (z : adjointGroup τ K) (hz3 : z ^ 3 = 1)
    (z' ν : ModGL τ (AlgebraicClosure K))
    (hz' : g * z' * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K))
    (hν : Units.map (entrywiseHom Fr) g = g * ν) (u₁ : ModGL τ (AlgebraicClosure K)) (k : ℕ)
    (hu₁ : u₁ ∈ adjointGroup τ (AlgebraicClosure K)) (hu₁r : u₁ ^ ringChar K = 1)
    (hF : ν * Units.map (entrywiseHom Fr) u₁ * ν⁻¹ = z' ^ k * u₁ * (z' ^ k)⁻¹)
    (h12 : Commute u₁ (z' * u₁ * z'⁻¹))
    (hnt : u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹) ≠ 1) :
    ∃ u : adjointGroup τ K, u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL τ K) =
        g * (u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹)) * g⁻¹ ∧ Commute u z := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set N := u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹) with hNdef
  have hιinj := baseChangeGL_injective (τ := τ) ι
  have hz'eq : z' = g⁻¹ * baseChangeGL ι (z : ModGL τ K) * g := by
    rw [← hz']
    group
  have hzL : baseChangeGL ι (z : ModGL τ K) ∈ adjointGroup τ L :=
    baseChangeGL_mem_adjointGroup ι z.2
  have hz'G : z' ∈ adjointGroup τ L := by
    rw [hz'eq]
    exact mul_mem (mul_mem (inv_mem hg) hzL) hg
  have hz'3 : z' ^ 3 = 1 := by
    have h : g * z' ^ 3 * g⁻¹ = 1 := by
      rw [← conj_pow, hz', ← map_pow]
      have : (z : ModGL τ K) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
      rw [this, map_one]
    calc z' ^ 3 = g⁻¹ * (g * z' ^ 3 * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hfix : ν * Φ z' * ν⁻¹ = z' := by
    have hΦz : Φ (baseChangeGL ι (z : ModGL τ K)) = baseChangeGL ι (z : ModGL τ K) :=
      frob_baseChangeGL Fr hFr _
    have hνdef : ν = g⁻¹ * Φ g := by rw [hν]; group
    rw [hz'eq, map_mul, map_mul, map_inv, hΦz, hν]
    group
  obtain ⟨hcomm, hFixN, hpow⟩ := norm_orbit_fixed Φ (g := g) (ν := ν) (z := z') (u₁ := u₁) k hν hz'3
    hfix hF h12
  have hu₂G : z' * u₁ * z'⁻¹ ∈ adjointGroup τ L := mul_mem (mul_mem hz'G hu₁) (inv_mem hz'G)
  have hu₃G : z' ^ 2 * u₁ * (z' ^ 2)⁻¹ ∈ adjointGroup τ L :=
    mul_mem (mul_mem (pow_mem hz'G 2) hu₁) (inv_mem (pow_mem hz'G 2))
  have hNG : N ∈ adjointGroup τ L := mul_mem (mul_mem hu₁ hu₂G) hu₃G
  have hx₀G : g * N * g⁻¹ ∈ adjointGroup τ L := mul_mem (mul_mem hg hNG) (inv_mem hg)
  have hx₀1 : g * N * g⁻¹ ≠ 1 := by
    intro h
    apply hnt
    calc N = g⁻¹ * (g * N * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hx₀p : (g * N * g⁻¹) ^ ringChar K = 1 := by
    rw [conj_pow, hpow _ hu₁r]
    group
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨u', hu'mem, hu'eq⟩ : ∃ u' ∈ adjointGroup τ K, baseChangeGL ι u' = g * N * g⁻¹ := by
    rcases hτ with rfl | rfl
    · have hodd : Odd (Nat.card K) → Odd (orderOf (g * N * g⁻¹)) := by
        intro hK
        rw [orderOf_eq_prime hx₀p hx₀1]
        obtain ⟨e, he, hcard⟩ : ∃ e : ℕ, 1 ≤ e ∧ Nat.card K = ringChar K ^ e := by
          letI : Fintype K := Fintype.ofFinite K
          obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
          exact ⟨(n : ℕ), n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
        rw [hcard] at hK
        exact Odd.of_dvd_nat hK (dvd_pow_self _ (by omega))
      exact Subgroup.mem_map.1
        (mem_map_baseChange_of_frobenius_fixed_E7 Fr hFr hx₀G hFixN hodd)
    · exact Subgroup.mem_map.1 (mem_map_baseChange_of_frobenius_fixed_E8 Fr hFr hx₀G hFixN)
  refine ⟨⟨u', hu'mem⟩, ?_, ⟨1, ?_⟩, hu'eq, ?_⟩
  · intro h
    apply hx₀1
    rw [← hu'eq]
    have : u' = 1 := congrArg Subtype.val h
    rw [this, map_one]
  · apply Subtype.ext
    apply hιinj
    rw [pow_one, Subgroup.coe_pow, map_pow, hu'eq, hx₀p, Subgroup.coe_one, map_one]
  · apply Subtype.ext
    show u' * (z : ModGL τ K) = (z : ModGL τ K) * u'
    apply hιinj
    rw [map_mul, map_mul, hu'eq, ← hz']
    have hcomm' : z' * N = N * z' := hcomm.eq
    calc g * N * g⁻¹ * (g * z' * g⁻¹) = g * (N * z') * g⁻¹ := by group
      _ = g * (z' * N) * g⁻¹ := by rw [hcomm']
      _ = g * z' * g⁻¹ * (g * N * g⁻¹) := by group

theorem exists_rational_centralizing_of_frame_orbit {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    {K : Type} [Field K] [Finite K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g : ModGL τ (AlgebraicClosure K))
    (hg : g ∈ adjointGroup τ (AlgebraicClosure K)) (E₀ P : Subgroup (adjointGroup τ K))
    (z : adjointGroup τ K) (hz3 : z ^ 3 = 1) (hEgen : E₀ ≤ P ⊔ Subgroup.zpowers z)
    (hPz : ∀ p ∈ P, Commute z p) (z' ν : ModGL τ (AlgebraicClosure K))
    (hz' : g * z' * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL τ K))
    (hν : Units.map (entrywiseHom Fr) g = g * ν) (u₁ : ModGL τ (AlgebraicClosure K)) (k : ℕ)
    (hu₁ : u₁ ∈ adjointGroup τ (AlgebraicClosure K)) (hu₁r : u₁ ^ ringChar K = 1)
    (hF : ν * Units.map (entrywiseHom Fr) u₁ * ν⁻¹ = z' ^ k * u₁ * (z' ^ k)⁻¹)
    (h12 : Commute u₁ (z' * u₁ * z'⁻¹))
    (hnt : u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹) ≠ 1)
    (hP : ∀ p ∈ P, Commute u₁
      (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (p : ModGL τ K) * g)) :
    ∃ u : adjointGroup τ K, u ≠ 1 ∧ (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧
      ∀ x ∈ E₀, Commute u x := by
  classical
  obtain ⟨u, hu1, hur, hue, hcz⟩ := exists_rational_of_frame_orbit hτ Fr hFr g hg z hz3 z' ν hz'
    hν u₁ k hu₁ hu₁r hF h12 hnt
  refine ⟨u, hu1, hur, ?_⟩
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  have hιinj := baseChangeGL_injective (τ := τ) ι
  have hz'eq : z' = g⁻¹ * baseChangeGL ι (z : ModGL τ K) * g := by
    rw [← hz']
    group
  have hcP : ∀ p ∈ P, Commute u p := by
    intro p hp
    set d := g⁻¹ * baseChangeGL ι (p : ModGL τ K) * g with hd
    have hpz : (z : ModGL τ K) * (p : ModGL τ K) = (p : ModGL τ K) * (z : ModGL τ K) :=
      congrArg Subtype.val (hPz p hp).eq
    have hιpz : baseChangeGL ι (p : ModGL τ K) * baseChangeGL ι (z : ModGL τ K) =
        baseChangeGL ι (z : ModGL τ K) * baseChangeGL ι (p : ModGL τ K) := by
      rw [← map_mul, ← map_mul, hpz]
    have hdz : Commute d z' := by
      show d * z' = z' * d
      rw [hd, hz'eq]
      generalize baseChangeGL ι (p : ModGL τ K) = pι at hιpz ⊢
      generalize baseChangeGL ι (z : ModGL τ K) = zι at hιpz ⊢
      calc g⁻¹ * pι * g * (g⁻¹ * zι * g) = g⁻¹ * (pι * zι) * g := by group
        _ = g⁻¹ * (zι * pι) * g := by rw [hιpz]
        _ = g⁻¹ * zι * g * (g⁻¹ * pι * g) := by group
    have hdu₁ : Commute d u₁ := (hP p hp).symm
    have hd2 : Commute d (z' * u₁ * z'⁻¹) := (hdz.mul_right hdu₁).mul_right hdz.inv_right
    have hz2 : Commute d (z' ^ 2) := hdz.pow_right 2
    have hd3 : Commute d (z' ^ 2 * u₁ * (z' ^ 2)⁻¹) :=
      (hz2.mul_right hdu₁).mul_right hz2.inv_right
    have hdN : Commute d (u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹)) :=
      (hdu₁.mul_right hd2).mul_right hd3
    apply Subtype.ext
    show (u : ModGL τ K) * (p : ModGL τ K) = (p : ModGL τ K) * (u : ModGL τ K)
    apply hιinj
    rw [map_mul, map_mul, hue]
    have hpd : baseChangeGL ι (p : ModGL τ K) = g * d * g⁻¹ := by
      rw [hd]
      group
    rw [hpd]
    calc g * (u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹)) * g⁻¹ * (g * d * g⁻¹)
        = g * ((u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹)) * d) * g⁻¹ := by group
      _ = g * (d * (u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹))) * g⁻¹ := by
          rw [hdN.eq]
      _ = g * d * g⁻¹ * (g * (u₁ * (z' * u₁ * z'⁻¹) * (z' ^ 2 * u₁ * (z' ^ 2)⁻¹)) * g⁻¹) := by
          group
  have hle : P ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer {u} := by
    refine sup_le (fun p hp => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hcP p hp).symm.eq
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hcz.symm.eq
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (hEgen hx))).symm

end Descent

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

end
