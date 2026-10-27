module

public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulSL4

public section

namespace CFSG.OddStandard.L34Faithful

open Module

section Main

variable {K : Type*} [Field K] [Fintype K]

theorem eq_one_of_commute_order_seven_gf16 (hK : Fintype.card K = 16)
    (X Y : Module.End K (Fin 3 → K)) (hXY : X * Y = Y * X) (hX : X ^ 7 = 1) (hY : Y ^ 2 = 1)
    (hX1 : X ≠ 1) : Y = 1 := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 4) (by rw [hK]; norm_num)
  have hX7 : X ^ 7 ^ 1 = 1 := by simpa using hX
  have hdim : finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hpow : ∀ U : Submodule K (Fin 3 → K), Nat.card U = 16 ^ finrank K U := by
    intro U
    have := Module.card_eq_pow_finrank (K := K) (V := U)
    rw [hK] at this
    rwa [Nat.card_eq_fintype_card]
  have hle3 : ∀ U : Submodule K (Fin 3 → K), finrank K U ≤ 3 := fun U => by
    have := Submodule.finrank_le U
    omega
  have hinv : ∀ {A B : Module.End K (Fin 3 → K)}, A * B = B * A →
      ∀ v ∈ LinearMap.ker (B - 1), A v ∈ LinearMap.ker (B - 1) := by
    intro A B hAB v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h1 : (B - 1) (A v) = A ((B - 1) v) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
      have := congrArg (fun T => T v) hAB.symm
      simp only [Module.End.mul_apply] at this
      rw [this]
    rw [h1, hv, map_zero]
  have key7 : ∀ a : ℕ, a ≤ 3 → 16 ^ a % 7 = 1 → a = 0 ∨ a = 3 := by
    intro a ha h
    interval_cases a <;> simp_all
  have c1 := AltStdFaithful.card_modEq_card_ker_inf (p := 7) (n := 1) hX7
    (⊤ : Submodule K (Fin 3 → K)) (fun _ _ => trivial)
  rw [top_inf_eq, hpow, hpow, finrank_top, hdim] at c1
  have ha : finrank K (LinearMap.ker (X - 1)) = 0 := by
    have h1 : 16 ^ finrank K (LinearMap.ker (X - 1)) % 7 = 1 := by
      have := c1
      unfold Nat.ModEq at this
      rw [← this]
      norm_num
    rcases key7 _ (hle3 _) h1 with h | h
    · exact h
    · exfalso
      apply hX1
      have htop : LinearMap.ker (X - 1) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h, hdim])
      rw [LinearMap.ker_eq_top] at htop
      exact sub_eq_zero.1 htop
  have hbot : LinearMap.ker (X - 1) = ⊥ := Submodule.finrank_eq_zero.1 ha
  have c2 := AltStdFaithful.card_modEq_card_ker_inf (p := 7) (n := 1) hX7
    (LinearMap.ker (Y - 1)) (hinv hXY)
  rw [hbot, inf_bot_eq, hpow, hpow, finrank_bot] at c2
  have hd : finrank K (LinearMap.ker (Y - 1)) = 0 ∨ finrank K (LinearMap.ker (Y - 1)) = 3 := by
    have h1 : 16 ^ finrank K (LinearMap.ker (Y - 1)) % 7 = 1 := by
      have := c2
      unfold Nat.ModEq at this
      rw [this]
      norm_num
    exact key7 _ (hle3 _) h1
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdd : ∀ u : Fin 3 → K, u + u = 0 := fun u => by
    rw [← two_smul K u, h2K, zero_smul]
  have hNN : (Y - 1) ∘ₗ (Y - 1) = 0 := by
    apply LinearMap.ext
    intro v
    have hYY : Y (Y v) = v := by
      have := congrArg (fun T => T v) hY
      simpa [sq] using this
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub, hYY,
      LinearMap.zero_apply]
    have := hdd v
    have h' := hdd (Y v)
    calc v - Y v - (Y v - v) = (v + v) - (Y v + Y v) := by abel
      _ = 0 := by rw [this, h', sub_zero]
  have hrange : LinearMap.range (Y - 1) ≤ LinearMap.ker (Y - 1) :=
    LinearMap.range_le_ker_iff.2 hNN
  have hrk := LinearMap.finrank_range_add_finrank_ker (Y - 1)
  have hmono := Submodule.finrank_mono hrange
  rw [hdim] at hrk
  have hd3 : finrank K (LinearMap.ker (Y - 1)) = 3 := by
    rcases hd with h | h
    · omega
    · exact h
  have htop : LinearMap.ker (Y - 1) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hd3, hdim])
  rw [LinearMap.ker_eq_top] at htop
  exact sub_eq_zero.1 htop

end Main

section Lift

open scoped commutatorElement

variable {H : Type*} [Group H]

theorem exists_commuting_lifts (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1) {x t : H ⧸ Z} (hxt : x * t = t * x) (hx : x ^ 7 = 1)
    (ht : t ^ 2 = 1) :
    ∃ a b : H, a ^ 7 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a ∧ (a : H ⧸ Z) = x ^ 3 ∧
      (b : H ⧸ Z) = t := by
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective t
  have hx7 : x' ^ 7 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  have ht2 : t' ^ 2 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact ht
  have ha7 : (x' ^ 3) ^ 7 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hZ3 _ hx7
  have hb2 : (t' ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hZ3 _ ht2
  have hcomm : (QuotientGroup.mk' Z (t' ^ 3)) * (QuotientGroup.mk' Z (x' ^ 3)) =
      (QuotientGroup.mk' Z (x' ^ 3)) * (QuotientGroup.mk' Z (t' ^ 3)) := by
    simp only [map_pow, QuotientGroup.mk'_apply]
    exact ((Commute.pow_pow (show Commute (t' : H ⧸ Z) (x' : H ⧸ Z) from hxt.symm) 3 3)).eq
  have hz : ⁅t' ^ 3, x' ^ 3⁆ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' Z) ⁅t' ^ 3, x' ^ 3⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hcen : Commute ⁅t' ^ 3, x' ^ 3⁆ (x' ^ 3) :=
    (Subgroup.mem_center_iff.1 (hZc hz) (x' ^ 3)).symm
  have hconj : ⁅t' ^ 3, x' ^ 3⁆ * x' ^ 3 = t' ^ 3 * x' ^ 3 * (t' ^ 3)⁻¹ := by
    rw [commutatorElement_def]
    group
  have hz7 : ⁅t' ^ 3, x' ^ 3⁆ ^ 7 = 1 := by
    have h1 : (⁅t' ^ 3, x' ^ 3⁆ * x' ^ 3) ^ 7 = 1 := by
      rw [hconj, conj_pow, ha7, mul_one, mul_inv_cancel]
    rwa [hcen.mul_pow, ha7, mul_one] at h1
  have hz1 : ⁅t' ^ 3, x' ^ 3⁆ = 1 := by
    have := pow_gcd_eq_one.2 ⟨hz7, hZ3 _ hz⟩
    simpa using this
  refine ⟨x' ^ 3, t' ^ 3, ha7, hb2, ?_, ?_, ?_⟩
  · exact ((commutatorElement_eq_one_iff_mul_comm).1 hz1).symm
  · simp [QuotientGroup.mk_pow]
  · have h3 : ((t' : H ⧸ Z)) ^ 3 = (t' : H ⧸ Z) := by
      calc (t' : H ⧸ Z) ^ 3 = (t' : H ⧸ Z) ^ 2 * (t' : H ⧸ Z) := by rw [pow_succ]
        _ = (t' : H ⧸ Z) := by rw [ht, one_mul]
    rw [QuotientGroup.mk_pow, h3]

end Lift

section Group

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Fintype K]

omit [Fintype K] in
theorem scalar_pow_three_eq_one {z : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hdet : (z : Matrix (Fin 3) (Fin 3) K).det = 1) : z ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h1 : ((c : Kˣ) : K) ^ 3 = 1 := by
    have : ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = (c : K) ^ 3 := by
      simp [Matrix.GeneralLinearGroup.scalar]
    rw [← this]
    exact hdet
  have h2 : c ^ 3 = 1 := Units.ext (by simpa using h1)
  rw [← map_pow, h2, map_one]

theorem eq_one_of_commute_order_seven_psl_gf16 (hK : Fintype.card K = 16) {G : Type} [Group G]
    (e : G ≃* StatedProj (StatedSL 3 K)) {x t : G} (hxt : x * t = t * x) (hx : x ^ 7 = 1)
    (hx1 : x ≠ 1) (ht : t ^ 2 = 1) : t = 1 := by
  set Z : Subgroup (StatedSL 3 K) := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) with hZ
  have hZc : Z ≤ Subgroup.center (StatedSL 3 K) := by
    intro z hz
    have hz' : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hz
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz' g)
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz =>
    Subtype.ext (scalar_pow_three_eq_one hz (AltStdFaithful.det_eq_one_of_mem_statedSL z.2))
  obtain ⟨a, b, ha7, hb2, hab, ha, hb⟩ := exists_commuting_lifts Z hZc hZ3
    (x := e x) (t := e t) (by rw [← map_mul, ← map_mul, hxt]) (by rw [← map_pow, hx, map_one])
    (by rw [← map_pow, ht, map_one])
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, QuotientGroup.mk_one] at ha
    have h3 : x ^ 3 = 1 := e.injective (by rw [map_pow, ← ha, map_one])
    apply hx1
    calc x = x ^ 7 * (x ^ 3)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hx, h3]; simp
  let A : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Module.End K (Fin 3 → K) := Matrix.toLinAlgEquiv'
  let c : GL (Fin 3) K →* Module.End K (Fin 3 → K) :=
    (A : Matrix (Fin 3) (Fin 3) K →* Module.End K (Fin 3 → K)).comp (Units.coeHom _)
  have hcinj : Function.Injective c := fun a b h => Units.ext (A.injective h)
  let φ : StatedSL 3 K →* Module.End K (Fin 3 → K) := c.comp (StatedSL 3 K).subtype
  have hφ : Function.Injective φ := hcinj.comp Subtype.val_injective
  have hX : φ a ^ 7 = 1 := by rw [← map_pow, ha7, map_one]
  have hY : φ b ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have hXY : φ a * φ b = φ b * φ a := by rw [← map_mul, ← map_mul, hab]
  have hX1 : φ a ≠ 1 := fun h => ha1 (hφ (by rw [h, map_one]))
  have hb1 : b = 1 := hφ (by rw [eq_one_of_commute_order_seven_gf16 hK _ _ hXY hX hY hX1, map_one])
  rw [hb1, QuotientGroup.mk_one] at hb
  exact e.injective (by rw [← hb, map_one])

end Group

end CFSG.OddStandard.L34Faithful
