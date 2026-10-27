module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.FrameNormalize
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.QuatDerived

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix


theorem twistComm_of_mat {w g : WeylGroup TwistTag.D4.tag}
    (hw : ∀ x, w • x = d4T36M (-1) *ᵥ permLattice TwistTag.D4.perm.symm x)
    {A : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ}
    (hg : ∀ x, g • x = A *ᵥ x) (hA : A * d4T36M (-1) = d4T36M (-1) * A) :
    w * weylTwist TwistTag.D4 g = g * w := by
  refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => ?_
  set y : Fin TwistTag.D4.tag.rank → ℤ := permLattice TwistTag.D4.perm.symm x with hy
  have hx : x = permLattice TwistTag.D4.perm y := by
    rw [hy]
    ext j; simp [permLattice]
  rw [mul_smul, mul_smul, hx, weylTwist_smul_permLattice, hw, hw, hg]
  have h1 : permLattice TwistTag.D4.perm.symm (permLattice TwistTag.D4.perm y) = y := by
    ext j; simp [permLattice]
  have h2 : permLattice TwistTag.D4.perm.symm
      (permLattice TwistTag.D4.perm (A *ᵥ y)) = A *ᵥ y := by
    ext j; simp [permLattice]
  rw [hg, h1, h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]

section Y

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ℓ f : ℕ}

@[expose] noncomputable def frameCent (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hwN : w ∈ frameNorm F) :
    Subgroup (frameNorm F) :=
  Subgroup.centralizer {(⟨w, hwN⟩ : frameNorm F)}

theorem mem_frameCent (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hwN : w ∈ frameNorm F)
    {x : frameNorm F} : x ∈ frameCent F hwN ↔ (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * w =
      w * x := by
  rw [frameCent, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg (fun z : frameNorm F => (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) h
  · intro h
    exact Subtype.ext h

theorem frameCent_injOn [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hwN : w ∈ frameNorm F)
    (hinv : ∀ y ∈ frameTorus F, w * y * w⁻¹ = y⁻¹) {x y : frameNorm F}
    (hx : x ∈ frameCent F hwN) (hy : y ∈ frameCent F hwN)
    (h : frameWeyl F x = frameWeyl F y) : x = y := by
  classical
  have hodd := frameWeyl_ker_card_odd hf hK hσ F
  set W' : frameNorm F := ⟨w, hwN⟩ with hW'
  set z : frameNorm F := x⁻¹ * y with hz
  have hzC : z ∈ frameCent F hwN := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy
  have hzker : z ∈ (frameWeyl F).ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, h, inv_mul_cancel]
  have hcomm : z * W' = W' * z := Subgroup.mem_centralizer_singleton_iff.1 hzC
  have hinvz : W' * z * W'⁻¹ = z⁻¹ :=
    Subtype.ext (hinv _ (frameWeyl_ker_mem hσ F hzker))
  have hzz : z * z = 1 := by
    have h1 : W' * z * W'⁻¹ = z := by rw [← hcomm]; group
    rw [h1] at hinvz
    calc z * z = z * z⁻¹ := by rw [← hinvz]
      _ = 1 := mul_inv_cancel z
  let zk : (frameWeyl F).ker := ⟨z, hzker⟩
  have hzk : zk ^ 2 = 1 := by
    apply Subtype.ext
    simp only [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact hzz
  have h2 : orderOf zk ∣ 2 := orderOf_dvd_of_pow_eq_one hzk
  have h3 : orderOf zk ∣ Nat.card (frameWeyl F).ker := orderOf_dvd_natCard zk
  have h1 : orderOf zk = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h' | h'
    · exact h'
    · exfalso
      rw [h'] at h3
      obtain ⟨m, hm⟩ := hodd
      obtain ⟨k, hk⟩ := h3
      omega
  have hzk1 : zk = 1 := orderOf_eq_one_iff.1 h1
  have hz1 : z = 1 := congrArg (fun t : (frameWeyl F).ker => (t : frameNorm F)) hzk1
  calc x = x * z := by rw [hz1, mul_one]
    _ = y := by rw [hz]; group

theorem exists_frameCent_lift [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hwN : w ∈ frameNorm F)
    (hwW : frameWeyl F ⟨w, hwN⟩ = quatHom (QuaternionGroup.a 2))
    (hinv : ∀ y ∈ frameTorus F, w * y * w⁻¹ = y⁻¹)
    {u : WeylGroup TwistTag.D4.tag} {A : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ}
    (hu : ∀ x, u • x = A *ᵥ x) (hA : A * d4T36M (-1) = d4T36M (-1) * A) :
    ∃ x ∈ frameCent F hwN, frameWeyl F x = u := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hodd := frameWeyl_ker_card_odd hf hK hσ F
  obtain ⟨x₀, hx₀⟩ := exists_frameLift hq1 F (twistComm_of_mat F.hw hu hA)
  set W' : frameNorm F := ⟨w, hwN⟩ with hW'
  have hinvG : ∀ y ∈ (frameWeyl F).ker, W' * y * W'⁻¹ = y⁻¹ := fun y hy =>
    Subtype.ext (hinv _ (frameWeyl_ker_mem hσ F hy))
  have hcommG : ∀ y₁ ∈ (frameWeyl F).ker, ∀ y₂ ∈ (frameWeyl F).ker, y₁ * y₂ = y₂ * y₁ :=
    fun y₁ h₁ y₂ h₂ =>
      Subtype.ext (frameTorus_comm F (frameWeyl_ker_mem hσ F h₁) (frameWeyl_ker_mem hσ F h₂))
  have hZu : u * frameWeyl F W' = frameWeyl F W' * u := by
    refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => ?_
    rw [hwW, mul_smul, mul_smul, quatHom_a_two_smul, quatHom_a_two_smul, hu, hu, Matrix.mulVec_neg]
  set m : frameNorm F := x₀ * W' * x₀⁻¹ * W'⁻¹ with hm
  have hmker : m ∈ (frameWeyl F).ker := by
    rw [MonoidHom.mem_ker, hm]
    simp only [map_mul, map_inv, hx₀]
    have key : u * frameWeyl F W' * u⁻¹ * (frameWeyl F W')⁻¹ = 1 := by rw [hZu]; group
    calc _ = u * frameWeyl F W' * u⁻¹ * (frameWeyl F W')⁻¹ := by group
      _ = 1 := key
  set t : frameNorm F := x₀⁻¹ * m⁻¹ * x₀ with ht
  have htker : t ∈ (frameWeyl F).ker := by
    have := (frameWeyl F).normal_ker.conj_mem _ ((frameWeyl F).ker.inv_mem hmker) x₀⁻¹
    rw [inv_inv] at this
    exact this
  set N := Nat.card (frameWeyl F).ker with hN
  obtain ⟨m', hm'⟩ := hodd
  let tk : (frameWeyl F).ker := ⟨t, htker⟩
  set Sk : (frameWeyl F).ker := tk ^ (m' + 1) with hSk
  have hSk2 : Sk * Sk = tk := by
    have h1 : tk ^ N = 1 := pow_card_eq_one'
    calc Sk * Sk = tk ^ (m' + 1 + (m' + 1)) := by rw [hSk]; exact (pow_add _ _ _).symm
      _ = tk ^ N * tk := by rw [show m' + 1 + (m' + 1) = N + 1 by omega, pow_succ]
      _ = tk := by rw [h1, one_mul]
  set S : frameNorm F := (Sk : frameNorm F) with hS
  have hSker : S ∈ (frameWeyl F).ker := Sk.2
  have hS2 : S * S = t := congrArg (fun x : (frameWeyl F).ker => (x : frameNorm F)) hSk2
  have hSW : S * W' * S⁻¹ = t * W' := by
    have h1 := hinvG _ ((frameWeyl F).ker.inv_mem hSker)
    rw [inv_inv] at h1
    calc S * W' * S⁻¹ = S * (W' * S⁻¹ * W'⁻¹) * W' := by group
      _ = S * S * W' := by rw [h1]
      _ = t * W' := by rw [hS2]
  refine ⟨x₀ * S, ?_, ?_⟩
  · rw [frameCent, Subgroup.mem_centralizer_singleton_iff]
    have h1 : x₀ * S * W' * (x₀ * S)⁻¹ = W' := by
      calc x₀ * S * W' * (x₀ * S)⁻¹ = x₀ * (S * W' * S⁻¹) * x₀⁻¹ := by group
        _ = x₀ * (t * W') * x₀⁻¹ := by rw [hSW]
        _ = x₀ * (x₀⁻¹ * m⁻¹ * x₀) * W' * x₀⁻¹ := by rw [ht]; group
        _ = W' := by rw [hm]; group
    calc x₀ * S * W' = (x₀ * S * W' * (x₀ * S)⁻¹) * (x₀ * S) := by group
      _ = W' * (x₀ * S) := by rw [h1]
  · rw [map_mul, hx₀, (MonoidHom.mem_ker.1 hSker), mul_one]

theorem exists_quaternion_derived [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hwN : w ∈ frameNorm F)
    (hwW : frameWeyl F ⟨w, hwN⟩ = quatHom (QuaternionGroup.a 2))
    (hinv : ∀ y ∈ frameTorus F, w * y * w⁻¹ = y⁻¹) :
    ∃ a b y₁ y₂ y₃ y₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      a ∈ frameNorm F ∧ b ∈ frameNorm F ∧ y₁ ∈ frameNorm F ∧ y₂ ∈ frameNorm F ∧
      y₃ ∈ frameNorm F ∧ y₄ ∈ frameNorm F ∧
      y₁ * w = w * y₁ ∧ y₂ * w = w * y₂ ∧ y₃ * w = w * y₃ ∧ y₄ * w = w * y₄ ∧
      a = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∧ b = y₃ * y₄ * y₃⁻¹ * y₄⁻¹ ∧
      a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b * a⁻¹ * b⁻¹ = w ∧ a * a = w ∧ b * b = w ∧
      b * a * b⁻¹ = a⁻¹ ∧ w * w = 1 := by
  classical
  obtain ⟨xc, hxc, hxcW⟩ := exists_frameCent_lift hf hK hσ F hwN hwW hinv (u := wElt derC)
    (wElt_smul derC) derC_comm
  obtain ⟨x1, hx1, hx1W⟩ := exists_frameCent_lift hf hK hσ F hwN hwW hinv (u := wElt derY1)
    (wElt_smul derY1) derY1_comm
  obtain ⟨x2, hx2, hx2W⟩ := exists_frameCent_lift hf hK hσ F hwN hwW hinv (u := wElt derY2)
    (wElt_smul derY2) derY2_comm
  set W' : frameNorm F := ⟨w, hwN⟩ with hW'
  have key : ∀ {x y : frameNorm F}, x ∈ frameCent F hwN → y ∈ frameCent F hwN →
      frameWeyl F x = frameWeyl F y → x = y := fun hx hy h =>
    frameCent_injOn hf hK hσ F hwN hinv hx hy h
  have hW'C : W' ∈ frameCent F hwN := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set a' : frameNorm F := xc * x1 * xc⁻¹ * x1⁻¹ with ha'
  set b' : frameNorm F := xc * x2 * xc⁻¹ * x2⁻¹ with hb'
  have ha'C : a' ∈ frameCent F hwN :=
    mul_mem (mul_mem (mul_mem hxc hx1) (inv_mem hxc)) (inv_mem hx1)
  have hb'C : b' ∈ frameCent F hwN :=
    mul_mem (mul_mem (mul_mem hxc hx2) (inv_mem hxc)) (inv_mem hx2)
  have hWa : frameWeyl F a' = quatHom (QuaternionGroup.a 1) := by
    rw [ha', map_mul, map_mul, map_mul, map_inv, map_inv, hxcW, hx1W]
    calc wElt derC * wElt derY1 * (wElt derC)⁻¹ * (wElt derY1)⁻¹
        = (quatHom (QuaternionGroup.a 1) * wElt derY1 * wElt derC) * (wElt derC)⁻¹ *
          (wElt derY1)⁻¹ := by rw [wElt_C_Y1]
      _ = quatHom (QuaternionGroup.a 1) := by group
  have hWb : frameWeyl F b' = quatHom (QuaternionGroup.xa 0) := by
    rw [hb', map_mul, map_mul, map_mul, map_inv, map_inv, hxcW, hx2W]
    calc wElt derC * wElt derY2 * (wElt derC)⁻¹ * (wElt derY2)⁻¹
        = (quatHom (QuaternionGroup.xa 0) * wElt derY2 * wElt derC) * (wElt derC)⁻¹ *
          (wElt derY2)⁻¹ := by rw [wElt_C_Y2]
      _ = quatHom (QuaternionGroup.xa 0) := by group
  have hq1 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
      (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 2 := by decide
  have hq2 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide
  have hq3 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide
  have hq4 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ := by decide
  have hq5 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
  have hq6 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 :=
    QuaternionGroup.a_one_pow_n (n := 2)
  have hq7 : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 4 = 1 := QuaternionGroup.xa_pow_four _
  have hA4 : a' ^ 4 = 1 := key (pow_mem ha'C 4) (one_mem _) (by
    rw [map_pow, hWa, ← map_pow, hq6, map_one, map_one])
  have hB4 : b' ^ 4 = 1 := key (pow_mem hb'C 4) (one_mem _) (by
    rw [map_pow, hWb, ← map_pow, hq7, map_one, map_one])
  have hAB : a' * b' * a'⁻¹ * b'⁻¹ = W' :=
    key (mul_mem (mul_mem (mul_mem ha'C hb'C) (inv_mem ha'C)) (inv_mem hb'C)) hW'C (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hWa, hWb, hwW, ← map_inv, ← map_inv,
        ← map_mul, ← map_mul, ← map_mul, hq1])
  have hAA : a' * a' = W' := key (mul_mem ha'C ha'C) hW'C (by
    rw [map_mul, hWa, hwW, ← map_mul, hq2])
  have hBB : b' * b' = W' := key (mul_mem hb'C hb'C) hW'C (by
    rw [map_mul, hWb, hwW, ← map_mul, hq3])
  have hBA : b' * a' * b'⁻¹ = a'⁻¹ :=
    key (mul_mem (mul_mem hb'C ha'C) (inv_mem hb'C)) (inv_mem ha'C) (by
      rw [map_mul, map_mul, map_inv, map_inv, hWa, hWb, ← map_inv, ← map_mul, ← map_mul, hq4,
        map_inv])
  have hWW : W' * W' = 1 := key (mul_mem hW'C hW'C) (one_mem _) (by
    rw [map_mul, hwW, ← map_mul, hq5, map_one, map_one])
  have hcN : ∀ x : frameNorm F, (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈ frameNorm F :=
    fun x => x.2
  refine ⟨(a' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (b' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (xc : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (x1 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (xc : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    (x2 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), a'.2, b'.2, xc.2, x1.2, xc.2, x2.2,
    (mem_frameCent F hwN).1 hxc, (mem_frameCent F hwN).1 hx1, (mem_frameCent F hwN).1 hxc,
    (mem_frameCent F hwN).1 hx2, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hA4]; rfl
  · rw [← Subgroup.coe_pow, hB4]; rfl
  · exact congrArg (fun x : frameNorm F => (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hAB
  · exact congrArg (fun x : frameNorm F => (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hAA
  · exact congrArg (fun x : frameNorm F => (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hBB
  · exact congrArg (fun x : frameNorm F => (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hBA
  · exact congrArg (fun x : frameNorm F => (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hWW

theorem exists_quaternion_derived_normalizing_plane [Fact ℓ.Prime] (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (F : D4PhiFrame K σ (ℓ ^ f) (-1))
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1)
    {s : ModGL TwistTag.D4.tag (AlgebraicClosure K)}
    (hs : s ∈ torusGroup TwistTag.D4.tag (AlgebraicClosure K))
    {w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hw : triEmb K σ (AlgebraicClosure K) w =
      F.g0 * (s * trialityOpposition (AlgebraicClosure K)) * F.g0⁻¹)
    {E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hEtor : E ≤ frameTorus F)
    (hEexp : ∀ y ∈ E, y ^ r = 1) (hEcard : Nat.card E = r ^ 2)
    (P : Sylow r (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hEP : E ≤ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hPΩ : ∀ x ∈ (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), x ^ r = 1 → x ∈ E) :
    ∃ a b y₁ y₂ y₃ y₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      y₁ * w = w * y₁ ∧ y₂ * w = w * y₂ ∧ y₃ * w = w * y₃ ∧ y₄ * w = w * y₄ ∧
      a = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∧ b = y₃ * y₄ * y₃⁻¹ * y₄⁻¹ ∧
      a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b * a⁻¹ * b⁻¹ = w ∧ a * a = w ∧ b * b = w ∧
      b * a * b⁻¹ = a⁻¹ ∧ w * w = 1 ∧
      (∀ y ∈ E, a * y * a⁻¹ ∈ E ∧ a⁻¹ * y * a ∈ E ∧ b * y * b⁻¹ ∈ E ∧ b⁻¹ * y * b ∈ E) := by
  have hz : trialityOpposition (AlgebraicClosure K) ∈
      monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K) :=
    trialityOpposition_mem_monomialSubgroup
  have hφw : frameConj F w = s * trialityOpposition (AlgebraicClosure K) := by
    rw [frameConj_apply, hw]
    group
  have hm : s * trialityOpposition (AlgebraicClosure K) ∈
      monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K) :=
    mul_mem (torusGroup_le_monomialSubgroup hs) hz
  have hwN : w ∈ frameNorm F := by
    change frameConj F w ∈ monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)
    rw [hφw]
    exact hm
  have hwW : frameWeyl F ⟨w, hwN⟩ = quatHom (QuaternionGroup.a 2) := by
    refine eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun x => ?_
    rw [quatHom_a_two_smul, frameWeyl_apply]
    have hW : weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨s * trialityOpposition _, hm⟩ =
        weylQuotientHom TwistTag.D4.tag (AlgebraicClosure K) ⟨trialityOpposition _, hz⟩ :=
      weylQuotientHom_eq (by
        simpa using (mapsRootLines_of_mem_torusGroup hs).mul
          (mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := AlgebraicClosure K)
            ⟨trialityOpposition (AlgebraicClosure K), hz⟩))
    have e : (⟨frameConj F ((⟨w, hwN⟩ : frameNorm F) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (⟨w, hwN⟩ : frameNorm F).2⟩ : monomialSubgroup TwistTag.D4.tag (AlgebraicClosure K)) =
        ⟨s * trialityOpposition _, hm⟩ := Subtype.ext hφw
    rw [e, hW]
    exact weylQuotientHom_trialityOpposition_smul x
  obtain ⟨a, b, y₁, y₂, y₃, y₄, ha, hb, h1, h2, h3, h4, c1, c2, c3, c4, ea, eb, ha4, hb4, hab, haa,
    hbb, hba, hww⟩ := exists_quaternion_derived hf hK hσ F hwN hwW
      (fun y hy => involution_inv_frameTorus F hs hw hy)
  have hnorm : ∀ g ∈ frameNorm F, ∀ y ∈ E, g * y * g⁻¹ ∈ E := fun g hg y hy =>
    frameNorm_normalizes_plane hf hK hσ F hr hr3 hrd hEtor hEexp hEcard P hEP hPΩ hg hy
  refine ⟨a, b, y₁, y₂, y₃, y₄, c1, c2, c3, c4, ea, eb, ha4, hb4, hab, haa, hbb, hba, hww,
    fun y hy => ⟨hnorm a ha y hy, ?_, hnorm b hb y hy, ?_⟩⟩
  · have := hnorm a⁻¹ ((frameNorm F).inv_mem ha) y hy
    rwa [inv_inv] at this
  · have := hnorm b⁻¹ ((frameNorm F).inv_mem hb) y hy
    rwa [inv_inv] at this

end Y

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
