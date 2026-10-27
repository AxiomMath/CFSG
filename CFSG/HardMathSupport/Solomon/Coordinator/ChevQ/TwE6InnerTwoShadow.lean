module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

section Unique


theorem eq_of_torus_mul_canonicalRep_eq {τ : Tag} {L : Type} [Field L] {t t' : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (ht' : t' ∈ torusGroup τ L) {u u' : WeylGroup τ}
    (h : t * canonicalRep (coxeterSystem τ) L u = t' * canonicalRep (coxeterSystem τ) L u') :
    u = u' := by
  have h1 := (mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_canonicalRep (R := L) u)
  have h2 := (mapsRootLines_of_mem_torusGroup ht').mul (mapsRootLines_canonicalRep (R := L) u')
  rw [one_mul] at h1 h2
  rw [h] at h1
  exact MapsRootLines.unique h1 h2

theorem eq_one_of_one_eq_torus_mul_canonicalRep {τ : Tag} {L : Type} [Field L] {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) {u : WeylGroup τ}
    (h : 1 = t * canonicalRep (coxeterSystem τ) L u) : u = 1 := by
  refine (eq_of_torus_mul_canonicalRep_eq (one_mem _) ht ?_).symm
  rw [canonicalRep_one, mul_one, h]

end Unique

theorem units_mul_apply_eq_self {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {A B : (Module.End L M)ˣ} {m : M} (hA : (A : Module.End L M) m = m)
    (hB : (B : Module.End L M) m = m) : ((A * B : (Module.End L M)ˣ) : Module.End L M) m = m := by
  rw [Units.val_mul, Module.End.mul_apply, hB, hA]

theorem units_inv_apply_eq_self {L M : Type*} [Field L] [AddCommGroup M] [Module L M]
    {A : (Module.End L M)ˣ} {m : M} (hA : (A : Module.End L M) m = m) :
    ((A⁻¹ : (Module.End L M)ˣ) : Module.End L M) m = m := by
  conv_lhs => rw [← hA]
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

section Product


theorem exists_torus_mul_canonicalRep_mul {τ : Tag} {L : Type} [Field L] {t t' : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (ht' : t' ∈ torusGroup τ L) (u u' : WeylGroup τ) :
    ∃ t'' ∈ torusGroup τ L, t * canonicalRep (coxeterSystem τ) L u *
        (t' * canonicalRep (coxeterSystem τ) L u') =
      t'' * canonicalRep (coxeterSystem τ) L (u * u') := by
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) u u'
  have hc : canonicalRep (coxeterSystem τ) L u * t' * (canonicalRep (coxeterSystem τ) L u)⁻¹ ∈
      torusGroup τ L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) u) t').1 ht'
  refine ⟨t * (canonicalRep (coxeterSystem τ) L u * t' * (canonicalRep (coxeterSystem τ) L u)⁻¹) *
    k, mul_mem (mul_mem ht hc) hk, ?_⟩
  calc t * canonicalRep (coxeterSystem τ) L u * (t' * canonicalRep (coxeterSystem τ) L u')
      = t * (canonicalRep (coxeterSystem τ) L u * t' * (canonicalRep (coxeterSystem τ) L u)⁻¹) *
          (canonicalRep (coxeterSystem τ) L u * canonicalRep (coxeterSystem τ) L u') := by group
    _ = _ := by rw [hkk]; group

theorem exists_torus_mul_canonicalRep_inv {τ : Tag} {L : Type} [Field L] {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (u : WeylGroup τ) :
    ∃ t' ∈ torusGroup τ L, (t * canonicalRep (coxeterSystem τ) L u)⁻¹ =
      t' * canonicalRep (coxeterSystem τ) L u⁻¹ := by
  obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (R := L) u⁻¹ u
  rw [inv_mul_cancel, canonicalRep_one, mul_one] at hkk
  have hc : canonicalRep (coxeterSystem τ) L u⁻¹ * t⁻¹ * (canonicalRep (coxeterSystem τ) L u⁻¹)⁻¹ ∈
      torusGroup τ L :=
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := L) u⁻¹) t⁻¹).1 (inv_mem ht)
  refine ⟨k⁻¹ * (canonicalRep (coxeterSystem τ) L u⁻¹ * t⁻¹ *
    (canonicalRep (coxeterSystem τ) L u⁻¹)⁻¹), mul_mem (inv_mem hk) hc, ?_⟩
  have hn :
      (canonicalRep (coxeterSystem τ) L u)⁻¹ = k⁻¹ * canonicalRep (coxeterSystem τ) L u⁻¹ := by
    rw [← hkk]
    group
  rw [mul_inv_rev, hn]
  group

theorem exists_torus_mul_canonicalRep_pow {τ : Tag} {L : Type} [Field L] {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) (u : WeylGroup τ) (m : ℕ) :
    ∃ t' ∈ torusGroup τ L, (t * canonicalRep (coxeterSystem τ) L u) ^ m =
      t' * canonicalRep (coxeterSystem τ) L (u ^ m) := by
  induction m with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, canonicalRep_one, mul_one]⟩
  | succ m ih =>
    obtain ⟨t', ht', h⟩ := ih
    obtain ⟨t'', ht'', h'⟩ := exists_torus_mul_canonicalRep_mul ht' ht (u ^ m) u
    exact ⟨t'', ht'', by rw [pow_succ, h, h', pow_succ]⟩

theorem pow_eq_one_of_torus_mul_canonicalRep {τ : Tag} {L : Type} [Field L] {t : ModGL τ L}
    (ht : t ∈ torusGroup τ L) {u : WeylGroup τ} {m : ℕ}
    (h : (t * canonicalRep (coxeterSystem τ) L u) ^ m = 1) : u ^ m = 1 := by
  obtain ⟨t', ht', h'⟩ := exists_torus_mul_canonicalRep_pow ht u m
  rw [h] at h'
  have e : (1 : ModGL τ L) * canonicalRep (coxeterSystem τ) L 1 =
      t' * canonicalRep (coxeterSystem τ) L (u ^ m) := by
    rw [canonicalRep_one, mul_one, h']
  exact (eq_of_torus_mul_canonicalRep_eq (one_mem _) ht' e).symm

end Product

section Frame

variable
  {K : Type} [Field K] {σ : K ≃+* K} (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))

theorem twE6Frame_mul (x y : twistedE6RootGroup K σ) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0) *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          g0) := by
  rw [Subgroup.coe_mul, map_mul]
  group

theorem twE6Frame_one :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 = 1 := by
  rw [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel]

theorem twE6Frame_inv (x : twistedE6RootGroup K σ) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0)⁻¹ := by
  rw [Subgroup.coe_inv, map_inv]
  group

theorem twE6Frame_pow (x : twistedE6RootGroup K σ) (m : ℕ) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x ^ m : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
      (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, twE6Frame_one]
  | succ m ih => rw [pow_succ, twE6Frame_mul, ih, pow_succ]

end Frame

section FrameParts

variable
  {K : Type} [Field K] {σ : K ≃+* K} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}

theorem exists_twE6Frame_mul_eq {x y : twistedE6RootGroup K σ}
    {t t' : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    (ht' : t' ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u u' : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)
    (hy : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
      g0 = t' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u') :
    ∃ s ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        s * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u') := by
  obtain ⟨s, hs, e⟩ := exists_torus_mul_canonicalRep_mul ht ht' u u'
  exact ⟨s, hs, by rw [twE6Frame_mul, hx, hy, e]⟩

theorem exists_twE6Frame_inv_eq {x : twistedE6RootGroup K σ}
    {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) :
    ∃ s ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        s * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u⁻¹ := by
  obtain ⟨s, hs, e⟩ := exists_torus_mul_canonicalRep_inv ht u
  exact ⟨s, hs, by rw [twE6Frame_inv, hx, e]⟩

theorem exists_twE6Frame_pow_eq {x : twistedE6RootGroup K σ}
    {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) (m : ℕ) :
    ∃ s ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x ^ m : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        s * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u ^ m) := by
  obtain ⟨s, hs, e⟩ := exists_torus_mul_canonicalRep_pow ht u m
  exact ⟨s, hs, by rw [twE6Frame_pow, hx, e]⟩

theorem pow_eq_one_of_twE6Frame_eq {x : twistedE6RootGroup K σ} {m : ℕ} (hxm : x ^ m = 1)
    {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) :
    u ^ m = 1 := by
  refine pow_eq_one_of_torus_mul_canonicalRep ht ?_
  rw [← hx, ← twE6Frame_pow, hxm, twE6Frame_one]

theorem commute_of_twE6Frame_eq {x y : twistedE6RootGroup K σ} (hxy : x * y = y * x)
    {t t' : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    (ht' : t' ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u u' : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)
    (hy : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
      g0 = t' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u') :
    Commute u u' := by
  obtain ⟨s, hs, e1⟩ := exists_twE6Frame_mul_eq ht ht' hx hy
  obtain ⟨s', hs', e2⟩ := exists_twE6Frame_mul_eq ht' ht hy hx
  rw [hxy] at e1
  exact eq_of_torus_mul_canonicalRep_eq hs hs' (e1.symm.trans e2)

end FrameParts

section Three

variable {G : Type*} [Group G]

theorem mem_zpowers_of_pow_three_eq_one {w w₁ u : G} (hw₁ : w₁ ∈ Subgroup.zpowers w)
    (hw₁3 : w₁ ^ 3 = 1) (hw₁1 : w₁ ≠ 1) (hu : u ∈ Subgroup.zpowers w) (hu3 : u ^ 3 = 1) :
    u ∈ Subgroup.zpowers w₁ := by
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw₁
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have hpow : ∀ c : ℤ, (w ^ c) ^ 3 = w ^ (3 * c) := fun c => by
    rw [mul_comm, zpow_mul, zpow_ofNat]
  obtain ⟨s, hs⟩ := (orderOf_dvd_iff_zpow_eq_one (x := w)).2 (by rw [← hpow]; exact hw₁3)
  obtain ⟨r, hr⟩ := (orderOf_dvd_iff_zpow_eq_one (x := w)).2 (by rw [← hpow]; exact hu3)
  set n : ℤ := (orderOf w : ℤ) with hn
  have hs3 : ¬ (3 : ℤ) ∣ s := by
    rintro ⟨s', rfl⟩
    refine hw₁1 ((orderOf_dvd_iff_zpow_eq_one (x := w)).1 ⟨s', ?_⟩)
    linarith
  have hm : s % 3 = 1 ∨ s % 3 = 2 := by omega
  have hss : s * s % 3 = 1 := by
    rcases hm with hm | hm <;> rw [Int.mul_emod, hm] <;> norm_num
  obtain ⟨c, hc⟩ : ∃ c : ℤ, 1 - s * s = 3 * c := by
    generalize s * s = N at hss ⊢
    exact ⟨(1 - N) / 3, by omega⟩
  have hw : w ^ n = 1 := by
    rw [hn, zpow_natCast]
    exact pow_orderOf_eq_one w
  have key : 3 * a = 3 * (b * (r * s) + n * (r * c)) := by
    linear_combination hr - r * s * hs + n * r * hc
  have key' : a = b * (r * s) + n * (r * c) := Int.eq_of_mul_eq_mul_left (by norm_num) key
  refine Subgroup.mem_zpowers_iff.2 ⟨r * s, ?_⟩
  rw [← zpow_mul, key', zpow_add, zpow_mul w n, hw, one_zpow, mul_one]

theorem exists_eq_pow_mul_pow_of_not_dvd {w₁ w₂ : G} (h12 : Commute w₁ w₂) (h1 : w₁ ^ 3 = 1)
    (h2 : w₂ ^ 3 = 1) {i j k l : ℕ} (hdet : ¬ (3 : ℤ) ∣ ((i * l : ℕ) : ℤ) - ((j * k : ℕ) : ℤ))
    (a b : ℕ) : ∃ c d : ℕ, w₁ ^ a * w₂ ^ b = (w₁ ^ i * w₂ ^ j) ^ c * (w₁ ^ k * w₂ ^ l) ^ d := by
  have hmod : ∀ {x : G}, x ^ 3 = 1 → ∀ m : ℕ, x ^ m = x ^ (m % 3) := fun hx m => by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, hx, one_pow, mul_one]
  set D : ℕ := i * l + 2 * (j * k) with hD
  have hD3 : D % 3 = 1 ∨ D % 3 = 2 := by
    have : ¬ 3 ∣ D := by
      intro h3
      apply hdet
      push_cast at h3 ⊢
      generalize i * l = A at h3 ⊢
      generalize j * k = B at h3 ⊢
      omega
    omega
  have hDD : D * D % 3 = 1 := by
    rcases hD3 with h | h <;> rw [Nat.mul_mod, h]
  refine ⟨(a * l + 2 * (b * k)) * D, (b * i + 2 * (a * j)) * D, ?_⟩
  have e1 : i * ((a * l + 2 * (b * k)) * D) + k * ((b * i + 2 * (a * j)) * D) =
      a * (D * D) + 3 * (b * i * k * D) := by
    rw [hD]
    ring
  have e2 : j * ((a * l + 2 * (b * k)) * D) + l * ((b * i + 2 * (a * j)) * D) =
      b * (D * D) + 3 * (a * j * l * D) := by
    rw [hD]
    ring
  have m1 : (a * (D * D) + 3 * (b * i * k * D)) % 3 = a % 3 := by
    rw [Nat.add_mul_mod_self_left, Nat.mul_mod, hDD, mul_one, Nat.mod_mod]
  have m2 : (b * (D * D) + 3 * (a * j * l * D)) % 3 = b % 3 := by
    rw [Nat.add_mul_mod_self_left, Nat.mul_mod, hDD, mul_one, Nat.mod_mod]
  rw [(h12.pow_pow i j).mul_pow, (h12.pow_pow k l).mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_mul, mul_assoc, ← mul_assoc (w₂ ^ (j * _)), ((h12.pow_pow _ _).symm).eq, mul_assoc,
    ← pow_add, ← mul_assoc, ← pow_add, hmod h1 (i * _ + k * _), hmod h2 (j * _ + l * _), e1, e2,
    m1, m2, ← hmod h1, ← hmod h2]

end Three

theorem neg_mem_a2Roots {τ : Tag} {α β γ : Fin τ.rank → ℤ} (hγ : γ ∈ a2Roots α β) :
    -γ ∈ a2Roots α β := by
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
