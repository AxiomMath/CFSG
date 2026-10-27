module

public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Perfect

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Module
open scoped IsMulCommutative

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

structure SuzukiData (na nb : Module.End (ZMod p) W) : Prop where
  sq_a : na * na = 0
  sq_b : nb * nb = 0
  ne_a : na ≠ 0
  irr : ∀ S : Submodule (ZMod p) W, (∀ w ∈ S, na w ∈ S) → (∀ w ∈ S, nb w ∈ S) → S = ⊥ ∨ S = ⊤

variable {na nb : Module.End (ZMod p) W}

def mu (na nb : Module.End (ZMod p) W) : Module.End (ZMod p) W := na * nb + nb * na

theorem mu_comm_a (h : SuzukiData na nb) : mu na nb * na = na * mu na nb := by
  have e1 : mu na nb * na = na * nb * na := by
    unfold mu; rw [add_mul, mul_assoc nb na na, h.sq_a]; simp
  have e2 : na * mu na nb = na * nb * na := by
    unfold mu; rw [mul_add, ← mul_assoc na na nb, h.sq_a]; simp [mul_assoc]
  rw [e1, e2]

theorem mu_comm_b (h : SuzukiData na nb) : mu na nb * nb = nb * mu na nb := by
  have e1 : mu na nb * nb = nb * na * nb := by
    unfold mu; rw [add_mul, mul_assoc na nb nb, h.sq_b]; simp
  have e2 : nb * mu na nb = nb * na * nb := by
    unfold mu; rw [mul_add, ← mul_assoc nb nb na, h.sq_b]; simp [mul_assoc]
  rw [e1, e2]

abbrev Kalg (na nb : Module.End (ZMod p) W) : Subalgebra (ZMod p) (Module.End (ZMod p) W) :=
  Algebra.adjoin (ZMod p) {mu na nb}

theorem Kalg_comm (h : SuzukiData na nb) {k : Module.End (ZMod p) W} (hk : k ∈ Kalg na nb) :
    k * na = na * k ∧ k * nb = nb * k := by
  have hle : Kalg na nb ≤ Subalgebra.centralizer (ZMod p) {na, nb} := by
    refine Algebra.adjoin_le ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | rfl
    · exact (mu_comm_a h).symm
    · exact (mu_comm_b h).symm
  have := (Subalgebra.mem_centralizer_iff (ZMod p)).mp (hle hk)
  exact ⟨(this na (by simp)).symm, (this nb (by simp)).symm⟩

theorem Kalg_unit [Finite W] (h : SuzukiData na nb) {k : Module.End (ZMod p) W}
    (hk : k ∈ Kalg na nb) (hk0 : k ≠ 0) : ∃ k' ∈ Kalg na nb, k * k' = 1 := by
  obtain ⟨hka, hkb⟩ := Kalg_comm h hk
  have hker : LinearMap.ker k = ⊥ := by
    rcases h.irr (LinearMap.ker k) (fun w hw => by
        rw [LinearMap.mem_ker] at hw ⊢
        have := congrArg (fun f => f w) hka
        simp only [Module.End.mul_apply] at this
        rw [this, hw, map_zero]) (fun w hw => by
        rw [LinearMap.mem_ker] at hw ⊢
        have := congrArg (fun f => f w) hkb
        simp only [Module.End.mul_apply] at this
        rw [this, hw, map_zero]) with hbot | htop
    · exact hbot
    · exfalso; apply hk0; ext w
      have : w ∈ LinearMap.ker k := by rw [htop]; trivial
      simpa using this
  have hinj : Function.Injective k := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective k := Finite.injective_iff_surjective.mp hinj
  have hunit : IsUnit k := (Module.End.isUnit_iff k).mpr ⟨hinj, hsurj⟩
  obtain ⟨u, rfl⟩ := hunit
  have : Finite (Module.End (ZMod p) W) :=
    Finite.of_injective (fun f : Module.End (ZMod p) W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨n, hn, hun⟩ := (isOfFinOrder_of_finite u).exists_pow_eq_one
  refine ⟨(u : Module.End (ZMod p) W) ^ (n - 1), Subalgebra.pow_mem _ hk _, ?_⟩
  have : (u : Module.End (ZMod p) W) * (u : Module.End (ZMod p) W) ^ (n - 1) =
      ((u ^ n : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) := by
    rw [Units.val_pow_eq_pow_val, ← pow_succ']
    congr 1; omega
  rw [this, hun]; rfl

theorem Kalg_isField [Finite W] (h : SuzukiData na nb) : IsField (Kalg na nb) := by
  have : IsMulCommutative (Kalg na nb) := Algebra.isMulCommutative_adjoin (ZMod p) (by simp)
  refine ⟨?_, fun a b => Std.Commutative.comm (op := (· * ·)) a b, fun {a} ha => ?_⟩
  · refine ⟨0, 1, fun h01 => ?_⟩
    have h01' : (0 : Module.End (ZMod p) W) = 1 := congrArg Subtype.val h01
    apply h.ne_a
    ext w
    have := congrArg (fun f => f (na w)) h01'
    simp at this
    simpa using this.symm
  · obtain ⟨k', hk', hk⟩ := Kalg_unit h a.2 (fun h0 => ha (Subtype.ext h0))
    exact ⟨⟨k', hk'⟩, Subtype.ext hk⟩

theorem suzuki_coord [Finite W] (h : SuzukiData na nb) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : Module K W) (_ : Finite K)
      (coord : W ≃ₗ[K] K × K) (r : K),
      r ≠ 0 ∧ Module.finrank (ZMod p) K = (minpoly (ZMod p) r).natDegree ∧
      (∀ (k : K) (w : W), na (k • w) = k • na w ∧ nb (k • w) = k • nb w) ∧
      (∀ x c : K, coord (na (coord.symm (x, c))) = (r * c, 0)) ∧
      (∀ x c : K, coord (nb (coord.symm (x, c))) = (0, x)) := by
  let _ : Field (Kalg na nb) := (Kalg_isField h).toField
  have hfin : Finite (Module.End (ZMod p) W) :=
    Finite.of_injective (fun f : Module.End (ZMod p) W => (f : W → W)) DFunLike.coe_injective
  have hKfin : Finite (Kalg na nb) := Finite.of_injective (Subalgebra.val _) Subtype.val_injective
  have hsmul : ∀ (k : Kalg na nb) (w : W), k • w = (k : Module.End (ZMod p) W) w := fun k w => rfl
  have hcomm : ∀ (k : Kalg na nb) (w : W), na (k • w) = k • na w ∧ nb (k • w) = k • nb w := by
    intro k w
    obtain ⟨h1, h2⟩ := Kalg_comm h k.2
    refine ⟨?_, ?_⟩
    · rw [hsmul, hsmul]
      have := congrArg (fun f => f w) h1
      simp only [Module.End.mul_apply] at this
      exact this.symm
    · rw [hsmul, hsmul]
      have := congrArg (fun f => f w) h2
      simp only [Module.End.mul_apply] at this
      exact this.symm
  obtain ⟨w₀, hw₀⟩ : ∃ w, na w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h.ne_a (by ext w; simpa using hcon w)
  set e₁ : W := na w₀ with he₁
  set e₂ : W := nb e₁ with he₂
  have hna1 : na e₁ = 0 := by
    have := congrArg (fun f => f w₀) h.sq_a
    simpa using this
  have hnb2 : nb e₂ = 0 := by
    have := congrArg (fun f => f e₁) h.sq_b
    simpa using this
  set r : Kalg na nb := ⟨mu na nb, Algebra.self_mem_adjoin_singleton (ZMod p) (mu na nb)⟩ with hr
  have hna2 : na e₂ = r • e₁ := by
    rw [hsmul]
    simp only [hr, mu, he₂, LinearMap.add_apply, Module.End.mul_apply]
    rw [hna1, map_zero, add_zero]
  have hL1 : e₁ ≠ 0 := hw₀
  let f : (Kalg na nb) × (Kalg na nb) →ₗ[Kalg na nb] W :=
    LinearMap.coprod (LinearMap.toSpanSingleton (Kalg na nb) W e₁)
      (LinearMap.toSpanSingleton (Kalg na nb) W e₂)
  have hf : ∀ x c : Kalg na nb, f (x, c) = x • e₁ + c • e₂ := fun x c => rfl
  have hfna : ∀ x c : Kalg na nb, na (f (x, c)) = f (r * c, 0) := by
    intro x c
    rw [hf, hf, map_add, (hcomm x e₁).1, (hcomm c e₂).1, hna1, hna2, smul_zero, zero_add,
      smul_smul, zero_smul, add_zero, mul_comm]
  have hfnb : ∀ x c : Kalg na nb, nb (f (x, c)) = f (0, x) := by
    intro x c
    rw [hf, hf, map_add, (hcomm x e₁).2, (hcomm c e₂).2, hnb2, smul_zero, add_zero, zero_smul,
      zero_add]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, c⟩ hxc
    have hxc' : x • e₁ + c • e₂ = 0 := by rw [← hf]; exact hxc
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero] at hxc'
      have hx : x = 0 := by
        rcases smul_eq_zero.mp hxc' with h0 | h0
        · exact h0
        · exact absurd h0 hL1
      subst hx; rfl
    · exfalso
      have he2 : e₂ = (-(c⁻¹ * x)) • e₁ := by
        have h1 : c • e₂ = -(x • e₁) := eq_neg_of_add_eq_zero_right hxc'
        calc e₂ = c⁻¹ • (c • e₂) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          _ = c⁻¹ • (-(x • e₁)) := by rw [h1]
          _ = (-(c⁻¹ * x)) • e₁ := by rw [smul_neg, smul_smul, neg_smul]
      let L : Submodule (ZMod p) W := (Submodule.span (Kalg na nb) {e₁}).restrictScalars (ZMod p)
      have hLa : ∀ w ∈ L, na w ∈ L := by
        intro w hw
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [(hcomm k e₁).1, hna1, smul_zero]
        exact Submodule.zero_mem _
      have hLb : ∀ w ∈ L, nb w ∈ L := by
        intro w hw
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [(hcomm k e₁).2]
        show k • nb e₁ ∈ Submodule.span (Kalg na nb) {e₁}
        rw [← he₂, he2, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₁)
      rcases h.irr L hLa hLb with hbot | htop
      · have : e₁ ∈ L := Submodule.mem_span_singleton_self e₁
        rw [hbot] at this
        exact hL1 (by simpa using this)
      · apply h.ne_a
        ext w
        have hw : w ∈ L := by rw [htop]; trivial
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [(hcomm k e₁).1, hna1, smul_zero]
        simp
  have hsurj : Function.Surjective f := by
    let S : Submodule (ZMod p) W := (LinearMap.range f).restrictScalars (ZMod p)
    have hSa : ∀ w ∈ S, na w ∈ S := by
      rintro w ⟨⟨x, c⟩, rfl⟩
      exact ⟨(r * c, 0), (hfna x c).symm⟩
    have hSb : ∀ w ∈ S, nb w ∈ S := by
      rintro w ⟨⟨x, c⟩, rfl⟩
      exact ⟨(0, x), (hfnb x c).symm⟩
    rcases h.irr S hSa hSb with hbot | htop
    · exfalso
      have : e₁ ∈ S := ⟨(1, 0), by simp [hf]⟩
      rw [hbot] at this
      exact hL1 (by simpa using this)
    · intro w
      have : w ∈ S := by rw [htop]; trivial
      exact this
  let coord : W ≃ₗ[Kalg na nb] (Kalg na nb) × (Kalg na nb) :=
    (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm
  have hcoord : ∀ x c : Kalg na nb, coord.symm (x, c) = f (x, c) := fun x c => rfl
  have hr0 : r ≠ 0 := by
    intro hr0
    apply h.ne_a
    ext w
    obtain ⟨⟨x, c⟩, rfl⟩ := hsurj w
    rw [hfna, hr0, zero_mul]
    simp [hf]
  have hrint : IsIntegral (ZMod p) r := by
    have : Module.Finite (ZMod p) (Kalg na nb) := Module.Finite.of_finite
    exact Algebra.IsIntegral.isIntegral r
  have htop : Algebra.adjoin (ZMod p) ({r} : Set (Kalg na nb)) = ⊤ := by
    have := Algebra.adjoin_adjoin_coe_preimage (R := ZMod p) (A := Module.End (ZMod p) W)
      (s := {mu na nb})
    convert this using 2
    ext y
    simp [hr, Subtype.ext_iff]
  have hfinrank : Module.finrank (ZMod p) (Kalg na nb) = (minpoly (ZMod p) r).natDegree := by
    have := (PowerBasis.ofAdjoinEqTop hrint htop).finrank
    simpa [PowerBasis.ofAdjoinEqTop] using this
  have hcf : ∀ z, coord (f z) = z := fun z =>
    (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm_apply_apply z
  refine ⟨Kalg na nb, inferInstance, inferInstance, inferInstance, hKfin, coord, r, hr0,
    hfinrank, hcomm, ?_, ?_⟩
  · intro x c
    rw [hcoord, hfna]
    exact hcf _
  · intro x c
    rw [hcoord, hfnb]
    exact hcf _

end CFSG.GH74.GLS.Stage2.Signalizer.L53
