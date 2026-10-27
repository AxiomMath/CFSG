module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterFlag

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [Finite V]
variable {H : Type} [Group H] (F : ReflForm K V) (ρ : H →* Module.End K V)

omit [Finite K] [Finite V] in
theorem apply_pow_two_pow_eq [CharP K 2] {g : H} {e : ℕ} {v : V}
    (hv : ((ρ g - 1 : Module.End K V) ^ (2 ^ e)) v = 0) : ρ (g ^ (2 ^ e)) v = v := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Subsingleton.elim _ _
  have hinj : Function.Injective (algebraMap K (Module.End K V)) := by
    intro a b hab
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have := congrArg (fun f : Module.End K V => f w) hab
    simp only [Module.algebraMap_end_apply] at this
    exact smul_left_injective K hw this
  have : CharP (Module.End K V) 2 := charP_of_injective_algebraMap hinj 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := add_pow_char_pow_of_commute 2 e (Commute.one_right (ρ g - 1))
  rw [sub_add_cancel, one_pow] at h1
  rw [map_pow, h1, LinearMap.add_apply, hv, Module.End.one_apply, zero_add]

@[expose] def fixingSubgroup' (W : Submodule K V) : Subgroup H where
  carrier := {g | ∀ w ∈ W, ρ g w = w}
  one_mem' := fun w _ => by rw [map_one, Module.End.one_apply]
  mul_mem' := fun {a b} ha hb w hw => by
    rw [map_mul, Module.End.mul_apply, hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    have h := ha w hw
    calc ρ a⁻¹ w = ρ a⁻¹ (ρ a w) := by rw [h]
      _ = w := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]

omit [Finite K] in
theorem apply_eq_of_mem_isoSeq_of_perfect [CharP K 2] (hρ : IsIsometric F ρ) (R : Subgroup H)
    {X : Subgroup H} [Finite X] (hXp : Group.IsPerfect X)
    (hXN : X ≤ Subgroup.normalizer (R : Set H))
    (htriv : ∀ x ∈ X, ∀ k, ∀ v ∈ isoSeq F ρ R (k + 1), ρ x v - v ∈ isoSeq F ρ R k)
    {x : H} (hx : x ∈ X) {w : V} (hw : w ∈ isoSeq F ρ R (Module.finrank K V)) : ρ x w = w := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  set d := Module.finrank K V with hd
  set W := isoSeq F ρ R d with hW
  set T := fixingSubgroup' ρ W with hT
  obtain ⟨e, he⟩ : ∃ e : ℕ, d ≤ 2 ^ e := ⟨d, (Nat.lt_two_pow_self).le⟩
  have hpow : ∀ y ∈ X, y ^ (2 ^ e) ∈ T := by
    intro y hy u hu
    have hker : y ∈ flagKernel ρ (isoSeq F ρ R) := by
      refine ⟨fun k v hv => ⟨apply_mem_isoSeq F ρ hρ R k (hXN hy) hv,
        apply_mem_isoSeq F ρ hρ R k (hXN (inv_mem hy)) hv⟩, fun k v hv => htriv y hy k v hv⟩
    have hu' : u ∈ isoSeq F ρ R (0 + 2 ^ e) := by
      rw [zero_add, isoSeq_eq_of_le F ρ R he]
      exact hu
    have h1 := pow_sub_one_mem ρ hker (2 ^ e) 0 u hu'
    rw [isoSeq_zero, Submodule.mem_bot] at h1
    exact apply_pow_two_pow_eq ρ h1
  set N := T.subgroupOf X with hN
  have hNn : N.Normal := ⟨fun a ha b => by
    rw [hN, Subgroup.mem_subgroupOf] at ha ⊢
    intro u hu
    have hbu : ρ (b : H)⁻¹ u ∈ W := apply_mem_isoSeq F ρ hρ R d (hXN (inv_mem b.2)) hu
    change ρ ((b : H) * (a : H) * (b : H)⁻¹) u = u
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha _ hbu,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  have hQp : IsPGroup 2 (X ⧸ N) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    exact hpow y y.2
  have hQperf : Group.IsPerfect (X ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hsub : Subsingleton (X ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hQp.isNilpotent
  have hmem : (⟨x, hx⟩ : X) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  rw [hN, Subgroup.mem_subgroupOf] at hmem
  exact hmem w hw

omit [Finite K] [Finite V] in
theorem sub_mem_perp_of_fixes (hρ : IsIsometric F ρ) {W : Submodule K V} {x : H}
    (hx : ∀ w ∈ W, ρ x⁻¹ w = w) (v : V) : ρ x v - v ∈ F.perp W := by
  refine perp_sub_mem_of_sub_mem F ρ hρ (W := ⊥) (fun u hu => ?_) (by rw [F.perp_bot]; trivial)
  rw [hx u hu, sub_self]
  exact Submodule.zero_mem _

omit [Finite K] [Finite V] in
theorem apply_comm_of_triv [FiniteDimensional K V] (hρ : IsIsometric F ρ) {W : Submodule K V}
    {s x : H} (hs : ∀ a ∈ F.perp W, ρ s a = a) (hxW : ∀ w ∈ W, ρ x w = w)
    (hxA : ∀ v, ρ x v - v ∈ F.perp W) (v : V) : ρ x (ρ s v) = ρ s (ρ x v) := by
  have hsW : ρ s v - v ∈ W := by
    rw [← F.perp_perp W]
    intro a ha
    have h1 := hρ s a v
    rw [hs a ha] at h1
    rw [F.β_sub_right, h1, sub_self]
  have h1 : ρ x (ρ s v) = ρ x v + (ρ s v - v) := by
    rw [show ρ s v = v + (ρ s v - v) by abel, map_add, hxW _ hsW]
    abel
  have h2 : ρ s (ρ x v) = ρ s v + (ρ x v - v) := by
    rw [show ρ x v = v + (ρ x v - v) by abel, map_add, hs _ (hxA v)]
    abel
  rw [h1, h2]
  abel

open scoped commutatorElement in
theorem spBorelTitsCountInput_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
      [Finite V] (F : ReflForm K V) (H : Type) [Group H] [Finite H] (ρ : H →* Module.End K V),
      IsIsometric F ρ → Function.Injective ρ →
      ∀ R X : Subgroup H, IsPGroup 2 R → X ≤ Subgroup.normalizer (R : Set H) → Group.IsPerfect X →
        ⁅R, X⁆ = R → (∀ r ∈ R, (∀ x ∈ X, x * r = r * x) → r = 1) →
        (∀ x ∈ X, ∀ k, ∀ v ∈ isoSeq F ρ R (k + 1), ρ x v - v ∈ isoSeq F ρ R k) →
        Nat.card R ≤ Nat.card K ^ ((Module.finrank K V -
            2 * Module.finrank K (isoSeq F ρ R (Module.finrank K V))) *
          Module.finrank K (isoSeq F ρ R (Module.finrank K V))) := by
  intro K _ _ _ V _ _ _ F H _ _ ρ hρ hinj R X hR hXN hXp hRX hC htriv
  have : FiniteDimensional K V := Module.Finite.of_finite
  set d := Module.finrank K V with hd
  set W := isoSeq F ρ R d with hW
  set A := F.perp W with hA
  have hWA : W ≤ A := isoSeq_isTotallyIsotropic F ρ R d
  have hXW : ∀ x ∈ X, ∀ w ∈ W, ρ x w = w := fun x hx w hw =>
    apply_eq_of_mem_isoSeq_of_perfect F ρ hρ R hXp hXN htriv hx hw
  have hXA : ∀ x ∈ X, ∀ v, ρ x v - v ∈ A := fun x hx v =>
    sub_mem_perp_of_fixes F ρ hρ (fun w hw => hXW _ (inv_mem hx) w hw) v
  have hRW : ∀ r ∈ R, ∀ w ∈ W, ρ r w = w := by
    have hle : ⁅R, X⁆ ≤ fixingSubgroup' ρ W := by
      rw [Subgroup.commutator_le]
      intro r hr x hx w hw
      have hrw : ρ r⁻¹ w ∈ W := apply_mem_isoSeq F ρ hρ R d
        (Subgroup.le_normalizer (inv_mem hr)) hw
      change ρ (r * x * r⁻¹ * x⁻¹) w = w
      rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Module.End.mul_apply, hXW _ (inv_mem hx) w hw, hXW _ hx _ hrw, ← Module.End.mul_apply,
        ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    intro r hr w hw
    exact (hRX ▸ hle) hr w hw
  have hRA : ∀ r ∈ R, ∀ a ∈ A, ρ r a - a ∈ W := fun r hr a ha =>
    isoSeq_middle_triv F ρ 2 hρ R hR hr ha
  set W' : Submodule K A := W.comap A.subtype with hW'
  let Φ : R → ((A ⧸ W') →ₗ[K] W) := fun r =>
    W'.liftQ (LinearMap.codRestrict W ((ρ (r : H) - 1).comp A.subtype)
      (fun a => by simpa using hRA r r.2 a a.2))
      (fun a ha => by
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          LinearMap.sub_apply, Module.End.one_apply, ZeroMemClass.coe_zero]
        rw [hRW r r.2 a ha, sub_self])
  have hΦ : ∀ (r : R) (a : A), ((Φ r (Submodule.Quotient.mk a) : W) : V) = ρ (r : H) a - a := by
    intro r a
    simp [Φ]
  have hΦinj : Function.Injective Φ := by
    intro r r' hrr'
    have hra : ∀ a ∈ A, ρ (r : H) a = ρ (r' : H) a := by
      intro a ha
      have h1 := congrArg (fun φ => ((φ (Submodule.Quotient.mk ⟨a, ha⟩) : W) : V)) hrr'
      simp only [hΦ] at h1
      exact sub_left_injective h1
    obtain ⟨s, hs⟩ : ∃ s : H, s = (r' : H)⁻¹ * r := ⟨_, rfl⟩
    have hsR : s ∈ R := hs ▸ mul_mem (inv_mem r'.2) r.2
    have hsA : ∀ a ∈ A, ρ s a = a := by
      intro a ha
      rw [hs, map_mul, Module.End.mul_apply, hra a ha, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hs1 : s = 1 := hC s hsR fun x hx => hinj (LinearMap.ext fun v => by
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact apply_comm_of_triv F ρ hρ hsA (hXW x hx) (hXA x hx) v)
    apply Subtype.ext
    rw [hs] at hs1
    exact (inv_mul_eq_one.mp hs1).symm
  have : Finite ((A ⧸ W') →ₗ[K] W) := Module.finite_of_finite K
  have hcard := Nat.card_le_card_of_injective Φ hΦinj
  rw [Module.natCard_eq_pow_finrank (K := K) (V := (A ⧸ W') →ₗ[K] W),
    Module.finrank_linearMap K K] at hcard
  have hq1 := Submodule.finrank_quotient_add_finrank W'
  have hq2 : Module.finrank K W' = Module.finrank K W :=
    (Submodule.comapSubtypeEquivOfLe hWA).finrank_eq
  have hq3 : Module.finrank K A + Module.finrank K W = d := F.finrank_perp W
  have hq : Module.finrank K (A ⧸ W') = d - 2 * Module.finrank K W := by omega
  rw [hq] at hcard
  exact hcard

end CFSG.SeitzReduction.SymplecticPilot
