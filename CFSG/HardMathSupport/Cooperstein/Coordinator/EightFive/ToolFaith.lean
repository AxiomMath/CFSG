module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {m : ℕ}

theorem eq_bot_or_alternatingGroup_le (hm : 5 ≤ m) {N : Subgroup (Perm (Fin m))}
    (hN : ∀ g ∈ alternatingGroup (Fin m), ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    N = ⊥ ∨ alternatingGroup (Fin m) ≤ N := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hnorm : (N.subgroupOf (alternatingGroup (Fin m))).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.2 (hN g g.2 x (Subgroup.mem_subgroupOf.1 hx))⟩
  rcases hnorm.eq_bot_or_eq_top with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine eq_one_of_commute_alt (by omega) fun σ hσ => ?_
    have hc : x * σ * x⁻¹ * σ⁻¹ ∈ N := by
      have h1 := N.mul_mem hx (hN σ hσ x⁻¹ (N.inv_mem hx))
      rwa [← mul_assoc, ← mul_assoc] at h1
    have hcA : x * σ * x⁻¹ * σ⁻¹ ∈ alternatingGroup (Fin m) :=
      (alternatingGroup (Fin m)).mul_mem (alternatingGroup.normal.conj_mem σ hσ x)
        ((alternatingGroup (Fin m)).inv_mem hσ)
    have h2 : (⟨_, hcA⟩ : alternatingGroup (Fin m)) ∈ N.subgroupOf (alternatingGroup (Fin m)) :=
      Subgroup.mem_subgroupOf.2 hc
    rw [h, Subgroup.mem_bot] at h2
    have h3 : x * σ * x⁻¹ * σ⁻¹ = 1 := congrArg Subtype.val h2
    calc x * σ = x * σ * x⁻¹ * σ⁻¹ * (σ * x) := by group
      _ = σ * x := by rw [h3, one_mul]
  · right
    intro σ hσ
    have h1 : (⟨σ, hσ⟩ : alternatingGroup (Fin m)) ∈ N.subgroupOf (alternatingGroup (Fin m)) :=
      h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1

variable {V : Type} [CommGroup V]

section AutSub

variable {K : Subgroup (MulAut V)} {W : Subgroup V}

@[expose] def autSubHom (hKW : K ≤ stabSub W) : ↥K →* ↥(autSub K W) :=
  ((resHom W).comp (Subgroup.inclusion hKW)).codRestrict (autSub K W) fun k =>
    mem_autSub.2 ⟨Subgroup.inclusion hKW k, k.2, rfl⟩

theorem coe_autSubHom_apply (hKW : K ≤ stabSub W) (k : ↥K) (w : ↥W) :
    (((autSubHom hKW k : MulAut ↥W) w : ↥W) : V) = (k : MulAut V) w :=
  rfl

theorem autSubHom_surjective (hKW : K ≤ stabSub W) : Function.Surjective (autSubHom hKW) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
  exact ⟨⟨g, hg⟩, rfl⟩

theorem autSubHom_eq_one_iff (hKW : K ≤ stabSub W) (k : ↥K) :
    autSubHom hKW k = 1 ↔ ∀ w ∈ W, (k : MulAut V) w = w := by
  constructor
  · intro h w hw
    have := congrArg (fun φ : ↥(autSub K W) => (((φ : MulAut ↥W) ⟨w, hw⟩ : ↥W) : V)) h
    exact this
  · intro h
    refine Subtype.ext (MulEquiv.ext fun w => Subtype.ext ?_)
    exact h w w.2

@[expose] noncomputable def autSubLift (κ : ↥K →* Perm (Fin m)) (hKW : K ≤ stabSub W)
    (hC : ∀ k : ↥K, (∀ w ∈ W, (k : MulAut V) w = w) → κ k = 1) :
    ↥(autSub K W) →* Perm (Fin m) :=
  (autSubHom hKW).liftOfSurjective (autSubHom_surjective hKW)
    ⟨κ, fun k hk => (MonoidHom.mem_ker).2 (hC k ((autSubHom_eq_one_iff hKW k).1
      ((MonoidHom.mem_ker).1 hk)))⟩

variable {κ : ↥K →* Perm (Fin m)} {hKW : K ≤ stabSub W}
  {hC : ∀ k : ↥K, (∀ w ∈ W, (k : MulAut V) w = w) → κ k = 1}

theorem autSubLift_apply (k : ↥K) : autSubLift κ hKW hC (autSubHom hKW k) = κ k :=
  (autSubHom hKW).liftOfRightInverse_comp_apply _ _ _ k

theorem range_autSubLift : (autSubLift κ hKW hC).range = κ.range := by
  ext σ
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨k, rfl⟩ := autSubHom_surjective hKW φ
    exact ⟨k, (autSubLift_apply k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨autSubHom hKW k, autSubLift_apply k⟩

theorem autSubLift_injective (h : ∀ k : ↥K, κ k = 1 → ∀ w ∈ W, (k : MulAut V) w = w) :
    Function.Injective (autSubLift κ hKW hC) := by
  refine (injective_iff_map_eq_one _).2 fun φ hφ => ?_
  obtain ⟨k, rfl⟩ := autSubHom_surjective hKW φ
  rw [autSubLift_apply] at hφ
  exact (autSubHom_eq_one_iff hKW k).2 (h k hφ)

end AutSub

theorem eq_one_of_commute_of_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {Q : Subgroup (MulAut V)} (hQ : IsPGroup 2 Q) {x : MulAut V} (hx : Odd (orderOf x))
    (hcomm : ∀ q ∈ Q, x * q = q * x) (hfix : ∀ v ∈ fixV Q, x v = v) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have hVp : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one, hV]⟩
  have hB : IsPGroup 2 (Q.map (MonoidHom.id (MulAut V))) := by
    rw [Subgroup.map_id]
    exact hQ
  exact thompson_AxB_element hVp (MonoidHom.id _) hB (Nat.coprime_two_right.2 hx)
    (fun q hq => hcomm q hq) (fun v hv => hfix v hv)

theorem faithW [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hm : 5 ≤ m) {K Q : Subgroup (MulAut V)}
    (κ : ↥K →* Perm (Fin m)) (hκ : alternatingGroup (Fin m) ≤ κ.range) (hQ : IsPGroup 2 Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set (MulAut V)))
    (hker : ∀ k : ↥K, κ k = 1 → ∀ w ∈ fixV Q, (k : MulAut V) w = w) (x : ↥K)
    (hxo : Odd (orderOf (x : MulAut V))) (hx1 : (x : MulAut V) ≠ 1)
    (hxA : κ x ∈ alternatingGroup (Fin m)) (hxQ : ∀ q ∈ Q, (x : MulAut V) * q = q * x) :
    ∀ k : ↥K, (∀ w ∈ fixV Q, (k : MulAut V) w = w) → κ k = 1 := by
  have hKW := le_stabSub_fixV hKQ
  set C : Subgroup ↥K := (centSub (fixV Q)).subgroupOf K with hC
  have hmemC : ∀ k : ↥K, k ∈ C ↔ ∀ w ∈ fixV Q, (k : MulAut V) w = w := fun k =>
    Subgroup.mem_subgroupOf.trans mem_centSub
  have hN : ∀ g ∈ alternatingGroup (Fin m), ∀ y ∈ C.map κ, g * y * g⁻¹ ∈ C.map κ := by
    rintro g hg _ ⟨c, hc, rfl⟩
    obtain ⟨k, rfl⟩ := hκ hg
    refine ⟨k * c * k⁻¹, (hmemC _).2 fun w hw => ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hw' : (k⁻¹ : ↥K) • w ∈ fixV Q := ((hKW (K.inv_mem k.2)) w).2 hw
    have h1 := (hmemC c).1 hc _ hw'
    change (k : MulAut V) ((c : MulAut V) ((k : MulAut V)⁻¹ w)) = w
    change (c : MulAut V) ((k : MulAut V)⁻¹ w) = (k : MulAut V)⁻¹ w at h1
    rw [h1, MulAut.apply_inv_self]
  rcases eq_bot_or_alternatingGroup_le hm hN with h | h
  · intro k hk
    have : κ k ∈ C.map κ := ⟨k, (hmemC k).2 hk, rfl⟩
    rwa [h, Subgroup.mem_bot] at this
  · exfalso
    obtain ⟨c, hc, hcx⟩ := h hxA
    have hxc : κ (x * c⁻¹) = 1 := by rw [map_mul, map_inv, hcx, mul_inv_cancel]
    have hfix : ∀ v ∈ fixV Q, (x : MulAut V) v = v := by
      intro v hv
      have h1 := hker _ hxc v hv
      have h2 := (hmemC c).1 hc v hv
      have h3 : ((x * c⁻¹ : ↥K) : MulAut V) v = (x : MulAut V) ((c : MulAut V)⁻¹ v) := rfl
      have h4 : (c : MulAut V)⁻¹ v = v := by
        rw [← h2, MulAut.inv_apply_self, h2]
      rw [h3, h4] at h1
      exact h1
    exact hx1 (eq_one_of_commute_of_fixV hV hQ hxo hxQ hfix)

theorem isFFStarOffender_autSub [Finite V] {X A K : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) {W : Subgroup V} (hW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hWA : commSub W A ≠ ⊥) (hAK : autSub A W ≤ autSub K W) :
    IsFFStarOffender (autSub K W) (autSub A W) :=
  ⟨hAK, (B7_1_1 hA hW hWA).2⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
