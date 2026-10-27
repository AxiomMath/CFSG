module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Rank

public section

namespace CFSG.QuasithinUnique.Setup.X7

section Fixed

variable {G k V : Type*} [Group G] [Field k] [AddCommMonoid V] [Module k V]

theorem fixedSub_map_conj (ρ : Representation k G V) (n : G) (P : Subgroup G) :
    fixedSub ρ (P.map (MulAut.conj n).toMonoidHom) = (fixedSub ρ P).map (ρ n) := by
  ext w
  constructor
  · intro hw
    refine ⟨ρ n⁻¹ w, fun u hu => ?_, ?_⟩
    · have h := hw (n * u * n⁻¹) ⟨u, hu, by simp [MulAut.conj_apply]⟩
      calc ρ u (ρ n⁻¹ w) = ρ n⁻¹ (ρ (n * u * n⁻¹) w) := by
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
            congr 2
            group
        _ = ρ n⁻¹ w := by rw [h]
    · show ρ n (ρ n⁻¹ w) = w
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rintro ⟨v, hv, rfl⟩ _ ⟨u, hu, rfl⟩
    change ρ (n * u * n⁻¹) (ρ n v) = ρ n v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
      hv u hu]

theorem mem_fixedSub_map_conj (ρ : Representation k G V) (n : G) (P : Subgroup G) {w : V} :
    w ∈ fixedSub ρ (P.map (MulAut.conj n).toMonoidHom) ↔ ρ n⁻¹ w ∈ fixedSub ρ P := by
  rw [fixedSub_map_conj, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h : ρ n⁻¹ (ρ n v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [h]
  · intro hw
    exact ⟨ρ n⁻¹ w, hw, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩

theorem natCard_fixedSub_map_conj (ρ : Representation k G V) (n : G) (P : Subgroup G) :
    Nat.card (fixedSub ρ (P.map (MulAut.conj n).toMonoidHom)) =
      Nat.card (fixedSub ρ P) := by
  rw [fixedSub_map_conj]
  have hinj : Function.Injective (ρ n : V →ₗ[k] V) := by
    refine LinearMap.injective_of_comp_eq_id (ρ n) (ρ n⁻¹) ?_
    ext v
    rw [LinearMap.comp_apply, LinearMap.id_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one]
    rfl
  exact (Nat.card_congr
    (Submodule.equivMapOfInjective (ρ n) hinj (fixedSub ρ P)).toEquiv).symm

theorem mem_fixedSub_zpowers (ρ : Representation k G V) (x : G) (w : V) :
    w ∈ fixedSub ρ (Subgroup.zpowers x) ↔ ρ x w = w := by
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h
    have hg_inv : ρ x⁻¹ w = w := by
      have hleft : Function.LeftInverse (ρ (x⁻¹)) (ρ x) := fun y => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      apply hleft.injective
      have hright : ρ x (ρ (x⁻¹) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply]
      rw [hright, h]
    refine mem_fixedSub.mpr fun y hy => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine zpow_induction_right (g := x) (P := fun y => ρ y w = w) ?_ ?_ ?_ n
    · simp
    · intro a ha
      rw [map_mul, Module.End.mul_apply, h, ha]
    · intro a ha
      rw [map_mul, Module.End.mul_apply, hg_inv, ha]

theorem fixedSub_inf_eq_map_conj_iff (ρ : Representation k G V) (n : G)
    (U V' W : Subgroup G) :
    (fixedSub ρ U ⊓ fixedSub ρ V' = fixedSub ρ W) ↔
      (fixedSub ρ (U.map (MulAut.conj n).toMonoidHom) ⊓
          fixedSub ρ (V'.map (MulAut.conj n).toMonoidHom) =
        fixedSub ρ (W.map (MulAut.conj n).toMonoidHom)) := by
  have hinj : Function.Injective (ρ n : V →ₗ[k] V) := by
    refine LinearMap.injective_of_comp_eq_id (ρ n) (ρ n⁻¹) ?_
    ext v
    rw [LinearMap.comp_apply, LinearMap.id_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one]
    rfl
  have hU : fixedSub ρ (U.map (MulAut.conj n).toMonoidHom) =
      (fixedSub ρ U).map (ρ n) := fixedSub_map_conj ρ n U
  have hV : fixedSub ρ (V'.map (MulAut.conj n).toMonoidHom) =
      (fixedSub ρ V').map (ρ n) := fixedSub_map_conj ρ n V'
  have hW : fixedSub ρ (W.map (MulAut.conj n).toMonoidHom) =
      (fixedSub ρ W).map (ρ n) := fixedSub_map_conj ρ n W
  constructor
  · intro h
    refine le_antisymm ?_ ?_
    · intro a ha
      have haU : a ∈ (fixedSub ρ U).map (ρ n) := by
        have := ha.1
        rwa [hU] at this
      have haV : a ∈ (fixedSub ρ V').map (ρ n) := by
        have := ha.2
        rwa [hV] at this
      obtain ⟨u, hu, rfl⟩ := haU
      obtain ⟨v, hv, hv_eq⟩ := haV
      have huv : u = v := hinj (by rw [hv_eq])
      subst huv
      rw [hW]
      exact ⟨u, h ▸ ⟨hu, hv⟩, rfl⟩
    · intro a ha
      have haW : a ∈ (fixedSub ρ W).map (ρ n) := by
        rwa [hW] at ha
      obtain ⟨w, hw, rfl⟩ := haW
      have hwP : w ∈ fixedSub ρ U ⊓ fixedSub ρ V' := by
        rwa [← h] at hw
      rw [hU, hV]
      exact ⟨⟨w, hwP.1, rfl⟩, ⟨w, hwP.2, rfl⟩⟩
  · intro h
    refine le_antisymm ?_ ?_
    · intro u hu
      have hmu : ρ n u ∈ fixedSub ρ (U.map (MulAut.conj n).toMonoidHom) ⊓
          fixedSub ρ (V'.map (MulAut.conj n).toMonoidHom) := by
        rw [hU, hV]
        exact ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩
      rw [h] at hmu
      rw [hW] at hmu
      obtain ⟨w, hw, hw_eq⟩ := hmu
      have : w = u := hinj (by rw [hw_eq])
      subst this
      exact hw
    · intro w hw
      have hmwR : ρ n w ∈ fixedSub ρ (W.map (MulAut.conj n).toMonoidHom) := by
        rw [hW]
        exact ⟨w, hw, rfl⟩
      have hmw : ρ n w ∈ fixedSub ρ (U.map (MulAut.conj n).toMonoidHom) ⊓
          fixedSub ρ (V'.map (MulAut.conj n).toMonoidHom) := by
        rwa [← h] at hmwR
      rw [hU, hV] at hmw
      obtain ⟨u, hu, hu_eq⟩ := hmw.1
      obtain ⟨v, hv, hv_eq⟩ := hmw.2
      have huw : u = w := hinj (by rw [hu_eq])
      have hvw : v = w := hinj (by rw [hv_eq])
      exact ⟨by simpa [← huw] using hu, by simpa [← hvw] using hv⟩

end Fixed

section Cyclic

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]

theorem fixedSub_zpowers (ρ : Representation k G V) (x : G) :
    fixedSub ρ (Subgroup.zpowers x) = LinearMap.ker (ρ x - 1) := by
  ext w
  rw [mem_fixedSub_zpowers, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]

end Cyclic

section Operators

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]

theorem conj_mul_sub (ρ : Representation k G V) (n p : G) :
    ρ n * (ρ p - 1) = (ρ (n * p * n⁻¹) - 1) * ρ n := by
  have h1 : ρ (n⁻¹) * ρ n = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc ρ n * (ρ p - 1) = ρ n * ρ p - ρ n := by rw [mul_sub, mul_one]
    _ = (ρ n * ρ p) * (ρ (n⁻¹) * ρ n) - ρ n := by rw [h1, mul_one]
    _ = (ρ n * ρ p * ρ (n⁻¹)) * ρ n - ρ n := by group
    _ = (ρ (n * p * n⁻¹) - 1) * ρ n := by
          rw [sub_mul, one_mul, map_mul, map_mul]

theorem conj_apply_sub (ρ : Representation k G V) (n p : G) (v : V) :
    ρ n ((ρ p - 1) v) = (ρ (n * p * n⁻¹) - 1) (ρ n v) := by
  have h := congrArg (fun f : Module.End k V => f v) (conj_mul_sub ρ n p)
  simpa [Module.End.mul_apply] using h

theorem map_sub_image_conj (ρ : Representation k G V) (c x : G) (U : Submodule k V) :
    (U.map (ρ x - 1)).map (ρ c) = (U.map (ρ c)).map (ρ (c * x * c⁻¹) - 1) := by
  ext w
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨ρ c v, Submodule.mem_map_of_mem hv, ?_⟩
    have h := congrArg (fun f : Module.End k V => f v) (conj_mul_sub ρ c x)
    simpa [Module.End.mul_apply] using h
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨(ρ x - 1) u, ⟨u, hu, rfl⟩, ?_⟩
    have h := congrArg (fun f : Module.End k V => f u) (conj_mul_sub ρ c x)
    simpa [Module.End.mul_apply] using h.symm

end Operators

section Commutator

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem commSub_induction (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    {P : V → Prop} (hgen : ∀ a ∈ A, ∀ v, P ((ρ a - 1) v)) (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) {w : V} (hw : w ∈ commSub ρ A) : P w := by
  rw [commSub, iSup_subtype'] at hw
  refine Submodule.iSup_induction (fun a : A => LinearMap.range (ρ (a : G) - 1))
    (motive := P) hw ?_ hzero hadd
  intro a wa hwa
  obtain ⟨v, rfl⟩ := hwa
  exact hgen a a.2 v

theorem commSub_map_conj (ρ : Representation (ZMod 2) G V) (n : G) (P : Subgroup G) :
    commSub ρ (P.map (MulAut.conj n).toMonoidHom) = (commSub ρ P).map (ρ n) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    have hmem : ρ (n⁻¹) w ∈ commSub ρ P := by
      refine commSub_induction ρ (P.map (MulAut.conj n).toMonoidHom)
        (P := fun x => ρ (n⁻¹) x ∈ commSub ρ P) ?_ ?_ ?_ hw
      · rintro a ⟨p, hp, rfl⟩ v
        have hconj : (MulAut.conj n).toMonoidHom p = n * p * n⁻¹ := rfl
        rw [hconj]
        have h1 : ρ (n⁻¹) ((ρ (n * p * n⁻¹) - 1) v) =
            (ρ p - 1) (ρ (n⁻¹) v) := by
          have h := congrArg (fun f : Module.End (ZMod 2) V => f v)
            (conj_mul_sub ρ n⁻¹ (n * p * n⁻¹))
          simpa [Module.End.mul_apply, mul_assoc] using h
        rw [h1]
        exact range_le_commSub hp ⟨ρ (n⁻¹) v, rfl⟩
      · simp
      · intro x y hx hy
        rw [map_add]
        exact (commSub ρ P).add_mem hx hy
    rw [Submodule.mem_map]
    exact ⟨ρ (n⁻¹) w, hmem, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  · rintro w ⟨u, hu, rfl⟩
    refine commSub_induction ρ P
      (P := fun x => ρ n x ∈ commSub ρ (P.map (MulAut.conj n).toMonoidHom)) ?_ ?_ ?_ hu
    · intro p hp v
      have e : ρ n ((ρ p - 1) v) = (ρ (n * p * n⁻¹) - 1) (ρ n v) := by
        have h := congrArg (fun f : Module.End (ZMod 2) V => f v)
          (conj_mul_sub ρ n p)
        simpa [Module.End.mul_apply] using h
      rw [e]
      exact range_le_commSub (Subgroup.mem_map_of_mem _ hp) ⟨ρ n v, rfl⟩
    · simp
    · intro x y hx hy
      rw [map_add]
      exact (commSub ρ (P.map (MulAut.conj n).toMonoidHom)).add_mem hx hy

theorem natCard_commSub_map_conj (ρ : Representation (ZMod 2) G V) (n : G) (P : Subgroup G) :
    Nat.card (commSub ρ (P.map (MulAut.conj n).toMonoidHom)) =
      Nat.card (commSub ρ P) := by
  rw [commSub_map_conj]
  have hinj : Function.Injective (ρ n : V →ₗ[ZMod 2] V) := by
    refine LinearMap.injective_of_comp_eq_id (ρ n) (ρ n⁻¹) ?_
    ext v
    rw [LinearMap.comp_apply, LinearMap.id_apply, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one]
    rfl
  exact (Nat.card_congr
    (Submodule.equivMapOfInjective (ρ n) hinj (commSub ρ P)).toEquiv).symm

end Commutator

end CFSG.QuasithinUnique.Setup.X7

end
