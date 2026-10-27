module

public import CFSG.ClassicalInvolution.Phan.PhanQ49ThmS

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section ConjSub

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

@[expose] def conjSub (S : Submodule K (V8 K)) : Submodule K (V8 K) where
  carrier := {v | conj D v ∈ S}
  add_mem' := fun {a b} ha hb => by
    show conj D (a + b) ∈ S
    rw [conj_add]
    exact S.add_mem ha hb
  zero_mem' := by
    show conj D 0 ∈ S
    have : conj D (0 : V8 K) = 0 := by ext i; simp [conj]
    rw [this]
    exact S.zero_mem
  smul_mem' := fun c {v} hv => by
    show conj D (c • v) ∈ S
    rw [conj_smul]
    exact S.smul_mem _ hv

theorem mem_conjSub {S : Submodule K (V8 K)} {v : V8 K} : v ∈ conjSub D S ↔ conj D v ∈ S :=
  Iff.rfl

theorem finrank_conjSub (S : Submodule K (V8 K)) :
    Module.finrank K (conjSub D S) = Module.finrank K S := by
  let j : ↥(conjSub D S) ≃+ ↥S :=
    { toFun := fun v => ⟨conj D v.1, v.2⟩
      invFun := fun w => ⟨conj D w.1, by rw [mem_conjSub, conj_conj]; exact w.2⟩
      left_inv := fun v => Subtype.ext (conj_conj D v.1)
      right_inv := fun w => Subtype.ext (conj_conj D w.1)
      map_add' := fun a b => Subtype.ext (conj_add D a.1 b.1) }
  have hi : Function.Bijective D.τ :=
    ⟨fun a b h => by simpa [D.tau_tau] using congrArg D.τ h,
      fun b => ⟨D.τ b, D.tau_tau b⟩⟩
  have hr := rank_eq_of_equiv_equiv D.τ j hi (fun r m => Subtype.ext (conj_smul D r m.1))
  unfold Module.finrank
  rw [hr]

end ConjSub

section GK

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem conj_extV (x : V8 F) : conj D (extV K x) = extV K x := by
  ext i
  simp [conj, extV, D.tau_alg]

theorem gK_conj (g : spinGroup (quadPlus 4 F)) (v : V8 K) :
    conj D (gK K g v) = gK K g (conj D v) := by
  ext i
  simp only [gK, extLin_apply, conj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : D.τ (extV K ((spinAction (quadPlus 4 F) g).toLinearMap (Pi.single j 1)) i) =
      extV K ((spinAction (quadPlus 4 F) g).toLinearMap (Pi.single j 1)) i := by
    have := congrFun (conj_extV D ((spinAction (quadPlus 4 F) g).toLinearMap (Pi.single j 1))) i
    simpa [conj] using this
  rw [this]

theorem gK_B (g : spinGroup (quadPlus 4 F)) (u v : V8 K) :
    B8 (gK K g u) (gK K g v) = B8 u v :=
  B8_extLin K _ (fun x y => by
    show B8 (spinAction (quadPlus 4 F) g x) (spinAction (quadPlus 4 F) g y) = B8 x y
    simp only [B8, polar_spinAction]) u v

theorem gK_injective (g : spinGroup (quadPlus 4 F)) : Function.Injective (gK K g) := by
  intro u v h
  have := congrArg (gK K g⁻¹) h
  rwa [gK_gK_inv, gK_gK_inv] at this

theorem gK_inv_gK (g : spinGroup (quadPlus 4 F)) (v : V8 K) : gK K g (gK K g⁻¹ v) = v := by
  have := gK_gK_inv (K := K) g⁻¹ v
  rwa [inv_inv] at this

theorem PhanSolid.map_gK {W : Submodule K (V8 K)} (hW : PhanSolid D W)
    (g : spinGroup (quadPlus 4 F)) : PhanSolid D (W.map (gK K g)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [gK_B]
    exact hW.ts u hu v hv
  · rintro v ⟨w, hw, rfl⟩ ⟨w', hw', hw''⟩
    have h1 : w' = conj D w := gK_injective g (by rw [hw'', gK_conj])
    rw [h1] at hw'
    rw [hW.inf w hw hw', map_zero]
  · intro v
    obtain ⟨w₁, hw₁, w₂, hw₂, hv⟩ := hW.sup (gK K g⁻¹ v)
    refine ⟨gK K g w₁, ⟨w₁, hw₁, rfl⟩, gK K g w₂, ⟨w₂, hw₂, rfl⟩, ?_⟩
    rw [gK_conj, ← map_add, ← hv, gK_inv_gK]

end GK

end CFSG.ClassicalInvolution.PhanQ
