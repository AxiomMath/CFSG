module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Model

theorem card_units_F4 : Nat.card F4ˣ = 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_units, card_F4]

theorem pow_three_units (u : F4ˣ) : u ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.1 (by
    have h := orderOf_dvd_natCard u
    rwa [card_units_F4] at h)

@[expose] noncomputable def mulUnitEquiv (u : F4ˣ) : F4 ≃ₗ[ZMod 2] F4 :=
  LinearEquiv.ofLinear (LinearMap.mulLeft (ZMod 2) (u : F4))
    (LinearMap.mulLeft (ZMod 2) ((u⁻¹ : F4ˣ) : F4))
    (by
      apply LinearMap.ext
      intro x
      simp [LinearMap.mulLeft_apply, ← mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp [LinearMap.mulLeft_apply, ← mul_assoc])

theorem mulUnitEquiv_apply (u : F4ˣ) (x : F4) : mulUnitEquiv u x = (u : F4) * x := rfl

@[expose] noncomputable def blockAct (m ε : ℕ) (x : Fin m → F4ˣ) :
    ((Fin m → F4) × (Fin ε → ZMod 2)) ≃ₗ[ZMod 2] ((Fin m → F4) × (Fin ε → ZMod 2)) :=
  LinearEquiv.prodCongr (LinearEquiv.piCongrRight fun j => mulUnitEquiv (x j))
    (LinearEquiv.refl (ZMod 2) (Fin ε → ZMod 2))

theorem blockAct_mul (m ε : ℕ) (x y : Fin m → F4ˣ) :
    blockAct m ε (x * y) = blockAct m ε x * blockAct m ε y := by
  apply LinearEquiv.ext
  rintro ⟨v, c⟩
  simp only [blockAct, LinearEquiv.mul_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    LinearEquiv.piCongrRight_apply, Pi.mul_apply, Units.val_mul, mul_assoc, mulUnitEquiv_apply,
    Prod.map_apply, id_eq]
  refine Prod.ext (funext fun j => ?_) rfl
  simp [LinearEquiv.piCongrRight_apply, mulUnitEquiv_apply, mul_assoc]

@[expose] noncomputable def blockHom (m ε : ℕ) :
    (Fin m → F4ˣ) →* ((Fin m → F4) × (Fin ε → ZMod 2)) ≃ₗ[ZMod 2] ((Fin m → F4) × (Fin ε → ZMod 2)) :=
  MonoidHom.mk' (blockAct m ε) (blockAct_mul m ε)

theorem blockHom_injective (m ε : ℕ) : Function.Injective (blockHom m ε) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  funext j
  have h := congrArg (fun e : ((Fin m → F4) × (Fin ε → ZMod 2)) ≃ₗ[ZMod 2]
    ((Fin m → F4) × (Fin ε → ZMod 2)) => e ((fun _ => (1 : F4)), (fun _ => (0 : ZMod 2)))) hx
  have h1 := congrArg Prod.fst h
  have h2 := congrFun h1 j
  simp [blockHom, blockAct, LinearEquiv.piCongrRight_apply, mulUnitEquiv_apply] at h2
  exact h2

theorem card_range_blockHom (m ε : ℕ) : Nat.card (blockHom m ε).range = 3 ^ m := by
  rw [Nat.card_congr (MonoidHom.ofInjective (blockHom_injective m ε)).toEquiv.symm, Nat.card_pi,
    card_units_F4]
  simp

theorem isElemAbelian_range_blockHom (m ε : ℕ) : IsElemAbelian 3 (blockHom m ε).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro a ha
    obtain ⟨x, rfl⟩ := ha
    rw [← map_pow]
    have : x ^ 3 = 1 := funext fun j => pow_three_units (x j)
    rw [this, map_one]

theorem isElemAbelian_map' {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (hK : IsElemAbelian 3 K) : IsElemAbelian 3 (K.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hK.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow, hK.2 x hx, map_one]

@[expose] noncomputable def conjHom {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (e : V ≃ₗ[ZMod 2] W) :
    (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V) :=
  MonoidHom.mk' (fun g => e.trans (g.trans e.symm)) (fun g h => by
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply])

theorem conjHom_injective {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (e : V ≃ₗ[ZMod 2] W) : Function.Injective (conjHom e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply LinearEquiv.ext
  intro w
  have h1 : (conjHom e g) (e.symm w) = e.symm w := by rw [hg]; rfl
  have h2 : e.symm (g w) = e.symm w := by
    have := h1
    simpa [conjHom] using this
  show g w = w
  exact e.symm.injective h2

theorem finrank_block (m ε : ℕ) :
    Module.finrank (ZMod 2) ((Fin m → F4) × (Fin ε → ZMod 2)) = 2 * m + ε := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fin_fun]
  simp [finrank_F4]
  ring

theorem exists_elemAb_card (V : Type) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (N : ℕ) (hV : Module.finrank (ZMod 2) V = N) :
    ∃ E0 : Subgroup (V ≃ₗ[ZMod 2] V), IsElemAbelian 3 E0 ∧ Nat.card E0 = 3 ^ (N / 2) := by
  have hfin : Module.finrank (ZMod 2) ((Fin (N / 2) → F4) × (Fin (N % 2) → ZMod 2)) = N := by
    rw [finrank_block]
    omega
  let e : V ≃ₗ[ZMod 2] ((Fin (N / 2) → F4) × (Fin (N % 2) → ZMod 2)) :=
    LinearEquiv.ofFinrankEq V _ (by rw [hV, hfin])
  refine ⟨(blockHom (N / 2) (N % 2)).range.map (conjHom e), ?_, ?_⟩
  · exact isElemAbelian_map' _ (isElemAbelian_range_blockHom _ _)
  · rw [Subgroup.card_map_of_injective (conjHom_injective e), card_range_blockHom]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std

end
