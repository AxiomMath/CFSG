module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate1

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Dictionary

variable {H : Type*} [Group H] {V : Subgroup H} [V.Normal] {Wm : Type*} [AddCommGroup Wm]
  [Module (ZMod 2) Wm] (θ : ↥V ≃* Multiplicative Wm)

theorem modelRho_conj_mem (x : H) {w : H} (hw : w ∈ V) :
    x * w * x⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem w hw x

theorem modelRho_apply' (x : H) {w : H} (hw : w ∈ V) :
    modelRho θ x (Multiplicative.toAdd (θ ⟨w, hw⟩)) =
      Multiplicative.toAdd (θ ⟨x * w * x⁻¹, modelRho_conj_mem x hw⟩) := by
  rw [modelRho_apply]
  exact congrArg (fun v : ↥V => Multiplicative.toAdd (θ v))
    (Subtype.ext (MulAut.conjNormal_apply x ⟨w, hw⟩))

theorem modelSub_normal {U : Submodule (ZMod 2) Wm}
    (hU : ∀ x : H, ∀ u ∈ U, modelRho θ x u ∈ U) : (modelSub (H := H) θ U).Normal := by
  refine ⟨fun w hw x => ?_⟩
  obtain ⟨hwV, hwU⟩ := mem_modelSub.1 hw
  refine mem_modelSub.2 ⟨modelRho_conj_mem x hwV, ?_⟩
  rw [← modelRho_apply' θ x hwV]
  exact hU x _ hwU

theorem map_conj_modelSub {U U' Wl : Submodule (ZMod 2) Wm} (hUW : U ≤ Wl) (hUW' : U' ≤ Wl)
    (hWl : ∀ x : H, ∀ w ∈ Wl, modelRho θ x w ∈ Wl) (x : H)
    (hiff : ∀ w ∈ Wl, modelRho θ x w ∈ U' ↔ w ∈ U) :
    (modelSub (H := H) θ U).map (MulAut.conj x).toMonoidHom = modelSub θ U' := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzV, hzU⟩ := mem_modelSub.1 hz
    show x * z * x⁻¹ ∈ modelSub θ U'
    refine mem_modelSub.2 ⟨modelRho_conj_mem x hzV, ?_⟩
    rw [← modelRho_apply' θ x hzV]
    exact (hiff _ (hUW hzU)).2 hzU
  · intro hy
    obtain ⟨hyV, hyU'⟩ := mem_modelSub.1 hy
    have hz : x⁻¹ * y * x ∈ V := by
      simpa using modelRho_conj_mem x⁻¹ hyV
    refine ⟨x⁻¹ * y * x, mem_modelSub.2 ⟨hz, ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 : modelRho θ x⁻¹ (Multiplicative.toAdd (θ ⟨y, hyV⟩)) =
        Multiplicative.toAdd (θ ⟨x⁻¹ * y * x⁻¹⁻¹, modelRho_conj_mem x⁻¹ hyV⟩) :=
      modelRho_apply' θ x⁻¹ hyV
    have h2 : (⟨x⁻¹ * y * x⁻¹⁻¹, modelRho_conj_mem x⁻¹ hyV⟩ : ↥V) = ⟨x⁻¹ * y * x, hz⟩ :=
      Subtype.ext (by simp)
    rw [h2] at h1
    rw [← h1]
    have hw : modelRho θ x⁻¹ (Multiplicative.toAdd (θ ⟨y, hyV⟩)) ∈ Wl :=
      hWl x⁻¹ _ (hUW' hyU')
    exact (hiff _ hw).1 (by rw [Offender.ρ_apply_inv]; exact hyU')

omit [V.Normal] in
theorem mem_modelSub_symm (U : Submodule (ZMod 2) Wm) (u : Wm) :
    ((θ.symm (Multiplicative.ofAdd u) : ↥V) : H) ∈ modelSub (H := H) θ U ↔ u ∈ U := by
  rw [mem_modelSub]
  constructor
  · rintro ⟨hx, h⟩
    simpa using h
  · intro hu
    exact ⟨(θ.symm _).2, by simpa using hu⟩

theorem rho_mem_iff_of_map_conj {U : Submodule (ZMod 2) Wm} {x : H}
    (hx : (modelSub (H := H) θ U).map (MulAut.conj x).toMonoidHom = modelSub θ U) (u : Wm) :
    modelRho θ x u ∈ U ↔ u ∈ U := by
  set v : ↥V := θ.symm (Multiplicative.ofAdd u) with hv
  have hu : u = Multiplicative.toAdd (θ v) := by simp [hv]
  have h1 : modelRho θ x u = Multiplicative.toAdd (θ ⟨x * (v : H) * x⁻¹,
      modelRho_conj_mem x v.2⟩) := by
    rw [hu]
    exact modelRho_apply' θ x v.2
  have h2 : modelRho θ x u = Multiplicative.toAdd (Multiplicative.ofAdd (modelRho θ x u)) := rfl
  have h3 : θ.symm (Multiplicative.ofAdd (modelRho θ x u)) =
      ⟨x * (v : H) * x⁻¹, modelRho_conj_mem x v.2⟩ := by
    rw [h1]
    simp
  rw [← mem_modelSub_symm θ U (modelRho θ x u), ← mem_modelSub_symm θ U u, h3]
  show x * (v : H) * x⁻¹ ∈ modelSub θ U ↔ (v : H) ∈ modelSub θ U
  conv_lhs => rw [← hx]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective

@[expose] def modelSubToLin (U : Submodule (ZMod 2) Wm) (x : ↥(modelSub (H := H) θ U)) : ↥U :=
  ⟨Multiplicative.toAdd (θ ⟨x.1, (mem_modelSub.1 x.2).1⟩), (mem_modelSub.1 x.2).2⟩

@[expose] def modelSubOfLin (U : Submodule (ZMod 2) Wm) (u : ↥U) : ↥(modelSub (H := H) θ U) :=
  ⟨((θ.symm (Multiplicative.ofAdd (u : Wm)) : ↥V) : H),
    mem_modelSub.2 ⟨(θ.symm _).2, by
      show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd (u : Wm)))) ∈ U
      rw [θ.apply_symm_apply]
      exact u.2⟩⟩

omit [V.Normal] in
theorem modelSubOfLin_toLin (U : Submodule (ZMod 2) Wm) (x : ↥(modelSub (H := H) θ U)) :
    modelSubOfLin θ U (modelSubToLin θ U x) = x := by
  apply Subtype.ext
  show ((θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (θ ⟨x.1, _⟩))) : ↥V) : H) = x.1
  simp

omit [V.Normal] in
theorem modelSubToLin_ofLin (U : Submodule (ZMod 2) Wm) (u : ↥U) :
    modelSubToLin θ U (modelSubOfLin (H := H) θ U u) = u := by
  apply Subtype.ext
  show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd (u : Wm)))) = (u : Wm)
  simp

omit [V.Normal] in
theorem modelSubToLin_mul (U : Submodule (ZMod 2) Wm) (x y : ↥(modelSub (H := H) θ U)) :
    modelSubToLin θ U (x * y) = modelSubToLin θ U x + modelSubToLin θ U y := by
  apply Subtype.ext
  have : (⟨(x * y).1, (mem_modelSub.1 (x * y).2).1⟩ : ↥V) =
      ⟨x.1, (mem_modelSub.1 x.2).1⟩ * ⟨y.1, (mem_modelSub.1 y.2).1⟩ := rfl
  show Multiplicative.toAdd (θ ⟨(x * y).1, _⟩) = _
  rw [this, map_mul, toAdd_mul]
  rfl

@[expose] def modelSubEquiv (U : Submodule (ZMod 2) Wm) :
    ↥(modelSub (H := H) θ U) ≃* Multiplicative ↥U where
  toFun x := Multiplicative.ofAdd (modelSubToLin θ U x)
  invFun u := modelSubOfLin θ U (Multiplicative.toAdd u)
  left_inv x := modelSubOfLin_toLin θ U x
  right_inv u := by
    apply Multiplicative.toAdd.injective
    exact modelSubToLin_ofLin θ U (Multiplicative.toAdd u)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact modelSubToLin_mul θ U x y

omit [V.Normal] in
theorem coe_modelSubEquiv (U : Submodule (ZMod 2) Wm) (x : ↥(modelSub (H := H) θ U)) :
    (((modelSubEquiv θ U x : Multiplicative ↥U).toAdd : ↥U) : Wm) =
      Multiplicative.toAdd (θ ⟨x.1, (mem_modelSub.1 x.2).1⟩) := rfl

end Dictionary

section Restrict

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def restrictLin (U : Submodule k V) (g : V ≃ₗ[k] V) (h : ∀ u : V, g u ∈ U ↔ u ∈ U) :
    U ≃ₗ[k] U where
  toFun u := ⟨g u, (h u).2 u.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)
  invFun u := ⟨g.symm u, (h (g.symm u)).1 (by simp)⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

theorem restrictLin_apply (U : Submodule k V) (g : V ≃ₗ[k] V) (h : ∀ u : V, g u ∈ U ↔ u ∈ U)
    (u : U) : ((restrictLin U g h u : U) : V) = g u := rfl

end Restrict

section Product

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {r : ℕ}

theorem exists_mem_iSup_of_agree (S : Fin r → Subgroup (V ≃ₗ[k] V)) (I : Fin r → Submodule k V)
    (y : V ≃ₗ[k] V) (hy : ∀ i, ∀ u ∈ I i, y u ∈ I i)
    (hfix : ∀ i j, i ≠ j → ∀ s ∈ S i, ∀ u ∈ I j, s u = u)
    (hs : ∀ i, ∃ s ∈ S i, ∀ u ∈ I i, s u = y u) :
    ∃ b ∈ ⨆ i, S i, ∀ j, ∀ u ∈ I j, b u = y u := by
  classical
  have key : ∀ J : Finset (Fin r), ∃ b ∈ ⨆ i ∈ J, S i,
      (∀ j ∈ J, ∀ u ∈ I j, b u = y u) ∧ (∀ j ∉ J, ∀ u ∈ I j, b u = u) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      exact ⟨1, Subgroup.one_mem _, fun j hj => absurd hj (Finset.notMem_empty j),
        fun j _ u _ => rfl⟩
    | insert i J hi ih =>
      obtain ⟨b', hb', hb'1, hb'2⟩ := ih
      obtain ⟨s, hsS, hsy⟩ := hs i
      refine ⟨b' * s, Subgroup.mul_mem _ ?_ ?_, ?_, ?_⟩
      · have hmono : (⨆ j ∈ J, S j) ≤ ⨆ j ∈ insert i J, S j :=
          iSup₂_le fun j hj => le_iSup₂_of_le j (Finset.mem_insert_of_mem hj) le_rfl
        exact hmono hb'
      · exact Subgroup.mem_iSup_of_mem i
          (Subgroup.mem_iSup_of_mem (Finset.mem_insert_self i J) hsS)
      · intro j hj u hu
        rcases Finset.mem_insert.1 hj with rfl | hjJ
        · show b' (s u) = y u
          rw [hsy u hu]
          exact hb'2 _ hi _ (hy _ u hu)
        · have hne : i ≠ j := fun h => hi (h ▸ hjJ)
          show b' (s u) = y u
          rw [hfix i j hne s hsS u hu]
          exact hb'1 j hjJ u hu
      · intro j hj u hu
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
        have hjJ : j ∉ J := fun h => hj (Finset.mem_insert_of_mem h)
        show b' (s u) = u
        rw [hfix i j hji.symm s hsS u hu]
        exact hb'2 j hjJ u hu
  obtain ⟨b, hb, hb1, -⟩ := key Finset.univ
  exact ⟨b, (iSup₂_le fun j _ => le_iSup S j) hb, fun j u hu => hb1 j (Finset.mem_univ j) u hu⟩

end Product

end CFSG.QuasithinUnique.Setup.Wreath
