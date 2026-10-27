module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

section Dict

variable {G : Type} [Group G] {V : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : ↥V ≃* Multiplicative W)

omit [Module (ZMod 2) W] in
theorem vecOf_mul (u v : ↥V) : vecOf θ (u * v) = vecOf θ u + vecOf θ v := by
  simp [vecOf]

omit [Module (ZMod 2) W] in
theorem vecOf_inv (u : ↥V) : vecOf θ u⁻¹ = - vecOf θ u := by
  simp [vecOf]

omit [Module (ZMod 2) W] in
theorem vecOf_one : vecOf θ (1 : ↥V) = 0 := by
  simp [vecOf]

omit [Module (ZMod 2) W] in
theorem vecOf_injective : Function.Injective (vecOf θ) := by
  intro u v h
  exact θ.injective (Multiplicative.toAdd.injective h)

theorem binPsi_vecOf (φ : MulAut V) (v : ↥V) : binPsi θ φ (vecOf θ v) = vecOf θ (φ v) := by
  simp [binPsi_apply, vecOf]

theorem binPsi_sub_vecOf (φ : MulAut V) (v : ↥V) :
    binPsi θ φ (vecOf θ v) - vecOf θ v = vecOf θ (φ v * v⁻¹) := by
  rw [binPsi_vecOf, vecOf_mul, vecOf_inv, sub_eq_add_neg]

theorem mem_modComm_imp (A : Subgroup (MulAut V)) {g : G} (hg : g ∈ modComm V A) :
    ∃ hgV : g ∈ V, vecOf θ ⟨g, hgV⟩ ∈ commGL (A.map (binPsi θ).toMonoidHom) ⊤ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, v, rfl⟩ := hx
    refine ⟨V.mul_mem (a v).2 (V.inv_mem v.2), ?_⟩
    have h1 : (⟨((a v : V) : G) * (v : G)⁻¹, V.mul_mem (a v).2 (V.inv_mem v.2)⟩ : ↥V) =
        a v * v⁻¹ := rfl
    rw [h1, ← binPsi_sub_vecOf θ a v]
    exact mem_commSub_of (b := binPsi θ a)
      (Subgroup.mem_map.2 ⟨a, ha, rfl⟩ : binPsi θ a ∈ A.map (binPsi θ).toMonoidHom)
      Submodule.mem_top
  | one =>
    refine ⟨V.one_mem, ?_⟩
    have : (⟨1, V.one_mem⟩ : ↥V) = 1 := rfl
    rw [this, vecOf_one]
    exact Submodule.zero_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨hxV, hx⟩ := hx
    obtain ⟨hyV, hy⟩ := hy
    refine ⟨V.mul_mem hxV hyV, ?_⟩
    have : (⟨x * y, V.mul_mem hxV hyV⟩ : ↥V) = ⟨x, hxV⟩ * ⟨y, hyV⟩ := rfl
    rw [this, vecOf_mul]
    exact Submodule.add_mem _ hx hy
  | inv x _ hx =>
    obtain ⟨hxV, hx⟩ := hx
    refine ⟨V.inv_mem hxV, ?_⟩
    have : (⟨x⁻¹, V.inv_mem hxV⟩ : ↥V) = ⟨x, hxV⟩⁻¹ := rfl
    rw [this, vecOf_inv]
    exact Submodule.neg_mem _ hx

theorem elOf_sub_eq (a : MulAut V) (u : W) :
    elOf θ (binPsi θ a u - u) = a (elOf θ u) * (elOf θ u)⁻¹ := by
  have h3 := binPsi_sub_vecOf θ a (elOf θ u)
  rw [vecOf_elOf] at h3
  rw [h3, elOf_vecOf]

theorem elOf_mem_modComm (A : Subgroup (MulAut V)) {w : W}
    (hw : w ∈ commGL (A.map (binPsi θ).toMonoidHom) ⊤) :
    ((elOf θ w : ↥V) : G) ∈ modComm V A := by
  refine elOf_mem_of_span θ (modComm V A) ?_ hw
  rintro _ ⟨b, hb, u, -, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hb
  have h1 : elOf θ ((MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((binPsi θ).toMonoidHom a) u - u) =
      a (elOf θ u) * (elOf θ u)⁻¹ := elOf_sub_eq θ a u
  rw [h1]
  exact Subgroup.subset_closure ⟨a, ha, elOf θ u, rfl⟩

theorem mem_modComm_iff (A : Subgroup (MulAut V)) (u : ↥V) :
    (u : G) ∈ modComm V A ↔ vecOf θ u ∈ commGL (A.map (binPsi θ).toMonoidHom) ⊤ := by
  constructor
  · intro h
    obtain ⟨hV, hv⟩ := mem_modComm_imp θ A h
    exact hv
  · intro h
    have := elOf_mem_modComm θ A h
    rwa [elOf_vecOf] at this

@[expose] def modCommEquiv (A : Subgroup (MulAut V)) :
    ↥(modComm V A) ≃* Multiplicative ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤) where
  toFun u := Multiplicative.ofAdd
    ⟨vecOf θ ⟨u.1, modComm_le V A u.2⟩, (mem_modComm_iff θ A _).1 u.2⟩
  invFun w := ⟨((elOf θ (Multiplicative.toAdd w).1 : ↥V) : G),
    elOf_mem_modComm θ A (Multiplicative.toAdd w).2⟩
  left_inv u := by
    apply Subtype.ext
    show ((elOf θ (vecOf θ ⟨u.1, modComm_le V A u.2⟩) : ↥V) : G) = u.1
    rw [elOf_vecOf]
  right_inv w := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show vecOf θ ⟨((elOf θ (Multiplicative.toAdd w).1 : ↥V) : G), _⟩ = (Multiplicative.toAdd w).1
    exact vecOf_elOf θ _
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show vecOf θ ⟨u.1 * v.1, _⟩ = vecOf θ ⟨u.1, _⟩ + vecOf θ ⟨v.1, _⟩
    exact vecOf_mul θ ⟨u.1, _⟩ ⟨v.1, _⟩

theorem modCommEquiv_apply (A : Subgroup (MulAut V)) (u : ↥(modComm V A)) :
    ((Multiplicative.toAdd (modCommEquiv θ A u) : ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤)) : W) =
      vecOf θ ⟨u.1, modComm_le V A u.2⟩ := rfl

end Dict

section Even

@[expose] def evenCongr {Ω : Type} [Fintype Ω] (e : Ω ≃ Fin 5) :
    ↥(CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight Ω) ≃+
      ↥(CFSG.QuasithinUnique.evenWeight 5) where
  toFun x := ⟨fun k => (x : Ω → ZMod 2) (e.symm k), by
    show ∑ k : Fin 5, (x : Ω → ZMod 2) (e.symm k) = 0
    rw [Equiv.sum_comp e.symm (x : Ω → ZMod 2)]
    exact x.2⟩
  invFun y := ⟨fun ω => (y : Fin 5 → ZMod 2) (e ω), by
    show ∑ ω, (y : Fin 5 → ZMod 2) (e ω) = 0
    rw [Equiv.sum_comp e (y : Fin 5 → ZMod 2)]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    funext ω
    simp
  right_inv y := by
    apply Subtype.ext
    funext k
    simp
  map_add' x y := Subtype.ext (funext fun k => rfl)

theorem evenCongr_apply {Ω : Type} [Fintype Ω] (e : Ω ≃ Fin 5)
    (x : ↥(CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight Ω)) (k : Fin 5) :
    ((evenCongr e x : ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2) k =
      (x : Ω → ZMod 2) (e.symm k) := rfl

end Even

section Alt

variable {G : Type} [Group G] {V : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : ↥V ≃* Multiplicative W)

theorem alt_data_of_model (A : Subgroup (MulAut V)) {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (h5 : Fintype.card Ω = 5) (Bm : Subgroup (W ≃ₗ[ZMod 2] W))
    (hAB : A.map (binPsi θ).toMonoidHom ≤ Bm) (ψi : ↥Bm ≃* Equiv.Perm Ω)
    (βi : ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤) ≃ₗ[ZMod 2]
      ↥(CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight Ω))
    (hcompat : ∀ (b : ↥Bm) (u u' : ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤)),
      (u' : W) = (b : W ≃ₗ[ZMod 2] W) (u : W) →
        ((βi u' : ↥(CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight Ω)) : Ω → ZMod 2) =
          CFSG.QuasithinUnique.Setup.SL2Modules.permAct (ψi b)
            ((βi u : ↥(CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight Ω)) : Ω → ZMod 2))
    (halt : ((A.map (binPsi θ).toMonoidHom).subgroupOf Bm).map ψi.toMonoidHom =
      alternatingGroup Ω) :
    ∃ (e : ↥A ≃* alternatingGroup (Fin 5))
      (β : ↥(modComm V A) ≃* Multiplicative ↥(CFSG.QuasithinUnique.evenWeight 5)),
      ∀ (x : ↥A) (u v : ↥(modComm V A)) (hu : (u : G) ∈ V) (hv : (v : G) ∈ V),
        ((x : MulAut V) ⟨u, hu⟩ : ↥V) = ⟨v, hv⟩ → ∀ k : Fin 5,
          ((Multiplicative.toAdd (β v) : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
              Fin 5 → ZMod 2) k =
            ((Multiplicative.toAdd (β u) : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
              Fin 5 → ZMod 2) (((e x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))⁻¹ k) := by
  classical
  let e5 : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq h5
  let e₁ : ↥A ≃* ↥(A.map (binPsi θ).toMonoidHom) := mapEquiv (binPsi θ) A
  let e₂ : ↥(A.map (binPsi θ).toMonoidHom) ≃*
      ↥((A.map (binPsi θ).toMonoidHom).subgroupOf Bm) :=
    (Subgroup.subgroupOfEquivOfLe hAB).symm
  let e₃ := ψi.subgroupMap ((A.map (binPsi θ).toMonoidHom).subgroupOf Bm)
  let e₄ := MulEquiv.subgroupCongr halt
  let e₅ := e5.altCongrHom
  let e : ↥A ≃* alternatingGroup (Fin 5) := e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))
  let β₂ : ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤) ≃+ ↥(CFSG.QuasithinUnique.evenWeight 5) :=
    βi.toAddEquiv.trans (evenCongr e5)
  let β : ↥(modComm V A) ≃* Multiplicative ↥(CFSG.QuasithinUnique.evenWeight 5) :=
    (modCommEquiv θ A).trans (AddEquiv.toMultiplicative β₂)
  have hex : ∀ x : ↥A, ((e x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
      e5.permCongr (ψi ⟨binPsi θ x, hAB (Subgroup.mem_map_of_mem _ x.2)⟩) := fun x => rfl
  refine ⟨e, β, ?_⟩
  intro x u v hu hv hxuv k
  set b : ↥Bm := ⟨binPsi θ x, hAB (Subgroup.mem_map_of_mem _ x.2)⟩ with hb
  set wu : ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤) :=
    Multiplicative.toAdd (modCommEquiv θ A u) with hwu
  set wv : ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤) :=
    Multiplicative.toAdd (modCommEquiv θ A v) with hwv
  have hwuv : (wv : W) = (b : W ≃ₗ[ZMod 2] W) (wu : W) := by
    rw [hwv, hwu, modCommEquiv_apply, modCommEquiv_apply]
    have h2 := binPsi_vecOf θ (x : MulAut V) ⟨u, hu⟩
    rw [hxuv] at h2
    exact h2.symm
  have h1 := hcompat b wu wv hwuv
  show ((evenCongr e5 (βi wv) : ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2) k =
    ((evenCongr e5 (βi wu) : ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2)
      (((e x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))⁻¹ k)
  have hsymm : ∀ (σ : Equiv.Perm Ω) (k : Fin 5),
      e5.symm ((e5.permCongr σ).symm k) = σ.symm (e5.symm k) := by
    intro σ k
    have h := (e5.permCongr σ).apply_symm_apply k
    rw [Equiv.permCongr_apply] at h
    have h' : σ (e5.symm ((e5.permCongr σ).symm k)) = e5.symm k :=
      (Equiv.eq_symm_apply e5).2 h
    exact ((Equiv.symm_apply_eq σ).2 h'.symm).symm
  rw [evenCongr_apply, evenCongr_apply, h1, hex x]
  simp only [CFSG.QuasithinUnique.Setup.SL2Modules.permAct, Equiv.Perm.inv_def, hsymm]
  rfl

end Alt

end CFSG.QuasithinUnique.Setup.Lift
