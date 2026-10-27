module

public import CFSG.GroupTheory.SolvableMinimalNormalNode

public section

namespace CFSG.GroupTheory.SteinbergBK

open scoped commutatorElement

variable {G : Type*} [Group G]

abbrev chiefQuot (X Y : Subgroup G) [Y.Normal] : Subgroup (G ⧸ Y) :=
  X.map (QuotientGroup.mk' Y)

instance chiefQuot_normal (X Y : Subgroup G) [X.Normal] [Y.Normal] : (chiefQuot X Y).Normal :=
  Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Y)

@[expose] noncomputable def chiefConj (X Y : Subgroup G) [X.Normal] [Y.Normal] :
    G →* MulAut (chiefQuot X Y) :=
  MulAut.conjNormal.comp (QuotientGroup.mk' Y)

theorem chiefConj_mk (X Y : Subgroup G) [X.Normal] [Y.Normal] (g x : G) (hx : x ∈ X) :
    chiefConj X Y g ⟨QuotientGroup.mk' Y x, Subgroup.mem_map_of_mem _ hx⟩ =
      ⟨QuotientGroup.mk' Y (g * x * g⁻¹),
        Subgroup.mem_map_of_mem _ (Subgroup.Normal.conj_mem inferInstance x hx g)⟩ := by
  apply Subtype.ext
  change ((MulAut.conjNormal (QuotientGroup.mk' Y g))
    ⟨QuotientGroup.mk' Y x, Subgroup.mem_map_of_mem _ hx⟩ : G ⧸ Y) =
      QuotientGroup.mk' Y (g * x * g⁻¹)
  rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]

@[instance_reducible] noncomputable def commGroupOfComm {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := hc }

@[instance_reducible] noncomputable def elemModule (p : ℕ) [NeZero p] {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ p = 1) :
    letI := commGroupOfComm hc
    Module (ZMod p) (Additive A) :=
  letI := commGroupOfComm hc
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp _

theorem solvable_chief_factor_module [Finite G] (hG : Group.IsSolvable G) {X Y : Subgroup G}
    [X.Normal] [Y.Normal] (hYX : Y < X) (hchief : ∀ Z : Subgroup G, Z.Normal → ¬ (Y < Z ∧ Z < X)) :
    ∃ (p d : ℕ) (_ : Fact p.Prime), 1 ≤ d ∧ IsElementaryAbelian p (chiefQuot X Y) ∧
      Nat.card (chiefQuot X Y) = p ^ d ∧
      ∃ (hc : ∀ a b : chiefQuot X Y, a * b = b * a) (hp : ∀ a : chiefQuot X Y, a ^ p = 1),
        letI : CommGroup (chiefQuot X Y) := commGroupOfComm hc
        letI : Module (ZMod p) (Additive (chiefQuot X Y)) := elemModule p hc hp
          ∃ ρ : G →* (Additive (chiefQuot X Y) ≃ₗ[ZMod p] Additive (chiefQuot X Y)),
            (∀ (g x : G) (hx : x ∈ X),
              ρ g (Additive.ofMul ⟨QuotientGroup.mk' Y x, Subgroup.mem_map_of_mem _ hx⟩) =
                Additive.ofMul ⟨QuotientGroup.mk' Y (g * x * g⁻¹),
                  Subgroup.mem_map_of_mem _ (Subgroup.Normal.conj_mem inferInstance x hx g)⟩) ∧
            (∀ W : Submodule (ZMod p) (Additive (chiefQuot X Y)),
              (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
            ∀ L : Subgroup G, (∀ g ∈ L, ρ g = 1) ↔ ⁅L, X⁆ ≤ Y := by
  have := hG
  set U := chiefQuot X Y with hUdef
  have hUne : U ≠ ⊥ := by
    intro hU
    obtain ⟨x, hxX, hxY⟩ := IsConcreteLE.exists_of_lt hYX
    have hmem : QuotientGroup.mk' Y x ∈ U := ⟨x, hxX, rfl⟩
    rw [hU, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hxY hmem
  have hmin : ∀ M : Subgroup (G ⧸ Y), M.Normal → M ≠ ⊥ → M ≤ U → M = U := by
    intro M hMn hMne hMU
    have hle : Y ≤ M.comap (QuotientGroup.mk' Y) := fun y hy => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
      exact one_mem M
    have hleX : M.comap (QuotientGroup.mk' Y) ≤ X := by
      have h := Subgroup.comap_mono (f := QuotientGroup.mk' Y) hMU
      rwa [hUdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hYX.le] at h
    have hne : Y ≠ M.comap (QuotientGroup.mk' Y) := by
      intro h
      apply hMne
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) M, ← h,
        QuotientGroup.map_mk'_self]
    have hX : M.comap (QuotientGroup.mk' Y) = X := by
      by_contra hneX
      exact hchief _ (hMn.comap _) ⟨lt_of_le_of_ne hle hne, lt_of_le_of_ne hleX hneX⟩
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) M, hX]
  obtain ⟨p, d, hp, hd, helem, hcard⟩ :=
    CFSG.SolvableHall.solvable_minimal_normal_elementary_abelian inferInstance U hUne hmin
  have : Fact p.Prime := ⟨hp⟩
  have hc : ∀ a b : U, a * b = b * a := fun a b => helem.is_comm.comm a b
  have hpz : ∀ a : U, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p U) a
  refine ⟨p, d, this, hd, helem, hcard, hc, hpz, ?_⟩
  let _ : CommGroup U := commGroupOfComm hc
  let _ : Module (ZMod p) (Additive U) := elemModule p hc hpz
  let ρf : G → (Additive U ≃ₗ[ZMod p] Additive U) := fun g =>
    (MulEquiv.toAdditive (chiefConj X Y g)).toLinearEquiv
      (ZMod.map_smul (MulEquiv.toAdditive (chiefConj X Y g)))
  have hρf : ∀ g a, ρf g a = Additive.ofMul (chiefConj X Y g (Additive.toMul a)) := fun _ _ => rfl
  let ρ : G →* (Additive U ≃ₗ[ZMod p] Additive U) :=
    { toFun := ρf
      map_one' := LinearEquiv.ext fun a => by
        rw [hρf, map_one]
        rfl
      map_mul' := fun g h => LinearEquiv.ext fun a => by
        rw [hρf, map_mul]
        rfl }
  have hρ : ∀ g a, ρ g a = Additive.ofMul (chiefConj X Y g (Additive.toMul a)) := fun _ _ => rfl
  refine ⟨ρ, fun g x hx => ?_, fun W hW => ?_, fun L => ?_⟩
  · rw [hρ, toMul_ofMul, chiefConj_mk X Y g x hx]
  ·
    let Wm : Subgroup U := AddSubgroup.toSubgroup' W.toAddSubgroup
    have hWm : ∀ x : U, x ∈ Wm ↔ Additive.ofMul x ∈ W := fun _ => Iff.rfl
    let M : Subgroup (G ⧸ Y) := Wm.map U.subtype
    have hMn : M.Normal := by
      refine ⟨fun m hm q => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hm
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Y q
      refine ⟨chiefConj X Y g x, (hWm _).mpr ?_, ?_⟩
      · have h := hW g _ ((hWm x).mp hx)
        rwa [hρ, toMul_ofMul] at h
      · change ((MulAut.conjNormal (QuotientGroup.mk' Y g) x : U) : G ⧸ Y) = _
        rw [MulAut.conjNormal_apply]
        rfl
    by_cases hMb : M = ⊥
    · left
      rw [eq_bot_iff]
      intro w hw
      have h1 : ((Additive.toMul w : U) : G ⧸ Y) ∈ M := ⟨Additive.toMul w, (hWm _).mpr hw, rfl⟩
      rw [hMb, Subgroup.mem_bot] at h1
      rw [Submodule.mem_bot]
      apply Additive.toMul.injective
      exact Subtype.ext h1
    · right
      have hMU := hmin M hMn hMb (Subgroup.map_subtype_le _)
      rw [eq_top_iff]
      intro w _
      have h1 : ((Additive.toMul w : U) : G ⧸ Y) ∈ M := by
        rw [hMU]
        exact (Additive.toMul w : U).2
      obtain ⟨x, hx, hxw⟩ := h1
      have hxw' : x = Additive.toMul w := Subtype.ext hxw
      rw [← ofMul_toMul w, ← hxw']
      exact (hWm x).mp hx
  · constructor
    · intro hL
      rw [Subgroup.commutator_le]
      intro g hg x hx
      have h := congrArg (fun f => f (Additive.ofMul
        (⟨QuotientGroup.mk' Y x, Subgroup.mem_map_of_mem _ hx⟩ : U))) (hL g hg)
      simp only [hρ, toMul_ofMul, LinearEquiv.coe_one, id_eq] at h
      have h' := congrArg Subtype.val (Additive.ofMul.injective h)
      change QuotientGroup.mk' Y (g * x * g⁻¹) = QuotientGroup.mk' Y x at h'
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
      have h2 : ⁅g, x⁆ = (x * ((g * x * g⁻¹)⁻¹ * x) * x⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact inv_mem (Subgroup.Normal.conj_mem inferInstance _ h' x)
    · intro hLX g hg
      refine LinearEquiv.ext fun a => ?_
      obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ : ∃ u : U, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
      rw [hρ, toMul_ofMul, LinearEquiv.coe_one, id, chiefConj_mk X Y g x hx]
      congr 2
      have hc' : ⁅g, x⁆ ∈ Y := (Subgroup.commutator_le.mp hLX) g hg x hx
      rw [show g * x * g⁻¹ = ⁅g, x⁆ * x by rw [commutatorElement_def]; group, map_mul,
        show QuotientGroup.mk' Y ⁅g, x⁆ = 1 from (QuotientGroup.eq_one_iff _).mpr hc', one_mul]

end CFSG.GroupTheory.SteinbergBK
