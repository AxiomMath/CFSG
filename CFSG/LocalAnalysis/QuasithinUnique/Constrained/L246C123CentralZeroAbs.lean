module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123SylowA7
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.QuasithinUnique.L246.C123

open CFSG.Quasithin Matrix

theorem card_dualSet (w : Fin 5 → ZMod 2) (hw : w ≠ 0) :
    Nat.card {v : Fin 5 → ZMod 2 // v ⬝ᵥ w = 1} = 16 := by
  rw [Nat.card_eq_fintype_card]
  revert w
  decide

section Dual

variable {Λ : Type} [Group Λ]

@[expose] noncomputable def dualHom (Mrep : Λ →* GL (Fin 5) (ZMod 2)) (w : Fin 5 → ZMod 2)
    (hfix : ∀ g, (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) :
    Λ →* Equiv.Perm {v : Fin 5 → ZMod 2 // v ⬝ᵥ w = 1} where
  toFun g :=
    { toFun := fun v => ⟨v.1 ᵥ* ((Mrep g)⁻¹ : GL (Fin 5) (ZMod 2)).1, by
        have hN : ((Mrep g)⁻¹ : GL (Fin 5) (ZMod 2)).1 *ᵥ w = w := by
          have := congrArg (fun x => ((Mrep g)⁻¹ : GL (Fin 5) (ZMod 2)).1 *ᵥ x) (hfix g)
          simp only [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
          exact this.symm
        rw [← dotProduct_mulVec, hN]
        exact v.2⟩
      invFun := fun v => ⟨v.1 ᵥ* (Mrep g).1, by
        rw [← dotProduct_mulVec, hfix g]
        exact v.2⟩
      left_inv := fun v => Subtype.ext (by
        simp only [vecMul_vecMul, Units.inv_mul, vecMul_one])
      right_inv := fun v => Subtype.ext (by
        simp only [vecMul_vecMul, Units.mul_inv, vecMul_one]) }
  map_one' := Equiv.ext fun v => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun v => Subtype.ext (by
    simp only [map_mul, _root_.mul_inv_rev, Units.val_mul, Equiv.Perm.mul_apply,
      Equiv.coe_fn_mk, vecMul_vecMul])

theorem dualHom_apply (Mrep : Λ →* GL (Fin 5) (ZMod 2)) (w : Fin 5 → ZMod 2)
    (hfix : ∀ g, (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) (g : Λ)
    (v : {v : Fin 5 → ZMod 2 // v ⬝ᵥ w = 1}) :
    (dualHom Mrep w hfix g v).1 = v.1 ᵥ* ((Mrep g)⁻¹ : GL (Fin 5) (ZMod 2)).1 := rfl

end Dual

section Abstract

open CFSG.SectionRank.Ccomm

theorem central_zero_abstract
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {Λ : Type} [Group Λ] (act : Λ →* MulAut V) (α : Λ →* A7) (hα : Function.Surjective α)
    (hker : ∀ q : Λ, α q = 1 → act q = 1) (Z : Subgroup V)
    (hZfix : ∀ g : Λ, ∀ z ∈ Z, act g z = z) (hcard : Nat.card V = 16 * Nat.card Z)
    (hgen : Subgroup.closure {x : V | ∃ (g : Λ) (v : V), x = act g v * v⁻¹} = ⊤) :
    Z = ⊥ := by
  by_contra hZ
  have hZp : IsPGroup 2 ↥Z := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hV2 x)⟩
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this, pow_zero, Subgroup.card_eq_one] at hk
    exact hZ hk
  obtain ⟨eZ⟩ := nonempty_mulEquiv_of_elementary (p := 2) (W := ↥Z)
    (fun a b => Subtype.ext (mul_comm _ _)) (fun a => Subtype.ext (hV2 a)) hk
  let ev : Multiplicative (Fin k → ZMod 2) →* Multiplicative (ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (Multiplicative.toAdd v ⟨0, hk1⟩)
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let ψ : ↥Z →* Multiplicative (ZMod 2) := ev.comp eZ.toMonoidHom
  let z₀ : ↥Z := eZ.symm (Multiplicative.ofAdd (Pi.single ⟨0, hk1⟩ 1))
  have hψz₀ : ψ z₀ ≠ 1 := by
    show Multiplicative.ofAdd (Multiplicative.toAdd (eZ (eZ.symm
      (Multiplicative.ofAdd (Pi.single (⟨0, hk1⟩ : Fin k) (1 : ZMod 2))))) ⟨0, hk1⟩) ≠ 1
    rw [MulEquiv.apply_symm_apply]
    simp
  have hψ1 : ∀ x : ↥Z, ψ x = 1 ∨ ψ x = Multiplicative.ofAdd 1 := fun x => by
    have h : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide
    exact h _
  have hψz₀' : ψ z₀ = Multiplicative.ofAdd 1 := (hψ1 z₀).resolve_left hψz₀
  let Z₀ : Subgroup V := ψ.ker.map Z.subtype
  have hZ₀Z : Z₀ ≤ Z := Subgroup.map_subtype_le _
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide
    rcases h y with rfl | rfl
    · exact one_mem _
    · exact ⟨z₀, hψz₀'⟩
  have hZ₀card : Nat.card Z₀ * 2 = Nat.card Z := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [hrange, Subgroup.card_top] at h1
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [h2] at h1
    rw [← h1, Subgroup.card_map_of_injective Z.subtype_injective]
  have hz₀Z : (z₀ : V) ∈ Z := z₀.2
  have hz₀Z₀ : (z₀ : V) ∉ Z₀ := by
    rintro ⟨z, hz, hzz⟩
    have : z = z₀ := Subtype.ext hzz
    rw [this] at hz
    exact hψz₀ hz
  have hcardÛ : Nat.card (V ⧸ Z₀) = 2 ^ 5 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z₀
    have hpos : 0 < Nat.card Z₀ := Nat.card_pos
    rw [hcard, ← hZ₀card] at h1
    have h4 : Nat.card (V ⧸ Z₀) * Nat.card Z₀ = 32 * Nat.card Z₀ := by omega
    have h5 : Nat.card (V ⧸ Z₀) = 32 := Nat.eq_of_mul_eq_mul_right hpos h4
    rw [h5]
    norm_num
  have hÛ2 : ∀ x : V ⧸ Z₀, x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hV2 v]; rfl
  obtain ⟨eÛ⟩ := nonempty_mulEquiv_of_elementary (p := 2) (W := V ⧸ Z₀)
    (fun a b => mul_comm a b) hÛ2 hcardÛ
  have hstab : ∀ g : Λ, act g ∈ stabSub Z₀ := by
    intro g u
    constructor
    · intro h
      have hu : act g u = u := by
        have h1 : act g (act g u) = act g u := hZfix g _ (hZ₀Z h)
        exact (act g).injective h1
      rw [hu] at h
      exact h
    · intro h
      have : act g u = u := hZfix g u (hZ₀Z h)
      rw [this]
      exact h
  let actFun : Λ →* ↥(stabSub Z₀) := act.codRestrict (stabSub Z₀) hstab
  let actHat : Λ →* MulAut (V ⧸ Z₀) := (quotHom Z₀).comp actFun
  have hactHat : ∀ (g : Λ) (v : V), actHat g (QuotientGroup.mk v) = QuotientGroup.mk (act g v) :=
    fun g v => rfl
  let Mrep : Λ →* GL (Fin 5) (ZMod 2) := (elemAutEquivGL eÛ).toMonoidHom.comp actHat
  have hMrep : ∀ (g : Λ) (x : V ⧸ Z₀), (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
      Multiplicative.toAdd (eÛ x) = Multiplicative.toAdd (eÛ (actHat g x)) :=
    fun g x => elemAutEquivGL_mulVec eÛ (actHat g) x
  let w : Fin 5 → ZMod 2 := Multiplicative.toAdd (eÛ (QuotientGroup.mk (z₀ : V)))
  have hw0 : w ≠ 0 := by
    intro h0
    have h1 : eÛ (QuotientGroup.mk (z₀ : V)) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_one]
      exact h0
    have h2 : (QuotientGroup.mk (z₀ : V) : V ⧸ Z₀) = 1 := eÛ.injective (h1.trans (map_one eÛ).symm)
    exact hz₀Z₀ ((QuotientGroup.eq_one_iff _).1 h2)
  have hwfix : ∀ g : Λ, (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w := by
    intro g
    show (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
      Multiplicative.toAdd (eÛ (QuotientGroup.mk (z₀ : V))) = _
    rw [hMrep, hactHat, hZfix g _ hz₀Z]
  let σΛ := dualHom Mrep w hwfix
  have hΩ : Nat.card {v : Fin 5 → ZMod 2 // v ⬝ᵥ w = 1} = 16 := card_dualSet w hw0
  have hker' : α.ker ≤ σΛ.ker := by
    intro q hq
    have hq1 : α q = 1 := hq
    have h1 : act q = 1 := hker q hq1
    have h2 : Mrep q = 1 := by
      have h3 : actHat q = 1 := by
        show quotHom Z₀ (actFun q) = 1
        have : actFun q = 1 := Subtype.ext h1
        rw [this, map_one]
      show (elemAutEquivGL eÛ) (actHat q) = 1
      rw [h3, map_one]
    show σΛ q = 1
    refine Equiv.ext fun v => Subtype.ext ?_
    rw [Equiv.Perm.coe_one, id_eq]
    show (dualHom Mrep w hwfix q v).1 = v.1
    rw [dualHom_apply, h2]
    simp
  let σ : A7 →* Equiv.Perm {v : Fin 5 → ZMod 2 // v ⬝ᵥ w = 1} :=
    (MonoidHom.liftOfRightInverse α (Function.surjInv hα) (Function.rightInverse_surjInv hα))
      ⟨σΛ, hker'⟩
  have hσ : ∀ g : Λ, σ (α g) = σΛ g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply α _ _ ⟨σΛ, hker'⟩ g
  obtain ⟨ω, hω⟩ := exists_fixed_of_card_sixteen hΩ σ
  have hv₀ : ∀ g : Λ, ω.1 ᵥ* (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = ω.1 := by
    intro g
    have h1 := hω (α g)
    rw [hσ] at h1
    have h2 : ω.1 ᵥ* ((Mrep g)⁻¹ : GL (Fin 5) (ZMod 2)).1 = ω.1 := congrArg Subtype.val h1
    calc ω.1 ᵥ* (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2))
        = (ω.1 ᵥ* ((Mrep g)⁻¹ : GL (Fin 5) (ZMod 2)).1) ᵥ*
            (Mrep g : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by rw [h2]
      _ = ω.1 := by rw [vecMul_vecMul, Units.inv_mul, vecMul_one]
  let r₀ : V →* Multiplicative (ZMod 2) :=
    { toFun := fun v =>
        Multiplicative.ofAdd (ω.1 ⬝ᵥ Multiplicative.toAdd (eÛ (QuotientGroup.mk v)))
      map_one' := by simp
      map_mul' := fun a b => by
        simp [QuotientGroup.mk_mul, map_mul, dotProduct_add] }
  have hr₀ : ∀ (g : Λ) (v : V), r₀ (act g v) = r₀ v := by
    intro g v
    show Multiplicative.ofAdd (ω.1 ⬝ᵥ Multiplicative.toAdd (eÛ (QuotientGroup.mk (act g v)))) =
      Multiplicative.ofAdd (ω.1 ⬝ᵥ Multiplicative.toAdd (eÛ (QuotientGroup.mk v)))
    rw [← hactHat g v, ← hMrep g, dotProduct_mulVec, hv₀ g]
  have hker₀ : Subgroup.closure {x : V | ∃ (g : Λ) (v : V), x = act g v * v⁻¹} ≤ r₀.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hr₀]
    exact mul_inv_cancel _
  rw [hgen] at hker₀
  have h1 : r₀ (z₀ : V) = 1 := hker₀ (Subgroup.mem_top _)
  have h2 : r₀ (z₀ : V) = Multiplicative.ofAdd 1 := by
    show Multiplicative.ofAdd (ω.1 ⬝ᵥ w) = _
    rw [ω.2]
  rw [h2] at h1
  exact absurd h1 (by decide)

end Abstract

end CFSG.QuasithinUnique.L246.C123
