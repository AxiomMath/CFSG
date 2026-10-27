module

public import CFSG.GroupTheory.GLnTwoSplitting.PointComplement
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule
open scoped IsMulCommutative

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (X : NatExt G E)

instance V_isMulCommutative : IsMulCommutative X.V :=
  ⟨⟨fun a b => by
    obtain ⟨u, hu⟩ := a.2
    obtain ⟨w, hw⟩ := b.2
    exact Subtype.ext (by
      change (a : G) * b = b * a
      rw [← hu, ← hw, X.ι_mul_comm])⟩⟩

theorem card_V : Nat.card X.V = Nat.card E :=
  (Nat.card_congr (Equiv.ofBijective (fun e => (⟨X.ι e, X.ι_mem_V e⟩ : X.V))
    ⟨fun a b h => X.injective (congrArg Subtype.val h), fun v => by
      obtain ⟨e, he⟩ := v.2
      exact ⟨e, Subtype.ext he⟩⟩)).symm

theorem index_stab [FiniteDimensional (ZMod 2) E] {e₀ : E} (he₀ : e₀ ≠ 0) :
    (X.stab e₀).index = Nat.card E - 1 := by
  let _ : MulAction G E := MulAction.compHom E X.π
  have hstab : MulAction.stabilizer G e₀ = X.stab e₀ := by
    ext g
    exact Iff.rfl
  have horbit : MulAction.orbit G e₀ = {v | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      change X.π g e₀ ≠ 0
      intro h
      exact he₀ ((X.π g).injective (h.trans (map_zero _).symm))
    · intro hv
      obtain ⟨f, d, hfd, hτ⟩ := exists_transvection_apply_eq he₀ hv
      obtain ⟨g, hg⟩ := X.surjective (LinearEquiv.transvection hfd)
      exact ⟨g, by change X.π g e₀ = v; rw [hg, hτ]⟩
  rw [← hstab, MulAction.index_stabilizer, horbit, show {v : E | v ≠ 0} = Set.univ \ {0} by
    ext v
    simp, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]

theorem exists_complement [Finite G] [FiniteDimensional (ZMod 2) E]
    (hE : 6 ≤ finrank (ZMod 2) E) : ∃ K : Subgroup G, X.V ⊓ K = ⊥ ∧ X.V ⊔ K = ⊤ := by
  obtain ⟨e₀, he₀⟩ := Module.finrank_pos_iff_exists_ne_zero.1
    (show 0 < finrank (ZMod 2) E by omega)
  obtain ⟨K₀, hK₀, hK₀'⟩ := X.exists_complement_stab hE he₀
  have hcard : Nat.card E = 2 ^ finrank (ZMod 2) E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcop : Nat.Coprime (X.stab e₀).index (Nat.card X.V) := by
    rw [X.index_stab he₀, X.card_V, hcard]
    exact (Nat.coprime_self_sub_left Nat.one_le_two_pow).2 (Nat.coprime_one_left _)
  obtain ⟨D, -, hVD, hVD'⟩ :=
    abelian_normal_coprime_index_complement_lifting X.V (X.stab e₀) K₀ hcop hK₀ hK₀'
  exact ⟨D, hVD, hVD'⟩

end NatExt

section Normal

variable {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

@[expose] noncomputable def conjLinear : G →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun g := (MulEquiv.toAdditive (MulAut.conjNormal g)).toLinearEquiv (ZMod.map_smul _)
  map_one' := LinearEquiv.ext fun e => Additive.toMul.injective (Subtype.ext (by
    change ((MulAut.conjNormal (1 : G) (Additive.toMul e) : V) : G) = ((Additive.toMul e : V) : G)
    rw [MulAut.conjNormal_apply]
    group))
  map_mul' g h := LinearEquiv.ext fun e => Additive.toMul.injective (Subtype.ext (by
    change ((MulAut.conjNormal (g * h) (Additive.toMul e) : V) : G) =
      ((MulAut.conjNormal g (MulAut.conjNormal h (Additive.toMul e)) : V) : G)
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    group))

theorem coe_conjLinear_apply (g : G) (e : Additive V) :
    ((Additive.toMul (conjLinear V g e) : V) : G) = g * ((Additive.toMul e : V) : G) * g⁻¹ :=
  MulAut.conjNormal_apply g (Additive.toMul e)

theorem conjLinear_eq_one_iff (hC : Subgroup.centralizer (V : Set G) ≤ V) (g : G) :
    conjLinear V g = 1 ↔ ∃ e : Additive V, ((Additive.toMul e : V) : G) = g := by
  constructor
  · intro h
    refine ⟨Additive.ofMul ⟨g, hC (Subgroup.mem_centralizer_iff.2 fun v hv => ?_)⟩, rfl⟩
    have h1 := congrArg (fun φ : Additive V ≃ₗ[ZMod 2] Additive V =>
      ((Additive.toMul (φ (Additive.ofMul ⟨v, hv⟩)) : V) : G)) h
    simp only [coe_conjLinear_apply] at h1
    change g * v * g⁻¹ = v at h1
    calc v * g = g * v * g⁻¹ * g := by rw [h1]
      _ = g * v := by group
  · rintro ⟨e, rfl⟩
    refine LinearEquiv.ext fun x => Additive.toMul.injective (Subtype.ext ?_)
    rw [coe_conjLinear_apply]
    have := mul_comm (Additive.toMul e) (Additive.toMul x)
    rw [← Subtype.coe_inj, Subgroup.coe_mul, Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
    rfl

theorem card_linearEquiv_eq {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {n : ℕ} (hn : finrank (ZMod 2) E = n) :
    Nat.card (E ≃ₗ[ZMod 2] E) = Nat.card (GL (Fin n) (ZMod 2)) := by
  let b := (Module.finBasisOfFinrankEq (ZMod 2) E hn).equivFun
  let e₁ : (E ≃ₗ[ZMod 2] E) ≃ ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun f => b.symm.trans (f.trans b)
      invFun := fun g => b.trans (g.trans b.symm)
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  rw [Nat.card_congr e₁]
  exact Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv)

variable {V}

@[expose] noncomputable def natExtOfNormal [Finite G] {n : ℕ}
    (hC : Subgroup.centralizer (V : Set G) ≤ V) (hcard : Nat.card (G ⧸ V) =
      Nat.card (GL (Fin n) (ZMod 2))) (hfin : finrank (ZMod 2) (Additive V) = n) :
    NatExt G (Additive V) where
  ι e := ((Additive.toMul e : V) : G)
  ι_add _ _ := rfl
  injective _ _ h := Additive.toMul.injective (Subtype.ext h)
  π := conjLinear V
  surjective := by
    have hker : (conjLinear V).ker = V := by
      ext g
      rw [MonoidHom.mem_ker, conjLinear_eq_one_iff V hC]
      exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hg => ⟨Additive.ofMul ⟨g, hg⟩, rfl⟩⟩
    have : Finite (Additive V ≃ₗ[ZMod 2] Additive V) :=
      Finite.of_injective
        (fun f : Additive V ≃ₗ[ZMod 2] Additive V => (f : Additive V → Additive V))
        fun _ _ h => LinearEquiv.ext (congrFun h)
    have hrange : (conjLinear V).range = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (conjLinear V)).toEquiv]
      have e₁ : G ⧸ (conjLinear V).ker ≃ G ⧸ V := by rw [hker]
      rw [Nat.card_congr e₁, hcard, card_linearEquiv_eq hfin]
    intro f
    obtain ⟨g, hg⟩ := hrange ▸ Subgroup.mem_top f
    exact ⟨g, hg⟩
  ker_iff g := conjLinear_eq_one_iff V hC g
  conj g e := (coe_conjLinear_apply V g e).symm

end Normal

theorem dempwolff_gln_two_natural_module_splitting {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : 6 ≤ n) (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hV : Nat.card V = 2 ^ n)
    (hC : Subgroup.centralizer (V : Set G) ≤ V) (hGV : Nonempty (G ⧸ V ≃* GL (Fin n) (ZMod 2))) :
    ∃ K : Subgroup G, V ⊔ K = ⊤ ∧ V ⊓ K = ⊥ := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hfin : finrank (ZMod 2) (Additive V) = n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = Nat.card V from rfl, hV] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  obtain ⟨e⟩ := hGV
  let X := natExtOfNormal hC (Nat.card_congr e.toEquiv) hfin
  have hXV : X.V = V := by
    ext g
    exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hg => ⟨Additive.ofMul ⟨g, hg⟩, rfl⟩⟩
  obtain ⟨K, hK, hK'⟩ := X.exists_complement (by omega)
  rw [hXV] at hK hK'
  exact ⟨K, hK', hK⟩

end CFSG.GroupTheory.GLnTwoSplitting
