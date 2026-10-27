module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Core

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.CGT.PushingUpLit.BHS6
open scoped TensorProduct MonoidAlgebra

section Translate

variable {V : Type} [CommGroup V]

@[expose, instance_reducible] noncomputable def m3Module (hV : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (fun x => by
    have h : Additive.ofMul (Additive.toMul x ^ 2) = 2 • x := ofMul_pow 2 (Additive.toMul x)
    rw [← h, hV]
    rfl)

variable {F : Type} [Field F]

@[expose] noncomputable def m3Rep [Module (ZMod 2) (Additive V)] (G : Subgroup (MulAut V))
    (φ : ↥G ≃* SLm F) : Representation (ZMod 2) (SLm F) (Additive V) where
  toFun s := AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun w => Additive.ofMul (((φ.symm s : ↥G) : MulAut V) (Additive.toMul w)))
      (fun a b => by simp [map_mul]))
  map_one' := by
    ext w
    simp
  map_mul' s t := by
    ext w
    simp [map_mul]

theorem m3Rep_apply [Module (ZMod 2) (Additive V)] (G : Subgroup (MulAut V)) (φ : ↥G ≃* SLm F)
    (g : ↥G) (w : Additive V) :
    m3Rep G φ (φ g) w = Additive.ofMul ((g : MulAut V) (Additive.toMul w)) := by
  simp [m3Rep]

theorem m3_addSubgroup_simple [Module (ZMod 2) (Additive V)] (G : Subgroup (MulAut V))
    (φ : ↥G ≃* SLm F) (hirr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤) :
    ∀ U : AddSubgroup (Additive V), (∀ s, ∀ w ∈ U, m3Rep G φ s w ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  let A : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ U}
      mul_mem' := fun {a b} ha hb => U.add_mem ha hb
      one_mem' := U.zero_mem
      inv_mem' := fun {a} ha => U.neg_mem ha }
  have hA : GInv G A := by
    intro g hg a ha
    have := hU (φ ⟨g, hg⟩) (Additive.ofMul a) ha
    rw [m3Rep_apply] at this
    exact this
  rcases hirr A hA with h | h
  · left
    refine (AddSubgroup.eq_bot_iff_forall U).mpr fun w hw => ?_
    have : Additive.toMul w ∈ A := by
      show Additive.ofMul (Additive.toMul w) ∈ U
      exact hw
    rw [h, Subgroup.mem_bot] at this
    exact Additive.toMul.injective this
  · right
    refine (AddSubgroup.eq_top_iff' U).mpr fun w => ?_
    have : Additive.toMul w ∈ A := by rw [h]; trivial
    exact this

theorem m3_isSimpleModule [Module (ZMod 2) (Additive V)] [Nontrivial V] (G : Subgroup (MulAut V))
    (φ : ↥G ≃* SLm F)
    (hU : ∀ U : AddSubgroup (Additive V), (∀ s, ∀ w ∈ U, m3Rep G φ s w ∈ U) → U = ⊥ ∨ U = ⊤) :
    IsSimpleModule (MonoidAlgebra (ZMod 2) (SLm F)) (m3Rep G φ).asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have hne : (⊥ : Subrepresentation (m3Rep G φ)) ≠ ⊤ := by
    intro h
    have h1 : Additive.ofMul v ∈ (⊥ : Subrepresentation (m3Rep G φ)).toSubmodule := by
      rw [h]; trivial
    have h2 : Additive.ofMul v = 0 := (Submodule.mem_bot (ZMod 2)).mp h1
    exact hv (Additive.ofMul.injective h2)
  exact
    { exists_pair_ne := ⟨⊥, ⊤, hne⟩
      eq_bot_or_eq_top := fun U => by
        rcases hU U.toSubmodule.toAddSubgroup
          (fun s w hw => U.apply_mem_toSubmodule s hw) with h | h
        · left
          refine Subrepresentation.ext ?_
          ext w
          constructor
          · intro hw
            have : w ∈ U.toSubmodule.toAddSubgroup := hw
            rw [h] at this
            exact this
          · intro hw
            have : w = 0 := (Submodule.mem_bot (ZMod 2)).mp hw
            rw [this]
            exact U.toSubmodule.zero_mem
        · right
          refine Subrepresentation.ext ?_
          ext w
          constructor
          · intro _
            trivial
          · intro _
            have : w ∈ U.toSubmodule.toAddSubgroup := by rw [h]; trivial
            exact this }

theorem m3_isNatSectionBy_of_equiv (G : Subgroup (MulAut V)) {S : Type} [Group S] (θ : ↥G ≃* S)
    {M : Type} [AddCommGroup M] (act : S → M → M) (e : M ≃+ Additive V)
    (he : ∀ (g : ↥G) (u : M),
      e (act (θ g) u) = Additive.ofMul ((g : MulAut V) (Additive.toMul (e u)))) :
    IsNatSectionBy (fun (s : S) (u : Multiplicative M) =>
      Multiplicative.ofAdd (act s (Multiplicative.toAdd u))) G ⊤ ⊥ := by
  refine ⟨fun _ _ _ _ => trivial, θ, ?_⟩
  refine ⟨
    { toFun := fun p => Multiplicative.ofAdd (e.symm (Additive.ofMul (p : V)))
      map_one' := by simp
      map_mul' := fun p q => by simp [← ofAdd_add] }, ?_, ?_, ?_⟩
  · intro u
    exact ⟨⟨Additive.toMul (e (Multiplicative.toAdd u)), trivial⟩, by simp⟩
  · ext p
    simp only [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.mem_subgroupOf,
      Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : e.symm (Additive.ofMul (p : V)) = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa using this
      have h2 : Additive.ofMul (p : V) = 0 := by simpa using congrArg e h1
      exact Additive.ofMul.injective h2
    · intro h
      rw [h]
      simp
  · intro x p hp
    have h1 := he x (e.symm (Additive.ofMul (p : V)))
    rw [AddEquiv.apply_symm_apply] at h1
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    have h2 : e.symm (Additive.ofMul ((x : MulAut V) (p : V))) =
        act (θ x) (e.symm (Additive.ofMul (p : V))) := by
      apply e.injective
      rw [AddEquiv.apply_symm_apply, h1]
      rfl
    show Multiplicative.ofAdd (e.symm (Additive.ofMul ((x : MulAut V) (p : V)))) =
      Multiplicative.ofAdd (act (θ x) (e.symm (Additive.ofMul (p : V))))
    rw [h2]

end Translate

section Final

theorem l2_two_pow_two_mul_le_card (m : ℕ) (hm : 1 ≤ m) (V : Type) [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V))
    (hG : Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)))
    (hirr : ∀ A : Subgroup V, GInv G A → A = ⊥ ∨ A = ⊤)
    (hnt : ∃ g ∈ G, ∃ v : V, g v ≠ v) : 2 ^ (2 * m) ≤ Nat.card V := by
  obtain ⟨φ⟩ := hG
  let _inst : Module (ZMod 2) (Additive V) := m3Module hV
  have hnV : Nontrivial V := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    obtain ⟨g, -, v, hv⟩ := hnt
    exact hv (Subsingleton.elim _ _)
  have hmf : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hnt' : ∃ g, m3Rep G φ g ≠ 1 := by
    obtain ⟨g, hg, v, hv⟩ := hnt
    refine ⟨φ ⟨g, hg⟩, fun h => hv ?_⟩
    have := LinearMap.congr_fun h (Additive.ofMul v)
    rw [m3Rep_apply] at this
    exact Additive.ofMul.injective this
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hU := m3_addSubgroup_simple G φ hirr
  have hW := m3_isSimpleModule G φ hU
  have hle := m3_two_mul_le_finrank (m3Rep G φ) hm hF hW hnt'
  have hcardW : Nat.card (Additive V) = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V), Nat.card_zmod]
  have hcardV : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
  rw [← hcardV, hcardW]
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem l2SmallModules_holds : L2SmallModules := by
  intro m hm V _ _ hV G hGiso hirr hcard
  obtain ⟨φ⟩ := hGiso
  let _inst : Module (ZMod 2) (Additive V) := m3Module hV
  by_cases hnt : Nontrivial V
  swap
  · left
    intro g _ v
    exact (not_nontrivial_iff_subsingleton.mp hnt).elim _ _
  have hmf : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  by_cases hact : ∀ s w, m3Rep G φ s w = w
  · left
    intro g hg v
    have := hact (φ ⟨g, hg⟩) (Additive.ofMul v)
    rw [m3Rep_apply] at this
    exact Additive.ofMul.injective this
  right
  push Not at hact
  have hnt' : ∃ g, m3Rep G φ g ≠ 1 := by
    obtain ⟨s, w, hw⟩ := hact
    exact ⟨s, fun h => hw (by rw [h]; rfl)⟩
  have hn : 0 < m := by omega
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hU := m3_addSubgroup_simple G φ hirr
  have hW := m3_isSimpleModule G φ hU
  have hcardW : Nat.card (Additive V) = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V), Nat.card_zmod]
  have hcardV : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
  have hfin : Module.finrank (ZMod 2) (Additive V) ≤ 2 * m := by
    have h1 : 2 ^ Module.finrank (ZMod 2) (Additive V) ≤ 2 ^ (2 * m) := by
      rw [← hcardW, hcardV]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  obtain ⟨hdim, hshape⟩ := m3_shape_data (m3Rep G φ) hn hF hW hnt' hfin
  rcases hshape with ⟨N, ⟨ι⟩⟩ | ⟨k, hk, hk0, N, ⟨ι⟩⟩
  · left
    obtain ⟨T, hT, hT0⟩ := m3_natural_hom (m3Rep G φ) hn hF ι
    have hM : Nat.card (Fin 2 → GaloisField 2 m) = 2 ^ (2 * m) := by
      rw [Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm]
    have hbij := m3_bijective_of_hom (m3Rep G φ)
      (fun (s : SLm (GaloisField 2 m)) (u : Fin 2 → GaloisField 2 m) =>
        (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec u) T hT hT0 hU
      (by rw [hM, hcardW, hdim])
    exact m3_isNatSectionBy_of_equiv G φ
      (fun (s : SLm (GaloisField 2 m)) (u : Fin 2 → GaloisField 2 m) =>
        (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)).mulVec u)
      (AddEquiv.ofBijective T hbij) (fun g u => by
        show T _ = _
        rw [hT, m3Rep_apply]
        rfl)
  · right
    subst hk
    have : NeZero k := ⟨by omega⟩
    obtain ⟨T, hT, hT0⟩ := m3_herm_hom (m3Rep G φ) hF ι
    have hbij := m3_bijective_of_hom (m3Rep G φ)
      (fun (s : SLm (Fq (2 * k))) (M : ↥(hermSub k)) =>
        (⟨(s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * M.1 *
          cstar k (s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))), herm_act_mem k s M⟩ :
            ↥(hermSub k))) T hT hT0 hU
      (by rw [card_hermSub, hcardW, hdim]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨k, rfl, ?_⟩
    have hact' : omegaMinusAct k = fun (s : SLm (Fq (2 * k))) (u : Multiplicative ↥(hermSub k)) =>
        Multiplicative.ofAdd
          (⟨(s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * (Multiplicative.toAdd u).1 *
            cstar k (s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))),
              herm_act_mem k s (Multiplicative.toAdd u)⟩ : ↥(hermSub k)) := by
      funext s u
      rw [omegaMinusAct_eq]
      rfl
    rw [hact']
    exact m3_isNatSectionBy_of_equiv G φ
      (fun (s : SLm (Fq (2 * k))) (M : ↥(hermSub k)) =>
        (⟨(s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * M.1 *
          cstar k (s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))), herm_act_mem k s M⟩ :
            ↥(hermSub k)))
      (AddEquiv.ofBijective T hbij) (fun g M => by
        show T _ = _
        rw [hT, m3Rep_apply]
        rfl)

end Final

end CFSG.CGT.PushingUpLit.CGT6
