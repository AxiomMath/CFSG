module

public import CFSG.Quasithin.Background.Module
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open scoped Multiplicative

section Dictionary

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem mem_fixGL_map (X : Subgroup (MulAut V)) (v : V) :
    Multiplicative.toAdd (θ v) ∈ fixGL (X.map (binPsi θ).toMonoidHom) ↔ v ∈ fixV X := by
  rw [mem_fixGL, mem_fixV]
  constructor
  · intro h x hx
    have h1 := h ((binPsi θ).toMonoidHom x) ⟨x, hx, rfl⟩
    change binPsi θ x (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ v) at h1
    rw [binPsi_apply] at h1
    simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h1
    exact θ.injective (Multiplicative.toAdd.injective h1)
  · intro h g hg
    obtain ⟨x, hx, rfl⟩ := hg
    change binPsi θ x (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ v)
    rw [binPsi_apply]
    simp [h x hx]

@[expose] def fixEquiv (X : Subgroup (MulAut V)) :
    ↥(fixV X) ≃ ↥(fixGL (X.map (binPsi θ).toMonoidHom)) where
  toFun v := ⟨Multiplicative.toAdd (θ v), (mem_fixGL_map θ X v).2 v.2⟩
  invFun w := ⟨θ.symm (Multiplicative.ofAdd w), (mem_fixGL_map θ X _).1 (by simpa using w.2)⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply Subtype.ext
    simp

theorem natCard_fixGL_map (X : Subgroup (MulAut V)) :
    Nat.card ↥(fixGL (X.map (binPsi θ).toMonoidHom)) = Nat.card ↥(fixV X) :=
  (Nat.card_congr (fixEquiv θ X)).symm

theorem weight_map (X : Subgroup (MulAut V)) :
    weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (X.map (binPsi θ).toMonoidHom) =
      Nat.card ↥X * Nat.card ↥(fixV X) := by
  unfold weight
  rw [Subgroup.card_map_of_injective (binPsi θ).injective]
  exact congrArg (Nat.card ↥X * ·) (natCard_fixGL_map θ X)

omit [Module (ZMod 2) W] in
theorem natCard_eq (θ : V ≃* Multiplicative W) : Nat.card V = Nat.card W :=
  Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)

theorem exists_map_eq (B' : Subgroup (W ≃ₗ[ZMod 2] W)) :
    ∃ B : Subgroup (MulAut V), B.map (binPsi θ).toMonoidHom = B' :=
  ⟨B'.map (binPsi θ).symm.toMonoidHom, by
    have := CFSG.LocalCores.map_map_symm (binPsi θ).symm B'
    simpa using this⟩

end Dictionary

section Elementary

variable {X : Type*} [Group X]

theorem isElementaryAbelian_two_of {A : Subgroup X} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h2 : ∀ a ∈ A, a ^ 2 = 1) : CFSG.IsElementaryAbelian 2 ↥A :=
  CFSG.IsElementaryAbelian.of_forall hc h2

theorem comm_of_isElementaryAbelian_two {A : Subgroup X} (h : CFSG.IsElementaryAbelian 2 ↥A) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem sq_of_isElementaryAbelian_two {A : Subgroup X} (h : CFSG.IsElementaryAbelian 2 ↥A) :
    ∀ a ∈ A, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha

end Elementary

section Offenders

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem isElemAbelian2_iff_map (A : Subgroup (MulAut V)) :
    IsElemAbelian2 A ↔ CFSG.IsElementaryAbelian 2 ↥(A.map (binPsi θ).toMonoidHom) := by
  constructor
  · rintro ⟨hc, h2⟩
    have := isElementaryAbelian_two_of hc h2
    exact isElementaryAbelian_map (binPsi θ).toMonoidHom A
  · intro h
    have h1 := isElementaryAbelian_map (p := 2) (binPsi θ).symm.toMonoidHom
      (A.map (binPsi θ).toMonoidHom)
    have e : (A.map (binPsi θ).toMonoidHom).map (binPsi θ).symm.toMonoidHom = A :=
      CFSG.LocalCores.map_map_symm (binPsi θ) A
    rw [e] at h1
    exact ⟨comm_of_isElementaryAbelian_two h1, sq_of_isElementaryAbelian_two h1⟩

theorem isMinOffender_map_iff (H A : Subgroup (MulAut V)) :
    IsMinOffender (H.map (binPsi θ).toMonoidHom) (A.map (binPsi θ).toMonoidHom) ↔
      (A ≤ H ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧ Nat.card V ≤ Nat.card ↥A * Nat.card ↥(fixV A) ∧
        ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A →
          Nat.card ↥B * Nat.card ↥(fixV B) < Nat.card ↥A * Nat.card ↥(fixV A)) := by
  have hinj := (binPsi θ).injective
  unfold IsMinOffender
  rw [Subgroup.map_le_map_iff_of_injective hinj, Ne, Subgroup.map_eq_bot_iff_of_injective A hinj,
    ← isElemAbelian2_iff_map θ A, weight_map θ A, ← natCard_eq θ]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  constructor
  · intro h B hBA hB hBne
    have h1 : ⊥ < B.map (binPsi θ).toMonoidHom := by
      rw [bot_lt_iff_ne_bot, Ne, Subgroup.map_eq_bot_iff_of_injective B hinj]
      exact hB
    have h2 : B.map (binPsi θ).toMonoidHom < A.map (binPsi θ).toMonoidHom := by
      rw [lt_iff_le_and_ne]
      refine ⟨Subgroup.map_mono hBA, fun heq => hBne ?_⟩
      exact le_antisymm hBA ((Subgroup.map_le_map_iff_of_injective hinj).1 heq.ge)
    have := h _ h1 h2
    rwa [weight_map] at this
  · intro h B' hB'1 hB'2
    obtain ⟨B, rfl⟩ := exists_map_eq θ B'
    rw [weight_map]
    have hle : B ≤ A := (Subgroup.map_le_map_iff_of_injective hinj).1 hB'2.le
    refine h B hle ?_ ?_
    · intro hB
      rw [hB, Subgroup.map_bot] at hB'1
      exact lt_irrefl _ hB'1
    · intro hBA
      rw [hBA] at hB'2
      exact lt_irrefl _ hB'2

end Offenders

section Hyp

variable {V : Type} [CommGroup V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : V ≃* Multiplicative W)

theorem map_hypotheses {H T M E : Subgroup (MulAut V)}
    (ho2 : ∀ N : Subgroup (MulAut V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hsyl : IsSylowTwoOf T H) (hnn : ¬ (T.subgroupOf H).Normal)
    (hmax : T ≤ M ∧ M < H ∧ ∀ X : Subgroup (MulAut V), T ≤ X → X < H → X ≤ M)
    (hE : E ≤ H ∧ E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      Nat.card V ≤ Nat.card ↥E * Nat.card ↥(fixV E)) :
    (∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ H.map (binPsi θ).toMonoidHom →
      (N.subgroupOf (H.map (binPsi θ).toMonoidHom)).Normal → IsPGroup 2 ↥N → N = ⊥) ∧
    IsSylowTwoOf (T.map (binPsi θ).toMonoidHom) (H.map (binPsi θ).toMonoidHom) ∧
    ¬ ((T.map (binPsi θ).toMonoidHom).subgroupOf (H.map (binPsi θ).toMonoidHom)).Normal ∧
    (T.map (binPsi θ).toMonoidHom ≤ M.map (binPsi θ).toMonoidHom ∧
      M.map (binPsi θ).toMonoidHom < H.map (binPsi θ).toMonoidHom ∧
      ∀ X : Subgroup (W ≃ₗ[ZMod 2] W), T.map (binPsi θ).toMonoidHom ≤ X →
        X < H.map (binPsi θ).toMonoidHom → X ≤ M.map (binPsi θ).toMonoidHom) ∧
    (E.map (binPsi θ).toMonoidHom ≤ H.map (binPsi θ).toMonoidHom ∧
      E.map (binPsi θ).toMonoidHom ≠ ⊥ ∧ CFSG.IsElementaryAbelian 2 ↥(E.map (binPsi
          θ).toMonoidHom) ∧
      Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (E.map (binPsi θ).toMonoidHom)) := by
  have hinj := (binPsi θ).injective
  refine ⟨?_, (isSylowTwoOf_map_mulEquiv (binPsi θ)).2 hsyl, ?_, ⟨Subgroup.map_mono hmax.1, ?_, ?_⟩,
    ⟨Subgroup.map_mono hE.1, ?_, ?_, ?_⟩⟩
  · intro N' hN'H hN'n hN'p
    obtain ⟨N, rfl⟩ := exists_map_eq θ N'
    have hNH : N ≤ H := (Subgroup.map_le_map_iff_of_injective hinj).1 hN'H
    have hNp : IsPGroup 2 ↥N :=
      hN'p.of_equiv (N.equivMapOfInjective (binPsi θ).toMonoidHom hinj).symm
    rw [ho2 N hNH ((normal_subgroupOf_map_iff (binPsi θ) hNH).1 hN'n) hNp, Subgroup.map_bot]
  · rw [normal_subgroupOf_map_iff (binPsi θ) hsyl.1]
    exact hnn
  · exact (Subgroup.map_lt_map_iff_of_injective hinj).2 hmax.2.1
  · intro X' hTX hXH
    obtain ⟨X, rfl⟩ := exists_map_eq θ X'
    exact Subgroup.map_mono (hmax.2.2 X ((Subgroup.map_le_map_iff_of_injective hinj).1 hTX)
      ((Subgroup.map_lt_map_iff_of_injective hinj).1 hXH))
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective E hinj]
    exact hE.2.1
  · have := isElementaryAbelian_two_of hE.2.2.1 hE.2.2.2.1
    exact isElementaryAbelian_map (binPsi θ).toMonoidHom E
  · rw [weight_map θ E, ← natCard_eq θ]
    exact hE.2.2.2.2

end Hyp

section Model

theorem exists_binModel_of_binary {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W),
      Nonempty (V ≃* Multiplicative W) := by
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h2 : (Additive.toMul x) ^ 2 = 1 := by
      rw [pow_two]
      exact hV _
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact h2
    exact toMul_eq_one.1 h3
  exact ⟨Additive V, inferInstance, inferInstance, inferInstanceAs (Finite V),
    ⟨(MulEquiv.multiplicativeAdditive V).symm⟩⟩

end Model

end CFSG.QuasithinUnique.Setup.Layer.Actor
