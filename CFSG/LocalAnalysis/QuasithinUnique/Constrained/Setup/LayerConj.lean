module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneMain
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

@[expose] def conjR (g : V ≃ₗ[k] V) (X : Subgroup (V ≃ₗ[k] V)) : Subgroup (V ≃ₗ[k] V) :=
  conjSub g⁻¹ X

theorem mem_conjR {g y : V ≃ₗ[k] V} {X : Subgroup (V ≃ₗ[k] V)} :
    y ∈ conjR g X ↔ g * y * g⁻¹ ∈ X := by
  unfold conjR
  rw [mem_conjSub, inv_inv]

theorem conjSub_conjR (y g : V ≃ₗ[k] V) (X : Subgroup (V ≃ₗ[k] V)) :
    conjSub y (conjR g X) = conjR (g * y⁻¹) X := by
  unfold conjR
  rw [← conjSub_mul, mul_inv_rev, inv_inv]

theorem conjR_one (X : Subgroup (V ≃ₗ[k] V)) : conjR 1 X = X := by
  unfold conjR
  rw [inv_one, conjSub_one]

theorem conjSub_conjSub_inv (x : V ≃ₗ[k] V) (X : Subgroup (V ≃ₗ[k] V)) :
    conjSub x (conjSub x⁻¹ X) = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_inv_conjSub (x : V ≃ₗ[k] V) (X : Subgroup (V ≃ₗ[k] V)) :
    conjSub x⁻¹ (conjSub x X) = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem natCard_conjSub (x : V ≃ₗ[k] V) (X : Subgroup (V ≃ₗ[k] V)) :
    Nat.card ↥(conjSub x X) = Nat.card ↥X :=
  (Nat.card_congr (X.equivMapOfInjective (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).toEquiv).symm

theorem conjSub_mem_of_mem {x : V ≃ₗ[k] V} {X : Subgroup (V ≃ₗ[k] V)} {a : V ≃ₗ[k] V}
    (ha : a ∈ X) : x * a * x⁻¹ ∈ conjSub x X := by
  rw [mem_conjSub]
  simpa [mul_assoc] using ha

theorem gl_inv_apply (x : V ≃ₗ[k] V) (v : V) : x⁻¹ (x v) = v := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem gl_apply_inv (x : V ≃ₗ[k] V) (v : V) : x (x⁻¹ v) = v := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

theorem natCard_map_linearEquiv (x : V ≃ₗ[k] V) (U : Submodule k V) :
    Nat.card ↥(U.map (x : V →ₗ[k] V)) = Nat.card ↥U :=
  (Nat.card_congr (Submodule.equivMapOfInjective (x : V →ₗ[k] V) x.injective U).toEquiv).symm

theorem fixGL_conjSub (x : V ≃ₗ[k] V) (B : Subgroup (V ≃ₗ[k] V)) :
    fixGL (conjSub x B) = (fixGL B).map (x : V →ₗ[k] V) := by
  ext v
  constructor
  · intro hv
    refine ⟨x⁻¹ v, ?_, ?_⟩
    · intro b hb
      have h1 : (x * b * x⁻¹) v = v := hv _ (conjSub_mem_of_mem hb)
      have h2 : x (b (x⁻¹ v)) = v := h1
      have h3 : b (x⁻¹ v) = x⁻¹ v := by
        have := congrArg (fun w => x⁻¹ w) h2
        simpa [gl_inv_apply] using this
      exact h3
    · show x (x⁻¹ v) = v
      exact gl_apply_inv x v
  · rintro ⟨u, hu, rfl⟩ b hb
    rw [mem_conjSub] at hb
    have h1 : (x⁻¹ * b * x) u = u := hu _ hb
    have h2 : x⁻¹ (b (x u)) = u := h1
    have h3 : b (x u) = x u := by
      have := congrArg (fun w => x w) h2
      simpa [gl_apply_inv] using this
    exact h3

theorem weight_conjSub (x : V ≃ₗ[k] V) (B : Subgroup (V ≃ₗ[k] V)) :
    weight (MonoidHom.id (V ≃ₗ[k] V)) (conjSub x B) = weight (MonoidHom.id (V ≃ₗ[k] V)) B := by
  unfold weight
  rw [natCard_conjSub]
  congr 1
  show Nat.card ↥(fixGL (conjSub x B)) = Nat.card ↥(fixGL B)
  rw [fixGL_conjSub]
  exact natCard_map_linearEquiv x (fixGL B)

theorem commutator_conjSub {N A : Subgroup (V ≃ₗ[k] V)} {x : V ≃ₗ[k] V}
    (hx : x ∈ Subgroup.normalizer (N : Set (V ≃ₗ[k] V))) :
    ⁅N, conjSub x A⁆ = conjSub x ⁅N, A⁆ := by
  have h1 : conjSub x N = N := conjSub_eq_self hx
  show ⁅N, A.map (MulAut.conj x).toMonoidHom⁆ = ⁅N, A⁆.map (MulAut.conj x).toMonoidHom
  rw [Subgroup.map_commutator]
  have h2 : N.map (MulAut.conj x).toMonoidHom = N := h1
  rw [h2]

theorem commutator_conjSub_conjSub (x : V ≃ₗ[k] V) (L A : Subgroup (V ≃ₗ[k] V)) :
    ⁅conjSub x L, conjSub x A⁆ = conjSub x ⁅L, A⁆ := by
  show ⁅L.map (MulAut.conj x).toMonoidHom, A.map (MulAut.conj x).toMonoidHom⁆ =
    ⁅L, A⁆.map (MulAut.conj x).toMonoidHom
  rw [Subgroup.map_commutator]

theorem commGL_conjSub (x : V ≃ₗ[k] V) (L : Subgroup (V ≃ₗ[k] V)) :
    commGL (conjSub x L) ⊤ = (commGL L ⊤).map (x : V →ₗ[k] V) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, u, -, rfl⟩
    rw [mem_conjSub] at hy
    refine ⟨(x⁻¹ * y * x) (x⁻¹ u) - x⁻¹ u, mem_commSub_of hy Submodule.mem_top, ?_⟩
    show x ((x⁻¹ * y * x) (x⁻¹ u) - x⁻¹ u) = y u - u
    have e : (x⁻¹ * y * x) (x⁻¹ u) = x⁻¹ (y u) := by
      show x⁻¹ (y (x (x⁻¹ u))) = x⁻¹ (y u)
      rw [gl_apply_inv]
    rw [e, map_sub, gl_apply_inv, gl_apply_inv]
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, u, -, rfl⟩
    show x (b u - u) ∈ commGL (conjSub x L) ⊤
    have e : x (b u - u) = (x * b * x⁻¹) (x u) - x u := by
      show x (b u - u) = x (b (x⁻¹ (x u))) - x u
      rw [gl_inv_apply, map_sub]
    rw [e]
    exact mem_commSub_of (conjSub_mem_of_mem hb) Submodule.mem_top

theorem finrank_map_linearEquiv [Module.Finite k V] (x : V ≃ₗ[k] V) (U : Submodule k V) :
    Module.finrank k ↥(U.map (x : V →ₗ[k] V)) = Module.finrank k ↥U :=
  (Submodule.equivMapOfInjective (x : V →ₗ[k] V) x.injective U).finrank_eq.symm

structure PlaneData (G N A L : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V) : Prop where
  card_k : Nat.card k = 2
  card_A : Nat.card A = 2
  card_L : Nat.card L = 3
  A_le : A ≤ G
  L_le : L ≤ N
  A_norm : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V))
  L_perf : ⁅L, A⁆ = L
  I_eq : I = commGL L ⊤
  finrank_I : Module.finrank k ↥I = 2
  inv_A : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I
  action : ∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I,
    Function.Bijective (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hW)
  V_eq : I ⊔ fixGL A = ⊤
  N_eq : N = L ⊔ (N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V)))
  cent_eq : N ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[k] V)) =
    N ⊓ centSub (MonoidHom.id (V ≃ₗ[k] V)) I

namespace OddAbelianSetting

variable {G N A : Subgroup (V ≃ₗ[k] V)} (h : OddAbelianSetting G N A)

include h

theorem mem_normalizer {x : V ≃ₗ[k] V} (hx : x ∈ G) :
    x ∈ Subgroup.normalizer (N : Set (V ≃ₗ[k] V)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.N_le).1 h.N_normal hx

theorem conj {x : V ≃ₗ[k] V} (hx : x ∈ G) : OddAbelianSetting G N (conjSub x A) where
  N_le := h.N_le
  N_normal := h.N_normal
  N_abelian := h.N_abelian
  N_odd := h.N_odd
  A_le := by
    intro y hy
    rw [mem_conjSub] at hy
    have h1 := h.A_le hy
    have h2 : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [h2]
    exact G.mul_mem (G.mul_mem hx h1) (G.inv_mem hx)
  A_elem := by
    have := h.A_elem
    exact isElementaryAbelian_of_mulEquiv
      (show ↥(conjSub x A) ≃* ↥A from
        (A.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).symm)
      h.A_elem
  A_ne := by
    intro hA
    apply h.A_ne
    apply (conjSub x).injective
    rw [hA]
    exact (conjSub x).map_bot.symm
  offender := by
    rw [weight_conjSub]
    exact h.offender
  strict := by
    intro B hB0 hBA
    have h1 : ⊥ < conjSub x⁻¹ B := by
      have := (conjSub x⁻¹).lt_iff_lt.2 hB0
      rwa [(conjSub x⁻¹).map_bot] at this
    have h2 : conjSub x⁻¹ B < A := by
      have := (conjSub x⁻¹).lt_iff_lt.2 hBA
      rwa [conjSub_inv_conjSub] at this
    have h3 := h.strict _ h1 h2
    have h4 : weight (MonoidHom.id (V ≃ₗ[k] V)) B =
        weight (MonoidHom.id (V ≃ₗ[k] V)) (conjSub x⁻¹ B) := by
      have := weight_conjSub x (conjSub x⁻¹ B)
      rwa [conjSub_conjSub_inv] at this
    rw [h4, weight_conjSub x A]
    exact h3
  comm_ne := by
    rw [commutator_conjSub (h.mem_normalizer hx)]
    intro hc
    apply h.comm_ne
    apply (conjSub x).injective
    rw [hc]
    exact (conjSub x).map_bot.symm

theorem planeData [CharP k 2] [Finite V] {L : Subgroup (V ≃ₗ[k] V)} (hL : ⁅N, A⁆ = L) :
    ∃ I, PlaneData G N A L I := by
  obtain ⟨I, hT⟩ := h.threePlane
  subst hL
  refine ⟨I, ?_⟩
  exact
    { card_k := hT.card_k
      card_A := hT.card_A
      card_L := hT.card_L
      A_le := h.A_le
      L_le := hT.L_le_N
      A_norm := h.A_le_normalizer_L
      L_perf := h.comm_comm
      I_eq := hT.I_eq
      finrank_I := hT.finrank_I
      inv_A := hT.inv_A
      action := hT.action
      V_eq := hT.V_eq
      N_eq := hT.N_eq
      cent_eq := hT.cent_eq }

theorem planeData_conj [CharP k 2] [Finite V] {x : V ≃ₗ[k] V} (hx : x ∈ G) :
    PlaneData G N (conjSub x A) (conjSub x ⁅N, A⁆) (commGL (conjSub x ⁅N, A⁆) ⊤) := by
  obtain ⟨I, hI⟩ := (h.conj hx).planeData (commutator_conjSub (h.mem_normalizer hx))
  have e := hI.I_eq
  subst e
  exact hI

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
