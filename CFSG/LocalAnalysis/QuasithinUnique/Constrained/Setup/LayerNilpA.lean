module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem isSubnormal_subgroupOf_subgroupOf_iff' {X : Type*} [Group X] {B L K : Subgroup X}
    (hLK : L ≤ K) :
    ((B.subgroupOf K).subgroupOf (L.subgroupOf K)).IsSubnormal ↔
      (B.subgroupOf L).IsSubnormal := by
  let e : L.subgroupOf K ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  constructor
  · intro h
    have h' := h.comap e.symm.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl
  · intro h
    have h' := h.comap e.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl

theorem isSubnormal_trans {X : Type*} [Group X] {B L K : Subgroup X} (hBL : B ≤ L) (hLK : L ≤ K)
    (hB : (B.subgroupOf L).IsSubnormal) (hL : (L.subgroupOf K).IsSubnormal) :
    (B.subgroupOf K).IsSubnormal :=
  Subgroup.IsSubnormal.trans (fun _ hz => hBL hz)
    ((isSubnormal_subgroupOf_subgroupOf_iff' (B := B) hLK).mpr hB) hL

@[expose] def conjAction (Fn A : Subgroup (V ≃ₗ[k] V))
    (hA : A ≤ Subgroup.normalizer (Fn : Set (V ≃ₗ[k] V))) : ↥A →* MulAut ↥Fn :=
  Fn.normalizerMonoidHom.comp (Subgroup.inclusion hA)

theorem conjAction_apply_coe (Fn A : Subgroup (V ≃ₗ[k] V))
    (hA : A ≤ Subgroup.normalizer (Fn : Set (V ≃ₗ[k] V))) (a : ↥A) (x : ↥Fn) :
    ((conjAction Fn A hA a x : ↥Fn) : V ≃ₗ[k] V) = (a : V ≃ₗ[k] V) * x * (a : V ≃ₗ[k] V)⁻¹ :=
  rfl

variable [Finite V]

theorem exists_cyclic_invariant {G Fn A : Subgroup (V ≃ₗ[k] V)} (hFG : Fn ≤ G) (hAG : A ≤ G)
    (hFn : (Fn.subgroupOf G).Normal) [Group.IsNilpotent ↥Fn] (hodd : Odd (Nat.card Fn))
    (hAel : CFSG.IsElementaryAbelian 2 A) (hcomm : ⁅Fn, A⁆ ≠ ⊥) :
    (∃ C : Subgroup (V ≃ₗ[k] V), C ≤ Fn ∧ IsCyclic C ∧
      A ≤ Subgroup.normalizer (C : Set (V ≃ₗ[k] V)) ∧ ⁅C, A⁆ ≠ ⊥) ∧
    ∀ U : Subgroup (V ≃ₗ[k] V), U ≤ Fn → (U.subgroupOf Fn).IsSubnormal := by
  have hFnorm : A ≤ Subgroup.normalizer (Fn : Set (V ≃ₗ[k] V)) :=
    hAG.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hFG).1 hFn)
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have : Finite ↥Fn := inferInstance
  have : Finite ↥A := inferInstance
  have : CFSG.IsElementaryAbelian 2 ↥A := hAel
  have hφ : conjAction Fn A hFnorm ≠ 1 := by
    intro h1
    apply hcomm
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx a ha
    have e : conjAction Fn A hFnorm ⟨a, ha⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [h1]
      rfl
    have e2 : a * x * a⁻¹ = x := congrArg Subtype.val e
    have e3 : a * x = x * a := mul_inv_eq_iff_eq_mul.1 e2
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 e3.symm
  obtain ⟨⟨C, hC0, hCcyc, hCinv, -, hCcomm⟩, hsub⟩ :=
    elementary_two_action_on_odd_nilpotent_detects_invariant_cyclic_subgroup hodd
      (conjAction Fn A hFnorm) hφ
  refine ⟨⟨C.map Fn.subtype, Subgroup.map_subtype_le C, ?_, ?_, ?_⟩, fun U hU => hsub (U.subgroupOf Fn)⟩
  · have e := C.equivMapOfInjective Fn.subtype Fn.subtype_injective
    exact isCyclic_of_surjective e e.surjective
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ b ∈ A, ∀ y ∈ C.map Fn.subtype, b * y * b⁻¹ ∈ C.map Fn.subtype := by
      intro b hb y hy
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨conjAction Fn A hFnorm ⟨b, hb⟩ c, hCinv ⟨b, hb⟩ c hc, rfl⟩
    intro y
    constructor
    · exact key a ha y
    · intro hy
      have := key a⁻¹ (A.inv_mem ha) _ hy
      simpa [mul_assoc] using this
  · intro hbot
    apply hCcomm
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨a, c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    apply Subtype.ext
    have h1 : ((a : V ≃ₗ[k] V) * (c : V ≃ₗ[k] V) * (a : V ≃ₗ[k] V)⁻¹ * (c : V ≃ₗ[k] V)⁻¹) ∈
        (⁅C.map Fn.subtype, A⁆ : Subgroup (V ≃ₗ[k] V)) := by
      have hc' : (c : V ≃ₗ[k] V) ∈ C.map Fn.subtype := ⟨c, hc, rfl⟩
      have := Subgroup.commutator_mem_commutator hc' a.2
      have h2 := (⁅C.map Fn.subtype, A⁆ : Subgroup (V ≃ₗ[k] V)).inv_mem this
      rw [commutatorElement_def] at h2
      simpa [mul_assoc] using h2
    rw [hbot] at h1
    have h3 : ((a : V ≃ₗ[k] V) * (c : V ≃ₗ[k] V) * (a : V ≃ₗ[k] V)⁻¹ * (c : V ≃ₗ[k] V)⁻¹) = 1 :=
      Subgroup.mem_bot.1 h1
    show ((conjAction Fn A hFnorm a c * c⁻¹ : ↥Fn) : V ≃ₗ[k] V) = 1
    have h4 : ((conjAction Fn A hFnorm a c * c⁻¹ : ↥Fn) : V ≃ₗ[k] V) =
        (a : V ≃ₗ[k] V) * (c : V ≃ₗ[k] V) * (a : V ≃ₗ[k] V)⁻¹ * (c : V ≃ₗ[k] V)⁻¹ := rfl
    rw [h4, h3]

end CFSG.QuasithinUnique.Setup.Layer
