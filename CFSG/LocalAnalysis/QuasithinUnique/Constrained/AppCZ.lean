
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_pCore_iff_mem_blockQ (x : ↥L) : x ∈ CFSG.pCore 2 L ↔ (x : G) ∈ blockQ L := by
  show x ∈ CFSG.pCore 2 L ↔ (x : G) ∈ pCoreOf 2 L
  unfold pCoreOf
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

omit [Finite G] in
theorem isElemAbelian_blockU (hL : IsShort2 L) : IsElemAbelian 2 (blockU L) :=
  C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hL)

instance instFactSqIntMod {V : Subgroup G} {hV : IsElemAbelian 2 V} :
    Fact (∀ w : IntMod V hV, w * w = 1) :=
  ⟨fun w => by rw [← pow_two]; exact IntMod.sq_eq_one w⟩

theorem blockZ_eq_bot_of_alt5 (hL : IsShort2 L) (h5 : IsAltType L 5) : blockZ L = ⊥ := by
  classical
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := h5
  have hU : IsElemAbelian 2 (blockU L) := isElemAbelian_blockU hL
  have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
  let κ : ↥L →* MulAut (IntMod (blockU L) hU) := (convI hU).comp (Subgroup.inclusion hLN)
  let ρ₀ : ↥L →* (Additive (IntMod (blockU L) hU) ≃ₗ[ZMod 2] Additive (IntMod (blockU L) hU)) :=
    Family.binaryLin.comp κ
  have hker : α.ker ≤ ρ₀.ker := by
    intro ℓ hℓ
    rw [hαk] at hℓ
    have hQ : (ℓ : G) ∈ blockQ L := (mem_pCore_iff_mem_blockQ ℓ).1 hℓ
    rw [MonoidHom.mem_ker]
    have h1 : κ ℓ = 1 :=
      (convI_eq_one_iff hU (Subgroup.inclusion hLN ℓ)).2
        (Subgroup.mem_centralizer_iff.2 fun u hu => C1.blockU_comm hL u hu ℓ hQ)
    simp only [ρ₀, MonoidHom.comp_apply, h1, map_one]
  let ρ' : ↥(alternatingGroup (Fin 5)) →*
      (Additive (IntMod (blockU L) hU) ≃ₗ[ZMod 2] Additive (IntMod (blockU L) hU)) :=
    α.liftOfSurjective hα ⟨ρ₀, hker⟩
  have hρ' : ∀ ℓ : ↥L, ρ' (α ℓ) = ρ₀ ℓ := fun ℓ =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨ρ₀, hker⟩ ℓ
  let ρ : Representation (ZMod 2) ↥(alternatingGroup (Fin 5))
      (Additive (IntMod (blockU L) hU)) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp ρ'
  have hρval : ∀ (ℓ : ↥L) (e : Additive (IntMod (blockU L) hU)),
      (Additive.toMul (ρ (α ℓ) e)).val = (ℓ : G) * (Additive.toMul e).val * (ℓ : G)⁻¹ := by
    intro ℓ e
    show (Additive.toMul (ρ' (α ℓ) e)).val = _
    rw [hρ' ℓ]
    exact convI_apply_val hU (Subgroup.inclusion hLN ℓ) (Additive.toMul e)
  let π₀ : Additive (IntMod (blockU L) hU) →+ ↥(SL2Modules.evenWeight (Fin 5)) :=
    { toFun := fun e => ⟨((Multiplicative.toAdd (β (Additive.toMul e : ↥(blockU L))) :
        ↥(evenWeight 5)) : Fin 5 → ZMod 2), (Multiplicative.toAdd (β (Additive.toMul e :
        ↥(blockU L)))).2⟩
      map_zero' := by
        apply Subtype.ext
        show ((Multiplicative.toAdd (β (1 : ↥(blockU L))) : ↥(evenWeight 5)) :
          Fin 5 → ZMod 2) = 0
        rw [map_one]
        rfl
      map_add' := fun e e' => by
        apply Subtype.ext
        show ((Multiplicative.toAdd (β ((Additive.toMul e : ↥(blockU L)) *
          (Additive.toMul e' : ↥(blockU L)))) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) = _
        rw [map_mul]
        rfl }
  let π : Additive (IntMod (blockU L) hU) →ₗ[ZMod 2] ↥(SL2Modules.evenWeight (Fin 5)) :=
    { toFun := π₀
      map_add' := π₀.map_add
      map_smul' := fun c e => by
        rcases SL2Modules.zmod2_cases c with rfl | rfl
        · simp only [zero_smul, map_zero]
        · simp only [one_smul, RingHom.id_apply] }
  have hπapp : ∀ e, ((π e : ↥(SL2Modules.evenWeight (Fin 5))) : Fin 5 → ZMod 2) =
      ((Multiplicative.toAdd (β (Additive.toMul e : ↥(blockU L))) : ↥(evenWeight 5)) :
        Fin 5 → ZMod 2) := fun e => rfl
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd
      (⟨(x : Fin 5 → ZMod 2), x.2⟩ : ↥(evenWeight 5)))
    refine ⟨Additive.ofMul (IntMod.mk hU u), Subtype.ext ?_⟩
    rw [hπapp]
    show ((Multiplicative.toAdd (β u) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) = _
    rw [hu]
    rfl
  have hπ : ∀ (s : ↥(alternatingGroup (Fin 5))) (e : Additive (IntMod (blockU L) hU)),
      π (ρ s e) = SL2Modules.deletedRep (alternatingGroup (Fin 5)) (Fin 5) s (π e) := by
    intro s e
    obtain ⟨ℓ, rfl⟩ := hα s
    apply Subtype.ext
    funext i
    rw [hπapp, SL2Modules.deletedRep_apply]
    exact hβe ℓ (Additive.toMul e : ↥(blockU L)) (Additive.toMul (ρ (α ℓ) e) : ↥(blockU L))
      (hρval ℓ e) i
  have hfix : ∀ (s : ↥(alternatingGroup (Fin 5))) (e : Additive (IntMod (blockU L) hU)),
      π e = 0 → ρ s e = e := by
    intro s e he
    obtain ⟨ℓ, rfl⟩ := hα s
    have h1 : β (Additive.toMul e : ↥(blockU L)) = 1 := by
      have h0 : (Multiplicative.toAdd (β (Additive.toMul e : ↥(blockU L))) : ↥(evenWeight 5)) =
          0 := by
        apply Subtype.ext
        exact congrArg Subtype.val he
      exact Multiplicative.toAdd.injective h0
    have h2 : (Additive.toMul e : ↥(blockU L)) ∈ β.ker := h1
    rw [hβk] at h2
    have hz : ((Additive.toMul e : ↥(blockU L)) : G) ∈ blockZ L := h2
    have hc := Subgroup.mem_centralizer_iff.1 hz.2 ℓ ℓ.2
    apply Additive.toMul.injective
    apply IntMod.val_injective
    rw [hρval]
    show (ℓ : G) * ((Additive.toMul e : ↥(blockU L)) : G) * (ℓ : G)⁻¹ = _
    rw [hc, mul_inv_cancel_right]
    rfl
  have hgen : Submodule.span (ZMod 2) (Set.range fun p : ↥(alternatingGroup (Fin 5)) ×
      Additive (IntMod (blockU L) hU) => ρ p.1 p.2 - p.2) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    set S₀ := Submodule.span (ZMod 2) (Set.range fun p : ↥(alternatingGroup (Fin 5)) ×
      Additive (IntMod (blockU L) hU) => ρ p.1 p.2 - p.2) with hS₀
    have key : ∀ x ∈ ⁅blockU L, L⁆, ∃ hx : x ∈ blockU L,
        Additive.ofMul (IntMod.mk hU ⟨x, hx⟩) ∈ S₀ := by
      intro x hx
      rw [Subgroup.commutator_def] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨u, hu, ℓ, hℓ, rfl⟩ := hx
        have hmem : ⁅u, ℓ⁆ ∈ blockU L :=
          C1.commutator_blockU_le L (Subgroup.commutator_mem_commutator hu hℓ)
        refine ⟨hmem, ?_⟩
        have hsp : ρ (α ⟨ℓ, hℓ⟩) (Additive.ofMul (IntMod.mk hU ⟨u, hu⟩)) -
            Additive.ofMul (IntMod.mk hU ⟨u, hu⟩) ∈ S₀ :=
          Submodule.subset_span ⟨(α ⟨ℓ, hℓ⟩, Additive.ofMul (IntMod.mk hU ⟨u, hu⟩)), rfl⟩
        have h3 := S₀.neg_mem hsp
        convert h3 using 1
        apply Additive.toMul.injective
        apply IntMod.val_injective
        have h4 := hρval ⟨ℓ, hℓ⟩ (Additive.ofMul (IntMod.mk hU ⟨u, hu⟩))
        have h5 : ((Additive.toMul (-(ρ (α ⟨ℓ, hℓ⟩) (Additive.ofMul (IntMod.mk hU ⟨u, hu⟩)) -
            Additive.ofMul (IntMod.mk hU ⟨u, hu⟩))) : IntMod (blockU L) hU)).val =
            u * ((Additive.toMul (ρ (α ⟨ℓ, hℓ⟩) (Additive.ofMul (IntMod.mk hU ⟨u, hu⟩)))).val)⁻¹ := by
          simp only [toMul_neg, toMul_sub, toMul_ofMul, div_eq_mul_inv, mul_inv_rev, inv_inv,
            IntMod.val_mul, IntMod.val_inv]
          rfl
        show u * ℓ * u⁻¹ * ℓ⁻¹ = _
        rw [h5, h4]
        show u * ℓ * u⁻¹ * ℓ⁻¹ = u * ((ℓ : G) * u * (ℓ : G)⁻¹)⁻¹
        group
      | one =>
        refine ⟨one_mem _, ?_⟩
        have h0 : Additive.ofMul (IntMod.mk hU ⟨1, one_mem _⟩) = 0 := rfl
        rw [h0]
        exact S₀.zero_mem
      | mul x y hx hy ihx ihy =>
        obtain ⟨hx', ih1⟩ := ihx
        obtain ⟨hy', ih2⟩ := ihy
        refine ⟨mul_mem hx' hy', ?_⟩
        have e : Additive.ofMul (IntMod.mk hU ⟨x * y, mul_mem hx' hy'⟩) =
            Additive.ofMul (IntMod.mk hU ⟨x, hx'⟩) + Additive.ofMul (IntMod.mk hU ⟨y, hy'⟩) := rfl
        rw [e]
        exact S₀.add_mem ih1 ih2
      | inv x hx ih =>
        obtain ⟨hx', ih1⟩ := ih
        refine ⟨inv_mem hx', ?_⟩
        have e : Additive.ofMul (IntMod.mk hU ⟨x⁻¹, inv_mem hx'⟩) =
            -Additive.ofMul (IntMod.mk hU ⟨x, hx'⟩) := rfl
        rw [e]
        exact S₀.neg_mem ih1
    obtain ⟨hx, h⟩ := key (Additive.toMul e : ↥(blockU L)).1 (by
      rw [C1.commutator_blockU hL]
      exact (Additive.toMul e : ↥(blockU L)).2)
    have e' : Additive.ofMul (IntMod.mk hU ⟨(Additive.toMul e : ↥(blockU L)).1, hx⟩) = e := rfl
    rw [e'] at h
    exact h
  have hres := SL2Modules.deleted_five_quotient_kernel_trivial (Ω := Fin 5) (Fintype.card_fin 5)
    ρ π hπs hπ hfix hgen
  rw [eq_bot_iff]
  intro z hz
  have hzU : z ∈ blockU L := hz.1
  have hβz : β ⟨z, hzU⟩ = 1 := by
    have hmem : (⟨z, hzU⟩ : ↥(blockU L)) ∈ β.ker := by
      rw [hβk]
      exact hz
    exact hmem
  have hπz : π (Additive.ofMul (IntMod.mk hU ⟨z, hzU⟩)) = 0 := by
    apply Subtype.ext
    rw [hπapp]
    show ((Multiplicative.toAdd (β ⟨z, hzU⟩) : ↥(evenWeight 5)) : Fin 5 → ZMod 2) = 0
    rw [hβz]
    rfl
  have hker0 : Additive.ofMul (IntMod.mk hU ⟨z, hzU⟩) ∈ LinearMap.ker π := hπz
  rw [hres.1, Submodule.mem_bot] at hker0
  have h1 : (⟨z, hzU⟩ : ↥(blockU L)) = 1 := Additive.ofMul.injective hker0
  have h2 : z = 1 := congrArg Subtype.val h1
  rw [h2]
  exact Subgroup.one_mem _

end CFSG.QuasithinUnique.AppC
