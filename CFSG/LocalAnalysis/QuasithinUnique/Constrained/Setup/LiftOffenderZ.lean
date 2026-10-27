module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem deleted_Z_trivial {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (hsec : ComponentSection L A I) {n : ℕ} {F : Type} [Field F]
    [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
    (θ : ↥(Lbar L A I hsec.A_norm (isInvariant_sup_subgroup hsec.inv_L hsec.inv_A)) ≃* SL(2, F))
    (hDel : DeletedAlt n (Lbar L A I hsec.A_norm (isInvariant_sup_subgroup hsec.inv_L hsec.inv_A))
      (Abar L A I hsec.A_norm (isInvariant_sup_subgroup hsec.inv_L hsec.inv_A)) θ) :
    I ⊓ fixGL L = ⊥ := by
  classical
  set hI := isInvariant_sup_subgroup hsec.inv_L hsec.inv_A with hIdef
  set R := actOn L A I hsec.A_norm hI L le_sup_left with hR
  set L₀ := Lbar L A I hsec.A_norm hI with hL₀
  set A₀ := Abar L A I hsec.A_norm hI with hA₀
  obtain ⟨-, -, hΩ5, ψ, β, -, hψ2, hψ3, -⟩ := hDel
  let resI : ↥L →* (↥I ≃ₗ[ZMod 2] ↥I) :=
    (resSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I hI).comp (Subgroup.inclusion le_sup_left)
  let j : ↥L →* ↥(L₀ ⊔ A₀) :=
    (Subgroup.inclusion (le_sup_left : L₀ ≤ L₀ ⊔ A₀)).comp R.rangeRestrict
  have hjval : ∀ l : ↥L, ((j l : ↥(L₀ ⊔ A₀)) : (↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I)) = R l :=
    fun l => rfl
  have hjmem : ∀ l : ↥L, ψ (j l) ∈ alternatingGroup (ℙ F (Fin 2 → F)) := by
    intro l
    rw [← hψ3]
    exact ⟨j l, ⟨l, rfl⟩, rfl⟩
  let q : ↥L →* ↥(alternatingGroup (ℙ F (Fin 2 → F))) :=
    (ψ.toMonoidHom.comp j).codRestrict _ hjmem
  have hqval : ∀ l : ↥L, ((q l : ↥(alternatingGroup (ℙ F (Fin 2 → F)))) :
      Equiv.Perm (ℙ F (Fin 2 → F))) = ψ (j l) := fun l => rfl
  have hqsurj : Function.Surjective q := by
    intro s
    have hs : (s : Equiv.Perm (ℙ F (Fin 2 → F))) ∈
        (L₀.subgroupOf (L₀ ⊔ A₀)).map ψ.toMonoidHom := by
      rw [hψ3]
      exact s.2
    obtain ⟨y, hy, hys⟩ := hs
    obtain ⟨l, hl⟩ := hy
    refine ⟨l, Subtype.ext ?_⟩
    have : j l = y := Subtype.ext hl
    show ψ (j l) = s
    rw [this]
    exact hys
  have hker : q.ker ≤ resI.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : ψ (j l) = 1 := congrArg Subtype.val hl
    have h2 : j l = 1 := ψ.injective (by rw [h1, map_one])
    have h3 : R l = 1 := by
      have := congrArg (fun y : ↥(L₀ ⊔ A₀) => (y : (↥I ⧸ fixIn L I) ≃ₗ[ZMod 2] (↥I ⧸ fixIn L I))) h2
      exact this
    exact hsec.inj ⟨l, Subgroup.mem_sup_left l.2⟩ h3
  let ρ' : ↥(alternatingGroup (ℙ F (Fin 2 → F))) →* (↥I ≃ₗ[ZMod 2] ↥I) :=
    MonoidHom.liftOfSurjective q hqsurj ⟨resI, hker⟩
  have hρ' : ∀ l, ρ' (q l) = resI l := fun l => by simp [ρ', MonoidHom.liftOfSurjective]
  let ρ : Representation (ZMod 2) ↥(alternatingGroup (ℙ F (Fin 2 → F))) ↥I :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ'
  have hρ : ∀ l e, ρ (q l) e = resI l e := fun l e => by
    show (ρ' (q l)) e = _
    rw [hρ']
  let π : ↥I →ₗ[ZMod 2] ↥(evenWeight (ℙ F (Fin 2 → F))) :=
    β.toLinearMap ∘ₗ (fixIn L I).mkQ
  have hπs : Function.Surjective π := β.surjective.comp (Submodule.mkQ_surjective _)
  have hπ : ∀ (s : ↥(alternatingGroup (ℙ F (Fin 2 → F)))) (e : ↥I),
      π (ρ s e) = deletedRep (alternatingGroup (ℙ F (Fin 2 → F))) (ℙ F (Fin 2 → F)) s (π e) := by
    intro s e
    obtain ⟨l, rfl⟩ := hqsurj s
    rw [hρ]
    apply Subtype.ext
    rw [deletedRep_apply]
    have h1 := actOn_L_mk hsec.A_norm hI l e
    have h2 := hψ2 (j l) (Submodule.Quotient.mk e)
    show ((β ((fixIn L I).mkQ (resI l e)) : ↥(evenWeight (ℙ F (Fin 2 → F)))) :
        ℙ F (Fin 2 → F) → ZMod 2) = permAct (MulAction.toPerm (q l))
        ((β ((fixIn L I).mkQ e) : ↥(evenWeight (ℙ F (Fin 2 → F)))) : ℙ F (Fin 2 → F) → ZMod 2)
    have h3 : (MulAction.toPerm (q l) : Equiv.Perm (ℙ F (Fin 2 → F))) = ψ (j l) := rfl
    rw [h3]
    rw [hjval] at h2
    rw [h1] at h2
    exact h2
  have hfix : ∀ (s : ↥(alternatingGroup (ℙ F (Fin 2 → F)))) (e : ↥I), π e = 0 → ρ s e = e := by
    intro s e he
    obtain ⟨l, rfl⟩ := hqsurj s
    rw [hρ]
    have h0 : (Submodule.Quotient.mk e : ↥I ⧸ fixIn L I) = 0 := by
      have : β ((fixIn L I).mkQ e) = 0 := he
      exact (map_eq_zero_iff β β.injective).1 this
    have hz := (Submodule.Quotient.mk_eq_zero _).1 h0
    apply Subtype.ext
    exact hz l l.2
  have hgen : Submodule.span (ZMod 2)
      (Set.range fun p : ↥(alternatingGroup (ℙ F (Fin 2 → F))) × ↥I => ρ p.1 p.2 - p.2) = ⊤ := by
    apply Submodule.map_injective_of_injective I.injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have himg : (I.subtype : ↥I →ₗ[ZMod 2] V) ''
        (Set.range fun p : ↥(alternatingGroup (ℙ F (Fin 2 → F))) × ↥I => ρ p.1 p.2 - p.2) =
        {w | ∃ b ∈ L, ∃ u ∈ I, w = (MonoidHom.id (V ≃ₗ[ZMod 2] V)) b u - u} := by
      ext w
      constructor
      · rintro ⟨_, ⟨⟨s, e⟩, rfl⟩, rfl⟩
        obtain ⟨l, rfl⟩ := hqsurj s
        refine ⟨l, l.2, e, e.2, ?_⟩
        show ((ρ (q l) e - e : ↥I) : V) = _
        rw [hρ]
        rfl
      · rintro ⟨b, hb, u, hu, rfl⟩
        refine ⟨ρ (q ⟨b, hb⟩) ⟨u, hu⟩ - ⟨u, hu⟩, ⟨(q ⟨b, hb⟩, ⟨u, hu⟩), rfl⟩, ?_⟩
        show ((ρ (q ⟨b, hb⟩) ⟨u, hu⟩ - ⟨u, hu⟩ : ↥I) : V) = _
        rw [hρ]
        rfl
    rw [himg]
    exact hsec.comm
  obtain ⟨hkerπ, -⟩ := deleted_five_quotient_kernel_trivial hΩ5 ρ π hπs hπ hfix hgen
  rw [eq_bot_iff]
  intro z hz
  have hz' : (⟨z, hz.1⟩ : ↥I) ∈ LinearMap.ker π := by
    rw [LinearMap.mem_ker]
    have : (Submodule.Quotient.mk ⟨z, hz.1⟩ : ↥I ⧸ fixIn L I) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hz.2
    show β ((fixIn L I).mkQ ⟨z, hz.1⟩) = 0
    rw [Submodule.mkQ_apply, this, map_zero]
  rw [hkerπ] at hz'
  exact congrArg Subtype.val ((Submodule.mem_bot _).1 hz')

end CFSG.QuasithinUnique.Setup.Lift
