module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLFix
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLTwo

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Matrix

namespace EvenSL

section Rep

variable {F : Type} [Field F]

@[expose] def repHom (G : Subgroup (GL (Fin 3) F)) : G →* Module.End F (Fin 3 → F) :=
  (Matrix.toLinAlgEquiv' (R := F) (n := Fin 3)).toAlgHom.toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin 3) (Fin 3) F)).comp G.subtype)

theorem repHom_apply (G : Subgroup (GL (Fin 3) F)) (g : G) (v : Fin 3 → F) :
    repHom G g v = (g.1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by
  simp [repHom, Matrix.toLinAlgEquiv'_apply]

theorem repHom_injective (G : Subgroup (GL (Fin 3) F)) : Function.Injective (repHom G) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  simpa [Matrix.toLin'_apply, repHom_apply] using LinearMap.congr_fun hgh v

end Rep

theorem commutator_map_eq_one {T E : Type*} [Group T] [Monoid E] (ρ : T →* E)
    (h : ∀ s t, ρ s * ρ t = ρ t * ρ s) (s t : T) : ρ (s * t * s⁻¹ * t⁻¹) = 1 := by
  have : s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
  rw [this, map_mul, map_mul, h s t, ← map_mul, ← map_mul, mul_inv_cancel, map_one]

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem reducible_false {Γ X : Type} [Group Γ] [Finite Γ] [Group X] (hSL : IsSLThreeFour X)
    (ρ : Γ →* Module.End F (Fin 3 → F)) (hρ : Function.Injective ρ) (π : Γ →* X)
    (hπ : Function.Surjective π) (W : Submodule F (Fin 3 → F))
    (hWrep : ∀ g : Γ, ∀ w ∈ W, ρ g w ∈ W) (h0 : W ≠ ⊥) (h1 : W ≠ ⊤) : False := by
  classical
  have hWL : ∀ g : Γ, W ≤ W.comap (ρ g) := fun g w hw => hWrep g w hw
  set ρW := subAct ρ W hWrep with hρW
  set ρQ := qAct ρ W hWL with hρQ
  have hfinV : Module.finrank F (Fin 3 → F) = 3 := by simp
  have hWpos : 1 ≤ Module.finrank F W := Submodule.one_le_finrank_iff.2 h0
  have hWlt : Module.finrank F W < Module.finrank F (Fin 3 → F) := Submodule.finrank_lt h1
  have hQsum := W.finrank_quotient_add_finrank
  have hdW : Module.finrank F W ≤ 2 := by omega
  have hdQ : Module.finrank F ((Fin 3 → F) ⧸ W) ≤ 2 := by omega
  let Q : Subgroup Γ := ρW.ker ⊓ ρQ.ker
  have hQnormal : Q.Normal := inferInstance
  have hQ : ∀ x : Γ, x ∈ Q ↔ (∀ w ∈ W, ρ x w = w) ∧ ∀ v, ρ x v - v ∈ W := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun w hw => ?_, fun v => ?_⟩
      · have := LinearMap.congr_fun (MonoidHom.mem_ker.1 h1) ⟨w, hw⟩
        exact congrArg Subtype.val this
      · have := LinearMap.congr_fun (MonoidHom.mem_ker.1 h2) (Submodule.Quotient.mk v)
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
        simpa [hρQ, qAct_mk] using this
    · rintro ⟨h1, h2⟩
      refine ⟨MonoidHom.mem_ker.2 ?_, MonoidHom.mem_ker.2 ?_⟩
      · refine LinearMap.ext fun w => Subtype.ext ?_
        exact h1 w.1 w.2
      · apply Submodule.linearMap_qext
        refine LinearMap.ext fun v => ?_
        have := h2 v
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero] at this
        change ρQ x (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
        rw [hρQ, qAct_mk]
        exact this
  have hQp : IsPGroup 2 Q := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨hx1, hx2⟩ := (hQ x.1).1 x.2
    have key : ∀ v, ρ x.1 (ρ x.1 v) = v := by
      intro v
      have hw := hx2 v
      obtain ⟨a, ha⟩ : ∃ a, a = ρ x.1 v - v := ⟨_, rfl⟩
      rw [← ha] at hw
      have hva : v + a = ρ x.1 v := by rw [ha]; abel
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      have haa : a + a = 0 := by rw [← two_smul F, h2, zero_smul]
      calc ρ x.1 (ρ x.1 v) = ρ x.1 (v + a) := by rw [hva]
        _ = ρ x.1 v + a := by rw [map_add, hx1 a hw]
        _ = v + (a + a) := by rw [← hva]; abel
        _ = v := by rw [haa, add_zero]
    apply Subtype.ext
    apply hρ
    refine LinearMap.ext fun v => ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    change (ρ x.1 ^ 2 ^ 1) v = v
    rw [pow_one, pow_two]
    exact key v
  have hfinX : Finite X := Finite.of_surjective π hπ
  have hQM : Q ≤ π.ker := by
    have hn : (Q.map π).Normal := Subgroup.Normal.map hQnormal π hπ
    have hp : IsPGroup 2 (Q.map π) := hQp.map _
    have hb := eq_bot_of_normal_isPGroup_two hSL (Q.map π) hp
    intro x hx
    have : π x ∈ Q.map π := Subgroup.mem_map_of_mem _ hx
    rw [hb, Subgroup.mem_bot] at this
    exact MonoidHom.mem_ker.2 this
  obtain ⟨A, hAp, a, ha, b, hb, hab⟩ := exists_nonabelian_isPGroup_two hSL
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hπ 2 S
  have hTS : (T : Subgroup Γ).map π = (S : Subgroup X) := by
    rw [← Sylow.coe_mapSurjective hπ T, hT]
  have hTp : IsPGroup 2 (T : Subgroup Γ) := T.isPGroup'
  have hcomm : ∀ t ∈ (T : Subgroup Γ), ∀ s ∈ (T : Subgroup Γ), π t * π s = π s * π t := by
    intro t ht s hs
    have hW1 := commutator_map_eq_one (ρW.comp (T : Subgroup Γ).subtype)
      (fun x y => comm_of_finrank_le_two hTp _ hdW x y) ⟨t, ht⟩ ⟨s, hs⟩
    have hQ1 := commutator_map_eq_one (ρQ.comp (T : Subgroup Γ).subtype)
      (fun x y => comm_of_finrank_le_two hTp _ hdQ x y) ⟨t, ht⟩ ⟨s, hs⟩
    have hmem : t * s * t⁻¹ * s⁻¹ ∈ Q := ⟨hW1, hQ1⟩
    have h : π (t * s * t⁻¹ * s⁻¹) = 1 := MonoidHom.mem_ker.1 (hQM hmem)
    simp only [map_mul, map_inv] at h
    calc π t * π s = (π t * π s * (π t)⁻¹ * (π s)⁻¹) * (π s * π t) := by group
      _ = _ := by rw [h, one_mul]
  have haS : a ∈ (T : Subgroup Γ).map π := hTS ▸ hAS ha
  have hbS : b ∈ (T : Subgroup Γ).map π := hTS ▸ hAS hb
  obtain ⟨t, ht, rfl⟩ := haS
  obtain ⟨s, hs, rfl⟩ := hbS
  exact hab (hcomm t ht s hs)

end EvenSL

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
