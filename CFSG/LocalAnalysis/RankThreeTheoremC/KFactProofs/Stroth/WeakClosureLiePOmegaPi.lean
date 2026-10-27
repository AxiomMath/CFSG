module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaSwap
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.GroupTheory.WeirSylow Module

section Pi

variable {K : Type} [Field K] {C : Type} [CommGroup C]

@[expose] noncomputable def piTorus (S₀ : FormSpace K K) (ρ : C →* S₀.isom) (r : ℕ) :
    (Fin r → C) →* (FormSpace.pi fun _ : Fin r => S₀).isom :=
  (piDiagIsom S₀ r).comp (MonoidHom.piMap fun _ => ρ)

theorem piTorus_apply (S₀ : FormSpace K K) (ρ : C →* S₀.isom) (r : ℕ) (c : Fin r → C) :
    piTorus S₀ ρ r c = piDiagIsom S₀ r (fun i => ρ (c i)) :=
  rfl

theorem piTorus_injective (S₀ : FormSpace K K) {ρ : C →* S₀.isom} (hρ : Function.Injective ρ)
    (r : ℕ) : Function.Injective (piTorus S₀ ρ r) :=
  (piDiagIsom_injective S₀ r).comp fun _ _ h => funext fun i => hρ (congrFun h i)

theorem piDiagIsom_mulSingle_conj_torus {S₀ : FormSpace K K} (ρ : C →* S₀.isom) {r : ℕ}
    (i : Fin r) (g : S₀.isom) (μ : ℤ) (hg : ∀ c, g * ρ c * g⁻¹ = ρ (c ^ μ))
    (c : Fin r → C) :
    piDiagIsom S₀ r (Pi.mulSingle i g) * piTorus S₀ ρ r c *
        (piDiagIsom S₀ r (Pi.mulSingle i g))⁻¹ =
      piTorus S₀ ρ r (Function.update c i (c i ^ μ)) := by
  rw [piTorus_apply, piTorus_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg (piDiagIsom S₀ r) (funext fun k => ?_)
  by_cases hk : k = i
  · subst hk
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, Function.update_self]
    exact hg _
  · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hk, Function.update_of_ne hk,
      one_mul, mul_one, inv_one]

@[expose] noncomputable def piBlockFrame (S₀ : FormSpace K K) (ρ : C →* S₀.isom)
    (hρ : Function.Injective ρ) (J₀ : S₀.isom) (hJ : ∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹) (r : ℕ) :
    BlockFrame C r (FormSpace.pi fun _ : Fin r => S₀).isom where
  T := piTorus S₀ ρ r
  S := piPermIsom S₀ r
  T_injective := piTorus_injective S₀ hρ r
  S_conj σ c := piPermIsom_conj S₀ r σ (fun i => ρ (c i))
  exists_inv i := ⟨piDiagIsom S₀ r (Pi.mulSingle i J₀), fun c => by
    have h := piDiagIsom_mulSingle_conj_torus ρ i J₀ (-1) (fun c => by
      rw [zpow_neg_one]
      exact hJ c) c
    rwa [zpow_neg_one] at h⟩

end Pi

@[expose] def OmegaFrameData {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p a r : ℕ) (μ₀ : ℤ) : Prop :=
  ∃ F : BlockFrame (Multiplicative (ZMod (p ^ a))) r
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
    (∀ i : Fin r, r = 2 → ∃ g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
      ∀ c, g * F.T c * g⁻¹ = F.T (Function.update c i (c i ^ μ₀))) ∧
    (∀ i j : Fin r, i ≠ j → r = 2 →
      ∃ g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q),
        ∀ c, g * F.T c * g⁻¹ = F.T (c ∘ Equiv.swap i j))

theorem mem_commutator_of_coe_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hg : (g : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rw [← Subgroup.map_subtype_commutator] at hg
  obtain ⟨g', hg', hgg'⟩ := hg
  rwa [← Subtype.ext hgg']

theorem omegaFrameData_of_embedding {K : Type} [Field K] [Fintype K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {p a r : ℕ} [Fact p.Prime]
    (S₀ : FormSpace K K) (hS₀ : IsQuadSpace S₀) {d : ℕ} (hdim : finrank K S₀.V = 2 * d)
    (ρ : Multiplicative (ZMod (p ^ a)) →* S₀.isom) (hρ : Function.Injective ρ)
    (J₀ φ₀ : S₀.isom) (hJ : ∀ c, J₀ * ρ c * J₀⁻¹ = ρ c⁻¹)
    (hφ : ∀ c, φ₀ * ρ c * φ₀⁻¹ = ρ (c ^ (Fintype.card K : ℤ)))
    (ψ : (FormSpace.pi fun _ : Fin r => S₀).isom →* TauCeti.QuadraticMap.orthogonalGroup Q)
    (hψ : Function.Injective ψ)
    (hψD : CharP K 2 → ∀ g : (FormSpace.pi fun _ : Fin r => S₀).isom,
      Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace
        (g : (Fin r → S₀.V) ≃ₗ[K] (Fin r → S₀.V)))) →
      (ψ g : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    OmegaFrameData Q p a r (Fintype.card K : ℤ) := by
  classical
  have hinj : Function.Injective (ψ.comp (piBlockFrame S₀ ρ hρ J₀ hJ r).T) :=
    hψ.comp (piBlockFrame S₀ ρ hρ J₀ hJ r).T_injective
  refine ⟨(piBlockFrame S₀ ρ hρ J₀ hJ r).map ψ hinj, ?_, ?_⟩
  · intro i _
    refine ⟨ψ (piDiagIsom S₀ r (Pi.mulSingle i φ₀)), fun c => ?_⟩
    have h := piDiagIsom_mulSingle_conj_torus ρ i φ₀ (Fintype.card K : ℤ) hφ c
    show ψ _ * ψ (piTorus S₀ ρ r c) * (ψ _)⁻¹ =
      ψ (piTorus S₀ ρ r (Function.update c i (c i ^ (Fintype.card K : ℤ))))
    rw [← map_inv, ← map_mul, ← map_mul, h]
  · intro i j hij hr
    subst hr
    have hsw : Equiv.swap i j = Equiv.swap (0 : Fin 2) 1 := by
      fin_cases i <;> fin_cases j <;> simp_all [Equiv.swap_comm]
    rw [hsw]
    by_cases h2 : (2 : K) = 0
    · haveI : CharP K 2 := charP_two_of_two_eq_zero h2
      have hS : (ψ (piPermIsom S₀ 2 (Equiv.swap 0 1)) : V ≃ₗ[K] V) ∈
          ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
        hψD inferInstance _ (by rw [finrank_commSpace_swap]; exact ⟨d, by omega⟩)
      refine ⟨ψ (piPermIsom S₀ 2 (Equiv.swap 0 1)), mem_commutator_of_coe_mem hS, fun c => ?_⟩
      show ψ _ * ψ (piTorus S₀ ρ 2 c) * (ψ _)⁻¹ =
        ψ (piTorus S₀ ρ 2 (c ∘ ⇑(Equiv.swap (0 : Fin 2) 1)))
      rw [← map_inv, ← map_mul, ← map_mul]
      refine congrArg ψ ?_
      rw [piTorus_apply, piTorus_apply, piPermIsom_conj]
      simp only [Equiv.swap_inv]
      rfl
    · have hm := swap_mul_negIsom_mem_commutator h2 hS₀ hdim
      have hmc : ψ (piPermIsom S₀ 2 (Equiv.swap 0 1) *
          piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀))) ∈
          commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
        have h1 : ψ (piPermIsom S₀ 2 (Equiv.swap 0 1) *
            piDiagIsom S₀ 2 (Pi.mulSingle 0 (negIsom hS₀))) ∈
            (commutator (FormSpace.pi fun _ : Fin 2 => S₀).isom).map ψ :=
          Subgroup.mem_map_of_mem ψ hm
        rw [commutator, Subgroup.map_commutator] at h1
        exact Subgroup.commutator_mono le_top le_top h1
      refine ⟨_, hmc, fun c => ?_⟩
      show ψ _ * ψ (piTorus S₀ ρ 2 c) * (ψ _)⁻¹ =
        ψ (piTorus S₀ ρ 2 (c ∘ ⇑(Equiv.swap (0 : Fin 2) 1)))
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg ψ (swap_mul_negIsom_conj hS₀ ρ c)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
