module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutOrbit

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Monster.B.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi22Theta_R
    (ψ : fi22R ≃* MulAut fi22P)
    (hψ : ∀ (r : fi22R) (g : fi22P), ((ψ r g : fi22P) : Equiv.Perm (Fin 3510)) =
      (r : Equiv.Perm (Fin 3510)) * g * (r : Equiv.Perm (Fin 3510))⁻¹)
    (r : fi22R) (i : Fin 3510) :
    ((fi22Theta ((r : Equiv.Perm (Fin 3510)) i) : fi22P) : Equiv.Perm (Fin 3510)) =
      (r : Equiv.Perm (Fin 3510)) * (fi22Theta i : fi22P) * (r : Equiv.Perm (Fin 3510))⁻¹ := by
  have hφg : ∀ (g : fi22P) (j : Fin 3510), fi22PhiPerm (ψ r) ((g : Equiv.Perm (Fin 3510)) j) =
      ((ψ r g : fi22P) : Equiv.Perm (Fin 3510)) (fi22PhiPerm (ψ r) j) := by
    intro g j
    apply fi22Theta.injective
    apply Subtype.ext
    have h1 : (fi22Theta (fi22PhiPerm (ψ r) ((g : Equiv.Perm (Fin 3510)) j)) : fi22P) =
        ψ r g * ψ r (fi22Theta j : fi22P) * (ψ r g)⁻¹ := by
      rw [fi22Theta_phiPerm, fi22Theta_equivariant, map_mul, map_mul, map_inv]
    have h2 : (fi22Theta (((ψ r g : fi22P) : Equiv.Perm (Fin 3510)) (fi22PhiPerm (ψ r) j)) :
        fi22P) = ψ r g * ψ r (fi22Theta j : fi22P) * (ψ r g)⁻¹ := by
      rw [fi22Theta_equivariant, fi22Theta_phiPerm]
    exact h1.trans h2.symm
  have hcomm : ∀ g : fi22P, ((r : Equiv.Perm (Fin 3510))⁻¹ * fi22PhiPerm (ψ r)) *
      (g : Equiv.Perm (Fin 3510)) =
      (g : Equiv.Perm (Fin 3510)) * ((r : Equiv.Perm (Fin 3510))⁻¹ * fi22PhiPerm (ψ r)) := by
    intro g
    ext j
    simp only [Equiv.Perm.mul_apply]
    rw [hφg g j, hψ r g]
    simp [Equiv.Perm.mul_apply]
  have hmem : ((r : Equiv.Perm (Fin 3510))⁻¹ * fi22PhiPerm (ψ r)) ∈
      Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcomm ⟨h, hh⟩).symm
  rw [fi22P_centralizer, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have h3 : (r : Equiv.Perm (Fin 3510)) i = fi22PhiPerm (ψ r) i := by rw [hmem]
  rw [h3, fi22Theta_phiPerm, hψ]

theorem centralizerCore_of_orbit
    (V : Subgroup fi22P) (p₀ : Fin 3510) (hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hreg : ∀ v ∈ V, (v : Equiv.Perm (Fin 3510)) p₀ = p₀ → v = 1)
    (huniq : ∀ q : Fin 3510, (∀ v ∈ V, (v : Equiv.Perm (Fin 3510)) q = q → v = 1) →
      ∃ v ∈ V, (v : Equiv.Perm (Fin 3510)) p₀ = q)
    (hgen : fi22P ≤ closure ((fun p => ((fi22Theta p : fi22P) : Equiv.Perm (Fin 3510))) ''
      {q | ∃ v ∈ V, (v : Equiv.Perm (Fin 3510)) p₀ = q})) :
    CentralizerCore V := by
  obtain ⟨-, -, -, hcent, ⟨ψ, hψ, -⟩, -⟩ := CTUC_Fi22_full_automorphism_permutation_model
  unfold CentralizerCore
  intro r hr
  have hVR : V.map fi22P.subtype ≤ fi22R := by
    rintro _ ⟨v, -, rfl⟩
    exact fi22P_le_R v.2
  have hmem := AutOrbit.mem_of_commute_of_regular_orbit (P := fi22P) (R := fi22R)
    (V := V.map fi22P.subtype) (fun p => ((fi22Theta p : fi22P) : Equiv.Perm (Fin 3510)))
    (fun r hr p => fi22Theta_R ψ hψ ⟨r, hr⟩ p)
    (fun g hg => by
      have : g ∈ Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact (hg h hh).symm
      rw [hcent, Subgroup.mem_bot] at this
      exact this)
    hVR
    (by
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (hVcomm v hv w hw))
    p₀
    (by
      rintro _ ⟨v, hv, rfl⟩ h
      have := hreg v hv h
      rw [this]
      rfl)
    (by
      intro q hq
      obtain ⟨v, hv, hvq⟩ := huniq q fun v hv h => by
        have := hq _ ⟨v, hv, rfl⟩ h
        exact Subtype.ext this
      exact ⟨v, ⟨v, hv, rfl⟩, hvq⟩)
    (hgen.trans (closure_mono (Set.image_mono (by
      rintro q ⟨v, hv, hvq⟩
      exact ⟨v, ⟨v, hv, rfl⟩, hvq⟩))))
    (r : Equiv.Perm (Fin 3510)) r.2
    (by
      rintro _ ⟨v, hv, rfl⟩
      exact hr v hv)
  obtain ⟨x, hx, hxr⟩ := hmem
  exact ⟨x, hx, hxr⟩

theorem centralizerCore_conj (V₀ : Subgroup fi22P) (g : fi22P) (h : CentralizerCore V₀) :
    CentralizerCore (V₀.map (MulAut.conj g).toMonoidHom) := by
  unfold CentralizerCore at h ⊢
  intro r hr
  have hg : (g : Equiv.Perm (Fin 3510)) ∈ fi22R := fi22P_le_R g.2
  have hr' : (g : Equiv.Perm (Fin 3510))⁻¹ * r * g ∈ fi22R :=
    fi22R.mul_mem (fi22R.mul_mem (fi22R.inv_mem hg) r.2) hg
  obtain ⟨x, hx, hxr⟩ := h ⟨_, hr'⟩ fun e he => by
    have h1 := hr ((MulAut.conj g).toMonoidHom e) ⟨e, he, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    calc (g : Equiv.Perm (Fin 3510))⁻¹ * r * g * e
        = (g : Equiv.Perm (Fin 3510))⁻¹ * (r * (g * e * (g : Equiv.Perm (Fin 3510))⁻¹)) * g := by
          group
      _ = (g : Equiv.Perm (Fin 3510))⁻¹ * ((g * e * (g : Equiv.Perm (Fin 3510))⁻¹) * r) * g := by
          rw [h1]
      _ = e * ((g : Equiv.Perm (Fin 3510))⁻¹ * r * g) := by group
  refine ⟨MulAut.conj g x, ⟨x, hx, rfl⟩, ?_⟩
  rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  change (g : Equiv.Perm (Fin 3510)) * (x : Equiv.Perm (Fin 3510)) *
    (g : Equiv.Perm (Fin 3510))⁻¹ = r
  rw [hxr]
  group

end CFSG.EvenSporadicStandard.TwoFi22.DS81
