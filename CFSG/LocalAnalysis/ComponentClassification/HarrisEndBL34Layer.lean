module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBTheta
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB

@[expose] def autEquivL34 :
    PSL3Four.R ≃* MulAut PSL3Four.S :=
  MulEquiv.ofBijective PSL3Four.conjAutS
    ⟨PSL3Four.conjAutS_injective, PSL3Four.conjAutS_surjective⟩

theorem autEquivL34_apply (r : PSL3Four.R) (s : PSL3Four.S) :
    ((autEquivL34 r s : PSL3Four.S) : Equiv.Perm (Fin 42)) =
      (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ :=
  PSL3Four.conjAutS_apply r s

theorem autEquivL34_of_mem (s : PSL3Four.S) :
    autEquivL34 ⟨s, PSL3Four.S_le_R s.2⟩ = MulAut.conj s := by
  ext q
  rw [autEquivL34_apply, MulAut.conj_apply]
  rfl

theorem autEquivL34_mem_innAut_iff (r : PSL3Four.R) :
    autEquivL34 r ∈ innAut PSL3Four.S ↔ (r : Equiv.Perm (Fin 42)) ∈ PSL3Four.S := by
  constructor
  · rintro ⟨s, hs⟩
    have : r = ⟨s, PSL3Four.S_le_R s.2⟩ :=
      autEquivL34.injective (by rw [autEquivL34_of_mem]; exact hs.symm)
    rw [this]
    exact s.2
  · intro h
    refine ⟨⟨r, h⟩, ?_⟩
    rw [← autEquivL34_of_mem]

structure LLayer (hs : Setting46e t L p f S w z V i j)
    (π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S) : Prop where
  h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)
  h47 : ∀ i' j' : ℕ, IsLemma47 p (w ^ (orderOf w / 2) * t ^ i' * z ^ j')
  quasi : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  out : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
    innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  surj : Function.Surjective π
  ker : π.ker = center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))

namespace LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem isPerfect (hL : LLayer hs π) :
    Group.IsPerfect ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  hL.quasi.1

@[expose] def theta (hL : LLayer hs π) :
    MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) →* MulAut PSL3Four.S :=
  haveI := hL.isPerfect
  Classical.choose (exists_theta π hL.surj hL.ker)

theorem theta_spec (hL : LLayer hs π) :
    (∀ (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
        (l l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))),
        (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = g * l * g⁻¹ →
          hL.theta g (π l) = π l') ∧
      ∀ g, hL.theta g = 1 ↔
        g ∈ centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
  haveI := hL.isPerfect
  Classical.choose_spec (exists_theta π hL.surj hL.ker)

theorem theta_apply (hL : LLayer hs π) (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (l l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (h : (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = g * l * g⁻¹) :
    hL.theta g (π l) = π l' :=
  hL.theta_spec.1 g l l' h

theorem theta_eq_one_iff (hL : LLayer hs π) (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    hL.theta g = 1 ↔ g ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [hL.theta_spec.2, hs.centralizer_layer_eq hL.h412]

theorem theta_conj (hL : LLayer hs π)
    (l : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    hL.theta l = MulAut.conj (π l) :=
  EndB.theta_conj hL.surj hL.theta_spec.1 l

theorem theta_mem_inner_iff (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    hL.theta g ∈ innAut PSL3Four.S ↔ g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [EndB.theta_mem_inner_iff hL.surj hL.theta_spec.1 hL.theta_spec.2,
    hs.centralizer_layer_eq hL.h412]

theorem alpha_not_mem (hL : LLayer hs π) :
    hL.theta (hs.setup.tBar i j) ∉ innAut PSL3Four.S := by
  rw [hL.theta_mem_inner_iff]
  intro h
  apply hL.out
  rw [← hs.centralizer_layer_eq hL.h412] at h
  have hc : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ n ∈ centralizer (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), k * n = n * k :=
    fun k hk n hn => mem_centralizer_iff.mp hn k hk
  obtain ⟨k, hk, n, hn, hkn⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hc h
  refine conjOn_mem_innAut_iff.mpr ⟨k, hk, ?_⟩
  rw [hkn, show k * n * k⁻¹ = n by rw [hc k hk n hn]; group]
  exact hn

theorem orderOf_alpha (hL : LLayer hs π) : orderOf (hL.theta (hs.setup.tBar i j)) = 2 := by
  refine orderOf_eq_prime (by rw [← map_pow, hs.tBar_sq, map_one]) fun h => hL.alpha_not_mem ?_
  rw [h]
  exact one_mem _

@[expose] def rho (hL : LLayer hs π) :
    MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) →* PSL3Four.R :=
  autEquivL34.symm.toMonoidHom.comp hL.theta

theorem autEquivL34_rho (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : autEquivL34 (hL.rho g) = hL.theta g := by
  simp only [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem rho_conj (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (l l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (h : (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = g * l * g⁻¹) :
    (hL.rho g : Equiv.Perm (Fin 42)) * (π l : Equiv.Perm (Fin 42)) *
        (hL.rho g : Equiv.Perm (Fin 42))⁻¹ = (π l' : Equiv.Perm (Fin 42)) := by
  rw [← autEquivL34_apply, autEquivL34_rho, hL.theta_apply g l l' h]

theorem rho_mem_S_iff (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    (hL.rho g : Equiv.Perm (Fin 42)) ∈ PSL3Four.S ↔
      g ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [← autEquivL34_mem_innAut_iff, autEquivL34_rho, hL.theta_mem_inner_iff]

theorem rho_eq_one_iff (hL : LLayer hs π)
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    hL.rho g = 1 ↔ g ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  rw [← hL.theta_eq_one_iff, ← autEquivL34_rho]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    exact autEquivL34.injective (by rw [h, map_one])

theorem rho_of_mem (hL : LLayer hs π)
    (l : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
    (hL.rho l : Equiv.Perm (Fin 42)) = π l := by
  have h : hL.rho l = ⟨π l, PSL3Four.S_le_R (π l).2⟩ :=
    autEquivL34.injective (by rw [autEquivL34_rho, autEquivL34_of_mem, hL.theta_conj])
  rw [h]

theorem rho_t_facts (hL : LLayer hs π) :
    orderOf (hL.rho (hs.setup.tBar i j)) = 2 ∧
      (hL.rho (hs.setup.tBar i j) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S := by
  refine ⟨?_, fun h => hL.alpha_not_mem ?_⟩
  · rw [rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq,
      hL.orderOf_alpha]
  · rw [← autEquivL34_rho, autEquivL34_mem_innAut_iff]
    exact h

end LLayer

end EndB

end CFSG.ComponentClassification.HarrisLit
