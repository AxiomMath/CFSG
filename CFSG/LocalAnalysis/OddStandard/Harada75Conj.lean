module

public import CFSG.LocalAnalysis.OddStandard.Harada75Heis
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OddStandard.Harada75

open Heis

section Conj

variable {S : Type} [Group S] (ι : Heis →* S)

noncomputable def conjHom (hι : Function.Injective ι) (t : S)
    (ht : ∀ h, ∃ h', t * ι h * t⁻¹ = ι h') : Heis →* Heis where
  toFun h := Classical.choose (ht h)
  map_one' := by
    apply hι
    rw [← Classical.choose_spec (ht 1)]
    simp
  map_mul' a b := by
    have hx := Classical.choose_spec (ht a)
    have hy := Classical.choose_spec (ht b)
    have hz := Classical.choose_spec (ht (a * b))
    apply hι
    show ι (Classical.choose (ht (a * b))) = ι (Classical.choose (ht a) * Classical.choose (ht b))
    rw [map_mul ι (Classical.choose (ht a)) (Classical.choose (ht b)), ← hx, ← hy, ← hz,
      map_mul ι a b]
    group

variable {ι}

theorem conjHom_spec (hι : Function.Injective ι) (t : S)
    (ht : ∀ h, ∃ h', t * ι h * t⁻¹ = ι h') (h : Heis) :
    ι (conjHom ι hι t ht h) = t * ι h * t⁻¹ :=
  (Classical.choose_spec (ht h)).symm

theorem conjHom_mul (hι : Function.Injective ι) (s t : S)
    (hs : ∀ h, ∃ h', s * ι h * s⁻¹ = ι h') (ht : ∀ h, ∃ h', t * ι h * t⁻¹ = ι h')
    (hst : ∀ h, ∃ h', (s * t) * ι h * (s * t)⁻¹ = ι h') :
    conjHom ι hι (s * t) hst = (conjHom ι hι s hs).comp (conjHom ι hι t ht) := by
  refine MonoidHom.ext fun h => hι ?_
  rw [conjHom_spec hι (s * t) hst h]
  simp only [MonoidHom.comp_apply]
  rw [conjHom_spec hι s hs, conjHom_spec hι t ht]
  group

theorem conjHom_one (hι : Function.Injective ι) (h1 : ∀ h, ∃ h', (1 : S) * ι h * 1⁻¹ = ι h') :
    conjHom ι hι 1 h1 = MonoidHom.id Heis := by
  refine MonoidHom.ext fun h => hι ?_
  rw [conjHom_spec hι 1 h1 h]
  simp

theorem exists_conj_of_mem_normalizer (t : S)
    (ht : t ∈ Subgroup.normalizer ((ι.range : Subgroup S) : Set S)) (h : Heis) :
    ∃ h', t * ι h * t⁻¹ = ι h' := by
  have := (Subgroup.mem_normalizer_iff.mp ht (ι h)).mp ⟨h, rfl⟩
  obtain ⟨h', hh'⟩ := this
  exact ⟨h', hh'.symm⟩


structure Setup (ι : Heis →* S) : Prop where
  inj : Function.Injective ι
  z_cent : ∀ s : S, s * ι z₀ = ι z₀ * s
  E_norm : ∀ t : S, ∀ h ∈ E₀, ∃ h' ∈ E₀, t * ι h * t⁻¹ = ι h'
  C_le : ∀ x : S, (∀ r ∈ ι.range, x * r = r * x) → x ∈ ι.range

variable {ι : Heis →* S}

@[expose] def Vsub (ι : Heis →* S) : Subgroup S :=
  Subgroup.normalizer ((ι.range : Subgroup S) : Set S)

namespace Setup

variable (D : Setup ι)

noncomputable def phi (t : Vsub ι) : Heis →* Heis :=
  conjHom ι D.inj t.1 (exists_conj_of_mem_normalizer t.1 t.2)

theorem phi_spec (t : Vsub ι) (h : Heis) : ι (D.phi t h) = t.1 * ι h * t.1⁻¹ :=
  conjHom_spec D.inj t.1 _ h

theorem phi_mul (s t : Vsub ι) : D.phi (s * t) = (D.phi s).comp (D.phi t) :=
  conjHom_mul D.inj s.1 t.1 _ _ _

theorem phi_one : D.phi 1 = MonoidHom.id Heis := conjHom_one D.inj _

theorem phi_z (t : Vsub ι) : D.phi t z₀ = z₀ := by
  apply D.inj
  rw [D.phi_spec]
  have := D.z_cent t.1
  rw [this]
  group

theorem phi_E (t : Vsub ι) (h : Heis) : D.phi t h ∈ E₀ ↔ h ∈ E₀ := by
  have key : ∀ (t : Vsub ι) (h : Heis), h ∈ E₀ → D.phi t h ∈ E₀ := by
    intro t h hh
    obtain ⟨h', hh', e⟩ := D.E_norm t.1 h hh
    have : D.phi t h = h' := D.inj (by rw [D.phi_spec, e])
    rw [this]
    exact hh'
  refine ⟨fun hh => ?_, key t h⟩
  have h2 := key t⁻¹ (D.phi t h) hh
  have h3 : D.phi t⁻¹ (D.phi t h) = h := by
    have := congrArg (fun f : Heis →* Heis => f h) (D.phi_mul t⁻¹ t)
    simp only [MonoidHom.comp_apply, inv_mul_cancel, D.phi_one, MonoidHom.id_apply] at this
    exact this.symm
  rwa [h3] at h2


theorem phi_inv_comp (t : Vsub ι) : (D.phi t).comp (D.phi t⁻¹) = MonoidHom.id Heis := by
  rw [← D.phi_mul, mul_inv_cancel, D.phi_one]

theorem phi_comp_inv (t : Vsub ι) : (D.phi t⁻¹).comp (D.phi t) = MonoidHom.id Heis := by
  rw [← D.phi_mul, inv_mul_cancel, D.phi_one]

@[expose] noncomputable def psiFun (t : Vsub ι) : Isom :=
  ⟨linPerm (D.phi t) (D.phi t⁻¹) (D.phi_inv_comp t) (D.phi_comp_inv t) (D.phi_z t)
      (D.phi_z t⁻¹), isIsom_lin (D.phi t) (D.phi_z t) (D.phi_E t)⟩

theorem psiFun_apply (t : Vsub ι) (w : W₀) :
    ((D.psiFun t : Isom) : Equiv.Perm W₀) w = lin (D.phi t) w := rfl

@[expose] noncomputable def psi : Vsub ι →* Isom :=
  MonoidHom.mk' D.psiFun (fun s t => by
    apply Subtype.ext
    apply Equiv.ext
    intro w
    show lin (D.phi (s * t)) w = lin (D.phi s) (lin (D.phi t) w)
    rw [D.phi_mul, lin_comp (D.phi s) (D.phi t) (D.phi_z s)])

theorem psi_apply (t : Vsub ι) (w : W₀) :
    ((D.psi t : Isom) : Equiv.Perm W₀) w = lin (D.phi t) w := rfl

theorem lin_phi_of_mem (t : Vsub ι) (h₀ : Heis) (ht : t.1 = ι h₀) (w : W₀) :
    lin (D.phi t) w = w := by
  have h1 : D.phi t ⟨w, 0⟩ = h₀ * ⟨w, 0⟩ * h₀⁻¹ := by
    apply D.inj
    rw [D.phi_spec, ht, map_mul, map_mul, map_inv]
  unfold lin
  rw [h1]
  simp only [Heis.mul_w, Heis.inv_w]
  rw [add_comm h₀.w w, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem psi_eq_one_iff (t : Vsub ι) : D.psi t = 1 ↔ t.1 ∈ ι.range := by
  constructor
  · intro h1
    have h2 : ∀ w, lin (D.phi t) w = w := by
      intro w
      have := congrArg (fun σ : Isom => (σ : Equiv.Perm W₀) w) h1
      exact this
    obtain ⟨h₀, hh₀⟩ := exists_conj_of_lin_eq_id (D.phi t) (D.phi_z t) h2
    have hc : (ι h₀)⁻¹ * t.1 ∈ ι.range := by
      apply D.C_le
      rintro _ ⟨x, rfl⟩
      have e1 : t.1 * ι x = ι (D.phi t x) * t.1 := by
        have := D.phi_spec t x
        rw [this]; group
      rw [hh₀ x, map_mul, map_mul, map_inv] at e1
      calc (ι h₀)⁻¹ * t.1 * ι x = (ι h₀)⁻¹ * (t.1 * ι x) := by group
        _ = (ι h₀)⁻¹ * (ι h₀ * ι x * (ι h₀)⁻¹ * t.1) := by rw [e1]
        _ = ι x * ((ι h₀)⁻¹ * t.1) := by group
    have : t.1 = ι h₀ * ((ι h₀)⁻¹ * t.1) := by group
    rw [this]
    exact ι.range.mul_mem (ι.mem_range.mpr ⟨h₀, rfl⟩) hc
  · rintro ⟨h₀, hh₀⟩
    apply Subtype.ext
    apply Equiv.ext
    intro w
    exact D.lin_phi_of_mem t h₀ hh₀.symm w

end Setup

end Conj

end CFSG.OddStandard.Harada75
