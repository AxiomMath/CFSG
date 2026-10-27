module

public import CFSG.FeitThompson.Representations.ExtraspecialWeightCosetBasis
import CFSG.FeitThompson.Representations.ExtraspecialQuotientAlternatingForm

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.ExtraspecialWeight

open CFSG.FeitThompson

universe u v w w'

variable {p n : ℕ} {P : Type u} [Group P] {B : Subgroup P} {k : Type v} [Field k]
  {V₁ : Type w} [AddCommGroup V₁] [Module k V₁]
  {V₂ : Type w'} [AddCommGroup V₂] [Module k V₂]
  {ρ₁ : Representation k P V₁} {ρ₂ : Representation k P V₂}
  {lam mu : ↥B →* kˣ} {v₁ : V₁} {v₂ : V₂}

theorem apply_mul_apply_eq_smul (hv : ∀ b : ↥B, ρ₁ (b : P) v₁ = (lam b : k) • v₁) {g t s : P}
    (hb : s⁻¹ * (g * t) ∈ B) :
    ρ₁ g (ρ₁ t v₁) = (lam ⟨s⁻¹ * (g * t), hb⟩ : k) • ρ₁ s v₁ := by
  have h1 : ρ₁ g (ρ₁ t v₁) = ρ₁ (g * t) v₁ := by rw [map_mul]; rfl
  have h2 : ρ₁ (g * t) = (ρ₁ s : Module.End k V₁) * ρ₁ (s⁻¹ * (g * t)) := by
    rw [← map_mul]; congr 1; group
  rw [h1, h2, Module.End.mul_apply, hv ⟨_, hb⟩, map_smul]

theorem apply_translate_weight (hBn : B.Normal)
    (hv : ∀ b : ↥B, ρ₁ (b : P) v₁ = (lam b : k) • v₁) (t : P) (b : ↥B) :
    ρ₁ (b : P) (ρ₁ t v₁) = (weightConj hBn lam t b : k) • ρ₁ t v₁ := by
  have hb : t⁻¹ * ((b : P) * t) ∈ B := by
    have := hBn.conj_mem' (b : P) b.2 t
    simpa [mul_assoc] using this
  rw [apply_mul_apply_eq_smul hv hb,
    weightConj_apply_mk hBn lam t b.2 (hBn.conj_mem' _ b.2 t),
    char_apply_congr lam hb (hBn.conj_mem' _ b.2 t) (by group)]

theorem exists_weightVector_of_conj (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hBab : IsMulCommutative ↥B) (hCB : Subgroup.centralizer (B : Set P) = B)
    (hPB : B.index = p ^ n) (hBZ : (Subgroup.center P).relIndex B = p ^ n)
    [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hlm : centerChar hZB mu = centerChar hZB lam) (hnt : centerChar hZB mu ≠ 1)
    (hv₂0 : v₂ ≠ 0) (hv₂ : ∀ b : ↥B, ρ₂ (b : P) v₂ = (mu b : k) • v₂) :
    ∃ w : V₂, w ≠ 0 ∧ ∀ b : ↥B, ρ₂ (b : P) w = (lam b : k) • w := by
  have hBn := normal_of_commutator_le_center hP.commutator_le_center hZB
  obtain ⟨t, ht⟩ := exists_conj_apply_eq_of_centerChar_eq (lam := mu) (mu := lam) (hZB := hZB)
    hP hBab hCB hPB hBZ hp hlm hnt
  have hkey : weightConj hBn mu t = lam := by
    refine MonoidHom.ext fun b => ?_
    rw [weightConj_apply_mk hBn mu t b.2 (hBn.conj_mem' _ b.2 t)]
    exact (ht (b : P) b.2 (hBn.conj_mem' _ b.2 t)).symm
  refine ⟨ρ₂ t v₂, apply_ne_zero t hv₂0, fun b => ?_⟩
  rw [apply_translate_weight hBn hv₂ t b, hkey]

theorem nonempty_equiv_of_weightVector (hP : IsExtraspecial p P) {hZB : Subgroup.center P ≤ B}
    (hCB : Subgroup.centralizer (B : Set P) = B) (hnt : centerChar hZB lam ≠ 1)
    (hirr₁ : ρ₁.IsIrreducible) (hirr₂ : ρ₂.IsIrreducible)
    (hv₁0 : v₁ ≠ 0) (hv₁ : ∀ b : ↥B, ρ₁ (b : P) v₁ = (lam b : k) • v₁)
    (hv₂0 : v₂ ≠ 0) (hv₂ : ∀ b : ↥B, ρ₂ (b : P) v₂ = (lam b : k) • v₂) :
    Nonempty (ρ₁.Equiv ρ₂) := by
  classical
  have hT : Function.Bijective
      fun q : P ⧸ B => (QuotientGroup.mk (Quotient.out q) : P ⧸ B) := by
    have hid : (fun q : P ⧸ B => (QuotientGroup.mk (Quotient.out q) : P ⧸ B)) = id := by
      funext q; simp [QuotientGroup.mk]
    rw [hid]; exact Function.bijective_id
  set T : P ⧸ B → P := fun q => Quotient.out q with hTdef
  set b₁ := cosetBasis hP hCB hnt hirr₁ hv₁0 hv₁ T hT with hb₁
  set b₂ := cosetBasis hP hCB hnt hirr₂ hv₂0 hv₂ T hT with hb₂
  set f := b₁.equiv b₂ (Equiv.refl (P ⧸ B)) with hfdef
  have hf : ∀ q : P ⧸ B, f (b₁ q) = b₂ q := by
    intro q; rw [hfdef, Module.Basis.equiv_apply]; rfl
  refine ⟨Representation.Equiv.mk f fun g => ?_⟩
  refine b₁.ext fun i => ?_
  have hb₁i : b₁ i = ρ₁ (T i) v₁ := cosetBasis_apply hP hCB hnt hirr₁ hv₁0 hv₁ T hT i
  have hb₂i : b₂ i = ρ₂ (T i) v₂ := cosetBasis_apply hP hCB hnt hirr₂ hv₂0 hv₂ T hT i
  set j : P ⧸ B := QuotientGroup.mk (g * T i) with hj
  have hmem : (T j)⁻¹ * (g * T i) ∈ B := by
    refine QuotientGroup.eq.1 ?_
    simp [T, hj, QuotientGroup.mk]
  have hb₁j : b₁ j = ρ₁ (T j) v₁ := cosetBasis_apply hP hCB hnt hirr₁ hv₁0 hv₁ T hT j
  have hb₂j : b₂ j = ρ₂ (T j) v₂ := cosetBasis_apply hP hCB hnt hirr₂ hv₂0 hv₂ T hT j
  have hL : f ((ρ₁ g) (b₁ i)) = (lam ⟨(T j)⁻¹ * (g * T i), hmem⟩ : k) • ρ₂ (T j) v₂ := by
    rw [hb₁i, apply_mul_apply_eq_smul hv₁ hmem, map_smul, ← hb₁j, hf, hb₂j]
  have hR : (ρ₂ g) (f (b₁ i)) = (lam ⟨(T j)⁻¹ * (g * T i), hmem⟩ : k) • ρ₂ (T j) v₂ := by
    rw [hf, hb₂i, apply_mul_apply_eq_smul hv₂ hmem]
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    using hL.trans hR.symm

theorem nonempty_equiv_of_centerChar (hP : IsExtraspecial p P) (hZB : Subgroup.center P ≤ B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr₁ : ρ₁.IsIrreducible) (hirr₂ : ρ₂.IsIrreducible)
    (zeta : ↥(Subgroup.center P) →* kˣ) (hzeta : zeta ≠ 1)
    (hz₁ : ∀ (z : ↥(Subgroup.center P)) (x : V₁), ρ₁ (z : P) x = (zeta z : k) • x)
    (hz₂ : ∀ (z : ↥(Subgroup.center P)) (x : V₂), ρ₂ (z : P) x = (zeta z : k) • x) :
    Nonempty (ρ₁.Equiv ρ₂) := by
  have hBab := isMulCommutative_of_centralizer_eq hCB
  obtain ⟨lam, v₁, hv₁0, hv₁, hlam⟩ :=
    exists_weightVector_centerChar_eq hP hZB hBab hp hirr₁ zeta hz₁
  obtain ⟨mu, w, hw0, hw, hmu⟩ :=
    exists_weightVector_centerChar_eq hP hZB hBab hp hirr₂ zeta hz₂
  obtain ⟨v₂, hv₂0, hv₂⟩ := exists_weightVector_of_conj (lam := lam) (mu := mu) (hZB := hZB)
    hP hBab hCB hPB hBZ hp (hmu.trans hlam.symm) (hmu ▸ hzeta) hw0 hw
  exact nonempty_equiv_of_weightVector hP hCB (hlam ▸ hzeta) hirr₁ hirr₂ hv₁0 hv₁ hv₂0 hv₂

theorem exists_linearEquiv_comm_of_centerChar (hP : IsExtraspecial p P)
    (hZB : Subgroup.center P ≤ B) (hCB : Subgroup.centralizer (B : Set P) = B)
    (hPB : B.index = p ^ n) (hBZ : (Subgroup.center P).relIndex B = p ^ n)
    [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hirr₁ : ρ₁.IsIrreducible) (hirr₂ : ρ₂.IsIrreducible)
    (zeta : ↥(Subgroup.center P) →* kˣ) (hzeta : zeta ≠ 1)
    (hz₁ : ∀ (z : ↥(Subgroup.center P)) (x : V₁), ρ₁ (z : P) x = (zeta z : k) • x)
    (hz₂ : ∀ (z : ↥(Subgroup.center P)) (x : V₂), ρ₂ (z : P) x = (zeta z : k) • x) :
    ∃ f : V₁ ≃ₗ[k] V₂, ∀ (g : P) (x : V₁), f (ρ₁ g x) = ρ₂ g (f x) := by
  obtain ⟨e⟩ := nonempty_equiv_of_centerChar hP hZB hCB hPB hBZ hp hirr₁ hirr₂ zeta hzeta hz₁ hz₂
  refine ⟨e.toLinearEquiv, fun g x => ?_⟩
  have h : (e.toLinearEquiv : V₁ → V₂) = (e : V₁ → V₂) := rfl
  rw [h]
  exact Representation.IntertwiningMap.isIntertwining ρ₁ ρ₂ e.toIntertwiningMap g x

end CFSG.FeitThompson.ExtraspecialWeight
