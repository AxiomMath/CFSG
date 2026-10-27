module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverRadical
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.GeneralLinearHermitianSplitting

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 1 K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
variable (θ) in
structure IsHermComplement (Vt : Subgroup E) : Prop where
  le : Vt ≤ preV θ
  inj : ∀ v ∈ Vt, θ v = 1 → v = 1
  dec : ∀ t ∈ preV θ, ∃ c v, θ c = 1 ∧ v ∈ Vt ∧ t = c * v
  conj : ∀ (A : GL (Fin r) K) (g : E), θ g = hypProj h r 1 (lHom h r A) →
    ∀ v ∈ Vt, g * v * g⁻¹ ∈ Vt

omit [CharP K 2] in
include hθ hC in
theorem liftConj_mem_preV (A : GL (Fin r) K) {t : E} (ht : t ∈ preV θ) :
    BinarySymplecticSix.liftConj hθ hC (hypProj h r 1 (lHom h r A)) t ∈ preV θ := by
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r A))
  rw [← hg, BinarySymplecticSix.liftConj_apply, MulAut.conj_apply]
  obtain ⟨B, hB⟩ := mem_preV.mp ht
  exact (hB.conj A hg).mem

include hθ hC in
theorem exists_herm_complement [Finite E] (h2 : ∀ c, θ c = 1 → c ^ 2 = 1) (hr : 2 ≤ r) :
    ∃ Vt : Subgroup E, IsHermComplement θ Vt := by
  have hK := card_eq_four h
  have hr1 : 1 ≤ r := by omega
  set T := preV θ with hT
  let : CommGroup T :=
    { (inferInstance : Group T) with
      mul_comm := fun a b => Subtype.ext (mul_comm_of_mem_preV hθ hC a.2 b.2) }
  set α : GL (Fin r) K →* MulAut E :=
    (BinarySymplecticSix.liftConj hθ hC).comp ((hypProj h r 1).comp (lHom h r)) with hα
  have hαT : ∀ A, ∀ x ∈ T, α A x ∈ T := fun A x hx => liftConj_mem_preV hθ hC A hx
  set ρ := BinarySymplecticSix.restrictAct α T hαT with hρ
  let : DistribMulAction (GL (Fin r) K) (Additive T) :=
    { smul := fun A t => Additive.ofMul (ρ A (Additive.toMul t))
      one_smul := fun t => by
        change Additive.ofMul (ρ 1 (Additive.toMul t)) = t
        rw [map_one, MulAut.one_apply]
        rfl
      mul_smul := fun A B t => by
        change Additive.ofMul (ρ (A * B) (Additive.toMul t)) =
          Additive.ofMul (ρ A (ρ B (Additive.toMul t)))
        rw [map_mul, MulAut.mul_apply]
      smul_zero := fun A => by
        change Additive.ofMul (ρ A 1) = 0
        rw [map_one]
        rfl
      smul_add := fun A t t' => by
        change Additive.ofMul (ρ A (Additive.toMul t * Additive.toMul t')) = _
        rw [map_mul]
        rfl }
  have hsmul : ∀ (A : GL (Fin r) K) (t : Additive T),
      ((Additive.toMul (A • t) : T) : E) = α A (Additive.toMul t : T) := fun _ _ => rfl
  set coordV : T → Matrix (Fin r) (Fin r) K := fun t => Classical.choose (mem_preV.mp t.2)
    with hcoordV
  have hcoord : ∀ t : T, IsV θ (coordV t) (t : E) := fun t =>
    Classical.choose_spec (mem_preV.mp t.2)
  have huniq : ∀ (t : T) {B : Matrix (Fin r) (Fin r) K}, IsV θ B (t : E) → coordV t = B :=
    fun t B hB => (hcoord t).eq_of_isV hr1 hB
  let πT : Additive T →+ Matrix (Fin r) (Fin r) K :=
    { toFun := fun t => coordV (Additive.toMul t)
      map_zero' := huniq 1 (isV_zero_iff.mpr (map_one θ))
      map_add' := fun t t' => huniq _ ((hcoord _).mul (hcoord _)) }
  have hπT : ∀ t : Additive T, πT t = coordV (Additive.toMul t) := fun _ => rfl
  have hker : ∀ t : Additive T, πT t = 0 ↔ θ ((Additive.toMul t : T) : E) = 1 := fun t => by
    rw [hπT]
    constructor
    · intro h0
      have := hcoord (Additive.toMul t)
      rw [h0] at this
      exact isV_zero_iff.mp this
    · intro h1
      exact huniq _ (isV_zero_iff.mpr h1)
  have hliftα : ∀ (A : GL (Fin r) K) (x : E), ∃ g, θ g = hypProj h r 1 (lHom h r A) ∧
      α A x = g * x * g⁻¹ := fun A x => by
    obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r A))
    refine ⟨g, hg, ?_⟩
    change BinarySymplecticSix.liftConj hθ hC (hypProj h r 1 (lHom h r A)) x = _
    rw [← hg, BinarySymplecticSix.liftConj_apply, MulAut.conj_apply]
  obtain ⟨-, M₀, hinv, hinf, hsup, hinj, -⟩ :=
    four_element_general_linear_hermitian_extension_splitting hK hr (M := Additive T)
      inferInstance
      (fun t => ⟨2, by
        change Additive.ofMul ((Additive.toMul t) ^ 2 ^ 2) = 0
        have hsq : θ (((Additive.toMul t : T) : E) ^ 2) = 1 := by
          have := (hcoord (Additive.toMul t)).mul (hcoord (Additive.toMul t))
          rw [show coordV (Additive.toMul t) + coordV (Additive.toMul t) = 0 by
            ext i j
            exact CharTwo.add_self_eq_zero _] at this
          rw [pow_two]
          exact isV_zero_iff.mp this
        have h4 : ((Additive.toMul t : T) : E) ^ 2 ^ 2 = 1 := by
          rw [show (2 ^ 2 : ℕ) = 2 * 2 from rfl, pow_mul, h2 _ hsq]
        exact congrArg Additive.ofMul (Subtype.ext h4)⟩)
      πT (fun t => isRad_zero_iff.mp (hcoord _).1)
      (fun B hB => by
        obtain ⟨t, ht⟩ := exists_isV hθ (isRad_zero_iff.mpr hB)
        exact ⟨Additive.ofMul ⟨t, ht.mem⟩, huniq _ ht⟩)
      (fun A t => by
        rw [hπT, hπT]
        obtain ⟨g, hg, he⟩ := hliftα A (Additive.toMul t : T)
        refine huniq _ ?_
        rw [hsmul, he, ← map_bar_transpose h]
        exact (hcoord _).conj A hg)
      (fun c hc => by
        rw [AddMonoidHom.mem_ker, hker] at hc
        have h1 := h2 _ hc
        rw [two_nsmul]
        change Additive.ofMul (Additive.toMul c * Additive.toMul c) = 0
        rw [← pow_two]
        exact congrArg Additive.ofMul (Subtype.ext h1))
      (fun A c hc => by
        rw [AddMonoidHom.mem_ker, hker] at hc
        apply Additive.toMul.injective
        apply Subtype.ext
        rw [hsmul]
        exact BinarySymplecticSix.liftConj_apply_of_mem_ker hθ hC _ hc)
  let Vt : Subgroup E :=
    { carrier := {e | ∃ he : e ∈ T, Additive.ofMul (⟨e, he⟩ : T) ∈ M₀}
      one_mem' := ⟨one_mem T, zero_mem M₀⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨mul_mem ha hb, add_mem ha' hb'⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨inv_mem ha, neg_mem ha'⟩ }
  refine ⟨Vt, ⟨fun e he => he.1, fun v hv hv1 => ?_, fun t ht => ?_, fun A g hg v hv => ?_⟩⟩
  · obtain ⟨hvT, hvM⟩ := hv
    have h0 := hinj _ hvM ((hker _).mpr hv1)
    exact congrArg Subtype.val (Additive.ofMul.injective h0 : (⟨v, hvT⟩ : T) = 1)
  · have hmem : Additive.ofMul (⟨t, ht⟩ : T) ∈ πT.ker ⊔ M₀ := by
      rw [hsup]
      exact AddSubgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hmem
    refine ⟨((Additive.toMul y : T) : E), ((Additive.toMul z : T) : E), (hker y).mp hy,
      ⟨(Additive.toMul z : T).2, hz⟩, ?_⟩
    have := congrArg (fun w : Additive T => ((Additive.toMul w : T) : E)) hyz
    exact this.symm
  · obtain ⟨hvT, hvM⟩ := hv
    have hαv : α A v = g * v * g⁻¹ := by
      change BinarySymplecticSix.liftConj hθ hC (hypProj h r 1 (lHom h r A)) v = _
      rw [← hg, BinarySymplecticSix.liftConj_apply, MulAut.conj_apply]
    have hgT : g * v * g⁻¹ ∈ T := hαv ▸ hαT A v hvT
    refine ⟨hgT, ?_⟩
    have e : Additive.ofMul (⟨g * v * g⁻¹, hgT⟩ : T) = A • Additive.ofMul ⟨v, hvT⟩ := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change g * v * g⁻¹ = ((Additive.toMul (A • Additive.ofMul (⟨v, hvT⟩ : T)) : T) : E)
      rw [hsmul]
      exact hαv.symm
    rw [e]
    exact hinv A _ hvM

omit [CharP K 2] in
theorem conj_mem_preV_of_lift {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {t : E} (ht : t ∈ preV θ) : g * t * g⁻¹ ∈ preV θ := by
  obtain ⟨B, hB⟩ := mem_preV.mp ht
  exact (hB.conj A hg).mem

section Commutator

variable {Vt : Subgroup E} (hVt : IsHermComplement θ Vt)

omit [CharP K 2] in
include hC hVt in
theorem IsHermComplement.conj_mul_inv_mem {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {t : E} (ht : t ∈ preV θ) :
    g * t * g⁻¹ * t⁻¹ ∈ Vt := by
  obtain ⟨c, v, hc, hv, rfl⟩ := hVt.dec t ht
  have hcc : c ∈ Subgroup.center E := hC hc
  have e : g * (c * v) * g⁻¹ * (c * v)⁻¹ = g * v * g⁻¹ * v⁻¹ :=
    calc g * (c * v) * g⁻¹ * (c * v)⁻¹ = (g * c * g⁻¹) * (g * v * g⁻¹ * v⁻¹) * c⁻¹ := by group
      _ = c * (g * v * g⁻¹ * v⁻¹) * c⁻¹ := by rw [conj_central hcc]
      _ = g * v * g⁻¹ * v⁻¹ := conj_eq_of_mem_center hcc _
  rw [e]
  exact mul_mem (hVt.conj A g hg v hv) (inv_mem hv)

include hθ hC in
theorem conj_preV_of_mem_preN (hr : 2 ≤ r) {τ m : E} (hτ : τ ∈ preV θ) (hm : m ∈ preN θ) :
    m * τ * m⁻¹ = τ := by
  rw [← mul_comm_of_mem_preV_of_mem_preN hθ hC hr hτ hm, mul_inv_cancel_right]

include hθ hC in
theorem commutatorElement_mul_left_preN (hr : 2 ≤ r) {m₁ m₂ m' : E} (hm₁ : m₁ ∈ preN θ)
    (hm₂ : m₂ ∈ preN θ) (hm' : m' ∈ preN θ) : ⁅m₁ * m₂, m'⁆ = ⁅m₁, m'⁆ * ⁅m₂, m'⁆ := by
  rw [commutatorElement_mul_left', conj_preV_of_mem_preN hθ hC hr
    (commutatorElement_mem_preV hm₂ hm') hm₁]
  exact mul_comm_of_mem_preV hθ hC (commutatorElement_mem_preV hm₂ hm')
    (commutatorElement_mem_preV hm₁ hm')

include hθ hC in
theorem commutatorElement_mul_right_preN (hr : 2 ≤ r) {m m'₁ m'₂ : E} (hm : m ∈ preN θ)
    (hm'₁ : m'₁ ∈ preN θ) (hm'₂ : m'₂ ∈ preN θ) : ⁅m, m'₁ * m'₂⁆ = ⁅m, m'₁⁆ * ⁅m, m'₂⁆ := by
  rw [commutatorElement_mul_right', conj_preV_of_mem_preN hθ hC hr
    (commutatorElement_mem_preV hm hm'₂) hm'₁]

include hθ hC in
theorem commutatorElement_eq_of_isN_left (hr : 2 ≤ r) {m m₁ m' : E} {x : Fin r → K}
    (hm : IsN θ x m) (hm₁ : IsN θ x m₁) (hm' : m' ∈ preN θ) : ⁅m, m'⁆ = ⁅m₁, m'⁆ := by
  have hτ := hm.inv_mul_mem hm₁
  rw [show m₁ = m * (m⁻¹ * m₁) by group, commutatorElement_mul_left_preN hθ hC hr hm.mem
    (preV_le_preN hτ) hm', commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm_of_mem_preV_of_mem_preN hθ hC hr hτ hm'), mul_one]

include hθ hC in
theorem commutatorElement_mul_preV_right' (hr : 2 ≤ r) {m m' τ : E} (hm : m ∈ preN θ)
    (hm' : m' ∈ preN θ) (hτ : τ ∈ preV θ) : ⁅m, m' * τ⁆ = ⁅m, m'⁆ := by
  rw [commutatorElement_mul_right_preN hθ hC hr hm hm' (preV_le_preN hτ),
    show ⁅m, τ⁆ = 1 from commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm_of_mem_preV_of_mem_preN hθ hC hr hτ hm).symm, mul_one]

include hθ hC in
theorem commutatorElement_eq_of_isN_right (hr : 2 ≤ r) {m m' m'₁ : E} {y : Fin r → K}
    (hm : m ∈ preN θ) (hm' : IsN θ y m') (hm'₁ : IsN θ y m'₁) : ⁅m, m'⁆ = ⁅m, m'₁⁆ := by
  rw [show m'₁ = m' * (m'⁻¹ * m'₁) by group,
    commutatorElement_mul_preV_right' hθ hC hr hm hm'.mem (hm'.inv_mul_mem hm'₁)]

include hθ hC hVt in
theorem commutatorElement_mem_of_weight (hr : 2 ≤ r) {m' : E} (hm' : m' ∈ preN θ)
    {ψ : K → Fin r → K} (hψ : ∀ s s', ψ (s + s') = ψ s + ψ s') {A : GL (Fin r) K} {g : E}
    (hg : θ g = hypProj h r 1 (lHom h r A)) {ζ : K} (hζ : ζ ≠ 1)
    (hgm' : m'⁻¹ * (g * m' * g⁻¹) ∈ preV θ)
    (hgψ : ∀ s m, IsN θ (ψ s) m → IsN θ (ψ (ζ * s)) (g * m * g⁻¹)) {s : K} {m : E}
    (hm : IsN θ (ψ s) m) : ⁅m, m'⁆ ∈ Vt := by
  choose ℓ hℓ using fun s => exists_isN hθ (ψ s)
  have hF : ∀ s, ⁅ℓ s, m'⁆ ∈ preV θ := fun s => commutatorElement_mem_preV (hℓ s).mem hm'
  have hadd : ∀ s s', ⁅ℓ (s + s'), m'⁆ = ⁅ℓ s, m'⁆ * ⁅ℓ s', m'⁆ := fun s s' => by
    rw [commutatorElement_eq_of_isN_left hθ hC hr (hℓ (s + s'))
      (((hℓ s).mul (hℓ s')).congr (hψ s s').symm) hm',
      commutatorElement_mul_left_preN hθ hC hr (hℓ s).mem (hℓ s').mem hm']
  have hconj : ∀ s, g * ⁅ℓ s, m'⁆ * g⁻¹ = ⁅ℓ (ζ * s), m'⁆ := fun s => by
    rw [conjugate_commutatorElement, show g * m' * g⁻¹ = m' * (m'⁻¹ * (g * m' * g⁻¹)) by group,
      commutatorElement_mul_preV_right' hθ hC hr (hgψ s _ (hℓ s)).mem hm' hgm',
      commutatorElement_eq_of_isN_left hθ hC hr (hgψ s _ (hℓ s)) (hℓ (ζ * s)) hm']
  have hmem : ∀ u, ⁅ℓ ((ζ - 1) * u), m'⁆ ∈ Vt := fun u => by
    have h1 := hVt.conj_mul_inv_mem hC hg (hF u)
    rw [hconj, show ζ * u = (ζ - 1) * u + u by ring, hadd, mul_inv_cancel_right] at h1
    exact h1
  have hζ' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  rw [commutatorElement_eq_of_isN_left hθ hC hr hm (hℓ s) hm',
    show s = (ζ - 1) * ((ζ - 1)⁻¹ * s) by field_simp]
  exact hmem _

include hθ hC hVt in
theorem commutatorElement_mem_of_ne (hr : 2 ≤ r) {i j : Fin r} (hij : i ≠ j) {a b : K}
    {m m' : E} (hm : IsN θ (Pi.single i a) m) (hm' : IsN θ (Pi.single j b) m') :
    ⁅m, m'⁆ ∈ Vt := by
  have hK := card_eq_four h
  obtain ⟨w, hw1, -, -⟩ := exists_unit_ne_one hK
  set d : Fin r → Kˣ := Pi.mulSingle j w * Pi.mulSingle j 1 with hd
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL d)))
  have hprod : ∏ l, ((d l : Kˣ) : K) = w := by rw [hd, prod_mulSingle_mul, Units.val_one, mul_one]
  refine commutatorElement_mem_of_weight hθ hC hVt hr hm'.mem
    (ψ := fun s : K => (Pi.single i s : Fin r → K)) (fun s s' => by rw [Pi.single_add]) hg
    (ζ := (w : K)⁻¹) (inv_ne_one.mpr hw1) ?_ ?_ hm
  · refine hm'.inv_mul_mem ((hm'.conj_torus d hg).congr ?_)
    rw [hprod, hd, mulSingle_mul_apply, ite_eq_left rfl, ite_eq_left rfl, Units.val_one,
      mul_one, inv_mul_cancel₀ w.ne_zero, one_mul]
  · intro s m hm
    refine (hm.conj_torus d hg).congr ?_
    rw [hprod, hd, mulSingle_mul_apply, ite_eq_right hij, ite_eq_right hij, mul_one, mul_one]

include hθ hC hVt in
theorem commutatorElement_mem_of_eq (hr : 2 ≤ r) {k : Fin r} {a b : K} {ν ν' : E}
    (hν : IsN θ (Pi.single k a) ν) (hν' : IsN θ (Pi.single k b) ν') : ⁅ν, ν'⁆ ∈ Vt := by
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨i, hik⟩ := exists_ne k
  have hki : k ≠ i := Ne.symm hik
  obtain ⟨μ, hμ⟩ := exists_isN hθ (Pi.single i a)
  obtain ⟨μ', hμ'⟩ := exists_isN hθ (Pi.single i b)
  set A : GL (Fin r) K := hElemGL hki 1 with hA
  obtain ⟨g, hg⟩ := hθ (hypProj h r 1 (lHom h r A))
  have hact : ∀ (c : K) (n : E), IsN θ (Pi.single i c) n →
      IsN θ (Pi.single k c) (n⁻¹ * (g * n * g⁻¹)) := fun c n hn => by
    have h1 := hn.conj A hg
    rw [dval_eq_det, hA, hElemGL_det, inv_one, one_smul, hElemGL_coe, hElem_mulVec,
      Pi.single_eq_same, one_mul] at h1
    exact (hn.inv.mul h1).congr (by abel)
  set ν₀ := μ⁻¹ * (g * μ * g⁻¹) with hν₀
  set ν₀' := μ'⁻¹ * (g * μ' * g⁻¹) with hν₀'
  have h₀ := hact a μ hμ
  have h₀' := hact b μ' hμ'
  have hX : g * ⁅μ, μ'⁆ * g⁻¹ = ⁅μ, μ'⁆ * ⁅μ, ν₀'⁆ * (⁅ν₀, μ'⁆ * ⁅ν₀, ν₀'⁆) := by
    rw [conjugate_commutatorElement, show g * μ * g⁻¹ = μ * ν₀ by rw [hν₀]; group,
      show g * μ' * g⁻¹ = μ' * ν₀' by rw [hν₀']; group,
      commutatorElement_mul_left_preN hθ hC hr hμ.mem h₀.mem (mul_mem hμ'.mem h₀'.mem),
      commutatorElement_mul_right_preN hθ hC hr hμ.mem hμ'.mem h₀'.mem,
      commutatorElement_mul_right_preN hθ hC hr h₀.mem hμ'.mem h₀'.mem]
  have hP := hVt.conj_mul_inv_mem hC hg (commutatorElement_mem_preV hμ.mem hμ'.mem)
  have hQ := commutatorElement_mem_of_ne hθ hC hVt hr hik hμ h₀'
  have hR := commutatorElement_mem_of_ne hθ hC hVt hr hki h₀ hμ'
  rw [commutatorElement_eq_of_isN_left hθ hC hr hν h₀ hν'.mem,
    commutatorElement_eq_of_isN_right hθ hC hr h₀.mem hν' h₀']
  have hcomm : ⁅μ, μ'⁆⁻¹ * (g * ⁅μ, μ'⁆ * g⁻¹) = g * ⁅μ, μ'⁆ * g⁻¹ * ⁅μ, μ'⁆⁻¹ :=
    mul_comm_of_mem_preV hθ hC (inv_mem (commutatorElement_mem_preV hμ.mem hμ'.mem))
      (conj_mem_preV_of_lift hg (commutatorElement_mem_preV hμ.mem hμ'.mem))
  have e : ⁅ν₀, ν₀'⁆ = ⁅ν₀, μ'⁆⁻¹ * ⁅μ, ν₀'⁆⁻¹ * (⁅μ, μ'⁆⁻¹ * (g * ⁅μ, μ'⁆ * g⁻¹)) := by
    rw [hX]
    group
  rw [e, hcomm]
  exact mul_mem (mul_mem (inv_mem hR) (inv_mem hQ)) hP

include hθ hC in
theorem commutatorElement_mem_of_single_left (hr : 2 ≤ r) {m' : E} (hm' : m' ∈ preN θ)
    (hgen : ∀ (k : Fin r) (a : K) (m : E), IsN θ (Pi.single k a) m → ⁅m, m'⁆ ∈ Vt) {m : E}
    (hm : m ∈ preN θ) : ⁅m, m'⁆ ∈ Vt := by
  let S : AddSubgroup (Fin r → K) :=
    { carrier := {x | ∀ m, IsN θ x m → ⁅m, m'⁆ ∈ Vt}
      zero_mem' := fun m hm => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm_of_mem_preV_of_mem_preN hθ hC hr (isN_zero_iff.mp hm) hm')]
        exact one_mem _
      add_mem' := by
        intro x y hx hy m hm
        obtain ⟨m₁, hm₁⟩ := exists_isN hθ x
        have hm₂ : IsN θ y (m₁⁻¹ * m) := (hm₁.inv.mul hm).congr (by abel)
        rw [show m = m₁ * (m₁⁻¹ * m) by group,
          commutatorElement_mul_left_preN hθ hC hr hm₁.mem hm₂.mem hm']
        exact mul_mem (hx m₁ hm₁) (hy _ hm₂)
      neg_mem' := by
        intro x hx m hm
        have hm₁ : IsN θ x m⁻¹ := hm.inv.congr (neg_neg x)
        have h1 := commutatorElement_mul_left_preN hθ hC hr hm.mem hm₁.mem hm'
        rw [mul_inv_cancel, commutatorElement_one_left] at h1
        rw [eq_inv_of_mul_eq_one_left h1.symm]
        exact inv_mem (hx _ hm₁) }
  obtain ⟨x, hx⟩ := mem_preN.mp hm
  have hxS : x ∈ S := by
    rw [← Finset.univ_sum_single x]
    exact AddSubgroup.sum_mem _ fun k _ => hgen k (x k)
  exact hxS m hx

include hθ hC in
theorem commutatorElement_mem_of_single_right (hr : 2 ≤ r) {m : E} (hm : m ∈ preN θ)
    (hgen : ∀ (k : Fin r) (b : K) (m' : E), IsN θ (Pi.single k b) m' → ⁅m, m'⁆ ∈ Vt) {m' : E}
    (hm' : m' ∈ preN θ) : ⁅m, m'⁆ ∈ Vt := by
  let S : AddSubgroup (Fin r → K) :=
    { carrier := {y | ∀ m', IsN θ y m' → ⁅m, m'⁆ ∈ Vt}
      zero_mem' := fun m' hm' => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm_of_mem_preV_of_mem_preN hθ hC hr (isN_zero_iff.mp hm') hm).symm]
        exact one_mem _
      add_mem' := by
        intro x y hx hy m' hm'
        obtain ⟨m₁, hm₁⟩ := exists_isN hθ x
        have hm₂ : IsN θ y (m₁⁻¹ * m') := (hm₁.inv.mul hm').congr (by abel)
        rw [show m' = m₁ * (m₁⁻¹ * m') by group,
          commutatorElement_mul_right_preN hθ hC hr hm hm₁.mem hm₂.mem]
        exact mul_mem (hx m₁ hm₁) (hy _ hm₂)
      neg_mem' := by
        intro x hx m' hm'
        have hm₁ : IsN θ x m'⁻¹ := hm'.inv.congr (neg_neg x)
        have h1 := commutatorElement_mul_right_preN hθ hC hr hm hm'.mem hm₁.mem
        rw [mul_inv_cancel, commutatorElement_one_right] at h1
        rw [eq_inv_of_mul_eq_one_left h1.symm]
        exact inv_mem (hx _ hm₁) }
  obtain ⟨y, hy⟩ := mem_preN.mp hm'
  have hyS : y ∈ S := by
    rw [← Finset.univ_sum_single y]
    exact AddSubgroup.sum_mem _ fun k _ => hgen k (y k)
  exact hyS m' hy

include hθ hC hVt in
theorem commutatorElement_mem_herm_complement (hr : 2 ≤ r) {m m' : E} (hm : m ∈ preN θ)
    (hm' : m' ∈ preN θ) : ⁅m, m'⁆ ∈ Vt := by
  refine commutatorElement_mem_of_single_right hθ hC hr hm (fun k b m'₀ hm'₀ => ?_) hm'
  refine commutatorElement_mem_of_single_left hθ hC hr hm'₀.mem (fun k' a m₀ hm₀ => ?_) hm
  by_cases hk : k' = k
  · subst hk
    exact commutatorElement_mem_of_eq hθ hC hVt hr hm₀ hm'₀
  · exact commutatorElement_mem_of_ne hθ hC hVt hr hk hm₀ hm'₀

end Commutator

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
