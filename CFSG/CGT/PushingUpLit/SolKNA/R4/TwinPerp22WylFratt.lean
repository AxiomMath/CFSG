module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22WylHull
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Conj
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Group

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp22Wyl

section Prod

variable {Y : Type} [Group Y]

theorem prod_perm_mul {W : Subgroup Y} (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (a δ : Fin 4 → Y)
    (ha : ∀ i, a i ∈ W) (hδ : ∀ i, δ i ∈ W) (π : Equiv.Perm (Fin 4)) :
    (a (π 0) * δ 0) * (a (π 1) * δ 1) * (a (π 2) * δ 2) * (a (π 3) * δ 3) =
      (a 0 * a 1 * a 2 * a 3) * (δ 0 * δ 1 * δ 2 * δ 3) := by
  let _ : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with mul_comm := fun x y => Subtype.ext (hc x x.2 y y.2) }
  let a' : Fin 4 → ↥W := fun i => ⟨a i, ha i⟩
  let δ' : Fin 4 → ↥W := fun i => ⟨δ i, hδ i⟩
  have h1 : ∏ i, (a' (π i) * δ' i) = (∏ i, a' (π i)) * ∏ i, δ' i := Finset.prod_mul_distrib
  have h2 : ∏ i, a' (π i) = ∏ i, a' i := Equiv.prod_comp π a'
  rw [h2] at h1
  simp only [Fin.prod_univ_four] at h1
  exact congrArg Subtype.val h1

end Prod

section Fratt


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}

theorem exists_conj_member (h : PerpHypR r n Y R S t)
    (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) (i : Fin 4) :
    ∃ j, conjSub c (F.ρ i).K = (F.ρ j).K := by
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hJ : (F.ρ i).K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    ⟨(F.ρ i).hK, t, hU, F.hz i⟩
  obtain ⟨hΩ', w, hw, hwJ⟩ := h.conj_mem_twinSet hJ hc
  have hwt : w = t := (hU.eq hw).symm
  rw [hwt] at hwJ
  exact F.hcover _ hΩ' hwJ

theorem cls_rel_a (hr : 4 ≤ r) (h : PerpHypR r n Y R S t)
    (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W) {c' : Y}
    (hc' : c' ∈ Subgroup.centralizer ({t} : Set Y)) (i j : Fin 4)
    (hij : conjSub c' (F.ρ i).K = (F.ρ j).K) :
    ∃ δ : Y, (δ = 1 ∨ δ = t) ∧
      Perp24.cls (Subgroup.centralizer ({t} : Set Y)) (c' * F.a i * c'⁻¹) =
        Perp24.cls (Subgroup.centralizer ({t} : Set Y)) (F.a j * δ) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  obtain ⟨xi, hxi, hxi_eq⟩ := a_eq_sq hr h c F i
  obtain ⟨xj, hxj, hxj_eq⟩ := a_eq_sq hr h c F j
  have hct : c' * t * c'⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc'
    calc c' * t * c'⁻¹ = t * c' * c'⁻¹ := by rw [this]
      _ = t := by group
  have hxK : c' * xi * c'⁻¹ ∈ (F.ρ j).K := by
    have := conj_mem_conjSub (n := c') hxi.1
    rwa [hij] at this
  have hLC : (F.ρ j).K ≤ C := isUniqueInvolution_le_centralizer (F.hz j)
  have hOL : oddCoreIn (F.ρ j).K ≤ oddCoreIn C :=
    oddCoreIn_le_of_isSubnormal (h.partIHypG.cls.isSubnormal_of_uniqueInvolution (F.ρ j).hK (F.hz j))
  have hp : c' * F.a i * c'⁻¹ = (c' * xi * c'⁻¹) * (c' * xi * c'⁻¹) := by rw [hxi_eq]; group
  have hp2 : (c' * F.a i * c'⁻¹) * (c' * F.a i * c'⁻¹) = t := by
    calc (c' * F.a i * c'⁻¹) * (c' * F.a i * c'⁻¹) = c' * (F.a i * F.a i) * c'⁻¹ := by group
      _ = t := by rw [F.a_sq i, hct]
  have hrel := Perp24.cls_rel h (F.ρ j).hK hLC hOL (F.hz j).mem hxK hxj.1 hp hxj_eq hp2 (F.a_sq j)
  have hajC : F.a j ∈ C := hLC (F.a_mem_K j)
  have hajinv : (F.a j)⁻¹ = F.a j * t := by
    apply inv_eq_of_mul_eq_one_right
    calc F.a j * (F.a j * t) = (F.a j * F.a j) * t := by group
      _ = 1 := by rw [F.a_sq j]; exact F.z_sq
  have haiC : F.a i ∈ C := isUniqueInvolution_le_centralizer (F.hz i) (F.a_mem_K i)
  have hpC : c' * F.a i * c'⁻¹ ∈ C := C.mul_mem (C.mul_mem hc' haiC) (C.inv_mem hc')
  rcases hrel with h1 | h1
  · exact ⟨1, Or.inl rfl, by rw [mul_one]; exact h1.symm⟩
  · refine ⟨t, Or.inr rfl, ?_⟩
    have h2 : Perp24.cls C (F.a j * t) = Perp24.cls C (c' * F.a i * c'⁻¹) := by
      rw [← hajinv, Perp24.cls_inv hajC, h1, inv_inv]
    exact h2.symm

theorem conj_t'_mem (hr : 4 ≤ r) (h : PerpHypR r n Y R S t)
    (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {c' : Y}
    (hc' : c' ∈ Subgroup.centralizer ({t} : Set Y)) :
    c' * F.t' * c'⁻¹ ∈ F.E ⊔ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
  classical
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  choose φ hφ using fun i => exists_conj_member h F hc' i
  have hφinj : Function.Injective φ := fun i i' he => by
    by_contra hne
    apply F.hne i i' hne
    have : conjSub c' (F.ρ i).K = conjSub c' (F.ρ i').K := by rw [hφ i, hφ i', he]
    exact Generic.conjSub_injective c' this
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφinj
  let π : Equiv.Perm (Fin 4) := Equiv.ofBijective φ hφbij
  choose δ hδ hcls using fun i => cls_rel_a hr h F c hc' i (φ i) (hφ i)
  have haiC : ∀ i, F.a i ∈ C := fun i => isUniqueInvolution_le_centralizer (F.hz i) (F.a_mem_K i)
  have hpC : ∀ i, c' * F.a i * c'⁻¹ ∈ C := fun i =>
    C.mul_mem (C.mul_mem hc' (haiC i)) (C.inv_mem hc')
  have hδW : ∀ i, δ i ∈ W := fun i => by
    rcases hδ i with h' | h'
    · rw [h']; exact W.one_mem
    · rw [h']; exact F.z_mem_W c
  have hδC : ∀ i, δ i ∈ C := fun i => by
    rcases hδ i with h' | h'
    · rw [h']; exact C.one_mem
    · rw [h']; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hmem : ∀ i, F.a (φ i) * δ i ∈ C := fun i => C.mul_mem (haiC _) (hδC i)
  have hm4 : ∀ x y u v : Y, x ∈ C → y ∈ C → u ∈ C → v ∈ C →
      Perp24.cls C (x * y * u * v) =
        Perp24.cls C x * Perp24.cls C y * Perp24.cls C u * Perp24.cls C v := by
    intro x y u v hx hy hu hv
    rw [Perp24.cls_mul (C.mul_mem (C.mul_mem hx hy) hu) hv,
      Perp24.cls_mul (C.mul_mem hx hy) hu, Perp24.cls_mul hx hy]
  have hprod : c' * F.t' * c'⁻¹ = (c' * F.a 0 * c'⁻¹) * (c' * F.a 1 * c'⁻¹) *
      (c' * F.a 2 * c'⁻¹) * (c' * F.a 3 * c'⁻¹) := by rw [F.hrel]; group
  have hcls_prod : Perp24.cls C (c' * F.t' * c'⁻¹) =
      Perp24.cls C ((F.a (φ 0) * δ 0) * (F.a (φ 1) * δ 1) * (F.a (φ 2) * δ 2) *
        (F.a (φ 3) * δ 3)) := by
    rw [hprod, hm4 _ _ _ _ (hpC 0) (hpC 1) (hpC 2) (hpC 3), hcls 0, hcls 1, hcls 2, hcls 3,
      ← hm4 _ _ _ _ (hmem 0) (hmem 1) (hmem 2) (hmem 3)]
  have hW4 := prod_perm_mul hc F.a δ F.a_mem_W hδW π
  have hπ : ∀ i, π i = φ i := fun i => rfl
  simp only [hπ] at hW4
  rw [hW4, ← F.hrel] at hcls_prod
  have hmul : ∀ x y : Y, (x = 1 ∨ x = t) → (y = 1 ∨ y = t) → (x * y = 1 ∨ x * y = t) := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left; rw [hx, hy, one_mul]
    · right; rw [hx, hy, one_mul]
    · right; rw [hx, hy, mul_one]
    · left; rw [hx, hy]; exact F.z_sq
  have hD := hmul _ _ (hmul _ _ (hmul _ _ (hδ 0) (hδ 1)) (hδ 2)) (hδ 3)
  have ht'C : F.t' ∈ C := t'_mem_centralizer F c hc
  have hDC : δ 0 * δ 1 * δ 2 * δ 3 ∈ C :=
    C.mul_mem (C.mul_mem (C.mul_mem (hδC 0) (hδC 1)) (hδC 2)) (hδC 3)
  have htDE : F.t' * (δ 0 * δ 1 * δ 2 * δ 3) ∈ F.E := by
    rcases hD with hD | hD
    · rw [hD, mul_one]; exact F.t'_mem_E
    · rw [hD]; exact F.E.mul_mem F.t'_mem_E F.z_mem_E
  have hcC : c' * F.t' * c'⁻¹ ∈ C := C.mul_mem (C.mul_mem hc' ht'C) (C.inv_mem hc')
  have hO := (Perp24.cls_eq_iff (C.mul_mem ht'C hDC) hcC).mp hcls_prod.symm
  have e : c' * F.t' * c'⁻¹ = (F.t' * (δ 0 * δ 1 * δ 2 * δ 3)) *
      ((F.t' * (δ 0 * δ 1 * δ 2 * δ 3))⁻¹ * (c' * F.t' * c'⁻¹)) := by group
  rw [e]
  exact Subgroup.mul_mem_sup htDE hO

theorem frattini (hr : 4 ≤ r) (h : PerpHypR r n Y R S t)
    (F : WylFrame (CoreAssembly.conjClass (tightCore R)) W t)
    (c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W)
    (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    ∀ c' ∈ Subgroup.centralizer ({t} : Set Y),
      ∃ o ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)),
        ∃ m ∈ Subgroup.centralizer ({t} : Set Y),
          m ∈ Subgroup.normalizer (F.E : Set Y) ∧ c' = o * m := by
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hEC : F.E ≤ C := by
    rw [WylFrame.E, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact htC
    · rw [Set.mem_singleton_iff.mp hx]; exact t'_mem_centralizer F c hc
  have hct : ∀ c' ∈ C, c' * t * c'⁻¹ = t := fun c' hc' => by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc'
    calc c' * t * c'⁻¹ = t * c' * c'⁻¹ := by rw [this]
      _ = t := by group
  have hEO : ∀ c' ∈ C, ∀ x ∈ F.E, c' * x * c'⁻¹ ∈ F.E ⊔ oddCoreIn C := by
    intro c' hc' x hx
    have hzE : t ∈ F.E ⊔ oddCoreIn C := Subgroup.mem_sup_left F.z_mem_E
    have h1 := conj_t'_mem hr h F c hc hc'
    rcases F.E_cases c hc x hx with rfl | rfl | rfl | rfl
    · simp only [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    · rw [hct c' hc']; exact hzE
    · exact h1
    · have e : c' * (t * F.t') * c'⁻¹ = (c' * t * c'⁻¹) * (c' * F.t' * c'⁻¹) := by group
      rw [e, hct c' hc']
      exact Subgroup.mul_mem _ hzE h1
  have hOn : ∀ c' ∈ C, ∀ x ∈ oddCoreIn C, c' * x * c'⁻¹ ∈ oddCoreIn C :=
    fun c' hc' x hx => conj_mem_oddCoreIn hc' hx
  exact fun c' hc' => Perp24.exists_mul_normalizer_of_le hEC (oddCoreIn_le C) hOn hEO
    (odd_card_oddCoreIn C) (F.E_isPGroup c hc) hc'

end Fratt

end Perp22Wyl

end CFSG.CGT.PushingUpLit.SolKNA.R4
