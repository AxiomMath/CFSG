module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Aut

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Gamma

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def tG (hb : PAB G L t E W z) (a : PA5 L t E z) : ↥(Cen a.ub) :=
  ⟨t, mem_Cen.2 (PA5.t_ub a hb)⟩

theorem tG_mul_tG (hb : PAB G L t E W z) (a : PA5 L t E z) : tG hb a * tG hb a = 1 :=
  Subtype.ext hb.t_mul_t

theorem PA5.J_le_Cen (hb : PAB G L t E W z) (a : PA5 L t E z) :
    derivedIn a.Abar ≤ Cen a.ub := fun j hj =>
  mem_Cen.2 (PA5.Abar_comm_ub hb a (derivedIn_le _ hj))

@[expose] def JG (hb : PAB G L t E W z) (a : PA5 L t E z) : Subgroup ↥(Cen a.ub) :=
  (derivedIn a.Abar).subgroupOf (Cen a.ub)

@[expose] def JG_equiv (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ↥(JG hb a) ≃* ↥(derivedIn a.Abar) := Subgroup.subgroupOfEquivOfLe (PA5.J_le_Cen hb a)

theorem JG_simple (hb : PAB G L t E W z) (a : PA5 L t E z) : IsSimpleGroup ↥(JG hb a) :=
  (MulEquiv.isSimpleGroup_congr (JG_equiv hb a)).2 (s8_J_simple a.Abar a.eAbar)

theorem JG_nonab (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∃ x y : ↥(JG hb a), x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := s8_J_nonab a.Abar a.eAbar
  exact ⟨(JG_equiv hb a).symm x, (JG_equiv hb a).symm y, fun h =>
    hxy ((JG_equiv hb a).symm.injective (by simpa using h))⟩

theorem JG_perfect (hb : PAB G L t E W z) (a : PA5 L t E z) : ⁅JG hb a, JG hb a⁆ = JG hb a :=
  commutator_eq_self_of_simple (JG_simple hb a) (JG_nonab hb a)

theorem JG_comm_t (hb : PAB G L t E W z) (a : PA5 L t E z) {y : ↥(Cen a.ub)}
    (hy : y ∈ JG hb a) : y * tG hb a = tG hb a * y :=
  Subtype.ext (PA5.Abar_comm_t hb a (derivedIn_le _ hy))

theorem JG_hHJ (hb : PAB G L t E W z) (a : PA5 L t E z) (Q : Subgroup ↥(Cen a.ub))
    (hQt : ∀ q ∈ Q, q * tG hb a = tG hb a * q) (hQ : ⁅Q, Q⁆ = Q) : Q ≤ JG hb a := by
  have h := PA5.perfect_le_J hb a (Q.map (Cen a.ub).subtype)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hQt y hy))
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact mem_Cen.1 y.2)
    (by rw [← Subgroup.map_commutator, hQ])
  intro q hq
  exact h ⟨q, hq, rfl⟩

theorem JG_hZ (hb : PAB G L t E W z) (a : PA6 L t E z) (K : Subgroup ↥(Cen a.ub))
    (hK : IsComponent K) : ¬ ∀ k ∈ K, ∀ j ∈ JG hb a.toPA5, k * j = j * k := by
  intro h
  have hmem : ∀ k : ↥K, ((k : ↥(Cen a.ub)) : G) ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) := by
    intro k
    rw [mem_centralizer_iff]
    intro j hj
    have := h k k.2 ⟨j, PA5.J_le_Cen hb a.toPA5 hj⟩ hj
    exact (congrArg Subtype.val this).symm
  let f : ↥K →* ↥(centralizer ((derivedIn a.Abar : Subgroup G) : Set G)) :=
    ((Cen a.ub).subtype.comp K.subtype).codRestrict _ hmem
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have hsolv : Group.IsSolvable ↥K := by
    have := a.Z_solv
    exact Group.isSolvable_of_isSolvable_injective hinj
  have : Nontrivial ↥K := isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K hsolv

theorem JG_le_layer (hb : PAB G L t E W z) (a : PA7 L t E z) :
    JG hb a.toPA6.toPA5 ≤ layer ↥(Cen a.ub) := by
  intro y hy
  have h1 : (y : G) ∈ GorensteinWalter.componentLayerOf (Cen a.ub) :=
    a.E₁_le (a.J_E₁ hy)
  rw [componentLayerOf_eq] at h1
  obtain ⟨y', hy', hyy⟩ := h1
  have : y' = y := Subtype.ext hyy
  rwa [← this]

theorem exists_orbit (hb : PAB G L t E W z) (a : PA7 L t E z) :
    ∃ K : Subgroup ↥(Cen a.ub), IsComponent K ∧
      ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' →
        K' = K ∨ K' = cj (tG hb a.toPA6.toPA5) K :=
  single_orbit (tG_mul_tG hb a.toPA6.toPA5) (JG_simple hb a.toPA6.toPA5) (JG_perfect hb a.toPA6.toPA5)
    (JG_le_layer hb a) (fun j hj => JG_comm_t hb a.toPA6.toPA5 hj)
    (fun Q _ hQt hQ => JG_hHJ hb a.toPA6.toPA5 Q hQt hQ) (JG_hZ hb a.toPA6)

end Gamma

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
