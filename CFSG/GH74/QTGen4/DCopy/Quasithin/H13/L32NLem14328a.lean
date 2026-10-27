module

public import CFSG.Quasithin.H13.L32NLem14328a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L32NSet14

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Setting_F4

variable (S : Setting_F4 G T L V V₂)
include S

theorem isSimple_autOn_F4 : IsSimpleGroup ↥(autOn L V) := by
  have hLV := S.LV_F4
  have hsurj := InternalSec.autOnHom_surjective hLV
  have hker : (InternalSec.autOnHom hLV).ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [InternalSec.mem_ker_autOnHom]
    constructor
    · intro hl
      have h1 : (l : G) ∈ pCoreOf 2 L := by
        rw [← S.cent_eq_F4]
        exact ⟨l.2, hl⟩
      obtain ⟨q, hq, hql⟩ := h1
      have : q = l := Subtype.ext hql
      rw [← this]
      exact hq
    · intro hl
      have h1 : (l : G) ∈ pCoreOf 2 L := ⟨l, hl, rfl⟩
      rw [← S.cent_eq_F4] at h1
      exact h1.2
  obtain ⟨e⟩ := S.h1281_F4.quot
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Vol2Native.A312L.Seven.slThree_isSimple
  exact ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans e)).isSimpleGroup

theorem eq_of_autOn_eq_F4 {X : Subgroup G} (hXL : X ≤ L)
    (hXn : pCoreOf 2 L ≤ Subgroup.normalizer (X : Set G)) (hA : autOn X V = autOn L V) :
    X = L := by
  have hLV := S.LV_F4

  have hdec : ∀ l ∈ L, ∃ x ∈ X, x⁻¹ * l ∈ pCoreOf 2 L := by
    intro l hl
    have hmem : conjAct V ⟨l, hLV hl⟩ ∈ autOn X V := by
      rw [hA]
      exact ⟨⟨l, hLV hl⟩, hl, rfl⟩
    obtain ⟨⟨x, hxN⟩, hxX, hx⟩ := hmem
    refine ⟨x, hxX, ?_⟩
    rw [← S.cent_eq_F4]
    refine ⟨L.mul_mem (L.inv_mem (hXL hxX)) hl, ?_⟩
    have h1 : conjAct V ((⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * ⟨l, hLV hl⟩) = 1 := by
      rw [map_mul, map_inv, hx, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.mp h1
  refine S.hH.faithful.2.1 X hXL ⟨fun x hx l => ?_⟩ fun l hl => ?_
  · obtain ⟨y, hyX, hyq⟩ := hdec l l.2
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hq := hXn hyq
    have e : ((l * x * l⁻¹ : ↥L) : G) =
        y * ((y⁻¹ * l) * x * (y⁻¹ * l)⁻¹) * y⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact X.mul_mem (X.mul_mem hyX ((Subgroup.mem_normalizer_iff.mp hq _).mp hx)) (X.inv_mem hyX)
  · obtain ⟨y, hyX, hyq⟩ := hdec l hl
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hyq⟩
    have hk' : (y⁻¹ * l) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have := pow_mul_inv_mem hyX (hXn hyq) (2 ^ k)
    rwa [hk', inv_one, mul_one, mul_inv_cancel_left] at this

theorem autOn_eq_of_normal_F4 {X : Subgroup G} (hXL : X ≤ L)
    (hXn : L ≤ Subgroup.normalizer (X : Set G)) (hX1 : ¬ X ≤ Subgroup.centralizer (V : Set G)) :
    autOn X V = autOn L V := by
  have := S.isSimple_autOn_F4
  have hLV := S.LV_F4
  have hAB : autOn X V ≤ autOn L V := by
    rintro φ ⟨⟨x, hxN⟩, hxX, rfl⟩
    exact ⟨⟨x, hxN⟩, hXL hxX, rfl⟩
  set A' := (autOn X V).subgroupOf (autOn L V) with hA'
  have hn : A'.Normal := by
    refine ⟨fun φ hφ ψ => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hφ ⊢
    obtain ⟨⟨x, hxN⟩, hxX, hx⟩ := hφ
    obtain ⟨⟨l, hlN⟩, hlL, hl⟩ := ψ.2
    refine ⟨⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hXn hlL) x).mp hxX
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hx, hl]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A' with hb | ht
  · exfalso
    apply hX1
    intro x hxX
    have hmem : (⟨conjAct V ⟨x, hLV (hXL hxX)⟩, ⟨_, hXL hxX, rfl⟩⟩ : ↥(autOn L V)) ∈ A' :=
      Subgroup.mem_subgroupOf.mpr ⟨_, hxX, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact A4.conjAct_eq_one_iff.mp (congrArg Subtype.val hmem)
  · refine le_antisymm hAB fun φ hφ => ?_
    have : (⟨φ, hφ⟩ : ↥(autOn L V)) ∈ A' := by rw [ht]; trivial
    exact Subgroup.mem_subgroupOf.mp this

theorem conjClosure_eq_F4 {X : Subgroup G} (hXL : X ≤ L)
    (hX1 : ¬ X ≤ Subgroup.centralizer (V : Set G)) : conjClosure X L = L := by
  have hNL : conjClosure X L ≤ L := conjClosure_le fun h hh x hx =>
    L.mul_mem (L.mul_mem hh (hXL hx)) (L.inv_mem hh)
  refine S.eq_of_autOn_eq_F4 hNL ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans
    (le_normalizer_conjClosure _ _)) (S.autOn_eq_of_normal_F4 hNL (le_normalizer_conjClosure _ _)
      fun h => hX1 ((le_conjClosure X L).trans h))

end Setting_F4

end L32NSet14

end CFSG.Quasithin.H13
