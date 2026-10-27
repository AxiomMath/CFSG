module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamAltCore
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Simple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Equiv Equiv.Perm
open scoped commutatorElement

theorem exists_perm_of_pow_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 5 ≤ n)
    (α : MulAut (alternatingGroup (Fin n))) (h5 : α ^ p = 1) :
    ∃ σ : Perm (Fin n), MulAut.conjNormal σ = α ∧ σ ^ p = 1 := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  have key : ∃ σ : Perm (Fin n), MulAut.conjNormal σ = α := by
    by_cases h6 : n = 6
    · subst h6
      have hout : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (alternatingGroup (Fin 6))) :=
        CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
      obtain ⟨m, hm⟩ := hout (QuotientGroup.mk α :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6)))
      have h5' : (QuotientGroup.mk α :
          CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6))) ^ p
            = 1 := by
        rw [← QuotientGroup.mk_pow, h5]
        rfl
      have hd5 := orderOf_dvd_of_pow_eq_one h5'
      have hd2 := orderOf_dvd_of_pow_eq_one hm
      have hcop : Nat.Coprime p (2 ^ m) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      have h1 : orderOf (QuotientGroup.mk α :
          CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6))) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hd5 hd2
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      obtain ⟨a, ha⟩ := h1
      refine ⟨(a : Perm (Fin 6)), ?_⟩
      rw [← ha]
      exact MulAut.conjNormal_val
    · obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).2 α
      exact ⟨σ, hσ⟩
  obtain ⟨σ, hσ⟩ := key
  refine ⟨σ, hσ, hinj ?_⟩
  rw [map_pow, hσ, h5, map_one]

theorem fixSubgroup_conjNormal_map {n : ℕ} (σ : Perm (Fin n)) :
    (fixSubgroup (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin n)))).map
        (alternatingGroup (Fin n)).subtype = B3FamAlt.centAlt σ := by
  ext y
  simp only [Subgroup.mem_map, mem_fixSubgroup, B3FamAlt.mem_centAlt]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : σ * (a : Perm (Fin n)) * σ⁻¹ = a := congrArg Subtype.val ha
    refine ⟨?_, mem_alternatingGroup.1 a.2⟩
    calc (a : Perm (Fin n)) * σ = σ * (a : Perm (Fin n)) * σ⁻¹ * σ := by rw [h1]
      _ = σ * a := by group
  · rintro ⟨h1, h2⟩
    refine ⟨⟨y, mem_alternatingGroup.2 h2⟩, ?_, rfl⟩
    apply Subtype.ext
    show σ * y * σ⁻¹ = y
    calc σ * y * σ⁻¹ = y * σ * σ⁻¹ := by rw [h1]
      _ = y := by group

theorem coreA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (α : MulAut (alternatingGroup (Fin n))) (hα : α ^ p = 1) :
    ∀ J : Subgroup (alternatingGroup (Fin n)), GLAPComponent p (fixSubgroup α) J →
      ∀ g ∈ J, ∀ o ∈ GLAPPrimeCoreOf p (fixSubgroup α), o * g = g * o := by
  obtain ⟨σ, rfl, hσ⟩ := exists_perm_of_pow_prime hp hp2 n hn α hα
  intro J hJ
  set ι : ↥(alternatingGroup (Fin n)) →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype with hι
  have hinj : Function.Injective ι := Subgroup.subtype_injective _
  have hX := fixSubgroup_conjNormal_map σ
  have hc : ∀ y ∈ fixSubgroup (MulAut.conjNormal σ : MulAut ↥(alternatingGroup (Fin n))) ⊓ ι.ker,
      ∀ x ∈ fixSubgroup (MulAut.conjNormal σ : MulAut ↥(alternatingGroup (Fin n))), x * y = y * x := by
    intro y hy x _
    have : y = 1 := hinj ((MonoidHom.mem_ker.1 hy.2).trans (map_one ι).symm)
    rw [this, mul_one, one_mul]
  have hJ' : GLAPComponent p (B3FamAlt.centAlt σ) (J.map ι) := by
    rw [← hX]
    exact glaPComponent_map_central hp ι hc hJ
  intro g hg o ho
  have hoO : (o : Perm (Fin n)) ∈ GLAPPrimeCoreOf p (B3FamAlt.centAlt σ) := by
    rw [← hX, ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p ι
      hinj]
    exact ⟨o, ho, rfl⟩
  exact Subtype.ext (B3FamAlt.core hp hp2 hσ hJ' (g : Perm (Fin n)) ⟨g, hg, rfl⟩ _ hoO)

theorem commutator_layer_eq_bot_A {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (α : MulAut (alternatingGroup (Fin n))) (hα : α ^ p = 1) :
    ⁅GLAPLayer p (fixSubgroup α), GLAPPrimeCoreOf p (fixSubgroup α)⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.2
    (sSup_le fun J hJ g hg => Subgroup.mem_centralizer_iff.2 fun o ho =>
      coreA hp hp2 hn α hα J hJ g hg o ho)

theorem b3SimpleAlt_holds : B3SimpleAlt := by
  intro S _ _ _ _ ⟨n, hn, ⟨e⟩⟩ β hβ
  have hp3 : Nat.Prime 3 := Nat.prime_three
  let π : S →* alternatingGroup (Fin n) := e.toMonoidHom
  have hπ : Function.Surjective π := e.surjective
  have hker : π.ker ≤ Subgroup.center S := by
    have : π.ker = ⊥ := (MonoidHom.ker_eq_bot_iff π).2 e.injective
    rw [this]; exact bot_le
  let β' : MulAut (alternatingGroup (Fin n)) := MulAut.congr e β
  have hββ : ∀ k, π (β k) = β' (π k) := fun k => by simp [β', π]
  have hβ' : β' ^ 3 = 1 := by
    show (MulAut.congr e : MulAut S →* MulAut (alternatingGroup (Fin n))) β ^ 3 = 1
    rw [← map_pow, hβ, map_one]
  have hB := commutator_layer_eq_bot_A hp3 (by norm_num) hn β' hβ'
  have hLmap : (GLAPLayer 3 (fixSubgroup β)).map π ≤ GLAPLayer 3 (fixSubgroup β') :=
    (map_glaPLayer_fixSubgroup_eq π hker β β' hββ hπ hp3).le
  have hOmap := map_glaPPrimeCoreOf_fixSubgroup_le π hker β β' hββ hπ hp3
  have hcm : (⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆).map π = ⊥ := by
    rw [Subgroup.map_commutator]
    exact eq_bot_iff.2 (hB ▸ Subgroup.commutator_mono hLmap hOmap)
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hcm

end CFSG.HardMathSupport.Solomon.Coordinator
