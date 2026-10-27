module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.CentralQuotient
public import CFSG.Goldschmidt.Steps.G37Quot
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

namespace Up34Chev2

theorem isQuasisimple_of_open_c2 {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, exists_not_comm_of_quasisimple h⟩

theorem exists_component_of_isLThreeFour_two {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hβ : PerfectInLayer β) {I : Subgroup S} (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hT : IsLThreeFour (barOf 3 I)) :
    IsComponentOf I (fixSubgroup β) ∧ IsLThreeFour (↥I ⧸ Subgroup.center ↥I) ∧
      ∀ z ∈ Subgroup.center ↥I, z ^ 3 = 1 → z = 1 := by
  have hle : I ≤ GLALayer (fixSubgroup β) := hβ I hI.1 (glaPComponent_perfect hI)
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hI hle
  have hq : CFSG.IsQuasisimple ↥I := isQuasisimple_of_open_c2 hcomp.2.2
  obtain ⟨hsimp, hnab⟩ := isSimpleGroup_of_isLThreeFour hT
  have hZ : Subgroup.center (barOf 3 I) = ⊥ := up34_center_eq_bot_of_simple hnab
  set N : Subgroup ↥I := GLAPPrimeCore 3 ↥I with hN
  have hNn : N.Normal := GLAPPrimeCore.normal 3 ↥I
  have hNZ : N ≤ Subgroup.center ↥I := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with h | h
    · exfalso
      have hsub : Subsingleton (barOf 3 I) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            change a⁻¹ * b ∈ GLAPPrimeCore 3 ↥I
            rw [← hN, h]
            exact Subgroup.mem_top _
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subsingleton.elim _ _)
    · exact h
  have hZN : Subgroup.center ↥I ≤ N := by
    intro z hz
    have hz' : (QuotientGroup.mk z : barOf 3 I) ∈ Subgroup.center (barOf 3 I) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.1 hz g
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz'
    exact hz'
  have hNeq : N = Subgroup.center ↥I := le_antisymm hNZ hZN
  refine ⟨hcomp, IsLThreeFour.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hNeq) hT, ?_⟩
  intro z hz hz3
  have hzN : z ∈ N := hZN hz
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 ↥I)
  by_contra hz1
  have hord : orderOf (⟨z, hzN⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hz3 hz1
  have := orderOf_dvd_natCard (⟨z, hzN⟩ : N)
  rw [hord] at this
  exact hN3 this

section Helpers

variable {X T : Type*} [Group X] [Group T]

theorem isSolvable_of_surjective_of_ker_le_c2 {A G Q : Type*} [Group A] [Group G] [Group Q]
    [Group.IsSolvable Q] (ψ : A →* Q) (φ : A →* G) (hφ : Function.Surjective φ)
    (hker : ψ.ker ≤ φ.ker) : Group.IsSolvable G := by
  haveI : Group.IsSolvable (A ⧸ ψ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective ψ)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective ψ.ker φ hφ hker)

theorem normal_map_subgroupOf_map_c2 (π : X →* T) {A L : Subgroup X}
    (hL : ∀ c ∈ A, ∀ g ∈ L, c * g * c⁻¹ ∈ L) :
    ((L.map π).subgroupOf (A.map π)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨c, hc, hcg⟩ := g.2
  refine ⟨c * f * c⁻¹, hL c hc f hf, ?_⟩
  simp only [map_mul, map_inv, hcg, hfx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem conj_mem_iSup_c2 {ι : Type*} {A : Subgroup X} (F : ι → Subgroup X)
    (hF : ∀ i, ∀ c ∈ A, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i) :
    ∀ c ∈ A, ∀ g ∈ ⨆ i, F i, c * g * c⁻¹ ∈ ⨆ i, F i := by
  intro c hc g hg
  refine Subgroup.iSup_induction F (C := fun x => c * x * c⁻¹ ∈ ⨆ i, F i) hg
    (fun i x hx => Subgroup.mem_iSup_of_mem i (hF i c hc x hx)) (by simp) fun x y hx hy => ?_
  have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx hy

theorem not_le_ker_of_isQuasisimple_c2 (π : X →* T) (hker : π.ker ≤ Subgroup.center X)
    {K : Subgroup X} (hK : CFSG.IsQuasisimple K) : ¬ K ≤ π.ker := by
  intro hKπ
  obtain ⟨-, -, a, b, hab⟩ := hK
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker (hKπ x.2)) y).symm

end Helpers

variable {X T : Type} [Group X] [Group T] [Finite X] [Finite T]

theorem perfect_le_map_iSup_of_centralQuotient_c2 (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i)
    {P : Subgroup T} (hPC : P ≤ fixSubgroup β) (hP : ⁅P, P⁆ = P) :
    P ≤ (⨆ i, F i).map π := by
  have hPN : P ≤ (fixSubgroup α).map π :=
    le_map_fixSubgroup_of_perfect π hker α β hαβ hπ hPC hP
  have hDα : (⨆ i, F i) ≤ fixSubgroup α := iSup_le hFα
  have hMN : (⨆ i, F i).map π ≤ (fixSubgroup α).map π := Subgroup.map_mono hDα
  haveI : (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
    normal_map_subgroupOf_map_c2 π (conj_mem_iSup_c2 F hFn)
  have hNM : Group.IsSolvable (↥((fixSubgroup α).map π) ⧸
      ((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π)) := by
    refine isSolvable_of_surjective_of_ker_le_c2 ψ
      ((QuotientGroup.mk' (((⨆ i, F i).map π).subgroupOf ((fixSubgroup α).map π))).comp
        (π.subgroupMap (fixSubgroup α)))
      ((QuotientGroup.mk'_surjective _).comp (π.subgroupMap_surjective _)) fun x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact ⟨x, hψ x hx, rfl⟩
  exact perfect_le_of_solvable_quotient hMN hNM hPN hP

theorem noL34Layer_of_centralQuotient_two (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (α : MulAut X) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hFq : ∀ i, CFSG.IsQuasisimple (F i)) {Q : Type*} [Group Q] [Group.IsSolvable Q]
    (ψ : ↥(fixSubgroup α) →* Q) (hψ : ∀ x : ↥(fixSubgroup α), ψ x = 1 → (x : X) ∈ ⨆ i, F i)
    (hno : ∀ i, IsLThreeFour (↥(F i) ⧸ Subgroup.center ↥(F i)) →
      ∃ z : X, z ∈ F i ∧ (∀ g ∈ F i, g * z = z * g) ∧ z ^ 3 = 1 ∧ π z ≠ 1) :
    NoL34Layer β := by
  have hPIL : PerfectInLayer β :=
    perfectInLayer_of_centralQuotient π hπ hker α β hαβ F hFα hFn hFq ψ hψ
  intro I hI hT
  obtain ⟨hcomp, hIT, hIZ⟩ := exists_component_of_isLThreeFour_two hPIL hI hT
  have hIM : I ≤ (⨆ i, F i).map π :=
    perfect_le_map_iSup_of_centralQuotient_c2 π hπ hker α β hαβ F hFα hFn ψ hψ hI.1
      (glaPComponent_perfect hI)
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β := map_fixSubgroup_le π hker α β hαβ
  haveI hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    normal_map_fixSubgroup π hker α β hαβ hπ
  have hGcomp : ∀ i, IsComponentOf ((F i).map π) (fixSubgroup β) := by
    intro i
    have hq : CFSG.IsQuasisimple ((F i).map π) :=
      CFSG.LocalCores.isQuasisimple_map (hFq i) π
        (not_le_ker_of_isQuasisimple_c2 π hker (hFq i))
    haveI : (((F i).map π).subgroupOf ((fixSubgroup α).map π)).Normal :=
      normal_map_subgroupOf_map_c2 π (hFn i)
    exact isComponentOf_of_normal_normal (Subgroup.map_mono (hFα i)) hNC inferInstance hNn hq
  have hIq : CFSG.Open.IsQuasisimple ↥I := hcomp.2.2
  have hex : ∃ i, (F i).map π ≤ I := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ i, ⁅(F i).map π, I⁆ = ⊥ := fun i =>
      (b3Lie_comp_le_or_comm (hGcomp i) hI.1 hI.2.1).resolve_left (hcon i)
    have hMcI : (⨆ i, (F i).map π) ≤ Subgroup.centralizer (I : Set T) :=
      iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i)
    have hIcI : I ≤ Subgroup.centralizer (I : Set T) := by
      refine le_trans ?_ hMcI
      rw [← Subgroup.map_iSup]
      exact hIM
    have hab : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1 (hIcI hb)) a ha
    obtain ⟨-, -, a, b, hab'⟩ := isQuasisimple_of_open_c2 hIq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab' ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hab a a.2 b b.2)
  obtain ⟨i, hiI⟩ := hex
  have hGsn : IsSubnormal ((F i).map π) I :=
    isSubnormal_of_le_of_le (hGcomp i).2.1 hiI hI.1
  have hGq : CFSG.Open.IsQuasisimple ↥((F i).map π) := (hGcomp i).2.2
  have hGp : ⁅(F i).map π, (F i).map π⁆ = (F i).map π := Subgroup.isPerfect_iff.1 ⟨hGq.1⟩
  have hGne : (F i).map π ≠ ⊥ := by
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_open_c2 hGq)
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hGeq : (F i).map π = I :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hIq hGsn hGp hGne
  subst hGeq
  let φ : ↥(F i) →* ↥((F i).map π) := π.subgroupMap (F i)
  have hφ : Function.Surjective φ := π.subgroupMap_surjective (F i)
  have hkc : φ.ker ≤ Subgroup.center ↥(F i) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπx : π (x : X) = 1 := by simpa [φ] using congrArg Subtype.val hx
    have hxz : (x : X) ∈ Subgroup.center X := hker hπx
    rw [Subgroup.mem_center_iff] at hxz ⊢
    intro g
    exact Subtype.ext (hxz g)
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv (hFq i).1 φ hφ hkc
  obtain ⟨z, hzF, hzc, hz3, hzπ⟩ := hno i (IsLThreeFour.of_mulEquiv e.symm hIT)
  have hπzI : π z ∈ (F i).map π := Subgroup.mem_map_of_mem π hzF
  have hcen : (⟨π z, hπzI⟩ : ↥((F i).map π)) ∈ Subgroup.center ↥((F i).map π) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.1 g.2
    apply Subtype.ext
    change (g : T) * π z = π z * (g : T)
    rw [← hgg, ← map_mul, ← map_mul, hzc g' hg']
  have h3 : (⟨π z, hπzI⟩ : ↥((F i).map π)) ^ 3 = 1 := by
    apply Subtype.ext
    change π z ^ 3 = 1
    rw [← map_pow, hz3, map_one]
  exact hzπ (congrArg Subtype.val (hIZ _ hcen h3))

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
