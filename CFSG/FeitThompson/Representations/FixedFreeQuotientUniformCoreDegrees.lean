module

public import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
import CFSG.FeitThompson.Representations.LinearIrreduciblesKillDerived
import CFSG.FeitThompson.Representations.CoprimeInvariantCharacterInduction
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import CFSG.FeitThompson.Representations.ProperNormalLayerDegreeIndexMember
import CFSG.FeitThompson.Representations.NormalInductionPreservesKernelSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FixedFreeCoreDegree

open Subgroup Module
open NormalInduction (conjClassFun conjClassFun_apply)
open scoped ComplexOrder

variable {K : Type*} [Group K]

theorem exists_monoidHom_units_of_apply_one_eq_one {X : Type*} [Group X]
    {θ : X → ℂ} (hθ : θ ∈ Irr X) (h1 : θ 1 = 1) : ∃ ν : X →* ℂˣ, (fun g => (ν g : ℂ)) = θ := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have hfr : finrank ℂ W.V = 1 := by
    have h := W.char_one
    rw [h1] at h
    exact_mod_cast h.symm
  obtain ⟨χ, hχ⟩ := Representation.exists_monoidHom_units_of_finrank_eq_one W.ρ hfr
  refine ⟨χ, funext fun g => ?_⟩
  have hg : W.ρ g = (χ g : ℂ) • LinearMap.id := by ext v; simpa using hχ g v
  rw [FDRep.character, hg]
  simp [hfr]

@[expose]
def inclHom {E D : Subgroup K} (hED : E ≤ D) : E →* D where
  toFun e := ⟨(e : K), hED e.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem inclHom_apply_coe {E D : Subgroup K} (hED : E ≤ D) (e : E) :
    ((inclHom hED e : D) : K) = (e : K) := (rfl)

private theorem eq_of_re_eq_of_norm_le {w : ℂ} {c : ℝ} (hre : w.re = c) (hnorm : ‖w‖ ≤ c) :
    w = (c : ℂ) := by
  have h1 : ‖w‖ = c := le_antisymm hnorm (hre ▸ Complex.re_le_norm w)
  have h3 := Complex.sq_norm w
  rw [Complex.normSq_apply, h1, hre] at h3
  have h4 : w.im * w.im = 0 := by nlinarith
  have h2 : w.im = 0 := by rcases mul_eq_zero.1 h4 with h | h <;> exact h
  exact Complex.ext (by simp [hre]) (by simp [h2])

theorem apply_eq_apply_one_of_mem_resConstituents {N : Subgroup K} [Finite K] [Fintype N]
    {θ : K → ℂ} (hθ : θ ∈ Irr K) {z : N} (hz : θ (z : K) = θ 1)
    {lam : N → ℂ} (hlam : lam ∈ resConstituents N θ) : lam z = lam 1 := by
  classical
  obtain ⟨hlamIrr, hlampos⟩ := mem_resConstituents.1 hlam
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hm⟩ := exists_multiplicities_resClassFun (N := N) hθ
  have hdeg : ∀ mu : irrFinset (N : Type _), ∃ n : ℕ, (mu : N → ℂ) 1 = (n : ℂ) ∧
      ∀ x : N, ‖(mu : N → ℂ) x‖ ≤ (n : ℝ) := fun mu =>
    NormalInduction.exists_degree_of_mem_irrChars
      (by rw [normalInduction_irrChars_eq_Irr]; exact mem_irrFinset.1 mu.2)
  choose d hd1 hd2 using hdeg
  set F : irrFinset (N : Type _) → ℝ := fun mu => (m mu : ℝ) * ((mu : N → ℂ) z).re with hF
  set G : irrFinset (N : Type _) → ℝ := fun mu => (m mu : ℝ) * (d mu : ℝ) with hG
  have hle : ∀ mu : irrFinset (N : Type _), F mu ≤ G mu := fun mu =>
    mul_le_mul_of_nonneg_left (((mu : N → ℂ) z).re_le_norm.trans (hd2 mu z)) (by positivity)
  have hvz : ∑ mu : irrFinset (N : Type _), F mu = (θ (z : K)).re := by
    have h := congrFun hm z
    rw [resClassFun_apply] at h
    rw [h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.re_sum, hF]
    exact Finset.sum_congr rfl fun mu _ => by simp [Complex.mul_re]
  have hv1 : ∑ mu : irrFinset (N : Type _), G mu = (θ 1).re := by
    have h := congrFun hm 1
    rw [resClassFun_apply] at h
    simp only [Subgroup.coe_one] at h
    rw [h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.re_sum, hG]
    exact Finset.sum_congr rfl fun mu _ => by rw [hd1 mu]; simp
  have heq := (Finset.sum_eq_sum_iff_of_le (fun mu _ => hle mu)).1 (by rw [hvz, hv1, hz])
  set l : irrFinset (N : Type _) := ⟨lam, mem_irrFinset.2 hlamIrr⟩ with hl
  have hmpos : 0 < m l := by
    have h := cfInner_eq_multiplicity hm l
    rw [h] at hlampos
    exact_mod_cast hlampos
  have hre : (lam z).re = (d l : ℝ) := by
    have hm0 : (m l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hmpos.ne'
    simpa [hF, hG, hl] using mul_left_cancel₀ hm0 (heq l (Finset.mem_univ l))
  rw [eq_of_re_eq_of_norm_le hre (hd2 l z)]
  rw [show ((d l : ℝ) : ℂ) = ((d l : ℕ) : ℂ) by norm_cast, ← hd1 l]

theorem subset_charValueKernel_of_mem_resConstituents {N Z : Subgroup K} [Finite K] [Fintype N]
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hZ : (Z : Set K) ⊆ charValueKernel θ)
    {lam : N → ℂ} (hlam : lam ∈ resConstituents N θ) :
    ((Z.subgroupOf N : Subgroup N) : Set N) ⊆ charValueKernel lam := fun z hz =>
  mem_charValueKernel.2
    (apply_eq_apply_one_of_mem_resConstituents hθ
      (mem_charValueKernel.1 (hZ (hz : (z : K) ∈ Z))) hlam)

variable {E U C : Subgroup K}

theorem normal_of_eq_inf_centralizer [E.Normal] (hEU : E.IsComplement' U)
    (hC : C = U ⊓ centralizer (E : Set K)) : C.Normal := by
  have hsup : E ⊔ U = ⊤ := hEU.sup_eq_top
  have hcenNormal : (centralizer (E : Set K)).Normal := Subgroup.normal_centralizer
  constructor
  intro c hc g
  have hg : g ∈ (⊤ : Subgroup K) := mem_top g
  rw [← hsup, ← SetLike.mem_coe, Subgroup.normal_mul E U] at hg
  obtain ⟨e, he, u, hu, rfl⟩ := hg
  have he' : e ∈ E := he
  have hu' : u ∈ U := hu
  rw [hC, Subgroup.mem_inf] at hc
  obtain ⟨hcU, hcC⟩ := hc
  have h1 : u * c * u⁻¹ ∈ C := by
    rw [hC, Subgroup.mem_inf]
    exact ⟨U.mul_mem (U.mul_mem hu' hcU) (U.inv_mem hu'), hcenNormal.conj_mem c hcC u⟩
  have h1' := h1
  rw [hC, Subgroup.mem_inf] at h1'
  have hcom : e * (u * c * u⁻¹) = (u * c * u⁻¹) * e :=
    Subgroup.mem_centralizer_iff.1 h1'.2 e he'
  have h2 : e * u * c * (e * u)⁻¹ = e * (u * c * u⁻¹) * e⁻¹ := by group
  rw [h2, hcom]
  simpa using h1

theorem normal_sup [E.Normal] (hEU : E.IsComplement' U)
    (hC : C = U ⊓ centralizer (E : Set K)) : (E ⊔ C).Normal :=
  haveI := normal_of_eq_inf_centralizer hEU hC
  Subgroup.sup_normal E C

theorem commute_of_mem_sup [hE : IsMulCommutative E] (hC : C ≤ centralizer (E : Set K))
    {x : K} (hx : x ∈ E) {y : K} (hy : y ∈ E ⊔ C) : Commute x y := by
  have hy' : y ∈ Subgroup.closure ((E : Set K) ∪ (C : Set K)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    exact hy
  refine Subgroup.closure_induction (p := fun y _ => Commute x y)
    (fun z hz => ?_) (Commute.one_right x)
    (fun a b _ _ ha hb => Commute.mul_right ha hb)
    (fun a _ ha => Commute.inv_right ha) hy'
  rcases hz with hz | hz
  · exact congrArg Subtype.val (hE.is_comm.comm (⟨x, hx⟩ : E) ⟨z, hz⟩)
  · exact Subgroup.mem_centralizer_iff.1 (hC hz) x hx

private theorem commutator_cancel_left {z a b : K} (hza : Commute z a) (hzb : Commute z b) :
    (z * a) * b * (z * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : Commute z (a * b * a⁻¹ * b⁻¹) :=
    ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  calc (z * a) * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * (z⁻¹ * b⁻¹) := by group
    _ = z * (a * b * a⁻¹) * (b⁻¹ * z⁻¹) := by rw [(hzb.inv_left.inv_right).eq]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [h1.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutator_cancel_right {z a b : K} (hza : Commute z a) (hzb : Commute z b) :
    a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : Commute z (a * b * a⁻¹ * b⁻¹) :=
    ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * z * b * a⁻¹ * (b⁻¹ * z⁻¹) := by group
    _ = z * a * b * a⁻¹ * (b⁻¹ * z⁻¹) := by rw [hza.eq]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [h1.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_sup_le_commutator [E.Normal] [IsMulCommutative E]
    (hC : C ≤ centralizer (E : Set K)) : ⁅E ⊔ C, E ⊔ C⁆ ≤ ⁅C, C⁆ := by
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  rw [← SetLike.mem_coe, Subgroup.normal_mul E C] at hg1 hg2
  obtain ⟨e1, he1, c1, hc1, rfl⟩ := hg1
  obtain ⟨e2, he2, c2, hc2, rfl⟩ := hg2
  have he1' : e1 ∈ E := he1
  have hc1' : c1 ∈ C := hc1
  have he2' : e2 ∈ E := he2
  have hc2' : c2 ∈ C := hc2
  have hc1s : c1 ∈ E ⊔ C := (le_sup_right : C ≤ E ⊔ C) hc1'
  have hc2s : c2 ∈ E ⊔ C := (le_sup_right : C ≤ E ⊔ C) hc2'
  have he2s : e2 ∈ E ⊔ C := (le_sup_left : E ≤ E ⊔ C) he2'
  change e1 * c1 * (e2 * c2) * (e1 * c1)⁻¹ * (e2 * c2)⁻¹ ∈ ⁅C, C⁆
  rw [commutator_cancel_left (commute_of_mem_sup hC he1' hc1s)
      (commute_of_mem_sup hC he1' (mul_mem he2s hc2s)),
    commutator_cancel_right (commute_of_mem_sup hC he2' hc1s)
      (commute_of_mem_sup hC he2' hc2s)]
  exact Subgroup.commutator_mem_commutator hc1' hc2'

theorem index_sup_eq_relIndex [Finite K] [E.Normal] (hEU : E.IsComplement' U) (hCU : C ≤ U)
    (hEC : E ⊓ C = ⊥) : (E ⊔ C).index = C.relIndex U := by
  have hcard : Nat.card C * (E ⊔ C).index = Nat.card U := by
    have h1 : E.relIndex (E ⊔ C) * (E ⊔ C).index = E.index :=
      Subgroup.relIndex_mul_index le_sup_left
    have h2 : E.relIndex (E ⊔ C) = Nat.card C := by
      rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hEC,
        Subgroup.relIndex_bot_left]
    rw [← h2, h1, hEU.symm.index_eq_card]
  have hcard2 : Nat.card C * C.relIndex U = Nat.card U := by
    have h1 : (C.subgroupOf U).index * Nat.card (C.subgroupOf U) = Nat.card U :=
      Subgroup.index_mul_card _
    have h2 : Nat.card (C.subgroupOf U) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
    rw [Subgroup.relIndex, mul_comm, ← h2, h1]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcard.trans hcard2.symm)

theorem inertiaGroup_eq_self [Finite K] {E : Subgroup K} [E.Normal] [IsMulCommutative E]
    {D : Subgroup K} [D.Normal] (hED : E ≤ D) {ξ : D → ℂ} (hξ : ξ ∈ Irr D) (hξ1 : ξ 1 = 1)
    (hEker : ¬ ((E.subgroupOf D : Subgroup D) : Set D) ⊆ charValueKernel ξ)
    (hfree : ∀ g : K, g ∉ D → E ⊓ centralizer {g} = ⊥) : inertiaGroup D ξ = D := by
  obtain ⟨ν, hν⟩ := exists_monoidHom_units_of_apply_one_eq_one hξ hξ1
  refine le_antisymm ?_ (le_inertiaGroup D (Irr_subset_classFun hξ))
  intro g hg
  by_contra hgD
  set lam : E → ℂ := fun e => (ν (inclHom hED e) : ℂ) with hlam
  have hlamξ : ∀ e : E, lam e = ξ (inclHom hED e) := fun e => by rw [hlam, ← hν]
  have hlamIrr : lam ∈ Irr E :=
    SolvableNormalLayer.coe_monoidHom_units_mem_Irr (ν.comp (inclHom hED))
  have hconj : conjClassFun E g lam = lam := by
    have hgξ : conjClassFun D g ξ = ξ := mem_inertiaGroup.1 hg
    funext n
    rw [conjClassFun_apply, hlamξ, hlamξ]
    have h1 := congrFun hgξ (inclHom hED n)
    rw [conjClassFun_apply] at h1
    have hpt : inclHom hED (MulAut.conjNormal g⁻¹ n)
        = MulAut.conjNormal g⁻¹ (inclHom hED n) :=
      Subtype.ext (by simp only [inclHom_apply_coe, MulAut.conjNormal_apply])
    rw [hpt, h1]
  have hlam1 : lam = 1 := FreeCore.eq_one_of_conjClassFun_eq g (hfree g hgD) hlamIrr hconj
  refine hEker fun d hd => ?_
  have hdE : (d : K) ∈ E := hd
  have hstep := hlamξ (⟨(d : K), hdE⟩ : E)
  have hd' : inclHom hED (⟨(d : K), hdE⟩ : E) = d := Subtype.ext rfl
  rw [hd'] at hstep
  have hone : lam (⟨(d : K), hdE⟩ : E) = 1 := by rw [hlam1]; rfl
  rw [mem_charValueKernel, hξ1, ← hstep, hone]

theorem inf_centralizer_eq_bot_of_notMem_sup [E.Normal] [IsMulCommutative E]
    (hEU : E.IsComplement' U)
    (hfree : ∀ u ∈ U, u ∉ C → E ⊓ centralizer {u} = ⊥)
    {g : K} (hg : g ∉ E ⊔ C) : E ⊓ centralizer {g} = ⊥ := by
  have hsup : E ⊔ U = ⊤ := hEU.sup_eq_top
  have hmem : g ∈ (⊤ : Subgroup K) := mem_top g
  rw [← hsup, ← SetLike.mem_coe, Subgroup.normal_mul E U] at hmem
  obtain ⟨e, he, u, hu, rfl⟩ := hmem
  have he' : e ∈ E := he
  have hu' : u ∈ U := hu
  have huC : u ∉ C := fun hc =>
    hg (mul_mem ((le_sup_left : E ≤ E ⊔ C) he') ((le_sup_right : C ≤ E ⊔ C) hc))
  have hkey : E ⊓ centralizer {e * u} = E ⊓ centralizer {u} := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    refine and_congr_right fun hx => ?_
    have hxe : e * x = x * e := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨e, he'⟩ : E) ⟨x, hx⟩)
    constructor
    · intro h
      have h2 : e * (u * x) = e * (x * u) := by
        calc e * (u * x) = (e * u) * x := by group
          _ = x * (e * u) := h
          _ = (x * e) * u := by group
          _ = (e * x) * u := by rw [hxe]
          _ = e * (x * u) := by group
      exact mul_left_cancel h2
    · intro h
      calc (e * u) * x = e * (u * x) := by group
        _ = e * (x * u) := by rw [h]
        _ = (e * x) * u := by group
        _ = (x * e) * u := by rw [hxe]
        _ = x * (e * u) := by group
  rw [hkey]
  exact hfree u hu' huC

theorem exists_linear_indClassFun_eq [Fintype K] [E.Normal] [IsMulCommutative E]
    (hEU : E.IsComplement' U) (hC : C = U ⊓ centralizer (E : Set K))
    (hfree : ∀ u ∈ U, u ∉ C → E ⊓ centralizer {u} = ⊥)
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hCker : ((⁅C, C⁆ : Subgroup K) : Set K) ⊆ charValueKernel θ)
    (hEker : ¬ (E : Set K) ⊆ charValueKernel θ) :
    ∃ ξ : (E ⊔ C : Subgroup K) → ℂ, ξ ∈ Irr (E ⊔ C : Subgroup K) ∧ ξ 1 = 1 ∧
      ((⁅C, C⁆.subgroupOf (E ⊔ C) : Subgroup (E ⊔ C : Subgroup K)) :
          Set (E ⊔ C : Subgroup K)) ⊆ charValueKernel ξ ∧
      ¬ ((E.subgroupOf (E ⊔ C) : Subgroup (E ⊔ C : Subgroup K)) :
          Set (E ⊔ C : Subgroup K)) ⊆ charValueKernel ξ ∧
      θ = indClassFun (E ⊔ C : Subgroup K) ξ := by
  classical
  set D : Subgroup K := E ⊔ C
  have : D.Normal := normal_sup hEU hC
  have hED : E ≤ D := le_sup_left
  have hCcen : C ≤ centralizer (E : Set K) := by rw [hC]; exact inf_le_right
  obtain ⟨ξ, hξmem, hξE⟩ :=
    exists_resConstituent_not_subset_charValueKernel (P := D) (Z := E) hED hθ hEker
  have hξ : ξ ∈ Irr D := (mem_resConstituents.1 hξmem).1
  have hξC : ((⁅C, C⁆.subgroupOf D : Subgroup D) : Set D) ⊆ charValueKernel ξ :=
    subset_charValueKernel_of_mem_resConstituents hθ hCker hξmem
  have hξ1 : ξ 1 = 1 := by
    refine Irr.apply_one_eq_one_of_commutator_subset_charValueKernel hξ fun x hx => ?_
    refine hξC ?_
    have hxD : (x : K) ∈ ⁅D, D⁆ := by
      rw [← Subgroup.map_subtype_commutator D]
      exact ⟨x, hx, rfl⟩
    exact (commutator_sup_le_commutator hCcen) hxD
  have hind : indClassFun D ξ ∈ Irr K :=
    (FreeCore.mem_Irr_indClassFun_iff D hξ).2
      (inertiaGroup_eq_self hED hξ hξ1 hξE
        fun g hg => inf_centralizer_eq_bot_of_notMem_sup hEU hfree hg)
  have hpos : 0 < cfInner (resClassFun D θ) ξ := (mem_resConstituents.1 hξmem).2
  have hinner : cfInner (indClassFun D ξ) θ = cfInner (resClassFun D θ) ξ :=
    cfInner_indClassFun_eq_cfInner_resClassFun hθ hξ
  have hne : cfInner (indClassFun D ξ) θ ≠ 0 := by rw [hinner]; exact hpos.ne'
  have hθeq : θ = indClassFun D ξ := by
    by_contra hne'
    rw [cfInner_eq_ite_of_mem_Irr hind hθ, if_neg fun h => hne' h.symm] at hne
    exact hne rfl
  exact ⟨ξ, hξ, hξ1, hξC, hξE, hθeq⟩

theorem apply_one_eq_relIndex [Finite K] [E.Normal] [IsMulCommutative E]
    (hEU : E.IsComplement' U) (hcop : (Nat.card E).Coprime (Nat.card U))
    (hC : C = U ⊓ centralizer (E : Set K))
    (hfree : ∀ u ∈ U, u ∉ C → E ⊓ centralizer {u} = ⊥)
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hCker : ((⁅C, C⁆ : Subgroup K) : Set K) ⊆ charValueKernel θ)
    (hEker : ¬ (E : Set K) ⊆ charValueKernel θ) :
    θ 1 = (C.relIndex U : ℂ) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ξ, -, hξ1, -, -, hθeq⟩ :=
    exists_linear_indClassFun_eq hEU hC hfree hθ hCker hEker
  have hCU : C ≤ U := by rw [hC]; exact inf_le_left
  have hEC : E ⊓ C = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hCU) hcop))
  rw [hθeq, indClassFun_one_eq_index _ hξ1, index_sup_eq_relIndex hEU hCU hEC]

end FixedFreeCoreDegree

end CFSG.FeitThompson
