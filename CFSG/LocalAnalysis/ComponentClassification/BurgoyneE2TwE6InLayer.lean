module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4Short
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents
public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofRootComponentGen
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6In

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped commutatorElement Pointwise

theorem commutator_le_of_eq_mul {G : Type*} [Group G] {H A N : Subgroup G}
    (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hAH : A ≤ H)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hH : ∀ h ∈ H, ∃ a ∈ A, ∃ n ∈ N, h = a * n) :
    ⁅H, H⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := hH x hx
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := hH y hy
  have hcomm : a₁ * a₂ * a₁⁻¹ = a₂ := by rw [hA a₁ ha₁ a₂ ha₂]; group
  have e : ⁅a₁ * n₁, a₂ * n₂⁆ = (a₁ * (n₁ * (a₂ * (n₂ * n₁⁻¹) * a₂⁻¹)) * a₁⁻¹) *
      ((a₁ * a₂ * a₁⁻¹) * n₂⁻¹ * a₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, hcomm]
  have hn₁H : n₁ ∈ H := by
    have h1 : a₁⁻¹ * (a₁ * n₁) ∈ H := mul_mem (inv_mem (hAH ha₁)) hx
    rwa [inv_mul_cancel_left] at h1
  have hn₂H : n₂ ∈ H := by
    have h1 : a₂⁻¹ * (a₂ * n₂) ∈ H := mul_mem (inv_mem (hAH ha₂)) hy
    rwa [inv_mul_cancel_left] at h1
  refine mul_mem (hN _ (hAH ha₁) _ (mul_mem hn₁ (hN _ (hAH ha₂) _ (mul_mem hn₂ (inv_mem hn₁)))))
    ?_
  have e2 : a₂ * n₂⁻¹ * a₂⁻¹ = (a₂ * n₂⁻¹ * a₂⁻¹) := rfl
  rw [e2]
  exact hN _ (hAH ha₂) _ (inv_mem hn₂)

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

section Generic

variable {τ : Tag}

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
theorem torus_mul_comm
    {h h' : ModGL τ k} (hh : h ∈ torusGroup τ k)
    (hh' : h' ∈ torusGroup τ k) : h * h' = h' * h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a hh'

theorem commutator_fixedGroup_le
    (D : OrthogonalSemilinearFixedRootDatum τ p k) :
    ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroupC := by
  refine commutator_le_of_eq_mul (fun h hh n hn => ?_) D.fixedTorus_le_fixedGroup
    (fun a ha b hb => ?_) (fun h hh => ?_)
  · have hnorm := D.orbitGroupC_normal
    have h1 := hnorm.conj_mem ⟨n, D.orbitGroupC_le_fixedGroup hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.1 h1
  · apply Subtype.ext
    exact torus_mul_comm (unionTorus_le_torusGroup (D.mem_fixedTorus.1 ha).1)
      (unionTorus_le_torusGroup (D.mem_fixedTorus.1 hb).1)
  · have hmul : h ∈ (D.fixedTorus : Set (adjointGroup τ k)) *
        (D.orbitGroupC : Set (adjointGroup τ k)) := by
      rw [← D.coe_fixedGroup_eq_mul]
      exact hh
    obtain ⟨a, ha, n, hn, rfl⟩ := hmul
    exact ⟨a, ha, n, hn, rfl⟩

theorem orbitGroupC_eq_commutator
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hq : IsQuasisimple D.orbitGroup) :
    D.orbitGroupC = ⁅D.fixedGroup, D.fixedGroup⁆ := by
  refine le_antisymm ?_ (commutator_fixedGroup_le D)
  have hperf : ⁅D.orbitGroup, D.orbitGroup⁆ = D.orbitGroup := Subgroup.isPerfect_iff.1 hq.1
  have hC : D.orbitGroupC.map (adjointGroup τ k).subtype = D.orbitGroup := by
    rw [OrthogonalSemilinearFixedRootDatum.orbitGroupC, Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left D.orbitGroup_le_adjointGroup
  have hperfC : ⁅D.orbitGroupC, D.orbitGroupC⁆ = D.orbitGroupC := by
    apply Subgroup.map_injective (adjointGroup τ k).subtype_injective
    rw [Subgroup.map_commutator, hC, hperf]
  rw [← hperfC]
  exact Subgroup.commutator_mono D.orbitGroupC_le_fixedGroup D.orbitGroupC_le_fixedGroup

theorem conj_mem_fixedGroup_withOrbit_of_total
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {J' : Set.range D.classOrbit} {x r : adjointGroup τ k}
    (hx : x ∈ D.totalFixedGroup) (hr : r ∈ (D.withOrbit J').fixedGroup) :
    x * r * x⁻¹ ∈ (D.withOrbit J').fixedGroup := by
  obtain ⟨hxM, hxF⟩ := D.mem_totalFixedGroup.1 hx
  obtain ⟨hrS, hrF⟩ := (D.withOrbit J').mem_fixedGroup.1 hr
  change D.F r = r at hrF
  have hT : torusGroup τ k ≤
      Subgroup.normalizer ((D.withOrbit J').rootSpanJ : Set (ModGL τ k)) :=
    torusGroup_le_normalizer_rootSpan fun α hα => by
      obtain ⟨i, -, hαi⟩ := mem_unionRoots_iff.1 hα
      exact hαi.1.1
  have hM : D.torusKernelSpan ≤
      Subgroup.normalizer ((D.withOrbit J').rootSpanJ : Set (ModGL τ k)) :=
    sup_le hT (D.kernelSpan_le_normalizer J')
  refine (D.withOrbit J').mem_fixedGroup.2 ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (hM hxM) _).1 hrS
  · change D.F (x * r * x⁻¹) = x * r * x⁻¹
    rw [map_mul, map_mul, map_inv, hxF, hrF]

theorem conj_mem_orbitGroup_withOrbit
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {J' : Set.range D.classOrbit} (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {x : adjointGroup τ k} (hx : x ∈ D.totalFixedGroup) {w : ModGL τ k}
    (hw : w ∈ (D.withOrbit J').orbitGroup) :
    (x : ModGL τ k) * w * (x : ModGL τ k)⁻¹ ∈ (D.withOrbit J').orbitGroup := by
  have hwG : w ∈ adjointGroup τ k := (D.withOrbit J').orbitGroup_le_adjointGroup hw
  have hwC : (⟨w, hwG⟩ : adjointGroup τ k) ∈ (D.withOrbit J').orbitGroupC :=
    (D.withOrbit J').mk_mem_orbitGroupC hw
  rw [orbitGroupC_eq_commutator (D.withOrbit J') hq] at hwC
  have hconj : x * ⟨w, hwG⟩ * x⁻¹ ∈ ⁅(D.withOrbit J').fixedGroup, (D.withOrbit J').fixedGroup⁆ := by
    have hmap : ⁅(D.withOrbit J').fixedGroup, (D.withOrbit J').fixedGroup⁆.map
        (MulAut.conj x).toMonoidHom ≤
          ⁅(D.withOrbit J').fixedGroup, (D.withOrbit J').fixedGroup⁆ := by
      rw [Subgroup.map_commutator]
      have hF : (D.withOrbit J').fixedGroup.map (MulAut.conj x).toMonoidHom ≤
          (D.withOrbit J').fixedGroup := by
        rintro _ ⟨r, hr, rfl⟩
        exact conj_mem_fixedGroup_withOrbit_of_total D hx hr
      exact Subgroup.commutator_mono hF hF
    exact hmap ⟨_, hwC, rfl⟩
  rw [← orbitGroupC_eq_commutator (D.withOrbit J') hq] at hconj
  exact Subgroup.mem_subgroupOf.1 hconj

theorem commute_orbitGroup_of_ne
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {J₁ J₂ : Set.range D.classOrbit} (h : J₁ ≠ J₂) {x y : ModGL τ k}
    (hx : x ∈ (D.withOrbit J₁).orbitGroup) (hy : y ∈ (D.withOrbit J₂).orbitGroup) :
    Commute x y :=
  D.commute_of_ne h ((D.withOrbit J₁).orbitGroup_le_rootSpanJ hx)
    ((D.withOrbit J₂).orbitGroup_le_rootSpanJ hy)

theorem orbitMap_of_fixed
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ D.simpleRootsJ) (hθβ : D.θ (toReal β) = toReal β) :
    ({β} : Set (Fin τ.rank → ℤ)) ∈ D.orbits ∧ orbitCard ({β} : Set (Fin τ.rank → ℤ)) = 1 ∧
      ∀ A, D.orbitMap {β} A = rootSL2 τ k β
        (Matrix.SpecialLinearGroup.map (D.orbitField {β}).subtype A) := by
  have hpow : ∀ m : ℕ, (D.θ ^ m) (toReal β) = toReal β := by
    intro m
    induction m with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hθβ, ih]
  have horb : thetaOrbit D.θ β = {β} := by
    ext γ
    simp only [thetaOrbit, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨m, hm⟩
      rw [hpow] at hm
      exact (toReal_injective hm).symm
    · rintro rfl
      exact ⟨0, by rw [pow_zero, Module.End.one_apply]⟩
  have hO : ({β} : Set (Fin τ.rank → ℤ)) ∈ D.orbits := ⟨_, hβ, horb.symm⟩
  have hcard : orbitCard ({β} : Set (Fin τ.rank → ℤ)) = 1 := Set.ncard_singleton _
  have hroot : orbitRoot ({β} : Set (Fin τ.rank → ℤ)) = β := D.orbitRoot_mem hO
  refine ⟨hO, hcard, fun A => ?_⟩
  rw [D.orbitMap_eq_prod, hcard, List.range_one, List.map_singleton, List.prod_singleton,
    D.orbitFactor_apply, D.orbitVec_zero, hroot, mul_zero, iterateFrobenius_zero]
  congr 1

theorem exists_involution_orbitGroup_of_fixed
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ D.simpleRootsJ) (hθβ : D.θ (toReal β) = toReal β) :
    ∃ w ∈ D.orbitGroup, w ≠ 1 ∧ w * w = 1 := by
  obtain ⟨hO, -, hmap⟩ := orbitMap_of_fixed D hβ hθβ
  refine ⟨D.orbitMap _ (-1), D.orbitMap_mem_orbitGroup hO _, ?_, ?_⟩
  · have hneg : Matrix.SpecialLinearGroup.map (D.orbitField {β}).subtype
        (-1 : SL2 (D.orbitField {β})) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hmap, hneg]
    intro h1
    have hk2 : ringChar k ≠ 2 := by
      rw [ringChar.eq k p]
      exact D.odd
    obtain ⟨-, -, -, -, -, -, -, hinj, -⟩ := exceptional_Lang_root_rank_one_data τ k β
    have h2 := (hinj hk2).1 (h1.trans (map_one _).symm)
    have h3 := congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h2
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h3
    exact Ring.neg_one_ne_one_of_char_ne_two hk2 h3
  · rw [← D.orbitMap_mul hO, neg_one_mul, neg_neg]
    exact D.orbitMap_one _

theorem three_le_q
    (D : OrthogonalSemilinearFixedRootDatum τ p k) :
    3 ≤ D.q := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h D.odd
    · have := hp.two_le
      obtain ⟨m, hm⟩ := h
      omega
  calc 3 ≤ p := h3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ D.e := Nat.pow_le_pow_right hp.pos D.one_le_e

end Generic

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {g : G} (hg : g ^ 2 = 1)
    (hodd : Odd (orderOf g)) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hodd
    exact absurd hodd (by decide)

end CFSG.ComponentClassification.Burgoyne.E2.TwE6In
