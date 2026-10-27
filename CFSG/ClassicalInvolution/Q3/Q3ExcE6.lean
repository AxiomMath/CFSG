module

public import CFSG.ClassicalInvolution.Q3.Q3ExcAdj
public import CFSG.ClassicalInvolution.Q3.Q3ExcLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exc3_closure_pow_three_of_equiv {G : Type*} [Group G] {L : Subgroup G}
    (e : SL(2, ZMod 3) ≃* L) : Subgroup.closure {y : L | y ^ 3 = 1} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, b, c, ha, hb, hc, hy⟩ := sl2Three_exists_cubes (e.symm y)
  have hy' : y = e a * e b * e c := by
    rw [← map_mul, ← map_mul, ← hy]
    simp
  have hmem : ∀ s : SL(2, ZMod 3), s ^ 3 = 1 → e s ∈ Subgroup.closure {y : L | y ^ 3 = 1} :=
    fun s hs => Subgroup.subset_closure (by rw [Set.mem_ofPred_eq, ← map_pow, hs, map_one])
  rw [hy']
  exact mul_mem (mul_mem (hmem a ha) (hmem b hb)) (hmem c hc)

theorem exc3_minGroup_rootGroup_pow_three {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type)
    [Field k] [Finite k] (hk : Nat.card k = 3) (γ : Fin τ.rank → ℤ) :
    ∀ a ∈ hV.rootGroup k γ, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 ha
  have h3 : c + c + c = 0 := by
    have h := CFSG.LieType.HighestRoot.three_eq_zero hk
    linear_combination c * h
  have e : hV.xm k γ c ^ 3 = hV.xm k γ (c + c + c) := by
    rw [hV.xm_add, hV.xm_add, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  rw [e, h3, hV.xm_zero]

theorem exc3_e6_mem_fundamentalSubgroups (hadm : StatedLieAdmissible .E6 0 3 1)
    [Finite ↥(e6Data_valid.minGroup (GaloisField 3 1))]
    (hZ2 : IsPGroup 2 (Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 3 1))))
    {L : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1))}
    {z : ↥(e6Data_valid.minGroup (GaloisField 3 1))} (hL : IsClassicalMember3 L z)
    (hO : classicalInvolutionOddCore L = ⊥) :
    L ∈ Generic.fundamentalSubgroups .E6 (e6Datum (GaloisField 3 1)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 := exc3_natCard_galoisField_three
  have hqs := isQuasisimple_e6 (GaloisField 3 1)
  have hθ := e6Isogeny_surjective (GaloisField 3 1)
  have hker : (e6Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one (GaloisField 3 1))
  have h2 : IsPGroup 2 (e6Isogeny (GaloisField 3 1)).ker := hZ2.to_le hker
  have hz : e6Isogeny (GaloisField 3 1) z ≠ 1 := fun h1 =>
    exc3_false_of_central_involution (open_isQuasisimple hqs) hL hO
      (hker (MonoidHom.mem_ker.2 h1))
  obtain ⟨hL', hO'⟩ := exc3_isClassicalMember3_map _ hθ hker hL hO hz
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exc3_exists_conj_rootGroup_of_member
    (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) uniqIsolated_E6 hL' hO'
  have hlong := isLongestRoot_single .E6 0 3 1 Nat.prime_three trivial hadm
  have hlongγ : IsLongestRoot (e6Datum (GaloisField 3 1)) γ :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 (GaloisField 3 1)).2 hγ.1)
  obtain ⟨g', hg'⟩ := hθ g⁻¹
  set A := (e6Datum (GaloisField 3 1)).rootGroup γ with hA
  set B := (e6Datum (GaloisField 3 1)).rootGroup (-γ) with hB
  have hAmap : A.map (e6Isogeny (GaloisField 3 1)) =
      rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) γ :=
    map_e6Isogeny_rootGroup _ hγ.1
  have hBmap : B.map (e6Isogeny (GaloisField 3 1)) =
      rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-γ) :=
    map_e6Isogeny_rootGroup _ (IsRoot.neg hγ.1)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := exc3_minGroup_rootGroup_pow_three e6Data_valid _ hK3 γ
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := exc3_minGroup_rootGroup_pow_three e6Data_valid _ hK3 (-γ)
  have hconj3 : ∀ C : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1)),
      (∀ x ∈ C, x ^ 3 = 1) → ∀ x ∈ C.map (MulAut.conj g').toMonoidHom, x ^ 3 = 1 := by
    rintro C hC _ ⟨x, hx, rfl⟩
    show (g' * x * g'⁻¹) ^ 3 = 1
    rw [conj_pow, hC x hx]
    group
  have hRgen := exc3_closure_pow_three_eq_top (hconj3 A hA3) (hconj3 B hB3)
  set R' := A.map (MulAut.conj g').toMonoidHom ⊔ B.map (MulAut.conj g').toMonoidHom with hR'
  have hRθ : (A ⊔ B).map (e6Isogeny (GaloisField 3 1)) =
      rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) γ ⊔
        rootGroup (rootOperatorFamily .E6) (GaloisField 3 1) (-γ) := by
    rw [Subgroup.map_sup, hAmap, hBmap]
  have hconjmap : ∀ H : Subgroup ↥(e6Data_valid.minGroup (GaloisField 3 1)),
      (H.map (MulAut.conj g').toMonoidHom).map (e6Isogeny (GaloisField 3 1)) =
        (H.map (e6Isogeny (GaloisField 3 1))).map (MulAut.conj g⁻¹).toMonoidHom := by
    intro H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv, hg']
  have hRsup : R' = (A ⊔ B).map (MulAut.conj g').toMonoidHom := (Subgroup.map_sup A B _).symm
  have hLmap : L.map (e6Isogeny (GaloisField 3 1)) = R'.map (e6Isogeny (GaloisField 3 1)) := by
    rw [hRsup, hconjmap, hRθ]
    exact hLeq
  obtain ⟨e⟩ := hL.nonempty_equiv_sl2 hO
  have hLR : L = R' :=
    exc3_eq_of_map_eq hker h2 (exc3_closure_pow_three_of_equiv e.symm) hRgen hLmap
  exact ⟨g', γ, Or.inl hlongγ, by rw [hLR, hRsup]; rfl⟩

theorem classicalMembersFundamental3Tag_E6 : ClassicalMembersFundamental3Tag .E6 := by
  intro n hp hFT hadm L z hL hO
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, hZ2⟩ := modelFiniteCenterTwoGroup3 .E6 0 hp hFT hadm
  have : Finite ↥(e6Data_valid.minGroup (GaloisField 3 1)) := hfin
  exact exc3_e6_mem_fundamentalSubgroups hadm hZ2 hL hO

theorem simpleOddCentralizerFreeTag_E6 : SimpleOddCentralizerFreeTag .E6 := by
  intro n hp hadm s hs
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, -⟩ := modelFiniteCenterTwoGroup3 .E6 0 hp trivial hadm
  have : Finite ↥(e6Data_valid.minGroup (GaloisField 3 1)) := hfin
  have : Finite ↥(adjointGroup .E6 (GaloisField 3 1)) := inferInstance
  have hqs := isQuasisimple_e6 (GaloisField 3 1)
  have hθ := e6Isogeny_surjective (GaloisField 3 1)
  have hker : (e6Isogeny (GaloisField 3 1)).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one (GaloisField 3 1))
  exact exc3_simpleOddCentralizer_of_cover (e6Isogeny (GaloisField 3 1)) hθ
    (exc3_ker_eq_center _ hθ hker center_adjointGroup_eq_bot)
    (fun c hc => exc3_oddCore_centralizer_eq_bot (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) hc)
    s hs

theorem oddCentralizerFreeTag_E6 : OddCentralizerFreeTag .E6 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_E6

end CFSG.ClassicalInvolution.Q3
