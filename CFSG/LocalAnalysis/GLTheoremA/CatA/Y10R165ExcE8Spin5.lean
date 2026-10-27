module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups


private theorem mem_e8SpinW1_of_polar_spinW2 {K : Type} [Field K]
    {v : Fin 8 ⊕ Fin 8 → K} (hv : ∀ u ∈ e8SpinW2 K, QuadraticMap.polar (quadPlus 8 K) v u = 0) :
    v ∈ e8SpinW1 K := by
  rw [mem_e8SpinW1]
  intro m hm
  have hmem1 : Pi.single (.inr m) (1 : K) ∈ e8SpinW2 K := by
    rw [mem_e8SpinW2]
    intro m' hm'
    refine ⟨?_, ?_⟩ <;>
      simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, if_neg (by omega : ¬ m' = m),
        if_neg (by simp : ¬ ((.inl m' : Fin 8 ⊕ Fin 8) = .inr m))]
  have hmem2 : Pi.single (.inl m) (1 : K) ∈ e8SpinW2 K := by
    rw [mem_e8SpinW2]
    intro m' hm'
    refine ⟨?_, ?_⟩ <;>
      simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, if_neg (by omega : ¬ m' = m),
        if_neg (by simp : ¬ ((.inr m' : Fin 8 ⊕ Fin 8) = .inl m))]
  constructor
  · have h := hv (Pi.single (.inr m) 1) hmem1
    rwa [polar_quadPlus_single_inr] at h
  · have h := hv (Pi.single (.inl m) 1) hmem2
    rwa [polar_quadPlus_single_inl] at h

private def sixIdx : Fin 3 ⊕ Fin 3 → Fin 8 ⊕ Fin 8
  | .inl i => .inl ⟨(i : ℕ), by omega⟩
  | .inr i => .inr ⟨(i : ℕ), by omega⟩

private theorem sixIdx_injective : Function.Injective sixIdx := by
  rintro (i | i) (j | j) h
  · have h' := Sum.inl.inj h
    simp only [sixIdx, Fin.mk.injEq] at h'
    rw [Fin.ext h']
  · exact absurd h (by simp [sixIdx])
  · exact absurd h (by simp [sixIdx])
  · have h' := Sum.inr.inj h
    simp only [sixIdx, Fin.mk.injEq] at h'
    rw [Fin.ext h']

private theorem sixIdx_linearIndependent (K : Type) [Field K] :
    LinearIndependent K (fun x : Fin 3 ⊕ Fin 3 => (Pi.single (sixIdx x) (1 : K) :
      Fin 8 ⊕ Fin 8 → K)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrFun hg (sixIdx i)
  rw [Finset.sum_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro x _ hxi
    have hne : ¬ (sixIdx i = sixIdx x) := fun h' => hxi (sixIdx_injective h'.symm)
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, hne, if_false, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem single_mem_spinW2_inl {K : Type} [Field K] {a : Fin 8} (ha : (a : ℕ) < 4) :
    (Pi.single (Sum.inl a) (1 : K) : Fin 8 ⊕ Fin 8 → K) ∈ e8SpinW2 K := by
  rw [mem_e8SpinW2]
  intro m hm
  have hne : m ≠ a := by rintro rfl; omega
  exact ⟨Pi.single_eq_of_ne (M := fun _ => K) (i := Sum.inl a) (i' := Sum.inl m)
      (by simp [hne]) 1,
    Pi.single_eq_of_ne (M := fun _ => K) (i := Sum.inl a) (i' := Sum.inr m) (by simp) 1⟩

private theorem single_mem_spinW2_inr {K : Type} [Field K] {a : Fin 8} (ha : (a : ℕ) < 4) :
    (Pi.single (Sum.inr a) (1 : K) : Fin 8 ⊕ Fin 8 → K) ∈ e8SpinW2 K := by
  rw [mem_e8SpinW2]
  intro m hm
  have hne : m ≠ a := by rintro rfl; omega
  exact ⟨Pi.single_eq_of_ne (M := fun _ => K) (i := Sum.inr a) (i' := Sum.inl m) (by simp) 1,
    Pi.single_eq_of_ne (M := fun _ => K) (i := Sum.inr a) (i' := Sum.inr m)
      (by simp [hne]) 1⟩

private theorem six_le_finrank_fixedSpace {K : Type} [Field K] [Finite K] [CharP K 2]
    (x : ↥(⨆ k, e8D8Chain K k)) (hxL : (x : adjointGroup .E8 K) ∈ e8D4Levi K) :
    6 ≤ Module.finrank K ↥(fixedSpace ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K))) := by
  classical
  set T : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) :=
    ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) with hT
  have hmem : ∀ i : Fin 3 ⊕ Fin 3, (Pi.single (sixIdx i) (1 : K) : Fin 8 ⊕ Fin 8 → K) ∈
      fixedSpace T := by
    intro i
    rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace]
    have hW2 : (Pi.single (sixIdx i) (1 : K) : Fin 8 ⊕ Fin 8 → K) ∈ e8SpinW2 K := by
      rcases i with i | i
      · exact single_mem_spinW2_inl (a := ⟨(i : ℕ), by omega⟩) (by simp only [Fin.val_mk]; omega)
      · exact single_mem_spinW2_inr (a := ⟨(i : ℕ), by omega⟩) (by simp only [Fin.val_mk]; omega)
    exact e8D4Levi_fixes_e8SpinW2 K (y := x) hxL hW2
  set S : Submodule K (Fin 8 ⊕ Fin 8 → K) :=
    Submodule.span K (Set.range fun i : Fin 3 ⊕ Fin 3 =>
      (Pi.single (sixIdx i) (1 : K) : Fin 8 ⊕ Fin 8 → K)) with hS
  have hSle : S ≤ fixedSpace T := by
    rintro _ hv
    exact Submodule.span_induction (p := fun x _ => x ∈ fixedSpace T)
      (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        exact hmem i) (Submodule.zero_mem _)
      (fun a b _ _ ha hb => Submodule.add_mem _ ha hb)
      (fun c a _ ha => Submodule.smul_mem _ c ha) hv
  have hSfin : Module.finrank K ↥S = 6 := by
    rw [hS, finrank_span_eq_card (sixIdx_linearIndependent K)]
    simp [Fintype.card_sum]
  have := Submodule.finrank_mono hSle
  omega


variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem theta_fixes_spinW2 (x : ↥(⨆ k, e8D8Chain K k))
    (hxL : (x : adjointGroup .E8 K) ∈ e8D4Levi K) {w : Fin 8 ⊕ Fin 8 → K}
    (hw : w ∈ e8SpinW2 K) :
    ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) w = w :=
  e8D4Levi_fixes_e8SpinW2 K (y := x) hxL hw

private theorem regular_quadPlus_eight {v : Fin 8 ⊕ Fin 8 → K}
    (hv : ∀ w, QuadraticMap.polar (quadPlus 8 K) v w = 0) : v = 0 := by
  funext x
  simp only [Pi.zero_apply]
  rcases x with m | m
  · have h := hv (Pi.single (.inr m) 1)
    rwa [polar_quadPlus_single_inr] at h
  · have h := hv (Pi.single (.inl m) 1)
    rwa [polar_quadPlus_single_inl] at h

private theorem oddOrderIsometry_theta {p : ℕ} (hp : p.Prime) (hpo : p ≠ 2)
    (x : ↥(⨆ k, e8D8Chain K k)) (hord : orderOf (e8D8Theta K x) = p) :
    OddOrderIsometry (quadPlus 8 K) p
      ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
        (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact orthDerived_le_orthogonalGroup
      (e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))).2
  · have h1 : e8D8Theta K x ^ p = 1 := by rw [← hord, pow_orderOf_eq_one]
    have h2 := congrArg (Subgroup.subtype (orthDerived (quadPlus 8 K))) h1
    simpa using h2
  · obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpo
    have h2 : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
    have h1 : (p : K) = 1 := by
      rw [hk, Nat.cast_add, Nat.cast_mul, h2, zero_mul, zero_add, Nat.cast_one]
    rw [h1]
    exact one_ne_zero
  · intro v hv
    exact regular_quadPlus_eight hv

private theorem polar_sum_left {ι : Type*} (Q : QuadraticForm K (Fin 8 ⊕ Fin 8 → K))
    (s : Finset ι) (f : ι → Fin 8 ⊕ Fin 8 → K) (u : Fin 8 ⊕ Fin 8 → K) :
    QuadraticMap.polar Q (∑ i ∈ s, f i) u = ∑ i ∈ s, QuadraticMap.polar Q (f i) u := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.polar_add_left, ih]

private theorem othersSpace_le_spinW1 {p : ℕ} (x : ↥(⨆ k, e8D8Chain K k))
    (hxL : (x : adjointGroup .E8 K) ∈ e8D4Levi K)
    (hodd : OddOrderIsometry (quadPlus 8 K) p
      ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
        (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K))) :
    othersSpace ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
        ((Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K))).toLinearMap (Polynomial.X - 1) ≤
      e8SpinW1 K := by
  classical
  set T : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) :=
    ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) with hT
  have hTmem : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 8 K) := hodd.mem
  have hpne : (p : K) ≠ 0 := hodd.cast_ne_zero
  intro r hr
  refine mem_e8SpinW1_of_polar_spinW2 ?_
  intro u hu
  have hfixu : T u = u := theta_fixes_spinW2 x hxL hu
  have hTpowu : ∀ i : ℕ, (T ^ i) u = u := by
    intro i
    induction i with
    | zero => rw [pow_zero]; rfl
    | succ i ih => rw [pow_succ, LinearEquiv.mul_apply, hfixu]; exact ih
  have hpolar : ∀ r ∈ othersSpace (T.toLinearMap) (Polynomial.X - 1),
      QuadraticMap.polar (quadPlus 8 K) r u = 0 := by
    intro r hr
    refine Submodule.iSup_induction _
      (motive := fun r => QuadraticMap.polar (quadPlus 8 K) r u = 0) hr (fun k r hr => ?_)
      (by simp) (fun a b ha hb => by
        rw [QuadraticMap.polar_add_left, ha, hb, add_zero])
    refine Submodule.iSup_induction _
      (motive := fun r => QuadraticMap.polar (quadPlus 8 K) r u = 0) hr (fun hk r hr => ?_)
      (by simp) (fun a b ha hb => by
        rw [QuadraticMap.polar_add_left, ha, hb, add_zero])
    have hsum : ∑ i ∈ Finset.range p, (T.toLinearMap ^ i) r = 0 :=
      hodd.sum_pow_eq_zero hk.1 hk.2.1 hr
    have h2 : ∀ i ∈ Finset.range p,
        QuadraticMap.polar (quadPlus 8 K) ((T.toLinearMap ^ i) r) u =
          QuadraticMap.polar (quadPlus 8 K) r u := by
      intro i _
      have hmem : (T ^ i) ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 8 K) :=
        Subgroup.pow_mem _ hTmem i
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmem r u
      rw [hTpowu i] at h
      have hbr : (T ^ i) r = (T.toLinearMap ^ i) r := by
        rw [← toLinearMap_pow]
        rfl
      rwa [hbr] at h
    have hkey : (p : K) • QuadraticMap.polar (quadPlus 8 K) r u = 0 := by
      calc (p : K) • QuadraticMap.polar (quadPlus 8 K) r u
          = ∑ i ∈ Finset.range p, QuadraticMap.polar (quadPlus 8 K) r u := by
            rw [Finset.sum_const, Finset.card_range]
            exact Nat.cast_smul_eq_nsmul K p _
        _ = ∑ i ∈ Finset.range p, QuadraticMap.polar (quadPlus 8 K) ((T.toLinearMap ^ i) r) u :=
            Finset.sum_congr rfl fun i hi => (h2 i hi).symm
        _ = QuadraticMap.polar (quadPlus 8 K)
              (∑ i ∈ Finset.range p, (T.toLinearMap ^ i) r) u :=
            (polar_sum_left _ _ _ _).symm
        _ = 0 := by rw [hsum]; simp
    rcases smul_eq_zero.1 hkey with h | h
    · exact absurd h hpne
    · exact h
  exact hpolar r hr


private theorem theta_mem_supportedBlock {p : ℕ} (x : ↥(⨆ k, e8D8Chain K k))
    (hxL : (x : adjointGroup .E8 K) ∈ e8D4Levi K)
    (hodd : OddOrderIsometry (quadPlus 8 K) p
      ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
        (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)))
    (y : ↥(⨆ k, e8D8Chain K k)) (hy : (y : adjointGroup .E8 K) ∈ e8D4Perp K) :
    ((e8D8Theta K y : ↥(orthDerived (quadPlus 8 K))) :
        (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) ∈
      supportedBlock (quadPlus 8 K)
        ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
          (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) (Polynomial.X - 1) := by
  classical
  set T : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) :=
    ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) with hT
  set g : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) :=
    ((e8D8Theta K y : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) with hg
  have hyC : (y : adjointGroup .E8 K) ∈ ⨆ k, e8D8Chain K k :=
    e8D4Group_le_d8 (e8D4Levi_sup_perp_le (Subgroup.mem_sup_right hy))
  have hxC : (x : adjointGroup .E8 K) ∈ ⨆ k, e8D8Chain K k := e8D4Levi_le_e8D8Chain K hxL
  have hcomm : g * T = T * g := by
    have hc : (⟨(y : adjointGroup .E8 K), hyC⟩ : ↥(⨆ k, e8D8Chain K k)) *
        ⟨(x : adjointGroup .E8 K), hxC⟩ =
        ⟨(x : adjointGroup .E8 K), hxC⟩ * ⟨(y : adjointGroup .E8 K), hyC⟩ :=
      Subtype.ext (by
        show (y : adjointGroup .E8 K) * (x : adjointGroup .E8 K) =
          (x : adjointGroup .E8 K) * (y : adjointGroup .E8 K)
        exact (e8D4Levi_commute_perp (K := K) x hxL y hy).symm)
    have h1 : e8D8Theta K ⟨(y : adjointGroup .E8 K), hyC⟩ *
        e8D8Theta K ⟨(x : adjointGroup .E8 K), hxC⟩ =
        e8D8Theta K ⟨(x : adjointGroup .E8 K), hxC⟩ *
          e8D8Theta K ⟨(y : adjointGroup .E8 K), hyC⟩ := by
      rw [← map_mul, ← map_mul, hc]
    have h2 := congrArg (fun z : ↥(orthDerived (quadPlus 8 K)) =>
      (z : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K))) h1
    simpa [hg, hT, LinearEquiv.mul_apply] using h2
  rw [mem_supportedBlock]
  refine ⟨?_, ?_⟩
  · rw [mem_isometryCentralizer]
    refine ⟨fun v => ?_, fun v => congrFun (congrArg DFunLike.coe hcomm) v⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (e8D8Theta K y : ↥(orthDerived (quadPlus 8 K))).2) v
  · intro v hv
    exact e8D4Perp_fixes_e8SpinW1 K hy (othersSpace_le_spinW1 x hxL hodd hv)

private theorem theta_mem_supportedFixedDerived {p : ℕ} (x : ↥(⨆ k, e8D8Chain K k))
    (hxL : (x : adjointGroup .E8 K) ∈ e8D4Levi K)
    (hodd : OddOrderIsometry (quadPlus 8 K) p
      ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
        (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)))
    (y : ↥(⨆ k, e8D8Chain K k)) (hy : (y : adjointGroup .E8 K) ∈ e8D4Perp K) :
    ((e8D8Theta K y : ↥(orthDerived (quadPlus 8 K))) :
        (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) ∈
      supportedFixedDerived (quadPlus 8 K)
        ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
          (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) := by
  classical
  set T : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) :=
    ((e8D8Theta K x : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) with hT
  set φ : ↥(e8D4Perp K) →* ((Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) :=
    (Subgroup.subtype (orthDerived (quadPlus 8 K))).comp
      ((e8D8Theta K).toMonoidHom.comp (Subgroup.inclusion
        ((le_trans le_sup_right e8D4Levi_sup_perp_le).trans e8D4Group_le_d8))) with hφ
  have hφapply : ∀ z : ↥(e8D4Perp K), φ z = ((e8D8Theta K ⟨(z : adjointGroup .E8 K),
      e8D4Group_le_d8 ((le_trans le_sup_right e8D4Levi_sup_perp_le) (z.2))⟩ :
      ↥(orthDerived (quadPlus 8 K))) : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) :=
    fun z => rfl
  have hblock : φ.range ≤ supportedBlock (quadPlus 8 K) T (Polynomial.X - 1) := by
    rintro _ ⟨z, rfl⟩
    exact theta_mem_supportedBlock x hxL hodd _ z.2
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    have hcomm : ⁅(⊤ : Subgroup ↥(e8D4Perp K)), ⊤⁆ = ⊤ :=
      (isQuasisimple_e8D4Perp K).1.commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hcomm, Subgroup.map_top]
  have hle : φ.range ≤ supportedFixedDerived (quadPlus 8 K) T := by
    rw [hodd.supportedFixedDerived_eq]
    calc φ.range = ⁅φ.range, φ.range⁆ := hperf.symm
      _ ≤ ⁅supportedBlock (quadPlus 8 K) T (Polynomial.X - 1),
            supportedBlock (quadPlus 8 K) T (Polynomial.X - 1)⁆ :=
          Subgroup.commutator_mono hblock hblock
  refine hle ⟨⟨(y : adjointGroup .E8 K), hy⟩, ?_⟩
  rw [hφapply]



theorem exists_layer_normal_centralizer {p : ℕ} (hp : p.Prime) (hpo : p ≠ 2)
    {x : adjointGroup .E8 K} (hxL : x ∈ e8D4Levi K)
    (hxC : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) ≤ ⨆ k, e8D8Chain K k)
    (hord : orderOf (e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩) = p)
    (hpq : p ∣ Nat.card K ^ 2 + 1) :
    ∃ J : Subgroup (adjointGroup .E8 K),
      e8D4Perp K ≤ J ∧
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) ∧
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥J ∧ p ∣ Nat.card ↥J := by
  classical
  set T : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) :=
    ((e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) with hT
  have hord' : orderOf (e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩) = p := hord
  have hodd : OddOrderIsometry (quadPlus 8 K) p T := by
    rw [hT]
    exact oddOrderIsometry_theta hp hpo ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ hord'
  set ψ : ↥(⨆ k, e8D8Chain K k) →* ((Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) :=
    (Subgroup.subtype (orthDerived (quadPlus 8 K))).comp (e8D8Theta K).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact (e8D8Theta K).injective (Subtype.ext hab)
  set P : Subgroup ((Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) :=
    supportedFixedDerived (quadPlus 8 K) T with hP
  have hPle : P ≤ ψ.range := by
    intro g hg
    refine ⟨(e8D8Theta K).symm ⟨g, ?_⟩, ?_⟩
    · exact hodd.supportedFixedDerived_le_orthDerived hg
    · show ((e8D8Theta K ((e8D8Theta K).symm ⟨g, _⟩) : ↥(orthDerived _)) : _) = g
      rw [MulEquiv.apply_symm_apply]
  have hPiso : P ≤ isometryCentralizer (quadPlus 8 K) T :=
    supportedFixedDerived_le_isometryCentralizer
  have hPq : CFSG.IsQuasisimple ↥P :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.isQuasisimple_supportedFixedDerived_of_six_le
      hodd (CharP.cast_eq_zero K 2)
      (by simpa [hT] using six_le_finrank_fixedSpace ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ hxL)
  set J : Subgroup (adjointGroup .E8 K) := (P.comap ψ).map (⨆ k, e8D8Chain K k).subtype with hJ
  have hQJ : e8D4Perp K ≤ J := by
    intro z hz
    have hzC : z ∈ ⨆ k, e8D8Chain K k :=
      e8D4Group_le_d8 ((le_trans le_sup_right e8D4Levi_sup_perp_le) hz)
    refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    show ((e8D8Theta K ⟨z, hzC⟩ : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) ∈ P
    exact theta_mem_supportedFixedDerived ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ hxL hodd ⟨z, hzC⟩ hz
  have hJle : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_comap] at hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hcomm : ((e8D8Theta K u : ↥(orthDerived (quadPlus 8 K))) : _) * T =
        T * ((e8D8Theta K u : ↥(orthDerived (quadPlus 8 K))) : _) := by
      apply LinearEquiv.ext
      intro v
      exact (mem_isometryCentralizer.mp (hPiso hu)).2 v
    have h2 : e8D8Theta K u * e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ =
        e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ * e8D8Theta K u :=
      Subtype.ext (by simpa [hT, Subgroup.coe_mul] using hcomm)
    have h3 : u * ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ = ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ * u := by
      apply (e8D8Theta K).injective
      rw [map_mul, map_mul]
      exact h2
    exact (congrArg (fun w : ↥(⨆ k, e8D8Chain K k) => (w : adjointGroup .E8 K)) h3).symm
  refine ⟨J, hQJ, hJle, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hJle]
    intro h k hh hk
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
    rw [Subgroup.mem_comap] at hu
    have hkC : k ∈ ⨆ k, e8D8Chain K k := hxC hk
    refine Subgroup.mem_map.mpr ⟨⟨k, hkC⟩ * u * ⟨k, hkC⟩⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have himage : ψ (⟨k, hkC⟩ * u * ⟨k, hkC⟩⁻¹) =
        ((e8D8Theta K ⟨k, hkC⟩ : ↥(orthDerived (quadPlus 8 K))) : _) * ψ u *
          ((e8D8Theta K ⟨k, hkC⟩ : ↥(orthDerived (quadPlus 8 K))) : _)⁻¹ := by
      simp only [hψ, MonoidHom.comp_apply, map_mul, map_inv]
      rfl
    rw [himage]
    refine hodd.conj_mem_supportedFixedDerived ?_ hu
    rw [mem_isometryCentralizer]
    refine ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup
        (e8D8Theta K ⟨k, hkC⟩ : ↥(orthDerived (quadPlus 8 K))).2) v, fun v => ?_⟩
    have hcomm : ((e8D8Theta K ⟨k, hkC⟩ : ↥(orthDerived (quadPlus 8 K))) : _) * T =
        T * ((e8D8Theta K ⟨k, hkC⟩ : ↥(orthDerived (quadPlus 8 K))) : _) := by
      have hkx : (⟨k, hkC⟩ : ↥(⨆ k, e8D8Chain K k)) * ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ =
          ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ * ⟨k, hkC⟩ :=
        Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact (Subgroup.mem_centralizer_iff.mp hk x (Set.mem_singleton x)).symm)
      have h2 : e8D8Theta K ⟨k, hkC⟩ * e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ =
          e8D8Theta K ⟨x, e8D4Levi_le_e8D8Chain K hxL⟩ * e8D8Theta K ⟨k, hkC⟩ := by
        rw [← map_mul, ← map_mul, hkx]
      simpa [hT, Subgroup.coe_mul] using
        congrArg (fun z : ↥(orthDerived (quadPlus 8 K)) =>
          (z : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K))) h2
    exact congrFun (congrArg (fun e : (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K) =>
      (e : (Fin 8 ⊕ Fin 8 → K) → (Fin 8 ⊕ Fin 8 → K))) hcomm) v
  · exact ExcEngine.isQuasisimple_map_comap_of_layer ψ hψinj hPle
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hPq)
  · have hdvd : Nat.card ↥(e8D4Perp K) ∣ Nat.card ↥J := Subgroup.card_dvd_of_le hQJ
    exact (dvd_card_e8D4Perp K hp hpq).trans hdvd


end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
