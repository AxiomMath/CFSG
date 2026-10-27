module

public import CFSG.ClassicalInvolution.Q3.Q3TY5
public import CFSG.ClassicalInvolution.Q3.Q3EPFrame
public import CFSG.ClassicalInvolution.Asc77.AscR10E23
public import CFSG.ClassicalInvolution.RouteD.GapsFrBLast
public import CFSG.ClassicalInvolution.RouteD.GapsFrBRel
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMinus
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFacts
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.RouteD.GapsFrPair
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorLie

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open scoped MatrixGroups commutatorElement

section Fixed

variable {Kc X : Type} [Group Kc] [Group X]

theorem eq_of_fixed_of_pow3 (θ : Kc →* X) (hker : θ.ker ≤ Subgroup.center Kc)
    (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z) (α : Kc ≃* Kc) (σ : X ≃* X)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {R : Subgroup Kc} (hR : Pow3 R)
    (hfix : ∀ r ∈ R, σ (θ r) = θ r) : ∀ r ∈ R, α r = r := by
  have hk : ∀ r ∈ R, r⁻¹ * α r ∈ θ.ker := fun r hr => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, hfix r hr, inv_mul_cancel]
  have hc : ∀ r ∈ R, r⁻¹ * α r ∈ Subgroup.center Kc := fun r hr => hker (hk r hr)
  have hle : ⁅R, R⁆ ≤ MonoidHom.eqLocus (α : Kc →* Kc) (MonoidHom.id Kc) := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    show α ⁅x, y⁆ = ⁅x, y⁆
    rw [map_commutatorElement]
    have e1 : α x = x * (x⁻¹ * α x) := by group
    have e2 : α y = y * (y⁻¹ * α y) := by group
    rw [e1, e2, CFSG.ClassicalInvolution.ModelFacts.commutatorElement_mul_central (hc x hx)
      (hc y hy)]
  intro r hr
  set k := r⁻¹ * α r with hkdef
  have hαr : α r = r * k := by rw [hkdef]; group
  have h3 : α (r ^ 3) = r ^ 3 := hle (hR r hr)
  have hkc : Commute r k := (Subgroup.mem_center_iff.mp (hc r hr)) r
  have hk3 : k ^ 3 = 1 := by
    have : r ^ 3 * k ^ 3 = r ^ 3 := by
      rw [← hkc.mul_pow, ← hαr, ← map_pow, h3]
    exact mul_eq_left.mp this
  have hk1 : k = 1 := by
    by_contra hne
    have h3' : orderOf k = 3 := orderOf_eq_prime hk3 hne
    exact hcop k (hk r hr) (by rw [h3'])
  rw [hαr, hk1, mul_one]

end Fixed

section Minus


theorem centralQuot3_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    CentralQuot3 (spinAction (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2))
      (fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr 3 1)))
      (fundSet (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (scalars (GaloisField 3 1) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1)) := by
  have hm4 : 4 ≤ n := hadm.2.2
  have hY := yData3_minus hm4 hadm
  have hker := ker_spinAction_le_center (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)
  have hF := Exotic.fundCorr_minus3 (p := 3) (f := 1) (by norm_num) hadm
  exact
    { ker_le := hker
      cop := fun z hz h3 => by
        have h2 : z ^ 2 = 1 := by
          rw [pow_two]
          exact ModelFacts.OrthAut.minus_hker2 (minusCoeffs_irr 3 1) z hz
        have := h3.trans (orderOf_dvd_of_pow_eq_one h2)
        omega
      center_le := fun z hz =>
        Exotic.spinAction_center_mem_scalars_minus hm4 (minusCoeffs_irr 3 1) hz
      pow3 := hY.pow3
      inj := fun R hR r hr h1 => hY.central R hR r hr (hker h1)
      map_mem := hF.1
      surj := hF.2 }

section RootSL2

open CFSG.ClassicalInvolution.ModelFacts (map_conj_map map_longSL2_range La_range_eq_map_conj)

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  {Q : QuadraticForm (GaloisField 3 1) V}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3W.CentralQuot3.rootSL2_conj_mem
    {𝓕 : Set (Subgroup (spinGroup Q))}
    {Z' : Subgroup (V ≃ₗ[GaloisField 3 1] V)}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) Z') {m : ℕ} (F₀ : HypFrame Q m) {a b : ℕ}
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) :
    (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom ∈ 𝓕 := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hLa : ∀ A : SL(2, GaloisField 3 1), ((F₀.toFrame hij s t).map hg).La A =
      spinAction Q x * (F₀.toFrame hij s t).La A * (spinAction Q x)⁻¹ := fun A =>
    Frame.map_La _ hg A
  have himg : ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map
      (spinAction Q) = ((F₀.toFrame hij s t).map hg).La.range := by
    rw [La_range_eq_map_conj hLa, map_conj_map]
    congr 1
    exact map_longSL2_range F₀ hij s t
  have hL : ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map
      (spinAction Q) ∈ fundSet Q := by
    rw [himg]
    exact ⟨_, IsFundamental.of_frame ((F₀.toFrame hij s t).map hg)⟩
  obtain ⟨R, hR, hRe⟩ := cq.surj _ hL
  have hRR := eq_of_map_eq_of_pow3 (spinAction Q) cq.ker_le cq.cop (cq.pow3 R hR)
    (rootSL2_map_conj_pow3 F₀ a b ha hb hab s t x) hRe
  rw [← hRR]
  exact hR

end RootSL2

theorem centralQuot3_plus {m : ℕ} (hm : 4 ≤ m) :
    CentralQuot3 (spinAction (quadPlus m (GaloisField 3 1)))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField 3 1) (by omega)))
      (fundSet (quadPlus m (GaloisField 3 1)))
      (scalars (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1)) := by
  have hm3 : 3 ≤ m := by omega
  have hadm : StatedLieAdmissible .POmegaPlus m 3 1 := ⟨Nat.prime_three, le_rfl, hm⟩
  have hY := yData3_plus hm hadm
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  have hpow : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField 3 1) hm3),
      Pow3 R := by
    have := hY.pow3
    rw [e] at this
    exact this
  have hcentral : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField 3 1) hm3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus m (GaloisField 3 1))) → r = 1 := by
    have := hY.central
    rw [e] at this
    exact this
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum m (GaloisField 3 1) hm3) := by
    have := hY.sc
    rw [e] at this
    exact this
  have hker := ker_spinAction_le_center (quadPlus m (GaloisField 3 1))
  exact
    { ker_le := hker
      cop := fun z hz h3 => by
        have h2 : z ^ 2 = 1 := by
          rw [pow_two]
          exact ModelFacts.OrthAut.plus_hker2 m z hz
        have := orderOf_dvd_of_pow_eq_one h2
        have := h3.trans this
        omega
      center_le := fun z hz => spinAction_center_mem_scalars hm3 hz
      pow3 := hpow
      inj := fun R hR r hr h1 => hcentral R hR r hr (hker h1)
      map_mem := fun R hR => map_mem_fundSet hm3 hsc hR
      surj := fun L hL => exists_map_eq hm3 odd_gf3 hL }


theorem exists_spin_pair3_gen {m : ℕ} (hm : 5 ≤ m)
    {R₀ R₁ : Subgroup (spinGroup (quadPlus m (GaloisField 3 1)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField 3 1) (by omega)))
    (hR₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField 3 1) (by omega)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₀ R₁) :
    ∃ x : spinGroup (quadPlus m (GaloisField 3 1)),
      R₀ = ((rootSL2 (plusFrame m (GaloisField 3 1) (by omega)) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 (plusFrame m (GaloisField 3 1) (by omega)) 1 2 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hQ : (quadPlus m (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus m (GaloisField 3 1))
  have cq := centralQuot3_plus (by omega : 4 ≤ m)
  let L : ℕ → Subgroup ((Fin m ⊕ Fin m → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin m ⊕ Fin m → GaloisField 3 1)) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction (quadPlus m (GaloisField 3 1)))
  have hL0 : L 0 = R₀.map (spinAction (quadPlus m (GaloisField 3 1))) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction (quadPlus m (GaloisField 3 1))) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → ((Fin m ⊕ Fin m → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin m ⊕ Fin m → GaloisField 3 1)) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental (quadPlus m (GaloisField 3 1)) (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  have hadjV : ModelAdj (scalars (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1))
      (R₀.map (spinAction (quadPlus m (GaloisField 3 1))))
      (R₁.map (spinAction (quadPlus m (GaloisField 3 1)))) := cq.modelAdj hR₀ hR₁ hadj
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hi₀ hi₁ hadjV
  have hVchain : VChain (quadPlus m (GaloisField 3 1)) 2 L i := by
    refine ⟨hi, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => by omega⟩
    · have : a = 0 := by omega
      subst this
      simpa [i] using cm
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using N
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using C
    · have : a = 0 := by omega
      subst this
      obtain ⟨W, hW⟩ := hlin
      have := hasSingularVector_of_linearPair3 hi₀ hi₁ cm N C
        ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ (plusFrame m (GaloisField 3 1) hm3) (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 (plusFrame m (GaloisField 3 1) hm3) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction (quadPlus m (GaloisField 3 1))) := by
    intro a ha
    have := La_range_eq_of_pairs (plusFrame m (GaloisField 3 1) hm3) (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  refine ⟨x, ?_, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₀)
      (rootSL2_map_conj_pow3 _ 0 1 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₁)
      (rootSL2_map_conj_pow3 _ 1 2 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL1]; exact hnode 1 (by omega))


theorem exists_chain_spin_plus3
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1)))}
    (h₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by norm_num)))
    (h₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by norm_num)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₀ R₁) :
    ∃ T₁ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by norm_num)),
      ∃ T₂ ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by norm_num)),
        Commutes T₁ R₀ ∧ (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ T₁) ∧
        Commutes T₂ R₀ ∧ Commutes T₂ R₁ ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₁ T₂ := by
  classical
  have hm3 : 3 ≤ 5 := by norm_num
  have cq := centralQuot3_plus (m := 5) (by norm_num)
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3_gen (m := 5) (by norm_num) h₀ h₁ hadj hlin
  let ι : spinGroup (quadPlus 5 (GaloisField 3 1)) ≃* spinGroup (quadPlus 5 (GaloisField 3 1)) :=
    MulAut.conj x₀
  have hrk : ∀ (k : ℕ) (hk : k + 1 < 5),
      rankOne (plusDatum 5 (GaloisField 3 1) hm3).rootGroup (⟨k, by omega⟩ : Fin 5) =
        rootSL2 (plusFrame 5 (GaloisField 3 1) hm3) k (k + 1) (by omega) hk (by omega) true
          false := fun k hk => rankOne_plusDatum_of_lt hm3 (k := ⟨k, by omega⟩) hk
  have hR₀ : R₀ = (rankOne (plusDatum 5 (GaloisField 3 1) hm3).rootGroup
      (⟨0, by norm_num⟩ : Fin 5)).map ι.toMonoidHom := by
    rw [hrk 0 (by norm_num)]
    exact hx0
  have hR₁ : R₁ = (rankOne (plusDatum 5 (GaloisField 3 1) hm3).rootGroup
      (⟨1, by norm_num⟩ : Fin 5)).map ι.toMonoidHom := by
    rw [hrk 1 (by norm_num)]
    exact hx1
  have c20 := commutes_rankOne_plusDatum (K := GaloisField 3 1) (hn3 := hm3)
    (i := (⟨2, by norm_num⟩ : Fin 5)) (j := (⟨0, by norm_num⟩ : Fin 5)) (by decide)
  have c30 := commutes_rankOne_plusDatum (K := GaloisField 3 1) (hn3 := hm3)
    (i := (⟨3, by norm_num⟩ : Fin 5)) (j := (⟨0, by norm_num⟩ : Fin 5)) (by decide)
  have c31 := commutes_rankOne_plusDatum (K := GaloisField 3 1) (hn3 := hm3)
    (i := (⟨3, by norm_num⟩ : Fin 5)) (j := (⟨1, by norm_num⟩ : Fin 5)) (by decide)
  have s12 := standardPair_plusDatum_edge (F := GaloisField 3 1) hm3
    (i := (⟨1, by norm_num⟩ : Fin 5)) (j := (⟨2, by norm_num⟩ : Fin 5))
    (Or.inl ⟨rfl, by norm_num⟩)
  have s23 := standardPair_plusDatum_edge (F := GaloisField 3 1) hm3
    (i := (⟨2, by norm_num⟩ : Fin 5)) (j := (⟨3, by norm_num⟩ : Fin 5))
    (Or.inl ⟨rfl, by norm_num⟩)
  refine ⟨(rankOne (plusDatum 5 (GaloisField 3 1) hm3).rootGroup (⟨2, by norm_num⟩ : Fin 5)).map
    ι.toMonoidHom, ?_, (rankOne (plusDatum 5 (GaloisField 3 1) hm3).rootGroup
      (⟨3, by norm_num⟩ : Fin 5)).map ι.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk 2 (by norm_num)]
    exact cq.rootSL2_conj_mem _ _ _ _ true false x₀
  · rw [hrk 3 (by norm_num)]
    exact cq.rootSL2_conj_mem _ _ _ _ true false x₀
  · rw [hR₀]
    exact (commutes_map_equiv ι).mpr c20
  · obtain ⟨W, hW⟩ := s12
    rw [hR₁]
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW⟩
  · rw [hR₀]
    exact (commutes_map_equiv ι).mpr c30
  · rw [hR₁]
    exact (commutes_map_equiv ι).mpr c31
  · obtain ⟨W, hW⟩ := s23
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW⟩


end Minus

end CFSG.ClassicalInvolution.Q3.Q3TY
