module

public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.ModelFacts.TG3D4Tri
public import CFSG.ClassicalInvolution.RouteD.TWS7Ord

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.ModelFacts.TG3
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups commutatorElement


section Swap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem swap_of_twin_pair_ord3 [Finite F] (hodd : Odd (Nat.card F))
    (hcop : ∀ z ∈ (spinAction Q).ker, ¬ 3 ∣ orderOf z)
    {R R' : Subgroup (spinGroup Q)} (hRp : Pow3 R) (hR'p : Pow3 R')
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') :
    ∃ F₁ : Frame Q, R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
        spinAction Q x' = F₁.swap.La (-1) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set θ := spinAction Q with hθ
  obtain ⟨i₁, F₁, hF₁, -⟩ := hR
  obtain ⟨i₂, F₂, hF₂, -⟩ := hR'
  have hθx : θ x = F₁.La (-1) := by
    have hmem : θ x ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ hx
    have hsq : θ x * θ x = 1 := by rw [← map_mul, hx2, map_one]
    have hne1 : θ x ≠ 1 := fun h => hx1 (hinj x hx h)
    have hord2 : orderOf (θ x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁).eq_of_orderOf_eq_two hodd hmem hord2
  have hθx' : θ x' = F₂.La (-1) := by
    have hmem : θ x' ∈ F₂.La.range := hF₂ ▸ Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord2 : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₂).eq_of_orderOf_eq_two hodd hmem hord2
  have hFeq : F₂.La (-1) = F₁.La (-1) := by rw [← hθx, ← hθx', hord]
  rcases Frame.La_range_eq_or_eq_swap h2 hFeq with h | h
  · exfalso
    apply hne
    apply eq_of_map_eq_of_pow3 θ (ker_spinAction_le_center Q) hcop hRp hR'p
    rw [hF₁, hF₂, h]
  · refine ⟨F₁, hF₁, hF₂.trans h, hθx, ?_⟩
    have hmem : θ x' ∈ F₁.swap.La.range := by
      rw [← h, ← hF₂]
      exact Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord2 : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁.swap).eq_of_orderOf_eq_two hodd hmem hord2

end Swap

section Plus4

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

theorem exists_central_involution3 {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num))) :
    ∃ x ∈ R, x ≠ 1 ∧ (∀ r ∈ R, x * r = r * x) ∧
      ∃ i : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃),
        IsFundamental (quadPlus 4 𝔽₃) (R.map (spinAction (quadPlus 4 𝔽₃))) i ∧
          spinAction (quadPlus 4 𝔽₃) x = i := by
  have cq := centralQuot3_plus (m := 4) le_rfl
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  obtain ⟨x, hx, hxi⟩ := hi.mem
  refine ⟨x, hx, ?_, ?_, i, hi, hxi⟩
  · intro h
    rw [h, map_one] at hxi
    exact hi.ne_one odd_gf3 hxi.symm
  · intro r hr
    have hcomm : i * spinAction (quadPlus 4 𝔽₃) r = spinAction (quadPlus 4 𝔽₃) r * i :=
      Subgroup.mem_centralizer_singleton_iff.mp (hi.le_centralizer ⟨r, hr, rfl⟩) |>.symm
    have h1 : x * r * (r * x)⁻¹ = 1 := by
      refine cq.inj R hR _ (R.mul_mem (R.mul_mem hx hr) (R.inv_mem (R.mul_mem hr hx))) ?_
      rw [map_mul, map_mul, map_inv, map_mul, hxi, hcomm, mul_inv_cancel]
    exact mul_inv_eq_one.mp h1

theorem preservesFund_symm3 {σ : spinGroup (quadPlus 4 𝔽₃) ≃* spinGroup (quadPlus 4 𝔽₃)}
    (hσ : PreservesFund 3 1 σ) : PreservesFund 3 1 σ.symm := by
  classical
  have : Finite 𝔽₃ := Nat.finite_of_card_ne_zero (by rw [card_gf3]; norm_num)
  have : NeZero 4 := inferInstance
  have : Finite (spinGroup (quadPlus 4 𝔽₃)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  set 𝒮 : Set (Subgroup (spinGroup (quadPlus 4 𝔽₃))) :=
    {R | R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num))} with h𝒮
  have hmaps : Set.MapsTo (fun R => R.map σ.toMonoidHom) 𝒮 𝒮 := fun R hR => hσ R hR
  have hinj : Set.InjOn (fun R => R.map σ.toMonoidHom) 𝒮 := fun R _ R' _ h =>
    Subgroup.map_injective σ.injective h
  have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite 𝒮) hmaps).mp hinj
  intro R hR
  obtain ⟨S, hS, hSR⟩ := hbij.surjOn hR
  have hSR' : S.map σ.toMonoidHom = R := hSR
  have : R.map σ.symm.toMonoidHom = S := by
    rw [← hSR']
    exact RouteD.TWS6.map_map_symm_equiv σ S
  rw [this]
  exact hS

theorem exists_ordinary_datum3 {R R' : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    {x x' : spinGroup (quadPlus 4 𝔽₃)}
    (hd : TwinDatumOn .POmegaPlus ⟨spinGroup (quadPlus 4 𝔽₃), plusDatum 4 𝔽₃ (by norm_num)⟩
      R R' x x')
    (hx2 : x * x = 1) (hx'2 : x' * x' = 1) :
    ∃ σ : spinGroup (quadPlus 4 𝔽₃) ≃* spinGroup (quadPlus 4 𝔽₃),
      PreservesFund 3 1 σ ∧ PreservesFund 3 1 σ.symm ∧
        spinAction (quadPlus 4 𝔽₃) (σ x) = spinAction (quadPlus 4 𝔽₃) (σ x') := by
  classical
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hc2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
    have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
    have hcomm : x * x' = x' * x := hd.comm x hd.hx x' hd.hx'
    rw [hx'inv]
    calc x * x' * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hcomm]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hx2, hx'2, one_mul]
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary3 hadm hd.same hc2
  refine ⟨σ, hσ, preservesFund_symm3 hσ, ?_⟩
  rw [map_mul, map_inv, map_mul, map_inv] at hθ
  exact mul_inv_eq_one.mp hθ

theorem exists_ordinary_pair3 {A B : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hA : A ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hB : B ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num)))
    (hne : A ≠ B) (hc : Commutes A B) :
    ∃ (σ : spinGroup (quadPlus 4 𝔽₃) ≃* spinGroup (quadPlus 4 𝔽₃)) (fr : OFrame (quadPlus 4 𝔽₃)),
      PreservesFund 3 1 σ ∧ PreservesFund 3 1 σ.symm ∧
      (A.map σ.toMonoidHom).map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range ∧
      (B.map σ.toMonoidHom).map (spinAction (quadPlus 4 𝔽₃)) = fr.swap.La.range := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have cq := centralQuot3_plus (m := 4) le_rfl
  have hV : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by rw [finrank_plus]
  have : Group.IsPerfect (spinGroup (quadPlus 4 𝔽₃)) := isPerfect_spinGroup_quadPlus hn3
  obtain ⟨x, hxA, hx1, hcx, i, hi, hθx⟩ := exists_central_involution3 hA
  obtain ⟨x', hxB, hx'1, hcx', j, hj, hθx'⟩ := exists_central_involution3 hB
  have hk : Commutes (A.map (spinAction (quadPlus 4 𝔽₃))) (B.map (spinAction (quadPlus 4 𝔽₃))) :=
    commutes_map_of_commutes _ hc
  have hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) := by
    obtain ⟨μ, hμ⟩ := Asc77.T8ZZ.fund_prod_scalar odd_gf3 hV hi hj hk
    have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj.mul_self
    refine mem_center_of_commutators_central fun s => ker_spinAction_le_center _ ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    have hscal : spinAction (quadPlus 4 𝔽₃) (x * x'⁻¹) ∈ scalars 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) :=
      mem_scalars.mpr ⟨μ, fun v => by rw [map_mul, map_inv, hθx, hθx', hjinv]; exact hμ v⟩
    exact commute_of_mem_scalars hscal _
  have hd : TwinDatumOn .POmegaPlus ⟨spinGroup (quadPlus 4 𝔽₃), plusDatum 4 𝔽₃ (by norm_num)⟩
      A B x x' :=
    { mem := hA, mem' := hB, ne := hne, comm := hc, hx := hxA, hx' := hxB, cx := hcx,
      cx' := hcx', nx := hx1, nx' := hx'1, same := hsame }
  have hx2 : x * x = 1 := sq_eq_one_of_central_fund (cq.map_mem A hA) (cq.inj A hA) hxA hcx
  have hx'2 : x' * x' = 1 := sq_eq_one_of_central_fund (cq.map_mem B hB) (cq.inj B hB) hxB hcx'
  obtain ⟨σ, hσ, hσ', hord⟩ := exists_ordinary_datum3 hd hx2 hx'2
  have hd₁ := RouteD.TWS6.map_datum_equiv hd σ hσ
  have hAσ : A.map σ.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 𝔽₃ (by norm_num)) := hσ A hA
  have hBσ : B.map σ.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 𝔽₃ (by norm_num)) := hσ B hB
  obtain ⟨F₁, h1, h2, -, -⟩ := swap_of_twin_pair_ord3 odd_gf3 cq.cop (cq.pow3 _ hAσ)
    (cq.pow3 _ hBσ) (cq.map_mem _ hAσ) (cq.map_mem _ hBσ) (cq.inj _ hAσ) (cq.inj _ hBσ) hd₁.ne
    hd₁.hx (sq_eq_one_of_central_fund (cq.map_mem _ hAσ) (cq.inj _ hAσ) hd₁.hx hd₁.cx) hd₁.nx
    hd₁.hx' (sq_eq_one_of_central_fund (cq.map_mem _ hBσ) (cq.inj _ hBσ) hd₁.hx' hd₁.cx')
    hd₁.nx' hord
  exact ⟨σ, F₁, hσ, hσ', h1, h2⟩

end Plus4

end CFSG.ClassicalInvolution.Q3.Q3TD
