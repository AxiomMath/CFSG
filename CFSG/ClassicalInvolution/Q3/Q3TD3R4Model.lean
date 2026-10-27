module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Lift
public import CFSG.ClassicalInvolution.RouteD.TWS7Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TY CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.TWS7
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.RouteD.Gaps (linearBlockStandardPair_map_equiv)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (plus_center_facts)
open scoped MatrixGroups commutatorElement


local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

theorem modelLeafD3_proved :
    ∀ {X : Type} [Group X] (ψ : spinGroup (quadPlus 4 (GaloisField 3 1)) →* X),
      ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) →
      ∀ (τ : X ≃* X), (∀ y, τ (τ y) = y) → (∀ k, τ (ψ k) ∈ ψ.range) →
      ∀ A B C : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1))),
        A ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)) →
        B ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)) →
        C ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)) →
        A ≠ B → Commutes A B → Commutes A C → Commutes B C →
        (∀ r ∈ A, τ (ψ r) = ψ r) → (∀ r ∈ B, τ (ψ r) = ψ r) →
        ∀ x ∈ C, ψ x ≠ 1 → x ^ 3 = 1 → τ (ψ x) = (ψ x)⁻¹ →
          ∃ R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1))),
            (∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
              (plusDatum 4 (GaloisField 3 1) (by norm_num))) ∧
            (∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R a) (R b)) ∧
            (∀ a b, edgeD 4 a b → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R b)) ∧
            (∀ a : Fin 4, 1 ≤ a.val → ∀ g ∈ R a, τ (ψ g) = ψ g) ∧
            (∀ g ∈ R ⟨0, by omega⟩, τ (ψ g) ∈ (R ⟨0, by omega⟩).map ψ) ∧
            (∃ g ∈ R ⟨0, by omega⟩, τ (ψ g) ≠ ψ g) := by
  classical
  intro X _ ψ hψ τ hτ2 hτr A B C hA hB hC hAB hcAB hcAC hcBC hfixA hfixB x hxC hψx hxp hτx
  have hm3 : 3 ≤ 4 := by norm_num
  have cq := centralQuot3_plus (m := 4) le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨σ, fr, hσ, hσ', hA', hB'⟩ := exists_ordinary_pair3 hA hB hAB hcAB
  let ψ' : spinGroup (quadPlus 4 (GaloisField 3 1)) →* X := ψ.comp σ.symm.toMonoidHom
  have hψ'σ : ∀ y, ψ' (σ y) = ψ y := fun y => by simp [ψ']
  have hker' : ψ'.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) := by
    intro y hy
    have h1 : σ.symm y ∈ ψ.ker := hy
    have := RouteD.TWS6.map_mem_center σ (hψ h1)
    simpa using this
  have hτr' : ∀ k, τ (ψ' k) ∈ ψ'.range := by
    intro k
    obtain ⟨m, hm⟩ := hτr (σ.symm k)
    exact ⟨σ m, by rw [hψ'σ, hm]; rfl⟩
  have hfixA' : ∀ r ∈ A.map σ.toMonoidHom, τ (ψ' r) = ψ' r := by
    rintro _ ⟨a, ha, rfl⟩
    show τ (ψ' (σ a)) = ψ' (σ a)
    rw [hψ'σ]
    exact hfixA a ha
  have hfixB' : ∀ r ∈ B.map σ.toMonoidHom, τ (ψ' r) = ψ' r := by
    rintro _ ⟨a, ha, rfl⟩
    show τ (ψ' (σ a)) = ψ' (σ a)
    rw [hψ'σ]
    exact hfixB a ha
  obtain ⟨α, w, hαψ, hwO, hwspan, hθw, hw2, hα2⟩ := exists_lift_isometry3 ψ' hker' τ hτ2
    hτr' fr (A.map σ.toMonoidHom) (B.map σ.toMonoidHom) hA' hB' (cq.pow3 _ (hσ A hA))
    (cq.pow3 _ (hσ B hB)) hfixA' hfixB'
  have hC' : C.map σ.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) (by norm_num)) := hσ C hC
  obtain ⟨iC, hiC⟩ := cq.map_mem _ hC'
  obtain ⟨FC, hFC, -⟩ := hiC
  set x' : spinGroup (quadPlus 4 (GaloisField 3 1)) := σ x with hx'
  have hx'C : x' ∈ C.map σ.toMonoidHom := ⟨x, hxC, rfl⟩
  have hψx' : ψ' x' = ψ x := hψ'σ x
  obtain ⟨A₀, hA₀⟩ : spinAction (quadPlus 4 (GaloisField 3 1)) x' ∈ FC.La.range := by
    rw [← hFC]
    exact Subgroup.mem_map_of_mem _ hx'C
  have hx'p : x' ^ 3 = 1 := by rw [hx', ← map_pow, hxp, map_one]
  have hA0p : A₀ ^ 3 = 1 := by
    refine FC.La_injective ?_
    rw [map_pow, hA₀, ← map_pow, hx'p, map_one, map_one]
  have hA0 : A₀ ≠ 1 := by
    intro h
    rw [h, map_one] at hA₀
    have := cq.inj _ hC' x' hx'C hA₀.symm
    apply hψx
    rw [← hψx', this, map_one]
  have hαx' : α x' = x'⁻¹ := by
    have hζ : x' * α x' ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) := by
      apply hker'
      rw [MonoidHom.mem_ker, map_mul, hαψ, hψx', hτx, mul_inv_cancel]
    have hcom : x' * α x' = α x' * x' := by
      have := Subgroup.mem_center_iff.mp hζ x'
      have h3 : x' * (x' * α x') = x' * (α x' * x') := by rw [this, mul_assoc]
      exact mul_left_cancel h3
    have hζp : (x' * α x') ^ 3 = 1 := by
      have : (x' * α x') ^ 3 = x' ^ 3 * (α x') ^ 3 := (Commute.mul_pow hcom 3)
      rw [this, hx'p, ← map_pow, hx'p, map_one, one_mul]
    have hZ := (plus_center_facts (F := GaloisField 3 1) (by norm_num) hm3).1 _ hζ hζp
    exact eq_inv_of_mul_eq_one_right hZ
  have hwinv : w * FC.La A₀ * w⁻¹ = (FC.La A₀)⁻¹ := by
    rw [hA₀, ← hθw x', hαx', map_inv]
  have hQ := nondegenerate_polarBilin_quadPlus 4 (GaloisField 3 1)
  have hCA : ∀ a ∈ A.map σ.toMonoidHom, x' * a = a * x' := by
    rintro _ ⟨a, ha, rfl⟩
    show σ x * σ a = σ a * σ x
    rw [← map_mul, ← map_mul, hcAC a ha x hxC]
  have hCB : ∀ a ∈ B.map σ.toMonoidHom, x' * a = a * x' := by
    rintro _ ⟨a, ha, rfl⟩
    show σ x * σ a = σ a * σ x
    rw [← map_mul, ← map_mul, hcBC a ha x hxC]
  have hcentA : ∀ A₁ : SL(2, GaloisField 3 1), FC.La A₀ * fr.La A₁ = fr.La A₁ * FC.La A₀ := by
    intro A₁
    have : fr.La A₁ ∈ (A.map σ.toMonoidHom).map (spinAction (quadPlus 4 (GaloisField 3 1))) := by
      rw [hA']
      exact ⟨A₁, rfl⟩
    obtain ⟨a, ha, hax⟩ := this
    rw [hA₀, ← hax, ← map_mul, ← map_mul, hCA a ha]
  have hcentB : ∀ B₁ : SL(2, GaloisField 3 1),
      FC.La A₀ * fr.swap.La B₁ = fr.swap.La B₁ * FC.La A₀ := by
    intro B₁
    have : fr.swap.La B₁ ∈ (B.map σ.toMonoidHom).map
        (spinAction (quadPlus 4 (GaloisField 3 1))) := by
      rw [hB']
      exact ⟨B₁, rfl⟩
    obtain ⟨a, ha, hax⟩ := this
    rw [hA₀, ← hax, ← map_mul, ← map_mul, hCB a ha]
  obtain ⟨up, um, hcup, hcum, hup0, hum0, hwup, hwum, hQup, hQum⟩ :=
    exists_eigen_pair_perp h2 hQ fr FC hA0 hA0p hwO hw2 hwinv hcentA hcentB
  obtain ⟨κ, hκ⟩ := exists_adapted_frame odd_gf3 hQ (plusFrame 4 (GaloisField 3 1) hm3) fr hwO
    hw2 hwspan hcup hcum hup0 hum0 hwup hwum hQup hQum
  obtain ⟨R, hRf, hRc, hRs, hRfix, hRn, hRm⟩ := exists_node_system (by norm_num) hm3 ψ' hker' τ hαψ
    (fun v => map_of_mem hwO v) hθw κ hκ
  refine ⟨fun a => (R a).map σ.symm.toMonoidHom, fun a => hσ' _ (hRf a), ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab h1 h2'
    exact (RouteD.TWS6.commutes_map_equiv σ.symm).mpr (hRc a b hab h1 h2')
  · intro a b hab
    obtain ⟨W, hW⟩ := hRs a b hab
    exact ⟨_, linearBlockStandardPair_map_equiv σ.symm hW⟩
  · intro a ha g hg
    obtain ⟨r, hr, rfl⟩ := hg
    exact hRfix a ha r hr
  · intro g hg
    obtain ⟨r, hr, rfl⟩ := hg
    obtain ⟨r', hr', hr'e⟩ := hRn r hr
    exact ⟨σ.symm r', ⟨r', hr', rfl⟩, hr'e⟩
  · obtain ⟨g, hg, hne⟩ := hRm
    exact ⟨σ.symm g, ⟨g, hg, rfl⟩, hne⟩

end CFSG.ClassicalInvolution.Q3.Q3TD
