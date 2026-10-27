module

public import CFSG.ClassicalInvolution.RouteD.TWS7Asm
public import CFSG.ClassicalInvolution.RouteD.TWS7Ord
public import CFSG.ClassicalInvolution.RouteD.TWS7Lift
public import CFSG.ClassicalInvolution.RouteD.TWS7Op
public import CFSG.ClassicalInvolution.RouteD.TWS7Frame
public import CFSG.ClassicalInvolution.RouteD.TWS7Diag
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.RouteD.Gaps (linearBlockStandardPair_map_equiv)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (plus_center_facts)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Model

variable {p f : ℕ} [Fact p.Prime]


theorem modelLeafD_proved : ModelLeafD p f := by
  classical
  intro hp2 hq X _ ψ hψ τ hτ2 hτr A B C hA hB hC hAB hcAB hcAC hcBC hfixA hfixB x hxC hψx hxp hτx
  have hf1 : 1 ≤ f := one_le_of_five_le_pow hq
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf1, le_refl 4⟩
  have hm3 : 3 ≤ 4 := by norm_num
  have c := TWS6.spinCtx8_plus hp2 hq hadm
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) := c.perfect
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd c.hodd
  obtain ⟨σ, fr, hσ, hσ', hA', hB'⟩ := exists_ordinary_pair hp2 hq hA hB hAB hcAB
  let ψ' : spinGroup (quadPlus 4 (GaloisField p f)) →* X := ψ.comp σ.symm.toMonoidHom
  have hψ'σ : ∀ y, ψ' (σ y) = ψ y := fun y => by simp [ψ']
  have hker' : ψ'.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    intro y hy
    have h1 : σ.symm y ∈ ψ.ker := hy
    have := TWS6.map_mem_center σ (hψ h1)
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
  obtain ⟨α, w, hαψ, hwO, hwspan, hθw, hw2, hα2⟩ := exists_lift_isometry hp2 hq ψ' hker' τ hτ2
    hτr' fr (A.map σ.toMonoidHom) (B.map σ.toMonoidHom) hA' hB' hfixA' hfixB'
  have hC' : C.map σ.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) (by norm_num)) := hσ C hC
  obtain ⟨iC, hiC⟩ := c.hcorr _ hC'
  obtain ⟨FC, hFC, -⟩ := hiC
  set x' : spinGroup (quadPlus 4 (GaloisField p f)) := σ x with hx'
  have hx'C : x' ∈ C.map σ.toMonoidHom := ⟨x, hxC, rfl⟩
  have hψx' : ψ' x' = ψ x := hψ'σ x
  obtain ⟨A₀, hA₀⟩ : spinAction (quadPlus 4 (GaloisField p f)) x' ∈ FC.La.range := by
    rw [← hFC]
    exact Subgroup.mem_map_of_mem _ hx'C
  have hx'p : x' ^ p = 1 := by rw [hx', ← map_pow, hxp, map_one]
  have hA0p : A₀ ^ p = 1 := by
    refine FC.La_injective ?_
    rw [map_pow, hA₀, ← map_pow, hx'p, map_one, map_one]
  have hA0 : A₀ ≠ 1 := by
    intro h
    rw [h, map_one] at hA₀
    have := c.hinj hC' x' hx'C hA₀.symm
    apply hψx
    rw [← hψx', this, map_one]
  have hαx' : α x' = x'⁻¹ := by
    have hζ : x' * α x' ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
      apply hker'
      rw [MonoidHom.mem_ker, map_mul, hαψ, hψx', hτx, mul_inv_cancel]
    have hcom : x' * α x' = α x' * x' := by
      have := Subgroup.mem_center_iff.mp hζ x'
      have h3 : x' * (x' * α x') = x' * (α x' * x') := by rw [this, mul_assoc]
      exact mul_left_cancel h3
    have hζp : (x' * α x') ^ p = 1 := by
      have : (x' * α x') ^ p = x' ^ p * (α x') ^ p := (Commute.mul_pow hcom p)
      rw [this, hx'p, ← map_pow, hx'p, map_one, one_mul]
    have hZ := (plus_center_facts (F := GaloisField p f) hp2 hm3).1 _ hζ hζp
    exact eq_inv_of_mul_eq_one_right hZ
  have hwinv : w * FC.La A₀ * w⁻¹ = (FC.La A₀)⁻¹ := by
    rw [hA₀, ← hθw x', hαx', map_inv]
  have hQ := c.hQ
  have hCA : ∀ a ∈ A.map σ.toMonoidHom, x' * a = a * x' := by
    rintro _ ⟨a, ha, rfl⟩
    show σ x * σ a = σ a * σ x
    rw [← map_mul, ← map_mul, hcAC a ha x hxC]
  have hCB : ∀ a ∈ B.map σ.toMonoidHom, x' * a = a * x' := by
    rintro _ ⟨a, ha, rfl⟩
    show σ x * σ a = σ a * σ x
    rw [← map_mul, ← map_mul, hcBC a ha x hxC]
  have hcentA : ∀ A₁ : SL(2, GaloisField p f), FC.La A₀ * fr.La A₁ = fr.La A₁ * FC.La A₀ := by
    intro A₁
    have : fr.La A₁ ∈ (A.map σ.toMonoidHom).map (spinAction (quadPlus 4 (GaloisField p f))) := by
      rw [hA']
      exact ⟨A₁, rfl⟩
    obtain ⟨a, ha, hax⟩ := this
    rw [hA₀, ← hax, ← map_mul, ← map_mul, hCA a ha]
  have hcentB : ∀ B₁ : SL(2, GaloisField p f),
      FC.La A₀ * fr.swap.La B₁ = fr.swap.La B₁ * FC.La A₀ := by
    intro B₁
    have : fr.swap.La B₁ ∈ (B.map σ.toMonoidHom).map
        (spinAction (quadPlus 4 (GaloisField p f))) := by
      rw [hB']
      exact ⟨B₁, rfl⟩
    obtain ⟨a, ha, hax⟩ := this
    rw [hA₀, ← hax, ← map_mul, ← map_mul, hCB a ha]
  obtain ⟨up, um, hcup, hcum, hup0, hum0, hwup, hwum, hQup, hQum⟩ :=
    exists_eigen_pair_perp h2 hQ fr FC hA0 hA0p hwO hw2 hwinv hcentA hcentB
  obtain ⟨κ, hκ⟩ := exists_adapted_frame c.hodd hQ (plusFrame 4 (GaloisField p f) hm3) fr hwO
    hw2 hwspan hcup hcum hup0 hum0 hwup hwum hQup hQum
  obtain ⟨R, hRf, hRc, hRs, hRfix, hRn, hRm⟩ := exists_node_system hp2 hm3 ψ' hker' τ hαψ
    (fun v => map_of_mem hwO v) hθw κ hκ
  refine ⟨fun a => (R a).map σ.symm.toMonoidHom, fun a => hσ' _ (hRf a), ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab h1 h2'
    exact (TWS6.commutes_map_equiv σ.symm).mpr (hRc a b hab h1 h2')
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

end Model

end CFSG.ClassicalInvolution.RouteD.TWS7
