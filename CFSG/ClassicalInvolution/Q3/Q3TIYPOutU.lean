module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGen
public import CFSG.ClassicalInvolution.Q3.Q3URPat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.ModelFacts (modelClauseZero)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (mulEquiv_mem_center_iff)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.ClassicalInvolution.Q3 (CompData)
open scoped commutatorElement

section Aut

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_aut_blocks3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (hcen : ∀ x ∈ Subgroup.center (Su K p f 4), ¬ 3 ∣ orderOf x) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (σ : MulAut X) (hσ4 : σ * σ * (σ * σ) = 1)
    (hfix0 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, σ (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    σ * σ = 1 ∨ σ * σ = MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) := by
  obtain ⟨α, g, φ, hlift, hmat, -, -⟩ :=
    Q3NT.unitaryAutClassification_isometry_of_odd hK hp hf (d := 4) (by norm_num) X θ hθ hker σ
  have hcop : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x := fun x hx => hcen x (hker hx)
  have hαfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A := fun A =>
    DFunLike.congr_fun (Q3W.lift_comp_eq_of_fixed3 hP3 hker hcop hlift
      (blockEmb K p f 4 2 0 (by norm_num)) hfix0) A
  have hαfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A := fun A =>
    DFunLike.congr_fun (Q3W.lift_comp_eq_of_fixed3 hP3 hker hcop hlift
      (blockEmb K p f 4 2 2 (by norm_num)) hfix2) A
  have h4 : ∀ y, σ (σ (σ (σ y))) = y := fun y => by
    have := congrArg (fun τ : MulAut X => τ y) hσ4
    simpa using this
  have hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    intro x
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, hlift, hlift, hlift, h4, mul_inv_cancel]
  rcases su4_fixing hK hp α g φ (fun x => hmat x) hαfix0 hαfix2 hα4 with h | h
  · left
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    show σ (σ (θ x)) = θ x
    rw [← hlift x, ← hlift (α x), h x]
  · right
    ext y
    obtain ⟨x, rfl⟩ := hθ y
    show σ (σ (θ x)) = _
    rw [← hlift x, ← hlift (α x), h x]
    simp [map_mul, map_inv]

theorem psu4_autVac3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hf : 1 ≤ f)
    (hP3 : ∀ l : Su K p f 2, l ^ 3 ∈ ⁅(⊤ : Subgroup (Su K p f 2)), (⊤ : Subgroup (Su K p f 2))⁆)
    (hcen : ∀ x ∈ Subgroup.center (Su K p f 4), ¬ 3 ∣ orderOf x)
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4))
    (σ : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)))
    (hσ : ∀ r ∈ R, σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ' : ∀ r ∈ R', σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ4 : σ * σ * (σ * σ) = 1) :
    σ * σ = 1 ∨ σ * σ = MulAut.conj (QuotientGroup.mk x) := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set θ : Su K p f 4 →* Su K p f 4 ⧸ Subgroup.center (Su K p f 4) := QuotientGroup.mk' _
    with hθ
  set c : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := MulAut.conj (θ g) with hcdef
  have hcp : ∀ s, c (θ s) = θ (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set σ' : MulAut (Su K p f 4 ⧸ Subgroup.center (Su K p f 4)) := c⁻¹ * σ * c with hσ'def
  have hσ'p : ∀ s, σ' (θ s) = (c⁻¹) (σ (c (θ s))) := fun s => rfl
  have hfixσ' : ∀ (S : Subgroup (Su K p f 4)),
      (∀ r ∈ S.map (MulAut.conj g).toMonoidHom, σ (θ r) = θ r) → ∀ r ∈ S, σ' (θ r) = θ r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hσ'p, hcp, hS _ hmem, ← hcp]
    simp
  have hσ4' : σ' * σ' * (σ' * σ') = 1 := by
    calc σ' * σ' * (σ' * σ') = c⁻¹ * (σ * σ * (σ * σ)) * c := by rw [hσ'def]; group
      _ = 1 := by rw [hσ4]; group
  have hfix0 := hfixσ' ((blockEmb K p f 4 2 0 (by norm_num)).range) (hRg ▸ hσ)
  have hfix2 := hfixσ' ((blockEmb K p f 4 2 2 (by norm_num)).range) (hR'g ▸ hσ')
  have hsq : σ * σ = c * (σ' * σ') * c⁻¹ := by rw [hσ'def]; group
  rcases su4_aut_blocks3 hK hp hf hP3 hcen θ (QuotientGroup.mk'_surjective _)
      (by rw [hθ, QuotientGroup.ker_mk']) σ' hσ4' (fun A => hfix0 _ ⟨A, rfl⟩)
      (fun A => hfix2 _ ⟨A, rfl⟩) with h | h
  · left
    rw [hsq, h]
    group
  · right
    rw [hsq, h, hxg]
    have : MulAut.conj (θ (g * rootInvSU K p f (show 2 ≤ 4 by norm_num) * g⁻¹)) =
        c * MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) * c⁻¹ := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    exact this.symm

end Aut


theorem sqDichotomyC_psu4 (hadm : StatedLieAdmissible .PSU 4 3 1) :
    SqDichotomyC (CompData.model .PSU 4) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv (p := 3) (f := 1) hp2 hadm
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 3 1
      Nat.prime_three).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSU 4 3 1 Nat.prime_three trivial hadm).1.1
  have hP3 : ∀ l : Su (GaloisField 3 (2 * 1)) 3 1 2,
      l ^ 3 ∈ ⁅(⊤ : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 2)),
        (⊤ : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 2))⁆ := Q3W.su2_pow_three_mem_commutator
  have hcen : ∀ x ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4), ¬ 3 ∣ orderOf x :=
    fun x hx => Q3W.center_orderOf_not_dvd_three_su3 (by norm_num) hx
  refine sqDichotomyC_of_autVac (CompData.model .PSU 4)
    ((QuotientGroup.mk' (Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))).comp
      φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp φ.surjective) ?_ ?_
  · ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ x) : Su (GaloisField 3 (2 * 1)) 3 1 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact mulEquiv_mem_center_iff φ x
  · intro R R' hR hR' hne x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc σ hσ hσ' hσ4
    have hne' : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective φ.injective h)
    have hc' : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
      have := (mulEquiv_mem_center_iff φ (x' * x⁻¹)).mpr hc
      rwa [map_mul, map_inv] at this
    exact psu4_autVac3 hK hp2 le_rfl hP3 hcen ((hφ R).mp hR) ((hφ R').mp hR') hne'
      ⟨x, hxR, rfl⟩ (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (φ.injective (h.trans (map_one φ).symm)))
      ⟨x', hx'R', rfl⟩ (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc' σ
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ r hr)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ' r hr)
      hσ4

end CFSG.ClassicalInvolution.Q3.Q3TIY
