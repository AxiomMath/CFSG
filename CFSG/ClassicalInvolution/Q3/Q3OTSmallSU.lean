module

public import CFSG.ClassicalInvolution.Q3.Q3P21S6
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1M
public import CFSG.ClassicalInvolution.Q3.Q3WAPow
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (twinOuterAlphaOn_of_autVac)
open scoped MatrixGroups


theorem pow3_su_two :
    ∀ l : Su (GaloisField 3 (2 * 1)) 3 1 2,
      l ^ 3 ∈ ⁅(⊤ : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 2)),
        (⊤ : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 2))⁆ := by
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨e⟩ := Q3.Q3P21.exists_su2_equiv_sl2 hK (by norm_num) (by norm_num)
  have hz3 : Nat.card (ZMod 3) = 3 := by simp
  have h := Q3.Q3W.pow3_range_sl2 hz3 e.symm.toMonoidHom
  have hr : e.symm.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.symm.surjective
  rw [hr] at h
  exact fun l => h l (Subgroup.mem_top l)

theorem su4_aut_blocks3 {X : Type} [Group X] (θ : Su (GaloisField 3 (2 * 1)) 3 1 4 →* X)
    (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4)) (σ : MulAut X)
    (hσ4 : σ * σ * (σ * σ) = 1)
    (hfix0 : ∀ A : Su (GaloisField 3 (2 * 1)) 3 1 2,
      σ (θ (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) A)) =
        θ (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su (GaloisField 3 (2 * 1)) 3 1 2,
      σ (θ (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num) A)) =
        θ (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num) A)) :
    σ * σ = 1 ∨ σ * σ = MulAut.conj (θ (rootInvSU (GaloisField 3 (2 * 1)) 3 1
      (show 2 ≤ 4 by norm_num))) := by
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨α, g, φ, hlift, hmat, -, -⟩ :=
    Q3NT.unitaryAutClassification_isometry_of_odd hK hp le_rfl (d := 4) (by norm_num) X θ hθ
      hker σ
  have hcop : ∀ x ∈ θ.ker, ¬ 3 ∣ orderOf x := fun x hx =>
    Q3.Q3P21.cop_center_su4_three x (hker hx)
  have hfixα : ∀ (i : ℕ) (hi : i + 2 ≤ 4),
      (∀ A : Su (GaloisField 3 (2 * 1)) 3 1 2,
        σ (θ (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 i hi A)) =
          θ (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 i hi A)) →
      ∀ A : Su (GaloisField 3 (2 * 1)) 3 1 2,
        α (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 i hi A) =
          blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 i hi A := by
    intro i hi hfix A
    have := Q3.Q3W.hom_eq_of_central_ker3_gen θ hker hcop pow3_su_two
      (α.comp (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 i hi))
      (blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 i hi) (fun l => by
        rw [MonoidHom.comp_apply, hlift, hfix l])
    exact DFunLike.congr_fun this A
  have hαfix0 := hfixα 0 (by norm_num) hfix0
  have hαfix2 := hfixα 2 (by norm_num) hfix2
  have h4 : ∀ y, σ (σ (σ (σ y))) = y := fun y => by
    have := congrArg (fun τ : MulAut X => τ y) hσ4
    simpa using this
  have hα4 : ∀ x, α (α (α (α x))) * x⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
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

theorem psu4_autVac3 {R R' : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)}
    (hR : R ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
      (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
      (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su (GaloisField 3 (2 * 1)) 3 1 4} (hxR : x ∈ R) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))
    (σ : MulAut (Su (GaloisField 3 (2 * 1)) 3 1 4 ⧸
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4)))
    (hσ : ∀ r ∈ R, σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ' : ∀ r ∈ R', σ (QuotientGroup.mk r) = QuotientGroup.mk r)
    (hσ4 : σ * σ * (σ * σ) = 1) :
    σ * σ = 1 ∨ σ * σ = MulAut.conj (QuotientGroup.mk x) := by
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std_u hK hp hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set θ : Su (GaloisField 3 (2 * 1)) 3 1 4 →*
      Su (GaloisField 3 (2 * 1)) 3 1 4 ⧸ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) :=
    QuotientGroup.mk' _ with hθ
  set c : MulAut (Su (GaloisField 3 (2 * 1)) 3 1 4 ⧸
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4)) := MulAut.conj (θ g) with hcdef
  have hcp : ∀ s, c (θ s) = θ (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set σ' : MulAut (Su (GaloisField 3 (2 * 1)) 3 1 4 ⧸
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4)) := c⁻¹ * σ * c with hσ'def
  have hσ'p : ∀ s, σ' (θ s) = (c⁻¹) (σ (c (θ s))) := fun s => rfl
  have hfixσ' : ∀ (S : Subgroup (Su (GaloisField 3 (2 * 1)) 3 1 4)),
      (∀ r ∈ S.map (MulAut.conj g).toMonoidHom, σ (θ r) = θ r) → ∀ r ∈ S, σ' (θ r) = θ r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hσ'p, hcp, hS _ hmem, ← hcp]
    simp
  have hσ4' : σ' * σ' * (σ' * σ') = 1 := by
    calc σ' * σ' * (σ' * σ') = c⁻¹ * (σ * σ * (σ * σ)) * c := by rw [hσ'def]; group
      _ = 1 := by rw [hσ4]; group
  have hfix0 := hfixσ' ((blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 0 (by norm_num)).range)
    (hRg ▸ hσ)
  have hfix2 := hfixσ' ((blockEmb (GaloisField 3 (2 * 1)) 3 1 4 2 2 (by norm_num)).range)
    (hR'g ▸ hσ')
  have hsq : σ * σ = c * (σ' * σ') * c⁻¹ := by rw [hσ'def]; group
  rcases su4_aut_blocks3 θ (QuotientGroup.mk'_surjective _)
      (by rw [hθ, QuotientGroup.ker_mk']) σ' hσ4' (fun A => hfix0 _ ⟨A, rfl⟩)
      (fun A => hfix2 _ ⟨A, rfl⟩) with h | h
  · left
    rw [hsq, h]
    group
  · right
    rw [hsq, h, hxg]
    have : MulAut.conj (θ (g * rootInvSU (GaloisField 3 (2 * 1)) 3 1 (show 2 ≤ 4 by norm_num) *
        g⁻¹)) = c * MulAut.conj (θ (rootInvSU (GaloisField 3 (2 * 1)) 3 1
          (show 2 ≤ 4 by norm_num))) * c⁻¹ := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    exact this.symm

theorem twinOuterAlpha3_psu (hadm : StatedLieAdmissible .PSU 4 3 1) :
    TwinOuterAlpha 3 1 .PSU 4 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : NeZero (2 * 1) := ⟨by norm_num⟩
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 4 3 1 Fact.out trivial hadm).1.1
  refine twinOuterAlphaOn_of_autVac (t := .PSU)
    (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 3 1 Fact.out)
    ((QuotientGroup.mk' (Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4))).comp
      φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp φ.surjective) ?_ ?_
  · ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ x) : Su (GaloisField 3 (2 * 1)) 3 1 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ x
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc σ hσ hσ' hσ4
    have hne' : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective φ.injective h)
    have hc' : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
      have := (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ
        (x' * x⁻¹)).mpr hc
      rwa [map_mul, map_inv] at this
    exact psu4_autVac3 ((hφ R).mp hR) ((hφ R').mp hR') hne' ⟨x, hxR, rfl⟩
      (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (φ.injective (h.trans (map_one φ).symm)))
      ⟨x', hx'R', rfl⟩ (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc' σ
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ r hr)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ' r hr)
      hσ4

end CFSG.ClassicalInvolution.Q3.Q3OT
