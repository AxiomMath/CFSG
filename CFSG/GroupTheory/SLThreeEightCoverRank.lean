module

public import CFSG.GroupTheory.PerfectCentralProd
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRankTwo
public import CFSG.Quasithin.H13.NQBlockPRankProduct

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup
open scoped commutatorElement

theorem four_le_pRank_of_sl3_eight_product_cover
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {F₀ F₁ : Type} [Field F₀] [Finite F₀] [Field F₁] [Finite F₁]
    (hF₀ : Nat.card F₀ = 8) (hF₁ : Nat.card F₁ = 8)
    (f : Y →* (Matrix.SpecialLinearGroup (Fin 3) F₀ ×
      Matrix.SpecialLinearGroup (Fin 3) F₁))
    (hf : Function.Surjective f)
    (hlayer : CFSG.layer (Y ⧸ CFSG.pCore 2 Y) = ⊤)
    (hsolv : Group.IsSolvable f.ker)
    (hR : CFSG.pCore 2 Y ≤ f.ker) :
    4 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup Y := CFSG.pCore 2 Y
  have hRn : R.Normal := CFSG.pCore_normal
  let Q := Y ⧸ R
  let π : Y →* Q := QuotientGroup.mk' R
  let η : Q →* (Matrix.SpecialLinearGroup (Fin 3) F₀ ×
      Matrix.SpecialLinearGroup (Fin 3) F₁) := QuotientGroup.lift R f hR
  have hηπ : η.comp π = f := MonoidHom.ext fun y => QuotientGroup.lift_mk' R hR y
  have hη : Function.Surjective η := by
    intro x
    obtain ⟨y, hy⟩ := hf x
    refine ⟨π y, ?_⟩
    have h : η (π y) = f y := by
      rw [← MonoidHom.comp_apply, hηπ]
    rw [h, hy]
  have hkerη : η.ker = f.ker.map π := QuotientGroup.ker_lift R f hR
  have hKn : (f.ker.map π).Normal :=
    (MonoidHom.normal_ker f).map π (QuotientGroup.mk'_surjective R)
  have hksolv : Group.IsSolvable ↥(f.ker.map π) := by
    have := hsolv
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective f.ker)
  have hkerle : η.ker ≤ Subgroup.center Q := by
    rw [hkerη]
    exact (CFSG.SectionRank.semisimple_solvable_quotient
      (by simpa [Q, R] using hlayer) (f.ker.map π) hksolv).1
  have hQcomm : commutator Q = ⊤ := by
    have h := CFSG.LocalCores.layer_perfect (G := Q)
    rw [show CFSG.layer Q = ⊤ by simpa [Q, R] using hlayer] at h
    simpa only [commutator_def] using h
  have hQperf : Group.IsPerfect Q := Group.IsPerfect.mk hQcomm
  have hcov : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 8 →
      ∀ E : Subgroup Q, commutator ↥E = ⊤ →
      ∀ g : ↥E →* Matrix.SpecialLinearGroup (Fin 3) F,
      Function.Surjective g → g.ker ≤ Subgroup.center ↥E → g.ker = ⊥ := by
    intro F _ _ hF E hE g hg hcen
    have hEperf : Group.IsPerfect ↥E := Group.IsPerfect.mk hE
    obtain ⟨σ, hσ⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
        (m := 2) (F := F) (E := ↥E) (π := g)
        (by norm_num) (by rw [hF]; norm_num) hg hcen
    have hsup' : Subgroup.center ↥E ⊔ σ.range = ⊤ := by
      rw [eq_top_iff]
      intro e _
      have hz : e * (σ (g e))⁻¹ ∈ Subgroup.center ↥E := hcen (by
        rw [MonoidHom.mem_ker]
        simp [hσ])
      have he : e = (e * (σ (g e))⁻¹) * σ (g e) := by group
      refine (Subgroup.mem_sup_of_normal_left (s := Subgroup.center ↥E)
        (t := σ.range) (x := e)).mpr ?_
      exact ⟨e * (σ (g e))⁻¹, hz, σ (g e), MonoidHom.mem_range.mpr ⟨g e, rfl⟩, he.symm⟩
    have hsup : σ.range ⊔ Subgroup.center ↥E = ⊤ := by
      simpa [sup_comm] using hsup'
    have hrange : σ.range = ⊤ :=
      (CFSG.SectionRank.perfect_central_supplement hEperf).1 σ.range hsup
    rw [eq_bot_iff]
    intro e he
    have hre : e ∈ σ.range := by rw [hrange]; exact Subgroup.mem_top e
    obtain ⟨s, rfl⟩ := hre
    have hs : s = 1 := by
      have := MonoidHom.mem_ker.mp he
      simpa [hσ] using this
    rw [hs, map_one]
    exact Subgroup.mem_bot.mpr rfl
  have hηkerbot : η.ker = ⊥ :=
    CFSG.GroupTheory.ker_eq_bot_of_perfect_central_prod_of_forall
      hQcomm η hη hkerle (hcov F₀ hF₀) (hcov F₁ hF₁)
  have hinj : Function.Injective η := (MonoidHom.ker_eq_bot_iff η).mp hηkerbot
  let e : Q ≃* (Matrix.SpecialLinearGroup (Fin 3) F₀ ×
      Matrix.SpecialLinearGroup (Fin 3) F₁) := MulEquiv.ofBijective η ⟨hinj, hη⟩
  have hQrank : 4 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup Q) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) Nat.prime_seven.one_lt e]
    have hprod : CFSG.Open.pRank 7
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₀ ×
          Matrix.SpecialLinearGroup (Fin 3) F₁)) =
        CFSG.Open.pRank 7 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₀)) +
          CFSG.Open.pRank 7 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₁)) := by
      calc CFSG.Open.pRank 7
            (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₀ ×
              Matrix.SpecialLinearGroup (Fin 3) F₁))
          = CFSG.pRank 7 (Matrix.SpecialLinearGroup (Fin 3) F₀ ×
              Matrix.SpecialLinearGroup (Fin 3) F₁) :=
            (CFSG.SectionRank.pRank_eq_open_pRank_top (p := 7) _).symm
        _ = CFSG.pRank 7 (Matrix.SpecialLinearGroup (Fin 3) F₀) +
              CFSG.pRank 7 (Matrix.SpecialLinearGroup (Fin 3) F₁) :=
            CFSG.Quasithin.H13.NQBlock.pRank_prod_eq Nat.prime_seven
        _ = CFSG.Open.pRank 7 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₀)) +
              CFSG.Open.pRank 7 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₁)) := by
            rw [CFSG.SectionRank.pRank_eq_open_pRank_top (p := 7),
              CFSG.SectionRank.pRank_eq_open_pRank_top (p := 7)]
    rw [hprod]
    have hchar₀ : CharP F₀ 2 := by
      have : Fintype F₀ := Fintype.ofFinite F₀
      exact charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
        rw [← Nat.card_eq_fintype_card, hF₀]; norm_num)
    have hchar₁ : CharP F₁ 2 := by
      have : Fintype F₁ := Fintype.ofFinite F₁
      exact charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
        rw [← Nat.card_eq_fintype_card, hF₁]; norm_num)
    have h0 : 2 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₀)) := by
      have := hchar₀
      have hdvd : 7 ∣ Nat.card F₀ - 1 := by
        rw [hF₀]
      exact (CFSG.ClassicalGroups.SpecialLinear.two_le_pRank_diagTorus
        (F := F₀) (q := 7) Nat.prime_seven hdvd).trans
        (CFSG.SectionRank.pRank_mono (p := 7) Nat.prime_seven.one_lt le_top)
    have h1 : 2 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F₁)) := by
      have := hchar₁
      have hdvd : 7 ∣ Nat.card F₁ - 1 := by
        rw [hF₁]
      exact (CFSG.ClassicalGroups.SpecialLinear.two_le_pRank_diagTorus
        (F := F₁) (q := 7) Nat.prime_seven hdvd).trans
        (CFSG.SectionRank.pRank_mono (p := 7) Nat.prime_seven.one_lt le_top)
    omega
  rw [← CFSG.SectionRank.pRank_quotient_two_group (G := Y) (P := CFSG.pCore 2 Y)
    (r := 7) (CFSG.pCore_isPGroup) Nat.prime_seven (by norm_num)]
  exact hQrank

end CFSG.GroupTheory
