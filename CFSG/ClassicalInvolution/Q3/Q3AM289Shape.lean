module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Dich
public import CFSG.ClassicalInvolution.Q3.Q3AM289SU3
public import CFSG.ClassicalInvolution.Q3.Q3T8B16T1
public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Gen

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.Q3W.EX (GenFact3 genFact3_g2 genFact3_td4)

section Def


@[expose] def S3Shape {Y : Type} [Group Y] (Φ : Set (Subgroup Y)) : Prop :=
  ∃ (c : CompData) (ψ : c.G →* Y),
    (c = CompData.model .PSU 3 ∨ c = CompData.model .G2 0 ∨ c = CompData.model .trialityD4 0) ∧
      ψ.ker ≤ Subgroup.center c.G ∧ Function.Surjective ψ ∧
        ∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map ψ

end Def

section Facts


variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}

theorem center_eq_bot_of_rows {c : CompData}
    (hc : c = CompData.model .PSU 3 ∨ c = CompData.model .G2 0 ∨
      c = CompData.model .trialityD4 0) : Subgroup.center c.G = ⊥ := by
  rcases hc with rfl | rfl | rfl
  · obtain ⟨e', -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
      Q3PP.statedLieAdmissible_psu3
    rw [eq_bot_iff]
    intro x hx
    have h1 : e' x ∈ Subgroup.center Q3PP.SU3 := by
      rw [← Subgroup.map_center_eq e']
      exact ⟨x, hx, rfl⟩
    rw [Q3PP.center_su3_eq_bot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (e'.injective (by rw [h1, map_one]))
  · exact RouteD.G2D4.center_modelUniv_g2d4_eq_bot (by norm_num) (Or.inl rfl) 0 le_rfl
  · exact RouteD.G2D4.center_modelUniv_g2d4_eq_bot (by norm_num) (Or.inr rfl) 0 le_rfl

theorem S3Shape.exists_bijective (h : S3Shape Φ) :
    ∃ (c : CompData) (ψ : c.G →* Y),
      (c = CompData.model .PSU 3 ∨ c = CompData.model .G2 0 ∨
        c = CompData.model .trialityD4 0) ∧ Function.Bijective ψ ∧
        ∀ L ∈ Φ, ∃ R ∈ c.fund, L = R.map ψ := by
  obtain ⟨c, ψ, hc, hker, hsurj, hfund⟩ := h
  refine ⟨c, ψ, hc, ⟨?_, hsurj⟩, hfund⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  exact hker.trans (center_eq_bot_of_rows hc).le

theorem S3Shape.center_eq_bot (h : S3Shape Φ) : Subgroup.center Y = ⊥ := by
  obtain ⟨c, ψ, hc, hbij, -⟩ := h.exists_bijective
  have hZ := center_eq_bot_of_rows hc
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := hbij.2 y
  have hx : x ∈ Subgroup.center c.G := by
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply hbij.1
    rw [map_mul, map_mul]
    exact hy (ψ g)
  rw [hZ, Subgroup.mem_bot] at hx
  rw [hx, map_one]
  exact Subgroup.one_mem _

theorem involutionsConj_of_rows {c : CompData}
    (hc : c = CompData.model .PSU 3 ∨ c = CompData.model .G2 0 ∨
      c = CompData.model .trialityD4 0) :
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj c.G := by
  rcases hc with rfl | rfl | rfl
  · exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.involutionsConj_modelUniv
      (p := 3) (by norm_num) (Or.inr (Or.inl ⟨rfl, rfl⟩)) Q3PP.statedLieAdmissible_psu3
  · exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.involutionsConj_modelUniv
      (p := 3) (by norm_num) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩)
  · exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.involutionsConj_modelUniv
      (p := 3) (by norm_num) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl⟩)

theorem S3Shape.involutionsConj (h : S3Shape Φ) :
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj Y := by
  obtain ⟨c, ψ, hc, hbij, -⟩ := h.exists_bijective
  exact CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj.of_mulEquiv
    (MulEquiv.ofBijective ψ hbij).symm (involutionsConj_of_rows hc)

theorem S3Shape.invol_dich (h : S3Shape Φ) {J' : Subgroup Y} (hJ' : J' ∈ Φ) {u : Y}
    (hu : IsUniqueInvolution J' u) (β : MulAut Y) (hβ2 : β * β = 1)
    (hβ : ∀ x ∈ J', β x = x) : β = 1 ∨ β = MulAut.conj u := by
  obtain ⟨c, ψ, hc, hbij, hfund⟩ := h.exists_bijective
  obtain ⟨R, hR, hJR⟩ := hfund J' hJ'
  rw [hJR] at hu hβ
  have hZ := center_eq_bot_of_rows hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨e', he'⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num)
      Q3PP.statedLieAdmissible_psu3
    obtain ⟨g₀, hg₀⟩ := (Models.mem_longRootSetU_iff (by norm_num)).mp ((he' R).mp hR)
    have hg₀' : R.map e'.toMonoidHom = conjSub g₀ Q3PP.rootSU2₃ := hg₀
    let ψ' : Q3PP.SU3 →* Y := ψ.comp e'.symm.toMonoidHom
    have hψ' : Function.Bijective ψ' :=
      ⟨hbij.1.comp e'.symm.injective, hbij.2.comp e'.symm.surjective⟩
    have hJψ : R.map ψ = (conjSub g₀ Q3PP.rootSU2₃).map ψ' := by
      rw [← hg₀', Subgroup.map_map]
      congr 1
      ext x
      simp [ψ']
    rw [hJψ] at hu hβ
    exact dich_transport ψ' hψ' (R := conjSub g₀ Q3PP.rootSU2₃)
      (fun ρ hρ2 hρR => Q3PP.su3_involutory_fixes Q3PP.outOne_su3 ρ hρ2 hρR) hu β hβ2 hβ
  · exact dich_transport ψ hbij (R := R)
      (fun ρ hρ2 hρR => invol_fixes_of_fg0 hZ
        (NDB.G2S.fg0Model_of_tag (by norm_num) le_rfl (Or.inl rfl) hR) ρ hρ2 hρR) hu β hβ2 hβ
  · exact dich_transport ψ hbij (R := R)
      (fun ρ hρ2 hρR => invol_fixes_of_fg0 hZ
        (NDB.G2S.fg0Model_of_tag (by norm_num) le_rfl (Or.inr rfl) hR) ρ hρ2 hρR) hu β hβ2 hβ

theorem linkModelFacts_of_gen {Q : Type} [Group Q]
    (hconj : CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj Q)
    (hgen : ∀ r r' : Q, r * r = 1 → r' * r' = 1 → r ≠ 1 → r' ≠ 1 → r ≠ r' → r * r' = r' * r →
      Subgroup.centralizer ({r} : Set Q) ⊔ Subgroup.centralizer ({r'} : Set Q) = ⊤) :
    LinkModelFacts Q := by
  refine ⟨fun u v hu hu1 hv hv1 => hconj u v hu hv hu1 hv1, ?_⟩
  intro u v hu hu1 hv hv1 huv hcomm
  rw [eq_top_iff, ← hgen u v hu hv hu1 hv1 huv hcomm]
  exact le_sup_left

theorem S3Shape.linkModelFacts (h : S3Shape Φ) :
    LinkModelFacts Y := by
  obtain ⟨c, ψ, hc, hbij, -⟩ := h.exists_bijective
  refine LinkModelFacts.of_mulEquiv (MulEquiv.ofBijective ψ hbij).symm ?_
  rcases hc with rfl | rfl | rfl
  · exact linkModelFacts_psu3_model
  · exact linkModelFacts_of_gen (involutionsConj_of_rows (Or.inr (Or.inl rfl)))
      (genFact3_g2 (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩))
  · exact linkModelFacts_of_gen (involutionsConj_of_rows (Or.inr (Or.inr rfl)))
      (genFact3_td4 (show CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 0 3 1 from
        ⟨Nat.prime_three, le_rfl, rfl⟩))

theorem S3Shape.of_lieSystemData3 {ι : Type} (D : LieSystemData3 ι Y Φ) {i₁ : ι}
    (hi : ∀ i, i = i₁)
    (hk : D.kind i₁ = CompData.model .PSU 3 ∨ D.kind i₁ = CompData.model .G2 0 ∨
      D.kind i₁ = CompData.model .trialityD4 0) : S3Shape Φ := by
  refine ⟨D.kind i₁, D.hom i₁, hk, D.ker_le_center i₁, ?_, fun L hL => ?_⟩
  · have h1 := D.generate
    have h2 : ⨆ i, (D.hom i).range = (D.hom i₁).range := by
      apply le_antisymm
      · exact iSup_le fun i => by rw [hi i]
      · exact le_iSup (fun i => (D.hom i).range) i₁
    rw [h2] at h1
    exact MonoidHom.range_eq_top.mp h1
  · obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl := hi i
    exact ⟨R, hR, hLR⟩

end Facts

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
