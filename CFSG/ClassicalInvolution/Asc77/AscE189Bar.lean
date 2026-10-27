module

public import CFSG.ClassicalInvolution.Asc77.AscE189Comp
public import CFSG.ClassicalInvolution.Asc77.AscIHThm4
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscE186CentA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Bar

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y]

theorem OmegaLie.map_fund_eq_comp_of_A1 {Ω : Set (Subgroup Y)} (D : OmegaLie p f Ω)
    (i : Fin D.card) (hA1 : D.tag i = .PSL ∧ D.rank i = 2)
    {R : Subgroup (D.model i).K} (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D) :
    R.map (D.hom i) = D.comp i := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (_ : t = .PSL) (_ : n = 2)
      (hadm : StatedLieAdmissible t n p e) (φ : (modelUniv t n p e Fact.out).K →* Y)
      (R : Subgroup (modelUniv t n p e Fact.out).K)
      (_ : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D), R.map φ = φ.range := by
    intro t n e hT hN hadm φ R hR
    subst hT hN
    have : R = ⊤ := CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e
      Fact.out hadm R hR
    rw [this, Subgroup.map_top]
  exact key _ _ _ hA1.1 hA1.2 (D.admissible i) (D.hom i) R hR

theorem OmegaLie.exists_model_conj {Ω : Set (Subgroup Y)} (D : OmegaLie p f Ω) (i : Fin D.card)
    {g : Y} (hg : g ∈ omegaGen Ω) :
    ∃ q : (D.model i).K, ∀ x ∈ D.comp i, g * x * g⁻¹ = D.hom i q * x * (D.hom i q)⁻¹ := by
  rw [← D.iSup_comp] at hg
  induction hg using Subgroup.iSup_induction' with
  | hp k y hy =>
    by_cases hki : k = i
    · subst hki
      obtain ⟨q, rfl⟩ := hy
      exact ⟨q, fun x _ => rfl⟩
    · refine ⟨1, fun x hx => ?_⟩
      have := D.comp_commute hki y hy x hx
      rw [map_one, one_mul, inv_one, mul_one, this, mul_assoc, mul_inv_cancel, mul_one]
  | h1 => exact ⟨1, fun x _ => by simp⟩
  | hmul a b ha hb ha' hb' =>
    obtain ⟨qa, hqa⟩ := ha'
    obtain ⟨qb, hqb⟩ := hb'
    refine ⟨qa * qb, fun x hx => ?_⟩
    have hbx : b * x * b⁻¹ ∈ D.comp i := D.mem_comp_conj (by rw [← D.iSup_comp]; exact hb) hx
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = D.hom i qa * (b * x * b⁻¹) * (D.hom i qa)⁻¹ := hqa _ hbx
      _ = D.hom i (qa * qb) * x * (D.hom i (qa * qb))⁻¹ := by
          rw [hqb x hx]
          simp [map_mul, mul_assoc]

omit [Fact p.Prime] in
theorem e189_mul_ne_one {K : Subgroup Y} {z t : Y} (hz : IsUniqueInvolution K z)
    (hne : conjSub t K ≠ K) : z * t ≠ 1 := by
  intro h1
  apply hne
  have : t = z⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  exact conjSub_eq_self_of_mem hz.mem

variable [Finite Y]

theorem mem_kPerp_iff_commutes (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Λ : Set (Subgroup Y)}
    (hΛ : HypOmega p f Λ) {K L : Subgroup Y} {z : Y} (hK : K ∈ Λ) (hL : L ∈ Λ)
    (hz : IsUniqueInvolution K z) : L ∈ KPerp Λ K ↔ (L = K ∨ Commutes L K) := by
  constructor
  · intro h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (AscE186.commutes_of_mem_omegaNbr hp hq hΛ hK h).symm
  · rintro (rfl | hc)
    · exact Or.inl rfl
    · by_cases hLK : L = K
      · exact Or.inl hLK
      · refine Or.inr (AscE186.mem_omegaNbr_of_le_centralizer hp hq hΛ.toMod hK hL hLK hz
          fun x hx => ?_)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc x hx z hz.mem

theorem e189_bar (hmodel : E189Model p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hbelow : CITBelowU p f n) (hcard : Nat.card Y < n)
    (hO : CFSG.Open.classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)}
    (hΛm : HypOmegaMod p f Λ) (hgen : (⨆ L ∈ Λ, L) = ⊤) (hA : ∀ L ∈ Λ, AEmpty Λ L)
    {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧ IsSylow2In R₂ K'' ∧
        Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = z * t) ∨
    (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
        ∀ w ∈ conjSub x K ⊔ M', w * (z * t) = (z * t) * w) := by
  obtain ⟨D⟩ := exists_omegaLie hbelow hΛm ⟨K, hK⟩ hO hcard
  have hΛ : HypOmega p f Λ := hΛm.toExact (D.exactMembers hp hq hΛm)
  obtain ⟨g, hg⟩ : ∃ g : Y, conjSub g K = J := by
    by_contra hnc
    have hc := thm4Below_of_citBelow hbelow hp hq Y hcard Λ hΛm hO hA K hK J hJ hnc
    exact hne (conjSub_eq_of_mem_of_commutes ht.mem hc.symm)
  have htg : t = g * z * g⁻¹ := ht.eq (hg ▸ hz.conj g)
  have hgΩ : g ∈ omegaGen Λ := by
    have : omegaGen Λ = ⊤ := hgen
    rw [this]
    exact Subgroup.mem_top g
  obtain ⟨i, F₁, hF₁, hKF⟩ := D.fundamental K hK
  have hnotA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    intro hA1
    have hKc : K = D.comp i := hKF.trans (D.map_fund_eq_comp_of_A1 i hA1 hF₁)
    apply hne
    have hJK : J ≤ K := by
      rw [← hg]
      intro x hx
      rw [mem_conjSub_iff] at hx
      have hx' : g * (g⁻¹ * x * g) * g⁻¹ ∈ D.comp i :=
        D.mem_comp_conj hgΩ (hKc ▸ hx)
      rw [hKc]
      simpa [mul_assoc] using hx'
    exact conjSub_eq_self_of_mem (hJK ht.mem)
  have hinj := D.injOn_fund i hnotA1 hF₁
  set ψ := D.hom i with hψ
  have hKperf : Group.IsPerfect ↥K := hΛm.isPerfect hK
  have hperfF : Group.IsPerfect ↥F₁ := isPerfect_of_map ψ hinj (hKF ▸ hKperf)
  have hperf : F₁ ≤ ⁅F₁, F₁⁆ := (Subgroup.isPerfect_iff.mp hperfF).ge
  obtain ⟨z₁, hz₁F, hψz₁⟩ : ∃ z₁ ∈ F₁, ψ z₁ = z := by
    have := hz.mem
    rw [hKF] at this
    obtain ⟨z₁, h1, h2⟩ := this
    exact ⟨z₁, h1, h2⟩
  have hz₁ : IsUniqueInvolution F₁ z₁ := by
    refine ⟨hz₁F, fun h1 => hz.ne_one (by rw [← hψz₁, h1, map_one]), ?_, ?_⟩
    · exact hinj _ (F₁.mul_mem hz₁F hz₁F) (by rw [map_mul, hψz₁, hz.sq])
    · intro y hy hy2
      have hψy : ψ y ∈ K := hKF ▸ Subgroup.mem_map_of_mem ψ hy
      rcases hz.unique (ψ y) hψy (by rw [← map_mul, hy2, map_one]) with h | h
      · left
        exact hinj y hy h
      · right
        have : ψ (y⁻¹ * z₁) = 1 := by rw [map_mul, map_inv, h, hψz₁, inv_mul_cancel]
        have := hinj _ (F₁.mul_mem (F₁.inv_mem hy) hz₁F) this
        exact inv_mul_eq_one.mp this
  obtain ⟨q, hq'⟩ := D.exists_model_conj i hgΩ
  have hzK : z ∈ D.comp i := by
    have : z ∈ F₁.map ψ := hKF ▸ hz.mem
    exact Subgroup.map_le_range _ _ this
  have hψt : ψ (q * z₁ * q⁻¹) = t := by
    rw [map_mul, map_mul, map_inv, hψz₁, ← hq' z hzK, ← htg]
  have hKΛ : F₁.map ψ ∈ Λ := hKF ▸ hK
  have hK' : conjSub t K ∈ Λ := hΛ.conjInvariant t K hK
  have hzK' : IsUniqueInvolution (conjSub t K) z := by
    have := hz.conj t
    rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
  have hcomm : Commutes K (conjSub t K) :=
    hΛ.commutes_of_twin hK hK' (Ne.symm hne) hz hzK'
  have hnb : ∀ L ∈ Λ, ((L = K ∨ Commutes L K) ↔
      (L = conjSub t K ∨ Commutes L (conjSub t K))) := by
    intro L hL
    rw [← mem_kPerp_iff_commutes hp hq hΛ hK hL hz,
      ← mem_kPerp_iff_commutes hp hq hΛ hK' hL hzK']
    rw [(l6_3 p f hp hq Y Λ hΛm K hK (conjSub t K) ⟨hK', z, hz, hzK'⟩).1]
  have hat : ψ z₁ * ψ (q * z₁ * q⁻¹) ≠ 1 := by
    rw [hψz₁, hψt]
    exact e189_mul_ne_one hz hne
  have := e189_component (D.exp i) (D.tag i) (D.rank i)
    (hmodel hp hq (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i) (D.admissible i) (D.exp_eq i))
    hΛ.conjInvariant ψ (D.ker_le_center i) hF₁ hinj hperf hKΛ hz₁ q
    (by rw [hψz₁, hψt]; exact hzt) hat
    (by rw [hψt, ← hKF]; exact hne) (by rw [hψt, ← hKF]; exact hcomm)
    (by rw [hψt, ← hKF]; exact hnb)
  rw [hψz₁, hψt, ← hKF] at this
  exact this

end Bar

end CFSG.ClassicalInvolution.Asc77
