module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87InvMax
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHG2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResG2
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)

open scoped commutatorElement

@[expose] def FixOddFree {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  ∀ N : Subgroup Y, N ≤ fixSub α → (∀ c ∈ fixSub α, ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
    Odd (Nat.card ↥N) → N = ⊥

theorem fixOddFree_of_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (α : MulAut Y)
    (h : FixOddFree (MulAut.congr e α)) : FixOddFree α := by
  intro N hN hNn hNodd
  have hfix : ∀ y : Y, y ∈ fixSub α ↔ e y ∈ fixSub (MulAut.congr e α) := by
    intro y
    rw [mem_fixSub, mem_fixSub]
    show α y = y ↔ e (α (e.symm (e y))) = e y
    simp
  have h1 : N.map e.toMonoidHom ≤ fixSub (MulAut.congr e α) := by
    rintro _ ⟨n, hn, rfl⟩
    exact (hfix n).1 (hN hn)
  have h2 : ∀ c ∈ fixSub (MulAut.congr e α), ∀ n ∈ N.map e.toMonoidHom,
      c * n * c⁻¹ ∈ N.map e.toMonoidHom := by
    intro c hc n hn
    obtain ⟨n', hn', rfl⟩ := hn
    have hc' : e.symm c ∈ fixSub α := by
      rw [hfix]
      simpa using hc
    refine ⟨e.symm c * n' * (e.symm c)⁻¹, hNn _ hc' _ hn', ?_⟩
    simp
  have h3 : Odd (Nat.card ↥(N.map e.toMonoidHom)) := by
    rw [← Nat.card_congr (N.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
    exact hNodd
  have h4 := h _ h1 h2 h3
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp h4

theorem eq_bot_of_normal_odd_of_derived_simple {Γ : Type} [Group Γ] [Finite Γ] (hZ : center Γ = ⊥)
    (hs : IsSimpleGroup ↥(commutator Γ)) (heven : Even (Nat.card ↥(commutator Γ)))
    (hidx : (commutator Γ).index = 3) {N : Subgroup Γ} (hN : N.Normal) (hodd : Odd (Nat.card ↥N)) :
    N = ⊥ := by
  classical
  set D : Subgroup Γ := commutator Γ with hD
  have hDn : D.Normal := inferInstance
  have hND : N ⊓ D = ⊥ := by
    have hnorm : ((N ⊓ D).subgroupOf D).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        refine ⟨?_, ?_⟩
        · have h2 : x * y * x⁻¹ ∈ N := hN.conj_mem y hy.1 x
          exact h2
        · exact D.mul_mem (D.mul_mem hx hy.2) (D.inv_mem hx)
      · intro hy
        refine ⟨?_, ?_⟩
        · have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ N := by
            have := hN.conj_mem _ hy.1 x⁻¹
            simpa [mul_assoc] using this
          simpa [mul_assoc] using h2
        · have h2 := D.mul_mem (D.mul_mem (D.inv_mem hx) hy.2) hx
          simpa [mul_assoc] using h2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ D).subgroupOf D) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx.2⟩ : ↥D) ∈ (N ⊓ D).subgroupOf D := hx
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    · exfalso
      have hDN : D ≤ N := by
        intro x hx
        have h1 : (⟨x, hx⟩ : ↥D) ∈ (N ⊓ D).subgroupOf D := by rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp h1).1
      have hdvd : Nat.card ↥D ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hDN
      have h2 : 2 ∣ Nat.card ↥N := (even_iff_two_dvd.mp heven).trans hdvd
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hcent : ∀ n ∈ N, ∀ d ∈ D, n * d = d * n := by
    intro n hn d hd
    have hmem : n * d * n⁻¹ * d⁻¹ ∈ N ⊓ D := by
      refine ⟨?_, ?_⟩
      · have h2 : n * (d * n⁻¹ * d⁻¹) ∈ N := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) d)
        simpa [mul_assoc] using h2
      · have h2 : (n * d * n⁻¹) * d⁻¹ ∈ D := D.mul_mem (hDn.conj_mem d hd n) (D.inv_mem hd)
        simpa using h2
    rw [hND, Subgroup.mem_bot] at hmem
    calc n * d = (n * d * n⁻¹ * d⁻¹) * (d * n) := by group
      _ = d * n := by rw [hmem, one_mul]
  have hdvd3 : Nat.card ↥N ∣ 3 := by
    have hker : ((QuotientGroup.mk' D).comp N.subtype).ker = ⊥ := by
      ext n
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_bot]
      constructor
      · intro hn
        have h1 : (n : Γ) ∈ N ⊓ D := ⟨n.2, hn⟩
        rw [hND, Subgroup.mem_bot] at h1
        exact Subtype.ext h1
      · intro hn
        rw [hn]
        simp
    have hinj : Function.Injective ((QuotientGroup.mk' D).comp N.subtype) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have h1 : Nat.card ↥N ∣ Nat.card (Γ ⧸ D) := Subgroup.card_dvd_of_injective _ hinj
    have h2 : Nat.card (Γ ⧸ D) = 3 := hidx
    rwa [h2] at h1
  by_contra hne
  have hN1 : Nat.card ↥N ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hN3 : Nat.card ↥N = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact absurd h hN1
    · exact h
  have hNcyc : IsCyclic ↥N := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hN3
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have := comm_of_isCyclic_group hNcyc ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hsup : N ⊔ D = ⊤ := by
    have hND' : ¬ N ≤ D := by
      intro hle
      have h1 : N ≤ N ⊓ D := le_inf le_rfl hle
      rw [hND] at h1
      exact hne (le_bot_iff.mp h1)
    have hlt : D < N ⊔ D :=
      lt_of_le_of_ne le_sup_right (fun h => hND' (by rw [h]; exact le_sup_left))
    have h1 : (N ⊔ D).index ∣ D.index := Subgroup.index_dvd_of_le le_sup_right
    rw [hidx] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact Subgroup.index_eq_one.mp h
    · exfalso
      have h2 : D.relIndex (N ⊔ D) * (N ⊔ D).index = D.index :=
        Subgroup.relIndex_mul_index le_sup_right
      rw [h, hidx] at h2
      have h3 : D.relIndex (N ⊔ D) = 1 := by omega
      exact absurd (Subgroup.relIndex_eq_one.mp h3) (not_le_of_gt hlt)
  have hcentral : ∀ n ∈ N, ∀ g : Γ, n * g = g * n := by
    intro n hn g
    have hg : g ∈ N ⊔ D := by rw [hsup]; exact Subgroup.mem_top g
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hNcomm n hn y hy
      · exact hcent n hn y hy
    | one => simp
    | mul y₁ y₂ _ _ h₁ h₂ =>
      calc n * (y₁ * y₂) = (n * y₁) * y₂ := by group
        _ = (y₁ * n) * y₂ := by rw [h₁]
        _ = y₁ * (n * y₂) := by group
        _ = y₁ * (y₂ * n) := by rw [h₂]
        _ = (y₁ * y₂) * n := by group
    | inv y _ h₁ =>
      calc n * y⁻¹ = y⁻¹ * (y * n) * y⁻¹ := by group
        _ = y⁻¹ * (n * y) * y⁻¹ := by rw [h₁]
        _ = y⁻¹ * n := by group
  have hmem : ∀ n ∈ N, n ∈ center Γ := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hcentral n hn g).symm
  apply hne
  rw [eq_bot_iff]
  intro n hn
  have := hmem n hn
  rw [hZ] at this
  exact this

@[expose] def InvOddCore (Y : Type) [Group Y] : Prop :=
  ∀ g : Y, g * g = 1 → g ≠ 1 → ∀ N : Subgroup Y, N ≤ centralizer ({g} : Set Y) →
    (∀ c ∈ centralizer ({g} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card ↥N) → N = ⊥

theorem invOddCore_of_equiv {Y Γ : Type} [Group Y] [Group Γ] (ψ : Y ≃* Γ) (h : InvOddCore Γ) :
    InvOddCore Y := by
  intro g hg2 hg1 N hN hNn hNodd
  have hψ2 : ψ g * ψ g = 1 := by rw [← map_mul, hg2, map_one]
  have hψ1 : ψ g ≠ 1 := fun h1 => hg1 (ψ.injective (by rw [h1, map_one]))
  have hmap : (centralizer ({g} : Set Y)).map ψ.toMonoidHom = centralizer ({ψ g} : Set Γ) :=
    CFSG.GH74.GLS.IVK.GHInv.map_centralizer_singleton' ψ g
  have h1 : N.map ψ.toMonoidHom ≤ centralizer ({ψ g} : Set Γ) := by
    rw [← hmap]
    exact Subgroup.map_mono hN
  have h2 : ∀ c ∈ centralizer ({ψ g} : Set Γ), ∀ n ∈ N.map ψ.toMonoidHom,
      c * n * c⁻¹ ∈ N.map ψ.toMonoidHom := by
    intro c hc n hn
    rw [← hmap] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨c' * n' * c'⁻¹, hNn c' hc' n' hn', by simp⟩
  have h3 : Odd (Nat.card ↥(N.map ψ.toMonoidHom)) := by
    rw [← Nat.card_congr (N.equivMapOfInjective ψ.toMonoidHom ψ.injective).toEquiv]
    exact hNodd
  exact (Subgroup.map_eq_bot_iff_of_injective N ψ.injective).mp (h (ψ g) hψ2 hψ1 _ h1 h2 h3)

theorem fixOddFree_of_inner {Y : Type} [Group Y] (hZ : center Y = ⊥) (hO : InvOddCore Y)
    {α : MulAut Y} (hin : α ∈ (MulAut.conj : Y →* MulAut Y).range) (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : FixOddFree α := by
  obtain ⟨g, rfl⟩ := hin
  have hgg : g * g = 1 := by
    have hmem : g * g ∈ center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun σ : MulAut Y => σ y) hα2
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = (g * g) * y := by group
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hg1 : g ≠ 1 := fun h1 => hα1 (by rw [h1, map_one])
  have hfix : fixSub (MulAut.conj g) = centralizer ({g} : Set Y) := by
    ext s
    rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulAut.conj_apply]
    constructor
    · intro h1
      calc s * g = (g * s * g⁻¹) * g := by rw [h1]
        _ = g * s := by group
    · intro h1
      calc g * s * g⁻¹ = (s * g) * g⁻¹ := by rw [← h1]
        _ = s := by group
  intro N hN hNn hNodd
  rw [hfix] at hN hNn
  exact hO g hgg hg1 N hN hNn hNodd

section Certs


theorem equiv_modelUniv_g2 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : 3 ≤ p ^ f) (hY : LieModel Y .G2 0 p f) :
    Nonempty (Y ≃* (modelUniv .G2 0 p f hp).K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hYq : LieModel (AdjointQuotient .G2 (GaloisField p f)) .G2 0 p f :=
    CFSG.Timmesfeld.lieModel_G2_quotient hp hf hq hcard
  obtain ⟨E⟩ := Upgrade.lieModel_unique hp2 (by trivial) hY hYq
  exact ⟨E.trans ((QuotientGroup.quotientMulEquivOfEq
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)⟩

theorem fixed_oddFree_exceptional_zero {F : Type} [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    (hK : Nat.card F = 3 ^ (2 * 0 + 1)) (g : adjointGroup ReeTag.G2.tag F)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut F 0) ^ 2 = 1) :
    FixOddFree (MulAut.conj g * ReeTag.G2.finiteReeAut F 0) := by
  intro N hN hNn hNodd
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components 0 F hK g hα
  obtain ⟨-, ⟨e, -⟩, -, -⟩ := CFSG.LieType.Chevalley.fixed_centralizer_of_conj_eq hψ
  have hmap : ((ReeTag.G2.finiteReeAut F 0).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup ReeTag.G2.tag F).subtype = ReeTag.G2.reeGamma F 0 := rfl
  let Ψ : ↥(fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut F 0)) ≃* ↥(ReeTag.G2.reeGamma F 0) :=
    e.trans ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap))
  have hZ : Subgroup.center ↥(ReeTag.G2.reeGamma F 0) = ⊥ :=
    ReeTag.center_reeGamma_G2_eq_bot (a := 0) hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max
    (fun w : WeylGroup ReeTag.G2.tag => (coxeterSystem ReeTag.G2.tag).length w)
  obtain ⟨hs, -, -, -, hzero, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 F hK
  obtain ⟨-, h504, hidx⟩ := hzero rfl w₀ hw₀
  have heven : Even (Nat.card ↥(commutator ↥(ReeTag.G2.reeGamma F 0))) := by
    rw [h504]
    decide
  set C : Subgroup (adjointGroup ReeTag.G2.tag F) :=
    fixSub (MulAut.conj g * ReeTag.G2.finiteReeAut F 0) with hC
  let Nc : Subgroup ↥C := N.subgroupOf C
  have hNcn : Nc.Normal := by
    refine ⟨fun n hn c => ?_⟩
    have h1 : (n : adjointGroup ReeTag.G2.tag F) ∈ N := hn
    have := hNn (c : adjointGroup ReeTag.G2.tag F) c.2 _ h1
    exact this
  have hN'n : (Nc.map Ψ.toMonoidHom).Normal := hNcn.map Ψ.toMonoidHom Ψ.surjective
  have hodd' : Odd (Nat.card ↥(Nc.map Ψ.toMonoidHom)) := by
    rw [← Nat.card_congr (Nc.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv]
    exact hNodd
  have hbot := eq_bot_of_normal_odd_of_derived_simple hZ hs heven hidx hN'n hodd'
  rw [eq_bot_iff]
  intro n hn
  have h1 : (⟨n, hN hn⟩ : ↥C) ∈ Nc := hn
  have h2 : Ψ ⟨n, hN hn⟩ ∈ Nc.map Ψ.toMonoidHom := ⟨_, h1, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h2
  have h3 : (⟨n, hN hn⟩ : ↥C) = 1 := Ψ.injective (by rw [h2, map_one])
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h3)

theorem g2_three_outer_fixOddFree {F : Type} [Field F] [Finite F] (hK : Nat.card F = 3)
    {α : MulAut (adjointGroup ReeTag.G2.tag F)} (hα : α ^ 2 = 1)
    (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range) : FixOddFree α := by
  have hK1 : Nat.card F = 3 ^ 1 := by simpa using hK
  have hchar : CharP F ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl hK1
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
      (f := 1) le_rfl hK1 hα with
    ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
  · exact absurd (ivk93res_inner_of_diag hαg) hnot
  · exfalso
    have h3 : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
    have h9 : 3 * 3 ≤ 3 ^ e * 3 ^ e := Nat.mul_le_mul h3 h3
    rw [hKe, sq] at hK
    omega
  · have hb : b = 0 := by omega
    subst hb
    exact fixed_oddFree_exceptional_zero (by simpa using hK) g hα

theorem g2_three_fixOddFree {Y : Type} [Group Y] [Finite Y] (hm : LieModel Y .G2 0 3 1) (α : MulAut Y)
    (hα2 : α * α = 1) (hα1 : α ≠ 1) : FixOddFree α := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .G2 0 3 1 := ⟨hp, le_rfl, rfl, le_rfl⟩
  by_cases hin : α ∈ (MulAut.conj : Y →* MulAut Y).range
  · obtain ⟨ψ⟩ := equiv_modelUniv_g2 hp (by norm_num) le_rfl (by norm_num) hm
    have hZ : center Y = ⊥ := center_eq_bot_of_mulEquiv_target ψ
      (RouteD.G2D4.center_modelUniv_g2d4_eq_bot (by norm_num) (Or.inl rfl) 0 le_rfl)
    have hO : InvOddCore Y :=
      invOddCore_of_equiv ψ fun u hu2 hu1 N hN hNn hNodd =>
        Asc77.thm5IH_g2_oddCoreTrivial (by norm_num) hadm u hu2 hu1 N hN hNn hNodd
    exact fixOddFree_of_inner hZ hO hin hα2 hα1
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hm
    have hF3 : Nat.card F = 3 := by simpa using hcard
    refine fixOddFree_of_equiv e α ?_
    have hα'2 : (MulAut.congr e α) ^ 2 = 1 := by rw [sq, ← map_mul, hα2, map_one]
    have hnot : MulAut.congr e α ∉ (MulAut.conj : Ivk47ab.G2g F →* MulAut (Ivk47ab.G2g F)).range := by
      rintro ⟨g', hg'⟩
      apply hin
      refine ⟨e.symm g', ?_⟩
      ext y
      have h1 : (MulAut.congr e α) (e y) = g' * e y * g'⁻¹ := by
        have := congrArg (fun σ : MulAut (Ivk47ab.G2g F) => σ (e y)) hg'
        simpa [MulAut.conj_apply] using this.symm
      have h2 : α y = e.symm ((MulAut.congr e α) (e y)) := by
        show α y = e.symm (e (α (e.symm (e y))))
        simp
      rw [MulAut.conj_apply, h2, h1]
      simp [map_mul, map_inv]
    exact g2_three_outer_fixOddFree hF3 hα'2 hnot

end Certs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
