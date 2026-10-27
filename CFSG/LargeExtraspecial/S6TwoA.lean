module

public import CFSG.LargeExtraspecial.S2SpLevi
public import CFSG.LargeExtraspecial.S4Lin
public import CFSG.LargeExtraspecial.S4SpU
public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by
  rcases zmod2_eq_zero_or_eq_one x with rfl | rfl <;> rfl

theorem exists_hyperbolic_complement (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {a b : V} (hab : β a b = 1) :
    ∃ u₁ u₂ : V, β a u₁ = 0 ∧ β b u₁ = 0 ∧ β a u₂ = 0 ∧ β b u₂ = 0 ∧ β u₁ u₂ = 1 := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ S2.spPerp β ⊥ = ⊥ := bot_inf_eq _
  have ha : a ∈ S2.spPerp β ⊥ := by rw [S2.spPerp_bot]; exact Submodule.mem_top
  have hb : b ∈ S2.spPerp β ⊥ := by rw [S2.spPerp_bot]; exact Submodule.mem_top
  have hK := S2.sup_span_pair_inf_spPerp_eq_bot hβ hF ha hb hab
  have hd := S2.finrank_spPerp_sup_span_pair hβ hnd hF ha hb hab
  rw [S2.spPerp_bot, finrank_top, h4] at hd
  have hne : S2.spPerp β (⊥ ⊔ Submodule.span (ZMod 2) {a, b}) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hd
    omega
  obtain ⟨u₁, hu₁, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u₂, hu₂, h12⟩ := S2.sp_exists_partner hβ hnd hK hu₁ hu₁0
  obtain ⟨-, h1a, h1b⟩ := S2.mem_spPerp_sup_span_pair.mp hu₁
  obtain ⟨-, h2a, h2b⟩ := S2.mem_spPerp_sup_span_pair.mp hu₂
  exact ⟨u₁, u₂, h1a, h1b, h2a, h2b, h12⟩

section Basis

variable (hβ : β.IsAlt) (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) {a b u₁ u₂ : V}
  (hab : β a b = 1) (h1a : β a u₁ = 0) (h1b : β b u₁ = 0) (h2a : β a u₂ = 0)
  (h2b : β b u₂ = 0) (h12 : β u₁ u₂ = 1)
include hβ hab h1a h1b h2a h2b h12

omit [FiniteDimensional (ZMod 2) V] in
theorem gram_values :
    β a a = 0 ∧ β b b = 0 ∧ β u₁ u₁ = 0 ∧ β u₂ u₂ = 0 ∧ β b a = 1 ∧ β u₂ u₁ = 1 ∧
      β u₁ a = 0 ∧ β u₁ b = 0 ∧ β u₂ a = 0 ∧ β u₂ b = 0 := by
  refine ⟨hβ.self_eq_zero a, hβ.self_eq_zero b, hβ.self_eq_zero u₁, hβ.self_eq_zero u₂, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;> rw [isAlt_symm hβ] <;> assumption

include h4 in
theorem span_four_eq_top : Submodule.span (ZMod 2) (Set.range ![a, b, u₁, u₂]) = ⊤ := by
  obtain ⟨haa, hbb, h11, h22, hba, h21, h1a', h1b', h2a', h2b'⟩ :=
    gram_values hβ hab h1a h1b h2a h2b h12
  refine LinearIndependent.span_eq_top_of_card_eq_finrank' ?_ (by simp [h4])
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : c 0 • a + c 1 • b + c 2 • u₁ + c 3 • u₂ = 0 := by
    simpa [Fin.sum_univ_four] using hc
  have e1 := congrArg (fun v => β v b) hc'
  have e2 := congrArg (fun v => β v a) hc'
  have e3 := congrArg (fun v => β v u₂) hc'
  have e4 := congrArg (fun v => β v u₁) hc'
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_zero,
    LinearMap.zero_apply] at e1 e2 e3 e4
  rw [hab, hbb, h1b', h2b', mul_one, mul_zero, mul_zero, mul_zero, add_zero, add_zero,
    add_zero] at e1
  rw [haa, hba, h1a', h2a', mul_one, mul_zero, mul_zero, mul_zero, zero_add, add_zero,
    add_zero] at e2
  rw [h2a, h2b, h12, h22, mul_one, mul_zero, mul_zero, mul_zero, zero_add, zero_add,
    add_zero] at e3
  rw [h1a, h1b, h11, h21, mul_one, mul_zero, mul_zero, mul_zero, zero_add, zero_add,
    zero_add] at e4
  intro i
  fin_cases i
  · exact e1
  · exact e2
  · exact e3
  · exact e4

include hnd h4 in
theorem eq_decomp (x : V) :
    x = β x b • a + β a x • b + β x u₂ • u₁ + β u₁ x • u₂ := by
  obtain ⟨haa, hbb, h11, h22, hba, h21, h1a', h1b', h2a', h2b'⟩ :=
    gram_values hβ hab h1a h1b h2a h2b h12
  set r := x - (β x b • a + β a x • b + β x u₂ • u₁ + β u₁ x • u₂) with hr
  have hsymm : ∀ u v : V, β u v = β v u := isAlt_symm hβ
  have hexp : ∀ w : V, β r w = β x w - (β x b * β a w + β a x * β b w + β x u₂ * β u₁ w +
      β u₁ x * β u₂ w) := fun w => by
    simp only [hr, map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
  have hra : β r a = 0 := by
    rw [hexp, haa, hba, h1a', h2a', hsymm x a]
    ring
  have hrb : β r b = 0 := by
    rw [hexp, hab, hbb, h1b', h2b']
    ring
  have hr1 : β r u₁ = 0 := by
    rw [hexp, h1a, h1b, h11, h21, hsymm x u₁]
    ring
  have hr2 : β r u₂ = 0 := by
    rw [hexp, h2a, h2b, h12, h22]
    ring
  have hle : Set.range ![a, b, u₁, u₂] ⊆ LinearMap.ker (β r) := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hra
    · exact hrb
    · exact hr1
    · exact hr2
  have htop := Submodule.span_le.mpr hle
  rw [span_four_eq_top hβ h4 hab h1a h1b h2a h2b h12, top_le_iff] at htop
  have hr0 : r = 0 := hnd.1 r fun y => by
    have : y ∈ LinearMap.ker (β r) := htop ▸ Submodule.mem_top
    exact this
  rw [hr] at hr0
  exact (sub_eq_zero.mp hr0)

end Basis

noncomputable def qMinus (β : LinearMap.BilinForm (ZMod 2) V) (a b u₁ u₂ : V) :
    QuadraticForm (ZMod 2) V :=
  linMulLin (β.flip b) (β a) + linMulLin (β.flip u₂) (β u₁) +
    linMulLin (β.flip u₂) (β.flip u₂) + linMulLin (β u₁) (β u₁)

omit [FiniteDimensional (ZMod 2) V] in
theorem qMinus_apply (a b u₁ u₂ v : V) :
    qMinus β a b u₁ u₂ v = β v b * β a v + β v u₂ * β u₁ v + β v u₂ * β v u₂ +
      β u₁ v * β u₁ v := by
  simp [qMinus, linMulLin_apply]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_qMinus_eq (a b u₁ u₂ x y : V) :
    polar (qMinus β a b u₁ u₂) x y =
      β x b * β a y + β y b * β a x + β x u₂ * β u₁ y + β y u₂ * β u₁ x := by
  simp only [polar, qMinus_apply, map_add, LinearMap.add_apply]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (β x u₂ * β y u₂ + β u₁ x * β u₁ y) * h2

omit [FiniteDimensional (ZMod 2) V] in
theorem qMinus_a (hβ : β.IsAlt) {a b u₁ u₂ : V} (h1a : β a u₁ = 0) (h2a : β a u₂ = 0) :
    qMinus β a b u₁ u₂ a = 0 := by
  rw [qMinus_apply, hβ.self_eq_zero a, h2a, isAlt_symm hβ u₁ a, h1a]
  ring

omit [FiniteDimensional (ZMod 2) V] in
theorem qMinus_b (hβ : β.IsAlt) {a b u₁ u₂ : V} (h1b : β b u₁ = 0) (h2b : β b u₂ = 0) :
    qMinus β a b u₁ u₂ b = 0 := by
  rw [qMinus_apply, hβ.self_eq_zero b, h2b, isAlt_symm hβ u₁ b, h1b]
  ring

omit [FiniteDimensional (ZMod 2) V] in
theorem qMinus_u₁ (hβ : β.IsAlt) {a b u₁ u₂ : V} (h1b : β b u₁ = 0) (h12 : β u₁ u₂ = 1) :
    qMinus β a b u₁ u₂ u₁ = 1 := by
  rw [qMinus_apply, hβ.self_eq_zero u₁, isAlt_symm hβ u₁ b, h1b, h12]
  ring

theorem zmod2_aniso (s r : ZMod 2) : s * r + s * s + r * r = 0 ↔ s = 0 ∧ r = 0 := by
  rcases zmod2_eq_zero_or_eq_one s with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one r with rfl | rfl <;> decide

section Form

variable (hβ : β.IsAlt) (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) {a b u₁ u₂ : V}
  (hab : β a b = 1) (h1a : β a u₁ = 0) (h1b : β b u₁ = 0) (h2a : β a u₂ = 0)
  (h2b : β b u₂ = 0) (h12 : β u₁ u₂ = 1)
include hβ hab h1a h1b h2a h2b h12

include hnd h4 in
theorem polar_qMinus (x y : V) : polar (qMinus β a b u₁ u₂) x y = β x y := by
  have hsymm : ∀ u v : V, β u v = β v u := isAlt_symm hβ
  rw [polar_qMinus_eq]
  conv_rhs => rw [eq_decomp hβ hnd h4 hab h1a h1b h2a h2b h12 x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm b y, hsymm u₂ y]
  ring

include hnd h4 in
theorem polarBilin_qMinus : (qMinus β a b u₁ u₂).polarBilin = β := by
  ext x y
  rw [polarBilin_apply_apply, polar_qMinus hβ hnd h4 hab h1a h1b h2a h2b h12]

include hnd h4 in
theorem qMinus_nondegenerate : (qMinus β a b u₁ u₂).polarBilin.Nondegenerate := by
  rw [polarBilin_qMinus hβ hnd h4 hab h1a h1b h2a h2b h12]
  exact hnd

include hnd h4 in
theorem qMinus_eq_zero_iff_a {d : V} (hd : β a d = 0) :
    qMinus β a b u₁ u₂ d = 0 ↔ d ∈ (ZMod 2) ∙ a := by
  obtain ⟨haa, hbb, h11, h22, hba, h21, h1a', h1b', h2a', h2b'⟩ :=
    gram_values hβ hab h1a h1b h2a h2b h12
  rw [qMinus_apply, hd, mul_zero, zero_add, zmod2_aniso, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hs, hr⟩
    refine ⟨β d b, ?_⟩
    conv_rhs => rw [eq_decomp hβ hnd h4 hab h1a h1b h2a h2b h12 d]
    rw [hd, hs, hr, zero_smul, zero_smul, zero_smul, add_zero, add_zero, add_zero]
  · rintro ⟨c, rfl⟩
    simp [h2a, h1a']

include hnd h4 in
theorem qMinus_eq_zero_iff_b {d : V} (hd : β b d = 0) :
    qMinus β a b u₁ u₂ d = 0 ↔ d ∈ (ZMod 2) ∙ b := by
  obtain ⟨haa, hbb, h11, h22, hba, h21, h1a', h1b', h2a', h2b'⟩ :=
    gram_values hβ hab h1a h1b h2a h2b h12
  have hd' : β d b = 0 := by rw [isAlt_symm hβ]; exact hd
  rw [qMinus_apply, hd', zero_mul, zero_add, zmod2_aniso, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hs, hr⟩
    refine ⟨β a d, ?_⟩
    conv_rhs => rw [eq_decomp hβ hnd h4 hab h1a h1b h2a h2b h12 d]
    rw [hd', hs, hr, zero_smul, zero_smul, zero_smul, zero_add, add_zero, add_zero]
  · rintro ⟨c, rfl⟩
    simp [h2b, h1b']

end Form

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_eq_spRho {Q : QuadraticForm (ZMod 2) V} (hQ : ∀ x y, polar Q x y = β x y)
    (hβ : β.IsAlt) {c u : V} (hc : Q c = 0) (hcu : β c u = 0) :
    eichler Q c u = spRho hβ hcu (Q u) := by
  ext x
  rw [eichler_apply_zmod2 hc (by rw [hQ]; exact hcu), spRho_apply, hQ, hQ]

theorem eq_pointRadical_of_index_two (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {Q : QuadraticForm (ZMod 2) V} (hQ : ∀ x y, polar Q x y = β x y)
    (hQnd : Q.polarBilin.Nondegenerate) {c : V} (hc0 : c ≠ 0) (hc : Q c = 0)
    (hQc : ∀ d, β c d = 0 → (Q d = 0 ↔ d ∈ (ZMod 2) ∙ c))
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEU : E ≤ spPointRadical β c)
    (hcard : Nat.card (spPointRadical β c) = 2 * Nat.card E)
    (hτ : spTransvection β hβ c ∉ E)
    (hno : ∀ d (hd : β c d = 0), d ∉ (ZMod 2) ∙ c → spRho hβ hd 0 ∉ E) :
    E = pointRadical Q c := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  set U := spPointRadical β c with hU
  have hidx : (E.subgroupOf U).index = 2 := by
    have h1 := (E.subgroupOf U).card_mul_index
    have h2 : Nat.card (E.subgroupOf U) = Nat.card E := by
      rw [← card_map_of_injective U.subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr hEU]
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    have := Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm 2 _))
    exact this
  have hτU : spTransvection β hβ c ∈ U := spTransvection_mem_U hβ c
  have hrho1 : ∀ d (hd : β c d = 0), d ∉ (ZMod 2) ∙ c → spRho hβ hd 1 ∈ E := by
    intro d hd hdc
    have hmul := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := ⟨spRho hβ hd 0, spRho_mem_spPointRadical hβ hd 0⟩) (b := ⟨_, hτU⟩)).mpr
    have : spRho hβ hd 0 * spTransvection β hβ c ∈ E := by
      have h := hmul (iff_of_false (fun h => hno d hd hdc h) (fun h => hτ h))
      exact h
    rw [spRho_one_eq]
    exact this
  apply le_antisymm
  · intro e he
    obtain ⟨d, hd, l, rfl⟩ := exists_eq_spRho hβ hnd hc0 (hEU he)
    by_cases hdc : d ∈ (ZMod 2) ∙ c
    ·
      have h0 : β c 0 = 0 := map_zero _
      have he0 : spRho hβ hd l = spRho hβ h0 l := by
        rcases mem_span_cl_iff.mp hdc with rfl | rfl
        · rfl
        · have := spRho_add_self hβ h0 l (by rw [zero_add]; exact hd)
          simpa using this
      rw [he0] at he ⊢
      rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
      · have h1 : spRho hβ h0 0 = 1 := by
          ext x
          simp [spRho_apply]
        rw [h1]
        exact one_mem _
      · rw [spRho_zero_one] at he
        exact absurd he hτ
    · rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
      · exact absurd he (hno d hd hdc)
      · have hQd : Q d = 1 := zmod2_eq_one_of_ne_zero fun h => hdc ((hQc d hd).mp h)
        rw [← hQd, ← eichler_eq_spRho hQ hβ hc hd]
        exact eichler_mem_pointRadical hc (by rw [hQ]; exact hd)
  · intro e he
    obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQnd hc0 hc).mp he
    have hcu : β c u = 0 := by rw [← hQ]; exact hu
    rw [eichler_eq_spRho hQ hβ hc hcu]
    by_cases huc : u ∈ (ZMod 2) ∙ c
    · have hQu : Q u = 0 := (hQc u hcu).mpr huc
      rw [hQu]
      have h0 : β c 0 = 0 := map_zero _
      have he0 : spRho hβ hcu 0 = spRho hβ h0 0 := by
        rcases mem_span_cl_iff.mp huc with rfl | rfl
        · rfl
        · have := spRho_add_self hβ h0 0 (by rw [zero_add]; exact hcu)
          simpa using this
      have h1 : spRho hβ h0 0 = 1 := by
        ext x
        simp [spRho_apply]
      rw [he0, h1]
      exact one_mem _
    · have hQu : Q u = 1 := zmod2_eq_one_of_ne_zero fun h => huc ((hQc u hcu).mp h)
      rw [hQu]
      exact hrho1 u hcu huc

end CFSG.LargeExtraspecial.S6
