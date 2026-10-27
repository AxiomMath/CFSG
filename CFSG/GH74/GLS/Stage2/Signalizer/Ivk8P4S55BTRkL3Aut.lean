module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87BadSL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Field
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Simple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkL3

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

variable {F : Type} [Field F]

theorem conj_injective :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  have := isSimpleGroup_projectiveSL3_fl3 F
  have : Nontrivial (projectiveSL 3 F) := IsSimpleGroup.toNontrivial
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).ker with h | h
  · exact h
  · exfalso
    have hc : commutator (projectiveSL 3 F) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      have hb : MulAut.conj b = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top b)
      have h1 : b * a * b⁻¹ = a := by
        simpa only [MulAut.conj_apply, MulAut.one_apply] using DFunLike.congr_fun hb a
      calc b * a = b * a * b⁻¹ * b := by group
        _ = a * b := by rw [h1]
    exact bot_ne_top (hc.symm.trans (isPerfect_projectiveSL3_fl3 F).commutator_eq_top)

theorem isElemAbelian_comap {A B : Type} [Group A] [Group B] {ψ : A →* B}
    (hψ : Function.Injective ψ) {I : Subgroup B} (hcomm : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a)
    (hsq : ∀ a ∈ I, a ^ 2 = 1) : CFSG.Open.IsElemAbelian 2 (I.comap ψ) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hψ ?_)⟩⟩, fun x hx => hψ ?_⟩
  · simp only [Subgroup.coe_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.mp a.2) _ (Subgroup.mem_comap.mp b.2)
  · rw [map_pow, map_one]
    exact hsq _ (Subgroup.mem_comap.mp hx)

theorem card_le_four_of_le_inner {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f) (e : Y ≃* projectiveSL 3 F)
    {I : Subgroup (MulAut (projectiveSL 3 F))} (hcomm : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a)
    (hsq : ∀ a ∈ I, a ^ 2 = 1)
    (hle : I ≤ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range) :
    Nat.card ↥I ≤ 4 := by
  let ψ : Y →* MulAut (projectiveSL 3 F) :=
    (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).comp e.toMonoidHom
  have hψ : Function.Injective ψ := conj_injective.comp e.injective
  have hrange : I ≤ ψ.range := by
    intro x hx
    obtain ⟨y, rfl⟩ := hle hx
    exact ⟨e.symm y, by simp [ψ]⟩
  have hcard : Nat.card ↥(I.comap ψ) = Nat.card ↥I := by
    rw [← Subgroup.card_map_of_injective hψ, Subgroup.map_comap_eq_self hrange]
  rw [← hcard]
  exact card_elemAbelian_two_le_four_of_PSL3 hp hp2 hLie _ (isElemAbelian_comap hψ hcomm hsq)

theorem card_le_eight [Finite F] {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f) (e : Y ≃* projectiveSL 3 F)
    (E : Subgroup (MulAut (projectiveSL 3 F))) (hE : IsElementaryAbelian 2 ↥E)
    (hno : ∀ x ∈ E, x ≠ 1 → ∀ (A : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 →
      x ≠ conjAut 3 F A * fieldAut 3 F σ) :
    Nat.card ↥E ≤ 8 := by
  have := hE
  have hsqE : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
  have hinn : semilinearAutGroup 3 F ⊓ E ≤
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    intro x hx
    obtain ⟨hxΓ, hxE⟩ := Subgroup.mem_inf.mp hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp hxΓ
    by_cases hσ : σ = 1
    · have hD : x ∈ linearAutGroup 3 F := by
        rw [hAσ, hσ, map_one, mul_one]
        exact conjAut_mem_linearAutGroup A
      exact CFSG.ClassicalInvolution.Q3.TA3.Q5L3.mem_inner_of_pow hD (k := 1)
        (by rw [pow_one]; exact hsqE x hxE)
    · exact (hno x hxE hx1 A σ hσ hAσ).elim
  have h4 : Nat.card ↥(semilinearAutGroup 3 F ⊓ E) ≤ 4 :=
    card_le_four_of_le_inner hp hp2 hLie e
      (fun a ha b hb => hcommE a (Subgroup.mem_inf.mp ha).2 b (Subgroup.mem_inf.mp hb).2)
      (fun a ha => hsqE a (Subgroup.mem_inf.mp ha).2) hinn
  have hrel : (semilinearAutGroup 3 F).relIndex E ≤ 2 := by
    obtain ⟨hgenTop, -⟩ := automorphism_generation (K := F) (n := 3) le_rfl
    obtain ⟨-, -, -, -, -, -, -, hidx, -⟩ := standard_outer_quotients (n := 3) (K := F)
    have h2 : (semilinearAutGroup 3 F).relIndex (standardAutGroup 3 F) ≤ 2 := hidx
    have : Finite (MulAut (projectiveSL 3 F)) := ProjectivePlane.finite_mulAut_projectiveSL 3
    rw [hgenTop] at h2
    refine (Subgroup.relIndex_le_of_le_right le_top ?_).trans h2
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have hc : Nat.card ↥((semilinearAutGroup 3 F).subgroupOf E) =
      Nat.card ↥(semilinearAutGroup 3 F ⊓ E) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective E.subtype_injective]
  have hcm := Subgroup.card_mul_index ((semilinearAutGroup 3 F).subgroupOf E)
  have hidx2 : ((semilinearAutGroup 3 F).subgroupOf E).index ≤ 2 := hrel
  rw [← hcm, hc]
  exact (Nat.mul_le_mul h4 hidx2).trans (by norm_num)

theorem false_of_fixed_kindFactorAll {k : Kind} {Y : Type} [Group Y] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (e : Y ≃* projectiveSL 3 F) {x : MulAut Y} (hx : x * x = 1) (A : GL (Fin 3) F)
    (σ : F ≃+* F) (hσ : σ ≠ 1) (hxeq : MulAut.congr e x = conjAut 3 F A * fieldAut 3 F σ)
    (hall : ∀ (Z : Type) [Group Z] [IsSimpleGroup Z], ¬ Group.IsSolvable Z →
      ∀ Q : Subgroup Y, (∀ y ∈ Q, x y = y) → IsSection Z ↥Q → KindFactorAll k Z) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hα : MulAut.congr e x * MulAut.congr e x = 1 := by rw [← map_mul, hx, map_one]
  obtain ⟨F0, _, _, _, hodd0, h30, Q, -, hQfix, c, hc⟩ :=
    fl3_field_section hp hp2 hf hcard (MulAut.congr e x) hα A σ hσ hxeq
  have hfix : ∀ y ∈ Q.map e.symm.toMonoidHom, x y = y := by
    rintro _ ⟨q, hq, rfl⟩
    have h1 : e (x (e.symm q)) = q := hQfix q hq
    show x (e.symm q) = e.symm q
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact h1
  have hsecQ : IsSection (projectiveSL 3 F0) ↥Q :=
    ⟨⊤, c.comp (⊤ : Subgroup ↥Q).subtype, fun v => by
      obtain ⟨w, rfl⟩ := hc v
      exact ⟨⟨w, Subgroup.mem_top w⟩, rfl⟩⟩
  have : IsSimpleGroup (projectiveSL 3 F0) := isSimpleGroup_projectiveSL3_fl3 F0
  have : Group.IsPerfect (projectiveSL 3 F0) := isPerfect_projectiveSL3_fl3 F0
  have : Nontrivial (projectiveSL 3 F0) := IsSimpleGroup.toNontrivial
  exact not_kindFactorAll hp2 (involved_qdSL_projectiveSL3 (p := p))
    (not_card_dvd_factorial_projectiveSL3 hodd0 h30)
    (hall _ (Group.IsPerfect.not_isSolvable _) _ hfix
      (IsSection.of_equiv (Q.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
        hsecQ))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkL3
