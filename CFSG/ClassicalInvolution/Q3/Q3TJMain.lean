module

public import CFSG.ClassicalInvolution.Q3.Q3TJInner
public import CFSG.ClassicalInvolution.Q3.Q3TJStmt
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification
open scoped MatrixGroups

variable {X : Type} [Group X]

theorem exists_eq_top_of_commute {ι : Type*} (hX : CFSG.Open.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) (R : ι → Subgroup X)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ R i, ∀ y ∈ R j, x * y = y * x)
    (hgen : ⨆ i, R i = ⊤) : ∃ i, R i = ⊤ := by
  by_contra hne'
  have hne : ∀ i, R i ≠ ⊤ := fun i h => hne' ⟨i, h⟩
  have hbot : ∀ i, R i = ⊥ := by
    intro i
    have hN : (R i).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
      refine iSup_le fun j => ?_
      by_cases hij : j = i
      · subst hij
        exact Subgroup.le_normalizer
      · intro y hy
        have h := hcomm i j (Ne.symm hij)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have h3 : y * x * y⁻¹ = x := by
            rw [← h x hx y hy]
            group
          rw [h3]
          exact hx
        · intro hx
          have h2 : (y * x * y⁻¹) * y⁻¹ = y⁻¹ * (y * x * y⁻¹) := h _ hx _ ((R j).inv_mem hy)
          have h3 : x = y * x * y⁻¹ := by
            calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
              _ = (y * x * y⁻¹) * y⁻¹ * y := by rw [← h2]
              _ = y * x * y⁻¹ := by group
          rw [h3]
          exact hx
    rcases normal_le_center_or_eq_top_qs hX hN with h | h
    · rw [hZ] at h
      exact le_bot_iff.mp h
    · exact absurd h (hne i)
  have htop : (⊤ : Subgroup X) = ⊥ := by
    rw [← hgen]
    exact iSup_eq_bot.mpr hbot
  have : Nontrivial (X ⧸ Subgroup.center X) := hX.2.toNontrivial
  have : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  exact top_ne_bot htop

theorem exists_eq_conj_of_component (hSt : SteinbergOddAut3) (hD4 : D4OddAutInner3)
    (h3D4 : TrialityD4OddAutInner3) [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) {c : CompData} (hc : c.Valid) (f : c.G →* X)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center c.G) {z : X}
    {K : Subgroup X} (hKz : IsClassicalMember3 K z) (α : MulAut X) (hodd : Odd (orderOf α))
    (hfix : ∀ c ∈ Subgroup.centralizer ({z} : Set X),
      c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X))) :
    ∃ g : X, α = MulAut.conj g := by
  rcases hc with ⟨t, n, ht, hadm, rfl⟩ | rfl | rfl
  · rcases hSt t n ht hadm X hX hZ f hf hker α hodd with h | ⟨rfl, rfl⟩ | rfl
    · exact h
    · exact hD4 X hX hZ f hf hker z K hKz α hodd hfix
    · have hn : n = 0 := hadm.2.2
      subst hn
      exact h3D4 X hX hZ f hf hker z K hKz α hodd hfix
  · exfalso
    have hs : Group.IsSolvable SL(2, ZMod 3) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [natCard_sl2Three]; norm_num)
    exact not_isSolvable_of_quasisimple hX (Group.isSolvable_of_surjective hf)
  · have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [Sporadic.Schreier.m11_center_eq_bot'] at hker
      exact le_bot_iff.mp hker
    let e := MulEquiv.ofBijective f ⟨hinj, hf⟩
    have hinner := Sporadic.Schreier.inner_eq_top_of_card_le
      Sporadic.Schreier.m11_center_eq_bot' Sporadic.Schreier.m11_mulAut_card
    have hβ : (MulAut.congr e).symm α ∈ OuterAutomorphisms.inner _ := by
      rw [hinner]
      exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := hβ
    refine ⟨e m, ?_⟩
    rw [← OuterAutomorphisms.congr_conj e m, hm, MulEquiv.apply_symm_apply]

theorem modelOddAutRigid_of (hSt : SteinbergOddAut3) (hD4 : D4OddAutInner3)
    (h3D4 : TrialityD4OddAutInner3) : ModelOddAutRigid := by
  intro X _ _ hX hZ Λ _ hLie z K _ hKz α hodd hfix
  have hz := hKz.orderOf_eq_two
  suffices h : ∃ g : X, α = MulAut.conj g by
    obtain ⟨g, rfl⟩ := h
    exact modelOddAutRigid_inner hX hZ hLie hz g hodd hfix
  have hO := oddCore_eq_bot_of_quasisimple hX hZ hz
  obtain ⟨ι, _, ⟨S⟩⟩ := hLie
  let e : X ⧸ classicalInvolutionOddCore X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  obtain ⟨i, hi⟩ := exists_eq_top_of_commute hX hZ
    (fun i => (e.toMonoidHom.comp (S.hom i)).range)
    (fun i j hij x hx y hy => by
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      show e (S.hom i a) * e (S.hom j b) = e (S.hom j b) * e (S.hom i a)
      rw [← map_mul, ← map_mul, S.commute i j hij a b])
    (by
      simp only [MonoidHom.range_comp]
      rw [← Subgroup.map_iSup, S.generate]
      exact Subgroup.map_top_of_surjective _ e.surjective)
  have hsurj : Function.Surjective (e.toMonoidHom.comp (S.hom i)) := MonoidHom.range_eq_top.mp hi
  have hker : (e.toMonoidHom.comp (S.hom i)).ker ≤ Subgroup.center (S.kind i).G := by
    intro x hx
    refine S.ker_le_center i ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulEquiv.map_eq_one_iff e).mp hx
  exact exists_eq_conj_of_component hSt hD4 h3D4 hX hZ (S.valid i) _ hsurj hker hKz α hodd hfix

end CFSG.ClassicalInvolution.Q3.Q3T
